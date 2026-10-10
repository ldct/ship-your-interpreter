import Dc.Mach.DcRefOps
import Dc.Mach.Bc.Free
import Dc.Mach.DcDup
import Dc.Mach.DcPend

/-!
# One reference fewer (M9)

`bc_free_num` (through `dc_free_num`) drops a handle's reference to a
number: the count is decremented, or the last reference releases the
object. On the state:

- `DcAt.decNum`: the handle `.num p` leaves `hs`, `n_refs` one less.
- `DcAt.relNum`: the handle was the last reference; the object leaves the
  number heap.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem NumObj.decRef_withRefs (x : NumObj) : x.decRef = x.withRefs (x.rep.refs - 1) := rfl

/-- A pairwise relation carried over with membership in the left list. -/
theorem forall₂_imp_mem {α β : Type} {P P' : α → β → Prop} :
    ∀ {l : List α} {m : List β}, (∀ a ∈ l, ∀ b, P a b → P' a b) → List.Forall₂ P l m →
      List.Forall₂ P' l m
  | [], [], _, .nil => .nil
  | _ :: _, _ :: _, hi, .cons h t =>
    .cons (hi _ List.mem_cons_self _ h) (forall₂_imp_mem (fun a ha => hi a (List.mem_cons_of_mem _ ha)) t)

/-- A datum other than `.num x.p` denotes through the list without `x`. -/
theorem GV.Den.drop {L1 L2 : List NumObj} {x : NumObj} {ss : List StrObj} {g : GV} {v : Val}
    (h : g.Den ⟨L1 ++ x :: L2, ss⟩ v) (hg : g ≠ .num x.rep.p) : g.Den ⟨L1 ++ L2, ss⟩ v := by
  cases g <;> cases v <;> simp only [GV.Den] at h ⊢
  · obtain ⟨y, hy, e1, e2⟩ := h
    rcases mem_split_cases hy with rfl | hy
    · exact absurd (by rw [e1]) hg
    · exact ⟨y, hy, e1, e2⟩
  · exact h

theorem RLev.Den.drop {L1 L2 : List NumObj} {x : NumObj} {ss : List StrObj} {e : RLev} {v : Entry}
    (h : e.Den ⟨L1 ++ x :: L2, ss⟩ v) (hg : ∀ g ∈ e.v.toList ++ e.arr.map (·.2.v), g ≠ .num x.rep.p) :
    e.Den ⟨L1 ++ L2, ss⟩ v := by
  refine ⟨?_, forall₂_imp_mem (fun bn hbn iv hh => ⟨hh.1, hh.2.drop (hg _ (List.mem_append_right _
    (List.mem_map.mpr ⟨bn, hbn, rfl⟩)))⟩) h.arr⟩
  have hv := h.val
  have hg' : ∀ g ∈ e.v.toList, g ≠ .num x.rep.p := fun g hg1 => hg g (List.mem_append_left _ hg1)
  revert hv hg'
  generalize e.v = a; generalize v.val = b
  intro hv hg'
  cases hv with
  | none => exact .none
  | some r => exact .some (r.drop (hg' _ (by simp)))

/-- The state's references to `x` after the handle left: none. -/
theorem DcDen.vals_ne {L1 L2 : List NumObj} {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV}
    {st : St} (d : DcDen (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st) (h1 : x.rep.refs = 1) :
    (∀ g ∈ G.vals ++ hs, g ≠ .num x.rep.p) ∧ C.cnt x.rep.p = 0 ∧ G.lk.count x.rep.p = 0 := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have e := d.numRefs x hx
  rw [count_cons_self] at e
  refine ⟨fun g hg hgx => ?_, by omega, by omega⟩
  subst hgx
  have := List.count_pos_iff.mpr hg
  omega

/-- **The last reference released**, on the ghost side. -/
theorem DcDen.rel {L1 L2 : List NumObj} {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV}
    {st : St} (d : DcDen (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st)
    (hpn : ∀ y ∈ L1 ++ L2, y.rep.p ≠ x.rep.p) (h1 : x.rep.refs = 1) :
    DcDen (L1 ++ L2) C G hs st := by
  obtain ⟨hne, hc0, hl0⟩ := d.vals_ne h1
  have hvs : ∀ g ∈ G.vals, g ≠ .num x.rep.p := fun g hg => hne g (List.mem_append_left _ hg)
  have hcx : ∀ c ∈ [C.z, C.o, C.t], c ≠ x := fun c hc e => by
    subst e
    have : 0 < C.cnt c.rep.p := by
      unfold BcConsts.cnt; exact List.countP_pos_iff.mpr ⟨c, hc, by simp⟩
    omega
  have hmem : ∀ c ∈ [C.z, C.o, C.t], c ∈ L1 ++ x :: L2 → c ∈ L1 ++ L2 := fun c hc hm => by
    rcases mem_split_cases hm with e | hm
    · exact absurd e (hcx c hc)
    · exact hm
  exact
    { stk := forall₂_imp_mem (fun bg hbg v hh => hh.drop (hvs _ (by
        unfold DcG.vals; exact List.mem_append_left _ (List.mem_map.mpr ⟨bg, hbg, rfl⟩)))) d.stk
      regs := fun r hr => forall₂_imp_mem (fun be hbe v hh => hh.drop fun g hg => hvs g (by
        unfold DcG.vals
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
          List.mem_flatMap.mpr ⟨be, hbe, hg⟩⟩))) (d.regs r hr)
      regsHi := d.regsHi
      hsDen := fun g hg => by
        obtain ⟨v, hv⟩ := d.hsDen g (List.mem_cons_of_mem _ hg)
        exact ⟨v, hv.drop (hne g (List.mem_append_right _ hg))⟩
      owns := fun y hy => d.owns y (mem_split_of hy)
      norm := fun y hy => d.norm y (mem_split_of hy)
      pos := fun y hy => d.pos y (mem_split_of hy)
      numRefs := fun y hy => by
        rw [d.numRefs y (mem_split_of hy), count_cons_ne _ _ fun e => hpn y hy (GV.num.inj e).symm]
      strRefs := fun o ho => by rw [d.strRefs o ho, count_cons_ne _ _ (by simp)]
      live := fun y hy => d.live y (mem_split_of hy)
      lkLen := d.lkLen
      lkIn := fun p hp => by
        obtain ⟨y, hy, e⟩ := d.lkIn p hp
        rcases mem_split_cases hy with rfl | hy
        · subst e; exact absurd (List.count_pos_iff.mpr hp) (by omega)
        · exact ⟨y, hy, e⟩
      mz := hmem _ (by simp) d.mz
      mo := hmem _ (by simp) d.mo
      mt := hmem _ (by simp) d.mt
      zv := d.zv
      ov := d.ov
      tv := d.tv
      ibase := d.ibase
      obase := d.obase
      scale := d.scale
      unwind := d.unwind
      lbuf := d.lbuf }

/-- **One reference fewer**, on the ghost side: the constants follow the
decremented object. -/
theorem DcDen.dec {L1 L2 : List NumObj} {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV}
    {st : St} (d : DcDen (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st)
    (hne : ∀ y ∈ L1 ++ L2, y.rep.p ≠ x.rep.p) (h2 : 2 ≤ x.rep.refs) :
    DcDen (L1 ++ x.decRef :: L2) (C.subst x x.decRef) G hs st := by
  classical
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hp' : x.decRef.rep.p = x.rep.p := rfl
  have hn' : x.decRef.rep.num = x.rep.num := rfl
  have hsub : ∀ ss : List StrObj, DObjs.Sub ⟨L1 ++ x :: L2, ss⟩ ⟨L1 ++ x.decRef :: L2, ss⟩ := fun ss =>
    ⟨fun y hy => ⟨_, BcConsts.subst_mem (x' := x.decRef) hy, ite_rep hp' hn' y _⟩,
      fun o ho => ⟨o, ho, rfl, rfl⟩⟩
  have hcz : ∀ (y : NumObj) [Decidable (y = x)], y ∈ L1 ++ x :: L2 →
      (if y = x then x.decRef else y) ∈ L1 ++ x.decRef :: L2 := fun y _ hy => BcConsts.subst_mem hy
  refine { d with
    stk := d.stk.imp fun hh => hh.relist (hsub _)
    regs := fun r hr => (d.regs r hr).imp fun hh => hh.relist (hsub _)
    hsDen := fun g hg => ?_
    owns := fun y hy => ?_
    norm := fun y hy => ?_
    pos := fun y hy => ?_
    numRefs := fun y hy => ?_
    strRefs := fun o ho => ?_
    live := fun y hy => ?_
    lkIn := fun p hp => by
      obtain ⟨y, hy, e⟩ := d.lkIn p hp
      exact ⟨_, hcz y hy, (ite_rep hp' hn' y _).1.trans e⟩
    mz := hcz _ d.mz
    mo := hcz _ d.mo
    mt := hcz _ d.mt
    zv := by simp only [BcConsts.subst, (ite_rep hp' hn' _ _).2]; exact d.zv
    ov := by simp only [BcConsts.subst, (ite_rep hp' hn' _ _).2]; exact d.ov
    tv := by simp only [BcConsts.subst, (ite_rep hp' hn' _ _).2]; exact d.tv }
  · obtain ⟨w, hw⟩ := d.hsDen g (List.mem_cons_of_mem _ hg); exact ⟨w, hw.relist (hsub _)⟩
  · rcases mem_split_cases hy with rfl | hy
    · exact d.owns x hx
    · exact d.owns y (mem_split_of hy)
  · rcases mem_split_cases hy with rfl | hy
    · exact d.norm x hx
    · exact d.norm y (mem_split_of hy)
  · rcases mem_split_cases hy with rfl | hy
    · exact d.pos x hx
    · exact d.pos y (mem_split_of hy)
  · rw [BcConsts.subst_cnt C hp' hn']
    rcases mem_split_cases hy with rfl | hy
    · show x.rep.refs - 1 = (G.vals ++ hs).count (.num x.rep.p) + C.cnt x.rep.p + G.lk.count x.rep.p
      have := d.numRefs x hx; rw [count_cons_self] at this; omega
    · rw [d.numRefs y (mem_split_of hy), count_cons_ne _ _ fun e => hne y hy (GV.num.inj e).symm]
  · rw [d.strRefs o ho, count_cons_ne _ _ (by simp)]
  · rcases mem_split_cases hy with rfl | hy
    · show 1 ≤ x.rep.refs - 1; omega
    · exact d.live y (mem_split_of hy)

/-- The constants' words read the same after a substitution keeping pointers. -/
theorem DcView.subst {M : Mem} {G : DcG} {C : BcConsts} {st : St} (v : DcView M G C st)
    {x x' : NumObj} (hp : x'.rep.p = x.rep.p) (hn : x'.rep.num = x.rep.num) :
    DcView M G (C.subst x x') st := by
  classical
  refine { v with zw := ?_, ow := ?_, tw := ?_ }
  · simp only [BcConsts.subst, (ite_rep hp hn _ _).1]; exact v.zw
  · simp only [BcConsts.subst, (ite_rep hp hn _ _).1]; exact v.ow
  · simp only [BcConsts.subst, (ite_rep hp hn _ _).1]; exact v.tw

/-- A member of the left list of a pairwise relation has a partner. -/
theorem forall₂_left {α β : Type} {P : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ P l m → ∀ a ∈ l, ∃ b, P a b
  | [], [], .nil, _, ha => absurd ha List.not_mem_nil
  | _ :: _, _ :: _, .cons h t, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, h⟩
    · exact forall₂_left t a ha

/-- Every reference of the state and of the handles denotes. -/
theorem DcDen.vals_den {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (d : DcDen L C G hs st) : ∀ g ∈ G.vals ++ hs, ∃ v, g.Den ⟨L, G.strs⟩ v := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · unfold DcG.vals at hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨bg, hbg, rfl⟩ := List.mem_map.mp hg
      exact forall₂_left d.stk bg hbg
    · obtain ⟨r, hr, hg⟩ := List.mem_flatMap.mp hg
      obtain ⟨be, hbe, hg⟩ := List.mem_flatMap.mp hg
      have hr := List.mem_range.mp hr
      obtain ⟨v, hv⟩ := forall₂_left (d.regs r hr) be hbe
      unfold RLev.vals at hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨g0, hg0, rfl⟩ : ∃ g0, be.2.v = some g0 ∧ g = g0 := by
          cases e : be.2.v <;> simp_all [Option.toList]
        have hvv := hv.val; rw [hg0] at hvv
        match v.val, hvv with
        | _, .some r => exact ⟨_, r⟩
      · obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hg
        obtain ⟨iv, hiv⟩ := forall₂_left hv.arr bn hbn
        exact ⟨_, hiv.2⟩
  · exact d.hsDen g hg

/-- **A fresh number with one reference** joins the heap with its handle. -/
theorem DcDen.addNum {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (d : DcDen L C G hs st) {y : NumObj} (hne : ∀ z ∈ L, z.rep.p ≠ y.rep.p)
    (h1 : y.rep.refs = 1) (hno : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (how : y.Owns) :
    DcDen (y :: L) C G (.num y.rep.p :: hs) st := by
  have hsub : ∀ ss : List StrObj, DObjs.Sub ⟨L, ss⟩ ⟨y :: L, ss⟩ := fun ss =>
    ⟨fun z hz => ⟨z, List.mem_cons_of_mem _ hz, rfl, rfl⟩, fun o ho => ⟨o, ho, rfl, rfl⟩⟩
  have hvy : ∀ g ∈ G.vals ++ hs, g ≠ .num y.rep.p := fun g hg e => by
    obtain ⟨v, hv⟩ := d.vals_den g hg
    subst e
    cases v with
    | num n => obtain ⟨z, hz, e1, -⟩ := hv; exact hne z hz e1
    | str s => exact hv
  have hc0 : C.cnt y.rep.p = 0 := by
    unfold BcConsts.cnt
    refine List.countP_eq_zero.mpr fun c hc e => ?_
    simp only [decide_eq_true_eq] at e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hne _ d.mz e
    · exact hne _ d.mo e
    · exact hne _ d.mt e
  have hl0 : G.lk.count y.rep.p = 0 := List.count_eq_zero.mpr fun hm => by
    obtain ⟨z, hz, e⟩ := d.lkIn _ hm; exact hne z hz e
  refine { d with
    stk := d.stk.imp fun hh => hh.relist (hsub _)
    regs := fun r hr => (d.regs r hr).imp fun hh => hh.relist (hsub _)
    hsDen := fun g hg => ?_
    owns := fun z hz => ?_
    norm := fun z hz => ?_
    pos := fun z hz => ?_
    numRefs := fun z hz => ?_
    strRefs := fun o ho => ?_
    live := fun z hz => ?_
    lkIn := fun p hp => by
      obtain ⟨z, hz, e⟩ := d.lkIn p hp
      exact ⟨z, List.mem_cons_of_mem _ hz, e⟩
    mz := List.mem_cons_of_mem _ d.mz
    mo := List.mem_cons_of_mem _ d.mo
    mt := List.mem_cons_of_mem _ d.mt }
  · rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨.num y.rep.num, y, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨w, hw⟩ := d.hsDen g hg; exact ⟨w, hw.relist (hsub _)⟩
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact how
    · exact d.owns z hz
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact hno
    · exact d.norm z hz
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact hpos
    · exact d.pos z hz
  · rcases List.mem_cons.mp hz with rfl | hz
    · rw [count_cons_self, List.count_eq_zero.mpr fun hm => hvy _ hm rfl, hc0, hl0, h1]
    · rw [d.numRefs z hz, count_cons_ne _ _ fun e => hne z hz (GV.num.inj e).symm]
  · rw [d.strRefs o ho, count_cons_ne _ _ (by simp)]
  · rcases List.mem_cons.mp hz with rfl | hz
    · omega
    · exact d.live z hz

/-- **Held handles keep their values** from objects `O` to `O'`. -/
def HsKeep (O O' : DObjs) (hs : List GV) : Prop := ∀ g ∈ hs, ∀ v, g.Den O v → g.Den O' v

theorem HsKeep.refl (O : DObjs) (hs : List GV) : HsKeep O O hs := fun _ _ _ h => h

theorem HsKeep.trans {O1 O2 O3 : DObjs} {hs : List GV} (h1 : HsKeep O1 O2 hs) (h2 : HsKeep O2 O3 hs) :
    HsKeep O1 O3 hs := fun g hg v h => h2 g hg v (h1 g hg v h)

theorem HsKeep.mono {O O' : DObjs} {hs hs' : List GV} (h : HsKeep O O' hs) (hm : ∀ g ∈ hs', g ∈ hs) :
    HsKeep O O' hs' := fun g hg => h g (hm g hg)

/-- One reference fewer on a number keeps every handle's value. -/
theorem HsKeep.decRef {L1 L2 : List NumObj} {x : NumObj} {ss : List StrObj} (hs : List GV) :
    HsKeep ⟨L1 ++ x :: L2, ss⟩ ⟨L1 ++ x.decRef :: L2, ss⟩ hs := by
  classical
  exact fun _ _ _ hv => GV.Den.relist (O := ⟨L1 ++ x :: L2, ss⟩) (O' := ⟨L1 ++ x.decRef :: L2, ss⟩)
    ⟨fun y hy => ⟨_, BcConsts.subst_mem (x := x) (x' := x.decRef) hy,
      ite_rep (x := x) (x' := x.decRef) rfl rfl y _⟩, fun o ho => ⟨o, ho, rfl, rfl⟩⟩ hv

/-- The last reference to a number released keeps the other handles' values. -/
theorem HsKeep.rel {L1 L2 : List NumObj} {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV}
    {st : St} (d : DcDen (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st) (h1 : x.rep.refs = 1)
    (ss : List StrObj) : HsKeep ⟨L1 ++ x :: L2, ss⟩ ⟨L1 ++ L2, ss⟩ hs :=
  fun g hg _ hv => hv.drop ((d.vals_ne h1).1 g (List.mem_append_right _ hg))

/-- **The last reference released**: the handle `.num p` leaves `hs`, the
object leaves the number heap; the state's blocks and dc's globals keep
their bytes. -/
theorem DcAt.relNum {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st) (h1 : x.rep.refs = 1)
    (hb : BcHeap S (G.raws M) M' H' (x.sb :: F) (L1 ++ L2))
    (hag : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a)
    (hgl : ∀ a, DcGlob a → imgM M' a = imgM M a) :
    DcAt S M' H' (x.sb :: F) (L1 ++ L2) C G hs st :=
  ⟨hb.subRaw (fun c hc => hc) fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm, h.nodup,
    h.view.frame hag hgl, h.den.rel h.heap.p_ne_all h1, h.glob, h.col⟩

/-- **One reference fewer**: the handle `.num p` leaves `hs`, `n_refs` one
less; the state's blocks and dc's globals keep their bytes. -/
theorem DcAt.decNum {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st) (_h2 : 2 ≤ x.rep.refs)
    (hb : BcHeap S (G.raws M) M' H F (L1 ++ x.decRef :: L2))
    (hag : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a)
    (hgl : ∀ a, DcGlob a → imgM M' a = imgM M a) :
    DcAt S M' H F (L1 ++ x.decRef :: L2) (C.subst x x.decRef) G hs st :=
  ⟨hb.subRaw (fun c hc => hc) fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm, h.nodup,
    (h.view.frame hag hgl).subst rfl rfl, h.den.dec h.heap.p_ne_all _h2, h.glob, h.col⟩

/-- Different owners of the heap have different digit buffers. -/
theorem db_ne_of_owns {L1 L2 : List NumObj} {x y : NumObj} (hd : (objBlocks (L1 ++ x :: L2)).Nodup)
    (hy : y ∈ L1) (hoy : y.Owns) (hox : x.Owns) : y.db ≠ x.db := by
  rw [objBlocks_append] at hd
  refine nodup_app_ne hd (mem_objBlocks_db hy hoy) ?_
  rw [objBlocks_cons]; exact List.mem_append_left _ (by rw [NumObj.blocks_own hox]; simp)

/-- A handle `.num p` names a number of the heap. -/
theorem DcAt.handle_num {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat}
    (h : DcAt S M H F L C G (.num p :: hs) st) :
    ∃ L1 L2 x, L = L1 ++ x :: L2 ∧ x.rep.p = p := by
  obtain ⟨v, hv⟩ := h.den.hsDen _ List.mem_cons_self
  obtain ⟨x, hx, e1⟩ : ∃ x ∈ L, x.rep.p = p := by
    cases v with
    | num n => obtain ⟨x, hx, e1, -⟩ := hv; exact ⟨x, hx, e1⟩
    | str s => exact hv.elim
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hx
  exact ⟨L1, L2, x, rfl, e1⟩

/-- Where the slot handed to `bc_free_num` lies: in the pending window,
above the heap, or in a block fresh to the state. -/
inductive SlotPlace (H : Heap) (F : List Blk) (L : List NumObj) (G : DcG) (W : Nat → Prop)
    (q : Nat) : Prop
  | win : (∀ a, slotBytes q a → W a) → SlotPlace H F L G W q
  | above : heapEnd ≤ q → SlotPlace H F L G W q
  | fresh (c : Blk) : DcFresh H F L G c → (∀ a, slotBytes q a → c.In a) → SlotPlace H F L G W q

/-- What a placed slot is apart from. -/
structure SlotClear (H : Heap) (F : List Blk) (L : List NumObj) (G : DcG) (E : List Blk)
    (W : Nat → Prop) (q : Nat) : Prop where
  apart : ∀ b ∈ H.live, b ∉ E → (b ∈ G.blocks ∨ b ∈ F ++ objBlocks L) → ∀ a, b.In a →
    ¬ slotBytes q a
  noAlloc : ∀ a, slotBytes q a → ¬ AllocByte H a
  lo : heapStart ≤ q
  winG : ∀ a, slotBytes q a → InBlocks G.blocks a → W a

theorem SlotPlace.clear {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {G : DcG} {E : List Blk} {W : Nat → Prop} {Φ : Mem → Mem} {q : Nat}
    (hs : SlotPlace H F L G W q) (hp : Pend G E W Φ) (hi : HeapInv S Mt H)
    (hE : ∀ e ∈ E, e ∈ H.live) (hG : ∀ b ∈ G.blocks, b ∈ H.live) : SlotClear H F L G E W q := by
  cases hs with
  | win hw =>
    exact
      { apart := fun b hb hbE _ a hba hsa => hp.not_win hi hE hb hbE hba (hw a hsa)
        noAlloc := fun a hsa => hp.not_alloc hi hE (hw a hsa)
        lo := (hp.inHeap hi hE (hw q ⟨Nat.le_refl q, by omega⟩)).1
        winG := fun a hsa _ => hw a hsa }
  | above hq =>
    have hout : ∀ a, slotBytes q a → heapEnd ≤ a := fun a hsa => by
      simp only [slotBytes] at hsa; omega
    exact
      { apart := fun b hb _ _ a hba hsa => by
          have := live_in_heap hi hb hba; have := hout a hsa; omega
        noAlloc := fun a hsa => OutHeap.not_alloc hi (outHeap_of_ge (hout a hsa))
        lo := by simp only [heapStart, heapEnd] at hq ⊢; omega
        winG := fun a hsa ⟨b, hb, hba⟩ => by
          have := live_in_heap hi (hG b hb) hba; have := hout a hsa; omega }
  | fresh c hc hin =>
    have hne : ∀ b, (b ∈ G.blocks ∨ b ∈ F ++ objBlocks L) → b ≠ c := fun b hb e => by
      subst e; rcases hb with hb | hb
      · exact hc.notG hb
      · exact hc.notNum hb
    exact
      { apart := fun b hb _ hbm a hba hsa =>
          live_apart hi hb hc.live (hne b hbm) hba (hin a hsa)
        noAlloc := fun a hsa => live_not_alloc hi hc.live (hin a hsa)
        lo := (live_in_heap hi hc.live (hin q ⟨Nat.le_refl q, by omega⟩)).1
        winG := fun a hsa ⟨b, hb, hba⟩ =>
          (live_apart hi (hG b hb) hc.live (hne b (.inl hb)) hba (hin a hsa)).elim }

/-- **`bc_free_num`'s entry from a handle** `.num p` held in a slot `q`, on a
pending state (`Pend`): the slot lies in the window or above the heap,
apart from the callee's 32-byte frame. -/
theorem DcAt.freeEntryP {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {E : List Blk}
    {W : Nat → Prop} {Φ : Mem → Mem} (hp : Pend G E W Φ)
    (h : DcAt S (Φ M) H F (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st) {q sp : Nat}
    (hq : PtrSlot S q) (hqs : SlotPlace H F (L1 ++ x :: L2) G W q)
    (hw : ldv .ld M q = BitVec.ofNat 64 x.rep.p) (hsf : StackFrame S sp 32)
    (hab : heapEnd + 32 ≤ sp) (hqf : q + 8 ≤ sp - 32 ∨ sp ≤ q) :
    FreeEntry S (G.rawsOff E (Φ M)) M H F L1 L2 x q sp := by
  have hb := h.machHeap hp
  have hi := hb.heap
  obtain ⟨hE, hEo⟩ := h.pendLive hp
  have hc := hqs.clear hp hi hE h.heap.raw.live
  have hrefs : 1 ≤ x.rep.refs := by
    have := h.den.numRefs x (List.mem_append_right _ List.mem_cons_self); rw [count_cons_self] at this; omega
  exact
    { heap := hb
      refs := hrefs
      slot := hq
      off :=
        { alloc := hc.noAlloc
          blocks := fun b hb' a ha hba => hc.apart b (hb.owned_live (List.mem_append_left _ hb'))
            (fun he => hEo b he hb') (.inr hb') a hba ha
          glob := by have := hc.lo; simp only [bcFreeAddr, heapStart] at this ⊢; omega
          frame := hqf
          raw := fun b hb' a ha hba => hc.apart b (hb.raw.live b hb') (DcG.mem_rawsOff.mp hb').2
            (.inl (DcG.mem_rawsOff.mp hb').1) a hba ha }
      word := hw
      stack := hsf
      above := by simp only [heapEnd] at hab ⊢; omega
      noView := fun _ hox y hy => db_ne_of_owns (List.nodup_append.mp h.heap.distinct).2.1 hy
        (h.den.owns y (List.mem_append_left _ hy)) hox }

/-- **`bc_free_num`'s entry from a handle** `.num p` held in a stack slot `q`
above the heap, apart from the callee's 32-byte frame. -/
theorem DcAt.freeEntry {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st) {q sp : Nat} (hq : PtrSlot S q)
    (hqh : heapEnd ≤ q) (hw : ldv .ld M q = BitVec.ofNat 64 x.rep.p) (hsf : StackFrame S sp 32)
    (hab : heapEnd + 32 ≤ sp) (hqf : q + 8 ≤ sp - 32 ∨ sp ≤ q) :
    FreeEntry S (G.raws M) M H F L1 L2 x q sp := by
  have e := DcAt.freeEntryP (Pend.id G) (M := M) h hq (.above hqh) hw hsf hab hqf
  rwa [DcG.rawsOff_nil] at e

/-- **`bc_free_num (&a)`** at `0x800048c0` on a handle `.num p` held in the
slot `q`, on a pending state: one reference fewer, or the object released;
the slot is `NULL`. -/
theorem bc_free_num_dcP {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat} {E : List Blk}
    {W : Nat → Prop} {Φ : Mem → Mem} (hp : Pend G E W Φ)
    (h : DcAt S (Φ M) H F L C G (.num p :: hs) st) {q sp : Nat} (hq : PtrSlot S q)
    (hqs : SlotPlace H F L G W q)
    (hw : ldv .ld M q = BitVec.ofNat 64 p) (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (hqf : q + 8 ≤ sp - 32 ∨ sp ≤ q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps freeNumClob R' R → DcAt S (Φ M') H' F' L' C' G hs st →
      ldv .ld M' q = 0#64 →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 32 a → ¬ slotBytes q a → imgM M' a = imgM M a) →
      (∀ c, DcFresh H F L G c → DcFresh H' F' L' G c ∧
        ∀ a, c.In a → ¬ slotBytes q a → imgM M' a = imgM M a) →
      HsKeep ⟨L, G.strs⟩ ⟨L', G.strs⟩ hs →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x800048c0#64 R M := by
  obtain ⟨L1, L2, x, rfl, rfl⟩ := h.handle_num
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have e := h.freeEntryP hp hq hqs hw hsf hab hqf
  have hi := e.heap.heap
  obtain ⟨hE, hEo⟩ := h.pendLive hp
  have hclr := hqs.clear hp hi hE h.heap.raw.live
  simp only [heapEnd] at hab
  have hxb := h.heap.blocks x hx
  have hGb : ∀ a, InBlocks G.blocks a → ¬ AllocByte H a ∧ ¬ x.sb.In a ∧ (slotBytes q a → W a) ∧
      ¬ frameIn sp 32 a ∧ ¬ bcFreeBytes a := fun a ha => by
    obtain ⟨hin, hna⟩ := h.inBlocks_heap ha
    obtain ⟨c, hc, hca⟩ := ha
    have hcl := h.heap.raw.live c hc
    refine ⟨hna, fun hxa => live_apart h.heap.heap hcl hxb.sLive
      (h.heap.raw_ne hc (List.mem_append_right _ (mem_objBlocks hx))) hca hxa,
      fun hs => hclr.winG a hs ⟨c, hc, hca⟩, fun hf => ?_, fun hf => ?_⟩
    · simp only [frameIn, heapStart, heapEnd] at hf hin; omega
    · have e : bcFreeAddr = 0x8001cdb0 := rfl
      simp only [bcFreeBytes, heapStart, heapEnd] at hf hin; omega
  have hGg : ∀ a, DcGlob a → ¬ AllocByte H a ∧ ¬ x.sb.In a ∧ ¬ slotBytes q a ∧
      ¬ frameIn sp 32 a ∧ ¬ bcFreeBytes a := fun a ha => by
    have hlt := ha.lt
    refine ⟨OutHeap.not_alloc hi ha.outHeap, fun hxa => ?_, fun hs => ?_, fun hf => ?_, fun hf => ?_⟩
    · have := live_in_heap hi hxb.sLive hxa; omega
    · have := hclr.lo; simp only [slotBytes, heapStart] at this hs hlt; omega
    · simp only [frameIn, heapStart] at hf hlt; omega
    · have := ha.outHeap; simp only [OutHeap] at this; exact this.2.2 hf
  have hob : objBlocks (L1 ++ x.decRef :: L2) = objBlocks (L1 ++ x :: L2) := by
    rw [objBlocks_append, objBlocks_cons, objBlocks_append, objBlocks_cons]; rfl
  refine bc_free_num_spec hlive e R h10 h2 hal ⟨fun h2r R' M' hk1 hb hz hm => ?_,
    fun h1r R' M' H' hk1 hr => ?_⟩
  · have hm' := hp.memOnlyW hm
    have hrx : ∀ a, refsBytes x.rep a → x.sb.In a := fun a ha => by
      have := hxb.sSz; have := hxb.sPay
      simp only [refsBytes, Blk.In, Blk.pay, Blk.fin] at ha this ⊢; omega
    have hag : ∀ a, InBlocks G.blocks a → imgM (Φ M') a = imgM (Φ M) a := fun a ha => hm' a ?_
    · have hb' := (hb.ofMach hp hE (by rw [hob]; exact hEo)).subRaw (X' := G.raws (Φ M)) (fun c hc => hc)
        fun c hc a ha => hag a ⟨c, hc, ha⟩
      refine hk R' M' H F _ _ hk1 (h.decNum h2r hb' hag fun a ha => hm' a ?_) hz
        (fun a ho hg hf hs => hm a ?_) (fun c hc => ⟨⟨hc.live, hc.notG, by rw [hob]; exact hc.notNum⟩,
          fun a hca hs => hm a ?_⟩) (HsKeep.decRef hs)
      · rintro ⟨hr | hs, -⟩; exact (hGg a ha).2.1 (hrx a hr); exact (hGg a ha).2.2.1 hs
      · rintro (hr | hs')
        · exact ho.1 (live_in_heap hi hxb.sLive (hrx a hr))
        · exact hs hs'
      · rintro (hr | hs')
        · exact live_apart hi hc.live hxb.sLive (fun e => hc.notNum (List.mem_append_right _
            (e ▸ mem_objBlocks hx))) hca (hrx a hr)
        · exact hs hs'
    · rintro ⟨hr | hs, hnw⟩; exact (hGb a ha).2.1 (hrx a hr); exact hnw ((hGb a ha).2.2.1 hs)
  · have hfr := hp.memOnlyW hr.frame
    have hE' : ∀ e ∈ E, e ∈ H'.live := fun c hc => by
      by_cases ho : x.Owns
      · exact ((hr.owned ho).2.1 c).mpr ⟨hE c hc, fun he => hEo c hc
          (List.mem_append_right _ (he ▸ h.heap.db_mem hx))⟩
      · rw [hr.view ho]; exact hE c hc
    have hnum' : ∀ c, c ∉ F ++ objBlocks (L1 ++ x :: L2) → c ∉ x.sb :: F ++ objBlocks (L1 ++ L2) :=
      fun c hc hm => by
        rcases List.mem_cons.mp hm with he | hm
        · exact hc (List.mem_append_right _ (he ▸ mem_objBlocks hx))
        rcases List.mem_append.mp hm with hm | hm
        · exact hc (List.mem_append_left _ hm)
        · refine hc (List.mem_append_right _ ?_)
          rw [objBlocks_append, objBlocks_cons] at *
          rcases List.mem_append.mp hm with hm | hm
          · exact List.mem_append_left _ hm
          · exact List.mem_append_right _ (List.mem_append_right _ hm)
    have hlive' : ∀ c ∈ H.live, c ∉ F ++ objBlocks (L1 ++ x :: L2) → c ∈ H'.live := fun c hc hcn => by
      by_cases ho : x.Owns
      · exact ((hr.owned ho).2.1 c).mpr ⟨hc, fun he => hcn
          (List.mem_append_right _ (he ▸ h.heap.db_mem hx))⟩
      · rw [hr.view ho]; exact hc
    have hEo' : ∀ e ∈ E, e ∉ x.sb :: F ++ objBlocks (L1 ++ L2) := fun c hc => hnum' c (hEo c hc)
    have hag : ∀ a, InBlocks G.blocks a → imgM (Φ M') a = imgM (Φ M) a := fun a ha => hfr a ?_
    · have hb' := (hr.heap.ofMach hp hE' hEo').subRaw (X' := G.raws (Φ M)) (fun c hc => hc)
        fun c hc a ha => hag a ⟨c, hc, ha⟩
      refine hk R' M' H' _ _ _ hk1 (h.relNum h1r hb' hag fun a ha => hfr a ?_) hr.slot
        (fun a ho hg hf hs => hr.frame a ?_) (fun c hc => ⟨⟨hlive' c hc.live hc.notNum, hc.notG,
          hnum' c hc.notNum⟩, fun a hca hs => hr.frame a ?_⟩) (HsKeep.rel h.den h1r _)
      · obtain ⟨n1, n2, n3, n4, n5⟩ := hGg a ha
        rintro ⟨c | c | c | c | c, -⟩ <;> contradiction
      · rintro (c | c | c | c | c)
        · exact OutHeap.not_alloc hi ho c
        · exact ho.1 (live_in_heap hi hxb.sLive c)
        · exact hs c
        · exact hf c
        · exact ho.2.2 c
      · have hin := live_in_heap hi hc.live hca
        rintro (c' | c' | c' | c' | c')
        · exact live_not_alloc hi hc.live hca c'
        · exact live_apart hi hc.live hxb.sLive (fun e => hc.notNum (List.mem_append_right _
            (e ▸ mem_objBlocks hx))) hca c'
        · exact hs c'
        · simp only [frameIn, heapStart, heapEnd] at c' hin; omega
        · have e : bcFreeAddr = 0x8001cdb0 := rfl
          simp only [bcFreeBytes, heapStart, heapEnd] at c' hin; omega
    · obtain ⟨n1, n2, n3, n4, n5⟩ := hGb a ha
      rintro ⟨c | c | c | c | c, hnw⟩
      · exact n1 c
      · exact n2 c
      · exact hnw (n3 c)
      · exact n4 c
      · exact n5 c

/-- **`dc_free_num (&a)`** at `0x80002ba0` (a jump to `bc_free_num`) on a
pending state. -/
theorem dc_free_num_specP {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat} {E : List Blk}
    {W : Nat → Prop} {Φ : Mem → Mem} (hp : Pend G E W Φ)
    (h : DcAt S (Φ M) H F L C G (.num p :: hs) st) {q sp : Nat} (hq : PtrSlot S q)
    (hqs : SlotPlace H F L G W q)
    (hw : ldv .ld M q = BitVec.ofNat 64 p) (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (hqf : q + 8 ≤ sp - 32 ∨ sp ≤ q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps freeNumClob R' R → DcAt S (Φ M') H' F' L' C' G hs st →
      ldv .ld M' q = 0#64 →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 32 a → ¬ slotBytes q a → imgM M' a = imgM M a) →
      (∀ c, DcFresh H F L G c → DcFresh H' F' L' G c ∧
        ∀ a, c.In a → ¬ slotBytes q a → imgM M' a = imgM M a) →
      HsKeep ⟨L, G.strs⟩ ⟨L', G.strs⟩ hs →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80002ba0#64 R M :=
  st_80002ba0 hlive (bc_free_num_dcP hlive hp h hq hqs hw hsf hab hqf R h10 h2 hal hk)

/-- **`bc_free_num (&a)`** at `0x800048c0` on a handle `.num p` held in the
stack slot `q`. -/
theorem bc_free_num_dc {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat}
    (h : DcAt S M H F L C G (.num p :: hs) st) {q sp : Nat} (hq : PtrSlot S q) (hqh : heapEnd ≤ q)
    (hw : ldv .ld M q = BitVec.ofNat 64 p) (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (hqf : q + 8 ≤ sp - 32 ∨ sp ≤ q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps freeNumClob R' R → DcAt S M' H' F' L' C' G hs st →
      ldv .ld M' q = 0#64 →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 32 a → ¬ slotBytes q a → imgM M' a = imgM M a) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x800048c0#64 R M :=
  bc_free_num_dcP hlive (Pend.id G) (M := M) h hq (.above hqh) hw hsf hab hqf R h10 h2 hal
    fun R' M' H' F' L' C' k1 k2 k3 k4 _ _ => hk R' M' H' F' L' C' k1 k2 k3 k4

/-- **`dc_free_num (&a)`** at `0x80002ba0` on a handle `.num p` held in the
stack slot `q`: one reference fewer, or the object released; the slot is
`NULL`. -/
theorem dc_free_num_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat}
    (h : DcAt S M H F L C G (.num p :: hs) st) {q sp : Nat} (hq : PtrSlot S q) (hqh : heapEnd ≤ q)
    (hw : ldv .ld M q = BitVec.ofNat 64 p) (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (hqf : q + 8 ≤ sp - 32 ∨ sp ≤ q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps freeNumClob R' R → DcAt S M' H' F' L' C' G hs st →
      ldv .ld M' q = 0#64 →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 32 a → ¬ slotBytes q a → imgM M' a = imgM M a) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80002ba0#64 R M :=
  dc_free_num_specP hlive (Pend.id G) (M := M) h hq (.above hqh) hw hsf hab hqf R h10 h2 hal
    fun R' M' H' F' L' C' k1 k2 k3 k4 _ _ => hk R' M' H' F' L' C' k1 k2 k3 k4

/-! ## Strings -/

/-- The ghost without the string `o` (`G.strs = A ++ o :: B`). -/
abbrev DcG.dropStr (G : DcG) (A B : List StrObj) : DcG := { G with strs := A ++ B }

theorem DcG.blocks_perm_drop {G : DcG} {A B : List StrObj} {o : StrObj} (he : G.strs = A ++ o :: B) :
    G.blocks.Perm ([o.hb, o.tb] ++ (G.dropStr A B).blocks) := by
  have hp : ((A ++ o :: B).flatMap fun o => [o.hb, o.tb]).Perm
      ([o.hb, o.tb] ++ (A ++ B).flatMap fun o => [o.hb, o.tb]) := by
    have := (List.perm_middle (a := o) (l₁ := A) (l₂ := B)).flatMap_right (fun o => [o.hb, o.tb])
    simpa using this
  unfold DcG.blocks
  rw [he, List.perm_iff_count]
  intro a
  have := hp.count_eq a
  simp only [DcG.dropStr, List.count_append] at this ⊢
  omega

/-- A window off the string `o` stays pending without it. -/
theorem Pend.dropStr {G : DcG} {E : List Blk} {W : Nat → Prop} {Φ : Mem → Mem}
    (hp : Pend G E W Φ) {A B : List StrObj} {o : StrObj} (he : G.strs = A ++ o :: B) :
    Pend (G.dropStr A B) E W Φ := by
  have hom : o ∈ G.strs := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
  refine { hp with sub := fun e hE => ?_, nstr := fun e hE o2 ho2 => hp.nstr e hE o2 (by
    rw [he]; exact mem_split_of ho2) }
  have := (G.blocks_perm_drop he).mem_iff.mp (hp.sub e hE)
  rcases List.mem_append.mp this with h | h
  · obtain ⟨n1, n2⟩ := hp.nstr e hE o hom
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> contradiction
  · exact h

/-- A string datum other than `.str o.p` denotes without `o`. -/
theorem GV.Den.dropStr {L : List NumObj} {A B : List StrObj} {o : StrObj} {g : GV} {v : Val}
    (h : g.Den ⟨L, A ++ o :: B⟩ v) (hg : g ≠ .str o.hb.pay) : g.Den ⟨L, A ++ B⟩ v := by
  cases g <;> cases v <;> simp only [GV.Den] at h ⊢
  · exact h
  · obtain ⟨o2, ho2, e1, e2⟩ := h
    rcases mem_split_cases ho2 with rfl | ho2
    · exact absurd (by rw [e1]) hg
    · exact ⟨o2, ho2, e1, e2⟩

theorem RLev.Den.dropStr {L : List NumObj} {A B : List StrObj} {o : StrObj} {e : RLev} {v : Entry}
    (h : e.Den ⟨L, A ++ o :: B⟩ v) (hg : ∀ g ∈ e.v.toList ++ e.arr.map (·.2.v), g ≠ .str o.hb.pay) :
    e.Den ⟨L, A ++ B⟩ v := by
  refine ⟨?_, forall₂_imp_mem (fun bn hbn iv hh => ⟨hh.1, hh.2.dropStr (hg _ (List.mem_append_right _
    (List.mem_map.mpr ⟨bn, hbn, rfl⟩)))⟩) h.arr⟩
  have hv := h.val
  have hg' : ∀ g ∈ e.v.toList, g ≠ .str o.hb.pay := fun g hg1 => hg g (List.mem_append_left _ hg1)
  revert hv hg'
  generalize e.v = a; generalize v.val = b
  intro hv hg'
  cases hv with
  | none => exact .none
  | some r => exact .some (r.dropStr (hg' _ (by simp)))

/-- **The last reference to a string dropped** (ghost only): the handle
`.str p` leaves `hs` and `o` leaves the ghost; its two blocks are now fresh
to the state. -/
theorem DcAt.dropStr {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {A B : List StrObj} {o : StrObj}
    (h : DcAt S M H F L C G (.str o.hb.pay :: hs) st) (he : G.strs = A ++ o :: B)
    (h1 : o.refs = 1) :
    DcAt S M H F L C (G.dropStr A B) hs st ∧ DcFresh H F L (G.dropStr A B) o.hb ∧
      DcFresh H F L (G.dropStr A B) o.tb := by
  have hom : o ∈ G.strs := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
  have hi := h.heap.heap
  have hp := G.blocks_perm_drop he
  have hnd : ([o.hb, o.tb] ++ (G.dropStr A B).blocks).Nodup := hp.nodup_iff.mp h.nodup
  have hsub : ∀ c ∈ (G.dropStr A B).blocks, c ∈ G.blocks := fun c hc =>
    hp.mem_iff.mpr (List.mem_append_right _ hc)
  have hbG := G.str_mem hom
  have hss := h.str_ne_str he
  have hcnt := h.den.strRefs o hom
  rw [h1, count_cons_self] at hcnt
  have hne : ∀ g ∈ G.vals ++ hs, g ≠ .str o.hb.pay := fun g hg e => by
    subst e; have := List.count_pos_iff.mpr hg; omega
  have hvs : ∀ g ∈ G.vals, g ≠ .str o.hb.pay := fun g hg => hne g (List.mem_append_left _ hg)
  have d := h.den
  refine ⟨⟨h.heap.subRaw hsub (fun _ _ _ _ => rfl), (List.nodup_append.mp hnd).2.1, ?_, ?_, h.glob, h.col⟩,
    ⟨h.heap.raw.live _ hbG.1, fun hm => (List.nodup_append.mp hnd).2.2 _ (by simp) _ hm rfl,
      h.heap.raw.out _ hbG.1⟩,
    ⟨h.heap.raw.live _ hbG.2, fun hm => (List.nodup_append.mp hnd).2.2 _ (by simp) _ hm rfl,
      h.heap.raw.out _ hbG.2⟩⟩
  · exact { h.view with strs := fun o2 ho2 => h.view.strs o2 (by rw [he]; exact mem_split_of ho2) }
  · refine
      { stk := forall₂_imp_mem (fun bg hbg v hh => by
          rw [he] at hh
          exact hh.dropStr (hvs _ (by
            unfold DcG.vals; exact List.mem_append_left _ (List.mem_map.mpr ⟨bg, hbg, rfl⟩)))) d.stk
        regs := fun r hr => forall₂_imp_mem (fun be hbe v hh => by
          rw [he] at hh
          exact hh.dropStr fun g hg => hvs g (by
            unfold DcG.vals
            exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
              List.mem_flatMap.mpr ⟨be, hbe, hg⟩⟩))) (d.regs r hr)
        regsHi := d.regsHi
        hsDen := fun g hg => by
          obtain ⟨v, hv⟩ := d.hsDen g (List.mem_cons_of_mem _ hg)
          rw [he] at hv
          exact ⟨v, hv.dropStr (hne g (List.mem_append_right _ hg))⟩
        live := d.live
        owns := d.owns
        norm := d.norm
        pos := d.pos
        numRefs := fun y hy => by rw [d.numRefs y hy, count_cons_ne _ _ (by simp)]; rfl
        strRefs := fun o2 ho2 => by
          have ho2G : o2 ∈ G.strs := by rw [he]; exact mem_split_of ho2
          have s1 := (h.view.strs o hom).hsz; have s2 := (h.view.strs o2 ho2G).hsz
          rw [d.strRefs o2 ho2G, count_cons_ne _ _ fun e => by
            have e' := GV.str.inj e
            exact live_apart hi (h.heap.raw.live _ (G.str_mem ho2G).1) (h.heap.raw.live _ hbG.1)
              (hss.2 o2 ho2).1 (a := o2.hb.pay) (by simp only [Blk.In, Blk.pay, Blk.fin] at *; omega)
              (by simp only [Blk.In, Blk.pay, Blk.fin] at *; omega)]
          rfl
        lkLen := d.lkLen
        lkIn := d.lkIn
        mz := d.mz
        mo := d.mo
        mt := d.mt
        zv := d.zv
        ov := d.ov
        tv := d.tv
        ibase := d.ibase
        obase := d.obase
        scale := d.scale
        unwind := d.unwind
        lbuf := d.lbuf }

/-- A string's count rewritten keeps every handle's value. -/
theorem HsKeep.withStr {L : List NumObj} {A B : List StrObj} {o o' : StrObj} (hh : o'.hb = o.hb)
    (hs' : o'.s = o.s) (hs : List GV) : HsKeep ⟨L, A ++ o :: B⟩ ⟨L, A ++ o' :: B⟩ hs :=
  fun _ _ _ hv => GV.Den.relist (O := ⟨L, A ++ o :: B⟩) (O' := ⟨L, A ++ o' :: B⟩)
    ⟨fun y hy => ⟨y, hy, rfl, rfl⟩, fun o2 ho2 => by
      rcases mem_split_cases ho2 with e | hm
      · subst e; exact ⟨o', List.mem_append_right _ List.mem_cons_self, by rw [hh], hs'⟩
      · exact ⟨o2, mem_split_of hm, rfl, rfl⟩⟩ hv

/-- The last reference to a string dropped keeps the other handles' values. -/
theorem HsKeep.dropStr {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {A B : List StrObj} {o : StrObj} (d : DcDen L C G (.str o.hb.pay :: hs) st) (he : G.strs = A ++ o :: B)
    (h1 : o.refs = 1) : HsKeep ⟨L, A ++ o :: B⟩ ⟨L, A ++ B⟩ hs := by
  have hom : o ∈ G.strs := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
  have e := d.strRefs o hom
  rw [count_cons_self] at e
  refine fun g hg _ hv => hv.dropStr fun hgx => ?_
  subst hgx
  have := List.count_pos_iff.mpr (List.mem_append_right G.vals hg)
  omega

/-- The registers `dc_free_str` may change. -/
abbrev freeStrClob : List Nat := [10, 14, 15]

/-- A block stays fresh to the state through another block's `free`. -/
theorem DcFresh.afterFree {H : Heap} {F : List Blk} {L : List NumObj} {G : DcG} {b c : Blk}
    {lpre lpost : List Blk} (h : DcFresh H F L G b) (hl : H.live = lpre ++ c :: lpost) (hne : b ≠ c)
    (braw : Nat) (fr : List Blk) : DcFresh ⟨braw, fr, lpre ++ lpost⟩ F L G b := by
  refine ⟨?_, h.notG, h.notNum⟩
  have := h.live; rw [hl] at this
  rcases mem_split_cases this with e | hm
  · exact absurd e hne
  · exact hm

/-- `dc_free_str`'s release (`0x800039bc`): `free (s_ptr)` then `free (s)`,
both blocks fresh to the state, `a4` the header `b1`; on a pending state. -/
theorem free_str_relP {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b1 b2 : Blk} {E : List Blk}
    {W : Nat → Prop} {Φ : Mem → Mem} (hpd : Pend G E W Φ)
    (h : DcAt S (Φ M) H F L C G hs st) (hf1 : DcFresh H F L G b1) (hf2 : DcFresh H F L G b2)
    (hne : b1 ≠ b2) (hsz1 : 8 ≤ b1.sz) (hptr : ldv .ld M b1.pay = BitVec.ofNat 64 b2.pay) {sp : Nat}
    (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (R : Nat → BitVec 64) (h14 : R 14 = BitVec.ofNat 64 b1.pay) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H', Keeps freeStrClob R' R → DcAt S (Φ M') H' F L C G hs st → StkOut sp 32 M' M →
      (∀ c, DcFresh H F L G c → c ≠ b1 → c ≠ b2 → DcFresh H' F L G c ∧
        ∀ a, c.In a → imgM M' a = imgM M a) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x800039bc#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have fbb := h.heap.heap.blk (List.mem_append_right _ hf1.live)
  have hblo : 2147603920 ≤ b1.h := fbb.lo
  have hbhi : b1.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : b1.h % 16 = 0 := fbb.al
  have hpl : 2147603936 ≤ b1.pay ∧ b1.pay + 8 ≤ 2273312768 ∧ b1.pay % 16 = 0 := by
    simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  bc_run hlive hS [h14, hptr, h2] at 0x80000a0c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hP : ∀ a, frameIn sp 32 a → OutHeap a ∧ ¬ DcGlob a := fun a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have hM1 : MemOnly (frameIn sp 32) (writeLog (writeLog M [(sp - 32 + 24, 8, R 1)])
      [(sp - 32 + 8, 8, BitVec.ofNat 64 b1.pay)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have h1 := h.outWriteP hpd hM1 hP
  obtain ⟨lpre, lpost, hl2⟩ := List.append_of_mem hf2.live
  refine free_spec hlive (h1.machHeap hpd).heap hl2 _ ?_ ?_ fun R1 M2 hk1 hp => ?_
  · bsimp []
  · bsimp []
  have h2' := h1.freeP hpd hf2 hl2 hp
  have hf1' := hf1.afterFree hl2 hne H.braw (b2 :: H.free)
  have hfm : ∀ o, o + 8 ≤ 32 → ldv .ld M2 (sp - 32 + o) = ldv .ld (writeLog (writeLog M
      [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 b1.pay)]) (sp - 32 + o) := fun o ho =>
    ldv_congr .ld fun j hj => hp.frame _ (OutHeap.not_alloc (h1.machHeap hpd).heap (outHeap_of_ge (by
      simp only [heapEnd, widthOfM] at hj ⊢; omega)))
  have q8 : ldv .ld M2 (sp - 32 + 8) = BitVec.ofNat 64 b1.pay := by
    rw [hfm 8 (by omega), ldv_store_hit]
  have q24 : ldv .ld M2 (sp - 32 + 24) = R 1 := by
    rw [hfm 24 (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  bsimp []
  bc_run hlive hS [q2, q8, q24] at 0x80000a0c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  obtain ⟨lpre2, lpost2, hl3⟩ := List.append_of_mem hf1'.live
  refine free_spec hlive (h2'.machHeap hpd).heap hl3 _ ?_ ?_ fun R2 M3 hk2 hp2 => ?_
  · bsimp []
  · bsimp []; exact hal
  have h3 := h2'.freeP hpd hf1' hl3 hp2
  refine hk R2 M3 _ ?_ h3 (fun a ho hg hf => ?_) fun c hc n1 n2 =>
    ⟨(hc.afterFree hl2 n2 _ _).afterFree hl3 n1 _ _, fun a hca => ?_⟩
  · refine (hk2.mono (by decide)).trans ?_
    refine Keeps.restore (by rw [h2]; congr 1; omega) ?_
    refine Keeps.restore rfl ?_
    refine Keeps.upd _ (by decide) ?_
    exact (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  · rw [hp2.frame a (OutHeap.not_alloc (h2'.machHeap hpd).heap ho), hp.frame a (OutHeap.not_alloc (h1.machHeap hpd).heap ho)]
    exact hM1 a hf
  · have hin := live_in_heap h.heap.heap hc.live hca
    rw [hp2.frame a (live_not_alloc (h2'.machHeap hpd).heap (hc.afterFree hl2 n2 _ _).live hca),
      hp.frame a (live_not_alloc (h1.machHeap hpd).heap hc.live hca)]
    exact hM1 a fun hf => by simp only [frameIn, heapStart, heapEnd] at hf hin; omega

/-- `dc_free_str`'s release (`0x800039bc`): `free (s_ptr)` then `free (s)`,
both blocks fresh to the state, `a4` the header `b1`. -/
theorem free_str_rel {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b1 b2 : Blk}
    (h : DcAt S M H F L C G hs st) (hf1 : DcFresh H F L G b1) (hf2 : DcFresh H F L G b2)
    (hne : b1 ≠ b2) (hsz1 : 8 ≤ b1.sz) (hptr : ldv .ld M b1.pay = BitVec.ofNat 64 b2.pay) {sp : Nat}
    (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (R : Nat → BitVec 64) (h14 : R 14 = BitVec.ofNat 64 b1.pay) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H', Keeps freeStrClob R' R → DcAt S M' H' F L C G hs st → StkOut sp 32 M' M →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x800039bc#64 R M :=
  free_str_relP hlive (Pend.id G) (M := M) h hf1 hf2 hne hsz1 hptr hsf hab R h14 h2 hal
    fun R' M' H' k1 k2 k3 _ => hk R' M' H' k1 k2 k3

/-- **`dc_free_str (&s)`** at `0x800039a4` on a handle `.str p` held in the
slot `q`, on a pending state: one reference fewer, or the string's two
blocks freed. -/
theorem dc_free_str_specP {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat} {E : List Blk}
    {W : Nat → Prop} {Φ : Mem → Mem} (hpd : Pend G E W Φ)
    (h : DcAt S (Φ M) H F L C G (.str p :: hs) st) {q sp : Nat} (hq : PtrSlot S q)
    (hw : ldv .ld M q = BitVec.ofNat 64 p) (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' G', Keeps freeStrClob R' R → SameNodes G G' → DcAt S (Φ M') H' F L C G' hs st →
      StkOut sp 32 M' M →
      (∀ c, DcFresh H F L G c → DcFresh H' F L G' c ∧ ∀ a, c.In a → imgM M' a = imgM M a) →
      HsKeep ⟨L, G.strs⟩ ⟨L, G'.strs⟩ hs →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x800039a4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  obtain ⟨v, hv⟩ := h.den.hsDen _ List.mem_cons_self
  obtain ⟨o, ho, e1⟩ : ∃ o ∈ G.strs, o.hb.pay = p := by
    cases v with
    | str s => obtain ⟨o, ho, e1, -⟩ := hv; exact ⟨o, ho, e1⟩
    | num n => exact hv.elim
  obtain ⟨A, B, he⟩ := List.append_of_mem ho
  subst e1
  have hso := h.view.strs o ho
  have hsz := hso.hsz
  have hoE : ∀ x, o.hb.In x → ¬ W x := fun x hx => hpd.not_win h.heap.heap (h.pendLive hpd).1
    (h.heap.raw.live _ (G.str_mem ho).1) (fun he => (hpd.nstr _ he o ho).1 rfl) hx
  have fbb := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live _ (G.str_mem ho).1))
  have hblo : 2147603920 ≤ o.hb.h := fbb.lo
  have hbhi : o.hb.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : o.hb.h % 16 = 0 := fbb.al
  have hpl : 2147603936 ≤ o.hb.pay ∧ o.hb.pay + 24 ≤ 2273312768 ∧ o.hb.pay % 16 = 0 := by
    simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  have hcnt := h.den.strRefs o ho
  rw [count_cons_self] at hcnt
  have hrf : ldv .lw M (o.hb.pay + 16) = BitVec.ofNat 64 o.refs :=
    (ldv_congr .lw fun j hj => (hpd.out M _ (hoE _ (by
      simp only [Blk.In, Blk.pay, Blk.fin, widthOfM] at hj ⊢; omega))).symm).trans hso.refs
  have hrl := hso.refsLt
  have wp : BitVec.ofNat 64 o.refs + 18446744073709551615#64 = BitVec.ofNat 64 (o.refs - 1) :=
    word_pred (by omega)
  have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (o.refs - 1))) =
      BitVec.ofNat 64 (o.refs - 1) := sxw_ofNat (by omega)
  have hv1 : (BitVec.ofNat 64 (o.refs - 1)).toNat % 2 ^ 32 = o.refs - 1 := toNat_ofNat_mod32 (by omega)
  have hm : MemOnly o.hb.In (writeLog M [(o.hb.pay + 16, 4, BitVec.ofNat 64 (o.refs - 1))]) M :=
    fun a ha => MemOnly.store M _ 4 _ a fun hh => ha (by simp only [Blk.In, Blk.pay, Blk.fin] at hh ⊢; omega)
  have hout : ∀ a, OutHeap a → imgM (writeLog M [(o.hb.pay + 16, 4, BitVec.ofNat 64 (o.refs - 1))]) a =
      imgM M a := fun a ho' => hm a fun hin => ho'.1 (live_in_heap h.heap.heap
        (h.heap.raw.live _ (G.str_mem ho).1) hin)
  rcases (show o.refs = 1 ∨ 2 ≤ o.refs by have := hso.refsPos; omega) with h1 | h2r
  · -- the last reference: both blocks freed
    have hz : BitVec.ofNat 64 (o.refs - 1) = 0#64 := by rw [h1]
    rw [hz] at hm hout wq
    bc_run hlive hS [h10, hw, hrf, wp, wq, hz] at 0x800039bc
    all_goals first | exact hq.acc | skip
    obtain ⟨h0, fh, ft⟩ := h.dropStr he h1
    have h1' := h0.rawWriteP (hpd.dropStr he) fh hm
    have hss := h.str_ne_str he
    have hptr : ldv .ld (writeLog M [(o.hb.pay + 16, 4, 0#64)]) o.hb.pay = BitVec.ofNat 64 o.tb.pay := by
      rw [ldv_ld_miss _ _ (by omega)]
      have e := ldv_congr (a := o.hb.pay + 0) .ld fun j hj => (hpd.out M _ (hoE _ (by
        simp only [Blk.In, Blk.pay, Blk.fin, widthOfM] at hj ⊢; omega))).symm
      simp only [Nat.add_zero] at e
      exact e.trans hso.ptr
    refine free_str_relP hlive (hpd.dropStr he) h1' fh ft (Ne.symm hss.1) (by omega) hptr hsf (by simp only [heapEnd]; omega)
      _ (by bsimp []) (by bsimp [h2]) (by bsimp []; exact hal) fun R' M' H' hk1 h' hfr hfc => ?_
    have hperm := DcG.blocks_perm_drop he
    refine hk R' M' H' (G.dropStr A B) (hk1.trans (by keeps_tac Keeps.refl _ _)) ⟨rfl, rfl, rfl⟩ h'
      (fun a ho' hg hf => ?_) (fun c hc => ?_) (by rw [he]; exact HsKeep.dropStr h.den he h1)
    · rw [hfr a ho' hg hf, hout a ho']
    · have hcG : ∀ b ∈ G.blocks, c ≠ b := fun b hb e => hc.notG (e ▸ hb)
      obtain ⟨hc', hcb⟩ := hfc c ⟨hc.live, fun hm => hc.notG (hperm.mem_iff.mpr
          (List.mem_append_right _ hm)), hc.notNum⟩
        (hcG _ (G.str_mem ho).1) (hcG _ (G.str_mem ho).2)
      refine ⟨hc', fun a hca => ?_⟩
      rw [hcb a hca]
      exact hm a fun hb => live_apart h.heap.heap hc.live (h.heap.raw.live _ (G.str_mem ho).1)
        (hcG _ (G.str_mem ho).1) hca hb
  · -- one reference fewer
    have hpos : ¬ (BitVec.ofNat 64 (o.refs - 1)).toInt ≤ (0#64).toInt := by
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [BitVec.toInt_zero]
      split <;> omega
    bc_run hlive hS [h10, hw, hrf, wp, wq] at 0x800039b4
    all_goals first | exact hq.acc | skip
    refine st_800039b4 hlive (fun hc => absurd hc ?_) fun _ => ?_
    · bsimp []; exact hpos
    bc_run hlive hS [h10, hw, hrf, wp, wq]
    refine hk _ _ H (G.withStr A B (o.withRefs (o.refs - 1))) (by keeps_tac Keeps.refl _ _)
      ⟨rfl, rfl, rfl⟩ ((h.decStr he h2r hv1).congr (hpd.store M _ (.inl rfl) fun x hx => hoE x (by
        simp only [Blk.In, Blk.pay, Blk.fin] at hx ⊢; omega))) (fun a ho' hg hf => hout a ho')
      (fun c hc => ⟨⟨hc.live, by rw [G.withStr_blocks (o' := o.withRefs (o.refs - 1)) he rfl rfl]; exact hc.notG, hc.notNum⟩,
        fun a hca => hm a fun hb => live_apart h.heap.heap hc.live
          (h.heap.raw.live _ (G.str_mem ho).1) (fun e => hc.notG (e ▸ (G.str_mem ho).1)) hca hb⟩)
      (by rw [he]; exact HsKeep.withStr (o := o) (o' := o.withRefs (o.refs - 1)) rfl rfl hs)

/-- **`dc_free_str (&s)`** at `0x800039a4` on a handle `.str p` held in the
slot `q`: one reference fewer, or the string's two blocks freed. -/
theorem dc_free_str_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat}
    (h : DcAt S M H F L C G (.str p :: hs) st) {q sp : Nat} (hq : PtrSlot S q)
    (hw : ldv .ld M q = BitVec.ofNat 64 p) (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' G', Keeps freeStrClob R' R → SameNodes G G' → DcAt S M' H' F L C G' hs st →
      StkOut sp 32 M' M → DW live S Q (R 1) R' M') :
    DW live S Q 0x800039a4#64 R M :=
  dc_free_str_specP hlive (Pend.id G) (M := M) h hq hw hsf hab R h10 h2 hal
    fun R' M' H' G' k1 k2 k3 k4 _ _ => hk R' M' H' G' k1 k2 k3 k4

end Dc.Mach
