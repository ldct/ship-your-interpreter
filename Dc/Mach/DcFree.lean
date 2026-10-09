import Dc.Mach.DcRefOps
import Dc.Mach.Bc.Free

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
theorem DcAt.vals_ne {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st) (h1 : x.rep.refs = 1) :
    (∀ g ∈ G.vals ++ hs, g ≠ .num x.rep.p) ∧ C.cnt x.rep.p = 0 := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have e := h.den.numRefs x hx
  rw [count_cons_self] at e
  refine ⟨fun g hg hgx => ?_, by omega⟩
  subst hgx
  have := List.count_pos_iff.mpr hg
  omega

/-- **The last reference released**: the handle `.num p` leaves `hs`, the
object leaves the number heap; the state's blocks and dc's globals keep
their bytes. -/
theorem DcAt.relNum {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st) (h1 : x.rep.refs = 1)
    (hb : BcHeap S (G.raws M) M' H' (x.sb :: F) (L1 ++ L2))
    (hag : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a)
    (hgl : ∀ a, DcGlob a → imgM M' a = imgM M a) :
    DcAt S M' H' (x.sb :: F) (L1 ++ L2) C G hs st := by
  obtain ⟨hne, hc0⟩ := h.vals_ne h1
  have hvs : ∀ g ∈ G.vals, g ≠ .num x.rep.p := fun g hg => hne g (List.mem_append_left _ hg)
  have hpn := h.heap.p_ne_all
  have d := h.den
  have hcx : ∀ c ∈ [C.z, C.o, C.t], c ≠ x := fun c hc e => by
    subst e
    have : 0 < C.cnt c.rep.p := by
      unfold BcConsts.cnt; exact List.countP_pos_iff.mpr ⟨c, hc, by simp⟩
    omega
  have hmem : ∀ c ∈ [C.z, C.o, C.t], c ∈ L1 ++ x :: L2 → c ∈ L1 ++ L2 := fun c hc hm => by
    rcases mem_split_cases hm with e | hm
    · exact absurd e (hcx c hc)
    · exact hm
  refine ⟨?_, h.nodup, h.view.frame hag hgl, ?_, h.glob, h.col⟩
  · exact hb.subRaw (fun c hc => hc) fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm
  · refine
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
        mz := hmem _ (by simp) d.mz
        mo := hmem _ (by simp) d.mo
        mt := hmem _ (by simp) d.mt
        zv := d.zv
        ov := d.ov
        ibase := d.ibase
        obase := d.obase
        scale := d.scale
        unwind := d.unwind
        lbuf := d.lbuf }

/-- **One reference fewer**: the handle `.num p` leaves `hs`, `n_refs` one
less; the state's blocks and dc's globals keep their bytes. -/
theorem DcAt.decNum {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st) (h2 : 2 ≤ x.rep.refs)
    (hb : BcHeap S (G.raws M) M' H F (L1 ++ x.decRef :: L2))
    (hag : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a)
    (hgl : ∀ a, DcGlob a → imgM M' a = imgM M a) :
    DcAt S M' H F (L1 ++ x.decRef :: L2) (C.subst x x.decRef) G hs st := by
  classical
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hp' : x.decRef.rep.p = x.rep.p := rfl
  have hn' : x.decRef.rep.num = x.rep.num := rfl
  have hsub : ∀ ss : List StrObj, DObjs.Sub ⟨L1 ++ x :: L2, ss⟩ ⟨L1 ++ x.decRef :: L2, ss⟩ := fun ss =>
    ⟨fun y hy => ⟨_, BcConsts.subst_mem (x' := x.decRef) hy, ite_rep hp' hn' y _⟩,
      fun o ho => ⟨o, ho, rfl, rfl⟩⟩
  have hne := h.heap.p_ne_all
  have hcz : ∀ (y : NumObj) [Decidable (y = x)], y ∈ L1 ++ x :: L2 →
      (if y = x then x.decRef else y) ∈ L1 ++ x.decRef :: L2 := fun y _ hy => BcConsts.subst_mem hy
  have hv0 := h.view.frame hag hgl
  have d := h.den
  refine ⟨?_, h.nodup, ?_, ?_, h.glob, h.col⟩
  · exact hb.subRaw (fun c hc => hc) fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm
  · refine { hv0 with zw := ?_, ow := ?_, tw := ?_ }
    · simp only [BcConsts.subst, (ite_rep hp' hn' _ _).1]; exact hv0.zw
    · simp only [BcConsts.subst, (ite_rep hp' hn' _ _).1]; exact hv0.ow
    · simp only [BcConsts.subst, (ite_rep hp' hn' _ _).1]; exact hv0.tw
  · refine { d with
      stk := d.stk.imp fun hh => hh.relist (hsub _)
      regs := fun r hr => (d.regs r hr).imp fun hh => hh.relist (hsub _)
      hsDen := fun g hg => ?_
      owns := fun y hy => ?_
      norm := fun y hy => ?_
      pos := fun y hy => ?_
      numRefs := fun y hy => ?_
      strRefs := fun o ho => ?_
      mz := hcz _ d.mz
      mo := hcz _ d.mo
      mt := hcz _ d.mt
      zv := by simp only [BcConsts.subst, (ite_rep hp' hn' _ _).2]; exact d.zv
      ov := by simp only [BcConsts.subst, (ite_rep hp' hn' _ _).2]; exact d.ov }
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
      · show x.rep.refs - 1 = (G.vals ++ hs).count (.num x.rep.p) + C.cnt x.rep.p
        have := d.numRefs x hx; rw [count_cons_self] at this; omega
      · rw [d.numRefs y (mem_split_of hy), count_cons_ne _ _ fun e => hne y hy (GV.num.inj e).symm]
    · rw [d.strRefs o ho, count_cons_ne _ _ (by simp)]

/-- Different owners of the heap have different digit buffers. -/
theorem db_ne_of_owns {L1 L2 : List NumObj} {x y : NumObj} (hd : (objBlocks (L1 ++ x :: L2)).Nodup)
    (hy : y ∈ L1) (hoy : y.Owns) (hox : x.Owns) : y.db ≠ x.db := by
  rw [objBlocks_append] at hd
  refine nodup_app_ne hd (mem_objBlocks_db hy hoy) ?_
  rw [objBlocks_cons]; exact List.mem_append_left _ (by rw [NumObj.blocks_own hox]; simp)

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
    DW live S Q 0x80002ba0#64 R M := by
  obtain ⟨v, hv⟩ := h.den.hsDen _ List.mem_cons_self
  obtain ⟨x, hx, e1⟩ : ∃ x ∈ L, x.rep.p = p := by
    cases v with
    | num n => obtain ⟨x, hx, e1, -⟩ := hv; exact ⟨x, hx, e1⟩
    | str s => exact hv.elim
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hx
  subst e1
  have hi := h.heap.heap
  have hql := hq.lo
  simp only [heapEnd] at hqh hab
  have hsl : ∀ a, slotBytes q a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have hfl : ∀ a, frameIn sp 32 a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨outHeap_of_ge (by simp only [heapEnd, frameIn] at ha ⊢; omega), fun hg => by
      have := hg.lt; simp only [heapStart, frameIn] at this ha; omega⟩
  have hheap : ∀ b ∈ H.live, ∀ a, b.In a → ¬ slotBytes q a := fun b hb a ha hs =>
    (hsl a hs).1.1 (live_in_heap hi hb ha)
  have hrefs : 1 ≤ x.rep.refs := by
    have := h.den.numRefs x hx; rw [count_cons_self] at this; omega
  have e : FreeEntry S (G.raws M) M H F L1 L2 x q sp :=
    { heap := h.heap
      refs := hrefs
      slot := hq
      off :=
        { alloc := fun a ha => OutHeap.not_alloc hi (hsl a ha).1
          blocks := fun b hb a ha hba => hheap b (h.heap.owned_live (List.mem_append_left _ hb)) a hba ha
          glob := by simp only [bcFreeAddr]; omega
          frame := hqf
          raw := fun b hb a ha hba => hheap b (h.heap.raw.live b hb) a hba ha }
      word := hw
      stack := hsf
      above := by simp only [heapEnd]; omega
      noView := fun _ hox y hy => db_ne_of_owns (List.nodup_append.mp h.heap.distinct).2.1 hy
        (h.den.owns y (List.mem_append_left _ hy)) hox }
  have hGb : ∀ a, InBlocks G.blocks a → ¬ AllocByte H a ∧ ¬ x.sb.In a ∧ ¬ slotBytes q a ∧
      ¬ frameIn sp 32 a ∧ ¬ bcFreeBytes a := fun a ha => by
    obtain ⟨c, hc, hca⟩ := ha
    have hcl := h.heap.raw.live c hc
    have hxb := h.heap.blocks x hx
    have hin := live_in_heap hi hcl hca
    refine ⟨live_not_alloc hi hcl hca, fun hxa => live_apart hi hcl hxb.sLive
      (h.heap.raw_ne hc (List.mem_append_right _ (mem_objBlocks hx))) hca hxa,
      fun hs => hheap c hcl a hca hs, fun hf => ?_, fun hf => ?_⟩
    · simp only [frameIn, heapStart, heapEnd] at hf hin; omega
    · have e : bcFreeAddr = 0x8001cdb0 := rfl
      simp only [bcFreeBytes, heapStart, heapEnd] at hf hin; omega
  have hGg : ∀ a, DcGlob a → ¬ AllocByte H a ∧ ¬ x.sb.In a ∧ ¬ slotBytes q a ∧
      ¬ frameIn sp 32 a ∧ ¬ bcFreeBytes a := fun a ha => by
    have hlt := ha.lt
    refine ⟨OutHeap.not_alloc hi ha.outHeap, fun hxa => ?_, fun hs => (hsl a hs).2 ha,
      fun hf => (hfl a hf).2 ha, fun hf => ?_⟩
    · have := live_in_heap hi (h.heap.blocks x hx).sLive hxa; omega
    · have := ha.outHeap; simp only [OutHeap] at this; exact this.2.2 hf
  refine st_80002ba0 hlive (bc_free_num_spec hlive e R h10 h2 hal ⟨fun h2r R' M' hk1 hb hz hm => ?_,
    fun h1r R' M' H' hk1 hp => ?_⟩)
  · have hm' : ∀ a, ¬ (refsBytes x.rep a ∨ slotBytes q a) → imgM M' a = imgM M a := hm
    have hrx : ∀ a, refsBytes x.rep a → x.sb.In a := fun a ha => by
      have hxb := h.heap.blocks x hx
      have := hxb.sSz; have := hxb.sPay
      simp only [refsBytes, Blk.In, Blk.pay, Blk.fin] at ha this ⊢; omega
    refine hk R' M' H F _ _ hk1 (h.decNum h2r hb (fun a ha => hm' a ?_) (fun a ha => hm' a ?_)) hz
      fun a ho hg hf hs => hm' a ?_
    · rintro (hr | hs); exact (hGb a ha).2.1 (hrx a hr); exact (hGb a ha).2.2.1 hs
    · rintro (hr | hs); exact (hGg a ha).2.1 (hrx a hr); exact (hGg a ha).2.2.1 hs
    · rintro (hr | hs')
      · exact ho.1 (live_in_heap hi (h.heap.blocks x hx).sLive (hrx a hr))
      · exact hs hs'
  · have hfr := hp.frame
    refine hk R' M' H' _ _ _ hk1 (h.relNum h1r hp.heap (fun a ha => hfr a ?_) (fun a ha => hfr a ?_))
      hp.slot fun a ho hg hf hs => hfr a ?_
    · obtain ⟨n1, n2, n3, n4, n5⟩ := hGb a ha
      rintro (c | c | c | c | c) <;> contradiction
    · obtain ⟨n1, n2, n3, n4, n5⟩ := hGg a ha
      rintro (c | c | c | c | c) <;> contradiction
    · rintro (c | c | c | c | c)
      · exact OutHeap.not_alloc hi ho c
      · exact ho.1 (live_in_heap hi (h.heap.blocks x hx).sLive c)
      · exact hs c
      · exact hf c
      · exact ho.2.2 c

end Dc.Mach
