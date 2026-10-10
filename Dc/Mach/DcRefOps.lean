import Dc.Mach.DcRefs
import Dc.Mach.Bc.KaraHeap
import Dc.Mach.Bc.RaiseModHeap

/-!
# One more reference (M9)

`dc_dup_num` and `dc_dup_str` increment a count and hand the caller a new
handle. On the state:

- `GV.Den.relist`, `RLev.Den.relist`: denotations carried to new object
  lists that keep every pointer and value.
- `BcConsts.subst`: the constants with a bumped object replaced.
- `DcAt.bumpNum`: `n_refs` of a heap number incremented, the handle
  `.num p` added to `hs`.
- `DcAt.bumpStr`: `s_refs` of a string incremented, the handle `.str p`
  added to `hs`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- Every object of `O` has a counterpart in `O'` with its pointer and value. -/
structure DObjs.Sub (O O' : DObjs) : Prop where
  nums : ∀ y ∈ O.L, ∃ y' ∈ O'.L, y'.rep.p = y.rep.p ∧ y'.rep.num = y.rep.num
  strs : ∀ o ∈ O.ss, ∃ o' ∈ O'.ss, o'.hb.pay = o.hb.pay ∧ o'.s = o.s

theorem GV.Den.relist {O O' : DObjs} (hs : O.Sub O') {g : GV} {v : Val} (h : g.Den O v) :
    g.Den O' v := by
  cases g <;> cases v <;> simp only [GV.Den] at h ⊢
  · obtain ⟨y, hy, e1, e2⟩ := h
    obtain ⟨y', hy', f1, f2⟩ := hs.nums y hy
    exact ⟨y', hy', f1.trans e1, f2.trans e2⟩
  · obtain ⟨o, ho, e1, e2⟩ := h
    obtain ⟨o', ho', f1, f2⟩ := hs.strs o ho
    exact ⟨o', ho', f1.trans e1, f2.trans e2⟩

theorem RLev.Den.relist {O O' : DObjs} (hs : O.Sub O') {e : RLev} {v : Entry} (h : e.Den O v) :
    e.Den O' v := by
  refine ⟨?_, h.arr.imp fun hh => ⟨hh.1, hh.2.relist hs⟩⟩
  have hv := h.val
  revert hv
  generalize e.v = a; generalize v.val = b
  intro hv
  cases hv with
  | none => exact .none
  | some r => exact .some (r.relist hs)

open Classical in
/-- The constants with `x` replaced by `x'`. -/
noncomputable def BcConsts.subst (C : BcConsts) (x x' : NumObj) : BcConsts :=
  ⟨if C.z = x then x' else C.z, if C.o = x then x' else C.o, if C.t = x then x' else C.t, C.lk⟩

/-- Replacing `x` by an object with its pointer and value. -/
theorem ite_rep {x x' : NumObj} (hp : x'.rep.p = x.rep.p) (hn : x'.rep.num = x.rep.num)
    (y : NumObj) (d : Decidable (y = x)) :
    (@ite _ (y = x) d x' y).rep.p = y.rep.p ∧ (@ite _ (y = x) d x' y).rep.num = y.rep.num := by
  cases d with
  | isFalse _ => exact ⟨rfl, rfl⟩
  | isTrue e => subst e; exact ⟨hp, hn⟩

theorem BcConsts.subst_cnt (C : BcConsts) {x x' : NumObj} (hp : x'.rep.p = x.rep.p)
    (hn : x'.rep.num = x.rep.num) (p : Nat) : (C.subst x x').cnt p = C.cnt p := by
  unfold BcConsts.subst BcConsts.cnt
  simp only [List.countP_cons, List.countP_nil, (ite_rep hp hn _ _).1]

theorem BcConsts.subst_mem {x x' y : NumObj} {L1 L2 : List NumObj} [Decidable (y = x)]
    (hy : y ∈ L1 ++ x :: L2) : (if y = x then x' else y) ∈ L1 ++ x' :: L2 := by
  split
  · exact List.mem_append_right _ List.mem_cons_self
  · rename_i e
    rcases List.mem_append.mp hy with h1 | h1
    · exact List.mem_append_left _ h1
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact absurd h2 e
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)

theorem mem_split_cases {α : Type} {L1 L2 : List α} {x y : α} (h : y ∈ L1 ++ x :: L2) :
    y = x ∨ y ∈ L1 ++ L2 := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr h)

theorem mem_split_of {α : Type} {L1 L2 : List α} {x y : α} (h : y ∈ L1 ++ L2) : y ∈ L1 ++ x :: L2 := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h
  · exact .inl h
  · exact .inr (.inr h)

theorem count_cons_ne {g a : GV} (vs hs : List GV) (hne : a ≠ g) :
    (vs ++ a :: hs).count g = (vs ++ hs).count g := by
  simp only [List.count_append, List.count_cons, beq_iff_eq, hne, ite_false]; omega

theorem count_cons_self (g : GV) (vs hs : List GV) :
    (vs ++ g :: hs).count g = (vs ++ hs).count g + 1 := by
  simp only [List.count_append, List.count_cons, beq_self_eq_true, ite_true]; omega

/-- **`n_refs` of a heap number incremented**: the handle `.num p` joins
`hs`; the constants follow the bumped object. -/
theorem DcAt.bumpNum {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F (L1 ++ x :: L2) C G hs st) (hhs : hs.length ≤ 2 ^ 30)
    {v : BitVec 64} (hv : v.toNat % 2 ^ 32 = x.rep.refs + 1) :
    DcAt S (writeLog M [(x.rep.p + 12, 4, v)]) H F (L1 ++ x.withRefs (x.rep.refs + 1) :: L2)
      (C.subst x (x.withRefs (x.rep.refs + 1))) G (.num x.rep.p :: hs) st := by
  classical
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hi := h.heap.heap
  have hb := h.heap.blocks x hx
  have hsz := hb.sSz
  have hsp := hb.sPay
  have hrl := h.numRefs_lt hhs hx
  have hb1 := h.heap.setRefs hv hrl
  have hin : ∀ a, ¬ x.sb.In a → imgM (writeLog M [(x.rep.p + 12, 4, v)]) a = imgM M a :=
    fun a ha => MemOnly.store M _ 4 v a fun hh => ha (by
      simp only [Blk.In, Blk.fin, Blk.pay] at hh ⊢; rw [hsp] at hh; simp only [Blk.pay] at hh; omega)
  have hsbo : x.sb ∈ F ++ objBlocks (L1 ++ x :: L2) :=
    List.mem_append_right _ (mem_objBlocks hx |> fun h => by exact h)
  have hblk : ∀ a, InBlocks G.blocks a → imgM (writeLog M [(x.rep.p + 12, 4, v)]) a = imgM M a :=
    fun a ⟨c, hc, hca⟩ => hin a fun hxa =>
      live_apart hi (h.heap.raw.live c hc) hb.sLive (h.heap.raw_ne hc hsbo) hca hxa
  have hgl : ∀ a, DcGlob a → imgM (writeLog M [(x.rep.p + 12, 4, v)]) a = imgM M a :=
    fun a ha => hin a fun hxa => by
      have := live_in_heap hi hb.sLive hxa; have := ha.lt; omega
  have hp' : (x.withRefs (x.rep.refs + 1)).rep.p = x.rep.p := rfl
  have hn' : (x.withRefs (x.rep.refs + 1)).rep.num = x.rep.num := rfl
  have hsub : ∀ ss : List StrObj, DObjs.Sub ⟨L1 ++ x :: L2, ss⟩ ⟨L1 ++ x.withRefs (x.rep.refs + 1) :: L2, ss⟩ := fun ss =>
    ⟨fun y hy => ⟨_, BcConsts.subst_mem (x' := x.withRefs (x.rep.refs + 1)) hy, ite_rep hp' hn' y _⟩,
      fun o ho => ⟨o, ho, rfl, rfl⟩⟩
  have hne := h.heap.p_ne_all
  have hcz : ∀ (y : NumObj) [Decidable (y = x)], y ∈ L1 ++ x :: L2 →
      (if y = x then x.withRefs (x.rep.refs + 1) else y) ∈ L1 ++ x.withRefs (x.rep.refs + 1) :: L2 := fun y _ hy => BcConsts.subst_mem hy
  have hv0 := h.view.frame hblk hgl
  have d := h.den
  refine ⟨?_, h.nodup, ?_, ?_, h.glob, h.col⟩
  · exact hb1.subRaw (fun c hc => hc) fun c hc a ha => (hblk a ⟨c, hc, ha⟩).symm
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
      lkIn := fun p hp => by
        obtain ⟨y, hy, e⟩ := d.lkIn p hp
        exact ⟨_, hcz y hy, (ite_rep hp' hn' y _).1.trans e⟩
      mz := hcz _ d.mz
      mo := hcz _ d.mo
      mt := hcz _ d.mt
      zv := by simp only [BcConsts.subst, (ite_rep hp' hn' _ _).2]; exact d.zv
      ov := by simp only [BcConsts.subst, (ite_rep hp' hn' _ _).2]; exact d.ov }
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨.num x.rep.num, x.withRefs (x.rep.refs + 1), List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩
      · obtain ⟨w, hw⟩ := d.hsDen g hg; exact ⟨w, hw.relist (hsub _)⟩
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
      · show x.rep.refs + 1 = (G.vals ++ .num x.rep.p :: hs).count (.num x.rep.p) + C.cnt x.rep.p
        rw [count_cons_self]; have := d.numRefs x hx; omega
      · rw [d.numRefs y (mem_split_of hy), count_cons_ne _ _ fun e => hne y hy (GV.num.inj e).symm]
    · rw [d.strRefs o ho, count_cons_ne _ _ (by simp)]

/-! ## Stores into the state's own blocks -/

/-- **A store confined to a block of the state** keeps the number heap; the
state's blocks are raw blocks, read at the new memory. -/
theorem DcAt.ownWrite {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk}
    (h : DcAt S M H F L C G hs st) (hb : b ∈ G.blocks) (hm : MemOnly b.In M' M) :
    BcHeap S (G.raws M') M' H F L := by
  have hi := h.heap.heap
  have hbl := h.heap.raw.live b hb
  have h0 : BcHeap S ⟨[], M⟩ M H F L := h.heap.subRaw (fun c hc => by cases hc) fun c hc => by cases hc
  have h1 := h0.rawWrite hbl (by
    simp only [List.append_nil]; exact h.heap.raw.out b hb) hm
  exact { h1 with raw := ⟨h.heap.raw.live, h.heap.raw.out, fun _ _ _ _ => rfl⟩ }

/-- Members of two parts of a duplicate-free list differ. -/
theorem nodup_app_ne {α : Type} {l1 l2 : List α} (h : (l1 ++ l2).Nodup) {a b : α} (ha : a ∈ l1)
    (hb : b ∈ l2) : a ≠ b :=
  (List.nodup_append.mp h).2.2 a ha b hb

/-- The ghost with the string list `A ++ o' :: B`. -/
abbrev DcG.withStr (G : DcG) (A B : List StrObj) (o' : StrObj) : DcG := { G with strs := A ++ o' :: B }

theorem DcG.withStr_blocks {G : DcG} {A B : List StrObj} {o o' : StrObj}
    (he : G.strs = A ++ o :: B) (hh : o'.hb = o.hb) (ht : o'.tb = o.tb) :
    (G.withStr A B o').blocks = G.blocks := by
  simp only [DcG.withStr, DcG.blocks, he, List.flatMap_append, List.flatMap_cons, hh, ht]

theorem DcG.withStr_vals (G : DcG) (A B : List StrObj) (o' : StrObj) :
    (G.withStr A B o').vals = G.vals := rfl

/-- The string blocks are none of the stack's or registers' blocks. -/
theorem DcAt.str_ne {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {o : StrObj} (ho : o ∈ G.strs) {c : Blk}
    (hc : c ∈ G.stk.map (·.1) ++ (List.range 256).flatMap (fun r => (G.regs r).flatMap RLev.blocks)) :
    c ≠ o.hb ∧ c ≠ o.tb := by
  have hn := h.nodup
  unfold DcG.blocks at hn
  have hn2 := (List.nodup_append.mp hn).1
  exact ⟨nodup_app_ne hn2 hc (List.mem_flatMap.mpr ⟨o, ho, by simp⟩),
    nodup_app_ne hn2 hc (List.mem_flatMap.mpr ⟨o, ho, by simp⟩)⟩

/-- Another string's blocks are not `o`'s header. -/
theorem DcAt.str_ne_str {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {A B : List StrObj} {o : StrObj} (he : G.strs = A ++ o :: B) :
    o.tb ≠ o.hb ∧ ∀ o2 ∈ A ++ B, o2.hb ≠ o.hb ∧ o2.tb ≠ o.hb := by
  have hn := h.nodup
  unfold DcG.blocks at hn
  have hn3 := (List.nodup_append.mp (List.nodup_append.mp hn).1).2.1
  rw [he] at hn3
  have hp : (A ++ o :: B).flatMap (fun o => [o.hb, o.tb]) |>.Perm
      ([o.hb, o.tb] ++ (A ++ B).flatMap (fun o => [o.hb, o.tb])) := by
    have := (List.perm_middle (a := o) (l₁ := A) (l₂ := B)).flatMap_right (fun o => [o.hb, o.tb])
    simpa using this
  have hn4 := hp.nodup_iff.mp hn3
  have hd := List.nodup_append.mp hn4
  refine ⟨fun e => ?_, fun o2 ho2 => ⟨?_, ?_⟩⟩
  · have := hd.1; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at this
    exact this.1 e.symm
  · exact fun e => hd.2.2 o.hb (by simp) o2.hb (List.mem_flatMap.mpr ⟨o2, ho2, by simp⟩) e.symm
  · exact fun e => hd.2.2 o.hb (by simp) o2.tb (List.mem_flatMap.mpr ⟨o2, ho2, by simp⟩) e.symm

/-- **The view after a store into a string's header block**: the string
becomes `o'` (same blocks), everything else reads the same. -/
theorem DcAt.strView {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {A B : List StrObj} {o o' : StrObj} (he : G.strs = A ++ o :: B)
    (hm : MemOnly o.hb.In M' M) (ho : StrAt M' o') :
    DcView M' (G.withStr A B o') C st := by
  have hi := h.heap.heap
  have hom : o ∈ G.strs := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
  have hhl := h.heap.raw.live _ (G.str_mem hom).1
  have hoff : ∀ c ∈ G.blocks, c ≠ o.hb → ∀ x, c.In x → imgM M' x = imgM M x := fun c hc hne x hx =>
    hm x fun hox => live_apart hi (h.heap.raw.live c hc) hhl hne hx hox
  have hgl : ∀ a, DcGlob a → imgM M' a = imgM M a := fun a ha => hm a fun hox => by
    have := live_in_heap hi hhl hox; have := ha.lt; omega
  have hss := h.str_ne_str he
  have v0 : DcView M { G with strs := [] } C st := { h.view with strs := fun o ho => by cases ho }
  have v1 : DcView M' { G with strs := [] } C st :=
    v0.withChains rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun o ho => by cases ho)
      (fun a ha _ => hgl a ha)
      (stkChain_frame h.view.stk
        (ldv_glob hgl .ld fun j hj => by simp only [widthOfM, DcGlob, dc_addrs] at hj ⊢; omega)
        fun bg hmm x hx => hoff _ (G.stk_mem hmm)
          (h.str_ne hom (List.mem_append_left _ (List.mem_map.mpr ⟨bg, hmm, rfl⟩))).1 x hx)
      fun r hr => regChain_frame (h.view.regs r hr)
        (ldv_glob hgl .ld fun j hj => by simp only [widthOfM, DcGlob, regAddr, dc_addrs] at hj ⊢; omega)
        fun be hmm c hc x hx => by
          have hcr : c ∈ (List.range 256).flatMap (fun r => (G.regs r).flatMap RLev.blocks) :=
            List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, List.mem_flatMap.mpr ⟨be, hmm, hc⟩⟩
          have hcG : c ∈ G.blocks := by
            unfold DcG.blocks
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hcr))
          exact hoff c hcG (h.str_ne hom (List.mem_append_right _ hcr)).1 x hx
  refine { v1 with strs := fun o2 ho2 => ?_ }
  rcases mem_split_cases ho2 with rfl | ho2
  · exact ho
  · have ho2G : o2 ∈ G.strs := by rw [he]; exact mem_split_of ho2
    have hb2 := G.str_mem ho2G
    obtain ⟨n1, n2⟩ := hss.2 o2 ho2
    exact (h.view.strs o2 ho2G).frame (bs := [o2.hb, o2.tb]) (by simp) (by simp) fun x ⟨c, hc, hcx⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hoff _ hb2.1 n1 x hcx
      · exact hoff _ hb2.2 n2 x hcx

/-- `s_refs` of a string written: the object with count `k`. -/
def StrObj.withRefs (o : StrObj) (k : Nat) : StrObj := { o with refs := k }

/-- The string with its count word rewritten. -/
theorem StrAt.setRefs {M : Mem} {o : StrObj} (h : StrAt M o) {v : BitVec 64} {k : Nat}
    (hv : v.toNat % 2 ^ 32 = k) (hk1 : 1 ≤ k) (hk : k < 2 ^ 31)
    (hap : ∀ a, o.tb.In a → ¬ (o.hb.pay + 16 ≤ a ∧ a < o.hb.pay + 16 + 4)) :
    StrAt (writeLog M [(o.hb.pay + 16, 4, v)]) (o.withRefs k) := by
  have hs := h.hsz; have hts := h.tsz
  unfold StrObj.withRefs
  refine
    { ptr := ?_
      len := ?_
      refs := ?_
      bytes := fun i hi => ?_
      nul := ?_
      hsz := hs
      tsz := hts
      byte := h.byte
      refsPos := hk1
      refsLt := hk }
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.ptr
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.len
  · exact ldv_lw_hitN _ rfl hv hk
  · rw [MemOnly.store M _ 4 v _ (hap _ (by
      simp only [Blk.In, Blk.pay, Blk.fin, StrObj.withRefs] at hi ⊢; omega))]
    exact h.bytes i hi
  · rw [MemOnly.store M _ 4 v _ (hap _ (by simp only [Blk.In, Blk.pay, Blk.fin] at hts ⊢; omega))]
    exact h.nul

/-- **`s_refs` of a string of the state rewritten to `k`**, the handles now
`hs'`: the count of `.str p` is `k`, every other count unchanged. -/
theorem DcAt.strRefsTo {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs hs' : List GV} {st : St} {A B : List StrObj} {o : StrObj}
    (h : DcAt S M H F L C G hs st) (he : G.strs = A ++ o :: B) {k : Nat} (hk1 : 1 ≤ k)
    (hk : k < 2 ^ 31) (hcnt : ∀ g, g ≠ .str o.hb.pay → (G.vals ++ hs').count g = (G.vals ++ hs).count g)
    (hkc : k = (G.vals ++ hs').count (.str o.hb.pay))
    (hsD : ∀ g ∈ hs', g = .str o.hb.pay ∨ g ∈ hs)
    {v : BitVec 64} (hv : v.toNat % 2 ^ 32 = k) :
    DcAt S (writeLog M [(o.hb.pay + 16, 4, v)]) H F L C (G.withStr A B (o.withRefs k)) hs' st := by
  have hom : o ∈ G.strs := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
  have hi := h.heap.heap
  have hso := h.view.strs o hom
  have hsz := hso.hsz
  have hm : MemOnly o.hb.In (writeLog M [(o.hb.pay + 16, 4, v)]) M := fun a ha =>
    MemOnly.store M _ 4 v a fun hh => ha (by simp only [Blk.In, Blk.pay, Blk.fin] at hh ⊢; omega)
  have hss := h.str_ne_str he
  have hbG := G.str_mem hom
  have hap : ∀ a, o.tb.In a → ¬ (o.hb.pay + 16 ≤ a ∧ a < o.hb.pay + 16 + 4) := fun a ha hh =>
    live_apart hi (h.heap.raw.live _ hbG.2) (h.heap.raw.live _ hbG.1) hss.1 ha
      (by simp only [Blk.In, Blk.pay, Blk.fin] at hh ⊢; omega)
  have hso' := hso.setRefs hv hk1 hk hap
  have hbl := G.withStr_blocks (o' := o.withRefs k) he rfl rfl
  have hhp := h.ownWrite hbG.1 hm
  have d := h.den
  have hsub : DObjs.Sub ⟨L, G.strs⟩ ⟨L, A ++ o.withRefs k :: B⟩ :=
    ⟨fun y hy => ⟨y, hy, rfl, rfl⟩, fun o2 ho2 => by
      rw [he] at ho2
      rcases mem_split_cases ho2 with rfl | ho2
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩
      · exact ⟨o2, mem_split_of ho2, rfl, rfl⟩⟩
  refine ⟨?_, ?_, h.strView he hm hso', ?_, h.glob, h.col⟩
  · unfold DcG.raws; rw [hbl]; exact hhp
  · rw [hbl]; exact h.nodup
  · refine { d with
      stk := d.stk.imp fun hh => hh.relist hsub
      regs := fun r hr => (d.regs r hr).imp fun hh => hh.relist hsub
      hsDen := fun g hg => ?_
      numRefs := fun y hy => ?_
      strRefs := fun o2 ho2 => ?_ }
    · rcases hsD g hg with rfl | hg
      · exact ⟨.str o.s, _, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩
      · obtain ⟨w, hw⟩ := d.hsDen g hg; exact ⟨w, hw.relist hsub⟩
    · rw [G.withStr_vals, hcnt _ (by simp)]; exact d.numRefs y hy
    · rw [G.withStr_vals]
      rcases mem_split_cases ho2 with rfl | ho2
      · exact hkc
      · have ho2G : o2 ∈ G.strs := by rw [he]; exact mem_split_of ho2
        have s1 := hso.hsz; have s2 := (h.view.strs o2 ho2G).hsz
        rw [hcnt _ fun e => by
          have e' := GV.str.inj e
          exact live_apart hi (h.heap.raw.live _ (G.str_mem ho2G).1) (h.heap.raw.live _ hbG.1)
            (hss.2 o2 ho2).1 (a := o2.hb.pay) (by simp only [Blk.In, Blk.pay, Blk.fin] at *; omega)
            (by simp only [Blk.In, Blk.pay, Blk.fin] at *; omega)]
        exact d.strRefs o2 ho2G

/-- **`s_refs` of a string of the state incremented**: the handle `.str p`
joins `hs`. -/
theorem DcAt.bumpStr {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {A B : List StrObj} {o : StrObj}
    (h : DcAt S M H F L C G hs st) (he : G.strs = A ++ o :: B) (hhs : hs.length ≤ 2 ^ 30)
    {v : BitVec 64} (hv : v.toNat % 2 ^ 32 = o.refs + 1) :
    DcAt S (writeLog M [(o.hb.pay + 16, 4, v)]) H F L C (G.withStr A B (o.withRefs (o.refs + 1)))
      (.str o.hb.pay :: hs) st := by
  have hom : o ∈ G.strs := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
  refine h.strRefsTo he (by omega) (h.strRefs_lt hhs hom) (fun g hg => count_cons_ne _ _ (Ne.symm hg))
    ?_ (fun g hg => List.mem_cons.mp hg) hv
  rw [count_cons_self, h.den.strRefs o hom]

/-- **`s_refs` of a string of the state decremented** (not the last
reference): the handle `.str p` leaves `hs`. -/
theorem DcAt.decStr {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {A B : List StrObj} {o : StrObj}
    (h : DcAt S M H F L C G (.str o.hb.pay :: hs) st) (he : G.strs = A ++ o :: B)
    (h2 : 2 ≤ o.refs) {v : BitVec 64} (hv : v.toNat % 2 ^ 32 = o.refs - 1) :
    DcAt S (writeLog M [(o.hb.pay + 16, 4, v)]) H F L C (G.withStr A B (o.withRefs (o.refs - 1)))
      hs st := by
  have hom : o ∈ G.strs := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
  have hso := h.view.strs o hom
  refine h.strRefsTo he (by omega) (by have := hso.refsLt; omega)
    (fun g hg => (count_cons_ne _ _ (Ne.symm hg)).symm) ?_
    (fun g hg => .inr (List.mem_cons_of_mem _ hg)) hv
  have := h.den.strRefs o hom; rw [count_cons_self] at this; omega

end Dc.Mach
