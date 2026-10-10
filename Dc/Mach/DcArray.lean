import Dc.Mach.DcRegPop

/-!
# Register arrays (M9)

`dc_array_get (r, i)` at `0x80003dc8` walks the top level's array (sorted by
index) to the first node with index `≥ i`; `dc_array_set (r, i, value)` at
`0x80003c7c` replaces or inserts there.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

theorem PChain.uncons {α : Type} {Mt : Mem} {off : Nat} {P : Blk → α → Prop} {p : BitVec 64}
    {b : Blk} {x : α} {l : List (Blk × α)} (h : PChain Mt off P p ((b, x) :: l)) :
    P b x ∧ PChain Mt off P (ldv .ld Mt (b.pay + off)) l := by
  generalize hl : (b, x) :: l = L at h
  cases h with
  | nil => cases hl
  | cons hp hr => cases hl; exact ⟨hp, hr⟩


theorem PChain.nil_eq {α : Type} {Mt : Mem} {off : Nat} {P : Blk → α → Prop} {p : BitVec 64}
    (h : PChain Mt off P p []) : p = 0#64 := by
  generalize hl : ([] : List (Blk × α)) = L at h
  cases h with
  | nil => rfl
  | cons => cases hl

theorem PChain.head_eq {α : Type} {Mt : Mem} {off : Nat} {P : Blk → α → Prop} {p : BitVec 64}
    {b : Blk} {x : α} {l : List (Blk × α)} (h : PChain Mt off P p ((b, x) :: l)) :
    p = BitVec.ofNat 64 b.pay := by
  generalize hl : (b, x) :: l = L at h
  cases h with
  | nil => cases hl
  | cons => cases hl; rfl

theorem ofNat_ne_small {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun e => h (by
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this; omega)

/-- The machine's search: the first node with index `≥ i`, if its index is `i`. -/
def afind (i : Nat) : List (Blk × ANode) → Option (Blk × ANode)
  | [] => none
  | bx :: rest => if bx.2.idx < i then afind i rest else if bx.2.idx = i then some bx else none

/-- `dc_array_get`'s search loop (`0x80003df0`, `a5` the node `b`, `a1` the
index `i`). -/
theorem ag_walk {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {i : Nat} (hi : i < 2 ^ 31) :
    ∀ {b : Blk} {x : ANode} {l : List (Blk × ANode)},
    PChain M 24 (ANodeAt M) (BitVec.ofNat 64 b.pay) ((b, x) :: l) →
    (∀ bx ∈ (b, x) :: l, heapStart + 16 ≤ bx.1.pay ∧ bx.1.pay + 32 ≤ heapEnd ∧ bx.1.pay % 16 = 0) →
    ∀ (R : Nat → BitVec 64), R 15 = BitVec.ofNat 64 b.pay → R 11 = BitVec.ofNat 64 i →
    (∀ R', Keeps [14, 15] R' R → (match afind i ((b, x) :: l) with
      | some bx => R' 15 = BitVec.ofNat 64 bx.1.pay → DW live S Q 0x80003e0c#64 R' M
      | none => DW live S Q 0x80003dfc#64 R' M)) →
    DW live S Q 0x80003df0#64 R M := by
  intro b x l
  induction l generalizing b x with
  | nil => ?_
  | cons y l ih => ?_
  all_goals
    intro hc hb R h15 h11 hk
    have htx : tohostAddr = 0x8001ad00 := rfl
    obtain ⟨hb1, hb2, hb3⟩ := hb (b, x) List.mem_cons_self
    simp only [heapStart, heapEnd] at hb1 hb2
    obtain ⟨hn, hl⟩ := hc.uncons
    have hidx := hn.idx
    have hil := hn.idxLt
    have ci : (BitVec.ofNat 64 x.idx).toInt = x.idx := toInt_ofNat_small (by omega)
    have cj : (BitVec.ofNat 64 i).toInt = i := toInt_ofNat_small (by omega)
    bc_run hlive hS [h15, h11, hidx, ci, cj] at 0x80003df8
    all_goals first | (intro hlt; bc_run hlive hS [h15, h11, hidx, ci, cj] at 0x80003de8) | skip
  -- the empty rest: the link is null
  · intro hlt
    have hz := hl.nil_eq
    bc_run hlive hS [h15, hz] at 0x80003dfc
    all_goals try (intro hc; exact (hc rfl).elim)
    try intro _
    have hk' := hk
    simp only [afind, show x.idx < i by omega, ↓reduceIte] at hk'
    exact hk' _ (by keeps_tac Keeps.refl _ _)
  · intro heq
    have e : x.idx = i := by
      have := congrArg BitVec.toNat heq; simp only [BitVec.toNat_ofNat] at this; omega
    subst e
    have hk' := hk
    simp only [afind, Nat.lt_irrefl, ↓reduceIte] at hk'
    exact hk' _ (by keeps_tac Keeps.refl _ _) (by bsimp [h15])
  · intro hne
    have hk' := hk
    have e : x.idx ≠ i := fun e => hne (by rw [e])
    simp only [afind, show ¬ x.idx < i by omega, e, ↓reduceIte] at hk'
    exact hk' _ (by keeps_tac Keeps.refl _ _)
  -- a next node: around the loop
  · intro hlt
    obtain ⟨b', x'⟩ := y
    have he := hl.head_eq
    obtain ⟨hb1', hb2', -⟩ := hb (b', x') (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [heapStart, heapEnd] at hb1' hb2'
    have hnz : BitVec.ofNat 64 b'.pay ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    bc_run hlive hS [h15, he] at 0x80003df0
    all_goals try (intro hc; exact (hnz hc).elim)
    try intro _
    rw [he] at hl
    refine ih hl (fun bx hm => hb bx (List.mem_cons_of_mem _ hm)) _ (by bsimp []) (by bsimp [h11])
      fun R' hk1 => ?_
    have hk' := hk R' (hk1.trans (by keeps_tac Keeps.refl _ _))
    simp only [afind, show x.idx < i by omega, ↓reduceIte] at hk'
    exact hk'
  · intro heq
    have e : x.idx = i := by
      have := congrArg BitVec.toNat heq; simp only [BitVec.toNat_ofNat] at this; omega
    subst e
    have hk' := hk
    simp only [afind, Nat.lt_irrefl, ↓reduceIte] at hk'
    exact hk' _ (by keeps_tac Keeps.refl _ _) (by bsimp [h15])
  · intro hne
    have hk' := hk
    have e : x.idx ≠ i := fun e => hne (by rw [e])
    simp only [afind, show ¬ x.idx < i by omega, e, ↓reduceIte] at hk'
    exact hk' _ (by keeps_tac Keeps.refl _ _)

theorem PChain_mem_sz {M : Mem} {p : BitVec 64} :
    ∀ {l : List (Blk × ANode)}, PChain M 24 (ANodeAt M) p l → ∀ {bx}, bx ∈ l → 32 ≤ bx.1.sz
  | [], _, _, h => by cases h
  | (b, x) :: _, hc, _, hm => by
    obtain ⟨hn, hr⟩ := hc.uncons
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hn.sz
    · exact PChain_mem_sz hr hm

theorem PChain_mem_node {M : Mem} {p : BitVec 64} :
    ∀ {l : List (Blk × ANode)}, PChain M 24 (ANodeAt M) p l → ∀ {bx}, bx ∈ l → ANodeAt M bx.1 bx.2
  | [], _, _, h => by cases h
  | (b, x) :: _, hc, _, hm => by
    obtain ⟨hn, hr⟩ := hc.uncons
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hn
    · exact PChain_mem_node hr hm

/-- The machine's search agrees with `find?` on a sorted array. -/
theorem afind_find {O : DObjs} {i : Nat} :
    ∀ {l : List (Blk × ANode)} {arr : List (Nat × Val)},
    List.Forall₂ (fun (be : Blk × ANode) (iv : Nat × Val) => be.2.idx = iv.1 ∧ be.2.v.Den O iv.2) l arr →
    arr.Pairwise (fun a b => a.1 < b.1) →
    (∀ bx, afind i l = some bx → bx ∈ l ∧ ∃ v, arr.find? (·.1 == i) = some (i, v) ∧ bx.2.v.Den O v) ∧
    (afind i l = none → arr.find? (·.1 == i) = none)
  | [], [], .nil, _ => ⟨fun _ h => (by cases h), fun _ => rfl⟩
  | (b, x) :: l, (j, w) :: arr, .cons ⟨hj, hw⟩ hr, hs => by
    have ih := afind_find (i := i) hr (List.pairwise_cons.mp hs).2
    simp only at hj hw
    subst hj
    by_cases hlt : x.idx < i
    · have hne : (x.idx == i) = false := by simp only [beq_eq_false_iff_ne]; omega
      simp only [afind, hlt, ↓reduceIte, List.find?_cons, hne]
      exact ⟨fun bx h => ⟨List.mem_cons_of_mem _ (ih.1 bx h).1, (ih.1 bx h).2⟩, ih.2⟩
    · by_cases heq : x.idx = i
      · subst heq
        simp only [afind, Nat.lt_irrefl, ↓reduceIte, List.find?_cons, beq_self_eq_true]
        refine ⟨fun bx h => ?_, fun h => (by cases h)⟩
        cases h
        exact ⟨List.mem_cons_self, w, rfl, hw⟩
      · have hne : (x.idx == i) = false := by simp only [beq_eq_false_iff_ne]; omega
        simp only [afind, hlt, heq, ↓reduceIte, List.find?_cons, hne]
        refine ⟨fun _ h => (by cases h), fun _ => ?_⟩
        rw [List.find?_eq_none]
        intro y hy
        have := (List.pairwise_cons.mp hs).1 y hy
        simp only [beq_iff_eq]; omega

/-- The top level's array nodes. -/
def topArr : List (Blk × RLev) → List (Blk × ANode)
  | [] => []
  | (_, e) :: _ => e.arr

/-- The top level's array head word, or `0` without a level. -/
def topArrPtr (M : Mem) : List (Blk × RLev) → BitVec 64
  | [] => 0#64
  | (c, _) :: _ => ldv .ld M (c.pay + 16)

/-- The model's top-level array. -/
def topArrSt (st : St) (r : Nat) : List (Nat × Val) :=
  match st.regs r with
  | [] => []
  | e :: _ => e.arr

theorem arrayGet_eq (st : St) (r i : Nat) : arrayGet st r i =
    match (topArrSt st r).find? (·.1 == i) with
    | some (_, v) => v
    | none => .num (Num.zero 0) := by
  unfold arrayGet topArrSt; rfl

/-- The top level's array: a chain from its head word, nodes in the heap. -/
theorem DcAt.topArr {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {r : Nat}
    (h : DcAt S M H F L C G hs st) (hr : r < 256) :
    PChain M 24 (ANodeAt M) (topArrPtr M (G.regs r)) (topArr (G.regs r)) ∧
    (∀ bx ∈ topArr (G.regs r), heapStart + 16 ≤ bx.1.pay ∧ bx.1.pay + 32 ≤ heapEnd ∧
      bx.1.pay % 16 = 0) ∧
    List.Forall₂ (fun (be : Blk × ANode) (iv : Nat × Val) => be.2.idx = iv.1 ∧
      be.2.v.Den ⟨L, G.strs⟩ iv.2) (topArr (G.regs r)) (topArrSt st r) := by
  have hv := h.view.regs r hr
  have hd := h.den.regs r hr
  have hmem : ∀ be ∈ G.regs r, ∀ c ∈ RLev.blocks be, c ∈ G.blocks := fun be hbe c hc =>
    G.lev_mem hr hbe hc
  unfold topArrSt
  generalize G.regs r = l at hv hd hmem
  cases hv with
  | nil => revert hd; generalize st.regs r = m; intro hd; cases hd
           exact ⟨.nil, fun _ h => (by cases h), .nil⟩
  | @cons _ c e l' h0 hn hl' =>
    revert hd; generalize st.regs r = m; intro hd
    cases hd with
    | cons hde _ =>
    refine ⟨hn.arr.toP, fun bx hbx => ?_, hde.arr⟩
    have hb : bx.1 ∈ G.blocks := hmem _ List.mem_cons_self _
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨bx, hbx, rfl⟩))
    have := blk_bounds h.heap.heap (h.heap.raw.live _ hb)
    have hsz := (PChain_mem_sz hn.arr.toP hbx)
    omega

/-- `dc_get_stacked_array (r)` at `0x800038f8`: the top level's array head. -/
theorem get_stacked {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {r : Nat}
    (h : DcAt S M H F L C G hs st) (hr : r < 256)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 r) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 15] R' R → R' 10 = topArrPtr M (G.regs r) → DW live S Q (R 1) R' M) :
    DW live S Q 0x800038f8#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  have hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs, regAddr] at this ⊢; omega)
  have hv := h.view.regs r hr
  have hmem : ∀ be ∈ G.regs r, ∀ c ∈ RLev.blocks be, c ∈ G.blocks := fun be hbe c hc =>
    G.lev_mem hr hbe hc
  generalize G.regs r = l at hv hmem hk
  cases hv with
  | nil h0 =>
    have hcS : True := trivial
    bc_run hlive hS [h10, regWord_addr hr, hra8, h0]
    all_goals first | exact hrown | (simp only [LdOK, regAddr, dcRegAddr]; omega) | skip
    all_goals try (intro hc; exact (hc rfl).elim)
    all_goals try intro _
    bc_run hlive hS []
    all_goals first | exact hcS | exact hal | skip
    refine hk _ ?_ ?_
    · keeps_tac Keeps.refl _ _
    · bsimp [topArrPtr]
  | @cons _ c e l' h0 hn hl' =>
    have hcG : c ∈ G.blocks := hmem _ List.mem_cons_self _ List.mem_cons_self
    have hbb := blk_bounds h.heap.heap (h.heap.raw.live c hcG)
    have hsz := hn.sz
    simp only [heapStart, heapEnd] at hbb
    have hnz : BitVec.ofNat 64 c.pay ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    have hcS : ∀ b ∈ accAddrs (c.pay + 16) 8, S b := fun b hb => by
      have := of_mem_accAddrs hb
      exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
    bc_run hlive hS [h10, regWord_addr hr, hra8, h0]
    all_goals first | exact hrown | exact hcS | (simp only [LdOK, regAddr, dcRegAddr]; omega) | skip
    all_goals try (intro hc; exact (hnz hc).elim)
    all_goals try intro _
    bc_run hlive hS []
    all_goals first | exact hcS | exact hal | skip
    refine hk _ ?_ ?_
    · keeps_tac Keeps.refl _ _
    · bsimp [topArrPtr]

/-- `dc_array_get` on a node with the index (`0x80003e0c`, `sp` lowered by
48, `a5` the node `b`): a duplicate of its datum. -/
theorem ag_found {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {v : Val}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) {sp : Nat} {b : Blk} {x : ANode}
    (hn : ANodeAt M b x) (hv : x.v.Den ⟨L, G.strs⟩ v)
    (hb : heapStart + 16 ≤ b.pay ∧ b.pay + 32 ≤ heapEnd ∧ b.pay % 16 = 0)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h15 : R 15 = BitVec.ofNat 64 b.pay)
    {ra : BitVec 64} (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' L' C' G', Keeps (1 :: 2 :: i2nClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      DatRegs (R' 10) (R' 11) x.v → DcAt S M' H F L' C' G' (x.v :: hs) st →
      x.v.Den ⟨L', G'.strs⟩ v → StkOut sp 336 M' M → StrPin G.strs G'.strs hs → G'.lk = G.lk →
      DW live S Q ra R' M') :
    DW live S Q 0x80003e0c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  obtain ⟨hb1, hb2, hb3⟩ := hb
  simp only [heapStart, heapEnd] at hb1 hb2 hab
  have hd := hn.dat
  bc_run hlive hS [h2, h15, hra] at 0x800020a0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_dup_spec hlive h hhs hv (StackFrame.shrink (hsf) (m := 16) (by omega))
    (by simp only [heapEnd]; omega) _ ⟨?_, ?_⟩ ?_ ?_ fun R' M' L' C' G' hk1 hd' hsn h' hden hfr hpin => ?_
  · bsimp []; exact hd.tag
  · bsimp []; exact hd.ptr
  · bsimp [h2]; congr 1; omega
  · bsimp []; exact hal
  refine hk R' M' L' C' G' ?_ ?_ ?_ hd' h' hden (fun a ho hg hf => hfr a ho hg fun h' => hf ?_) hpin hsn.lk
  · exact (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  · rw [hk1.get 1]; bsimp []
  · rw [hk1.get 2]; bsimp [h2]; congr 1; omega
  · simp only [frameIn] at h' ⊢; omega

/-- `dc_array_get` without a node of the index (`0x80003dfc`, `sp` lowered
by 48): a fresh zero. -/
theorem ag_zero {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) {sp : Nat}
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48))
    {ra : BitVec 64} (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' g, Keeps (1 :: 2 :: i2nClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DatRegs (R' 10) (R' 11) g → DcAt S M' H' F' L' C' G (g :: hs) st →
      g.Den ⟨L', G.strs⟩ (.num (Num.zero 0)) → StkOut sp 336 M' M → DW live S Q ra R' M')
    (hoom : ∀ R' M', StkOut sp 336 M' M → DW live S Q 0x80002bcc#64 R' M') :
    DW live S Q 0x80003dfc#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  simp only [heapEnd] at hab
  bc_run hlive hS [h2, hra] at 0x800026d8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_int2data_spec hlive h hhs (v := 0) (StackFrame.shrink hsf (m := 192) (by omega))
    (by simp only [heapEnd]; omega) _ ?_ ?_ ?_ (by decide) (by decide)
    (fun R' M' H' F' L' C' g hk1 hd' hden h' hfr => ?_)
    (fun R' M' _ hfr => hoom R' M' fun a ho hg hf => hfr a ho hg fun h' => hf (by
      simp only [frameIn] at h' ⊢; omega))
  · bsimp []; rfl
  · bsimp [h2]; congr 1; omega
  · bsimp []; exact hal
  refine hk R' M' H' F' L' C' g ?_ ?_ ?_ hd' h' hden fun a ho hg hf => hfr a ho hg fun h' => hf ?_
  · exact (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  · rw [hk1.get 1]; bsimp []
  · rw [hk1.get 2]; bsimp [h2]; congr 1; omega
  · simp only [frameIn] at h' ⊢; omega

theorem ofNat_sub48 {sp : Nat} (h1 : 48 ≤ sp) :
    BitVec.ofNat 64 sp + 18446744073709551568#64 = BitVec.ofNat 64 (sp - 48) := by
  change BitVec.ofNat 64 sp + -(48#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le sp 48 (by decide) h1

/-- **`dc_array_get (regid, index)`** at `0x80003dc8`, `r = regid`, `i =
index`: the datum `arrayGet st r i` in `a0`/`a1` with one more reference (a
fresh zero when the index is absent), on a sorted array. -/
theorem dc_array_get_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) {sp r i : Nat} (hr : r < 256)
    (hi : i < 2 ^ 31) (hsrt : (topArrSt st r).Pairwise (fun a b => a.1 < b.1))
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 r) (h11 : R 11 = BitVec.ofNat 64 i)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G' g, Keeps i2nClob R' R → DatRegs (R' 10) (R' 11) g →
      DcAt S M' H' F' L' C' G' (g :: hs) st → g.Den ⟨L', G'.strs⟩ (arrayGet st r i) →
      StkOut sp 336 M' M → StrPin G.strs G'.strs hs → G'.lk = G.lk → DW live S Q (R 1) R' M')
    (hoom : ∀ R' M', StkOut sp 336 M' M → DW live S Q 0x80002bcc#64 R' M') :
    DW live S Q 0x80003dc8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  simp only [heapEnd] at hab
  have hP : ∀ a, frameIn sp 336 a → OutHeap a ∧ ¬ DcGlob a := fun a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have hM1 : MemOnly (frameIn sp 336) (writeLog (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 i)])
      [(sp - 48 + 40, 8, R 1)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hM1 hP
  have hout : ∀ M', StkOut sp 336 M' (writeLog (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 i)])
      [(sp - 48 + 40, 8, R 1)]) → StkOut sp 336 M' M :=
    fun M' hm a ho hg hf => (hm a ho hg hf).trans (hM1 a hf)
  obtain ⟨hch, hbd, hf2⟩ := h1.topArr hr
  have hsp := ofNat_sub48 (sp := sp) (by omega)
  bc_run hlive hS [h2, h11, hsp] at 0x800038f8
  case hS => exact frame_acc hsf (by omega) (by omega)
  case hk.hS => exact frame_acc hsf (by omega) (by omega)
  have hff := afind_find (i := i) hf2 hsrt
  refine get_stacked hlive h1 hr _ ?_ ?_ fun R1 hk1 e10 => ?_
  · bsimp [h10]
  · bsimp []
  rw [show upd (upd R 2 (BitVec.ofNat 64 (sp - 48))) 1 (2147499480#64) 1 = 2147499480#64 by bsimp []]
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp [h2, hsp]
  have l8 : ldv .ld (writeLog (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 i)]) [(sp - 48 + 40, 8, R 1)])
      (sp - 48 + 8) = BitVec.ofNat 64 i := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have l40 : ldv .ld (writeLog (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 i)]) [(sp - 48 + 40, 8, R 1)])
      (sp - 48 + 40) = R 1 := ldv_store_hit _ _ _
  -- the continuation at the zero exit
  have hz : ∀ R2 : Nat → BitVec 64, R2 2 = BitVec.ofNat 64 (sp - 48) →
      Keeps (1 :: 2 :: 10 :: 11 :: 14 :: 15 :: i2nClob) R2 R →
      afind i (topArr (G.regs r)) = none → DW live S Q 0x80003dfc#64 R2
        (writeLog (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 i)]) [(sp - 48 + 40, 8, R 1)]) :=
    fun R2 e2 hk2 ha => ag_zero hlive h1 hhs hsf (by simp only [heapEnd]; omega) R2 e2 l40 hal
      (fun R' M' H' F' L' C' g hk3 e1 e2' hd h' hden hfr => by
        have hnone := hff.2 ha
        refine hk R' M' H' F' L' C' G g (Keeps.restore2 (R1 := R) ((hk3.trans
          (hk2.mono (by decide))).mono (by decide)) (by keeps_tac Keeps.refl _ _) e1 (by rw [e2', h2]))
          hd h' ?_ (hout M' hfr) (StrPin.refl _ _) rfl
        rw [arrayGet_eq, hnone]; exact hden)
      fun R' M' hfr => hoom R' M' (hout M' hfr)
  generalize hM2 : writeLog (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 i)]) [(sp - 48 + 40, 8, R 1)] = M2
    at h1 hch hbd hf2 l8 l40 e10 hz hout ⊢
  rcases hl : topArr (G.regs r) with _ | ⟨⟨b, x⟩, l⟩
  · rw [hl] at hch
    have e0 : R1 10 = 0#64 := by rw [e10]; exact hch.nil_eq
    bc_run hlive hS [q2, e0, l8] at 0x80003dfc
    · exact frame_acc hsf (by omega) (by omega)
    bc_run hlive hS [] at 0x80003dfc
    refine hz _ ?_ ?_ (by rw [hl]; rfl)
    · bsimp [q2]
    · keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
  · rw [hl] at hch hbd hff
    have e0 : R1 10 = BitVec.ofNat 64 b.pay := by rw [e10]; exact hch.head_eq
    have hb := hbd _ (.head _)
    have hnz : BitVec.ofNat 64 b.pay ≠ 0#64 := ofNat_ne_small
      (by simp only [heapEnd] at hb; omega) (by decide) (by simp only [heapStart] at hb; omega)
    bc_run hlive hS [q2, e0, l8, hnz] at 0x80003df0
    · exact frame_acc hsf (by omega) (by omega)
    case hF => intro hc; exact (hc hnz).elim
    intro _
    have he := hch.head_eq
    rw [he] at hch
    have hKR1 : Keeps (1 :: 2 :: 10 :: 11 :: 14 :: 15 :: i2nClob)
        (upd (upd R1 11 (BitVec.ofNat 64 i)) 15 (BitVec.ofNat 64 b.pay)) R := by
      keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
    refine ag_walk hlive hS hi hch hbd _ (by bsimp []) (by bsimp []) fun R3 hk3 => ?_
    have hKR3 := (hk3.mono (by decide)).trans hKR1
    have q3 : R3 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk3.get 2]; bsimp [q2]
    rcases ha : afind i ((b, x) :: l) with _ | ⟨b', x'⟩
    · exact hz R3 q3 hKR3 (by rw [hl]; exact ha)
    intro e15
    obtain ⟨hm, v, hfind, hv⟩ := hff.1 _ ha
    refine ag_found hlive h1 hhs (PChain_mem_node hch hm) hv (hbd _ hm) hsf
      (by simp only [heapEnd]; omega) R3 q3 e15 l40 hal
      fun R' M' L' C' G' hk4 e1 e2 hd h' hden hfr hpin hlk => ?_
    exact hk R' M' H F L' C' G' x'.v (Keeps.restore2 (R1 := R) ((hk4.trans
      (hKR3.mono (by decide))).mono (by decide)) (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2]))
      hd h' (by rw [arrayGet_eq, hfind]; exact hden) (hout M' hfr) hpin hlk

end Dc.Mach
