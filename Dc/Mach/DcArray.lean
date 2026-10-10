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

end Dc.Mach
