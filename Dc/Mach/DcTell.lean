import Dc.Mach.DcRotate

/-!
# `dc_tell_stackdepth` (M9)

    dc_tell_stackdepth ():
      for (n = 0, t = dc_stack; t; t = t->link) ++n;
      return n;

The count walks the stack chain (`h.view.stk.toP`); every node is a block of
the state, so the depth is at most `DcAt.blocks_len` and the 32-bit `addiw`
counts exactly.

- `tsd_walk`: the loop at `0x800037f0`.
- `dc_tell_stackdepth_spec`: `a0` the model's stack length.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `dc_tell_stackdepth`'s loop (`0x800037f0`, `a5` the node `b`, `a0` the
nodes counted before it). -/
theorem tsd_walk {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {P : Blk → GV → Prop} :
    ∀ {b : Blk} {x : GV} {l : List (Blk × GV)} {k : Nat},
    PChain M 24 P (BitVec.ofNat 64 b.pay) ((b, x) :: l) →
    (∀ bx ∈ (b, x) :: l, heapStart + 16 ≤ bx.1.pay ∧ bx.1.pay + 32 ≤ heapEnd ∧ bx.1.pay % 16 = 0) →
    k + 1 + l.length < 2 ^ 31 →
    ∀ {ra : BitVec 64} (R : Nat → BitVec 64), ra.toNat % 4 = 0 → R 1 = ra → R 15 = BitVec.ofNat 64 b.pay →
    R 10 = BitVec.ofNat 64 k →
    (∀ R', Keeps [10, 15] R' R → R' 10 = BitVec.ofNat 64 (k + 1 + l.length) →
      DW live S Q ra R' M) →
    DW live S Q 0x800037f0#64 R M := by
  intro b x l
  induction l generalizing b x with
  | nil => ?_
  | cons y l ih => ?_
  all_goals
    intro k hc hb hlen ra R hal h1 h15 h10 hk
    have htx : tohostAddr = 0x8001ad00 := rfl
    obtain ⟨hb1, hb2, hb3⟩ := hb (b, x) List.mem_cons_self
    simp only [heapStart, heapEnd] at hb1 hb2
    obtain ⟨-, hl⟩ := hc.uncons
    have wk : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (k + 1))) =
        BitVec.ofNat 64 (k + 1) := sxw_ofNat (by simp only [List.length_cons, List.length_nil] at hlen; omega)
  -- the last node: the link is null
  · have hz := hl.nil_eq
    bc_run hlive hS [h1, h15, h10, hz, word_succ, wk]
    all_goals try (intro hc; exact (hc rfl).elim)
    try intro _
    try bc_run hlive hS [h1, h15, h10, hz, word_succ, wk]
    all_goals first | exact hal | skip
    exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp [h10, word_succ, wk]; rfl)
  -- a next node: around the loop
  · obtain ⟨b', x'⟩ := y
    have he := hl.head_eq
    obtain ⟨hb1', hb2', -⟩ := hb (b', x') (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [heapStart, heapEnd] at hb1' hb2'
    have hnz : BitVec.ofNat 64 b'.pay ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    bc_run hlive hS [h15, h10, he, word_succ, wk] at 0x800037f8
    bc_run hlive hS [h15, h10, he, word_succ, wk]
    all_goals try (intro hc; exact (hc hnz).elim)
    try intro _
    refine ih (k := k + 1) (by rw [← he]; exact hl) (fun bx hm => hb bx (List.mem_cons_of_mem _ hm))
      (by simp only [List.length_cons] at hlen ⊢; omega) _ hal (by bsimp [h1]) (by bsimp [he])
      (by bsimp [word_succ, wk]) fun R' hk' e10 => ?_
    exact hk R' (hk'.trans (by keeps_tac Keeps.refl _ _))
      (by rw [e10]; simp only [List.length_cons]; congr 1; omega)

/-- The stack is at most as long as the state has blocks. -/
theorem DcAt.stk_len {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) :
    G.stk.length ≤ 7856803 := by
  have := h.blocks_len
  simp only [DcG.blocks, List.length_append, List.length_map] at this
  omega

/-- **`dc_tell_stackdepth ()`** at `0x800037e0`: `a0` the model's stack
length, memory unchanged. -/
theorem dc_tell_stackdepth_spec {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 15] R' R → R' 10 = BitVec.ofNat 64 st.stack.length →
      DWO live S Q t (R 1) R' M) :
    DWO live S Q t 0x800037e0#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hG := h.glob
  have hch := h.view.stk.toP
  have hle : G.stk.length = st.stack.length := h.den.stk.length_eq
  have hbl := h.stk_len
  have geo := h.stkGeo
  rcases hst : G.stk with _ | ⟨⟨b, g⟩, rest⟩
  · rw [hst] at hch
    have hz := hch.nil_eq
    rw [hst] at hle
    bc_run hlive hS []
    all_goals first | (intro hc; exact absurd hz hc) | skip
    intro _
    try bc_run hlive hS []
    all_goals first | exact hal | skip
    exact hk _ (by keeps_tac Keeps.refl _ _) (by rw [← hle]; bsimp []; rfl)
  · rw [hst] at hch hle hbl
    have hgb := geo.bnd
    rw [hst] at hgb
    have he := hch.head_eq
    obtain ⟨hb1, hb2, -⟩ := hgb (b, g) List.mem_cons_self
    simp only [heapStart, heapEnd] at hb1 hb2
    have hnz : BitVec.ofNat 64 b.pay ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    bc_run hlive hS []
    all_goals first | (intro hc; exact absurd (he.symm.trans hc) hnz) | skip
    try intro _
    rw [he]
    refine tsd_walk hlive hS (k := 0) (by rw [← he]; exact hch) hgb
      (by simp only [List.length_cons] at hbl; omega) _ hal (by bsimp []) (by bsimp []) (by bsimp [])
      fun R' hk' e10 => ?_
    exact hk R' (hk'.trans (by keeps_tac Keeps.refl _ _))
      (by rw [e10, ← hle]; simp only [List.length_cons]; congr 1; omega)

end Dc.Mach
