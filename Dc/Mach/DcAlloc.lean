import Dc.Mach.State

/-!
# `dc_malloc` (M9)

`dc_malloc(n)` at `0x80001ea0` calls `malloc` and, on `NULL`, `dc_memfail`
(`0x80001e74`, a message to `stderr` and `exit(1)`). `dc_malloc_spec`
returns the fresh block with the allocator's invariant and frame, or enters
`dc_memfail` with `sp` lowered by 16.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `malloc`'s fresh block `b` of at least `n` bytes, the heap `H'` after it,
and the memory `M'` (only allocator bytes of `H` and the 16-byte frame below
`sp` changed since `M`). -/
structure DcMallocPost (S : Nat → Prop) (M M' : Mem) (H H' : Heap) (n sp : Nat) (b : Blk) : Prop where
  inv : HeapInv S M' H'
  live : H'.live = b :: H.live
  free : ∀ c ∈ H'.free, c ∈ H.free
  size : n ≤ b.sz
  alloc : ∀ a, b.h ≤ a → a < b.fin → AllocByte H a
  frame : ∀ a, ¬ AllocByte H a → ¬ frameIn sp 16 a → imgM M' a = imgM M a

/-- **`dc_malloc(n)`** at `0x80001ea0`: a fresh block in `a0`, or
`dc_memfail`. Clobbers `malloc`'s registers. -/
theorem dc_malloc_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} (hi : HeapInv S M H) {n sp : Nat}
    (hn : n < 2 ^ 62) (hsf : StackFrame S sp 16) (hab : heapEnd + 16 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 n) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' b, Keeps mallocClob R' R → DcMallocPost S M M' H H' n sp b →
      R' 10 = BitVec.ofNat 64 b.pay → DW live S Q (R 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 16) →
      (∀ a, ¬ AllocByte H a → ¬ frameIn sp 16 a → imgM M' a = imgM M a) →
      DW live S Q 0x80001e74#64 R' M') :
    DW live S Q 0x80001ea0#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  bc_run hlive hS [h2] at 0x8000096c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 16) (writeLog M [(sp - 16 + 8, 8, R 1)]) M := fun a ha => by
    simp only [frameIn] at ha; rw [imgM_store_miss _ _ (by omega)]
  have hi1 : HeapInv S (writeLog M [(sp - 16 + 8, 8, R 1)]) H :=
    hi.transport fun a ha => hM1 a fun hf => by
      rcases AllocByte.glob_or_heap hi ha with h1 | h1 <;>
        simp only [frameIn, freeListAddr, heapStart, heapEnd] at hf h1 <;> omega
  refine malloc_spec hlive hi1 (n := n) hn _ (by bsimp [h10]) (by bsimp [])
    fun R1 M1 H1 hk1 hp => ?_
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 16) := by rw [hk1.get 2]; bsimp [h2]
  have hra : ldv .ld M1 (sp - 16 + 8) = R 1 := by
    rw [ldv_congr .ld fun j hj => hp.frame _ fun ha => by
      rcases AllocByte.glob_or_heap hi1 ha with h1 | h1 <;>
        simp only [widthOfM, freeListAddr, heapStart, heapEnd] at hj h1 <;> omega]
    exact ldv_store_hit _ _ _
  have hfr : ∀ a, ¬ AllocByte H a → ¬ frameIn sp 16 a → imgM M1 a = imgM M a := fun a ha hf =>
    (hp.frame a ha).trans (hM1 a hf)
  cases hres : hp.res with
  | null e1 e2 e3 =>
    bsimp []
    bc_run hlive hS [e1, q1] at 0x80001e74
    bc_run hlive hS [e1, q1] at 0x80001e74
    refine hoom _ _ ?_ hfr
    bsimp [q1]
  | block b e1 e2 e3 e4 e5 =>
    have hp' : MallocPost S _ M1 H H1 n (BitVec.ofNat 64 b.pay) := e1 ▸ hp
    have hbl : b ∈ H1.live := by rw [e3]; exact List.mem_cons_self
    have hne : BitVec.ofNat 64 b.pay ≠ 0#64 := fun hc => by
      have fbb := hp'.inv.blk (List.mem_append_right _ hbl)
      have hsl := fbb.lo; have hst := fbb.top; have hsf2 := fbb.fin
      have hbp : b.pay = b.h + 16 := rfl
      have hbf : b.fin = b.h + 16 + b.sz := rfl
      bv_nat at hc
      simp only [heapStart, heapEnd] at hsl hst
      rw [Nat.mod_eq_of_lt (by omega)] at hc
      omega
    bsimp []
    bc_run hlive hS [e1, q1, hra]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals try (intro hc; exact absurd hc hne)
    intro _
    bc_run hlive hS [e1, q1, hra]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    · exact hal
    refine hk _ M1 H1 b ?_ ⟨hp.inv, e3, e4, e2, e5, hfr⟩ ?_
    · refine Keeps.restore (by rw [h2]; congr 1; omega) ?_
      refine Keeps.restore (by bsimp [hra]) ?_
      exact (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
    · bsimp [e1]

end Dc.Mach
