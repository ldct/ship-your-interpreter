import Dc.Mach.Tac

/-!
# `strlen` (`dc-port/libc/libc.c`)

`strlen(a)` at `0x80000904` on a NUL-terminated string in owned memory:
returns the length in `a0`, clobbers `a4`/`a5`, leaves memory unchanged.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `len` nonzero owned bytes at `a`, then an owned NUL, in writable RAM. -/
structure OwnedCStr (S : Nat → Prop) (Mt : Mem) (a len : Nat) : Prop where
  own : ∀ i, i ≤ len → S (a + i)
  nz : ∀ i, i < len → imgM Mt (a + i) ≠ 0
  nul : imgM Mt (a + len) = 0
  lo : tohostAddr + 16 ≤ a
  hi : a + len + 1 ≤ 0x88000000

/-- The registers `strlen` keeps: all but `a0`, `a4`, `a5`. -/
def StrlenKeep (R' R : Nat → BitVec 64) : Prop :=
  ∀ z, z ≠ 10 → z ≠ 14 → z ≠ 15 → R' z = R z

theorem lbu_zero_iff (Mt : Mem) (x : Nat) : ldv .lbu Mt x = 0#64 ↔ imgM Mt x = 0 := by
  rw [show ldv .lbu Mt x = zero_extend (m := 64) (imgM Mt x) by
    simp [ldv, bytesAt, bytesVal, widthOfM]]
  constructor <;> intro h
  · have := congrArg BitVec.toNat h
    simp [zero_extend, Sail.BitVec.zeroExtend] at this
    have hl := (imgM Mt x).isLt
    exact BitVec.eq_of_toNat_eq (by rw [Nat.mod_eq_of_lt (by omega)] at this; simpa using this)
  · rw [h]; rfl

theorem se12_zero : sign_extend (m := 64) (0x000#12) = 0#64 := by decide
theorem se12_one : sign_extend (m := 64) (0x001#12) = 1#64 := by decide

theorem ofNat_succ64 (i : Nat) : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]

theorem ofNat_add_toNat (a i : Nat) (h : a + i < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 i).toNat = a + i := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt h]

theorem accAddrs_one (x : Nat) : accAddrs x 1 = [x] := rfl

theorem StrlenKeep.upd {R R0 : Nat → BitVec 64} {k : Nat} (v : BitVec 64)
    (hk : k = 10 ∨ k = 14 ∨ k = 15) (h : StrlenKeep R R0) : StrlenKeep (upd R k v) R0 := by
  intro z h10 h14 h15
  rw [upd_other _ _ (by omega)]; exact h z h10 h14 h15

/-- The byte loop at `0x80000910` (one pass by `dx_run`) with `a5 = i`, `0 ≤ i < len`. -/
theorem strlen_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {a len : Nat} (hs : OwnedCStr S Mt a len) (R0 : Nat → BitVec 64)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', R' 10 = BitVec.ofNat 64 len → StrlenKeep R' R0 → DW live S Q (R0 1) R' Mt) :
    ∀ n i (R : Nat → BitVec 64), len - i = n → i < len →
      R 15 = BitVec.ofNat 64 i → R 10 = BitVec.ofNat 64 a → StrlenKeep R R0 →
      DW live S Q 0x80000910#64 R Mt := by
  have hlo := hs.lo
  have hhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro n
  induction n with
  | zero => intro i R h1 h2; omega
  | succ n ih =>
    intro i R hn hi h15 h10 hkeep
    have hea : (BitVec.ofNat 64 a + BitVec.ofNat 64 (i + 1)).toNat = a + (i + 1) :=
      ofNat_add_toNat _ _ (by omega)
    dx_run hlive
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, se12_zero, BitVec.add_zero,
      h10, h15, ofNat_succ64, hea, accAddrs_one, List.mem_singleton]
    · omega
    · rintro b rfl; exact hs.own _ (by omega)
    · intro hne
      refine ih (i + 1) _ (by omega) ?_ ?_ ?_ ?_
      · refine Classical.byContradiction fun hge => ?_
        have heq : i + 1 = len := by omega
        apply hne
        rw [lbu_zero_iff, heq]; exact hs.nul
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15]
      · simp only [upd_apply, Nat.reduceEqDiff, ite_false, h10]
      · (repeat (refine StrlenKeep.upd _ (by decide) ?_)); exact hkeep
    · intro heq
      have hz : i + 1 = len := by
        refine Classical.byContradiction fun hne => ?_
        apply heq
        rw [Ne, lbu_zero_iff]; exact hs.nz _ (by omega)
      apply st_80000920 hlive
      apply st_80000924 hlive
      · simp only [upd_other _ _ (show (1:Nat) ≠ 10 by decide),
          upd_other _ _ (show (1:Nat) ≠ 14 by decide), upd_other _ _ (show (1:Nat) ≠ 15 by decide),
          hkeep 1 (by decide) (by decide) (by decide), hal]
      · simp only [upd_other _ _ (show (1:Nat) ≠ 10 by decide),
          upd_other _ _ (show (1:Nat) ≠ 14 by decide), upd_other _ _ (show (1:Nat) ≠ 15 by decide),
          hkeep 1 (by decide) (by decide) (by decide)]
        refine hk _ ?_ (by (repeat (refine StrlenKeep.upd _ (by decide) ?_)); exact hkeep)
        simp only [upd_same, upd_other _ _ (show (15:Nat) ≠ 14 by decide), se12_zero,
          BitVec.add_zero, hz]

/-- **`strlen(a)`** at `0x80000904` on an owned C string of length `len`:
returns `len` in `a0` at the return address, with every register but `a0`,
`a4`, `a5` and all memory unchanged. -/
theorem strlen_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {a len : Nat} (hs : OwnedCStr S Mt a len)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 a) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', R' 10 = BitVec.ofNat 64 len → StrlenKeep R' R → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x80000904#64 R Mt := by
  have hlo := hs.lo
  have hhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hea : (BitVec.ofNat 64 a + 0#64).toNat = a := by
    rw [BitVec.add_zero, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hkeep0 : StrlenKeep R R := fun _ _ _ _ => rfl
  apply st_80000904 hlive
  · simp only [se12_zero, h10, hea]; omega
  · simp only [se12_zero, h10, hea, accAddrs_one, List.mem_singleton]
    rintro b rfl; simpa using hs.own 0 (by omega)
  apply st_80000908 hlive
  · intro hz
    rw [upd_same, se12_zero, h10] at hz
    have h0 : len = 0 := by
      refine Classical.byContradiction fun hne => ?_
      rw [hea, lbu_zero_iff] at hz
      exact hs.nz 0 (by omega) (by simpa using hz)
    apply st_80000920 hlive
    apply st_80000924 hlive
    · simp only [upd_other _ _ (show (1:Nat) ≠ 10 by decide),
        upd_other _ _ (show (1:Nat) ≠ 15 by decide), hal]
    · simp only [upd_other _ _ (show (1:Nat) ≠ 10 by decide),
        upd_other _ _ (show (1:Nat) ≠ 15 by decide)]
      refine hk _ ?_ (by (repeat (refine StrlenKeep.upd _ (by decide) ?_)); exact hkeep0)
      simp only [upd_same, se12_zero, BitVec.add_zero, h10, h0]
      rw [BitVec.add_zero] at hz; exact hz
  · intro hnz
    have hpos : 0 < len := by
      refine Classical.byContradiction fun h0 => ?_
      apply hnz
      rw [upd_same, se12_zero, h10, hea, lbu_zero_iff]
      simpa [show len = 0 by omega] using hs.nul
    apply st_8000090c hlive
    refine strlen_loop hlive hs R hal hk (len - 0) 0 _ rfl hpos ?_ ?_ ?_
    · simp only [upd_same, se12_zero, BitVec.add_zero]
    · simp only [upd_other _ _ (show (10:Nat) ≠ 15 by decide), h10]
    · (repeat (refine StrlenKeep.upd _ (by decide) ?_)); exact hkeep0

end Dc.Mach
