import Dc.Mach.Bc.DivAlloc

/-!
# `bc_divide`'s operand buffers (`0x800059d0` to `0x80005a50`)

- `count_rec`: induction on a loop's remaining count with the body taking
  the next iteration only when one remains (the shape of every scan loop).
- `dvn_skip`: the leading-zero skip over `num2` at `0x80005a34`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

/-- **Counted loops**: a body proving the head at `k` from the head at
`k - 1` (one iteration on) when `k` is a successor proves every head. -/
theorem count_rec {G : Nat → Nat → (Nat → BitVec 64) → Prop}
    (hbody : ∀ k i R, (∀ k', k = k' + 1 → ∀ R', G k' (i + 1) R') → G k i R) :
    ∀ k i R, G k i R := by
  intro k
  induction k with
  | zero => exact fun i R => hbody 0 i R fun k' h => absurd h (by omega)
  | succ k ih =>
    intro i R
    refine hbody (k + 1) i R fun k' h R' => ?_
    rw [show k' = k by omega]
    exact ih (i + 1) R'

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- **The leading-zero skip** at `0x80005a34` over `num2` (`while (*n2ptr == 0)
{ n2ptr++; len2--; }`): digits `0 … i` zero, `s8` at digit `i`, `s7 = len2 - i`;
the first nonzero digit `z0` ends it at `0x80005a50` with `s8` at `z0`,
`s7 = len2 - z0`, `a6 = s11 = len2 - z0 + 1`. -/
theorem dvn_skip {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {Rb : Nat → BitVec 64} (hS : HeapOwn S) {ds : List Nat} (hd : IsDigits ds)
    {N0 z0 len2 : Nat} (hb : ∀ i, i ≤ z0 → imgM M (N0 + i) = BitVec.ofNat 8 (ds.getD i 0))
    (hz : ∀ i, i < z0 → ds.getD i 0 = 0) (hnz : ds.getD z0 0 ≠ 0) (hzl : z0 < len2) (hl2 : len2 < 2 ^ 30)
    (hlo : 2147603920 ≤ N0) (hhi : N0 + len2 ≤ 2273312768)
    (hexit : ∀ R', Keeps [15, 16, 23, 24, 27] R' Rb → R' 24 = BitVec.ofNat 64 (N0 + z0) →
      R' 23 = BitVec.ofNat 64 (len2 - z0) → R' 16 = BitVec.ofNat 64 (len2 - z0 + 1) →
      R' 27 = BitVec.ofNat 64 (len2 - z0 + 1) → DW live S Q 0x80005a50#64 R' M) :
    ∀ k i R, i + 1 + k = z0 → Keeps [15, 16, 23, 24, 27] R Rb →
      R 24 = BitVec.ofNat 64 (N0 + i) → R 23 = BitVec.ofNat 64 (len2 - i) →
      DW live S Q 0x80005a34#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  refine count_rec fun k i R ih hi kk h24 h23 => ?_
  have hl := lbu_digit (hd.getD (i + 1)) (hb (i + 1) (by omega))
  have hdl := hd.getD (i + 1)
  have e1 : BitVec.ofNat 64 (N0 + i) + 1#64 = BitVec.ofNat 64 (N0 + (i + 1)) := by
    rw [show (1#64) = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat]; congr 1
  have e2 := subw_ofNat_le (a := len2 - i) (b := 1) (by omega) (by omega)
  bc_run hlive hS [h24, h23, hl, e1] at 0x80005a48
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro h0
    bsimp [ofNat_eq_zero_iff (show ds.getD (i + 1) 0 < 2 ^ 64 by omega)] at h0
    rcases k with _ | k
    · exact absurd h0 (by rw [show i + 1 = z0 by omega]; exact hnz)
    exact ih k rfl _ (by omega) (by keeps_tac kk) (by bsimp []; try exact congrArg _ (by omega)) (by bsimp []; try exact congrArg _ (by omega))
  · intro h0
    bsimp [ofNat_eq_zero_iff (show ds.getD (i + 1) 0 < 2 ^ 64 by omega)] at h0
    have hiz : i + 1 = z0 := by
      rcases Nat.lt_or_ge (i + 1) z0 with h | h
      · exact absurd (hz _ h) h0
      · omega
    subst hiz
    have e3 : BitVec.ofNat 64 (len2 - i) <<< 32 >>> 32 = BitVec.ofNat 64 (len2 - i) := shl_shr32 (by omega)
    bc_run hlive hS [e3] at 0x80005a50
    exact hexit _ (by keeps_tac kk) (by bsimp []; try exact congrArg _ (by omega)) (by bsimp []; try exact congrArg _ (by omega))
      (by bsimp []; try exact congrArg _ (by omega)) (by bsimp []; try exact congrArg _ (by omega))

end

end Dc.Mach
