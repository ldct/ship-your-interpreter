import Dc.BcModel.Sqrt

/-!
# `bc_sqrt`'s first guess

`Num.sqrtInit` against what the machine computes: below one the guess is
`1` at the number's scale; above one, `10 ^ (n_len / 2)` with `n_len / 2`
from `bc_int2num (n_len) * 0.5` cut to scale `0` (`mul_half`), `n_len` the
number of integer digits (`intLen_eq`).
-/

namespace Dc.BcModel

open Dc

/-- The digits of a number with `m + 1` of them. -/
theorem digitsIn_length : ∀ (m f n : Nat), 10 ^ m ≤ n → n < 10 ^ (m + 1) → n < f →
    (Num.digitsIn 10 f n).length = m + 1 := by
  intro m
  induction m with
  | zero =>
    intro f n h1 h2 h3
    cases f with
    | zero => omega
    | succ f =>
      simp only [Nat.pow_zero, Nat.zero_add, Nat.pow_one] at h1 h2
      have hn : (n == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
      have hd : n / 10 = 0 := by omega
      simp only [Num.digitsIn, hn, hd, Bool.false_eq_true, if_false, List.length_append,
        List.length_singleton]
      cases f <;> simp [Num.digitsIn]
  | succ m ih =>
    intro f n h1 h2 h3
    have e2 : 10 ^ (m + 1) = 10 ^ m * 10 := Nat.pow_succ ..
    have e3 : 10 ^ (m + 1 + 1) = 10 ^ m * 10 * 10 := by rw [Nat.pow_succ, Nat.pow_succ]
    have hp : 0 < 10 ^ m := Nat.pow_pos (by decide)
    rw [e2] at h1
    rw [e3] at h2
    cases f with
    | zero => omega
    | succ f =>
      have hn : (n == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
      simp only [Num.digitsIn, hn, Bool.false_eq_true, if_false, List.length_append,
        List.length_singleton]
      rw [ih f (n / 10) (by omega) (by rw [e2]; omega) (by omega)]

/-- The number of integer digits of a number with `l` of them. -/
theorem intLen_eq {x : Num} {l : Nat} (hl : 1 ≤ l) (h1 : l = 1 ∨ 10 ^ (l - 1) ≤ x.intPart)
    (h2 : x.intPart < 10 ^ l) : x.intLen = l := by
  unfold Num.intLen Num.digits
  rcases Nat.eq_zero_or_pos x.intPart with h0 | hp
  · rw [h0]
    rcases h1 with rfl | h1
    · simp [Num.digitsIn]
    · rw [h0] at h1; have := Nat.pow_pos (n := l - 1) (show 0 < 10 by decide); omega
  · rcases h1 with rfl | h1
    · rw [digitsIn_length 0 _ _ (by simp; omega) (by simpa using h2) (by omega)]; rfl
    · rw [digitsIn_length (l - 1) _ _ h1 (by rw [Nat.sub_add_cancel hl]; exact h2) (by omega)]
      omega

/-- `bc_compare (x, _one_)` of a non-negative `x`: its magnitude against
`10 ^ scale`. -/
theorem cmp_one {x : Num} (hx : x.neg = false) :
    Num.cmp x Num.one = compare x.mag (10 ^ x.scale) := by
  simp only [Num.cmp, Num.one, hx, bne_self_eq_false, Bool.false_eq_true, if_false, Num.cmpMag,
    Num.align, Nat.max_zero, Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.one_mul]

/-- `bc_int2num (l) * 0.5` at scale `0`. -/
theorem mul_half (l : Nat) (hl : 1 ≤ l) :
    Num.mul (Num.ofInt l) Num.half 0 = ⟨false, 5 * l, 1⟩ := by
  have e1 : min (0 + 1) (max 0 (max 0 1)) = 1 := rfl
  have h5 : (l : Int).natAbs * 5 / 10 ^ (0 + 1 - 1) = 5 * l := by
    rw [Int.natAbs_natCast]; simp only [Nat.zero_add, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    omega
  have : (5 * l == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  simp only [Num.mul, Num.ofInt, Num.half, e1, h5, this, Bool.false_eq_true, if_false,
    show ¬ ((l : Int) < 0) from by omega, decide_false, bne_self_eq_false]

/-- The first guess above one. -/
theorem sqrtInit_hi {x : Num} (hc : Num.cmp x Num.one ≠ .lt) (hu : x.intLen / 2 < 2 ^ 31) :
    Num.sqrtInit x = (⟨false, 10 ^ (x.intLen / 2), 0⟩, 3) := by
  unfold Num.sqrtInit
  rw [if_neg (by simpa using hc), raise_ten _ (by unfold Num.longMax; omega)]

/-- The first guess below one. -/
theorem sqrtInit_lo {x : Num} (hc : Num.cmp x Num.one = .lt) :
    Num.sqrtInit x = (Num.one, x.scale) := by
  unfold Num.sqrtInit
  rw [if_pos (by simp [hc])]

end Dc.BcModel
