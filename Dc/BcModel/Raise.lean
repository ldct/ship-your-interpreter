import Dc.Num

/-!
# The repeated squaring of `bc_raise`

`bc_raise` squares `power` at `pwrscale = 2 * pwrscale` and multiplies it
into `temp` at `calcscale = pwrscale + calcscale`; both scales are the full
scale of the product, so no step truncates. `mul_powExact` is the exact
product of two powers; `RaiseInv` is the invariant of the second loop
(`u = T + 2·P·e` with `temp = a^T`, `power = a^P`).
-/

namespace Dc.BcModel

open Dc

/-- `bc_multiply` at a scale at least the full scale is exact. -/
theorem mul_exact (a b : Num) (k : Nat) (hk : a.scale + b.scale ≤ k) :
    Num.mul a b k =
      ⟨if a.mag * b.mag == 0 then false else a.neg != b.neg, a.mag * b.mag, a.scale + b.scale⟩ := by
  have hps : min (a.scale + b.scale) (max k (max a.scale b.scale)) = a.scale + b.scale := by
    omega
  simp only [Num.mul, hps, Nat.sub_self, Nat.pow_zero, Nat.div_one]

theorem powExact_scale (a : Num) (u : Nat) : (Num.powExact a u).scale = a.scale * u := rfl

theorem powExact_mag (a : Num) (u : Nat) : (Num.powExact a u).mag = a.mag ^ u := rfl

/-- The exact product of two powers of `a` is a power of `a`. -/
theorem mul_powExact (a : Num) (m n k : Nat) (hk : a.scale * m + a.scale * n ≤ k) :
    Num.mul (Num.powExact a m) (Num.powExact a n) k = Num.powExact a (m + n) := by
  rw [mul_exact _ _ _ hk]
  simp only [Num.powExact, ← Nat.pow_add, Nat.mul_add]
  congr 1
  by_cases h0 : a.mag ^ (m + n) = 0
  · simp [h0]
  · have hm : a.mag ^ m ≠ 0 := by
      intro h; apply h0; rw [Nat.pow_add, h, Nat.zero_mul]
    have hn : a.mag ^ n ≠ 0 := by
      intro h; apply h0; rw [Nat.pow_add, h, Nat.mul_zero]
    simp only [h0, hm, hn, beq_iff_eq, ite_false]
    cases a.neg <;> simp only [Bool.false_and, Bool.true_and, bne_self_eq_false] <;>
      rcases Nat.mod_two_eq_zero_or_one m with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;>
      simp [h1, h2, Nat.add_mod]

/-- `power = bc_copy_num (num1)`. -/
theorem powExact_one (a : Num) (h : a.neg = true → a.mag ≠ 0) : Num.powExact a 1 = a := by
  cases a with
  | mk neg mag scale =>
    simp only [Num.powExact, Nat.pow_one, Nat.mul_one]
    congr 1
    cases neg <;> simp_all

/-- The invariant of `bc_raise`'s second loop: `temp = a^T`, `power = a^P`,
the remaining exponent `e`, with `u = T + 2·P·e`. -/
structure RaiseInv (u T P e : Nat) : Prop where
  total : u = T + 2 * P * e

/-- Entry to the second loop: after the first loop `power = a^(2^i)` with
the odd exponent `2e + 1` left, `temp := power` and `exponent >>= 1`. -/
theorem RaiseInv.init {u i e : Nat} (hu : u = 2 ^ i * (2 * e + 1)) :
    RaiseInv u (2 ^ i) (2 ^ i) e :=
  ⟨by rw [hu, Nat.mul_add, Nat.mul_one, Nat.add_comm, ← Nat.mul_assoc, Nat.mul_comm (2 ^ i) 2]⟩

/-- One iteration: `power := power²`; when the exponent is odd
`temp := temp · power`; `exponent >>= 1`. -/
theorem RaiseInv.step {u T P e : Nat} (h : RaiseInv u T P e) :
    RaiseInv u (if e % 2 = 1 then T + 2 * P else T) (2 * P) (e / 2) := by
  constructor
  have key : 2 * P * e = 2 * (2 * P) * (e / 2) + 2 * P * (e % 2) := by
    conv => lhs; rw [← Nat.div_add_mod e 2]
    rw [Nat.mul_add, ← Nat.mul_assoc (2 * P) 2, Nat.mul_comm (2 * P) 2]
  rw [h.total, key]
  generalize 2 * (2 * P) * (e / 2) = X
  split
  · rename_i ho; rw [ho, Nat.mul_one]; omega
  · have : e % 2 = 0 := by omega
    rw [this, Nat.mul_zero, Nat.add_zero]

/-- Exit: with no exponent left, `temp = a^u`. -/
theorem RaiseInv.done {u T P : Nat} (h : RaiseInv u T P 0) : T = u := by
  have := h.total; simp at this; omega

/-- The first loop: while the exponent is even, square. -/
theorem raise_first_step {u i e : Nat} (hu : u = 2 ^ i * e) (he : e % 2 = 0) :
    u = 2 ^ (i + 1) * (e / 2) := by
  rw [hu, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he)]

end Dc.BcModel
