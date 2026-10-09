import Dc.BcModel.DivGuess

/-!
# `bc_divide`'s quotient value

- `dvalBE_eq_of_getD`: a digit list whose digits are those of `X < 10^n` has
  value `X`.
- `quot_digits_val`: the quotient array (`off` leading zeros, then the
  `K + 1` digits of `Q`) has value `Q`.
-/

namespace Dc.BcModel

/-- A digit list read off a value: its digits are `X`'s, so its value is `X`. -/
theorem dvalBE_eq_of_getD : ∀ {xs : List Nat} {X : Nat}, IsDigits xs → X < 10 ^ xs.length →
    (∀ i, i < xs.length → xs.getD i 0 = X / 10 ^ (xs.length - 1 - i) % 10) → dvalBE xs = X
  | [], X, _, hX, _ => by simp only [List.length_nil, Nat.pow_zero] at hX; rw [dvalBE_nil]; omega
  | d :: ds, X, hd, hX, h => by
    rw [dvalBE_cons]
    have hds : IsDigits ds := fun e he => hd e (List.mem_cons_of_mem _ he)
    simp only [List.length_cons] at hX h
    have hp : 0 < 10 ^ ds.length := Nat.pow_pos (by decide)
    have h0 := h 0 (by omega)
    simp only [List.getD_cons_zero, Nat.sub_zero, Nat.add_sub_cancel] at h0
    have hm : X / 10 ^ ds.length < 10 := by
      rw [Nat.div_lt_iff_lt_mul hp]; rw [Nat.pow_succ] at hX; rwa [Nat.mul_comm]
    rw [Nat.mod_eq_of_lt hm] at h0
    have ih := dvalBE_eq_of_getD (X := X % 10 ^ ds.length) hds (Nat.mod_lt _ hp) fun i hi => by
      have e := h (i + 1) (by omega)
      simp only [List.getD_cons_succ] at e
      rw [e, show ds.length + 1 - 1 - (i + 1) = ds.length - 1 - i by omega]
      have := div_pow_mod_low (X / 10 ^ ds.length) (X % 10 ^ ds.length) ds.length
        (ds.length - 1 - i) (by omega)
      rw [Nat.mul_comm, Nat.div_add_mod] at this
      exact this
    rw [ih, h0, Nat.mul_comm, Nat.div_add_mod]

/-- **The quotient array's value**: `off` leading zeros, then the `K + 1`
digits of `Q < 10^(K+1)`. -/
theorem quot_digits_val {ds : List Nat} {off K Q : Nat} (hl : ds.length = off + K + 1)
    (hd : IsDigits ds) (hz : ∀ j, j < off → ds.getD j 0 = 0)
    (hq : ∀ j, j < K + 1 → ds.getD (off + j) 0 = Q / 10 ^ (K - j) % 10)
    (hQ : Q < 10 ^ (K + 1)) : dvalBE ds = Q := by
  refine dvalBE_eq_of_getD hd (Nat.lt_of_lt_of_le hQ (Nat.pow_le_pow_right (by decide) (by omega)))
    fun i hi => ?_
  rcases Nat.lt_or_ge i off with h | h
  · rw [hz i h, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hQ (Nat.pow_le_pow_right (by decide)
      (by omega)))]
  · have e := hq (i - off) (by omega)
    rw [show off + (i - off) = i by omega] at e
    rw [e, hl]; congr 3; omega

end Dc.BcModel
