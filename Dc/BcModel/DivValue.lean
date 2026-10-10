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


/-! ## Big-endian digits of a value -/

/-- The `n` low digits of `X`, big-endian. -/
abbrev digBE (X n : Nat) : List Nat := (digLE X n).reverse

theorem digBE_length (X n : Nat) : (digBE X n).length = n := by
  rw [List.length_reverse, digLE_length]

theorem digBE_digits (X n : Nat) : IsDigits (digBE X n) := fun d hd =>
  digLE_digits X n d (List.mem_reverse.mp hd)

theorem digBE_getD {X n i : Nat} (hi : i < n) : (digBE X n).getD i 0 = X / 10 ^ (n - 1 - i) % 10 := by
  have hl := digLE_length X n
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega), hl, ← List.getD_eq_getElem?_getD,
    digLE_getD _ _ _ (by omega)]

theorem digBE_val (X n : Nat) : dvalBE (digBE X n) = X % 10 ^ n := by
  rw [dvalBE_reverse, digLE_val]

/-- A digit list is the big-endian digits of its value. -/
theorem digBE_self {xs : List Nat} (h : IsDigits xs) : digBE (dvalBE xs) xs.length = xs := by
  apply List.ext_getElem (digBE_length _ _)
  intro i h1 h2
  have e := digBE_getD (X := dvalBE xs) (n := xs.length) (i := i) h2
  rw [dvalBE_digit h h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at e
  simpa using e

end Dc.BcModel
