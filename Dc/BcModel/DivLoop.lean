import Dc.BcModel.Result

/-!
# Digit arithmetic of `bc_divide`'s loops

- `div_pow_mod_low`, `dvalBE_digit`, `dvalBE_drop_pred`: the digits of a
  product `_one_mult` stores, read off its value.
-/

namespace Dc.BcModel

/-- A digit below position `k` does not see what is added at `10^k`. -/
theorem div_pow_mod_low (A B k j : Nat) (hj : j < k) :
    (A * 10 ^ k + B) / 10 ^ j % 10 = B / 10 ^ j % 10 := by
  have h : A * 10 ^ k = (A * 10 ^ (k - j - 1)) * 10 * 10 ^ j := by
    rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_succ', ← Nat.pow_add]
    congr 2; omega
  rw [h, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
    Nat.add_mul_mod_self_right]

/-- Digit `i` (big-endian) of a digit list, read off its value. -/
theorem dvalBE_digit {xs : List Nat} (h : IsDigits xs) {i : Nat} (hi : i < xs.length) :
    dvalBE xs / 10 ^ (xs.length - 1 - i) % 10 = xs.getD i 0 := by
  have e := dvalBE_append (xs.take (i + 1)) (xs.drop (i + 1))
  rw [List.take_append_drop] at e
  have hl : (xs.drop (i + 1)).length = xs.length - 1 - i := by
    simp only [List.length_drop]; omega
  have hd : IsDigits (xs.drop (i + 1)) := fun d hd => h d (List.mem_of_mem_drop hd)
  have hlt := dvalBE_lt hd
  rw [hl] at e hlt
  rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [List.take_succ, List.getElem?_eq_getElem hi, Option.toList_some, dvalBE_append]
  have hx := h _ (List.getElem_mem hi)
  simp only [List.length_singleton, Nat.pow_one, dvalBE, List.foldl_cons, List.foldl_nil,
    Nat.mul_zero, Nat.zero_add]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

/-- One more digit of a suffix. -/
theorem dvalBE_drop_pred {xs : List Nat} {m : Nat} (hm : 0 < m) (hml : m ≤ xs.length) :
    dvalBE (xs.drop (m - 1)) = xs.getD (m - 1) 0 * 10 ^ (xs.length - m) + dvalBE (xs.drop m) := by
  rw [List.drop_eq_getElem_cons (show m - 1 < xs.length by omega), dvalBE_cons,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m - 1 < xs.length by omega),
    Option.getD_some, List.length_drop, show m - 1 + 1 = m by omega]

/-- `_one_mult`'s step at the `k`-th last digit `x`: with `c` the carry of
the last `k` digits, the next digit of `dvalBE xs · d` and the next carry. -/
theorem oneMult_step {xs : List Nat} {n k d : Nat} (hn : xs.length = n) (hk : k < n) :
    dvalBE xs * d / 10 ^ k % 10 =
        (xs.getD (n - 1 - k) 0 * d + dvalBE (xs.drop (n - k)) * d / 10 ^ k) % 10 ∧
      dvalBE (xs.drop (n - (k + 1))) * d / 10 ^ (k + 1) =
        (xs.getD (n - 1 - k) 0 * d + dvalBE (xs.drop (n - k)) * d / 10 ^ k) / 10 := by
  have e1 := dvalBE_drop_pred (xs := xs) (m := n - k) (by omega) (by omega)
  rw [show n - k - 1 = n - (k + 1) by omega, hn, show n - (n - k) = k by omega,
    show n - (k + 1) = n - 1 - k by omega] at e1
  have hp : 0 < 10 ^ k := Nat.pow_pos (by decide)
  have e2 : dvalBE (xs.drop (n - (k + 1))) * d / 10 ^ k =
      xs.getD (n - 1 - k) 0 * d + dvalBE (xs.drop (n - k)) * d / 10 ^ k := by
    rw [show n - (k + 1) = n - 1 - k by omega, e1, Nat.add_mul,
      show xs.getD (n - 1 - k) 0 * 10 ^ k * d = xs.getD (n - 1 - k) 0 * d * 10 ^ k by ac_rfl,
      Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.add_comm]
  have e3 := dvalBE_append (xs.take (n - (k + 1))) (xs.drop (n - (k + 1)))
  rw [List.take_append_drop, List.length_drop, hn, show n - (n - (k + 1)) = k + 1 by omega] at e3
  refine ⟨?_, ?_⟩
  · rw [e3, Nat.add_mul, show dvalBE (List.take (n - (k + 1)) xs) * 10 ^ (k + 1) * d =
      dvalBE (List.take (n - (k + 1)) xs) * d * 10 ^ (k + 1) by ac_rfl,
      div_pow_mod_low _ _ _ _ (Nat.lt_succ_self k), e2]
  · rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, e2]

end Dc.BcModel
