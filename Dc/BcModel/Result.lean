import Dc.BcModel.Div

/-!
# Truncated results of `bc_multiply` and `bc_divide`

`bc_multiply` reads the first `n_len + prod_scale` digits of the full
product array; `bc_divide` divides the first `len1 + scale + 1` digits of
`num1` (a leading zero, `n1`'s digits, zero padding) by `n2`'s digits with
trailing fraction zeros dropped. These lemmas take those digit-level reads
to the magnitudes of `Num.mul` and `Num.div`.
-/

namespace Dc.BcModel

theorem dvalBE_lt {ds : List Nat} (h : IsDigits ds) : dvalBE ds < 10 ^ ds.length := by
  rw [← dvalLE_reverse, ← List.length_reverse]
  exact dvalLE_lt fun d hd => h d (List.mem_reverse.mp hd)

/-- The value of a prefix of a digit list is the value of the whole list with
the dropped digits divided away. -/
theorem dvalBE_take {ds : List Nat} (h : IsDigits ds) (k : Nat) :
    dvalBE (ds.take k) = dvalBE ds / 10 ^ (ds.length - k) := by
  have hsplit := dvalBE_append (ds.take k) (ds.drop k)
  rw [List.take_append_drop] at hsplit
  have hlt : dvalBE (ds.drop k) < 10 ^ (ds.drop k).length :=
    dvalBE_lt fun d hd => h d (List.mem_of_mem_drop hd)
  rw [List.length_drop] at hsplit hlt
  rw [hsplit, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- `bc_multiply`: the product array holds `a·b` in `len` digits with `full`
fraction digits; reading `len - full + ps` of them (`n_len`, `n_scale = ps`)
gives `Num.mul`'s magnitude. -/
theorem mul_trunc {ds : List Nat} (h : IsDigits ds) {full ps : Nat} (hps : ps ≤ full)
    (hfull : full ≤ ds.length) :
    dvalBE (ds.take (ds.length - full + ps)) = dvalBE ds / 10 ^ (full - ps) := by
  rw [dvalBE_take h]; congr 2; omega

/-- `Num.mul`'s magnitude through the product array. -/
theorem num_mul_mag (a b : Num) (k : Nat) :
    (Num.mul a b k).mag = a.mag * b.mag / 10 ^ (a.scale + b.scale -
      min (a.scale + b.scale) (max k (max a.scale b.scale))) := rfl

/-- `Num.mul`'s scale. -/
theorem num_mul_scale (a b : Num) (k : Nat) :
    (Num.mul a b k).scale = min (a.scale + b.scale) (max k (max a.scale b.scale)) := rfl

/-! ## Division -/

/-- `bc_divide`'s quotient value. `B = V·10^(sb - s2)` (`s2` is `n2`'s
scale with trailing zeros dropped); the dividend digits read are `A`
shifted by `s2 + k` fraction positions and truncated at `sa`. -/
theorem div_value (A B V sa sb s2 k : Nat) (hs2 : s2 ≤ sb) (hB : B = V * 10 ^ (sb - s2)) :
    A * 10 ^ (sb + k) / (B * 10 ^ sa) = A * 10 ^ (s2 + k) / 10 ^ sa / V := by
  rw [Nat.div_div_eq_div_mul, hB, show sb + k = (sb - s2) + (s2 + k) by omega, Nat.pow_add,
    show A * (10 ^ (sb - s2) * 10 ^ (s2 + k)) = 10 ^ (sb - s2) * (A * 10 ^ (s2 + k)) by ac_rfl,
    show V * 10 ^ (sb - s2) * 10 ^ sa = 10 ^ (sb - s2) * (10 ^ sa * V) by ac_rfl,
    Nat.mul_div_mul_left _ _ (Nat.pow_pos (by decide))]

/-- The dividend digits `bc_divide` reads: `A` at `sa` fraction digits,
shifted to `t` fraction digits (zero padding below, truncation above). -/
theorem shift_value (A sa t : Nat) :
    A * 10 ^ t / 10 ^ sa = if sa ≤ t then A * 10 ^ (t - sa) else A / 10 ^ (sa - t) := by
  split
  · rename_i h
    rw [show t = (t - sa) + sa by omega, Nat.pow_add, ← Nat.mul_assoc,
      Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]
    congr 2; omega
  · rename_i h
    rw [show sa = (sa - t) + t by omega, Nat.pow_add, Nat.mul_comm (10 ^ (sa - t)),
      ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]
    congr 2; omega

/-- Normalisation by `norm` (`_one_mult` of both operands) leaves each
quotient unchanged. -/
theorem norm_div (n X V : Nat) (hn : 0 < n) : n * X / (n * V) = X / V :=
  Nat.mul_div_mul_left _ _ hn

/-- The zero-quotient branch (`len2 > len1 + scale`): a dividend with fewer
digits than the divisor divides to zero. -/
theorem div_small {X V m : Nat} (hX : X < 10 ^ m) (hV : 10 ^ m ≤ V) : X / V = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hX hV)

/-- A divisor whose top digit is nonzero is at least `10^(len-1)`. -/
theorem dvalBE_ge_top {d : Nat} {ds : List Nat} (hd : 0 < d) :
    10 ^ ds.length ≤ dvalBE (d :: ds) := by
  rw [dvalBE_cons]
  exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ hd)

/-- The remainder entering the first division step: a leading zero followed
by `len2 - 1` digits is below a divisor with a nonzero top digit of `len2`
digits. -/
theorem first_window_lt {xs : List Nat} (hx : IsDigits xs) {d : Nat} {ds : List Nat} (hd : 0 < d)
    (hlen : xs.length ≤ ds.length) : dvalBE xs < dvalBE (d :: ds) :=
  Nat.lt_of_lt_of_le (dvalBE_lt hx)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) hlen) (dvalBE_ge_top hd))

/-- `bc_divide`'s loop: long division of the window digits from the first
remainder computes the quotient of the whole prefix. -/
theorem longDiv_prefix (D : Nat) (hD : 0 < D) (pre xs : List Nat) (hpre : dvalBE pre < D) :
    dvalBE (longDiv D (dvalBE pre) xs).1 = dvalBE (pre ++ xs) / D := by
  have hv := longDiv_val D (dvalBE pre) xs
  have hr := longDiv_rem D hD (dvalBE pre) xs hpre
  rw [dvalBE_append, ← hv, Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hr,
    Nat.zero_add]

end Dc.BcModel
