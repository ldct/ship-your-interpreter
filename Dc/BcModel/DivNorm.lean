import Dc.BcModel.DivValue
import Dc.BcModel.Result

/-!
# `bc_divide`'s normalised operands

`bc_divide` multiplies the dividend buffer `xs0` (a leading zero) and the
divisor `vs0` (a nonzero top digit) by `norm = 10 / (vs0[0] + 1)`:

- `normDiv_val`: the normalised divisor keeps its length, `norm · 10^(L-1)`
  is below it and its top digit is at least 5;
- `normDiv_first`: the normalised dividend's first `L` digits are below the
  normalised divisor;
- `normDiv_quot`: the quotient of a normalised prefix by the normalised
  divisor is the quotient of the raw prefix by the raw divisor.
-/

namespace Dc.BcModel

/-- A prefix of the big-endian digits of `Y < 10^T`: `Y` with the dropped
digits divided away. -/
theorem digBE_take_val {Y T m : Nat} (hY : Y < 10 ^ T) (hm : m ≤ T) :
    dvalBE ((digBE Y T).take m) = Y / 10 ^ (T - m) := by
  rw [dvalBE_take (digBE_digits Y T), digBE_val, digBE_length, Nat.mod_eq_of_lt hY]

/-- **The normalised divisor**: `V0 · norm` has `L` digits, at least
`norm · 10^(L-1)`, its top digit at least 5. -/
theorem normDiv_val {vs0 : List Nat} (hd : IsDigits vs0) (hl : 1 ≤ vs0.length)
    (h0 : 0 < vs0.getD 0 0) :
    dvalBE vs0 * (10 / (vs0.getD 0 0 + 1)) < 10 ^ vs0.length ∧
    10 ^ (vs0.length - 1) * (10 / (vs0.getD 0 0 + 1)) ≤ dvalBE vs0 * (10 / (vs0.getD 0 0 + 1)) ∧
    5 ≤ (digBE (dvalBE vs0 * (10 / (vs0.getD 0 0 + 1))) vs0.length).getD 0 0 := by
  obtain ⟨v1, rest, rfl⟩ : ∃ v1 rest, vs0 = v1 :: rest := by
    cases vs0 with
    | nil => simp at hl
    | cons a l => exact ⟨a, l, rfl⟩
  simp only [List.getD_cons_zero, List.length_cons, Nat.add_sub_cancel] at h0 ⊢
  have hv1 : v1 < 10 := hd v1 List.mem_cons_self
  have hr : dvalBE rest < 10 ^ rest.length := dvalBE_lt fun d hd' => hd d (List.mem_cons_of_mem _ hd')
  obtain ⟨hb1, hb2⟩ := norm_bounds h0 hv1 hr
  have hn := norm_pos h0 hv1
  rw [dvalBE_cons]
  have hE : 0 < 10 ^ rest.length := Nat.pow_pos (by decide)
  refine ⟨by rw [Nat.pow_succ, Nat.mul_comm _ 10]; exact hb1, ?_, ?_⟩
  · have : 10 ^ rest.length ≤ v1 * 10 ^ rest.length + dvalBE rest := by
      have := Nat.le_mul_of_pos_left (10 ^ rest.length) h0; omega
    exact Nat.mul_le_mul_right _ this
  · rw [digBE_getD (by omega), Nat.add_sub_cancel, Nat.sub_zero]
    generalize (v1 * 10 ^ rest.length + dvalBE rest) * (10 / (v1 + 1)) = Y at hb1 hb2
    have h1 : 5 ≤ Y / 10 ^ rest.length := (Nat.le_div_iff_mul_le hE).mpr hb2
    have h2 : Y / 10 ^ rest.length < 10 := (Nat.div_lt_iff_lt_mul hE).mpr hb1
    omega

/-- **The first window**: the normalised dividend's first `L` digits are below
the normalised divisor when the dividend starts with a zero. -/
theorem normDiv_first {xs0 : List Nat} {V0 nm L : Nat} (hd : IsDigits xs0) (hl : L < xs0.length)
    (h0 : xs0.getD 0 0 = 0) (hn : 0 < nm) (hV : 10 ^ (L - 1) * nm ≤ V0 * nm) (hL : 1 ≤ L)
    (hX : dvalBE xs0 * nm < 10 ^ xs0.length) :
    dvalBE ((digBE (dvalBE xs0 * nm) xs0.length).take L) < V0 * nm := by
  rw [digBE_take_val hX (by omega)]
  obtain ⟨rest, rfl⟩ : ∃ rest, xs0 = 0 :: rest := by
    cases xs0 with
    | nil => simp at hl
    | cons a l => simp only [List.getD_cons_zero] at h0; exact ⟨l, by rw [h0]⟩
  simp only [List.length_cons] at hl ⊢
  rw [dvalBE_cons, Nat.zero_mul, Nat.zero_add]
  have hr : dvalBE rest < 10 ^ rest.length := dvalBE_lt fun d hd' => hd d (List.mem_cons_of_mem _ hd')
  have hE : 0 < 10 ^ (rest.length + 1 - L) := Nat.pow_pos (by decide)
  refine Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul hE).mpr ?_) hV
  rw [show 10 ^ (L - 1) * nm * 10 ^ (rest.length + 1 - L) = nm * 10 ^ rest.length by
    rw [Nat.mul_comm (10 ^ (L - 1)), Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega,
    Nat.mul_comm]
  exact Nat.mul_lt_mul_of_pos_left hr hn

/-- **The quotient through normalisation**: the normalised prefix of `m`
digits over the normalised divisor is the raw prefix over the raw divisor. -/
theorem normDiv_quot {xs0 : List Nat} {V0 nm m : Nat} (hd : IsDigits xs0) (hm : m ≤ xs0.length)
    (hn : 0 < nm) (hV : 0 < V0) (hX : dvalBE xs0 * nm < 10 ^ xs0.length) :
    dvalBE ((digBE (dvalBE xs0 * nm) xs0.length).take m) / (V0 * nm) =
      dvalBE (xs0.take m) / V0 := by
  rw [digBE_take_val hX hm, dvalBE_take hd]
  generalize xs0.length - m = j
  have hT : 0 < 10 ^ j := Nat.pow_pos (by decide)
  have e := norm_trunc (n := nm) (X := dvalBE xs0 / 10 ^ j) (Y := dvalBE xs0 % 10 ^ j) (T := 10 ^ j)
    (V := V0) hn hV (Nat.mod_lt _ hT)
  rw [Nat.div_add_mod', Nat.mul_comm nm V0] at e
  rw [Nat.mul_comm (dvalBE xs0) nm, e]

/-- Trailing zeros scale the value. -/
theorem dvalBE_append_zeros (xs : List Nat) (e : Nat) :
    dvalBE (xs ++ List.replicate e 0) = dvalBE xs * 10 ^ e := by
  rw [dvalBE_append, dvalBE_replicate_zero, List.length_replicate, Nat.add_zero]

/-- Leading zeros do not change the value. -/
theorem dvalBE_zeros_append (z : Nat) (xs : List Nat) :
    dvalBE (List.replicate z 0 ++ xs) = dvalBE xs := by
  rw [dvalBE_append, dvalBE_replicate_zero, Nat.zero_mul, Nat.zero_add]

/-- **The dividend buffer's prefix**: the first `m` digits of `ds` padded with
`e` zeros are `A · 10^m / 10^|ds|`. -/
theorem dvalBE_take_padded {ds : List Nat} (hd : IsDigits ds) {e m : Nat} (hm : m ≤ ds.length + e) :
    dvalBE ((ds ++ List.replicate e 0).take m) = dvalBE ds * 10 ^ m / 10 ^ ds.length := by
  rw [shift_value]
  split
  · rename_i h
    rw [List.take_append, List.take_of_length_le h, List.take_replicate, dvalBE_append_zeros]
    congr 2; omega
  · rename_i h
    rw [List.take_append_of_le_length (by omega), dvalBE_take hd]

/-- A list whose digits past `n` are zero: its value is its first `n`
digits' shifted. -/
theorem dvalBE_take_zeros {ds : List Nat} {n : Nat} (hn : n ≤ ds.length)
    (hz : ∀ i, n ≤ i → i < ds.length → ds.getD i 0 = 0) :
    dvalBE ds = dvalBE (ds.take n) * 10 ^ (ds.length - n) := by
  have hdr : ds.drop n = List.replicate (ds.length - n) 0 := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by rw [List.length_drop], fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    rw [List.getElem_drop]
    have := hz (n + i) (by omega) (by rw [List.length_drop] at hi; omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_drop] at hi; omega)] at this
    exact this
  calc dvalBE ds = dvalBE (ds.take n ++ ds.drop n) := by rw [List.take_append_drop]
    _ = _ := by rw [hdr, dvalBE_append_zeros]

/-- A list whose first `z` digits are zero has the value of the rest. -/
theorem dvalBE_drop_zeros {ds : List Nat} {z : Nat} (hz : ∀ i, i < z → ds.getD i 0 = 0)
    (hl : z ≤ ds.length) : dvalBE ds = dvalBE (ds.drop z) := by
  have hdr : ds.take z = List.replicate z 0 := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by rw [List.length_take]; omega, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    rw [List.length_take] at hi
    rw [List.getElem_take]
    have := hz i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
    exact this
  calc dvalBE ds = dvalBE (ds.take z ++ ds.drop z) := by rw [List.take_append_drop]
    _ = _ := by rw [hdr, dvalBE_zeros_append]

/-- **The dividend buffer's prefix**: `0`, `ds` (`l + sa` digits), the zero
padding; its first `l + s2 + k + 1` digits are `A · 10^(s2+k) / 10^sa`. -/
theorem dvx_take_val {ds : List Nat} (hd : IsDigits ds) {l sa s2 k : Nat} (hl : ds.length = l + sa) :
    dvalBE ((0 :: ds ++ List.replicate (k + s2 - sa + 1) 0).take (l + s2 + k + 1)) =
      dvalBE ds * 10 ^ (s2 + k) / 10 ^ sa := by
  rw [List.cons_append, List.take_succ_cons, dvalBE_cons, Nat.zero_mul, Nat.zero_add,
    dvalBE_take_padded hd (by rw [hl]; omega), hl,
    show l + s2 + k = l + (s2 + k) by omega, Nat.pow_add 10 l (s2 + k), Nat.pow_add 10 l sa,
    show dvalBE ds * (10 ^ l * 10 ^ (s2 + k)) = 10 ^ l * (dvalBE ds * 10 ^ (s2 + k)) by ac_rfl,
    Nat.mul_div_mul_left _ _ (Nat.pow_pos (by decide : 0 < 10))]

/-- **The divisor's digits**: `ds` (`ln + sb` digits) zero past `ln + s2` and
before `z0` is `dvalBE vs0 · 10^(sb - s2)` with `vs0` the digits between. -/
theorem dv2_val {ds : List Nat} {ln sb s2 z0 : Nat} (hl : ds.length = ln + sb) (hs : s2 ≤ sb)
    (htz : ∀ j, s2 ≤ j → j < sb → ds.getD (ln + j) 0 = 0) (hz : ∀ i, i < z0 → ds.getD i 0 = 0)
    (hz0 : z0 ≤ ln + s2) :
    dvalBE ds = dvalBE ((ds.take (ln + s2)).drop z0) * 10 ^ (sb - s2) := by
  rw [dvalBE_take_zeros (n := ln + s2) (by omega) fun i h1 h2 => by
    rw [show i = ln + (i - ln) by omega]; exact htz _ (by omega) (by omega)]
  rw [hl, show ln + sb - (ln + s2) = sb - s2 by omega]
  congr 1
  refine dvalBE_drop_zeros (fun i hi => ?_) (by rw [List.length_take]; omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by omega), ← List.getD_eq_getElem?_getD]
  exact hz i hi

/-- A digit list with a nonzero first digit is at least `10^(length - 1)`. -/
theorem dvalBE_ge_of_first {vs : List Nat} (hl : 1 ≤ vs.length) (h0 : 0 < vs.getD 0 0) :
    10 ^ (vs.length - 1) ≤ dvalBE vs := by
  obtain ⟨v1, rest, rfl⟩ : ∃ v1 rest, vs = v1 :: rest := by
    cases vs with
    | nil => simp at hl
    | cons a l => exact ⟨a, l, rfl⟩
  simp only [List.getD_cons_zero, List.length_cons, Nat.add_sub_cancel] at h0 ⊢
  rw [dvalBE_cons]
  have := Nat.le_mul_of_pos_left (10 ^ rest.length) h0
  omega

/-- **A short dividend**: `A < 10^(l + sa)` with `l + s2 + k < L` over a
divisor of `L` digits at least `10^(L-1)` has quotient zero. -/
theorem dv_short_zero {A V l sa s2 k L : Nat} (hA : A < 10 ^ (l + sa)) (hL : l + s2 + k < L)
    (hV : 10 ^ (L - 1) ≤ V) : A * 10 ^ (s2 + k) / 10 ^ sa / V = 0 := by
  apply Nat.div_eq_of_lt
  refine Nat.lt_of_lt_of_le ?_ (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : l + s2 + k ≤ L - 1)) hV)
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 10)), ← Nat.pow_add,
    show l + s2 + k + sa = (l + sa) + (s2 + k) by omega, Nat.pow_add 10 (l + sa) (s2 + k)]
  exact Nat.mul_lt_mul_of_pos_right hA (Nat.pow_pos (n := s2 + k) (by decide : 0 < 10))

end Dc.BcModel
