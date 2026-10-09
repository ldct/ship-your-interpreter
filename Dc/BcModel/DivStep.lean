import Dc.BcModel.DivLoop

/-!
# One step of `bc_divide`'s long division

The window `w` (`L + 1` digits, little-endian, value `W`) and the
normalised divisor `v` (`L` digits, value `V`). With the guess `g` (`W / V`
or `W / V + 1`, `guess_spec`) and `m` the `L + 1` digits of `V · g`
(`_one_mult`), the machine subtracts `m` from the window with borrow
(`subLE`); when the subtraction borrows it lowers the digit and adds `v`
back over the low `L` positions, bumping the top digit by the final carry
mod 10 (`addBack`).

- `step_spec`: the stored digit is `W / V`, the new window `W % V`.
- `step_zero`: a zero guess (the machine skips the subtraction).
- `norm_bounds`: normalisation by `10 / (v1 + 1)` keeps `L` digits with a
  top digit of at least 5.
- `norm_trunc`: the quotient of the normalised dividend's truncated prefix.
- `div_snoc`: the quotient and remainder after one more dividend digit.
-/

namespace Dc.BcModel

/-- The add-back of a borrowing step: `v` added with carry to the low
`v.length` digits of `s`, the top digit bumped by the final carry mod 10. -/
def addBack (s v : List Nat) : List Nat :=
  (addLE (s.take v.length) v 0).take v.length ++
    [(s.getD v.length 0 + (addLE (s.take v.length) v 0).getD v.length 0) % 10]

/-- One step's new window: `w - m` with borrow, then the add-back when it
borrowed. -/
def stepWin (w m v : List Nat) : List Nat :=
  if subBorrow w m 0 = 1 then addBack (subLE w m 0) v else subLE w m 0

/-- The result of one step. -/
structure StepRes (w m v : List Nat) (g : Nat) : Prop where
  dig : g - subBorrow w m 0 = dvalLE w / dvalLE v
  val : dvalLE (stepWin w m v) = dvalLE w % dvalLE v
  digits : IsDigits (stepWin w m v)
  len : (stepWin w m v).length = v.length + 1

theorem dvalLE_take_last {xs : List Nat} {n : Nat} (h : xs.length = n + 1) :
    dvalLE xs = dvalLE (xs.take n) + 10 ^ n * xs.getD n 0 := by
  have e : xs = xs.take n ++ [xs.getD n 0] := by
    apply List.ext_getElem
    · simp only [List.length_append, List.length_take, List.length_singleton]; omega
    · intro i h1 h2
      rw [List.getElem_append]
      split
      · simp
      · simp only [List.getElem_singleton, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        simp only [List.length_take] at *
        congr 1; omega
  conv => lhs; rw [e]
  rw [dvalLE_append, List.length_take, show min n xs.length = n by omega]
  simp only [dvalLE, Nat.mul_zero, Nat.add_zero]

theorem IsDigits.take {xs : List Nat} (h : IsDigits xs) (n : Nat) : IsDigits (xs.take n) :=
  fun d hd => h d (List.mem_of_mem_take hd)

theorem IsDigits.getD {xs : List Nat} (h : IsDigits xs) (i : Nat) : xs.getD i 0 < 10 := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : xs[i]? with
  | none => simp
  | some d => exact h d (List.mem_of_getElem? hx)

/-- `A + P k = R + 10 P` with `A, R < P` forces `A = R`, `k = 10`. -/
theorem split_pow {A R P k : Nat} (hA : A < P) (hR : R < P) (e : A + P * k = R + P * 10) :
    A = R ∧ k = 10 := by
  have hP : 0 < P := by omega
  have h1 := congrArg (· % P) e
  have h2 := congrArg (· / P) e
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hR] at h1
  simp only [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hA, Nat.div_eq_of_lt hR] at h2
  omega

/-- **One division step.** -/
theorem step_spec {w m v : List Nat} {g : Nat} (hw : IsDigits w) (hm : IsDigits m)
    (hv : IsDigits v) (hlw : w.length = v.length + 1) (hlm : m.length = v.length + 1)
    (hmv : dvalLE m = dvalLE v * g) (hV : 0 < dvalLE v)
    (hlo : dvalLE w / dvalLE v ≤ g) (hhi : g ≤ dvalLE w / dvalLE v + 1) : StepRes w m v g := by
  have hdm := Nat.mod_add_div (dvalLE w) (dvalLE v)
  have hrv := Nat.mod_lt (dvalLE w) hV
  have hVlt : dvalLE v < 10 ^ v.length := dvalLE_lt hv
  have hsl := subLE_length w m 0 (by omega)
  have hsd := subLE_digits w m 0 hw hm (by decide)
  rcases Nat.lt_or_ge g (dvalLE w / dvalLE v + 1) with hg | hg
  · -- exact guess: no borrow
    have hq : g = dvalLE w / dvalLE v := by omega
    have hle : dvalLE m ≤ dvalLE w := by
      rw [hmv, hq, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    obtain ⟨hb, hs⟩ := subLE_exact w m (by omega) hw hm hle
    have hwin : stepWin w m v = subLE w m 0 := by simp [stepWin, hb]
    refine ⟨by rw [hb]; omega, ?_, by rw [hwin]; exact hsd, by rw [hwin, hsl, hlw]⟩
    rw [hwin, hs, hmv, hq]
    rw [Nat.mul_comm] at hdm ⊢
    omega
  · -- high guess: the subtraction borrows, the add-back corrects
    have hq : g = dvalLE w / dvalLE v + 1 := by omega
    have hgt : dvalLE w < dvalLE m := by
      rw [hmv, hq, Nat.mul_add, Nat.mul_one]
      have := Nat.mul_comm (dvalLE v) (dvalLE w / dvalLE v)
      omega
    have hsv := subLE_val w m 0 (by omega) hm (by decide)
    have hb1 := subBorrow_le w m 0 (by decide)
    have hb : subBorrow w m 0 = 1 := by
      rcases Nat.lt_or_ge (subBorrow w m 0) 1 with h0 | h0
      · have : subBorrow w m 0 = 0 := by omega
        rw [this, Nat.mul_zero] at hsv; omega
      · omega
    have hwin : stepWin w m v = addBack (subLE w m 0) v := by simp [stepWin, hb]
    rw [hb, Nat.mul_one] at hsv
    -- the pieces of the add-back
    generalize hs_def : subLE w m 0 = s at hsv hsl hsd hwin
    have hst := dvalLE_take_last (xs := s) (n := v.length) (by rw [hsl, hlw])
    have htl : (s.take v.length).length = v.length := by simp only [List.length_take]; omega
    have hal := addLE_length (s.take v.length) v 0 (by omega)
    rw [htl] at hal
    have had := addLE_digits (s.take v.length) v 0 (hsd.take v.length) hv (by decide)
      (by simp only [List.length_take]; omega)
    have hav := addLE_val (s.take v.length) v 0 (by simp only [List.length_take]; omega)
    generalize ha_def : addLE (s.take v.length) v 0 = a at hal had hav
    have hat := dvalLE_take_last (xs := a) (n := v.length) hal
    have hatl : (a.take v.length).length = v.length := by simp only [List.length_take]; omega
    have hAlt : dvalLE (a.take v.length) < 10 ^ v.length := by
      have := dvalLE_lt (had.take v.length); rwa [hatl] at this
    have hc : a.getD v.length 0 ≤ 1 := by
      have h1 : dvalLE (s.take v.length) < 10 ^ v.length := by
        have := dvalLE_lt (hsd.take v.length)
        rwa [List.length_take, Nat.min_eq_left (by omega)] at this
      have h2 := dvalLE_lt hv
      have : dvalLE a < 2 * 10 ^ v.length := by omega
      refine Nat.le_of_not_lt fun hc => ?_
      have : 10 ^ v.length * 2 ≤ 10 ^ v.length * a.getD v.length 0 :=
        Nat.mul_le_mul_left _ hc
      omega
    have htop := hsd.getD v.length
    -- the corrected window value
    have hsum : dvalLE (a.take v.length) + 10 ^ v.length * (a.getD v.length 0 + s.getD v.length 0) =
        dvalLE w % dvalLE v + 10 ^ v.length * 10 := by
      have h10 : 10 ^ (v.length + 1) = 10 ^ v.length * 10 := by rw [Nat.pow_succ]
      rw [hlw, h10] at hsv
      rw [hmv, hq, Nat.mul_add, Nat.mul_one] at hsv
      rw [Nat.mul_add]
      have := Nat.mul_comm (dvalLE v) (dvalLE w / dvalLE v)
      omega
    obtain ⟨hA, hk⟩ := split_pow hAlt (by omega) hsum
    refine ⟨by rw [hb, hq, Nat.add_sub_cancel], ?_, ?_, ?_⟩
    · rw [hwin, addBack, ha_def, dvalLE_append, hatl]
      simp only [dvalLE, Nat.mul_zero, Nat.add_zero]
      rw [show (s.getD v.length 0 + a.getD v.length 0) % 10 = 0 by omega, Nat.mul_zero, Nat.add_zero, hA]
    · rw [hwin, addBack, ha_def]
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact had.take v.length d hd
      · rw [List.mem_singleton] at hd; rw [hd]; exact Nat.mod_lt _ (by decide)
    · rw [hwin, addBack, ha_def, List.length_append, hatl, List.length_singleton]

/-- A zero guess: the window is below the divisor and is kept. -/
theorem step_zero {W V : Nat} (hlo : W / V ≤ 0) : W / V = 0 ∧ W % V = W := by
  have h0 : W / V = 0 := Nat.le_zero.mp hlo
  refine ⟨h0, ?_⟩
  have := Nat.mod_add_div W V
  rw [h0, Nat.mul_zero, Nat.add_zero] at this
  exact this

/-- The top digit after the add-back: bumped mod 10 exactly when the carry
fires. -/
theorem addBack_top {s v : List Nat} (hs : IsDigits s) (hv : IsDigits v)
    (hl : s.length = v.length + 1) :
    (addLE (s.take v.length) v 0).getD v.length 0 ≤ 1 ∧
      ((s.getD v.length 0 + (addLE (s.take v.length) v 0).getD v.length 0) % 10 =
        if (addLE (s.take v.length) v 0).getD v.length 0 = 1 then (s.getD v.length 0 + 1) % 10
        else s.getD v.length 0) := by
  have had := addLE_digits (s.take v.length) v 0 (hs.take _) hv (by decide)
    (by simp only [List.length_take]; omega)
  have hal := addLE_length (s.take v.length) v 0 (by simp only [List.length_take]; omega)
  have hav := addLE_val (s.take v.length) v 0 (by simp only [List.length_take]; omega)
  have hat := dvalLE_take_last (xs := addLE (s.take v.length) v 0) (n := v.length)
    (by rw [hal]; simp only [List.length_take]; omega)
  have h1 : dvalLE (s.take v.length) < 10 ^ v.length := by
    have := dvalLE_lt (hs.take v.length)
    rwa [List.length_take, Nat.min_eq_left (by omega)] at this
  have h2 := dvalLE_lt hv
  have hc : (addLE (s.take v.length) v 0).getD v.length 0 ≤ 1 := by
    refine Nat.le_of_not_lt fun hc => ?_
    have : 10 ^ v.length * 2 ≤ 10 ^ v.length * (addLE (s.take v.length) v 0).getD v.length 0 :=
      Nat.mul_le_mul_left _ hc
    omega
  have ht := hs.getD v.length
  refine ⟨hc, ?_⟩
  split
  · rename_i h; rw [h]
  · have : (addLE (s.take v.length) v 0).getD v.length 0 = 0 := by omega
    rw [this, Nat.add_zero, Nat.mod_eq_of_lt ht]

/-! ## Normalisation -/

/-- `norm = 10 / (v1 + 1)` keeps a divisor `v1·E + Vr` below `10 E` and lifts
it to at least `5 E`. -/
theorem norm_bounds {v1 E Vr : Nat} (hv1 : 0 < v1) (hv1' : v1 < 10) (hr : Vr < E) :
    (v1 * E + Vr) * (10 / (v1 + 1)) < 10 * E ∧ 5 * E ≤ (v1 * E + Vr) * (10 / (v1 + 1)) := by
  have : v1 = 1 ∨ v1 = 2 ∨ v1 = 3 ∨ v1 = 4 ∨ v1 = 5 ∨ v1 = 6 ∨ v1 = 7 ∨ v1 = 8 ∨ v1 = 9 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [Nat.reduceAdd, Nat.reduceDiv]; constructor <;> omega)

/-- The normalisation factor is positive and at most 5. -/
theorem norm_pos {v1 : Nat} (hv0 : 0 < v1) (hv1 : v1 < 10) :
    0 < 10 / (v1 + 1) ∧ 10 / (v1 + 1) ≤ 5 := by
  have : v1 = 1 ∨ v1 = 2 ∨ v1 = 3 ∨ v1 = 4 ∨ v1 = 5 ∨ v1 = 6 ∨ v1 = 7 ∨ v1 = 8 ∨ v1 = 9 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The truncated prefix of a normalised dividend divides like the
unnormalised prefix: `⌊n (X T + Y) / T⌋ / (n V) = X / V` for `Y < T`. -/
theorem norm_trunc {n X Y T V : Nat} (hn : 0 < n) (hV : 0 < V) (hY : Y < T) :
    n * (X * T + Y) / T / (n * V) = X / V := by
  have hT : 0 < T := by omega
  have e1 : n * (X * T + Y) / T = n * X + n * Y / T := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hT, Nat.add_comm]
  have he : n * Y / T < n := by
    refine (Nat.div_lt_iff_lt_mul hT).mpr ?_
    exact Nat.mul_lt_mul_of_pos_left hY hn
  rw [e1]
  have hq := Nat.mod_add_div X V
  have hr := Nat.mod_lt X hV
  -- `n X + e = n V q + (n r + e)` with `n r + e < n V`
  have hsplit : n * X + n * Y / T = (n * (X % V) + n * Y / T) + n * V * (X / V) := by
    conv => lhs; rw [← hq]
    rw [Nat.mul_add, Nat.mul_assoc]; omega
  have hlt : n * (X % V) + n * Y / T < n * V := by
    have : n * (X % V) + n ≤ n * V := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
    omega
  rw [hsplit, Nat.add_mul_div_left _ _ (Nat.mul_pos hn hV), Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- `norm_trunc` with `n = 1`. -/
theorem trunc_div {X Y T V : Nat} (hV : 0 < V) (hY : Y < T) : (X * T + Y) / T / V = X / V := by
  have := norm_trunc (n := 1) (X := X) (Y := Y) (T := T) (V := V) (by decide) hV hY
  simpa using this

/-! ## The loop -/

/-- One more dividend digit: the quotient gains the step's digit, the
remainder is the step's remainder. -/
theorem div_snoc {P x V : Nat} (hV : 0 < V) :
    (10 * P + x) / V = 10 * (P / V) + (10 * (P % V) + x) / V ∧
      (10 * P + x) % V = (10 * (P % V) + x) % V := by
  have hq := Nat.mod_add_div P V
  have e : 10 * P + x = (10 * (P % V) + x) + V * (10 * (P / V)) := by
    conv => lhs; rw [← hq]
    rw [Nat.mul_add]; ac_nf
  refine ⟨?_, ?_⟩
  · rw [e, Nat.add_mul_div_left _ _ hV, Nat.add_comm]
  · rw [e, Nat.add_mul_mod_self_left]

end Dc.BcModel
