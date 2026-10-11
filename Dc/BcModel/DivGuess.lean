import Dc.BcModel.DivStep

/-!
# The guess on a window's digits

`guess_window`: with the window `W < 10 V` (`L + 1` digits) and the
normalised divisor `V` (`L` digits, top digit at least 5), `bc_divide`'s
guess from the top digits is `W / V` or `W / V + 1`, and at most 9. For
`L = 1` the third window digit `b` is whatever byte follows the window and
the divisor's second digit is the sentinel `0`.
-/

namespace Dc.BcModel

/-- Splitting off the top two and the next digit at scale `E`. -/
theorem split3 (X E : Nat) (hE : 0 < E) :
    X = (100 * (X / (100 * E)) + 10 * (X / (10 * E) % 10) + X / E % 10) * E + X % E := by
  have h1 := Nat.mod_add_div X E
  have h2 := Nat.mod_add_div (X / E) 10
  have h3 := Nat.mod_add_div (X / E / 10) 10
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul] at h3
  rw [Nat.div_div_eq_div_mul] at h2
  rw [show 100 * E = E * 10 * 10 by omega, show 10 * E = E * 10 by omega]
  -- `X / E = 100 a + 10 b + c`
  have e : X / E = 100 * (X / (E * 10 * 10)) + 10 * (X / (E * 10) % 10) + X / E % 10 := by omega
  conv => lhs; rw [← h1]
  rw [← e, Nat.mul_comm (X / E) E]; omega

/-- Splitting off the top digit at scale `E`. -/
theorem split2 (X E : Nat) (hE : 0 < E) : X = (10 * (X / (10 * E)) + X / E % 10) * E + X % E := by
  have h1 := Nat.mod_add_div X E
  have h2 := Nat.mod_add_div (X / E) 10
  rw [Nat.div_div_eq_div_mul] at h2
  rw [show 10 * E = E * 10 by omega]
  have e : X / E = 10 * (X / (E * 10)) + X / E % 10 := by omega
  conv => lhs; rw [← h1]
  rw [← e, Nat.mul_comm (X / E) E]; omega

theorem guess_le_guess0 (w0 w1 w2 v1 v2 : Nat) : guess w0 w1 w2 v1 v2 ≤ guess0 w0 w1 v1 := by
  unfold guess guessStep
  simp only
  split
  · split <;> omega
  · exact Nat.le_refl _

theorem guess0_le9 {w0 w1 v1 : Nat} (h : w0 ≤ v1) (hw1 : w1 < 10) (hv : 0 < v1) :
    guess0 w0 w1 v1 ≤ 9 := by
  unfold guess0
  split
  · exact Nat.le_refl _
  · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hv).mpr (by
      have : w0 + 1 ≤ v1 := by omega
      have := Nat.mul_le_mul_left 10 this
      rw [Nat.mul_add] at this; omega))

/-- **The guess on a window.** -/
theorem guess_window {L V W b : Nat} (hL : 1 ≤ L) (hV1 : 5 * 10 ^ (L - 1) ≤ V)
    (hV2 : V < 10 ^ L) (hW : W < 10 * V) :
    W / V ≤ guess (W / 10 ^ L) (W / 10 ^ (L - 1) % 10) (if 2 ≤ L then W / 10 ^ (L - 2) % 10 else b)
        (V / 10 ^ (L - 1)) (if 2 ≤ L then V / 10 ^ (L - 2) % 10 else 0) ∧
      guess (W / 10 ^ L) (W / 10 ^ (L - 1) % 10) (if 2 ≤ L then W / 10 ^ (L - 2) % 10 else b)
        (V / 10 ^ (L - 1)) (if 2 ≤ L then V / 10 ^ (L - 2) % 10 else 0) ≤ W / V + 1 ∧
      guess (W / 10 ^ L) (W / 10 ^ (L - 1) % 10) (if 2 ≤ L then W / 10 ^ (L - 2) % 10 else b)
        (V / 10 ^ (L - 1)) (if 2 ≤ L then V / 10 ^ (L - 2) % 10 else 0) ≤ 9 := by
  have hVp : 0 < V := Nat.lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) hV1
  have hq : W / V < 10 := (Nat.div_lt_iff_lt_mul hVp).mpr (by omega)
  by_cases h2 : 2 ≤ L
  · simp only [h2, ite_true]
    obtain ⟨E, hE⟩ : ∃ E, E = 10 ^ (L - 2) := ⟨_, rfl⟩
    have hEp : 0 < E := hE ▸ Nat.pow_pos (by decide)
    have e1 : 10 ^ (L - 1) = 10 * E := by
      rw [hE, ← Nat.pow_succ']; congr 1; omega
    have e0 : 10 ^ L = 100 * E := by
      rw [hE, show 100 = 10 ^ 2 from rfl, ← Nat.pow_add, show 2 + (L - 2) = L by omega]
    rw [e0, e1, ← hE]
    rw [e1] at hV1
    rw [e0] at hV2
    have hv1lo : 5 ≤ V / (10 * E) := (Nat.le_div_iff_mul_le (by omega)).mpr hV1
    have hv1hi : V / (10 * E) < 10 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    have hs : StepShape W V E (W / (100 * E)) (W / (10 * E) % 10) (W / E % 10) (V / (10 * E))
        (V / E % 10) (W % E) (V % E) :=
      ⟨hEp, split3 W E hEp, Nat.mod_lt _ hEp, split2 V E hEp, Nat.mod_lt _ hEp,
        Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), hv1lo,
        hv1hi, hW⟩
    obtain ⟨g1, g2⟩ := hs.guess_spec
    refine ⟨g1, g2, Nat.le_trans (guess_le_guess0 _ _ _ _ _) (guess0_le9 hs.w0_le
      (Nat.mod_lt _ (by decide)) (by omega))⟩
  · simp only [h2, ite_false]
    have hL1 : L = 1 := by omega
    subst hL1
    simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.pow_one] at hV1 hV2 ⊢
    rw [guess_spec_one hVp (Nat.mod_lt _ (by decide)) (by omega),
      show 10 * (W / 10) + W % 10 = W by omega]
    exact ⟨Nat.le_refl _, by omega, by omega⟩

/-- `(10 Q + d) / 10^(e+1) = Q / 10^e` for a digit `d`. -/
theorem div_shift (Q d e : Nat) (hd : d < 10) : (10 * Q + d) / 10 ^ (e + 1) = Q / 10 ^ e := by
  rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
  congr 1; omega

/-- The digits of a window `10 R + x`: its top `L` digits are `R`'s. -/
theorem win_digit {R x L j : Nat} (hx : x < 10) (hj : j < L) :
    (10 * R + x) / 10 ^ (L - j) % 10 = R / 10 ^ (L - 1 - j) % 10 := by
  rw [show L - j = L - 1 - j + 1 by omega, div_shift _ _ _ hx]

theorem win_last {R x : Nat} (hx : x < 10) : (10 * R + x) / 10 ^ 0 % 10 = x := by
  rw [Nat.pow_zero, Nat.div_one]; omega

/-- The top digit of a value below `10^L` needs no `% 10`. -/
theorem top_digit {X L : Nat} (hX : X < 10 ^ L) (hL : 1 ≤ L) : X / 10 ^ (L - 1) % 10 = X / 10 ^ (L - 1) := by
  apply Nat.mod_eq_of_lt
  refine (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr ?_
  rw [← Nat.pow_succ']; rwa [show (L - 1).succ = L by omega]

end Dc.BcModel
