import Dc.BcModel.Digits

/-!
# The quotient-digit guess of `bc_divide`

One step of `bc_divide`'s long division (Knuth's algorithm D in base 10):
the window `W` (`len2 + 1` digits of the partial remainder, top digits
`w0 w1 w2`) and the normalised divisor `V` (`len2` digits, top digits
`v1 v2`, `v1 ≥ 5`; `v2 = 0` when `len2 = 1`, the sentinel byte), with
`W < 10 * V`. The true digit is `q = W / V ≤ 9`.

`bc_divide` guesses `9` when `w0 = v1`, else `(10 w0 + w1) / v1`, and lowers
the guess at most twice while `v2 * g > (10 w0 + w1 - v1 g) * 10 + w2`.
`guess_spec`: the result is `q` or `q + 1` (the multiply-and-subtract then
borrows exactly in the second case, and the add-back corrects it).

The arithmetic is over naturals: `E = 10^(len2 - 2)` scales the third digit
(`len2 ≥ 2`); `len2 = 1` is `guess_spec_one`.
-/

namespace Dc.BcModel

/-- The first guess. -/
def guess0 (w0 w1 v1 : Nat) : Nat := if w0 = v1 then 9 else (10 * w0 + w1) / v1

/-- The test that lowers a guess. -/
def guessHigh (w0 w1 w2 v1 v2 g : Nat) : Bool := decide ((10 * w0 + w1 - v1 * g) * 10 + w2 < v2 * g)

/-- One test-and-lower. -/
def guessStep (w0 w1 w2 v1 v2 g : Nat) : Nat := if guessHigh w0 w1 w2 v1 v2 g then g - 1 else g

/-- `bc_divide`'s guess: the first guess, lowered by at most two tests (the
second only after the first lowered it). -/
def guess (w0 w1 w2 v1 v2 : Nat) : Nat :=
  let g := guess0 w0 w1 v1
  if guessHigh w0 w1 w2 v1 v2 g then guessStep w0 w1 w2 v1 v2 (g - 1) else g

section
variable {W V E w0 w1 w2 v1 v2 Wr Vr : Nat}

/-- The shape of one step for `len2 ≥ 2`. -/
structure StepShape (W V E w0 w1 w2 v1 v2 Wr Vr : Nat) : Prop where
  ePos : 1 ≤ E
  w : W = (100 * w0 + 10 * w1 + w2) * E + Wr
  wr : Wr < E
  v : V = (10 * v1 + v2) * E + Vr
  vr : Vr < E
  dw1 : w1 < 10
  dw2 : w2 < 10
  dv2 : v2 < 10
  v1lo : 5 ≤ v1
  v1hi : v1 < 10
  lt : W < 10 * V

theorem StepShape.vpos (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) : 0 < V := by
  have := h.v; have := h.v1lo; have := h.ePos
  rw [h.v]
  exact Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) h.ePos) (Nat.le_add_right _ _)

/-- The true digit is at most `9`. -/
theorem StepShape.q_le (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) : W / V ≤ 9 := by
  have hv := h.vpos
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hv).mpr (by have := h.lt; omega))

/-- `w0 ≤ v1`. -/
theorem StepShape.w0_le (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) : w0 ≤ v1 := by
  have h1 := h.lt; rw [h.w, h.v] at h1
  have hE := h.ePos
  have := h.vr; have := h.dv2
  refine Nat.le_of_lt_succ (Nat.lt_of_not_le fun hc => ?_)
  -- `100 w0 E ≤ W < 10 V < 100 (v1 + 1) E`
  have h2 : 100 * (v1 + 1) * E ≤ 100 * w0 * E :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc)
  have h3 : 10 * ((10 * v1 + v2) * E + Vr) < 100 * (v1 + 1) * E := by
    rw [Nat.mul_add, ← Nat.mul_assoc, show 100 * (v1 + 1) * E = (10 * (10 * v1 + v2)) * E + (10 * (10 - v2)) * E by
      rw [← Nat.add_mul]; congr 1; omega]
    have : 10 * Vr < 10 * (10 - v2) * E := by
      have : 1 ≤ 10 - v2 := by omega
      calc 10 * Vr < 10 * E := by omega
        _ ≤ 10 * ((10 - v2) * E) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
        _ = _ := by rw [Nat.mul_assoc]
    omega
  have h4 : 100 * w0 * E ≤ (100 * w0 + 10 * w1 + w2) * E + Wr := by
    rw [Nat.add_mul, Nat.add_mul]; omega
  omega

/-- The top two digits `T = 10 w0 + w1` bound `W` from both sides. -/
theorem StepShape.top (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) :
    (10 * w0 + w1) * (10 * E) ≤ W ∧ W < (10 * w0 + w1 + 1) * (10 * E) := by
  rw [h.w]
  have := h.wr; have := h.dw2
  constructor
  · rw [show (10 * w0 + w1) * (10 * E) = (100 * w0 + 10 * w1) * E by
      rw [← Nat.mul_assoc, Nat.add_mul]; congr 1; omega]
    rw [Nat.add_mul (100 * w0 + 10 * w1)]; omega
  · rw [show (10 * w0 + w1 + 1) * (10 * E) = (100 * w0 + 10 * w1 + w2) * E + (10 - w2) * E by
      rw [← Nat.add_mul, ← Nat.mul_assoc]; congr 1; omega]
    have : E ≤ (10 - w2) * E := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- `V` lies between `v1 * 10 E` and `(v1 + 1) * 10 E`. -/
theorem StepShape.vbounds (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) :
    v1 * (10 * E) ≤ V ∧ V < (v1 + 1) * (10 * E) := by
  rw [h.v]
  have := h.vr; have := h.dv2
  constructor
  · rw [← Nat.mul_assoc, Nat.mul_comm v1 10, Nat.add_mul]; omega
  · rw [show (v1 + 1) * (10 * E) = (10 * v1 + v2) * E + (10 - v2) * E by
      rw [← Nat.add_mul, ← Nat.mul_assoc]; congr 1; omega]
    have : E ≤ (10 - v2) * E := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The remainder estimate of a guess is never negative. -/
theorem StepShape.guess0_le (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) :
    v1 * guess0 w0 w1 v1 ≤ 10 * w0 + w1 := by
  unfold guess0
  split
  · subst w0; omega
  · exact Nat.mul_div_le _ _

/-- **The first guess is not low** (`q ≤ guess0`). -/
theorem StepShape.q_le_guess0 (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) :
    W / V ≤ guess0 w0 w1 v1 := by
  unfold guess0
  split
  · exact h.q_le
  · have hv := h.vpos
    have ⟨_, ht⟩ := h.top
    have ⟨hvl, _⟩ := h.vbounds
    have hv1 : 0 < v1 := by have := h.v1lo; omega
    refine (Nat.le_div_iff_mul_le hv1).mpr ?_
    -- `q v1 (10E) ≤ q V ≤ W < (T + 1)(10E)`
    have h1 : W / V * V ≤ W := Nat.div_mul_le_self _ _
    have h2 : W / V * (v1 * (10 * E)) ≤ W / V * V := Nat.mul_le_mul_left _ hvl
    have h3 : W / V * v1 * (10 * E) < (10 * w0 + w1 + 1) * (10 * E) := by
      rw [Nat.mul_assoc]; omega
    have := Nat.lt_of_mul_lt_mul_right h3
    omega

/-- **The test lowers only a high guess**: if it fires, `g > q`. -/
theorem StepShape.test_sound (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) {g : Nat}
    (hg : v1 * g ≤ 10 * w0 + w1) (ht : guessHigh w0 w1 w2 v1 v2 g = true) : W / V < g := by
  simp only [guessHigh, decide_eq_true_eq] at ht
  have hv := h.vpos
  refine (Nat.div_lt_iff_lt_mul hv).mpr ?_
  -- `g V ≥ (10 v1 g + v2 g) E ≥ (10 T + w2 + 1) E > W`
  have h1 : (10 * v1 + v2) * E * g ≤ V * g := Nat.mul_le_mul_right _ (by rw [h.v]; omega)
  have h2 : (10 * (10 * w0 + w1) + w2 + 1) ≤ (10 * v1 + v2) * g := by
    have e : (10 * v1 + v2) * g = 10 * (v1 * g) + v2 * g := by rw [Nat.add_mul, Nat.mul_assoc]
    have : (10 * w0 + w1 - v1 * g) * 10 = 10 * (10 * w0 + w1) - 10 * (v1 * g) := by
      rw [Nat.mul_comm, Nat.mul_sub]
    omega
  have h3 : W < (10 * (10 * w0 + w1) + w2 + 1) * E := by
    have e : (10 * (10 * w0 + w1) + w2 + 1) * E = (100 * w0 + 10 * w1 + w2) * E + E := by
      rw [Nat.succ_mul]; congr 2; omega
    rw [e, h.w]; have := h.wr; omega
  have h4 : (10 * (10 * w0 + w1) + w2 + 1) * E ≤ (10 * v1 + v2) * g * E := Nat.mul_le_mul_right _ h2
  calc W < _ := h3
    _ ≤ (10 * v1 + v2) * g * E := h4
    _ = (10 * v1 + v2) * E * g := by rw [Nat.mul_right_comm]
    _ ≤ V * g := h1
    _ = g * V := Nat.mul_comm _ _

/-- **A guess that passes the test is at most one high**. -/
theorem StepShape.test_complete (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) {g : Nat}
    (hg9 : g ≤ 9) (hg : v1 * g ≤ 10 * w0 + w1) (ht : guessHigh w0 w1 w2 v1 v2 g = false) :
    g ≤ W / V + 1 := by
  simp only [guessHigh, decide_eq_false_iff_not, Nat.not_lt] at ht
  have hv := h.vpos
  -- `g (10 v1 + v2) ≤ 10 T + w2`
  have h2 : (10 * v1 + v2) * g ≤ 10 * (10 * w0 + w1) + w2 := by
    have e : (10 * v1 + v2) * g = 10 * (v1 * g) + v2 * g := by rw [Nat.add_mul, Nat.mul_assoc]
    have : (10 * w0 + w1 - v1 * g) * 10 = 10 * (10 * w0 + w1) - 10 * (v1 * g) := by
      rw [Nat.mul_comm, Nat.mul_sub]
    omega
  -- `g V < g (10 v1 + v2 + 1) E ≤ (10 T + w2) E + g E ≤ W + 9 E < W + V`
  have hV : V < (10 * v1 + v2 + 1) * E := by rw [h.v, Nat.add_mul (10 * v1 + v2)]; have := h.vr; omega
  have hW : (10 * (10 * w0 + w1) + w2) * E ≤ W := by
    rw [h.w, show 10 * (10 * w0 + w1) + w2 = 100 * w0 + 10 * w1 + w2 by omega]; omega
  have h5 : g * V ≤ g * ((10 * v1 + v2 + 1) * E) := Nat.mul_le_mul_left _ (Nat.le_of_lt hV)
  have h6 : g * ((10 * v1 + v2 + 1) * E) = (10 * v1 + v2) * g * E + g * E := by
    rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_left_comm, ← Nat.mul_assoc, Nat.mul_comm g]
  have h7 : (10 * v1 + v2) * g * E ≤ (10 * (10 * w0 + w1) + w2) * E := Nat.mul_le_mul_right _ h2
  have h8 : g * E ≤ 9 * E := Nat.mul_le_mul_right _ hg9
  have h9 : 10 * E ≤ V := by
    have ⟨hvl, _⟩ := h.vbounds
    have : 1 * (10 * E) ≤ v1 * (10 * E) := Nat.mul_le_mul_right _ (by have := h.v1lo; omega)
    omega
  have h10 : g * V < W + V := by omega
  -- so `(g - 1) V ≤ W`
  refine Nat.le_of_lt_succ (Nat.lt_of_not_le fun hc => ?_)
  have : (W / V + 2) * V ≤ g * V := Nat.mul_le_mul_right _ hc
  have h11 : W < (W / V + 1) * V := Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) hv
  rw [Nat.add_mul] at this h11
  omega

/-- **Knuth's Theorem B**: with `v1 ≥ 5` the first guess is at most two high. -/
theorem StepShape.guess0_le_q2 (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) :
    guess0 w0 w1 v1 ≤ W / V + 2 := by
  have hq := h.q_le
  have hg := h.guess0_le
  have hg9 : guess0 w0 w1 v1 ≤ 9 := by
    unfold guess0; split
    · exact Nat.le_refl _
    · have := h.w0_le
      have : w0 < v1 := by omega
      have hv1 : 0 < v1 := by omega
      refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hv1).mpr ?_)
      have := h.dw1; omega
  refine Nat.le_of_not_lt fun hc => ?_
  -- `(q + 3) v1 (10E) ≤ g v1 (10E) ≤ T (10E) ≤ W < (q + 1) V < (q + 1)(v1 + 1)(10E)`
  have hv := h.vpos
  have ⟨ht, _⟩ := h.top
  have ⟨_, hvu⟩ := h.vbounds
  have h1 : W < (W / V + 1) * V := Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) hv
  have h2 : (W / V + 1) * V ≤ (W / V + 1) * ((v1 + 1) * (10 * E)) :=
    Nat.mul_le_mul_left _ (Nat.le_of_lt hvu)
  have h3 : (W / V + 3) * v1 ≤ 10 * w0 + w1 :=
    Nat.le_trans (Nat.mul_le_mul_right _ hc) (by rw [Nat.mul_comm]; exact hg)
  have h4 : (W / V + 3) * v1 * (10 * E) ≤ (10 * w0 + w1) * (10 * E) := Nat.mul_le_mul_right _ h3
  have h5 : (W / V + 3) * v1 < (W / V + 1) * (v1 + 1) := by
    have : (W / V + 3) * v1 * (10 * E) < (W / V + 1) * (v1 + 1) * (10 * E) := by
      rw [Nat.mul_assoc (W / V + 1)]; omega
    exact Nat.lt_of_mul_lt_mul_right this
  -- `(q + 3) v1 < (q + 1)(v1 + 1)` gives `2 v1 < q + 1 ≤ 10`
  have e1 : (W / V + 3) * v1 = W / V * v1 + 3 * v1 := Nat.add_mul _ _ _
  have e2 : (W / V + 1) * (v1 + 1) = W / V * v1 + W / V + v1 + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_one]; omega
  have := h.v1lo
  omega

/-- **`bc_divide`'s guess is `q` or `q + 1`.** -/
theorem StepShape.guess_spec (h : StepShape W V E w0 w1 w2 v1 v2 Wr Vr) :
    W / V ≤ guess w0 w1 w2 v1 v2 ∧ guess w0 w1 w2 v1 v2 ≤ W / V + 1 := by
  have hq0 := h.q_le_guess0
  have hq2 := h.guess0_le_q2
  have hg := h.guess0_le
  have hg9 : guess0 w0 w1 v1 ≤ 9 := by
    have := h.q_le; unfold guess0; split
    · exact Nat.le_refl _
    · have := h.w0_le
      have : w0 < v1 := by omega
      have hv1 : 0 < v1 := by have := h.v1lo; omega
      refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hv1).mpr ?_)
      have := h.dw1; omega
  unfold guess
  simp only
  cases ht1 : guessHigh w0 w1 w2 v1 v2 (guess0 w0 w1 v1)
  · exact ⟨hq0, h.test_complete hg9 hg ht1⟩
  · have hlt := h.test_sound hg ht1
    have hg' : v1 * (guess0 w0 w1 v1 - 1) ≤ 10 * w0 + w1 :=
      Nat.le_trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hg
    simp only [ite_true, guessStep]
    cases ht2 : guessHigh w0 w1 w2 v1 v2 (guess0 w0 w1 v1 - 1)
    · simp only [Bool.false_eq_true, ite_false]
      exact ⟨by omega, h.test_complete (Nat.le_trans (Nat.sub_le _ _) hg9) hg' ht2⟩
    · have := h.test_sound hg' ht2
      simp only [ite_true]
      generalize W / V = q at *
      generalize guess0 w0 w1 v1 = g at *
      constructor <;> omega

end

/-- **A one-digit divisor** (`len2 = 1`, `v2 = 0`): the guess is exact. -/
theorem guess_spec_one {w0 w1 w2 v1 : Nat} (hv1 : 0 < v1) (hw1 : w1 < 10)
    (hlt : 10 * w0 + w1 < 10 * v1) :
    guess w0 w1 w2 v1 0 = (10 * w0 + w1) / v1 := by
  have hne : w0 ≠ v1 := by omega
  have hf : guessHigh w0 w1 w2 v1 0 ((10 * w0 + w1) / v1) = false := by
    simp [guessHigh]
  simp only [guess, guess0, hne, ite_false, hf]
  rfl

/-! ## Long division -/

/-- Schoolbook long division of the digits `xs` (big-endian) by `D` from the
remainder `R`: the quotient digits and the final remainder. -/
def longDiv (D : Nat) : Nat → List Nat → List Nat × Nat
  | R, [] => ([], R)
  | R, x :: xs =>
    let r := longDiv D ((10 * R + x) % D) xs
    ((10 * R + x) / D :: r.1, r.2)

theorem longDiv_val (D : Nat) : ∀ (R : Nat) (xs : List Nat),
    dvalBE (longDiv D R xs).1 * D + (longDiv D R xs).2 = R * 10 ^ xs.length + dvalBE xs
  | R, [] => by simp [longDiv, dvalBE]
  | R, x :: xs => by
    simp only [longDiv, dvalBE_cons, List.length_cons]
    have ih := longDiv_val D ((10 * R + x) % D) xs
    have hlen : (longDiv D ((10 * R + x) % D) xs).1.length = xs.length := by
      clear ih; induction xs generalizing R x with
      | nil => rfl
      | cons y ys ih' => simp only [longDiv, List.length_cons]; rw [ih']
    rw [hlen, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (10 ^ xs.length) D, ← Nat.mul_assoc,
      Nat.add_assoc, ih, ← Nat.add_assoc, ← Nat.add_mul, Nat.mul_comm ((10 * R + x) / D) D,
      Nat.div_add_mod, Nat.pow_succ, Nat.add_mul, Nat.mul_comm 10, Nat.mul_assoc, Nat.add_assoc,
      Nat.add_comm (x * _), ← Nat.add_assoc]
    rw [Nat.mul_comm 10 (10 ^ xs.length)]; omega

theorem longDiv_rem (D : Nat) (hD : 0 < D) : ∀ (R : Nat) (xs : List Nat), R < D →
    (longDiv D R xs).2 < D
  | R, [], h => h
  | R, x :: xs, _ => longDiv_rem D hD _ xs (Nat.mod_lt _ hD)

theorem longDiv_digits (D : Nat) (hD : 0 < D) : ∀ (R : Nat) (xs : List Nat), R < D → IsDigits xs →
    IsDigits (longDiv D R xs).1
  | R, [], _, _ => by intro d hd; simp [longDiv] at hd
  | R, x :: xs, hR, hx => by
    intro d hd
    simp only [longDiv, List.mem_cons] at hd
    rcases hd with rfl | hd
    · have := hx x List.mem_cons_self
      refine (Nat.div_lt_iff_lt_mul hD).mpr ?_
      have : 10 * R + x < 10 * (R + 1) := by omega
      have : 10 * (R + 1) ≤ 10 * D := Nat.mul_le_mul_left _ hR
      rw [Nat.mul_comm]; omega
    · exact longDiv_digits D hD _ xs (Nat.mod_lt _ hD) (fun e he => hx e (List.mem_cons_of_mem _ he)) d hd

/-- From a zero remainder, the quotient of `xs` is its value divided by `D`. -/
theorem longDiv_quot (D : Nat) (hD : 0 < D) (xs : List Nat) :
    dvalBE (longDiv D 0 xs).1 = dvalBE xs / D := by
  have hv := longDiv_val D 0 xs
  have hr := longDiv_rem D hD 0 xs hD
  rw [Nat.zero_mul, Nat.zero_add] at hv
  rw [← hv, Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hr, Nat.zero_add]

end Dc.BcModel
