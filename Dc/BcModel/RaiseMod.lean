import Dc.BcModel.Raise

/-!
# The loop of `bc_raisemod`

`bc_modulo` leaves a remainder at scale `max a.scale (b.scale + k)` whose
magnitude is below the divisor's at that scale (`ModRes`), which bounds every
number the loop builds. The exponent is an integer (`scale = 0`) throughout;
`bc_divmod (exponent, _two_, …, 0)` halves it and leaves its parity
(`halve`), and the fuel `raisemod` gives the loop is enough at every step
(`raisemodLoop_step`).
-/

namespace Dc.BcModel

open Dc

/-- What `bc_modulo a b k` leaves: the full remainder scale, and a magnitude
below the divisor's at that scale. -/
structure ModRes (a b : Num) (k : Nat) (r : Num) : Prop where
  scale : r.scale = max a.scale (b.scale + k)
  mag : r.mag < b.mag * 10 ^ (max a.scale (b.scale + k) - b.scale - k)

/-- The remainder magnitude of a truncated division:
`A·10^e1 - Q·B·10^e2 < B·10^e2` with `Q = A·10^{sb+k} / (B·10^sa)`. -/
theorem rem_bounds (A B sa sb k e1 e2 : Nat) (he : sa + e1 = sb + k + e2) (hB : 0 < B) :
    A * 10 ^ (sb + k) / (B * 10 ^ sa) * B * 10 ^ e2 ≤ A * 10 ^ e1 ∧
      A * 10 ^ e1 < A * 10 ^ (sb + k) / (B * 10 ^ sa) * B * 10 ^ e2 + B * 10 ^ e2 := by
  have hD : 0 < B * 10 ^ sa := Nat.mul_pos hB (Nat.pow_pos (by decide))
  have hP : 0 < 10 ^ (sb + k) := Nat.pow_pos (by decide)
  generalize hQ : A * 10 ^ (sb + k) / (B * 10 ^ sa) = Q
  have h1 : Q * (B * 10 ^ sa) ≤ A * 10 ^ (sb + k) := hQ ▸ Nat.div_mul_le_self _ _
  have h2 : A * 10 ^ (sb + k) < (Q + 1) * (B * 10 ^ sa) := by
    rw [← hQ, Nat.add_mul, Nat.one_mul]
    have := Nat.div_add_mod (A * 10 ^ (sb + k)) (B * 10 ^ sa)
    have := Nat.mod_lt (A * 10 ^ (sb + k)) hD
    rw [Nat.mul_comm (A * 10 ^ (sb + k) / (B * 10 ^ sa))]
    omega
  -- scale both sides by `10^e1`, then cancel `10^(sb+k)`
  have key : ∀ X : Nat, X * (B * 10 ^ sa) * 10 ^ e1 = X * B * 10 ^ e2 * 10 ^ (sb + k) := by
    intro X
    simp only [Nat.mul_assoc, ← Nat.pow_add]
    rw [show e2 + (sb + k) = sa + e1 by omega]
  have hA : A * 10 ^ (sb + k) * 10 ^ e1 = A * 10 ^ e1 * 10 ^ (sb + k) := by
    rw [Nat.mul_assoc, Nat.mul_comm (10 ^ (sb + k)), ← Nat.mul_assoc]
  constructor
  · have := Nat.mul_le_mul_right (10 ^ e1) h1
    rw [key, hA] at this
    exact Nat.le_of_mul_le_mul_right this hP
  · have := Nat.mul_lt_mul_of_pos_right h2 (Nat.pow_pos (n := e1) (by decide : 0 < 10))
    rw [key, hA] at this
    have := Nat.lt_of_mul_lt_mul_right this
    rwa [Nat.add_mul, Nat.add_mul, Nat.one_mul] at this

/-- `bc_sub`'s scale. -/
theorem sub_scale (a p : Num) (s : Nat) :
    (Num.sub a p s).scale = max s (max a.scale p.scale) := by
  unfold Num.sub; dsimp only; split
  · rfl
  · cases compare (a.align (max s (max a.scale p.scale)))
      (p.align (max s (max a.scale p.scale))) <;> rfl

/-- `bc_sub` of a smaller magnitude of the same sign (or of zero). -/
theorem sub_mag_of_le (a p : Num) (s : Nat)
    (hle : p.align (max s (max a.scale p.scale)) ≤ a.align (max s (max a.scale p.scale)))
    (hz : a.neg ≠ p.neg → p.mag = 0) :
    (Num.sub a p s).mag =
      a.align (max s (max a.scale p.scale)) - p.align (max s (max a.scale p.scale)) := by
  unfold Num.sub; dsimp only; split
  · rename_i h
    have h0 : p.mag = 0 := hz (by simpa using h)
    simp only [Num.align, h0, Nat.zero_mul] at hle ⊢
    omega
  · cases hc : compare (a.align (max s (max a.scale p.scale)))
      (p.align (max s (max a.scale p.scale)))
    · have := Nat.compare_eq_lt.mp hc; omega
    · have := Nat.compare_eq_eq.mp hc; simp only [Num.zero]; omega
    · rfl

/-- `bc_modulo a b k` by a nonzero divisor. -/
theorem modulo_res {a b : Num} {k : Nat} (hb : b.mag ≠ 0) :
    ∃ r, Num.modulo a b k = some r ∧ ModRes a b k r := by
  obtain ⟨hle, hlt⟩ := rem_bounds a.mag b.mag a.scale b.scale k
    (max a.scale (b.scale + k) - a.scale) (max a.scale (b.scale + k) - (b.scale + k))
    (by omega) (Nat.pos_of_ne_zero hb)
  unfold Num.modulo Num.divmod Num.div
  rw [if_neg (by simpa using hb)]
  simp only [Option.map_some]
  rw [mul_exact _ _ _ (by show k + b.scale ≤ _; omega)]
  refine ⟨_, rfl, ?_⟩
  have hS : max (max a.scale (b.scale + k)) (max a.scale (k + b.scale)) =
      max a.scale (b.scale + k) := by omega
  constructor
  · rw [sub_scale]; exact hS
  · rw [sub_mag_of_le]
    · simp only [Num.align, Nat.add_comm k b.scale, Nat.max_self] at hle hlt ⊢
      rw [Nat.sub_sub]
      omega
    · simp only [Num.align, Nat.add_comm k b.scale, Nat.max_self]; exact hle
    · intro h
      dsimp only at h ⊢
      by_cases h0 : a.mag * 10 ^ (b.scale + k) / (b.mag * 10 ^ a.scale) * b.mag = 0
      · exact h0
      exfalso
      have hq : a.mag * 10 ^ (b.scale + k) / (b.mag * 10 ^ a.scale) ≠ 0 :=
        fun hq => h0 (by rw [hq, Nat.zero_mul])
      apply h
      simp only [beq_iff_eq, h0, hq, ite_false]
      cases a.neg <;> cases b.neg <;> rfl

/-- `bc_divmod (exponent, _two_, …, 0)` of a non-negative integer: its half
and its parity. -/
theorem divmod_two (m : Nat) :
    Num.divmod ⟨false, m, 0⟩ ⟨false, 2, 0⟩ 0 = some (⟨false, m / 2, 0⟩, ⟨false, m % 2, 0⟩) := by
  have hd : Num.div ⟨false, m, 0⟩ ⟨false, 2, 0⟩ 0 = some ⟨false, m / 2, 0⟩ := by
    simp only [Num.div, Nat.add_zero, Nat.pow_zero, Nat.mul_one]
    rw [if_neg (by decide)]
    split <;> rfl
  have hm : Num.mul ⟨false, m / 2, 0⟩ ⟨false, 2, 0⟩ 0 = ⟨false, m / 2 * 2, 0⟩ := by
    rw [mul_exact _ _ _ (Nat.le_refl 0)]
    split <;> rfl
  unfold Num.divmod
  rw [hd]
  dsimp only
  rw [show max 0 (0 + 0) = 0 from rfl, hm]
  congr 2
  unfold Num.sub
  simp only [Num.align, Nat.pow_zero, Nat.mul_one, Nat.max_self, Nat.sub_self]
  have := Nat.div_add_mod m 2
  have := Nat.mod_lt m (show 0 < 2 by decide)
  cases hc : compare m (m / 2 * 2)
  · have := Nat.compare_eq_lt.mp hc; omega
  · have := Nat.compare_eq_eq.mp hc; simp only [Num.zero]
    rw [if_neg (by decide)]; congr 1; omega
  · rw [if_neg (by decide)]; show Num.mk _ _ _ = _; congr 1; omega

/-- The loop does not depend on its fuel once the fuel exceeds the
(integer, non-negative) exponent. -/
theorem raisemodLoop_fuel (md : Num) (k rs : Nat) :
    ∀ (f g m : Nat) (p t : Num), m < f → m < g →
      Num.raisemodLoop md k rs f ⟨false, m, 0⟩ p t = Num.raisemodLoop md k rs g ⟨false, m, 0⟩ p t
  | 0, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, g + 1, m, p, t, hf, hg => by
    unfold Num.raisemodLoop
    simp only [divmod_two, Option.getD_some]
    split
    · rfl
    · rename_i h0
      have : m ≠ 0 := by simpa [Num.isZero] using h0
      exact raisemodLoop_fuel md k rs f g (m / 2) _ _ (by omega) (by omega)

/-- One iteration of the loop: halve the exponent; multiply `temp` by
`power` modulo `md` on an odd exponent; square `power` modulo `md`. -/
theorem raisemodLoop_step (md : Num) (k rs m : Nat) (p t : Num) (hm : m ≠ 0) :
    Num.raisemodLoop md k rs (m + 1) ⟨false, m, 0⟩ p t =
      Num.raisemodLoop md k rs (m / 2 + 1) ⟨false, m / 2, 0⟩
        ((Num.modulo (Num.mul p p rs) md k).getD p)
        (if m % 2 = 0 then t else (Num.modulo (Num.mul t p rs) md k).getD t) := by
  conv => lhs; unfold Num.raisemodLoop
  simp only [divmod_two, Option.getD_some, Num.isZero, beq_iff_eq, hm, ite_false]
  refine raisemodLoop_fuel md k rs m (m / 2 + 1) (m / 2) _ _ (by omega) (by omega) |>.trans ?_
  rfl

/-- The loop at a zero exponent. -/
theorem raisemodLoop_zero (md : Num) (k rs f : Nat) (p t : Num) :
    Num.raisemodLoop md k rs (f + 1) ⟨false, 0, 0⟩ p t = t := by
  unfold Num.raisemodLoop; rfl

/-- `expo / 1` at scale 0 of a non-negative `expo`: its integer part. -/
theorem div_one_int (e : Num) (hn : e.neg = false) :
    Num.div e Num.one 0 = some ⟨false, e.intPart, 0⟩ := by
  rcases e with ⟨en, em, es⟩
  cases hn
  simp only [Num.div, Num.one, Num.intPart, Nat.add_zero, Nat.pow_zero, Nat.mul_one, Nat.one_mul]
  rw [if_neg (by decide)]
  split <;> rfl

/-- **`bc_raisemod` on a nonzero modulus and a non-negative exponent**: the
loop on the exponent's integer part. -/
theorem raisemod_eq (b e md : Num) (k : Nat) (hm : md.mag ≠ 0) (hn : e.neg = false) :
    Num.raisemod b e md k = some (Num.raisemodLoop md k (max k b.scale) (e.intPart + 1)
      ⟨false, e.intPart, 0⟩ b Num.one) := by
  have hz : md.isZero = false := by simpa [Num.isZero] using hm
  unfold Num.raisemod
  simp only [hz, hn, Bool.false_eq_true, ↓reduceIte]
  by_cases hs : e.scale = 0
  · have he : e = ⟨false, e.intPart, 0⟩ := by
      rcases e with ⟨en, em, es⟩
      simp only at hn hs
      subst hn hs
      simp [Num.intPart]
    simp only [hs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    conv => lhs; rw [he]
    simp [Num.intPart]
  · simp only [hs, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, div_one_int e hn,
      Option.getD_some]
    simp [Num.intPart]

end Dc.BcModel
