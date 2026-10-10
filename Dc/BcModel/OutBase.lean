import Dc.BcModel.Out
import Dc.BcModel.SqrtInit

/-!
# Output in a base other than 10 (`bc_out_num`)

The machine computes `int_part = num / 1` at scale `0` and `frac_part =
num - int_part` (both made positive). It then pushes the digits of
`int_part` with `bc_modulo`/`bc_divide` by `base` at scale `0`. The fraction
digits come from `frac_part * base` at `num`'s scale, `bc_num2long`, and the
subtraction of that digit, while `t = base ^ i` has at most `scale` decimal
digits. Each lemma here equates one such call with the arithmetic of
`Num.outChars`.

- `div_one_zero`, `divInt`, `divmodInt`, `toLong_int`: the integer part and
  one step of the integer-digit loop.
- `FracInv`, `fracStep_*`: one step of the fraction loop.
- `FracFuel`, `fracDigits_unfold`, `fracDigits_stop`: the fuel of
  `Num.fracDigits` against the loop's exit test.
- `intLen_dec`: `n_len` of a positive integer is the length of its decimal
  text.
-/

namespace Dc.BcModel

open Dc

/-- `bc_divide (n, _one_, &int_part, 0)`: the integer part at scale `0`. -/
theorem div_one_zero (n : Num) :
    ∃ m, Num.div n Num.one 0 = some m ∧ m.mag = n.intPart ∧ m.scale = 0 :=
  ⟨_, by simp only [Num.div, Num.one, Nat.one_ne_zero, beq_iff_eq, if_false]; rfl,
    by simp only [Num.intPart, Num.one, Nat.zero_add, Nat.pow_zero, Nat.mul_one, Nat.one_mul], rfl⟩

/-- `bc_divide (c, base, &c, 0)` on non-negative integers. -/
theorem divInt (c b : Nat) (hb : b ≠ 0) :
    Num.div ⟨false, c, 0⟩ ⟨false, b, 0⟩ 0 = some ⟨false, c / b, 0⟩ := by
  simp only [Num.div, Nat.add_zero, Nat.pow_zero, Nat.mul_one, beq_iff_eq, hb, if_false]
  congr 2
  split <;> rfl

/-- `bc_modulo (c, base, &d, 0)` on non-negative integers. -/
theorem divmodInt (c b : Nat) (hb : b ≠ 0) :
    Num.divmod ⟨false, c, 0⟩ ⟨false, b, 0⟩ 0 = some (⟨false, c / b, 0⟩, ⟨false, c % b, 0⟩) := by
  simp only [Num.divmod, divInt c b hb]
  have hle : c / b * b ≤ c := Nat.div_mul_le_self c b
  have hmod : c % b = c - c / b * b := by
    have := Nat.div_add_mod c b; rw [Nat.mul_comm] at this; omega
  have hm : Num.mul ⟨false, c / b, 0⟩ ⟨false, b, 0⟩ (max 0 (0 + 0)) = ⟨false, c / b * b, 0⟩ := by
    simp only [Num.mul, Nat.add_zero, Nat.max_self, Nat.min_self, Nat.sub_self, Nat.pow_zero,
      Nat.div_one, bne_self_eq_false]
    split <;> rfl
  rw [hm]
  simp only [Num.sub, Num.align, Nat.max_self, Nat.sub_self, Nat.pow_zero, Nat.mul_one,
    bne_self_eq_false, Bool.false_eq_true, if_false, Nat.max_zero, Nat.zero_max]
  congr 2
  rcases Nat.lt_trichotomy (c / b * b) c with h | h | h
  · rw [show compare c (c / b * b) = .gt from Nat.compare_eq_gt.mpr h]; simp only [hmod]
  · rw [show compare c (c / b * b) = .eq from Nat.compare_eq_eq.mpr h.symm]
    simp only [Num.zero, hmod, h, Nat.sub_self]
  · omega

/-- `bc_num2long` of a small non-negative integer. -/
theorem toLong_int (r : Nat) (h : r ≤ 2147483649) : Num.toLong ⟨false, r, 0⟩ = r := by
  simp only [Num.toLong, Num.intPart, Nat.pow_zero, Nat.div_one, Num.longMax,
    Bool.false_eq_true, if_false]
  rw [if_pos (by omega)]

/-! ## The fraction loop -/

/-- The fraction at the loop head: non-negative, below one, at `num`'s
scale. -/
structure FracInv (f : Num) (s : Nat) : Prop where
  neg : f.neg = false
  scale : f.scale = s
  lt : f.mag < 10 ^ s

/-- `frac_part * base` at scale `s`. -/
theorem fracStep_mul {f : Num} {s b : Nat} (h : FracInv f s) :
    Num.mul f ⟨false, b, 0⟩ s = ⟨false, f.mag * b, s⟩ := by
  obtain ⟨n, m, s'⟩ := f
  obtain ⟨hn, hs, _⟩ := h
  simp only at hn hs; subst hn hs
  simp only [Num.mul, Nat.add_zero, Nat.max_self, Nat.zero_max, Nat.max_zero, Nat.min_self,
    Nat.sub_self, Nat.pow_zero, Nat.div_one, bne_self_eq_false]
  congr 1
  split <;> rfl

/-- The digit `bc_num2long (frac_part * base)`. -/
theorem fracStep_digit {f : Num} {s b : Nat} (h : FracInv f s) (hb0 : 0 < b) (hb : b < 2 ^ 31) :
    (Num.toLong ⟨false, f.mag * b, s⟩) = ↑(f.mag * b / 10 ^ s) ∧ f.mag * b / 10 ^ s < b := by
  have hlt : f.mag * b / 10 ^ s < b :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right h.lt hb0)
  refine ⟨?_, hlt⟩
  simp only [Num.toLong, Num.intPart, Num.longMax, Bool.false_eq_true, if_false]
  rw [if_pos (by omega)]

/-- `frac_part - digit` at scale `0`: the next fraction. -/
theorem fracStep_sub {f : Num} {s b : Nat} :
    Num.sub ⟨false, f.mag * b, s⟩ (Num.ofInt ↑(f.mag * b / 10 ^ s)) 0 =
      ⟨false, f.mag * b % 10 ^ s, s⟩ := by
  generalize f.mag * b = N
  have hof : Num.ofInt ↑(N / 10 ^ s) = ⟨false, N / 10 ^ s, 0⟩ := by
    simp only [Num.ofInt, Int.natAbs_natCast, Num.mk.injEq, and_true, decide_eq_false_iff_not]
    exact Int.not_lt.mpr (Int.ofNat_zero_le _)
  rw [hof]
  generalize hP : 10 ^ s = P
  have hdm := Nat.div_add_mod' N P
  simp only [Num.sub, Num.align, Nat.zero_max, Nat.max_zero, Nat.max_self, Nat.sub_zero, Nat.sub_self,
    Nat.pow_zero, Nat.mul_one, bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [hP]
  generalize N / P = q at hdm ⊢
  generalize N % P = r at hdm ⊢
  rcases Nat.lt_or_ge (q * P) N with hl | hl
  · rw [show compare N (q * P) = .gt from Nat.compare_eq_gt.mpr hl]
    generalize q * P = Q at hdm hl ⊢
    show (⟨false, N - Q, s⟩ : Num) = _
    congr 1; omega
  · rw [show compare N (q * P) = .eq from Nat.compare_eq_eq.mpr (by omega)]
    simp only [Num.zero, Num.mk.injEq, true_and, and_true]
    generalize q * P = Q at hdm hl
    omega

theorem fracStep_inv {f : Num} {s b : Nat} (_h : FracInv f s) :
    FracInv ⟨false, f.mag * b % 10 ^ s, s⟩ s :=
  ⟨rfl, rfl, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

/-- The decimal text of a positive number has as many characters as its
`n_len`. -/
theorem intLen_dec {t : Nat} (ht : t ≠ 0) :
    Num.intLen ⟨false, t, 0⟩ = (Num.decText t).length := by
  have hd : Num.decText t = (Num.digits 10 t).map Num.decChar := by
    have hst := digits_step 10 (by decide) t ht
    unfold Num.decText
    split
    · rename_i he; rw [hst] at he; simp at he
    · rfl
  have hne : (Num.digits 10 t).length ≠ 0 := by
    rw [digits_step 10 (by decide) t ht]; simp
  simp only [Num.intLen, Num.intPart, Nat.pow_zero, Nat.div_one, hd, List.length_map]
  omega

theorem digits_len_ge {s t : Nat} (h : 10 ^ s ≤ t) : s + 1 ≤ (Num.digits 10 t).length := by
  induction s generalizing t with
  | zero =>
    have ht : t ≠ 0 := by simp at h; omega
    rw [digits_step 10 (by decide) t ht]; simp
  | succ s ih =>
    have ht : t ≠ 0 := by have := Nat.pow_pos (n := s + 1) (show 0 < 10 by decide); omega
    rw [digits_step 10 (by decide) t ht, List.length_append, List.length_singleton]
    have : 10 ^ s ≤ t / 10 := by
      rw [Nat.le_div_iff_mul_le (by decide)]; rw [Nat.pow_succ] at h; exact h
    have := ih this; omega

theorem digits_len_le {s t : Nat} (ht : t ≠ 0) (h : t < 10 ^ s) : (Num.digits 10 t).length ≤ s := by
  induction s generalizing t with
  | zero => simp at h; omega
  | succ s ih =>
    rw [digits_step 10 (by decide) t ht, List.length_append, List.length_singleton]
    by_cases h0 : t / 10 = 0
    · rw [h0]; show (Num.digitsIn 10 1 0).length + 1 ≤ s + 1; simp [Num.digitsIn]
    · have : t / 10 < 10 ^ s := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.pow_succ] at h; exact h
      have := ih h0 this; omega

/-- A positive number has at most `s` decimal digits exactly when it is
below `10 ^ s`. -/
theorem decText_le_iff {t s : Nat} (ht : t ≠ 0) : (Num.decText t).length ≤ s ↔ t < 10 ^ s := by
  rw [← intLen_dec ht]
  have hpart : Num.intPart ⟨false, t, 0⟩ = t := by simp [Num.intPart]
  unfold Num.intLen
  rw [hpart]
  constructor
  · intro h
    rcases Nat.lt_or_ge t (10 ^ s) with h1 | h1
    · exact h1
    · have := digits_len_ge h1; omega
  · intro h
    have := digits_len_le ht h
    have : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp at h; omega
      · exact hs
    omega

/-- The loop's fuel bound: `t * 2 ^ fuel` stays at least `10 ^ s`. -/
def FracFuel (s t fuel : Nat) : Prop := 10 ^ s ≤ t * 2 ^ fuel

theorem fracFuel_init (s : Nat) : FracFuel s 1 (4 * s + 4) := by
  unfold FracFuel
  rw [Nat.one_mul, show 4 * s + 4 = 4 * (s + 1) by omega, Nat.pow_mul]
  calc 10 ^ s ≤ 10 ^ (s + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ (2 ^ 4) ^ (s + 1) := Nat.pow_le_pow_left (by decide) _

theorem fracFuel_pos {s t fuel : Nat} (h : FracFuel s t fuel) (ht : t < 10 ^ s) : 0 < fuel := by
  unfold FracFuel at h
  rcases Nat.eq_zero_or_pos fuel with rfl | hp
  · simp at h; omega
  · exact hp

theorem fracFuel_step {s t fuel b : Nat} (h : FracFuel s t (fuel + 1)) (hb : 2 ≤ b) :
    FracFuel s (t * b) fuel := by
  unfold FracFuel at h ⊢
  rw [Nat.pow_succ] at h
  calc 10 ^ s ≤ t * (2 ^ fuel * 2) := h
    _ = t * 2 * 2 ^ fuel := by rw [Nat.mul_comm (2 ^ fuel), Nat.mul_assoc]
    _ ≤ t * b * 2 ^ fuel := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)

/-- One more digit while `t < 10 ^ s`. -/
theorem fracDigits_unfold {b s t fuel : Nat} {f : Num} (ht0 : t ≠ 0) (ht : t < 10 ^ s) :
    Num.fracDigits b s (fuel + 1) f t =
      (Num.mul f ⟨false, b, 0⟩ s).toLong.natAbs ::
        Num.fracDigits b s fuel (Num.sub (Num.mul f ⟨false, b, 0⟩ s)
          (Num.ofInt (Num.mul f ⟨false, b, 0⟩ s).toLong.natAbs) 0) (t * b) := by
  rw [Num.fracDigits, if_pos ((decText_le_iff ht0).mpr ht)]

/-- No more digits once `t ≥ 10 ^ s`. -/
theorem fracDigits_stop {b s t fuel : Nat} {f : Num} (ht0 : t ≠ 0) (ht : 10 ^ s ≤ t) :
    Num.fracDigits b s fuel f t = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [Num.fracDigits, if_neg (fun h => by have := (decText_le_iff ht0).mp h; omega)]

/-! ## The whole output -/

/-- A nonzero number in a base other than 10. -/
theorem outChars_base {n : Num} {obase : Nat} (hz : n.isZero = false) (hb : obase ≠ 10) :
    Num.outChars n obase =
      (if n.neg then [45] else []) ++
        (Num.digits obase ((Num.div n Num.one 0).getD n).mag).flatMap
          (fun d => if obase ≤ 16 then [Num.hexChar d]
            else Num.outLong d (Num.decText (obase - 1)).length true) ++
        (if n.scale == 0 then []
         else 46 :: ((Num.fracDigits obase n.scale (4 * n.scale + 4)
            { Num.sub n ((Num.div n Num.one 0).getD n) 0 with neg := false } 1).zipIdx.flatMap
              fun (d, i) => if obase ≤ 16 then [Num.hexChar d]
                else Num.outLong d (Num.decText (obase - 1)).length (i != 0))) := by
  have hb' : (obase == 10) = false := by simp [hb]
  simp only [Num.outChars, hz, hb', Bool.false_eq_true, if_false]

end Dc.BcModel
