import Dc.BcModel.Digits

/-!
# The digit arrays `_bc_do_add` and `_bc_do_sub` build

For operands with `l` integer and `s` fraction digits (big-endian `ds`,
`ds.length = l + s`), result scale `s' = max smin (max s1 s2)`:

- `addDigits`: `_bc_do_add`'s array of `max l1 l2 + 1` integer and `s'`
  fraction digits. Its value is the sum of the operands aligned to `s'`
  (`addDigits_val`).
- `subDigits`: `_bc_do_sub`'s array of `max l1 l2` integer and `s'` fraction
  digits; for a subtrahend not above the minuend its value is the difference
  (`subDigits_val`).

Both are the little-endian loop results (`addLE`, `subLE` over `padLE`)
reversed, followed by the `scale_min` zero padding.
-/

namespace Dc.BcModel

/-- The fraction scale of the loops: `max s1 s2`. -/
abbrev loopScale (s1 s2 : Nat) : Nat := max s1 s2

/-- The positions the loops run over: `max l1 l2 + max s1 s2`. -/
abbrev loopLen (l1 s1 l2 s2 : Nat) : Nat := max l1 l2 + max s1 s2

/-- The aligned little-endian operands of the loops. -/
abbrev opLE (ds : List Nat) (sc l1 s1 l2 s2 : Nat) : List Nat :=
  padLE ds sc (loopScale s1 s2) (loopLen l1 s1 l2 s2)

/-- `_bc_do_add`'s digit array. -/
def addDigits (l1 s1 : Nat) (ds1 : List Nat) (l2 s2 : Nat) (ds2 : List Nat) (smin : Nat) :
    List Nat :=
  (addLE (opLE ds1 s1 l1 s1 l2 s2) (opLE ds2 s2 l1 s1 l2 s2) 0).reverse ++
    List.replicate (smin - loopScale s1 s2) 0

/-- `_bc_do_sub`'s digit array. -/
def subDigits (l1 s1 : Nat) (ds1 : List Nat) (l2 s2 : Nat) (ds2 : List Nat) (smin : Nat) :
    List Nat :=
  (subLE (opLE ds1 s1 l1 s1 l2 s2) (opLE ds2 s2 l1 s1 l2 s2) 0).reverse ++
    List.replicate (smin - loopScale s1 s2) 0

/-- The result scale. -/
abbrev resScale (s1 s2 smin : Nat) : Nat := max smin (max s1 s2)

theorem opLE_length {ds : List Nat} {sc l : Nat} (h : ds.length = l + sc) (l1 s1 l2 s2 : Nat)
    (hl : l ≤ max l1 l2) (hs : sc ≤ max s1 s2) :
    (opLE ds sc l1 s1 l2 s2).length = loopLen l1 s1 l2 s2 :=
  padLE_length _ _ _ _ (by simp only [loopScale, loopLen] at *; omega)

theorem pow_split (s1 s2 smin : Nat) :
    10 ^ (max s1 s2 - s1) * 10 ^ (smin - max s1 s2) = 10 ^ (max smin (max s1 s2) - s1) := by
  rw [← Nat.pow_add]; congr 1; omega

theorem pow_split' (s1 s2 smin : Nat) :
    10 ^ (max s1 s2 - s2) * 10 ^ (smin - max s1 s2) = 10 ^ (max smin (max s1 s2) - s2) := by
  rw [← Nat.pow_add]; congr 1; omega

theorem addDigits_length {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) :
    (addDigits l1 s1 ds1 l2 s2 ds2 smin).length = max l1 l2 + 1 + resScale s1 s2 smin := by
  have e1 := opLE_length h1 l1 s1 l2 s2 (by omega) (by omega)
  have e2 := opLE_length h2 l1 s1 l2 s2 (by omega) (by omega)
  simp only [addDigits, List.length_append, List.length_reverse, List.length_replicate]
  rw [addLE_length _ _ _ (by rw [e1, e2]), e1]
  simp only [loopLen, loopScale, resScale]; omega

theorem addDigits_val {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) :
    dvalBE (addDigits l1 s1 ds1 l2 s2 ds2 smin) =
      dvalBE ds1 * 10 ^ (resScale s1 s2 smin - s1) + dvalBE ds2 * 10 ^ (resScale s1 s2 smin - s2) := by
  have e1 := opLE_length h1 l1 s1 l2 s2 (by omega) (by omega)
  have e2 := opLE_length h2 l1 s1 l2 s2 (by omega) (by omega)
  simp only [addDigits, dvalBE_append, dvalBE_reverse, dvalBE_replicate_zero, List.length_replicate,
    Nat.add_zero]
  rw [addLE_val _ _ _ (by rw [e1, e2]), padLE_val, padLE_val, Nat.add_zero, Nat.add_mul,
    Nat.mul_assoc, Nat.mul_assoc]
  simp only [loopScale, resScale]
  rw [pow_split, pow_split']

theorem addDigits_digits {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) (d1 : IsDigits ds1) (d2 : IsDigits ds2) :
    IsDigits (addDigits l1 s1 ds1 l2 s2 ds2 smin) := by
  have e1 := opLE_length h1 l1 s1 l2 s2 (by omega) (by omega)
  have e2 := opLE_length h2 l1 s1 l2 s2 (by omega) (by omega)
  intro d hd
  simp only [addDigits, List.mem_append, List.mem_reverse, List.mem_replicate] at hd
  rcases hd with hd | ⟨_, rfl⟩
  · exact addLE_digits _ _ _ (padLE_digits d1 _ _ _) (padLE_digits d2 _ _ _) (by decide)
      (by rw [e1, e2]) d hd
  · decide

theorem subDigits_length {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) :
    (subDigits l1 s1 ds1 l2 s2 ds2 smin).length = max l1 l2 + resScale s1 s2 smin := by
  have e1 := opLE_length h1 l1 s1 l2 s2 (by omega) (by omega)
  have e2 := opLE_length h2 l1 s1 l2 s2 (by omega) (by omega)
  simp only [subDigits, List.length_append, List.length_reverse, List.length_replicate]
  rw [subLE_length _ _ _ (by rw [e1, e2]), e1]
  simp only [loopLen, loopScale, resScale]; omega

/-- The subtrahend aligned is at most the minuend aligned. -/
abbrev SubOK (s1 s2 : Nat) (ds1 ds2 : List Nat) : Prop :=
  dvalBE ds2 * 10 ^ (max s1 s2 - s2) ≤ dvalBE ds1 * 10 ^ (max s1 s2 - s1)

theorem subDigits_val {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) (d1 : IsDigits ds1) (d2 : IsDigits ds2)
    (hle : SubOK s1 s2 ds1 ds2) :
    dvalBE (subDigits l1 s1 ds1 l2 s2 ds2 smin) =
      dvalBE ds1 * 10 ^ (resScale s1 s2 smin - s1) - dvalBE ds2 * 10 ^ (resScale s1 s2 smin - s2) := by
  have e1 := opLE_length h1 l1 s1 l2 s2 (by omega) (by omega)
  have e2 := opLE_length h2 l1 s1 l2 s2 (by omega) (by omega)
  have hex := subLE_exact _ _ (by rw [e1, e2]) (padLE_digits d1 s1 (loopScale s1 s2) (loopLen l1 s1 l2 s2))
    (padLE_digits d2 s2 (loopScale s1 s2) (loopLen l1 s1 l2 s2))
    (by rw [padLE_val, padLE_val]; exact hle)
  simp only [subDigits, dvalBE_append, dvalBE_reverse, dvalBE_replicate_zero, List.length_replicate,
    Nat.add_zero]
  rw [hex.2, padLE_val, padLE_val, Nat.sub_mul, Nat.mul_assoc, Nat.mul_assoc]
  simp only [loopScale, resScale]
  rw [pow_split, pow_split']

theorem subDigits_digits {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (d1 : IsDigits ds1) (d2 : IsDigits ds2) :
    IsDigits (subDigits l1 s1 ds1 l2 s2 ds2 smin) := by
  intro d hd
  simp only [subDigits, List.mem_append, List.mem_reverse, List.mem_replicate] at hd
  rcases hd with hd | ⟨_, rfl⟩
  · exact subLE_digits _ _ _ (padLE_digits d1 _ _ _) (padLE_digits d2 _ _ _) (by decide) d hd
  · decide

/-! ## `bc_add` and `bc_sub` on values -/

theorem resScale_comm (s1 s2 smin : Nat) : resScale s2 s1 smin = resScale s1 s2 smin := by
  simp only [resScale]; omega

/-- `Num.align` at the result scale is the aligned digit value. -/
theorem align_res (neg : Bool) (ds : List Nat) (sc s1 s2 smin : Nat) :
    (Dc.Num.mk neg (dvalBE ds) sc).align (max smin (max s1 s2)) = dvalBE ds * 10 ^ (max smin (max s1 s2) - sc) :=
  rfl

/-- Same signs: `bc_add` is `_bc_do_add` with the first operand's sign. -/
theorem num_add_same {n1 n2 : Bool} {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) (hs : n1 = n2) :
    Dc.Num.add ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ smin =
      ⟨n1, dvalBE (addDigits l1 s1 ds1 l2 s2 ds2 smin), resScale s1 s2 smin⟩ := by
  subst hs
  rw [addDigits_val h1 h2]
  simp [Dc.Num.add, Dc.Num.align, resScale]

/-- Different signs, first magnitude larger: `_bc_do_sub (n1, n2)` with `n1`'s sign. -/
theorem num_add_gt {n1 n2 : Bool} {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) (d1 : IsDigits ds1) (d2 : IsDigits ds2)
    (hs : n1 ≠ n2)
    (hc : Dc.Num.cmpMag ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ = .gt) :
    Dc.Num.add ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ smin =
      ⟨n1, dvalBE (subDigits l1 s1 ds1 l2 s2 ds2 smin), resScale s1 s2 smin⟩ := by
  simp only [Dc.Num.cmpMag, Dc.Num.align] at hc
  have hgt : dvalBE ds2 * 10 ^ (max s1 s2 - s2) < dvalBE ds1 * 10 ^ (max s1 s2 - s1) := by
    simp only [compare, compareOfLessAndEq] at hc
    split at hc
    · cases hc
    · split at hc
      · cases hc
      · omega
  rw [subDigits_val h1 h2 d1 d2 (Nat.le_of_lt hgt)]
  have e1 := pow_split s1 s2 smin
  have e2 := pow_split' s1 s2 smin
  have hgt' : dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2) < dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1) := by
    rw [← e1, ← e2, ← Nat.mul_assoc, ← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right hgt (Nat.pow_pos (by decide))
  have hne : (n1 == n2) = false := by cases n1 <;> cases n2 <;> simp_all
  simp only [Dc.Num.add, Dc.Num.align, hne, resScale]
  simp only [Bool.false_eq_true, ite_false]
  rw [show compare (dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1))
      (dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2)) = .gt from
    Nat.compare_eq_gt.mpr hgt']

/-- Different signs, first magnitude smaller: `_bc_do_sub (n2, n1)` with `n2`'s sign. -/
theorem num_add_lt {n1 n2 : Bool} {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) (d1 : IsDigits ds1) (d2 : IsDigits ds2)
    (hs : n1 ≠ n2)
    (hc : Dc.Num.cmpMag ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ = .lt) :
    Dc.Num.add ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ smin =
      ⟨n2, dvalBE (subDigits l2 s2 ds2 l1 s1 ds1 smin), resScale s1 s2 smin⟩ := by
  simp only [Dc.Num.cmpMag, Dc.Num.align] at hc
  have hlt : dvalBE ds1 * 10 ^ (max s1 s2 - s1) < dvalBE ds2 * 10 ^ (max s1 s2 - s2) :=
    Nat.compare_eq_lt.mp hc
  have hle : SubOK s2 s1 ds2 ds1 := by
    simp only [SubOK, Nat.max_comm s2 s1]; exact Nat.le_of_lt hlt
  rw [subDigits_val h2 h1 d2 d1 hle, resScale_comm]
  have e1 := pow_split s1 s2 smin
  have e2 := pow_split' s1 s2 smin
  have hlt' : dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1) < dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2) := by
    rw [← e1, ← e2, ← Nat.mul_assoc, ← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right hlt (Nat.pow_pos (by decide))
  have hne : (n1 == n2) = false := by cases n1 <;> cases n2 <;> simp_all
  simp only [Dc.Num.add, Dc.Num.align, hne, resScale]
  simp only [Bool.false_eq_true, ite_false]
  rw [show compare (dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1))
      (dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2)) = .lt from
    Nat.compare_eq_lt.mpr hlt']

/-- Different signs, equal magnitudes: zero at the result scale. -/
theorem num_add_eq {n1 n2 : Bool} {s1 s2 smin : Nat} {ds1 ds2 : List Nat} (hs : n1 ≠ n2)
    (hc : Dc.Num.cmpMag ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ = .eq) :
    Dc.Num.add ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ smin = Dc.Num.zero (resScale s1 s2 smin) := by
  simp only [Dc.Num.cmpMag, Dc.Num.align] at hc
  have heq : dvalBE ds1 * 10 ^ (max s1 s2 - s1) = dvalBE ds2 * 10 ^ (max s1 s2 - s2) :=
    Nat.compare_eq_eq.mp hc
  have e1 := pow_split s1 s2 smin
  have e2 := pow_split' s1 s2 smin
  have heq' : dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1) = dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2) := by
    rw [← e1, ← e2, ← Nat.mul_assoc, ← Nat.mul_assoc, heq]
  have hne : (n1 == n2) = false := by cases n1 <;> cases n2 <;> simp_all
  simp only [Dc.Num.add, Dc.Num.align, hne, resScale]
  simp only [Bool.false_eq_true, ite_false]
  rw [show compare (dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1))
      (dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2)) = .eq from Nat.compare_eq_eq.mpr heq']

/-- Different signs: `bc_sub` is `_bc_do_add` with the first operand's sign. -/
theorem num_sub_diff {n1 n2 : Bool} {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) (hs : n1 ≠ n2) :
    Dc.Num.sub ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ smin =
      ⟨n1, dvalBE (addDigits l1 s1 ds1 l2 s2 ds2 smin), resScale s1 s2 smin⟩ := by
  rw [addDigits_val h1 h2]
  have hne : (n1 != n2) = true := by cases n1 <;> cases n2 <;> simp_all
  simp [Dc.Num.sub, Dc.Num.align, resScale, hne]

/-- Same signs, first magnitude larger: `_bc_do_sub (n1, n2)` with `n1`'s sign. -/
theorem num_sub_gt {n1 n2 : Bool} {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) (d1 : IsDigits ds1) (d2 : IsDigits ds2)
    (hs : n1 = n2)
    (hc : Dc.Num.cmpMag ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ = .gt) :
    Dc.Num.sub ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ smin =
      ⟨n1, dvalBE (subDigits l1 s1 ds1 l2 s2 ds2 smin), resScale s1 s2 smin⟩ := by
  subst hs
  simp only [Dc.Num.cmpMag, Dc.Num.align] at hc
  have hgt : dvalBE ds2 * 10 ^ (max s1 s2 - s2) < dvalBE ds1 * 10 ^ (max s1 s2 - s1) :=
    Nat.compare_eq_gt.mp hc
  rw [subDigits_val h1 h2 d1 d2 (Nat.le_of_lt hgt)]
  have e1 := pow_split s1 s2 smin
  have e2 := pow_split' s1 s2 smin
  have hgt' : dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2) < dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1) := by
    rw [← e1, ← e2, ← Nat.mul_assoc, ← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right hgt (Nat.pow_pos (by decide))
  simp only [Dc.Num.sub, Dc.Num.align, bne_self_eq_false, resScale]
  simp only [Bool.false_eq_true, ite_false]
  rw [show compare (dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1))
      (dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2)) = .gt from Nat.compare_eq_gt.mpr hgt']

/-- Same signs, first magnitude smaller: `_bc_do_sub (n2, n1)` with the
opposite of `n2`'s sign. -/
theorem num_sub_lt {n1 n2 : Bool} {l1 s1 l2 s2 smin : Nat} {ds1 ds2 : List Nat}
    (h1 : ds1.length = l1 + s1) (h2 : ds2.length = l2 + s2) (d1 : IsDigits ds1) (d2 : IsDigits ds2)
    (hs : n1 = n2)
    (hc : Dc.Num.cmpMag ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ = .lt) :
    Dc.Num.sub ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ smin =
      ⟨!n2, dvalBE (subDigits l2 s2 ds2 l1 s1 ds1 smin), resScale s1 s2 smin⟩ := by
  subst hs
  simp only [Dc.Num.cmpMag, Dc.Num.align] at hc
  have hlt : dvalBE ds1 * 10 ^ (max s1 s2 - s1) < dvalBE ds2 * 10 ^ (max s1 s2 - s2) :=
    Nat.compare_eq_lt.mp hc
  have hle : SubOK s2 s1 ds2 ds1 := by
    simp only [SubOK, Nat.max_comm s2 s1]; exact Nat.le_of_lt hlt
  rw [subDigits_val h2 h1 d2 d1 hle, resScale_comm]
  have e1 := pow_split s1 s2 smin
  have e2 := pow_split' s1 s2 smin
  have hlt' : dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1) < dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2) := by
    rw [← e1, ← e2, ← Nat.mul_assoc, ← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right hlt (Nat.pow_pos (by decide))
  simp only [Dc.Num.sub, Dc.Num.align, bne_self_eq_false, resScale]
  simp only [Bool.false_eq_true, ite_false]
  rw [show compare (dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1))
      (dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2)) = .lt from Nat.compare_eq_lt.mpr hlt']

/-- Same signs, equal magnitudes: zero at the result scale. -/
theorem num_sub_eq {n1 n2 : Bool} {s1 s2 smin : Nat} {ds1 ds2 : List Nat} (hs : n1 = n2)
    (hc : Dc.Num.cmpMag ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ = .eq) :
    Dc.Num.sub ⟨n1, dvalBE ds1, s1⟩ ⟨n2, dvalBE ds2, s2⟩ smin = Dc.Num.zero (resScale s1 s2 smin) := by
  subst hs
  simp only [Dc.Num.cmpMag, Dc.Num.align] at hc
  have heq : dvalBE ds1 * 10 ^ (max s1 s2 - s1) = dvalBE ds2 * 10 ^ (max s1 s2 - s2) :=
    Nat.compare_eq_eq.mp hc
  have e1 := pow_split s1 s2 smin
  have e2 := pow_split' s1 s2 smin
  have heq' : dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1) = dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2) := by
    rw [← e1, ← e2, ← Nat.mul_assoc, ← Nat.mul_assoc, heq]
  simp only [Dc.Num.sub, Dc.Num.align, bne_self_eq_false, resScale]
  simp only [Bool.false_eq_true, ite_false]
  rw [show compare (dvalBE ds1 * 10 ^ (max smin (max s1 s2) - s1))
      (dvalBE ds2 * 10 ^ (max smin (max s1 s2) - s2)) = .eq from Nat.compare_eq_eq.mpr heq']

end Dc.BcModel
