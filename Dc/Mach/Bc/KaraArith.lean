import Dc.Mach.Bc.KaraFill
import Dc.Mach.Bc.BcSub

/-!
# `_bc_rec_mul`'s Karatsuba step: the arithmetic

The values the step's obligations (`KDiffSpec`, `KM3Spec`, `KM1Spec`) state,
from the four halves' digit strings:

- `NumRep.subM_val`: `bc_sub` of two non-negative normalised integers is
  their distance, with the sign of the larger (`SubMVal`); this covers the
  machine's length-first route for an empty operand.
- `NumRep.len_le_of_lt`: a normalised integer below `10 ^ k` has at most `k`
  digits, so a difference is no longer than its longer operand.
- `kfill_val`: the Karatsuba identity by the differences' signs and the
  product's digit bound (`kara_bound`, `Dc/BcModel/Karatsuba.lean`) as
  `KFillVal`, for an operand split `U = U1 · 10^n + U0`.
-/

namespace Dc.Mach

open Dc.BcModel

/-! ## Digit counts and values of normalised integers -/

/-- A normalised integer's leading digit is nonzero when it has two digits
or more. -/
theorem NumRep.pow_le_of_norm {o : NumRep} (hs : NumShape o) (hsc : o.scale = 0) (hn : o.Norm)
    (h2 : 2 ≤ o.len) : 10 ^ (o.len - 1) ≤ dval o.ds := by
  rcases hn with h | h
  · omega
  · have hl := hs.dsLen
    rw [hsc, Nat.add_zero] at hl
    cases hds : o.ds with
    | nil => rw [hds] at hl; simp at hl; omega
    | cons d t =>
      rw [hds] at h hl
      simp only [List.getD_cons_zero] at h
      simp only [List.length_cons] at hl
      have h1 : d * 10 ^ t.length ≤ dval (d :: t) := dval_ge_head
      have h2 : 10 ^ t.length ≤ d * 10 ^ t.length := Nat.le_mul_of_pos_left _ (by omega)
      rw [show o.len - 1 = t.length by omega]
      omega

/-- **A normalised integer below `10 ^ k`** has at most `k` digits. -/
theorem NumRep.len_le_of_lt {o : NumRep} (hs : NumShape o) (hsc : o.scale = 0) (hn : o.Norm)
    {k : Nat} (hk : 1 ≤ k) (hv : dval o.ds < 10 ^ k) : o.len ≤ k := by
  rcases Nat.lt_or_ge o.len 2 with h | h
  · omega
  · have h1 := NumRep.pow_le_of_norm hs hsc hn h
    have h2 : 10 ^ (o.len - 1) < 10 ^ k := by omega
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).mp h2
    omega

/-- An integer's value is below `10 ^ len`. -/
theorem NumRep.val_lt {o : NumRep} (hs : NumShape o) (hsc : o.scale = 0) :
    dval o.ds < 10 ^ o.len := by
  have h := dval_lt hs.dig
  rwa [hs.dsLen, hsc, Nat.add_zero] at h

/-- A shorter integer is not above a longer normalised one. -/
theorem NumRep.val_le_of_len_lt {a b : NumRep} (ha : NumShape a) (hb : NumShape b)
    (sa : a.scale = 0) (sb : b.scale = 0) (hnb : b.Norm) (hl : a.len < b.len) :
    dval a.ds ≤ dval b.ds := by
  rcases Nat.lt_or_ge b.len 2 with h | h
  · rw [NumRep.mag_eq_zero ha (by omega)]; exact Nat.zero_le _
  · have h1 := NumRep.pow_le_of_norm hb sb hnb h
    have h2 := NumRep.val_lt ha sa
    have h3 : 10 ^ a.len ≤ 10 ^ (b.len - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- An integer's digit value is its handle value (`hdVal`). -/
theorem hdVal_eq_dval {y : NumObj} (hs : NumShape y.rep) (hsc : y.rep.scale = 0) :
    hdVal y = dval y.rep.ds := by
  show dvalBE (y.rep.ds.take y.rep.len) = _
  rw [List.take_of_length_le (by rw [hs.dsLen, hsc]; omega)]; rfl

/-! ## `bc_sub` of two non-negative integers -/

/-- `r` is the signed difference `A - B` of two magnitudes: scale `0`, the
distance, and the sign of the larger (either sign at `A = B`). -/
structure SubMVal (r : Dc.Num) (A B : Nat) : Prop where
  scale : r.scale = 0
  mag : r.mag + min A B = max A B
  negT : r.neg = true → A ≤ B
  negF : r.neg = false → B ≤ A

/-- **`bc_sub` of two non-negative normalised integers**, by either of the
machine's routes. -/
theorem NumRep.subM_val {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (sa : a.scale = 0)
    (sb : b.scale = 0) (na : a.neg = false) (nb : b.neg = false) (hna : a.Norm) (hnb : b.Norm) :
    SubMVal (a.subM b 0) (dval a.ds) (dval b.ds) := by
  unfold NumRep.subM
  by_cases h : a.neg = b.neg ∧ a.len ≠ b.len
  · rw [if_pos h]
    by_cases hl : a.len < b.len
    · rw [if_pos hl]
      have hle := NumRep.val_le_of_len_lt ha hb sa sb hnb hl
      have hv := subDigits_val (smin := 0) hb.dsLen ha.dsLen hb.dig ha.dig
        (by simp only [SubOK, sa, sb, Nat.max_self, Nat.sub_self, Nat.pow_zero, Nat.mul_one];
            exact hle)
      simp only [resScale, sa, sb, Nat.max_self, Nat.sub_self, Nat.pow_zero, Nat.mul_one] at hv
      refine ⟨by simp only [resScale, sa, sb]; rfl, ?_, fun _ => hle, fun e => ?_⟩
      · show dvalBE _ + _ = _
        rw [sa, sb, hv, ← dval_eq_dvalBE]; omega
      · simp only [nb] at e; exact absurd e (by decide)
    · rw [if_neg hl]
      have hle := NumRep.val_le_of_len_lt hb ha sb sa hna (by omega)
      have hv := subDigits_val (smin := 0) ha.dsLen hb.dsLen ha.dig hb.dig
        (by simp only [SubOK, sa, sb, Nat.max_self, Nat.sub_self, Nat.pow_zero, Nat.mul_one];
            exact hle)
      simp only [resScale, sa, sb, Nat.max_self, Nat.sub_self, Nat.pow_zero, Nat.mul_one] at hv
      refine ⟨by simp only [resScale, sa, sb]; rfl, ?_, fun e => ?_, fun _ => hle⟩
      · show dvalBE _ + _ = _
        rw [sa, sb, hv, ← dval_eq_dvalBE]; omega
      · simp only [na] at e; exact absurd e (by decide)
  · rw [if_neg h]
    simp only [Dc.Num.sub, NumRep.num, na, nb, sa, sb, Dc.Num.align, Nat.max_self, Nat.sub_self,
      Nat.pow_zero, Nat.mul_one, bne_self_eq_false, Bool.false_eq_true, if_false]
    rcases Nat.lt_trichotomy (dval a.ds) (dval b.ds) with hc | hc | hc
    · rw [Nat.compare_eq_lt.2 hc]
      exact ⟨rfl, by show _ - _ + _ = _; omega, fun _ => Nat.le_of_lt hc, fun e => by simp at e⟩
    · rw [Nat.compare_eq_eq.2 hc]
      exact ⟨rfl, by show 0 + _ = _; omega, fun e => by simp [Dc.Num.zero] at e, fun _ => Nat.le_of_eq hc.symm⟩
    · rw [Nat.compare_eq_gt.2 hc]
      exact ⟨rfl, by show _ - _ + _ = _; omega, fun e => by simp at e, fun _ => Nat.le_of_lt hc⟩

/-! ## The Karatsuba identity and the product's bound -/

/-- An operand split at `n`: `U1 · 10^n + U0 < 10^l`. -/
theorem split_lt {U1 U0 l n : Nat} (h1 : U1 < 10 ^ (l - n)) (h0 : U0 < 10 ^ (l - (l - n))) :
    U1 * 10 ^ n + U0 < 10 ^ l := by
  rcases Nat.lt_or_ge l n with hn | hn
  · have e1 : l - n = 0 := by omega
    have e0 : l - (l - n) = l := by omega
    rw [e1, Nat.pow_zero] at h1
    rw [e0] at h0
    rw [show U1 = 0 by omega, Nat.zero_mul, Nat.zero_add]; exact h0
  · have e : 10 ^ l = 10 ^ (l - n) * 10 ^ n := by rw [← Nat.pow_add]; congr 1; omega
    have e0 : 10 ^ (l - (l - n)) = 10 ^ n := by congr 1; omega
    rw [e0] at h0
    have hm : (U1 + 1) * 10 ^ n ≤ 10 ^ (l - n) * 10 ^ n := Nat.mul_le_mul_right _ h1
    rw [Nat.succ_mul] at hm
    omega

/-- **The filled product's arithmetic** for `U = U1 · 10^n + U0` and
`V = V1 · 10^n + V0`, `d1 = |U1 - U0|`, `d2 = |V0 - V1|` with signs `s1`,
`s2` (the sign of the larger). -/
theorem kfill_val {U1 U0 V1 V0 d1 d2 n la lb : Nat} {s1 s2 : Bool}
    (hla : 20 ≤ la) (hlb : 20 ≤ lb) (hn : n = (max la lb + 1) / 2)
    (hU1 : U1 < 10 ^ (la - n)) (hU0 : U0 < 10 ^ (la - (la - n)))
    (hV1 : V1 < 10 ^ (lb - n)) (hV0 : V0 < 10 ^ (lb - (lb - n)))
    (hd1 : d1 + min U1 U0 = max U1 U0) (hd2 : d2 + min V0 V1 = max V0 V1)
    (s1T : s1 = true → U1 ≤ U0) (s1F : s1 = false → U0 ≤ U1)
    (s2T : s2 = true → V0 ≤ V1) (s2F : s2 = false → V1 ≤ V0) :
    KFillVal (U1 * V1) (d1 * d2) (U0 * V0) (10 ^ n) ((U1 * 10 ^ n + U0) * (V1 * 10 ^ n + V0))
      (la + lb + 1) (s1 != s2) := by
  have hU := split_lt hU1 hU0
  have hV := split_lt hV1 hV0
  have hL : 10 ^ (la + lb + 1) = 10 ^ la * 10 ^ lb * 10 := by rw [Nat.pow_succ, Nat.pow_add]
  have huv : (U1 * 10 ^ n + U0) * (V1 * 10 ^ n + V0) < 10 ^ la * 10 ^ lb :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hU) hV (Nat.pow_pos (by decide))
  -- the identity in both sign cases
  have idAdd : (s1 != s2) = false → U1 * V1 * 10 ^ n * 10 ^ n + U1 * V1 * 10 ^ n +
      U0 * V0 * 10 ^ n + U0 * V0 + d1 * d2 * 10 ^ n =
      (U1 * 10 ^ n + U0) * (V1 * 10 ^ n + V0) := by
    intro hs
    cases s1 <;> cases s2 <;> simp at hs
    · have e1 : d1 + U0 = U1 := by have := s1F rfl; omega
      have e2 : d2 + V1 = V0 := by have := s2F rfl; omega
      subst e1 e2; grind
    · have e1 : d1 + U1 = U0 := by have := s1T rfl; omega
      have e2 : d2 + V0 = V1 := by have := s2T rfl; omega
      subst e1 e2; grind
  have idSub : (s1 != s2) = true → U1 * V1 * 10 ^ n * 10 ^ n + U1 * V1 * 10 ^ n +
      U0 * V0 * 10 ^ n + U0 * V0 =
      (U1 * 10 ^ n + U0) * (V1 * 10 ^ n + V0) + d1 * d2 * 10 ^ n := by
    intro hs
    cases s1 <;> cases s2 <;> simp at hs
    · have e1 : d1 + U0 = U1 := by have := s1F rfl; omega
      have e2 : d2 + V0 = V1 := by have := s2T rfl; omega
      subst e1 e2; grind
    · have e1 : d1 + U1 = U0 := by have := s1T rfl; omega
      have e2 : d2 + V1 = V0 := by have := s2F rfl; omega
      subst e1 e2; grind
  refine ⟨?_, idSub, idAdd, by omega⟩
  exact kara_bound hU hV
    (Nat.lt_of_lt_of_le hU0 (Nat.pow_le_pow_right (by decide) (by omega)))
    (Nat.lt_of_lt_of_le hV0 (Nat.pow_le_pow_right (by decide) (by omega)))
    (by omega) (by omega) (by omega)

end Dc.Mach
