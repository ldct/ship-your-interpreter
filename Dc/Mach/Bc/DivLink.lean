import Dc.Mach.Bc.DivEntry
import Dc.BcModel.DivNorm

/-!
# `bc_divide`'s buffers against `Num.div`

`bc_divide` divides the raw dividend buffer `dvXs0` (a zero, `n1`'s digits,
`dvExtra + 1` zeros) by the raw divisor `dvVs0` (`n2`'s digits up to the
trimmed scale, from the first nonzero digit), both scaled by `dvNorm`.

- `dv_shape`: the loop's `DvShape` for the normalised buffers.
- `dv_quot`: the loop's quotient is `Num.div`'s magnitude.
- `dv_quot_zero`: a dividend shorter than the divisor has quotient zero.
-/

namespace Dc.Mach

open Dc.BcModel

/-- The raw dividend buffer: a zero, `n1`'s digits, `e + 1` zeros. -/
abbrev dvXs0 (ds : List Nat) (e : Nat) : List Nat := 0 :: ds ++ List.replicate (e + 1) 0

/-- The raw divisor: `n2`'s first `len2` digits from the first nonzero `z0`. -/
abbrev dvVs0 (ds : List Nat) (len2 z0 : Nat) : List Nat := (ds.take len2).drop z0

/-- The normalisation factor `10 / (v1 + 1)`. -/
abbrev dvNorm (vs : List Nat) : Nat := 10 / (vs.getD 0 0 + 1)

theorem dvXs0_length (ds : List Nat) (e : Nat) : (dvXs0 ds e).length = ds.length + e + 2 := by
  simp only [dvXs0, List.cons_append, List.length_cons, List.length_append, List.length_replicate]
  omega

theorem dvXs0_digits {ds : List Nat} (hd : IsDigits ds) (e : Nat) : IsDigits (dvXs0 ds e) :=
  fun d h => by
    simp only [dvXs0, List.cons_append, List.mem_cons, List.mem_append, List.mem_replicate] at h
    rcases h with rfl | h | ⟨_, rfl⟩
    · decide
    · exact hd d h
    · decide

theorem dvXs0_val_lt {ds : List Nat} (hd : IsDigits ds) (e : Nat) {nm : Nat} (hn : nm ≤ 10) :
    dvalBE (dvXs0 ds e) * nm < 10 ^ (dvXs0 ds e).length := by
  have hr := dvalBE_lt (dvXs0_digits hd e)
  simp only [dvXs0, List.cons_append, dvalBE_cons, Nat.zero_mul, Nat.zero_add, List.length_cons] at hr ⊢
  have hr' := dvalBE_lt (fun d h => dvXs0_digits hd e d (List.mem_cons_of_mem _ (by
    simpa only [dvXs0, List.cons_append] using h)))
  rw [Nat.pow_succ]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hn) (Nat.mul_lt_mul_of_pos_right hr' (by decide))

theorem dvVs0_length {ds : List Nat} {len2 z0 : Nat} (hl : len2 ≤ ds.length) :
    (dvVs0 ds len2 z0).length = len2 - z0 := by
  simp only [dvVs0, List.length_drop, List.length_take]; omega

theorem dvVs0_getD {ds : List Nat} {len2 z0 i : Nat} (hl : len2 ≤ ds.length) (hi : z0 + i < len2) :
    (dvVs0 ds len2 z0).getD i 0 = ds.getD (z0 + i) 0 := by
  simp only [dvVs0, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_take, if_pos hi]

theorem dvVs0_digits {ds : List Nat} (hd : IsDigits ds) (len2 z0 : Nat) : IsDigits (dvVs0 ds len2 z0) :=
  fun d h => hd d (List.mem_of_mem_take (List.mem_of_mem_drop h))

/-- The raw divisor's facts: `L` digits, a nonzero first digit, the
normalised value below `10^L` with top digit at least `5`. -/
structure DvVs (vs0 : List Nat) (L : Nat) : Prop where
  len : vs0.length = L
  dig : IsDigits vs0
  l1 : 1 ≤ L
  first : 0 < vs0.getD 0 0
  nlt : dvalBE vs0 * dvNorm vs0 < 10 ^ L
  nge : 10 ^ (L - 1) * dvNorm vs0 ≤ dvalBE vs0 * dvNorm vs0
  top : 5 ≤ (digBE (dvalBE vs0 * dvNorm vs0) L).getD 0 0
  npos : 0 < dvNorm vs0
  nle : dvNorm vs0 ≤ 5

theorem dvVs_of {ds : List Nat} (hd : IsDigits ds) {len2 z0 : Nat} (hl : len2 ≤ ds.length)
    (hzl : z0 < len2) (hnz : ds.getD z0 0 ≠ 0) : DvVs (dvVs0 ds len2 z0) (len2 - z0) := by
  have hlen := dvVs0_length (z0 := z0) hl
  have hdig := dvVs0_digits hd len2 z0
  have h0 : (dvVs0 ds len2 z0).getD 0 0 = ds.getD z0 0 := dvVs0_getD hl (by omega)
  have hf : 0 < (dvVs0 ds len2 z0).getD 0 0 := by rw [h0]; omega
  have hv := normDiv_val hdig (by omega) hf
  have hp := norm_pos hf (by rw [h0]; exact hd.getD z0)
  rw [hlen] at hv
  exact ⟨hlen, hdig, by omega, hf, hv.1, hv.2.1, hv.2.2, hp.1, hp.2⟩

/-- The loop's buffers from the raw ones. -/
structure DvBuild (D : DvData) (xs0 vs0 : List Nat) (len1 k : Nat) : Prop where
  xs : D.xs = digBE (dvalBE xs0 * dvNorm vs0) xs0.length
  vs : D.vs = digBE (dvalBE vs0 * dvNorm vs0) D.L
  kb : D.Kb + D.L = len1 + k

/-- **The loop's shape** for the normalised buffers of `dvXs0` and `dvVs0`. -/
theorem dv_shape {D : DvData} {ds1 vs0 : List Nat} {l1 sa s2 k : Nat}
    (hd1 : IsDigits ds1) (hl1 : ds1.length = l1 + sa) (hv : DvVs vs0 D.L)
    (hb : DvBuild D (dvXs0 ds1 (k + s2 - sa)) vs0 (l1 + s2) k) (hle : D.L ≤ l1 + s2 + k)
    (hsz : l1 + sa + k + s2 < 2 ^ 28) : DvShape D := by
  have hxl := dvXs0_length ds1 (k + s2 - sa)
  have hxd := dvXs0_digits hd1 (k + s2 - sa)
  have hX := dvXs0_val_lt hd1 (k + s2 - sa) (nm := dvNorm vs0) (by have := hv.nle; omega)
  have hkb := hb.kb
  have hvl : D.vs.length = D.L := by rw [hb.vs, digBE_length]
  have hxsl : D.xs.length = ds1.length + (k + s2 - sa) + 2 := by rw [hb.xs, digBE_length, hxl]
  refine ⟨hvl, by rw [hb.vs]; exact digBE_digits _ _, hv.l1, by rw [hb.vs]; exact hv.top, by omega,
    by rw [hb.xs]; exact digBE_digits _ _, ?_, by omega⟩
  simp only [DvData.pre, DvData.V, Nat.add_zero]
  rw [hb.vs, digBE_val, Nat.mod_eq_of_lt hv.nlt, hb.xs]
  exact normDiv_first hxd (by omega) rfl hv.npos hv.nge hv.l1 hX

/-- **The quotient**: the loop's `pre (Kb + 1) / V` is `Num.div`'s magnitude. -/
theorem dv_quot {D : DvData} {ds1 ds2 : List Nat} {l1 sa ln2 sb s2 z0 k : Nat}
    (hd1 : IsDigits ds1) (hl1 : ds1.length = l1 + sa) (hl2 : ds2.length = ln2 + sb)
    (hs2 : s2 ≤ sb) (htz : ∀ j, s2 ≤ j → j < sb → ds2.getD (ln2 + j) 0 = 0)
    (hz : ∀ i, i < z0 → ds2.getD i 0 = 0) (hzl : z0 < ln2 + s2)
    (hv : DvVs (dvVs0 ds2 (ln2 + s2) z0) D.L)
    (hb : DvBuild D (dvXs0 ds1 (k + s2 - sa)) (dvVs0 ds2 (ln2 + s2) z0) (l1 + s2) k)
    (hle : D.L ≤ l1 + s2 + k) :
    D.pre (D.Kb + 1) / D.V = dvalBE ds1 * 10 ^ (sb + k) / (dvalBE ds2 * 10 ^ sa) := by
  have hxl := dvXs0_length ds1 (k + s2 - sa)
  have hxd := dvXs0_digits hd1 (k + s2 - sa)
  have hX := dvXs0_val_lt hd1 (k + s2 - sa) (nm := dvNorm (dvVs0 ds2 (ln2 + s2) z0))
    (by have := hv.nle; omega)
  have hkb := hb.kb
  have hV0 : 0 < dvalBE (dvVs0 ds2 (ln2 + s2) z0) := by
    have := dvalBE_ge_of_first (by rw [hv.len]; exact hv.l1) hv.first
    have := Nat.pow_pos (n := (dvVs0 ds2 (ln2 + s2) z0).length - 1) (by decide : 0 < 10)
    omega
  simp only [DvData.pre, DvData.V]
  rw [hb.vs, digBE_val, Nat.mod_eq_of_lt hv.nlt, hb.xs, show D.L + (D.Kb + 1) = l1 + s2 + k + 1 by omega,
    normDiv_quot hxd (by omega) hv.npos hV0 hX, dvx_take_val hd1 hl1,
    div_value _ _ _ _ _ _ _ hs2 (dv2_val hl2 hs2 htz hz (by omega))]

/-- **A short dividend** (`len1 + k < L`): `Num.div`'s magnitude is zero. -/
theorem dv_quot_zero {ds1 ds2 : List Nat} {l1 sa ln2 sb s2 z0 k : Nat}
    (hd1 : IsDigits ds1) (hl1 : ds1.length = l1 + sa) (hl2 : ds2.length = ln2 + sb)
    (hs2 : s2 ≤ sb) (htz : ∀ j, s2 ≤ j → j < sb → ds2.getD (ln2 + j) 0 = 0)
    (hz : ∀ i, i < z0 → ds2.getD i 0 = 0) (hzl : z0 < ln2 + s2)
    (hv : DvVs (dvVs0 ds2 (ln2 + s2) z0) (ln2 + s2 - z0)) (hlt : l1 + s2 + k < ln2 + s2 - z0) :
    dvalBE ds1 * 10 ^ (sb + k) / (dvalBE ds2 * 10 ^ sa) = 0 := by
  rw [div_value _ _ _ _ _ _ _ hs2 (dv2_val hl2 hs2 htz hz (by omega))]
  have hA := dvalBE_lt hd1
  rw [hl1] at hA
  have hge := dvalBE_ge_of_first (by rw [hv.len]; exact hv.l1) hv.first
  rw [hv.len] at hge
  exact dv_short_zero hA hlt hge

end Dc.Mach
