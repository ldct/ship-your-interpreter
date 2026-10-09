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
  kb : D.Kb = len1 + k - D.L

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

/-- `Num.div` by a nonzero divisor. -/
theorem num_div_some {a b : Num} (k : Nat) (hb : b.mag ≠ 0) :
    Num.div a b k = some ⟨if a.mag * 10 ^ (b.scale + k) / (b.mag * 10 ^ a.scale) = 0 then false
      else a.neg != b.neg, a.mag * 10 ^ (b.scale + k) / (b.mag * 10 ^ a.scale), k⟩ := by
  simp only [Num.div, beq_iff_eq, hb, if_false]

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `n2`'s digits as `bc_divide` reads them: the trimmed scale `s2`, zeros
past it and before the first nonzero digit `z0`. -/
structure DvDivisor (x2 : NumObj) (s2 z0 : Nat) : Prop where
  s2le : s2 ≤ x2.rep.scale
  tz : ∀ j, s2 ≤ j → j < x2.rep.scale → x2.rep.ds.getD (x2.rep.len + j) 0 = 0
  lz : ∀ i, i < z0 → x2.rep.ds.getD i 0 = 0
  zl : z0 < x2.rep.len + s2
  nz : x2.rep.ds.getD z0 0 ≠ 0

/-- **`bc_divide` from `0x80005a50`** with both buffers in place: the length
dispatch, then the quotient loop or the zero quotient. -/
theorem dv_after {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z : NumObj} {D : DvData} {H : Heap} {F : List Blk} {n : Option Num} {s2 z0 k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S Q R0 Mt0 Fr q sp W n)
    (hn : n = Num.div x1.rep.num x2.rep.num k)
    (bf : DvBufs S Mt0 M R0 sp W D H F L0)
    (hx1 : x1 ∈ L0) (hx2 : x2 ∈ L0) (hdv : DvDivisor x2 s2 z0)
    (hb : DvBuild D (dvXs0 x1.rep.ds (k + s2 - x1.rep.scale))
      (dvVs0 x2.rep.ds (x2.rep.len + s2) z0) (x1.rep.len + s2) k)
    (hL : D.L = x2.rep.len + s2 - z0) (hoff : D.off = D.L - (x1.rep.len + s2))
    (hn1 : D.n1p = x1.rep.p) (hn2 : D.n2p = x2.rep.p) (hrs : D.rs = q)
    (hx : ∀ i, i < (dvXs0 x1.rep.ds (k + s2 - x1.rep.scale)).length →
      imgM M (D.P + i) = BitVec.ofNat 8 ((dvXs0 x1.rep.ds (k + s2 - x1.rep.scale)).getD i 0))
    (hv : ∀ i, i < D.L → imgM M (D.N + i) =
      BitVec.ofNat 8 ((dvVs0 x2.rep.ds (x2.rep.len + s2) z0).getD i 0))
    (hsent : imgM M (D.N + D.L) = 0#8)
    (hsz : x1.rep.len + x1.rep.scale + k + x2.rep.len + x2.rep.scale < 2 ^ 27)
    (hr0 : QSlot Mt0 q L0 Fr) (hz : z ∈ L0)
    (hzg : ldv .ld Mt0 zeroAddr = BitVec.ofNat 64 z.rep.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p)
    (h16 : R 16 = BitVec.ofNat 64 (D.L + 1)) (h18 : R 18 = BitVec.ofNat 64 D.P)
    (h19 : R 19 = BitVec.ofNat 64 D.b2.pay) (h21 : R 21 = BitVec.ofNat 64 k)
    (h22 : R 22 = BitVec.ofNat 64 q) (h23 : R 23 = BitVec.ofNat 64 D.L)
    (h24 : R 24 = BitVec.ofNat 64 D.N)
    (h25 : R 25 = BitVec.ofNat 64 (x1.rep.len + x1.rep.scale + (k + s2 - x1.rep.scale)))
    (h26 : R 26 = BitVec.ofNat 64 (x1.rep.len + s2)) (h27 : R 27 = BitVec.ofNat 64 (D.L + 1))
    (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005a50#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => bf.heap.heap.own a h1 h2
  have hn1' := bf.heap.nums x1 hx1
  have hn2' := bf.heap.nums x2 hx2
  have hd1 := hn1'.shape.dig
  have hl1 := hn1'.shape.dsLen
  have hd2 := hn2'.shape.dig
  have hl2 := hn2'.shape.dsLen
  have hs2 := hdv.s2le
  have hzl := hdv.zl
  have hvv : DvVs (dvVs0 x2.rep.ds (x2.rep.len + s2) z0) D.L := by
    rw [hL]; exact dvVs_of hd2 (by omega) hzl hdv.nz
  have hmag : x2.rep.num.mag ≠ 0 := fun h => hdv.nz
    ((dval_eq_zero_iff x2.rep.ds).mp h z0 (by omega))
  have hxl := dvXs0_length x1.rep.ds (k + s2 - x1.rep.scale)
  refine dvs_disp hlive hS (len1 := x1.rep.len + s2) (k := k) (L := D.L) (by omega) (by omega) h21 h23 h26
    (fun R' hge K r12 r20 => ?_) (fun R' hlt K r12 r20 => ?_)
  · have hq := dv_quot hd1 hl1 hl2 hs2 hdv.tz hdv.lz hzl hvv hb hge
    refine dvs_main (len1 := x1.rep.len + s2) (k := k) hlive cx hk
      (by rw [hn, num_div_some k hmag]) bf (dv_shape hd1 hl1 hvv hb hge (by omega))
      (by rw [hb.xs, digBE_length]) (dvXs0_digits hd1 _) (by omega) rfl
      (by rw [hxl]; simp only [dvXs0, dvx_getD]; rw [if_neg (by omega)])
      hvv.len hvv.dig hvv.first hb.xs hb.vs hx hv hsent hoff (by have := hb.kb; omega) hge (by omega)
      (by rw [hq]; rfl) hr0 hn1 hn2 hrs hx1 hx2 hz hzg
      (by rw [K.get 2]; exact h2) (by rw [K.get 8]; rw [hn1]; exact h8) (by rw [K.get 9, hn2]; exact h9)
      r12 (by rw [K.get 16]; exact h16) (by rw [K.get 18]; exact h18) (by rw [K.get 19]; exact h19)
      r20 (by rw [K.get 21]; exact h21) (by rw [K.get 22, hrs]; exact h22) (by rw [K.get 23]; exact h23)
      (by rw [K.get 24]; exact h24) (by rw [K.get 25, hxl]; rw [h25]; exact congrArg _ (by omega))
      (by rw [K.get 26]; exact h26) (by rw [K.get 27]; exact h27) ((K.mono (by decide)).trans hkp)
  · have hq := dv_quot_zero (l1 := x1.rep.len) (sa := x1.rep.scale) (ln2 := x2.rep.len) (k := k)
      (sb := x2.rep.scale) hd1 hl1 hl2 hs2 hdv.tz hdv.lz hzl (by rw [← hL]; exact hvv) (by omega)
    refine dvz_zero hlive cx hk (by rw [hn, num_div_some k hmag]; simp only [NumRep.num, dval_eq_dvalBE] at hq ⊢; rw [hq]; rfl)
      bf hr0 hx1 hx2 hz hzg (by omega) (by omega)
      (by rw [K.get 2]; exact h2) (by rw [K.get 8]; exact h8) (by rw [K.get 9]; exact h9) r12
      (by rw [K.get 18]; exact h18) (by rw [K.get 19]; exact h19) (by rw [K.get 21]; exact h21)
      (by rw [K.get 22]; exact h22) (by rw [K.get 27]; exact h27) ((K.mono (by decide)).trans hkp)

/-- **`bc_divide` from `0x800059d0`** with `num1` in place: `num2`
(`dvn_setup`), then `dv_after` over the normalised buffers. -/
theorem dv_num2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {s2 z0 k : Nat} {b1 : Blk}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S Q R0 Mt0 Fr q sp W n)
    (hn : n = Num.div x1.rep.num x2.rep.num k)
    (hb1 : ∀ D : DvData, D.b1 = b1 → D.P = b1.pay →
      D.xs.length = x1.rep.len + x1.rep.scale + (k + s2 - x1.rep.scale) + 2 →
      DvBuf1 S Mt0 M R0 sp W D H F L0)
    (hdig : ∀ i, i < x1.rep.len + x1.rep.scale + (k + s2 - x1.rep.scale) + 2 → imgM M (b1.pay + i) =
      BitVec.ofNat 8 ((dvXs0 x1.rep.ds (k + s2 - x1.rep.scale)).getD i 0))
    (hx1 : x1 ∈ L0) (hx2 : x2 ∈ L0) (hdv : DvDivisor x2 s2 z0)
    (hl1 : x1.rep.ds.length = x1.rep.len + x1.rep.scale)
    (hl2 : x2.rep.ds.length = x2.rep.len + x2.rep.scale)
    (hsz : x1.rep.len + x1.rep.scale + k + x2.rep.len + x2.rep.scale < 2 ^ 27)
    (hr0 : QSlot Mt0 q L0 Fr) (hz : z ∈ L0)
    (hzg : ldv .ld Mt0 zeroAddr = BitVec.ofNat 64 z.rep.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h18 : R 18 = BitVec.ofNat 64 b1.pay)
    (h19 : R 19 = BitVec.ofNat 64 s2) (h21 : R 21 = BitVec.ofNat 64 k)
    (h22 : R 22 = BitVec.ofNat 64 q)
    (h25 : R 25 = BitVec.ofNat 64 (x1.rep.len + x1.rep.scale + (k + s2 - x1.rep.scale)))
    (h26 : R 26 = BitVec.ofNat 64 (x1.rep.len + s2)) (hkp : Keeps divAll R R0) :
    DW live S Q 0x800059d0#64 R M := by
  let xs0 := dvXs0 x1.rep.ds (k + s2 - x1.rep.scale)
  let vs0 := dvVs0 x2.rep.ds (x2.rep.len + s2) z0
  let L := x2.rep.len + s2 - z0
  let D0 : DvData :=
    { P := b1.pay, N := 0, Bm := 0, off := L - (x1.rep.len + s2), L := L,
      Kb := x1.rep.len + s2 + k - L, xs := digBE (dvalBE xs0 * dvNorm vs0) xs0.length,
      vs := digBE (dvalBE vs0 * dvNorm vs0) L, b1 := b1, b2 := b1, b3 := b1, qv := 0,
      n1p := x1.rep.p, n2p := x2.rep.p, rs := q }
  have hxl : xs0.length = x1.rep.len + x1.rep.scale + (k + s2 - x1.rep.scale) + 2 := by
    rw [dvXs0_length, hl1]
  have bD := hb1 D0 rfl rfl (by simp only [D0]; rw [digBE_length, hxl])
  refine dvn_setup hlive cx.dv bD hx2 hdv.s2le hdv.lz hdv.nz hdv.zl h2 h9 h19 hk.oom
    fun R' M' H' b2 bfs hkb1 hdig2 hsent r24 r23 r16 r27 r19 K => ?_
  have hs2 := hdv.s2le
  have hzl := hdv.zl
  refine dv_after hlive cx hk hn bfs hx1 hx2 hdv ⟨rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
    (fun i hi => (hkb1 _ (bD.pIn i (by simp only [D0]; rw [digBE_length]; exact hi))).trans
      (hdig i (by rw [← hxl]; exact hi)))
    (fun i hi => by
      simp only at hi ⊢
      rw [show b2.pay + z0 + i = b2.pay + (z0 + i) by omega, hdig2 _ (by omega),
        dvVs0_getD (by omega) (by omega)])
    (by simp only; rw [show b2.pay + z0 + (x2.rep.len + s2 - z0) = b2.pay + (x2.rep.len + s2) by omega]
        exact hsent)
    hsz hr0 hz hzg (by rw [K.get 2]; exact h2) (by rw [K.get 8]; exact h8) (by rw [K.get 9]; exact h9)
    r16 (by rw [K.get 18]; exact h18) r19 (by rw [K.get 21]; exact h21) (by rw [K.get 22]; exact h22)
    r23 r24 (by rw [K.get 25]; exact h25) (by rw [K.get 26]; exact h26) r27 ((K.mono (by decide)).trans hkp)

/-- **`bc_divide` from `0x80005954`** (the trimmed scale `s2` in `s3`): `num1`
(`dv1_setup`), then `dv_num2`. -/
theorem dv_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {s2 z0 k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S Q R0 Mt0 Fr q sp W n)
    (hn : n = Num.div x1.rep.num x2.rep.num k) (core : DvCore S Mt0 M R0 sp W H F L0)
    (hx1 : x1 ∈ L0) (hx2 : x2 ∈ L0) (hdv : DvDivisor x2 s2 z0)
    (hsz : x1.rep.len + x1.rep.scale + k + x2.rep.len + x2.rep.scale < 2 ^ 27)
    (hr0 : QSlot Mt0 q L0 Fr) (hz : z ∈ L0)
    (hzg : ldv .ld Mt0 zeroAddr = BitVec.ofNat 64 z.rep.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h19 : R 19 = BitVec.ofNat 64 s2)
    (h21 : R 21 = BitVec.ofNat 64 k) (h22 : R 22 = BitVec.ofNat 64 q) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005954#64 R M := by
  have hl1 := (core.heap.nums x1 hx1).shape.dsLen
  have hl2 := (core.heap.nums x2 hx2).shape.dsLen
  have hs2 := hdv.s2le
  refine dv1_setup hlive cx.dv core hx1 (by omega) h2 h8 h19 h21 hk.oom
    fun R' M' H' b hD hd r18 r25 r26 K => ?_
  exact dv_num2 hlive cx hk hn hD hd hx1 hx2 hdv hl1 hl2 hsz hr0 hz hzg (by rw [K.get 2]; exact h2)
    (by rw [K.get 8]; exact h8) (by rw [K.get 9]; exact h9) r18 (by rw [K.get 19]; exact h19)
    (by rw [K.get 21]; exact h21) (by rw [K.get 22]; exact h22) r25 r26 ((K.mono (by decide)).trans hkp)

/-- `a - 1 + b` as words, the `- 1` wrapping when `a = 0`. -/
theorem pred_add_word {a b : Nat} (h : 1 ≤ a + b) (hb : a + b < 2 ^ 63) :
    BitVec.ofNat 64 a + 18446744073709551615#64 + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b - 1) := by
  rw [show (18446744073709551615#64) = BitVec.ofNat 64 18446744073709551615 from rfl, ofNat_add_ofNat,
    ofNat_add_ofNat, show a + 18446744073709551615 + b = (a + b - 1) + 2 ^ 64 by omega]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.add_mod_right]

/-- **`n2`'s first nonzero digit found** at `0x80005924` (`z0`): the
trailing-zero trim (`dvz_trim`) or, at scale zero, the test for `n2 = 1`
(`hone`, the divide-by-one detour at `0x80005e54`); then `dv_body`. -/
theorem dv_found {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {z0 k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S Q R0 Mt0 Fr q sp W n)
    (hn : n = Num.div x1.rep.num x2.rep.num k) (core : DvCore S Mt0 M R0 sp W H F L0)
    (hx1 : x1 ∈ L0) (hx2 : x2 ∈ L0)
    (hlz : ∀ i, i < z0 → x2.rep.ds.getD i 0 = 0) (hnz : x2.rep.ds.getD z0 0 ≠ 0)
    (hzl : z0 < x2.rep.len + x2.rep.scale)
    (hsz : x1.rep.len + x1.rep.scale + k + x2.rep.len + x2.rep.scale < 2 ^ 27)
    (hr0 : QSlot Mt0 q L0 Fr) (hz : z ∈ L0)
    (hzg : ldv .ld Mt0 zeroAddr = BitVec.ofNat 64 z.rep.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.len)
    (h15 : R 15 = BitVec.ofNat 64 x2.rep.val)
    (h16 : R 16 = BitVec.ofNat 64 (x2.rep.len + x2.rep.scale))
    (h19 : R 19 = BitVec.ofNat 64 x2.rep.scale) (h21 : R 21 = BitVec.ofNat 64 k)
    (h22 : R 22 = BitVec.ofNat 64 q) (hkp : Keeps divAll R R0)
    (hone : ∀ R', x2.rep.len = 1 → x2.rep.scale = 0 → x2.rep.ds.getD 0 0 = 1 →
      R' 2 = BitVec.ofNat 64 (sp - 208) → R' 8 = BitVec.ofNat 64 x1.rep.p →
      R' 9 = BitVec.ofNat 64 x2.rep.p → R' 21 = BitVec.ofNat 64 k → R' 22 = BitVec.ofNat 64 q →
      Keeps divAll R' R0 → DW live S Q 0x80005e54#64 R' M) :
    DW live S Q 0x80005924#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => core.heap.heap.own a h1 h2
  have hn2 := core.heap.nums x2 hx2
  num_facts hn2
  have hd2 : IsDigits x2.rep.ds := hn2.shape.dig
  have hb2 : ∀ j, j < x2.rep.len + x2.rep.scale →
      imgM M (x2.rep.val + j) = BitVec.ofNat 8 (x2.rep.ds.getD j 0) := hn2.digit
  -- `s2 = 0`: straight to `dv_body`
  have hzero : ∀ R', R' 2 = BitVec.ofNat 64 (sp - 208) → R' 8 = BitVec.ofNat 64 x1.rep.p →
      R' 9 = BitVec.ofNat 64 x2.rep.p → R' 19 = 0#64 → R' 21 = BitVec.ofNat 64 k →
      R' 22 = BitVec.ofNat 64 q → Keeps divAll R' R0 → x2.rep.scale = 0 →
      DW live S Q 0x80005954#64 R' M := fun R' r2 r8 r9 r19 r21 r22 kk hs0 =>
    dv_body (s2 := 0) (z0 := z0) hlive cx hk hn core hx1 hx2
      ⟨by omega, fun j h1 h2 => absurd h2 (by omega), hlz, by omega, hnz⟩ hsz hr0 hz hzg r2 r8 r9 r19 r21 r22 kk
  have e1 := ofNat_eq_zero_iff (show x2.rep.scale < 2 ^ 64 by omega)
  bc_run hlive hS [h19, e1] at 0x80005b78 0x80005948
  · intro hs0
    -- scale zero: `n2 = 1`?
    have e2 := ofNat_eq_iff (show x2.rep.len + x2.rep.scale < 2 ^ 64 by omega) (show 1 < 2 ^ 64 by omega)
    bc_run hlive hS [h16, e2] at 0x80005e4c 0x80005b80
    · intro hl1
      have hd0 := hb2 0 (by omega)
      rw [Nat.add_zero] at hd0
      have hl0 := lbu_digit (hd2.getD 0) hd0
      have e3 := ofNat_eq_iff (show x2.rep.ds.getD 0 0 < 2 ^ 64 by have := hd2.getD 0; omega)
        (show 1 < 2 ^ 64 by omega)
      bc_run hlive hS [h15, h16, hl0, e3, hl1] at 0x80005b80 0x80005e54
      · intro h1
        bc_run hlive hS [] at 0x80005954
        exact hzero _ (by bsimp [h2]) (by bsimp [h8]) (by bsimp [h9]) (by bsimp []) (by bsimp [h21])
          (by bsimp [h22]) (by keeps_tac hkp) hs0
      · intro h1
        have h1' : x2.rep.ds.getD 0 0 = 1 := e3.mp (Classical.not_not.mp h1)
        exact hone _ (by omega) hs0 h1' (by bsimp [h2]) (by bsimp [h8]) (by bsimp [h9]) (by bsimp [h21])
          (by bsimp [h22]) (by keeps_tac hkp)
    · intro hl1
      bc_run hlive hS [] at 0x80005954
      exact hzero _ (by bsimp [h2]) (by bsimp [h8]) (by bsimp [h9]) (by bsimp []) (by bsimp [h21])
        (by bsimp [h22]) (by keeps_tac hkp) hs0
  · intro hs0
    have e4 := shl_shr32 (n := x2.rep.scale) (by omega)
    have e5 := pred_add_word (a := x2.rep.len) (b := x2.rep.scale) (by omega) (by omega)
    bc_run hlive hS [h11, h15, h19, e4, e5] at 0x80005948
    refine dvz_trim hlive hS hd2 hb2 (by omega) (by omega) (by omega) ?_ (x2.rep.scale - 1) 0 _ (by omega)
      (fun j h1 h2 => absurd h2 (by omega)) (Keeps.refl _ _) (by bsimp [h19])
      (by bsimp []; try exact congrArg _ (by omega))
    intro R' s2 hs2 htz kk r19
    have hzl2 : z0 < x2.rep.len + s2 := by
      rcases Nat.lt_or_ge z0 (x2.rep.len + s2) with h | h
      · exact h
      · have := htz (z0 - x2.rep.len) (by omega) (by omega)
        rw [show x2.rep.len + (z0 - x2.rep.len) = z0 by omega] at this
        exact absurd this hnz
    exact dv_body (s2 := s2) (z0 := z0) hlive cx hk hn core hx1 hx2 ⟨hs2, htz, hlz, hzl2, hnz⟩ hsz hr0 hz
      hzg (by rw [kk.get 2]; bsimp [h2]) (by rw [kk.get 8]; bsimp [h8]) (by rw [kk.get 9]; bsimp [h9]) r19
      (by rw [kk.get 21]; bsimp [h21]) (by rw [kk.get 22]; bsimp [h22])
      ((kk.mono (by decide)).trans (by keeps_tac hkp))

end

end Dc.Mach
