import Dc.Mach.Bc.KaraShiftSites

/-!
# `_bc_rec_mul`'s Karatsuba step: filling the product

From the new product (all zeros): `m1·B²` and `m1·B` unless `m1` is zero
(`0x80005468`), then `m3·B`, `m3` (`0x80005164`) and `±m2·B`, then the frees.
`B = 10^n`; the values are the handles' (`hdVal`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- The arithmetic of the filled product: the handles' values `a` (`m1`),
`b` (`m2`), `c` (`m3`), `B = 10^n`, the sign flag `sub`. -/
structure KFillVal (a b c B UV L : Nat) (sub : Bool) : Prop where
  bound : a * B * B + a * B + c * B + c < 10 ^ L
  subV : sub = true → a * B * B + a * B + c * B + c = UV + b * B
  addV : sub = false → a * B * B + a * B + c * B + c + b * B = UV
  uv : UV < 10 ^ L

/-- **From `0x80005164`**: `m3·B`, `m3`, `±m2·B` into the product, then the
frees. -/
theorem kara_fill5164 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj} {z : NumObj}
    {u v : NumRep} {y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2 : Hd}
    (km : KMid S M0 M R0 R sp q W n z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 y)
    (hb : BcHeap S M H F (y :: KList [] (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) A B z))
    (hok : HdOK (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2)) (hz : 1 ≤ z.rep.refs)
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0) (hy15 : R 15 = BitVec.ofNat 64 y.rep.p)
    (hP : dvalBE y.rep.ds =
      hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1) * 10 ^ n * 10 ^ n +
      hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1) * 10 ^ n)
    (hfit3 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3).rep ≤
      la + lb + 1)
    (hfit2 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2).rep ≤
      la + lb + 1)
    (hw2 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2).rep.len)
    (hw3 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3).rep.len)
    (hv : KFillVal (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3)) (10 ^ n) (kUV u v la lb)
      (la + lb + 1)
      ((Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hd1).rep.neg !=
        (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hd2).rep.neg)) :
    DW live S Q 0x80005164#64 R M := by
  have hb1 := hv.bound
  refine kshift_80005164 hlive cx km hb hyo hy15 hw3 (by rw [hyl, hys]; omega)
    (by rw [hP, hyl, hys, Nat.add_zero]; omega) fun R2 M2 ds km2 hb2 hv2 => ?_
  refine kshift_80005180 hlive cx km2 hb2 hyo hw3 (by simp only [withDs, hyl, hys]; omega)
    (by simp only [withDs, hyl, hys, Nat.add_zero, Nat.pow_zero, Nat.mul_one]; rw [hv2, hP]; omega) fun R3 M3 ds3 km3 hb3 hv3 => ?_
  simp only [withDs] at hv3
  exact kara_m2 hlive cx hk km3.st hb3 hok hz hyo hyr hyn hyl hys km3.hq km3.tr km3.sl hfit2
    (fun hs => by rw [hv3, hv2, hP]; have := hv.subV hs; simp only [Nat.pow_zero, Nat.mul_one]; omega)
    (fun hs => by rw [hv3, hv2, hP]; have := hv.addV hs; simp only [Nat.pow_zero, Nat.mul_one]; omega)
    hv.uv hw2

/-- **From `0x80005468`** (`m1` not zero, the product all zeros): `m1·B²`,
`m1·B`, then `0x80005164`. -/
theorem kara_fill5468 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj} {z : NumObj}
    {u v : NumRep} {y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2 : Hd}
    (km : KMid S M0 M R0 R sp q W n z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 y)
    (hb : BcHeap S M H F (y :: KList [] (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) A B z))
    (hok : HdOK (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2)) (hz : 1 ≤ z.rep.refs)
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0) (hy10 : R 10 = BitVec.ofNat 64 y.rep.p)
    (hP : dvalBE y.rep.ds = 0)
    (hfit1 : 2 * n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1).rep ≤
      la + lb + 1)
    (hfit3 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3).rep ≤
      la + lb + 1)
    (hfit2 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2).rep ≤
      la + lb + 1)
    (hw1 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1).rep.len)
    (hw2 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2).rep.len)
    (hw3 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3).rep.len)
    (hv : KFillVal (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3)) (10 ^ n) (kUV u v la lb)
      (la + lb + 1)
      ((Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hd1).rep.neg !=
        (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hd2).rep.neg)) :
    DW live S Q 0x80005468#64 R M := by
  have hb1 := hv.bound
  have hBB : 10 ^ (2 * n) = 10 ^ n * 10 ^ n := by rw [← Nat.pow_add]; congr 1; omega
  refine kshift_80005468 hlive cx km hb hyo hy10 hw1 (by rw [hyl, hys]; omega)
    (by rw [hP, hyl, hys, Nat.add_zero, hBB, ← Nat.mul_assoc]; omega)
    fun R2 M2 ds km2 hb2 hv2 => ?_
  refine kshift_80005480 hlive cx km2 hb2 hyo hw1 (by simp only [withDs, hyl, hys]; omega)
    (by simp only [withDs, hyl, hys, Nat.add_zero]; rw [hv2, hP, hBB, ← Nat.mul_assoc]; omega)
    fun R3 M3 ds3 km3 hb3 hv3 => ?_
  simp only [withDs] at hv3
  have hsf := km3.st.rm
  have hqs := cx.slot
  have q2 := hqs.hi; have q3 := hqs.lo; have q4 := hqs.al
  have hS : HeapOwn S := fun a h1 h2 => hb3.heap.own a h1 h2
  have hyp : y.rep.p = y.sb.pay := (hb.blocks y List.mem_cons_self).sPay
  have hq := km3.hq
  simp only [withDs] at hq
  have h9 := km3.tr.q
  bc_run hlive hS [h9, hq] at 0x80005164
  all_goals first | exact hqs.acc | (simp only [LdOK, tohostAddr] at *; omega) | skip
  have h15 : upd R3 15 (BitVec.ofNat 64 y.sb.pay) 15 =
      BitVec.ofNat 64 (withDs (withDs y ds) ds3).rep.p := by
    simp only [withDs]; bsimp [hyp]
  exact kara_fill5164 (R := upd R3 15 (BitVec.ofNat 64 y.sb.pay)) hlive cx hk ((km3.st.rm.keeps (by keeps_tac Keeps.refl _ _) (by bsimp [])) |>
      fun r => ⟨⟨r, km3.st.saved2⟩, km3.tr.keeps (ks := [15]) (by keeps_tac Keeps.refl _ _),
        km3.sl, km3.hq⟩)
    hb3 hok hz hyo hyr hyn hyl hys h15
    (by rw [hv3, hv2, hP, hBB, ← Nat.mul_assoc]; omega) hfit3 hfit2 hw2 hw3 hv

end Dc.Mach
