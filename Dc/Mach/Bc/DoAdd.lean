import Dc.Mach.Bc.NumStore
import Dc.Mach.Bc.Scan
import Dc.BcModel.Steps
import Dc.BcModel.Add

/-!
# `_bc_do_add` (`lib/number.c`)

```
80004304 S = max s1 s2 (s0) ; D = max l1 l2 + 1 (s3) ; save s0-s3, ra ; smin at sp+8
80004364 bc_new_num (D, max S smin)
8000436c smin > S: zero the scale_min tail (already zero)
80004398 n1ptr (a1), n2ptr (a7), sumptr (a6) at their last digits
800043d8 s1 > s2: copy n1's extra fraction digits (80004400)
         s2 > s1: copy n2's extra fraction digits (80004564)
80004430 c1 = l1 + min s (a4), c2 = l2 + min s (a3), carry = 0 (a2)
80004450 add loop while c1 > 0 and c2 > 0
80004498 carry loop over the longer operand (800044a8)
800044f0 final carry into digit 0
80004500 _bc_rm_leading_zeros (inlined) ; 80004534 restore, ret
```

The result's digits from the last one down are the little-endian sum
`addLE xs ys 0` of the aligned operands (`Dc/BcModel/Steps.lean`): after
`k` positions the result object holds `sumDs (N + 1) k r Z`, and the carry
register holds `carryAt xs ys 0 k`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-! ## Machine-free helpers -/

/-- Leaving a function: the saved registers back, every other register in
`all` outside `clob`. -/
theorem Keeps.unwind {all clob saved : List Nat} {R' R R0 : Nat → BitVec 64}
    (hs : ∀ z ∈ saved, R' z = R0 z) (hcov : ∀ z ∈ all, z ∈ clob ∨ z ∈ saved := by decide)
    (hk : Keeps all R' R) (hkp : Keeps all R R0) : Keeps clob R' R0 := fun z hz => by
  by_cases ha : z ∈ all
  · rcases hcov z ha with h | h
    · exact absurd h hz
    · exact hs z h
  · exact (hk z ha).trans (hkp z ha)

theorem reverse_getD (ds : List Nat) {j : Nat} (hj : j < ds.length) :
    ds.reverse.getD j 0 = ds.getD (ds.length - 1 - j) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_reverse hj]

theorem ext_sext32 (x : BitVec 32) : BitVec.extractLsb 31 0 (BitVec.signExtend 64 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : i < 32 := by omega
  simp [BitVec.getLsbD_signExtend, h1]
  omega

theorem sext_of32 {x : BitVec 32} {k : Nat} (h : x.toNat = k) (hk : k < 2 ^ 31) :
    BitVec.signExtend 64 x = BitVec.ofNat 64 k := by
  subst h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  have : x.msb = false := by rw [BitVec.msb_eq_decide]; simp; omega
  simp [this]

theorem toNat_ext32 (n : Nat) : (BitVec.extractLsb 31 0 (BitVec.ofNat 64 n)).toNat = n % 2 ^ 32 := by
  simp

/-- `sub` of two words. -/
theorem sub_ofNat {a b : Nat} (h : b ≤ a) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) :=
  BitVec.ofNat_sub_ofNat_of_le a b hb h

theorem se12_ff6 : sign_extend (m := 64) (0xff6#12) = 18446744073709551606#64 := by decide

/-- `addi r, r, -10` on a word of at least 10. -/
theorem word_sub10 {k : Nat} (h : 10 ≤ k) :
    BitVec.ofNat 64 k + 18446744073709551606#64 = BitVec.ofNat 64 (k - 10) := by
  change BitVec.ofNat 64 k + -(10#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le k 10 (by decide) h

/-- The carry loop's count `(a7 + 1) + (c - 1) - a1` in 32-bit words. -/
theorem carry_count {A j c : Nat} (hj : j < c) (hjA : j + 1 ≤ A) (hA : A < 2 ^ 64) (hc : c < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (A - j - 1 + 1)))) +
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 (c - 1)))) - BitVec.extractLsb 31 0 (BitVec.ofNat 64 A)) =
    BitVec.ofNat 64 (c - 1 - j) := by
  rw [ext_sext32, ext_sext32]
  apply sext_of32 _ (by omega)
  rw [BitVec.toNat_sub, BitVec.toNat_add, toNat_ext32, toNat_ext32, toNat_ext32]
  omega

theorem and255_ofNat {k : Nat} (h : k < 256) : BitVec.ofNat 64 k &&& 255#64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and255, BitVec.toNat_ofNat]; omega

theorem sbData_ofNat (d : Nat) : sbData (BitVec.ofNat 64 d) = BitVec.ofNat 8 d := by
  rw [sbData_eq]
  apply BitVec.eq_of_toNat_eq
  simp [lo8]

/-- The number of leading zeros, from where the scan stops. -/
theorem lzCount_eq : ∀ (n : Nat) (ds : List Nat) (j : Nat), j ≤ n → n < ds.length →
    (∀ i, i < j → ds.getD i 0 = 0) → (j = n ∨ ds.getD j 0 ≠ 0) → lzCount n ds = j
  | 0, _, j, hj, _, _, _ => by simp only [lzCount] <;> omega
  | _ + 1, [], _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, d :: ds, j, hj, hl, hz, hs => by
    simp only [lzCount]
    cases j with
    | zero =>
      rcases hs with h | h
      · omega
      · simp only [List.getD_cons_zero] at h; simp [h]
    | succ j =>
      have h0 : d = 0 := by simpa using hz 0 (by omega)
      simp only [h0, if_true]
      rw [lzCount_eq n ds j (by omega) (by simp only [List.length_cons] at hl; omega)
        (fun i hi => by simpa using hz (i + 1) (by omega))
        (by rcases hs with h | h
            · exact .inl (by omega)
            · exact .inr (by simpa using h))]

/-! ## The model, position by position -/

/-- Digit `k` of an aligned operand inside its digits. -/
theorem padLE_getD_in {ds : List Nat} {l sc s m k : Nat} (hl : ds.length = l + sc) (hs : sc ≤ s)
    (h1 : s - sc ≤ k) (h2 : k < l + s) :
    (padLE ds sc s m).getD k 0 = ds.getD (l + s - 1 - k) 0 := by
  rw [padLE_getD, if_neg (by omega), reverse_getD _ (by omega), hl]
  congr 1; omega

/-- Digit `k` of an aligned operand outside its digits. -/
theorem padLE_getD_out {ds : List Nat} {l sc s m k : Nat} (hl : ds.length = l + sc) (hs : sc ≤ s)
    (h : k < s - sc ∨ l + s ≤ k) : (padLE ds sc s m).getD k 0 = 0 := by
  rw [padLE_getD]
  split
  · rfl
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]
    rfl

/-- The carry stays zero while one operand is zero at every position. -/
theorem carryAt_eq_zero {xs ys : List Nat} (hl : xs.length = ys.length) (hx : IsDigits xs)
    (hy : IsDigits ys) : ∀ k, k ≤ xs.length → (∀ j, j < k → xs.getD j 0 = 0 ∨ ys.getD j 0 = 0) →
      carryAt xs ys 0 k = 0
  | 0, _, _ => carryAt_zero _ _ _
  | k + 1, hk, h => by
    rw [carryAt_succ _ _ _ _ hl (by omega), carryAt_eq_zero hl hx hy k (by omega)
      fun j hj => h j (by omega)]
    have d1 : xs.getD k 0 < 10 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact hx _ (List.getElem_mem _)
    have d2 : ys.getD k 0 < 10 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact hy _ (List.getElem_mem _)
    rcases h k (by omega) with e | e <;> omega

/-- The aligned first operand of `_bc_do_add` (little-endian). -/
abbrev addXs (a b : NumRep) : List Nat := opLE a.ds a.scale a.len a.scale b.len b.scale
/-- The aligned second operand. -/
abbrev addYs (a b : NumRep) : List Nat := opLE b.ds b.scale a.len a.scale b.len b.scale
/-- The positions the loops cover: `max l1 l2 + max s1 s2`. -/
abbrev addN (a b : NumRep) : Nat := loopLen a.len a.scale b.len b.scale
/-- The little-endian sum. -/
abbrev addR (a b : NumRep) : List Nat := addLE (addXs a b) (addYs a b) 0
/-- The `scale_min` zero tail. -/
abbrev addZ (a b : NumRep) (smin : Nat) : List Nat := List.replicate (smin - max a.scale b.scale) 0
/-- The result's digits after `k` positions. -/
abbrev addDs (a b : NumRep) (smin k : Nat) : List Nat := sumDs (addN a b + 1) k (addR a b) (addZ a b smin)
/-- The carry into position `k`. -/
abbrev addC (a b : NumRep) (k : Nat) : Nat := carryAt (addXs a b) (addYs a b) 0 k

/-- The lengths and digits of the operands and the sum. -/
structure AddModel (a b : NumRep) : Prop where
  xl : (addXs a b).length = addN a b
  yl : (addYs a b).length = addN a b
  rl : (addR a b).length = addN a b + 1
  xd : IsDigits (addXs a b)
  yd : IsDigits (addYs a b)
  rd : IsDigits (addR a b)

theorem addModel {a b : NumRep} (ha : NumShape a) (hb : NumShape b) : AddModel a b := by
  have xl := opLE_length ha.dsLen a.len a.scale b.len b.scale (by omega) (by omega)
  have yl := opLE_length hb.dsLen a.len a.scale b.len b.scale (by omega) (by omega)
  have xd := padLE_digits ha.dig a.scale (loopScale a.scale b.scale) (addN a b)
  have yd := padLE_digits hb.dig b.scale (loopScale a.scale b.scale) (addN a b)
  exact ⟨xl, yl, by rw [addLE_length _ _ _ (by rw [xl, yl]), xl], xd, yd,
    addLE_digits _ _ _ xd yd (by decide) (by rw [xl, yl])⟩

theorem AddModel.getD_lt_r {a b : NumRep} (h : AddModel a b) (k : Nat) : (addR a b).getD k 0 < 10 := by
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge k (addR a b).length with hk | hk
  · rw [List.getElem?_eq_getElem hk]; exact h.rd _ (List.getElem_mem _)
  · rw [List.getElem?_eq_none hk]; decide

theorem AddModel.carry_le {a b : NumRep} (h : AddModel a b) (k : Nat) : addC a b k ≤ 1 :=
  carryAt_le _ _ _ _ h.xd h.yd (by decide)

/-- One position: the digit written and the carry out. -/
theorem AddModel.step {a b : NumRep} (h : AddModel a b) {k : Nat} (hk : k < addN a b) :
    (addR a b).getD k 0 = ((addXs a b).getD k 0 + (addYs a b).getD k 0 + addC a b k) % 10 ∧
      addC a b (k + 1) = ((addXs a b).getD k 0 + (addYs a b).getD k 0 + addC a b k) / 10 :=
  ⟨addLE_getD _ _ _ _ (by rw [h.xl, h.yl]) (by rw [h.xl]; exact hk),
    carryAt_succ _ _ _ _ (by rw [h.xl, h.yl]) (by rw [h.xl]; exact hk)⟩

/-- The final carry is the sum's top digit. -/
theorem AddModel.last {a b : NumRep} (h : AddModel a b) :
    (addR a b).getD (addN a b) 0 = addC a b (addN a b) := by
  have := addLE_getD_last (addXs a b) (addYs a b) 0 (by rw [h.xl, h.yl])
  rwa [h.xl] at this

/-- The first operand's digit at position `k`. -/
theorem addXs_in {a b : NumRep} (ha : NumShape a) {k : Nat}
    (h1 : max a.scale b.scale - a.scale ≤ k) (h2 : k < a.len + max a.scale b.scale) :
    (addXs a b).getD k 0 = a.ds.getD (a.len + max a.scale b.scale - 1 - k) 0 :=
  padLE_getD_in ha.dsLen (by simp only [loopScale]; omega) (by simp only [loopScale]; omega)
    (by simp only [loopScale]; omega)

theorem addXs_out {a b : NumRep} (ha : NumShape a) {k : Nat}
    (h : k < max a.scale b.scale - a.scale ∨ a.len + max a.scale b.scale ≤ k) :
    (addXs a b).getD k 0 = 0 :=
  padLE_getD_out ha.dsLen (by simp only [loopScale]; omega) (by simp only [loopScale]; omega)

theorem addYs_in {a b : NumRep} (hb : NumShape b) {k : Nat}
    (h1 : max a.scale b.scale - b.scale ≤ k) (h2 : k < b.len + max a.scale b.scale) :
    (addYs a b).getD k 0 = b.ds.getD (b.len + max a.scale b.scale - 1 - k) 0 :=
  padLE_getD_in hb.dsLen (by simp only [loopScale]; omega) (by simp only [loopScale]; omega)
    (by simp only [loopScale]; omega)

theorem addYs_out {a b : NumRep} (hb : NumShape b) {k : Nat}
    (h : k < max a.scale b.scale - b.scale ∨ b.len + max a.scale b.scale ≤ k) :
    (addYs a b).getD k 0 = 0 :=
  padLE_getD_out hb.dsLen (by simp only [loopScale]; omega) (by simp only [loopScale]; omega)

/-- The result `bc_new_num` hands over is the sum before any position. -/
theorem addDs_zero (a b : NumRep) (smin : Nat) :
    List.replicate (max a.len b.len + 1 + max smin (max a.scale b.scale)) 0 = addDs a b smin 0 := by
  simp only [addDs, addZ]
  rw [sumDs_zero, List.replicate_append_replicate]
  congr 1; simp only [addN, loopLen]; omega

/-- After every position the result is `_bc_do_add`'s digit array. -/
theorem addDs_full {a b : NumRep} (h : AddModel a b) (smin : Nat) :
    addDs a b smin (addN a b + 1) = addDigits a.len a.scale a.ds b.len b.scale b.ds smin :=
  sumDs_full h.rl

theorem addDs_length {a b : NumRep} (h : AddModel a b) (smin : Nat) {k : Nat} (hk : k ≤ addN a b + 1) :
    (addDs a b smin k).length = max a.len b.len + 1 + max smin (max a.scale b.scale) := by
  rw [sumDs_length hk (by rw [h.rl]; exact hk)]
  simp only [addN, loopLen, addZ, List.length_replicate]; omega

/-- One position written into the result object: digit `k` of the sum at
index `N - k`. -/
theorem add_store {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {a b : NumRep} {smin k : Nat} (h : AddModel a b)
    (hyl : y.rep.len + y.rep.scale = max a.len b.len + 1 + max smin (max a.scale b.scale))
    (hb : BcHeap S M H F (withDs y (addDs a b smin k) :: L)) (hk : k < addN a b + 1)
    {v : BitVec 64} (hv : sbData v = BitVec.ofNat 8 ((addR a b).getD k 0)) :
    BcHeap S (writeLog M [(y.rep.val + (addN a b - k), 1, v)]) H F
      (withDs y (addDs a b smin (k + 1)) :: L) := by
  have hst := BcHeap.setDigit (L1 := []) hb (i := addN a b - k) (d := (addR a b).getD k 0)
    (by simp only [withDs, addN, loopLen] at hyl ⊢; omega) (h.getD_lt_r k) hv
  simp only [withDs, List.nil_append] at hst ⊢
  rw [show addN a b - k = addN a b + 1 - 1 - k by omega, sumDs_step hk (by rw [h.rl]; exact hk)] at hst
  exact hst

/-! ## Advancing `n_value` past a leading zero -/

/-- `n_len` lowered and `n_value` advanced by one (`_bc_rm_leading_zeros`). -/
theorem NumAt.advance {Mt : Mem} {o : NumRep} (h : NumAt Mt o) (hl : 2 ≤ o.len) {v1 v2 : BitVec 64}
    (h1 : v1.toNat % 2 ^ 32 = o.len - 1) (h2 : v2 = BitVec.ofNat 64 (o.val + 1)) :
    NumAt (writeLog (writeLog Mt [(o.p + 4, 4, v1)]) [(o.p + 32, 8, v2)]) (o.drop 1) := by
  have hs := h.shape
  have hsep := hs.sep; have hpl := hs.ptrLe; have hvh := hs.vHi; have hsz := hs.size
  have hshape : NumShape (o.drop 1) :=
    { hs with
      dsLen := by simp only [NumRep.drop, List.length_drop, hs.dsLen]; omega
      dig := fun e he => hs.dig e (List.mem_of_mem_drop he)
      lenPos := by simp only [NumRep.drop]; omega
      size := by simp only [NumRep.drop]; omega
      ptrLe := by simp only [NumRep.drop]; omega
      vHi := by simp only [NumRep.drop]; omega
      sep := by simp only [NumRep.drop]; omega }
  refine ⟨hshape, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [ldv_store_miss .lw _ _ (by simp only [NumRep.drop, widthOfM]; omega),
      ldv_store_miss .lw _ _ (by simp only [NumRep.drop, widthOfM]; omega)]; exact h.sign
  · rw [ldv_store_miss .lw _ _ (by simp only [NumRep.drop, widthOfM]; omega)]
    exact ldv_lw_hitN _ rfl (k := o.len - 1) h1 (by omega)
  · rw [ldv_store_miss .lw _ _ (by simp only [NumRep.drop, widthOfM]; omega),
      ldv_store_miss .lw _ _ (by simp only [NumRep.drop, widthOfM]; omega)]; exact h.scale
  · rw [ldv_store_miss .lw _ _ (by simp only [NumRep.drop, widthOfM]; omega),
      ldv_store_miss .lw _ _ (by simp only [NumRep.drop, widthOfM]; omega)]; exact h.refs
  · rw [ldv_store_miss .ld _ _ (by simp only [NumRep.drop, widthOfM]; omega),
      ldv_store_miss .ld _ _ (by simp only [NumRep.drop, widthOfM]; omega)]; exact h.ptr
  · show ldv .ld _ (o.p + 32) = _
    rw [ldv_store_hit, h2]; rfl
  · simp only [NumRep.drop] at hi ⊢
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      show o.val + 1 + i = o.val + (i + 1) by omega, h.digit (i + 1) (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [Nat.add_comm 1 i]

/-- The object `x` with `n_value` advanced past a leading zero. -/
theorem BcHeap.advance {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (x :: L)) (hl : 2 ≤ x.rep.len)
    {v1 v2 : BitVec 64} (h1 : v1.toNat % 2 ^ 32 = x.rep.len - 1)
    (h2 : v2 = BitVec.ofNat 64 (x.rep.val + 1)) :
    BcHeap S (writeLog (writeLog Mt [(x.rep.p + 4, 4, v1)]) [(x.rep.p + 32, 8, v2)]) H F
      ({ x with rep := x.rep.drop 1 } :: L) := by
  have h' : BcHeap S Mt H F ([] ++ x :: L) := h
  have hx : x ∈ x :: L := List.mem_cons_self
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  have hi' := h.heap
  have hsp := hxb.sPay; have hsz := hxb.sSz; have hdf := hxb.dFit
  have hfin : x.sb.fin = x.sb.pay + x.sb.sz := rfl
  have hin : ∀ a, x.rep.p + 4 ≤ a ∧ a < x.rep.p + 40 → x.sb.In a := fun a ha => ⟨by omega, by omega⟩
  have hsep := hn.shape.sep; have hpl := hn.shape.ptrLe
  refine BcHeap.update h' rfl rfl ⟨hxb.sLive, hxb.dLive, hxb.sPay, hxb.sSz, hxb.dPay, by
      simp only [NumRep.drop]; omega⟩
    (hn.advance hl h1 h2) (P := fun a => x.rep.p + 4 ≤ a ∧ a < x.rep.p + 40)
    (fun a ha => by
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]) fun a ha => ?_
  have hsa := hin a ha
  have hhp := live_in_heap hi' hxb.sLive hsa
  refine ⟨live_not_alloc hi' hxb.sLive hsa, ?_, fun b hb hba => ?_⟩
  · simp only [bcFreeBytes, bcFreeAddr, heapStart] at *; omega
  · have sf := SplitFacts.of_nodup (L1 := []) h.distinct
    rcases List.mem_append.mp hb with hb | hb
    · exact live_apart hi' (h.deadLive b hb).1 hxb.sLive (fun e' => sf.sF (e' ▸ hb)) hba hsa
    · obtain ⟨y, hy, hby⟩ := List.mem_flatMap.mp hb
      have ⟨n1, _, n3, _⟩ := sf.other hy
      have hyb := h.blocks y (mem_split (L1 := []) hy)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hby
      rcases hby with rfl | rfl
      · exact live_apart hi' hyb.sLive hxb.sLive n1 hba hsa
      · exact live_apart hi' hyb.dLive hxb.sLive n3 hba hsa

theorem NumRep.drop_zero (o : NumRep) : o.drop 0 = o := by
  cases o; simp [NumRep.drop]

theorem NumRep.drop_drop (o : NumRep) (j : Nat) : (o.drop j).drop 1 = o.drop (j + 1) := by
  simp only [NumRep.drop, List.drop_drop]
  congr 1 <;> omega

/-! ## Frame, context, and result -/

/-- `_bc_do_add`'s saved registers in its 64-byte frame: `s3`, `ra`, `s2`,
`s1`, `s0` (offsets from the lowered `sp`). -/
abbrev addSlots : List (Nat × Nat) := [(19, 24), (1, 56), (18, 32), (9, 40), (8, 48)]

/-- The registers `_bc_do_add` may change. -/
abbrev addClob : List Nat := [6, 10, 11, 12, 13, 14, 15, 16, 17, 28]

/-- The registers changed inside `_bc_do_add` before its epilogue. -/
abbrev addAll : List Nat := [1, 2, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 28]

/-- The scratch registers of `_bc_do_add`'s loops. -/
abbrev addTmp : List Nat := [6, 8, 11, 12, 13, 14, 15, 16, 17, 19, 28]

/-- `_bc_do_add`'s fixed context: its 64-byte frame and `bc_new_num`'s 32
bytes below, above the heap; the entry's `sp` and return address. -/
structure AddCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp : Nat) : Prop where
  frame : StackFrame S sp 96
  above : heapEnd + 96 ≤ sp
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0

/-- The operands: two numbers of the heap (possibly the same), `scale_min`,
and the result's size in range. -/
structure AddArgs (L : List NumObj) (x1 x2 : NumObj) (smin : Nat) : Prop where
  m1 : x1 ∈ L
  m2 : x2 ∈ L
  size : max x1.rep.len x2.rep.len + 1 + max smin (max x1.rep.scale x2.rep.scale) < 2 ^ 31

/-- `_bc_do_add`'s result: the new number `y` (positive, normalized, one
reference) holding `_bc_do_add`'s digit array heads the heap; off the heap
only the stack window changed. -/
structure AddPost (S : Nat → Prop) (Mt0 Mt : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (a b : NumRep) (smin sp : Nat) (y : NumObj) : Prop where
  heap : BcHeap S Mt H F (y :: L)
  num : y.rep.num = ⟨false, dval (addDigits a.len a.scale a.ds b.len b.scale b.ds smin),
    resScale a.scale b.scale smin⟩
  norm : y.rep.Norm
  refs : y.rep.refs = 1
  out : ∀ a, OutHeap a → ¬ frameIn sp 96 a → imgM Mt a = imgM Mt0 a

/-- `_bc_do_add`'s continuations: the result, or `out_of_memory`. -/
structure AddK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (L : List NumObj) (a b : NumRep) (smin sp : Nat) : Prop where
  ret : ∀ R' Mt' H F y, Keeps addClob R' R0 → R' 10 = BitVec.ofNat 64 y.sb.pay →
    AddPost S Mt0 Mt' H F L a b smin sp y → DW live S Q (R0 1) R' Mt'
  oom : ∀ R' Mt', R' 2 = BitVec.ofNat 64 (sp - 96) →
    (∀ a, OutHeap a → ¬ frameIn sp 96 a → imgM Mt' a = imgM Mt0 a) →
    DW live S Q 0x80002bcc#64 R' Mt'

/-- Inside `_bc_do_add` after `bc_new_num`: `sp` lowered by 64, the saved
registers in the frame, `s2 = n1`, `s1 = n2`, `a0` the result's struct `p`,
and off the heap only the stack window changed. -/
structure AddAt (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp : Nat)
    (x1 x2 : NumObj) (p : Nat) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 64)
  saved : SavedWords M (sp - 64) addSlots R0
  r18 : R 18 = BitVec.ofNat 64 x1.rep.p
  r9 : R 9 = BitVec.ofNat 64 x2.rep.p
  r10 : R 10 = BitVec.ofNat 64 p
  regs : Keeps addAll R R0
  out : ∀ a, OutHeap a → ¬ frameIn sp 96 a → imgM M a = imgM Mt0 a

/-- `AddAt` through writes inside the heap. -/
theorem AddAt.heap {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp : Nat}
    {x1 x2 : NumObj} {p : Nat} (st : AddAt S Mt0 M R0 R sp x1 x2 p) (cx : AddCtx S R0 sp)
    (hag : ∀ a, OutHeap a → imgM M' a = imgM M a) : AddAt S Mt0 M' R0 R sp x1 x2 p := by
  have hab := cx.above
  simp only [heapEnd] at hab
  exact
    { st with
      saved := st.saved.transport (lo := 24) (top := 64) (hag := fun a h1 h2 => hag a (by
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega))
      out := fun a ha hf => (hag a ha).trans (st.out a ha hf) }

/-- `AddAt` through changes of the loops' scratch registers. -/
theorem AddAt.keeps {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp : Nat}
    {x1 x2 : NumObj} {p : Nat} (st : AddAt S Mt0 M R0 R sp x1 x2 p) (hk : Keeps addTmp R' R) :
    AddAt S Mt0 M R0 R' sp x1 x2 p :=
  { st with
    r2 := by rw [hk.get 2]; exact st.r2
    r18 := by rw [hk.get 18]; exact st.r18
    r9 := by rw [hk.get 9]; exact st.r9
    r10 := by rw [hk.get 10]; exact st.r10
    regs := (hk.mono (by decide)).trans st.regs }

/-- The epilogue at `0x80004534`: the saved registers back, `sp` up. -/
theorem add_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hp : AddPost S Mt0 M H F L x1.rep x2.rep smin sp y) :
    DW live S Q 0x80004534#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hp.heap.heap.own a h1 h2
  have e1 := st.saved.get 1 56
  have e8 := st.saved.get 8 48
  have e9 := st.saved.get 9 40
  have e18 := st.saved.get 18 32
  have e19 := st.saved.get 19 24
  have h2 := st.r2
  have h10 := st.r10
  have hal := cx.al
  bc_run hlive hS [h2, e1, e8, e9, e18, e19]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk.ret _ _ H F y (Keeps.unwind (saved := [1, 2, 8, 9, 18, 19]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := st.regs)) (by bsimp [h10]) hp
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0]
  congr 1; omega

/-- The result before `_bc_rm_leading_zeros`: positive, one reference,
`_bc_do_add`'s digit array at the result scale. -/
structure AddFinal (o a b : NumRep) (smin : Nat) : Prop where
  neg : o.neg = false
  refs : o.refs = 1
  ds : o.ds = addDigits a.len a.scale a.ds b.len b.scale b.ds smin
  scale : o.scale = resScale a.scale b.scale smin
  dsLen : o.ds.length = o.len + o.scale
  lenPos : 1 ≤ o.len

/-- Leading zeros removed: the result. -/
theorem add_done {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {o : NumRep} {j : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay) (hf : AddFinal o x1.rep x2.rep smin)
    (hj : lzCount (o.len - 1) o.ds = j) (hb : BcHeap S M H F ({ y with rep := o.drop j } :: L)) :
    DW live S Q 0x80004534#64 R M := by
  obtain ⟨hnum, hnorm, -, -⟩ := NumRep.rmLeadingZeros_spec hf.dsLen hf.lenPos
  have e : o.rmLeadingZeros = o.drop j := by rw [NumRep.rmLeadingZeros, hj]
  rw [e] at hnum hnorm
  refine add_epi hlive cx hk (y := { y with rep := o.drop j }) st ⟨hb, ?_, hnorm, hf.refs, st.out⟩
  show (o.drop j).num = _
  rw [hnum, NumRep.num, hf.neg, hf.ds, hf.scale]

/-- `_bc_rm_leading_zeros`' loop at `0x8000452c`: `j` leading zeros
dropped (`n_value = val + j`, `n_len = len - j`), digit `j` zero too. -/
theorem add_rmlz_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {o : NumRep}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hf : AddFinal o x1.rep x2.rep smin) (hp : o.p = y.sb.pay) :
    ∀ n j (R : Nat → BitVec 64) (M : Mem), o.len - 1 - j = n → j < o.len →
      AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F ({ y with rep := o.drop j } :: L) →
      R 15 = BitVec.ofNat 64 (o.val + j) → R 14 = BitVec.ofNat 64 (o.len - j) →
      R 12 = BitVec.ofNat 64 1 → (∀ i, i ≤ j → o.ds.getD i 0 = 0) →
      DW live S Q 0x8000452c#64 R M := by
  have hsf := cx.frame
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro n
  induction n with
  | zero =>
    intro j R M hn hj st hb h15 h14 h12 hz
    have hn0 := hb.nums _ List.mem_cons_self
    have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
    num_facts hn0
    have v5 := hn0.shape.vHi; have v7 := hn0.shape.size; have v8 := hn0.shape.lenPos
    have v9 := hn0.shape.vLo; have v6 := hn0.shape.ptrLe
    simp only [NumRep.drop, heapEnd, heapStart] at v5 v7 v8 v9 v6
    bc_run hlive hS [h15, h14, h12, toInt_ofNat_small] at 0x80004534
    · intro hc; exfalso; (try simp (disch := omega) only [toInt_ofNat_small] at hc); omega
    · intro _
      exact add_done hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hf
        (lzCount_eq _ _ _ (by omega) (by rw [hf.dsLen]; omega) (fun i hi => hz i (by omega))
          (.inl (by omega))) hb
  | succ n ih =>
    intro j R M hn hj st hb h15 h14 h12 hz
    have hn0 := hb.nums _ List.mem_cons_self
    have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
    num_facts hn0
    have v5 := hn0.shape.vHi; have v7 := hn0.shape.size; have v8 := hn0.shape.lenPos
    have v9 := hn0.shape.vLo; have v6 := hn0.shape.ptrLe
    simp only [NumRep.drop, heapEnd, heapStart] at v5 v7 v8 v9 v6
    have hr10 := st.r10
    bc_run hlive hS [h15, h14, h12, hr10, toInt_ofNat_small] at 0x80004534 0x80004524
    · intro hc
      have hb' := BcHeap.advance hb (v1 := BitVec.ofNat 64 (o.len - j - 1))
        (v2 := BitVec.ofNat 64 (o.val + j + 1)) (by simp only [NumRep.drop]; omega)
        (by simp only [NumRep.drop]; rw [toNat_ofNat_mod32 (by omega)]) (by simp only [NumRep.drop])
      simp only [NumRep.drop_drop] at hb'
      have hp' : (o.drop j).p = y.sb.pay := hp
      rw [hp'] at hb'
      have hn1 := hb'.nums _ List.mem_cons_self
      have hl1 := hn1.lbu (i := 0) (by simp only [NumRep.drop]; omega)
      simp only [NumRep.drop, Nat.add_zero, List.getD_eq_getElem?_getD, List.getElem?_drop,
        ← Nat.add_assoc] at hl1
      bc_run hlive hS [h15, h14, h12, hr10, hl1] at 0x80004524
      have st' := (st.heap cx (M' := writeLog (writeLog M [(y.sb.pay + 4, 4,
        BitVec.ofNat 64 (o.len - j - 1))]) [(y.sb.pay + 32, 8, BitVec.ofNat 64 (o.val + j + 1))])
        fun a ha => by
          have := hn0.shape.pLo; have := hn0.shape.pHi
          simp only [NumRep.drop, OutHeap, heapStart, heapEnd] at *
          rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)])
      have hd := hn1.getD_lt 0
      simp only [NumRep.drop, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero] at hd
      bc_run hlive hS [h12, hl1] at 0x8000452c 0x80004534
      · intro hne
        bv_nat at hne
        rw [Nat.mod_eq_of_lt (by omega)] at hne
        exact add_done hlive cx hk (st'.keeps (by keeps_tac Keeps.refl _ _)) hf
          (lzCount_eq _ _ _ (by omega) (by rw [hf.dsLen]; omega) (fun i hi => hz i (by omega))
            (.inr (by rw [List.getD_eq_getElem?_getD]; exact hne))) hb'
      · intro he
        bv_nat at he
        rw [Classical.not_not, Nat.mod_eq_of_lt (by omega)] at he
        refine ih (j + 1) _ _ (by omega) (by omega) (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
          (by bsimp [Nat.add_assoc]) (by bsimp [Nat.sub_sub]) (by bsimp [h12]) fun i hi => ?_
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hz i (by omega)
        · rw [show i = j + 1 by omega, List.getD_eq_getElem?_getD]; exact he
    · intro _
      exact add_done hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hf
        (lzCount_eq _ _ _ (by omega) (by rw [hf.dsLen]; omega) (fun i hi => hz i (by omega))
          (.inl (by omega))) hb

/-- `_bc_rm_leading_zeros` inlined at `0x80004500`. -/
theorem add_rmlz {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {o : NumRep}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hf : AddFinal o x1.rep x2.rep smin) (hp : o.p = y.sb.pay)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay) (hb : BcHeap S M H F ({ y with rep := o } :: L)) :
    DW live S Q 0x80004500#64 R M := by
  have hsf := cx.frame
  have hn := hb.nums _ List.mem_cons_self
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  num_facts hn
  have hv : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 o.val := by rw [← hp]; exact hn.value
  have hlen : ldv .lw M (y.sb.pay + 4) = BitVec.ofNat 64 o.len := by rw [← hp]; exact hn.len
  have hl0 := hn.lbu (i := 0) (by omega)
  have hd := hn.getD_lt 0
  simp only [Nat.add_zero] at hl0 hd
  have hr10 := st.r10
  have hb0 : BcHeap S M H F ({ y with rep := o.drop 0 } :: L) := by rw [NumRep.drop_zero]; exact hb
  bc_run hlive hS [hr10, hv, hl0, hlen] at 0x8000452c 0x80004534
  · intro hne
    bv_nat at hne
    rw [Nat.mod_eq_of_lt (by omega)] at hne
    exact add_done hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hf
      (lzCount_eq _ _ _ (by omega) (by rw [hf.dsLen]; omega) (fun i hi => absurd hi (by omega))
        (.inr hne)) hb0
  · intro he
    bv_nat at he
    rw [Classical.not_not, Nat.mod_eq_of_lt (by omega)] at he
    bc_run hlive hS [hr10, hv, hl0, hlen] at 0x8000452c
    exact add_rmlz_loop hlive cx hk hf hp _ 0 _ _ rfl (by omega)
      (st.keeps (by keeps_tac Keeps.refl _ _)) hb0 (by bsimp []) (by bsimp []) (by bsimp [])
      fun i hi => by rw [show i = 0 by omega]; exact he

/-! ## The sum object -/

/-- The object `bc_new_num` returned for the sum, and the model of the
operands `a`, `b`. -/
structure AddSum (y : NumObj) (a b : NumRep) (smin : Nat) : Prop where
  rep : y.rep = zeroRep y.sb.pay y.db.pay (max a.len b.len + 1) (max smin (max a.scale b.scale))
  model : AddModel a b
  size : max a.len b.len + 1 + max smin (max a.scale b.scale) < 2 ^ 31

theorem AddSum.N_lt {y : NumObj} {a b : NumRep} {smin : Nat} (h : AddSum y a b smin) :
    addN a b + 1 < 2 ^ 31 := by
  have := h.size; simp only [addN, loopLen]; omega

theorem AddSum.p {y : NumObj} {a b : NumRep} {smin : Nat} (h : AddSum y a b smin) :
    y.rep.p = y.sb.pay := by rw [h.rep]; rfl

theorem AddSum.lenScale {y : NumObj} {a b : NumRep} {smin : Nat} (h : AddSum y a b smin) :
    y.rep.len + y.rep.scale = max a.len b.len + 1 + max smin (max a.scale b.scale) := by
  rw [h.rep]; rfl

/-- After every position, the object before `_bc_rm_leading_zeros`. -/
theorem AddSum.final {y : NumObj} {a b : NumRep} {smin : Nat} (h : AddSum y a b smin) :
    AddFinal { y.rep with ds := addDs a b smin (addN a b + 1) } a b smin := by
  have hm := h.model
  have hl := addDs_length hm smin (Nat.le_refl _)
  exact
    { neg := by show y.rep.neg = false; rw [h.rep]; rfl
      refs := by show y.rep.refs = 1; rw [h.rep]; rfl
      ds := addDs_full hm smin
      scale := by show y.rep.scale = _; rw [h.rep]; rfl
      dsLen := by show (addDs a b smin (addN a b + 1)).length = y.rep.len + y.rep.scale
                  rw [hl, h.lenScale]
      lenPos := by show 1 ≤ y.rep.len; rw [h.rep]; simp [zeroRep] }

/-- Index `0` is still zero before the last position. -/
theorem addDs_getD_zero (a b : NumRep) (smin : Nat) :
    (addDs a b smin (addN a b)).getD 0 0 = 0 := by
  simp [addDs, sumDs]

/-- The last position written with a zero digit changes nothing. -/
theorem addDs_last_zero {a b : NumRep} {smin : Nat} (h : AddModel a b)
    (h0 : (addR a b).getD (addN a b) 0 = 0) :
    addDs a b smin (addN a b) = addDs a b smin (addN a b + 1) := by
  have e := sumDs_step (N := addN a b + 1) (k := addN a b) (r := addR a b) (Z := addZ a b smin)
    (by omega) (by rw [h.rl]; omega)
  rw [h0, show addN a b + 1 - 1 - addN a b = 0 by omega] at e
  simp only [addDs]
  rw [← e]
  simp [sumDs]

/-- The final carry at `0x800044f0`: `a6` at index `0`, `a2` the carry. -/
theorem add_final {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin (addN x1.rep x2.rep)) :: L))
    (h16 : R 16 = BitVec.ofNat 64 y.rep.val)
    (h12 : R 12 = BitVec.ofNat 64 (addC x1.rep x2.rep (addN x1.rep x2.rep))) :
    DW live S Q 0x800044f0#64 R M := by
  have hm := hy.model
  have hn := hb.nums _ List.mem_cons_self
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hls := hy.lenScale
  have v1 : heapStart ≤ y.rep.ptr := hn.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn.shape.ptrLe
  simp only [heapStart, heapEnd] at v1 v2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hc := hm.carry_le (addN x1.rep x2.rep)
  have hlast := hm.last
  have hl0 := hn.lbu (i := 0) (by show 0 < y.rep.len + y.rep.scale; omega)
  simp only [withDs, Nat.add_zero, addDs_getD_zero] at hl0
  bc_run hlive hS [h12, h16, hl0] at 0x80004500
  · intro he
    bv_nat at he
    rw [Nat.mod_eq_of_lt (by omega)] at he
    rw [addDs_last_zero hm (by rw [hlast]; omega)] at hb
    exact add_rmlz hlive cx hk hy.final hy.p (st.keeps (by keeps_tac Keeps.refl _ _)) hb
  · intro hne
    bv_nat at hne
    rw [Nat.mod_eq_of_lt (by omega)] at hne
    have hb' := add_store hm hy.lenScale hb (Nat.lt_succ_self _) (v := BitVec.ofNat 64 1)
      (by rw [sbData_ofNat, hlast]; congr 1; omega)
    rw [Nat.sub_self, Nat.add_zero] at hb'
    have e1 : BitVec.signExtend 64 (BitVec.extractLsb 31 0 1#64) = 1#64 := by decide
    bc_run hlive hS [h12, h16, hl0, e1] at 0x80004500
    refine add_rmlz hlive cx hk hy.final hy.p
      ((st.heap cx fun a ha => imgM_store_miss _ _ ?_).keeps (by keeps_tac Keeps.refl _ _)) hb'
    simp only [OutHeap, heapStart, heapEnd] at ha; omega

/-! ## The carry loop -/

/-- From position `k0` on, only the operand `o` has digits: position `k`
holds `o`'s digit `o.len + S - 1 - k`; the last position is `k0 + c - 1`. -/
structure AddTail (a b o : NumRep) (k0 c : Nat) : Prop where
  stop : k0 + c = addN a b
  digit : ∀ k, k0 ≤ k → k < addN a b →
    (addXs a b).getD k 0 + (addYs a b).getD k 0 = o.ds.getD (o.len + max a.scale b.scale - 1 - k) 0
  top : addN a b ≤ o.len + max a.scale b.scale
  low : max a.scale b.scale - o.scale ≤ k0

/-- The registers of the carry loop at `0x800044a8` after `j` positions:
`a7` the operand's digit, `a1` its first, `a3 = c - 1`, `t1` the result's
digit, `a6` its first, `a2` the carry, `t3 = 9`. -/
structure CarryRegs (R : Nat → BitVec 64) (A Y c j carry : Nat) : Prop where
  r17 : R 17 = BitVec.ofNat 64 (A - j)
  r11 : R 11 = BitVec.ofNat 64 A
  r13 : R 13 = BitVec.ofNat 64 (c - 1)
  r6 : R 6 = BitVec.ofNat 64 (Y - j)
  r16 : R 16 = BitVec.ofNat 64 Y
  r12 : R 12 = BitVec.ofNat 64 carry
  r28 : R 28 = BitVec.ofNat 64 9

/-- After the carry loop, from `0x800044e0`: `a6` back to index `0`. -/
theorem add_carry_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c Y : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hstop : k0 + c = addN x1.rep x2.rep) (hc : 1 ≤ c)
    (hY : Y = y.rep.val + (addN x1.rep x2.rep - k0))
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin (addN x1.rep x2.rep)) :: L))
    (h16 : R 16 = BitVec.ofNat 64 Y) (h13 : R 13 = BitVec.ofNat 64 (c - 1))
    (h12 : R 12 = BitVec.ofNat 64 (addC x1.rep x2.rep (addN x1.rep x2.rep))) :
    DW live S Q 0x800044e0#64 R M := by
  have hn0 := hb.nums _ List.mem_cons_self
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hls := hy.lenScale
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  simp only [heapStart, heapEnd] at v1 v2
  simp only [addN, loopLen] at hstop hY hls
  bc_run hlive hS [h16, h13, h12, toInt_ofNat_small] at 0x800044f0
  · intro hc'; exfalso; (try simp (disch := omega) only [toInt_ofNat_small] at hc'); omega
  · intro _
    bc_run hlive hS [h16, h13, h12, sub_ofNat] at 0x800044f0
    exact add_final hlive cx hk hy (st.keeps (by keeps_tac Keeps.refl _ _)) hb
      (by bsimp []; congr 1; omega) (by bsimp [h12])

/-- The carry loop's store, step and back edge at `0x800044d4`: `a5` the
digit of position `k0 + j`, `a2` the carry out, `a4` the count left. -/
theorem add_carry_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c A Y j : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hstop : k0 + c = addN x1.rep x2.rep) (hj : j < c) (hjA : j + 1 ≤ A)
    (hY : Y = y.rep.val + (addN x1.rep x2.rep - k0))
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin (k0 + j)) :: L))
    (h15 : R 15 = BitVec.ofNat 64 ((addR x1.rep x2.rep).getD (k0 + j) 0))
    (h12 : R 12 = BitVec.ofNat 64 (addC x1.rep x2.rep (k0 + j + 1)))
    (h14 : R 14 = BitVec.ofNat 64 (c - 1 - j)) (h17 : R 17 = BitVec.ofNat 64 (A - j - 1))
    (h11 : R 11 = BitVec.ofNat 64 A) (h13 : R 13 = BitVec.ofNat 64 (c - 1))
    (h6 : R 6 = BitVec.ofNat 64 (Y - j)) (h16 : R 16 = BitVec.ofNat 64 Y)
    (h28 : R 28 = BitVec.ofNat 64 9)
    (hnext : j + 1 < c → ∀ (R' : Nat → BitVec 64) (M' : Mem), AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin (k0 + (j + 1))) :: L) →
      CarryRegs R' A Y c (j + 1) (addC x1.rep x2.rep (k0 + (j + 1))) →
      DW live S Q 0x800044a8#64 R' M') :
    DW live S Q 0x800044d4#64 R M := by
  have hm := hy.model
  have hn0 := hb.nums _ List.mem_cons_self
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hls := hy.lenScale
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapStart, heapEnd] at v1 v2
  have eaddr : Y - j = y.rep.val + (addN x1.rep x2.rep - (k0 + j)) := by
    simp only [addN, loopLen] at hstop hY hls ⊢; omega
  have hb' : BcHeap S (writeLog M [(Y - j, 1,
      BitVec.ofNat 64 ((addR x1.rep x2.rep).getD (k0 + j) 0))]) H F
      (withDs y (addDs x1.rep x2.rep smin (k0 + j + 1)) :: L) := by
    rw [eaddr]
    exact add_store hm hls hb (by omega) (sbData_ofNat _)
  have st' := st.heap cx (M' := writeLog M [(Y - j, 1,
      BitVec.ofNat 64 ((addR x1.rep x2.rep).getD (k0 + j) 0))]) fun a ha =>
    imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; simp only [addN, loopLen] at hstop hY hls; omega)
  simp only [addN, loopLen] at hstop hY hls
  bc_run hlive hS [h15, h12, h14, h17, h11, h13, h6, h16, h28, toInt_ofNat_small] at 0x800044a8 0x800044e0
  · intro hgt
    exact hnext (by (try simp (disch := omega) only [toInt_ofNat_small] at hgt); omega) _ _
      (st'.keeps (by keeps_tac Keeps.refl _ _)) hb' ⟨by bsimp [h17, Nat.sub_sub], by bsimp [h11],
        by bsimp [h13], by bsimp [h6, Nat.sub_sub], by bsimp [h16], by bsimp [h12, Nat.add_assoc],
        by bsimp [h28]⟩
  · intro hle
    have hcj : j + 1 = c := by (try simp (disch := omega) only [toInt_ofNat_small] at hle); omega
    rw [show k0 + j + 1 = addN x1.rep x2.rep by simp only [addN, loopLen]; omega] at hb' h12
    exact add_carry_exit hlive cx hk hy (st'.keeps (by keeps_tac Keeps.refl _ _))
      (by simp only [addN, loopLen]; omega) (by omega) (by simp only [addN, loopLen]; omega) hb'
      (by bsimp [h16]) (by bsimp [h13]) (by bsimp [h12])

/-- The carry loop at `0x800044a8`: `j` positions after `k0` done. -/
theorem add_carry_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y z : NumObj}
    {H : Heap} {F : List Blk} {k0 c A Y : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (hz : z ∈ L) (ht : AddTail x1.rep x2.rep z.rep k0 c)
    (hA : A = z.rep.val + (z.rep.len + max x1.rep.scale x2.rep.scale - 1 - k0))
    (hY : Y = y.rep.val + (addN x1.rep x2.rep - k0)) :
    ∀ n j (R : Nat → BitVec 64) (M : Mem), c - j = n → j < c →
      AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin (k0 + j)) :: L) →
      CarryRegs R A Y c j (addC x1.rep x2.rep (k0 + j)) →
      DW live S Q 0x800044a8#64 R M := by
  have hm := hy.model
  intro n
  induction n with
  | zero => intro j R M h1 h2; omega
  | succ n ih =>
    intro j R M hn hj st hb cr
    have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
    have hzn := hb.nums z (List.mem_cons_of_mem _ hz)
    num_facts hzn
    have htop := ht.top; have hlow := ht.low; have hstop := ht.stop
    have hc := hm.carry_le (k0 + j)
    have hd := ht.digit (k0 + j) (by omega) (by omega)
    have hdl := hzn.getD_lt (z.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j))
    have hl := hzn.lbu (i := z.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j)) (by omega)
    rw [show z.rep.val + (z.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j)) = A - j by
      omega] at hl
    obtain ⟨hr, hcs⟩ := hm.step (k := k0 + j) (by omega)
    rw [hd] at hr hcs
    have h17 := cr.r17; have h11 := cr.r11; have h13 := cr.r13; have h6 := cr.r6
    have h16 := cr.r16; have h12 := cr.r12; have h28 := cr.r28
    have hnext : j + 1 < c → ∀ (R' : Nat → BitVec 64) (M' : Mem),
        AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
        BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin (k0 + (j + 1))) :: L) →
        CarryRegs R' A Y c (j + 1) (addC x1.rep x2.rep (k0 + (j + 1))) →
        DW live S Q 0x800044a8#64 R' M' := fun hj' R' M' => ih (j + 1) R' M' (by omega) hj'
    have hNl := hy.N_lt
    have ecc := carry_count (A := A) (j := j) (c := c) (by omega) (by omega) (by omega) (by omega)
    bc_run hlive hS [h17, h11, h13, h6, h16, h12, h28, hl, addw_ofNat, and255_ofNat, ecc] at 0x800044d4
    · intro hle
      exact add_carry_tail hlive cx hk hy (st.keeps (by keeps_tac Keeps.refl _ _)) hstop hj
        (by omega) hY hb (by bsimp [hr]; congr 1; omega) (by bsimp [hcs]; congr 1; omega)
        (by bsimp [ecc]) (by bsimp []) (by bsimp [h11]) (by bsimp [h13]) (by bsimp [h6])
        (by bsimp [h16]) (by bsimp [h28]) hnext
    · intro hgt
      bc_run hlive hS [h17, h11, h13, h6, h16, h12, h28, hl, addw_ofNat, and255_ofNat, ecc, se12_ff6,
        word_sub10] at 0x800044d4
      exact add_carry_tail hlive cx hk hy (st.keeps (by keeps_tac Keeps.refl _ _)) hstop hj
        (by omega) hY hb (by bsimp [hr]; congr 1; omega)
        (by bsimp [hcs]; congr 1; omega)
        (by bsimp [ecc]) (by bsimp []) (by bsimp [h11]) (by bsimp [h13]) (by bsimp [h6])
        (by bsimp [h16]) (by bsimp [h28]) hnext

/-- The carry loop's entry at `0x80004498`: `a4` the positions left, `a1`
the operand's digit, `a6` the result's. -/
theorem add_carry_entry {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y z : NumObj}
    {H : Heap} {F : List Blk} {k0 c A Y : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (hz : z ∈ L) (ht : AddTail x1.rep x2.rep z.rep k0 c)
    (hc : 1 ≤ c) (hA : A = z.rep.val + (z.rep.len + max x1.rep.scale x2.rep.scale - 1 - k0))
    (hY : Y = y.rep.val + (addN x1.rep x2.rep - k0))
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin k0) :: L))
    (h14 : R 14 = BitVec.ofNat 64 c) (h11 : R 11 = BitVec.ofNat 64 A)
    (h16 : R 16 = BitVec.ofNat 64 Y) (h12 : R 12 = BitVec.ofNat 64 (addC x1.rep x2.rep k0)) :
    DW live S Q 0x80004498#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hNl := hy.N_lt
  have hstop := ht.stop
  bc_run hlive hS [h14, h11, h16, h12] at 0x800044a8
  exact add_carry_loop hlive cx hk hy hz ht hA hY _ 0 _ _ rfl (by omega)
    (st.keeps (by keeps_tac Keeps.refl _ _)) hb
    ⟨by bsimp [h11], by bsimp [h11], by bsimp [h14], by bsimp [h16], by bsimp [h16],
      by bsimp [h12], by bsimp []⟩

/-- `n1` alone from position `S + l2` on (`l2 < l1`). -/
theorem addTail_x1 {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hl : b.len < a.len) :
    AddTail a b a (max a.scale b.scale + b.len) (a.len - b.len) where
  stop := by simp only [addN, loopLen]; omega
  digit k h1 h2 := by
    simp only [addN, loopLen] at h2
    rw [addXs_in ha (by omega) (by omega), addYs_out hb (.inr (by omega)), Nat.add_zero]
  top := by simp only [addN, loopLen]; omega
  low := by omega

/-- `n2` alone from position `S + l1` on (`l1 < l2`). -/
theorem addTail_x2 {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hl : a.len < b.len) :
    AddTail a b b (max a.scale b.scale + a.len) (b.len - a.len) where
  stop := by simp only [addN, loopLen]; omega
  digit k h1 h2 := by
    simp only [addN, loopLen] at h2
    rw [addXs_out ha (.inr (by omega)), addYs_in hb (by omega) (by omega), Nat.zero_add]
  top := by simp only [addN, loopLen]; omega
  low := by omega

/-! ## The add loop -/

/-- The add loop's geometry: positions from `k0 = S - min s1 s2` on, `c1`
and `c2` digits of each operand, their digits at `P1`, `P2` and the
result's at `Y` going down. -/
structure AddMain (a b : NumRep) (yv k0 c1 c2 P1 P2 Y : Nat) : Prop where
  k0 : k0 = max a.scale b.scale - min a.scale b.scale
  c1 : c1 = a.len + min a.scale b.scale
  c2 : c2 = b.len + min a.scale b.scale
  P1 : P1 = a.val + (a.len + min a.scale b.scale - 1)
  P2 : P2 = b.val + (b.len + min a.scale b.scale - 1)
  Y : Y = yv + (max a.len b.len + min a.scale b.scale)

/-- The registers of the add loop at `0x80004450` after `j` positions. -/
structure MainRegs (R : Nat → BitVec 64) (P1 P2 Y c1 c2 j carry : Nat) : Prop where
  r11 : R 11 = BitVec.ofNat 64 (P1 - j)
  r17 : R 17 = BitVec.ofNat 64 (P2 - j)
  r16 : R 16 = BitVec.ofNat 64 (Y - j)
  r14 : R 14 = BitVec.ofNat 64 (c1 - j)
  r13 : R 13 = BitVec.ofNat 64 (c2 - j)
  r12 : R 12 = BitVec.ofNat 64 carry
  r28 : R 28 = BitVec.ofNat 64 9

/-- The common hypotheses of the add loop's exits. -/
structure MainExit (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp smin : Nat)
    (L : List NumObj) (x1 x2 y : NumObj) (H : Heap) (F : List Blk) (k : Nat) : Prop where
  st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay
  heap : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin k) :: L)
  r12 : R 12 = BitVec.ofNat 64 (addC x1.rep x2.rep k)
  r16 : R 16 = BitVec.ofNat 64 (y.rep.val + (addN x1.rep x2.rep - k))

/-- `n1`'s digits used up at `0x800045b0` (`k = S + l1`, `a3` the digits of
`n2` left): the final carry, or the carry loop over `n2`. -/
theorem add_exit1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hl : x1.rep.len ≤ x2.rep.len) {k : Nat} (hk0 : k = max x1.rep.scale x2.rep.scale + x1.rep.len)
    (e : MainExit S Mt0 M R0 R sp smin L x1 x2 y H F k)
    (h13 : R 13 = BitVec.ofNat 64 (x2.rep.len - x1.rep.len))
    (h17 : x1.rep.len < x2.rep.len →
      R 17 = BitVec.ofNat 64 (x2.rep.val + (x2.rep.len - x1.rep.len - 1))) :
    DW live S Q 0x800045b0#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => e.heap.heap.own a h1 h2
  have hs1 := (e.heap.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (e.heap.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have h12 := e.r12; have h16 := e.r16; have hb := e.heap
  subst hk0
  have := hs1.size; have := hs2.size; have := hs1.lenPos; have := hs2.lenPos
  bc_run hlive hS [h13] at 0x80004498 0x800044f0
  · intro e2
    bv_nat at e2
    have eN : max x1.rep.scale x2.rep.scale + x1.rep.len = addN x1.rep x2.rep := by
      simp only [addN, loopLen]; omega
    rw [eN] at hb h12 h16
    exact add_final hlive cx hk hy (e.st.keeps (by keeps_tac Keeps.refl _ _)) hb
      (by bsimp [h16, Nat.sub_self]) (by bsimp [h12])
  · intro e2
    bv_nat at e2
    have h17 := h17 (by omega)
    bc_run hlive hS [h13, h17] at 0x80004498 0x800044f0
    exact add_carry_entry hlive cx hk hy ha.m2
      (addTail_x2 hs1 hs2 (by omega)) (by omega) rfl rfl
      (e.st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [h13])
      (by bsimp [h17]; congr 1; omega) (by bsimp [h16]) (by bsimp [h12])

/-- `n2`'s digits used up first at `0x80004494` (`k = S + l2`, `a4` the
digits of `n1` left): the carry loop over `n1`. -/
theorem add_exit2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hl : x2.rep.len < x1.rep.len) {k : Nat} (hk0 : k = max x1.rep.scale x2.rep.scale + x2.rep.len)
    (e : MainExit S Mt0 M R0 R sp smin L x1 x2 y H F k)
    (h14 : R 14 = BitVec.ofNat 64 (x1.rep.len - x2.rep.len))
    (h11 : R 11 = BitVec.ofNat 64 (x1.rep.val + (x1.rep.len - x2.rep.len - 1))) :
    DW live S Q 0x80004494#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => e.heap.heap.own a h1 h2
  have hs1 := (e.heap.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (e.heap.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have h12 := e.r12; have h16 := e.r16; have hb := e.heap
  subst hk0
  have := hs1.size; have := hs2.size; have := hs1.lenPos; have := hs2.lenPos
  bc_run hlive hS [h14, h11] at 0x80004498 0x800045b0
  · intro e3; bv_nat at e3; omega
  · intro _
    exact add_carry_entry hlive cx hk hy ha.m1
      (addTail_x1 hs1 hs2 hl) (by omega) rfl rfl
      (e.st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [h14])
      (by bsimp [h11]; congr 1; omega) (by bsimp [h16]) (by bsimp [h12])

/-- The add loop's hypotheses after the store of position `k0 + j`: the
exit state at `k0 + j + 1`, the counts left, the operands' digits, and the
next iteration. -/
structure MainNext (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp smin : Nat) (L : List NumObj) (x1 x2 y : NumObj)
    (H : Heap) (F : List Blk) (k0 c1 c2 P1 P2 Y j : Nat) : Prop where
  ex : MainExit S Mt0 M R0 R sp smin L x1 x2 y H F (k0 + j + 1)
  r11 : R 11 = BitVec.ofNat 64 (P1 - j - 1)
  r17 : R 17 = BitVec.ofNat 64 (P2 - j - 1)
  r14 : R 14 = BitVec.ofNat 64 (c1 - j - 1)
  r13 : R 13 = BitVec.ofNat 64 (c2 - j - 1)
  r28 : R 28 = BitVec.ofNat 64 9
  next : j + 1 < c1 → j + 1 < c2 → ∀ (R' : Nat → BitVec 64) (M' : Mem),
    AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
    BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin (k0 + (j + 1))) :: L) →
    MainRegs R' P1 P2 Y c1 c2 (j + 1) (addC x1.rep x2.rep (k0 + (j + 1))) →
    DW live S Q 0x80004450#64 R' M'

/-- The add loop's second test at `0x80004490` (`n1` has digits left). -/
theorem add_main_br2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c1 c2 P1 P2 Y j : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hg : AddMain x1.rep x2.rep y.rep.val k0 c1 c2 P1 P2 Y) (hj1 : j + 1 < c1) (hj2 : j < c2)
    (nx : MainNext live S Q Mt0 M R0 R sp smin L x1 x2 y H F k0 c1 c2 P1 P2 Y j) :
    DW live S Q 0x80004490#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => nx.ex.heap.heap.own a h1 h2
  have h11 := nx.r11; have h17 := nx.r17; have h14 := nx.r14; have h13 := nx.r13
  have h28 := nx.r28; have h12 := nx.ex.r12; have h16 := nx.ex.r16
  have hNl := hy.N_lt
  have g1 := hg.k0; have g2 := hg.c1; have g3 := hg.c2; have g6 := hg.Y
  have g4 := hg.P1; have g5 := hg.P2
  simp only [addN, loopLen] at hNl h16
  bc_run hlive hS [h13] at 0x80004450 0x80004494
  · intro e2
    bv_nat at e2
    exact nx.next (by omega) (by omega) _ _ nx.ex.st nx.ex.heap
      ⟨by bsimp [h11, Nat.sub_sub], by bsimp [h17, Nat.sub_sub],
        by bsimp [h16]; congr 1; omega,
        by bsimp [h14, Nat.sub_sub], by bsimp [h13, Nat.sub_sub], by bsimp [h12, Nat.add_assoc],
        by bsimp [h28]⟩
  · intro e2
    bv_nat at e2
    exact add_exit2 hlive cx hk hy ha (by omega) (k := k0 + j + 1) (by omega) nx.ex
      (by bsimp [h14]; congr 1; omega) (by bsimp [h11]; congr 1; omega)

/-- The add loop's first test at `0x8000448c` (`a4` the digits of `n1` left). -/
theorem add_main_br1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c1 c2 P1 P2 Y j : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hg : AddMain x1.rep x2.rep y.rep.val k0 c1 c2 P1 P2 Y) (hj1 : j < c1) (hj2 : j < c2)
    (nx : MainNext live S Q Mt0 M R0 R sp smin L x1 x2 y H F k0 c1 c2 P1 P2 Y j) :
    DW live S Q 0x8000448c#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => nx.ex.heap.heap.own a h1 h2
  have h14 := nx.r14; have h13 := nx.r13; have h17 := nx.r17
  have hNl := hy.N_lt
  have g1 := hg.k0; have g2 := hg.c1; have g3 := hg.c2; have g5 := hg.P2
  simp only [addN, loopLen] at hNl
  bc_run hlive hS [h14] at 0x80004490 0x800045b0
  · intro e1
    bv_nat at e1
    exact add_exit1 hlive cx hk hy ha (by omega) (k := k0 + j + 1) (by omega) nx.ex
      (by bsimp [h13]; congr 1; omega) (fun _ => by bsimp [h17]; congr 1; omega)
  · intro e1
    bv_nat at e1
    exact add_main_br2 hlive cx hk hy ha hg (by omega) hj2 nx

/-- The add loop's store at `0x80004484`. -/
theorem add_main_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c1 c2 P1 P2 Y j : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hg : AddMain x1.rep x2.rep y.rep.val k0 c1 c2 P1 P2 Y) (hj1 : j < c1) (hj2 : j < c2)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin (k0 + j)) :: L))
    (h15 : R 15 = BitVec.ofNat 64 ((addR x1.rep x2.rep).getD (k0 + j) 0))
    (h12 : R 12 = BitVec.ofNat 64 (addC x1.rep x2.rep (k0 + j + 1)))
    (h11 : R 11 = BitVec.ofNat 64 (P1 - j - 1)) (h17 : R 17 = BitVec.ofNat 64 (P2 - j - 1))
    (h16 : R 16 = BitVec.ofNat 64 (Y - j))
    (h14 : R 14 = BitVec.ofNat 64 (c1 - j - 1)) (h13 : R 13 = BitVec.ofNat 64 (c2 - j - 1))
    (h28 : R 28 = BitVec.ofNat 64 9)
    (hnext : j + 1 < c1 → j + 1 < c2 → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin (k0 + (j + 1))) :: L) →
      MainRegs R' P1 P2 Y c1 c2 (j + 1) (addC x1.rep x2.rep (k0 + (j + 1))) →
      DW live S Q 0x80004450#64 R' M') :
    DW live S Q 0x80004484#64 R M := by
  have hm := hy.model
  have hn0 := hb.nums _ List.mem_cons_self
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hls := hy.lenScale
  have hNl := hy.N_lt
  have htx : tohostAddr = 0x8001ad00 := rfl
  have g1 := hg.k0; have g2 := hg.c1; have g3 := hg.c2; have g6 := hg.Y
  simp only [heapStart, heapEnd] at v1 v2
  simp only [addN, loopLen] at hls hNl
  have eaddr : Y - j = y.rep.val + (addN x1.rep x2.rep - (k0 + j)) := by
    simp only [addN, loopLen]; omega
  have hb' : BcHeap S (writeLog M [(Y - j, 1,
      BitVec.ofNat 64 ((addR x1.rep x2.rep).getD (k0 + j) 0))]) H F
      (withDs y (addDs x1.rep x2.rep smin (k0 + j + 1)) :: L) := by
    rw [eaddr]
    exact add_store hm hy.lenScale hb (by simp only [addN, loopLen]; omega) (sbData_ofNat _)
  have st' := st.heap cx (M' := writeLog M [(Y - j, 1,
      BitVec.ofNat 64 ((addR x1.rep x2.rep).getD (k0 + j) 0))]) fun a ha =>
    imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  have e16 : BitVec.ofNat 64 (Y - j - 1) =
      BitVec.ofNat 64 (y.rep.val + (addN x1.rep x2.rep - (k0 + j + 1))) := by
    congr 1; simp only [addN, loopLen]; omega
  bc_run hlive hS [h15, h16] at 0x8000448c
  exact add_main_br1 hlive cx hk hy ha hg hj1 hj2
    ⟨⟨st'.keeps (by keeps_tac Keeps.refl _ _), hb', by bsimp [h12], by bsimp [h16, e16]⟩,
      by bsimp [h11], by bsimp [h17], by bsimp [h14], by bsimp [h13], by bsimp [h28],
      fun a b R' M' st'' hb'' mr => hnext a b R' M' st'' hb'' mr⟩

/-- One iteration of the add loop at `0x80004450`: the operands' digits
`d1`, `d2` at `P1 - j`, `P2 - j`, the carry `c` in. -/
theorem add_main_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c1 c2 P1 P2 Y j d1 d2 c : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hg : AddMain x1.rep x2.rep y.rep.val k0 c1 c2 P1 P2 Y) (hj1 : j < c1) (hj2 : j < c2)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin (k0 + j)) :: L))
    (mr : MainRegs R P1 P2 Y c1 c2 j c)
    (l1 : ldv .lbu M (P1 - j) = BitVec.ofNat 64 d1) (l2 : ldv .lbu M (P2 - j) = BitVec.ofNat 64 d2)
    (hd1 : d1 < 10) (hd2 : d2 < 10) (hc : c ≤ 1)
    (a1 : 2147603920 ≤ P1 - j) (a2 : P1 - j < 2273312768)
    (b1 : 2147603920 ≤ P2 - j) (b2 : P2 - j < 2273312768)
    (hr : (addR x1.rep x2.rep).getD (k0 + j) 0 = (d1 + d2 + c) % 10)
    (hcs : addC x1.rep x2.rep (k0 + j + 1) = (d1 + d2 + c) / 10)
    (hnext : j + 1 < c1 → j + 1 < c2 → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin (k0 + (j + 1))) :: L) →
      MainRegs R' P1 P2 Y c1 c2 (j + 1) (addC x1.rep x2.rep (k0 + (j + 1))) →
      DW live S Q 0x80004450#64 R' M') :
    DW live S Q 0x80004450#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hNl := hy.N_lt
  have g2 := hg.c1; have g3 := hg.c2
  simp only [addN, loopLen] at hNl
  have h11 := mr.r11; have h17 := mr.r17; have h16 := mr.r16; have h14 := mr.r14
  have h13 := mr.r13; have h12 := mr.r12; have h28 := mr.r28
  bc_run hlive hS [h11, h17, h16, h14, h13, h12, h28, l1, l2, addw_ofNat, and255_ofNat] at 0x80004484
  · intro hle
    exact add_main_tail hlive cx hk hy ha hg hj1 hj2 (st.keeps (by keeps_tac Keeps.refl _ _)) hb
      (by bsimp [hr]; congr 1; omega) (by bsimp [hcs]; congr 1; omega) (by bsimp [h11])
      (by bsimp [h17]) (by bsimp [h16]) (by bsimp [h14]) (by bsimp [h13]) (by bsimp [h28]) hnext
  · intro hgt
    bc_run hlive hS [h11, h17, h16, h14, h13, h12, h28, l1, l2, addw_ofNat, and255_ofNat, se12_ff6,
      word_sub10] at 0x80004484
    exact add_main_tail hlive cx hk hy ha hg hj1 hj2 (st.keeps (by keeps_tac Keeps.refl _ _)) hb
      (by bsimp [hr]; congr 1; omega) (by bsimp [hcs]; congr 1; omega) (by bsimp [h11])
      (by bsimp [h17]) (by bsimp [h16]) (by bsimp [h14]) (by bsimp [h13]) (by bsimp [h28]) hnext

/-- The add loop at `0x80004450`: `j` positions after `k0` done. -/
theorem add_main_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c1 c2 P1 P2 Y : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hg : AddMain x1.rep x2.rep y.rep.val k0 c1 c2 P1 P2 Y) :
    ∀ n j (R : Nat → BitVec 64) (M : Mem), c1 - j = n → j < c1 → j < c2 →
      AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin (k0 + j)) :: L) →
      MainRegs R P1 P2 Y c1 c2 j (addC x1.rep x2.rep (k0 + j)) →
      DW live S Q 0x80004450#64 R M := by
  have hm := hy.model
  have g1 := hg.k0; have g2 := hg.c1; have g3 := hg.c2; have g4 := hg.P1; have g5 := hg.P2
  intro n
  induction n with
  | zero => intro j R M h1 h2; omega
  | succ n ih =>
    intro j R M hn hj1 hj2 st hb mr
    have hn1 := hb.nums x1 (List.mem_cons_of_mem _ ha.m1)
    have hn2 := hb.nums x2 (List.mem_cons_of_mem _ ha.m2)
    have hs1 := hn1.shape; have hs2 := hn2.shape
    have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a3 := hs1.size; have a4 := hs1.vHi
    have b1 := hs2.vLo; have b2 := hs2.ptrLe; have b3 := hs2.size; have b4 := hs2.vHi
    simp only [heapStart, heapEnd] at a1 a4 b1 b4
    have hx := addXs_in hs1 (b := x2.rep) (k := k0 + j) (by omega) (by omega)
    have hyy := addYs_in hs2 (a := x1.rep) (k := k0 + j) (by omega) (by omega)
    have l1 := hn1.lbu (i := x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j)) (by omega)
    have l2 := hn2.lbu (i := x2.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j)) (by omega)
    rw [show x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j)) = P1 - j by
      omega] at l1
    rw [show x2.rep.val + (x2.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j)) = P2 - j by
      omega] at l2
    obtain ⟨hr, hcs⟩ := hm.step (k := k0 + j) (by simp only [addN, loopLen]; omega)
    rw [hx, hyy] at hr hcs
    exact add_main_body hlive cx hk hy ha hg hj1 hj2 st hb mr l1 l2 (hn1.getD_lt _) (hn2.getD_lt _)
      (hm.carry_le _) (by omega) (by omega) (by omega) (by omega) hr hcs
      fun e1 e2 R' M' => ih (j + 1) R' M' (by omega) e1 e2

/-- The carry into a position below `S - min s1 s2` is zero: below it one
operand is zero at every position. -/
theorem addC_low {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hm : AddModel a b) {k : Nat}
    (hk : k ≤ max a.scale b.scale - min a.scale b.scale) : addC a b k = 0 :=
  carryAt_eq_zero (by rw [hm.xl, hm.yl]) hm.xd hm.yd _
    (by rw [hm.xl]; simp only [addN, loopLen]; omega) fun j hj => by
      rcases Nat.le_total a.scale b.scale with h | h
      · exact .inl (addXs_out ha (.inl (by omega)))
      · exact .inr (addYs_out hb (.inl (by omega)))

/-- Below `s1 - s2` (`s2 < s1`) the sum's digit is `n1`'s. -/
theorem addR_low1 {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hm : AddModel a b)
    (hs : b.scale < a.scale) {k : Nat} (hk : k < a.scale - b.scale) :
    (addR a b).getD k 0 = a.ds.getD (a.len + a.scale - 1 - k) 0 := by
  obtain ⟨hr, -⟩ := hm.step (k := k) (by simp only [addN, loopLen]; omega)
  rw [hr, addC_low ha hb hm (by omega), addXs_in ha (by omega) (by omega),
    addYs_out hb (.inl (by omega)), Nat.add_zero,
    Nat.mod_eq_of_lt (getD_digit ha.dig _), show max a.scale b.scale = a.scale by omega]

/-- Below `s2 - s1` (`s1 < s2`) the sum's digit is `n2`'s. -/
theorem addR_low2 {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hm : AddModel a b)
    (hs : a.scale < b.scale) {k : Nat} (hk : k < b.scale - a.scale) :
    (addR a b).getD k 0 = b.ds.getD (b.len + b.scale - 1 - k) 0 := by
  obtain ⟨hr, -⟩ := hm.step (k := k) (by simp only [addN, loopLen]; omega)
  rw [hr, addC_low ha hb hm (by omega), addYs_in hb (by omega) (by omega),
    addXs_out ha (.inl (by omega)), Nat.zero_add, Nat.add_zero,
    Nat.mod_eq_of_lt (getD_digit hb.dig _), show max a.scale b.scale = b.scale by omega]

/-- The join at `0x80004430`: `a4 = a3 = min s1 s2`, `t3 = l1`, `t1 = l2`;
the counts, the zero carry, and the add loop. -/
theorem add_join {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c1 c2 P1 P2 Y : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hg : AddMain x1.rep x2.rep y.rep.val k0 c1 c2 P1 P2 Y)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin k0) :: L))
    (h14 : R 14 = BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale))
    (h13 : R 13 = BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale))
    (h28 : R 28 = BitVec.ofNat 64 x1.rep.len) (h6 : R 6 = BitVec.ofNat 64 x2.rep.len)
    (h11 : R 11 = BitVec.ofNat 64 P1) (h17 : R 17 = BitVec.ofNat 64 P2)
    (h16 : R 16 = BitVec.ofNat 64 Y) :
    DW live S Q 0x80004430#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have := hs1.size; have := hs2.size; have := hs1.lenPos; have := hs2.lenPos
  have g1 := hg.k0; have g2 := hg.c1; have g3 := hg.c2
  have hc0 := addC_low hs1 hs2 hy.model (k := k0) (by omega)
  have e1 : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale)) +
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 x1.rep.len)) = BitVec.ofNat 64 c1 := by
    rw [addw_ofNat (by omega)]; congr 1; omega
  have e2 : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale)) +
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 x2.rep.len)) = BitVec.ofNat 64 c2 := by
    rw [addw_ofNat (by omega)]; congr 1; omega
  bc_run hlive hS [h14, h13, h28, h6, e1, e2] at 0x80004450 0x800045c0
  · intro hc; exact absurd hc (not_blez (by omega) (by omega))
  · intro _
    bc_run hlive hS [h14, h13, h28, h6, e1, e2] at 0x80004450 0x800045c0
    · intro hc; exact absurd hc (not_blez (by omega) (by omega))
    · intro _
      bc_run hlive hS [h14, h13, h28, h6, e1, e2] at 0x80004450
      rw [← Nat.add_zero k0] at hb
      exact add_main_loop hlive cx hk hy ha hg _ 0 _ _ rfl (by omega) (by omega)
        (st.keeps (by keeps_tac Keeps.refl _ _)) hb
        ⟨by bsimp [h11], by bsimp [h17], by bsimp [h16], by bsimp [e1], by bsimp [e2],
          by rw [Nat.add_zero, hc0]; bsimp [], by bsimp []⟩

/-! ## The fraction copies -/

/-- The registers of the first fraction copy at `0x80004400` after `j`
digits: `a5` at `n1`'s digit, `a3` below the result's, `t1` where `a5`
stops, `t3 = n - 1`. -/
structure Copy1Regs (R : Nat → BitVec 64) (A Y n s P2 j : Nat) : Prop where
  r15 : R 15 = BitVec.ofNat 64 (A - j)
  r13 : R 13 = BitVec.ofNat 64 (Y - j)
  r6 : R 6 = BitVec.ofNat 64 (A - n)
  r28 : R 28 = BitVec.ofNat 64 (n - 1)
  r16 : R 16 = BitVec.ofNat 64 Y
  r11 : R 11 = BitVec.ofNat 64 A
  r14 : R 14 = BitVec.ofNat 64 s
  r17 : R 17 = BitVec.ofNat 64 P2

/-- After the first fraction copy, from `0x80004414`: `a1`, `a6` past the
copied digits, `t1 = l2`, `t3 = l1`, `a3 = s2`, then the join. -/
theorem add_copy1_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A Y P2 : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hs : x2.rep.scale < x1.rep.scale) (hA : A = x1.rep.val + (x1.rep.len + x1.rep.scale - 1))
    (hY : Y = y.rep.val + (max x1.rep.len x2.rep.len + x1.rep.scale))
    (hP2 : P2 = x2.rep.val + (x2.rep.len + x2.rep.scale - 1))
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin (x1.rep.scale - x2.rep.scale)) :: L))
    (cr : Copy1Regs R A Y (x1.rep.scale - x2.rep.scale) x2.rep.scale P2
      (x1.rep.scale - x2.rep.scale)) :
    DW live S Q 0x80004414#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ ha.m1)
  have hn2 := hb.nums x2 (List.mem_cons_of_mem _ ha.m2)
  have hs1 := hn1.shape; have hs2 := hn2.shape
  have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a3 := hs1.size; have a4 := hs1.vHi
  have p1 := hs1.pLo; have p2 := hs1.pHi; have p3 := hs2.pLo; have p4 := hs2.pHi
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  simp only [heapStart, heapEnd] at a1 a4 v1 p1 p2 p3 p4
  have l1 := hn1.len; have l2 := hn2.len
  have h18 := st.r18; have h9 := st.r9
  have h15 := cr.r15; have h13 := cr.r13; have h6 := cr.r6; have h28 := cr.r28
  have h16 := cr.r16; have h11 := cr.r11; have h14 := cr.r14; have h17 := cr.r17
  num_facts hn1
  num_facts hn2
  bc_run hlive hS [h16, h11, h14, h17, h28, h18, h9, l1, l2, word_pred, sub_ofNat] at 0x80004430
  exact add_join hlive cx hk hy ha (k0 := x1.rep.scale - x2.rep.scale)
    (c1 := x1.rep.len + x2.rep.scale) (c2 := x2.rep.len + x2.rep.scale)
    (P1 := A - (x1.rep.scale - x2.rep.scale)) (P2 := P2) (Y := Y - (x1.rep.scale - x2.rep.scale))
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    (st.keeps (by keeps_tac Keeps.refl _ _)) hb
    (by bsimp [h14]; congr 1; omega) (by bsimp [h14]; congr 1; omega) (by bsimp [h18, l1])
    (by bsimp [h9, l2]) (by bsimp [h11]; congr 1; omega) (by bsimp [h17])
    (by bsimp [h16]; congr 1; omega)

/-- One step of the first fraction copy at `0x80004400`: the digit `d` of
`n1` at `A - j` into the result at `Y - j`. -/
theorem add_copy1_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A Y n s P2 j d : Nat}
    (cx : AddCtx S R0 sp) (hy : AddSum y x1.rep x2.rep smin)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin j) :: L))
    (cr : Copy1Regs R A Y n s P2 j) (hj : j < n) (hnA : n ≤ A) (hA : A < 2 ^ 63)
    (hl : ldv .lbu M (A - j) = BitVec.ofNat 64 d) (hr : (addR x1.rep x2.rep).getD j 0 = d)
    (a1 : 2147603920 ≤ A - j) (a2 : A - j < 2273312768) (hjN : j < addN x1.rep x2.rep) (hYa : Y = y.rep.val + addN x1.rep x2.rep)
    (hnext : j + 1 < n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin (j + 1)) :: L) →
      Copy1Regs R' A Y n s P2 (j + 1) → DW live S Q 0x80004400#64 R' M')
    (hexit : j + 1 = n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin (j + 1)) :: L) →
      Copy1Regs R' A Y n s P2 (j + 1) → DW live S Q 0x80004414#64 R' M') :
    DW live S Q 0x80004400#64 R M := by
  have hm := hy.model
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hls := hy.lenScale
  simp only [heapStart, heapEnd] at v1 v2
  simp only [addN, loopLen] at hls hjN hYa
  have hb' : BcHeap S (writeLog M [(Y - j - 1 + 1, 1, BitVec.ofNat 64 d)]) H F
      (withDs y (addDs x1.rep x2.rep smin (j + 1)) :: L) := by
    rw [show Y - j - 1 + 1 = y.rep.val + (addN x1.rep x2.rep - j) by simp only [addN, loopLen]; omega]
    exact add_store hm hy.lenScale hb (by simp only [addN, loopLen]; omega) (by rw [sbData_ofNat, hr])
  have st' := st.heap cx (M' := writeLog M [(Y - j - 1 + 1, 1, BitVec.ofNat 64 d)]) fun a ha =>
    imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  have h15 := cr.r15; have h13 := cr.r13; have h6 := cr.r6; have h28 := cr.r28
  have h16 := cr.r16; have h11 := cr.r11; have h14 := cr.r14; have h17 := cr.r17
  bc_run hlive hS [h15, h13, hl] at 0x80004410
  bc_run hlive hS [h15, h13, hl, h6] at 0x80004400 0x80004414
  · intro hne
    bv_nat at hne
    exact hnext (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [Nat.sub_sub], by bsimp [Nat.sub_sub], by bsimp [h6], by bsimp [h28], by bsimp [h16],
        by bsimp [h11], by bsimp [h14], by bsimp [h17]⟩
  · intro he
    bv_nat at he
    exact hexit (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [Nat.sub_sub], by bsimp [Nat.sub_sub], by bsimp [h6], by bsimp [h28], by bsimp [h16],
        by bsimp [h11], by bsimp [h14], by bsimp [h17]⟩

/-- The first fraction copy at `0x80004400` (`s2 < s1`): `n1`'s last
`s1 - s2` digits into the result, then the join. -/
theorem add_copy1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A Y P2 : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hs : x2.rep.scale < x1.rep.scale) (hA : A = x1.rep.val + (x1.rep.len + x1.rep.scale - 1))
    (hY : Y = y.rep.val + (max x1.rep.len x2.rep.len + x1.rep.scale))
    (hP2 : P2 = x2.rep.val + (x2.rep.len + x2.rep.scale - 1)) :
    ∀ m j (R : Nat → BitVec 64) (M : Mem), x1.rep.scale - x2.rep.scale - j = m →
      j < x1.rep.scale - x2.rep.scale →
      AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin j) :: L) →
      Copy1Regs R A Y (x1.rep.scale - x2.rep.scale) x2.rep.scale P2 j →
      DW live S Q 0x80004400#64 R M := by
  have hm := hy.model
  intro m
  induction m with
  | zero => intro j R M h1 h2; omega
  | succ m ih =>
    intro j R M hm' hj st hb cr
    have hn1 := hb.nums x1 (List.mem_cons_of_mem _ ha.m1)
    have hs1 := hn1.shape
    have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
    have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a3 := hs1.size; have a4 := hs1.vHi
    simp only [heapStart, heapEnd] at a1 a4
    have hl := hn1.lbu (i := x1.rep.len + x1.rep.scale - 1 - j) (by omega)
    rw [show x1.rep.val + (x1.rep.len + x1.rep.scale - 1 - j) = A - j by omega] at hl
    exact add_copy1_body hlive cx hy st hb cr hj (by omega) (by omega) hl
      (addR_low1 hs1 hs2 hm hs (k := j) (by omega)) (by omega) (by omega)
      (by simp only [addN, loopLen]; omega) (by simp only [addN, loopLen]; omega)
      (fun e R' M' => ih (j + 1) R' M' (by omega) e)
      (fun e R' M' st' hb' cr' => by
        rw [e] at hb' cr'
        exact add_copy1_exit hlive cx hk hy ha hs hA hY hP2 st' hb' cr')

/-- The second fraction copy's count `(a5 - 1) + s - a7` in 32-bit words. -/
theorem copy2_count {A j s : Nat} (hj : j < s) (hjA : j + 1 ≤ A) (hA : A < 2 ^ 64) (hs : s < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (BitVec.ofNat 64 (A - j - 1)) + BitVec.extractLsb 31 0 (BitVec.ofNat 64 s))) -
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 A)) = BitVec.ofNat 64 (s - j - 1) := by
  rw [ext_sext32]
  apply sext_of32 _ (by omega)
  rw [BitVec.toNat_sub, BitVec.toNat_add, toNat_ext32, toNat_ext32, toNat_ext32]
  omega

/-- The registers of the second fraction copy at `0x80004564` after `j`
digits: `a5` at `n2`'s digit, `t1` at the result's. -/
structure Copy2Regs (R : Nat → BitVec 64) (A Y s1 s2 P1 j : Nat) : Prop where
  r15 : R 15 = BitVec.ofNat 64 (A - j)
  r6 : R 6 = BitVec.ofNat 64 (Y - j)
  r17 : R 17 = BitVec.ofNat 64 A
  r14 : R 14 = BitVec.ofNat 64 s2
  r13 : R 13 = BitVec.ofNat 64 s1
  r16 : R 16 = BitVec.ofNat 64 Y
  r11 : R 11 = BitVec.ofNat 64 P1

/-- After the second fraction copy, from `0x80004580`: `a7`, `a6` past the
copied digits, `t1 = l2`, `t3 = l1`, `a4 = s1`, then the join. -/
theorem add_copy2_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A Y P1 : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hs : x1.rep.scale < x2.rep.scale) (hA : A = x2.rep.val + (x2.rep.len + x2.rep.scale - 1))
    (hY : Y = y.rep.val + (max x1.rep.len x2.rep.len + x2.rep.scale))
    (hP1 : P1 = x1.rep.val + (x1.rep.len + x1.rep.scale - 1))
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin (x2.rep.scale - x1.rep.scale)) :: L))
    (cr : Copy2Regs R A Y x1.rep.scale x2.rep.scale P1 (x2.rep.scale - x1.rep.scale)) :
    DW live S Q 0x80004580#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ ha.m1)
  have hn2 := hb.nums x2 (List.mem_cons_of_mem _ ha.m2)
  have hs1 := hn1.shape; have hs2 := hn2.shape
  have a1 := hs2.vLo; have a2 := hs2.ptrLe; have a3 := hs2.size; have a4 := hs2.vHi
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  simp only [heapStart, heapEnd] at a1 a4 v1
  num_facts hn1
  num_facts hn2
  have l1 := hn1.len; have l2 := hn2.len
  have h18 := st.r18; have h9 := st.r9
  have h15 := cr.r15; have h6 := cr.r6; have h17 := cr.r17; have h14 := cr.r14
  have h13 := cr.r13; have h16 := cr.r16; have h11 := cr.r11
  bc_run hlive hS [h16, h11, h14, h17, h13, h18, h9, l1, l2, subw_ofNat, word_pred, sxw_ofNat,
    shl_shr32, sub_ofNat] at 0x80004430
  exact add_join hlive cx hk hy ha (k0 := x2.rep.scale - x1.rep.scale)
    (c1 := x1.rep.len + x1.rep.scale) (c2 := x2.rep.len + x1.rep.scale)
    (P1 := P1) (P2 := A - (x2.rep.scale - x1.rep.scale)) (Y := Y - (x2.rep.scale - x1.rep.scale))
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    (st.keeps (by keeps_tac Keeps.refl _ _)) hb
    (by bsimp [h13]; congr 1; omega) (by bsimp [h13]; congr 1; omega) (by bsimp [h18, l1])
    (by bsimp [h9, l2]) (by bsimp [h11]) (by bsimp [h17]; congr 1; omega)
    (by bsimp [h16]; congr 1; omega)

/-- One step of the second fraction copy at `0x80004564`: the digit `d` of
`n2` at `A - j` into the result at `Y - j`. -/
theorem add_copy2_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A Y s1 s2 P1 j d : Nat}
    (cx : AddCtx S R0 sp) (hy : AddSum y x1.rep x2.rep smin)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin j) :: L))
    (cr : Copy2Regs R A Y s1 s2 P1 j) (hj : j + s1 < s2) (hs2 : s2 < 2 ^ 31) (hsA : s2 ≤ A)
    (hA : A < 2 ^ 63)
    (hl : ldv .lbu M (A - j) = BitVec.ofNat 64 d) (hr : (addR x1.rep x2.rep).getD j 0 = d)
    (a1 : 2147603920 ≤ A - j) (a2 : A - j < 2273312768) (hjN : j < addN x1.rep x2.rep)
    (hYa : Y = y.rep.val + addN x1.rep x2.rep)
    (hnext : j + 1 + s1 < s2 → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin (j + 1)) :: L) →
      Copy2Regs R' A Y s1 s2 P1 (j + 1) → DW live S Q 0x80004564#64 R' M')
    (hexit : j + 1 + s1 = s2 → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin (j + 1)) :: L) →
      Copy2Regs R' A Y s1 s2 P1 (j + 1) → DW live S Q 0x80004580#64 R' M') :
    DW live S Q 0x80004564#64 R M := by
  have hm := hy.model
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hls := hy.lenScale
  simp only [heapStart, heapEnd] at v1 v2
  simp only [addN, loopLen] at hls hjN hYa
  have hb' : BcHeap S (writeLog M [(Y - j, 1, BitVec.ofNat 64 d)]) H F
      (withDs y (addDs x1.rep x2.rep smin (j + 1)) :: L) := by
    rw [show Y - j = y.rep.val + (addN x1.rep x2.rep - j) by simp only [addN, loopLen]; omega]
    exact add_store hm hy.lenScale hb (by simp only [addN, loopLen]; omega) (by rw [sbData_ofNat, hr])
  have st' := st.heap cx (M' := writeLog M [(Y - j, 1, BitVec.ofNat 64 d)]) fun a ha =>
    imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  have h15 := cr.r15; have h6 := cr.r6; have h17 := cr.r17; have h14 := cr.r14
  have h13 := cr.r13; have h16 := cr.r16; have h11 := cr.r11
  have ecc := copy2_count (A := A) (j := j) (s := s2) (by omega) (by omega) (by omega) hs2
  bc_run hlive hS [h15, h6, h17, h14, hl, ecc] at 0x8000457c
  bc_run hlive hS [h15, h6, h17, h14, h13, hl, ecc, toInt_ofNat_small] at 0x80004564 0x80004580
  · intro hlt
    have hlt' : j + 1 + s1 < s2 := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
    exact hnext hlt' _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [Nat.sub_sub], by bsimp [Nat.sub_sub], by bsimp [h17], by bsimp [h14],
        by bsimp [h13], by bsimp [h16], by bsimp [h11]⟩
  · intro hge
    have hge' : j + 1 + s1 = s2 := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hge); omega
    exact hexit hge' _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [Nat.sub_sub], by bsimp [Nat.sub_sub], by bsimp [h17], by bsimp [h14],
        by bsimp [h13], by bsimp [h16], by bsimp [h11]⟩

/-- The second fraction copy at `0x80004564` (`s1 < s2`): `n2`'s last
`s2 - s1` digits into the result, then the join. -/
theorem add_copy2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A Y P1 : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hs : x1.rep.scale < x2.rep.scale) (hA : A = x2.rep.val + (x2.rep.len + x2.rep.scale - 1))
    (hY : Y = y.rep.val + (max x1.rep.len x2.rep.len + x2.rep.scale))
    (hP1 : P1 = x1.rep.val + (x1.rep.len + x1.rep.scale - 1)) :
    ∀ m j (R : Nat → BitVec 64) (M : Mem), x2.rep.scale - x1.rep.scale - j = m →
      j < x2.rep.scale - x1.rep.scale →
      AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin j) :: L) →
      Copy2Regs R A Y x1.rep.scale x2.rep.scale P1 j →
      DW live S Q 0x80004564#64 R M := by
  have hm := hy.model
  intro m
  induction m with
  | zero => intro j R M h1 h2; omega
  | succ m ih =>
    intro j R M hm' hj st hb cr
    have hn2 := hb.nums x2 (List.mem_cons_of_mem _ ha.m2)
    have hs2 := hn2.shape
    have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
    have a1 := hs2.vLo; have a2 := hs2.ptrLe; have a3 := hs2.size; have a4 := hs2.vHi
    simp only [heapStart, heapEnd] at a1 a4
    have hl := hn2.lbu (i := x2.rep.len + x2.rep.scale - 1 - j) (by omega)
    rw [show x2.rep.val + (x2.rep.len + x2.rep.scale - 1 - j) = A - j by omega] at hl
    exact add_copy2_body hlive cx hy st hb cr (by omega) (by omega) (by omega) (by omega) hl
      (addR_low2 hs1 hs2 hm hs (k := j) (by omega)) (by omega) (by omega)
      (by simp only [addN, loopLen]; omega) (by simp only [addN, loopLen]; omega)
      (fun e R' M' => ih (j + 1) R' M' (by omega) (by omega))
      (fun e R' M' st' hb' cr' => by
        rw [show j + 1 = x2.rep.scale - x1.rep.scale by omega] at hb' cr'
        exact add_copy2_exit hlive cx hk hy ha hs hA hY hP1 st' hb' cr')

/-- `add (a - 1), b` with `a` possibly zero. -/
theorem pred_add_ofNat {a b : Nat} (hb : 1 ≤ b) :
    BitVec.ofNat 64 a + 18446744073709551615#64 + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b - 1) := by
  rw [BitVec.add_assoc, BitVec.add_comm 18446744073709551615#64, ← BitVec.add_assoc,
    ofNat_add_ofNat, word_pred (by omega)]

/-- `add a, b; addi a, a, -1` with `a + b` positive. -/
theorem add2_pred {a b : Nat} (h : 1 ≤ a + b) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b + 18446744073709551615#64 = BitVec.ofNat 64 (a + b - 1) := by
  rw [ofNat_add_ofNat, word_pred h]

/-- The first fraction copy's entry at `0x800043e0` (`s2 < s1`): the count
`s1 - s2 - 1` in `t3`, `a5`'s stop in `t1`. -/
theorem add_copy1_entry {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A Y P2 : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hs : x2.rep.scale < x1.rep.scale) (hA : A = x1.rep.val + (x1.rep.len + x1.rep.scale - 1))
    (hY : Y = y.rep.val + (max x1.rep.len x2.rep.len + x1.rep.scale))
    (hP2 : P2 = x2.rep.val + (x2.rep.len + x2.rep.scale - 1))
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin 0) :: L))
    (h13 : R 13 = BitVec.ofNat 64 x1.rep.scale) (h14 : R 14 = BitVec.ofNat 64 x2.rep.scale)
    (h16 : R 16 = BitVec.ofNat 64 Y) (h11 : R 11 = BitVec.ofNat 64 A)
    (h17 : R 17 = BitVec.ofNat 64 P2) :
    DW live S Q 0x800043e0#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a3 := hs1.size; have a4 := hs1.vHi
  simp only [heapStart, heapEnd] at a1 a4
  bc_run hlive hS [h13, h14, h16, h11, h17, se12_fff, word_pred, sxw_ofNat, subw_ofNat, shl_shr32,
    add_not_ofNat] at 0x80004400
  exact add_copy1 hlive cx hk hy ha hs hA hY hP2 _ 0 _ _ rfl (by omega)
    (st.keeps (by keeps_tac Keeps.refl _ _)) hb
    ⟨by bsimp [h11], by bsimp [h16], by bsimp []; congr 1; omega, by bsimp []; congr 1; omega,
      by bsimp [h16], by bsimp [h11], by bsimp [h14], by bsimp [h17]⟩

/-- The second fraction copy's entry at `0x8000455c` (`s1 < s2`). -/
theorem add_copy2_entry {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A Y P1 : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hs : x1.rep.scale < x2.rep.scale) (hA : A = x2.rep.val + (x2.rep.len + x2.rep.scale - 1))
    (hY : Y = y.rep.val + (max x1.rep.len x2.rep.len + x2.rep.scale))
    (hP1 : P1 = x1.rep.val + (x1.rep.len + x1.rep.scale - 1))
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin 0) :: L))
    (h13 : R 13 = BitVec.ofNat 64 x1.rep.scale) (h14 : R 14 = BitVec.ofNat 64 x2.rep.scale)
    (h16 : R 16 = BitVec.ofNat 64 Y) (h11 : R 11 = BitVec.ofNat 64 P1)
    (h17 : R 17 = BitVec.ofNat 64 A) :
    DW live S Q 0x8000455c#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  bc_run hlive hS [h13, h14, h16, h11, h17] at 0x80004564
  exact add_copy2 hlive cx hk hy ha hs hA hY hP1 _ 0 _ _ rfl (by omega)
    (st.keeps (by keeps_tac Keeps.refl _ _)) hb
    ⟨by bsimp [h17], by bsimp [h16], by bsimp [h17], by bsimp [h14], by bsimp [h13], by bsimp [h16],
      by bsimp [h11]⟩

/-- The three-way dispatch at `0x800043d8` on the operands' scales `a3`,
`a4`: equal scales to the join, the longer fraction copied first otherwise. -/
theorem add_dispatch {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {Y P1 P2 : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin 0) :: L))
    (hY : Y = y.rep.val + (max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale))
    (hP1 : P1 = x1.rep.val + (x1.rep.len + x1.rep.scale - 1))
    (hP2 : P2 = x2.rep.val + (x2.rep.len + x2.rep.scale - 1))
    (h13 : R 13 = BitVec.ofNat 64 x1.rep.scale) (h14 : R 14 = BitVec.ofNat 64 x2.rep.scale)
    (h28 : R 28 = BitVec.ofNat 64 x1.rep.len) (h6 : R 6 = BitVec.ofNat 64 x2.rep.len)
    (h16 : R 16 = BitVec.ofNat 64 Y) (h11 : R 11 = BitVec.ofNat 64 P1)
    (h17 : R 17 = BitVec.ofNat 64 P2) :
    DW live S Q 0x800043d8#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have := hs1.size; have := hs2.size
  bc_run hlive hS [h13, h14, toInt_ofNat_small] at 0x80004430 0x8000455c 0x800043e0
  · intro he
    bv_nat at he
    exact add_join hlive cx hk hy ha (k0 := 0) (c1 := x1.rep.len + x1.rep.scale)
      (c2 := x2.rep.len + x1.rep.scale) (P1 := P1) (P2 := P2) (Y := Y)
      ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [h14]; congr 1; omega)
      (by bsimp [h13]; congr 1; omega) (by bsimp [h28]) (by bsimp [h6]) (by bsimp [h11])
      (by bsimp [h17]) (by bsimp [h16])
  · intro hne
    bv_nat at hne
    bc_run hlive hS [h13, h14, toInt_ofNat_small] at 0x80004430 0x8000455c 0x800043e0
    · intro hge
      have hge' : x1.rep.scale ≤ x2.rep.scale := by
        (try simp (disch := omega) only [toInt_ofNat_small] at hge); omega
      exact add_copy2_entry hlive cx hk hy ha (by omega) (by omega) (Y := Y) (by omega) hP1
        (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [h13]) (by bsimp [h14])
        (by bsimp [h16]) (by bsimp [h11]) (by bsimp [h17])
    · intro hlt
      have hlt' : x2.rep.scale < x1.rep.scale := by
        (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
      exact add_copy1_entry hlive cx hk hy ha hlt' hP1 (Y := Y) (by omega) hP2
        (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [h13]) (by bsimp [h14])
        (by bsimp [h16]) (by bsimp [h11]) (by bsimp [h17])

/-- The setup's arithmetic at `0x800043b4`: the operands' and the result's
last digit addresses from `n_value`, the lengths and scales. -/
theorem add_setup_addr {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin 0) :: L))
    (h8 : R 8 = BitVec.ofNat 64 (max x1.rep.scale x2.rep.scale))
    (h19 : R 19 = BitVec.ofNat 64 (max x1.rep.len x2.rep.len + 1))
    (h13 : R 13 = BitVec.ofNat 64 x1.rep.scale) (h14 : R 14 = BitVec.ofNat 64 x2.rep.scale)
    (h28 : R 28 = BitVec.ofNat 64 x1.rep.len) (h6 : R 6 = BitVec.ofNat 64 x2.rep.len)
    (h16 : R 16 = BitVec.ofNat 64 y.rep.val) (h11 : R 11 = BitVec.ofNat 64 x1.rep.val)
    (h17 : R 17 = BitVec.ofNat 64 x2.rep.val) :
    DW live S Q 0x800043b4#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have := hs1.size; have := hs2.size; have := hs1.lenPos; have := hs2.lenPos
  have w1 := hs1.vHi; have w2 := hs2.vHi
  have hn0 := hb.nums _ List.mem_cons_self
  have w3 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have hls := hy.lenScale
  simp only [heapEnd] at w1 w2 w3
  bc_run hlive hS [h8, h19, h13, h14, h28, h6, h16, h11, h17, add2_pred, pred_add_ofNat]
    at 0x800043d8
  exact add_dispatch hlive cx hk hy ha (st.keeps (by keeps_tac Keeps.refl _ _)) hb
    (Y := y.rep.val + (max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale)) rfl rfl rfl
    (by bsimp [h13]) (by bsimp [h14]) (by bsimp [h28]) (by bsimp [h6])
    (by bsimp [h16]; congr 1; omega) (by bsimp [h11]) (by bsimp [h17])

/-- After `bc_new_num` and the zero fill, from `0x80004398`: the operands'
scales, lengths and `n_value`s, the result's `n_value`. -/
theorem add_setup {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin 0) :: L))
    (h8 : R 8 = BitVec.ofNat 64 (max x1.rep.scale x2.rep.scale))
    (h19 : R 19 = BitVec.ofNat 64 (max x1.rep.len x2.rep.len + 1)) :
    DW live S Q 0x80004398#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ ha.m1)
  have hn2 := hb.nums x2 (List.mem_cons_of_mem _ ha.m2)
  have hn0 := hb.nums _ List.mem_cons_self
  num_facts hn1
  num_facts hn2
  have yp1 : heapStart ≤ y.rep.p := hn0.shape.pLo
  have yp2 : y.rep.p + 40 ≤ heapEnd := hn0.shape.pHi
  have yp3 : y.rep.p % 8 = 0 := hn0.shape.pAl
  simp only [heapStart, heapEnd] at yp1 yp2
  have hp := hy.p
  have hv0 : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by rw [← hp]; exact hn0.value
  have l1 := hn1.len; have l2 := hn2.len; have c1 := hn1.scale; have c2 := hn2.scale
  have u1 := hn1.value; have u2 := hn2.value
  have h18 := st.r18; have h9 := st.r9; have h10 := st.r10
  bc_run hlive hS [h18, h9, h10, l1, l2, c1, c2, u1, u2, hv0] at 0x800043b4
  exact add_setup_addr hlive cx hk hy ha (st.keeps (by keeps_tac Keeps.refl _ _)) hb
    (by bsimp [h8]) (by bsimp [h19]) (by bsimp [c1]) (by bsimp [c2]) (by bsimp [l1]) (by bsimp [l2])
    (by bsimp [hv0]) (by bsimp [u1]) (by bsimp [u2])

/-! ## The `scale_min` zero fill -/

/-- A zero written into the result before any position changes nothing. -/
theorem BcHeap.zeroFill {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {a b : NumRep} {smin i : Nat}
    (hyl : y.rep.len + y.rep.scale = max a.len b.len + 1 + max smin (max a.scale b.scale))
    (hb : BcHeap S M H F (withDs y (addDs a b smin 0) :: L))
    (hi : i < max a.len b.len + 1 + max smin (max a.scale b.scale)) {v : BitVec 64}
    (hv : sbData v = BitVec.ofNat 8 0) :
    BcHeap S (writeLog M [(y.rep.val + i, 1, v)]) H F (withDs y (addDs a b smin 0) :: L) := by
  have hst := BcHeap.setDigit (L1 := []) hb (i := i) (d := 0) (by simp only [withDs]; omega)
    (by decide) hv
  simp only [withDs, List.nil_append] at hst ⊢
  rw [← addDs_zero, List.set_replicate_self] at hst
  rw [← addDs_zero]
  exact hst

/-- `addi a, a, 1` then the offset `-1`. -/
theorem inc_dec (x : BitVec 64) : x + 1#64 + 18446744073709551615#64 = x := by
  rw [BitVec.add_assoc, show (1#64 : BitVec 64) + 18446744073709551615#64 = 0#64 by decide,
    BitVec.add_zero]

/-- One zero of the `scale_min` tail at `0x8000438c`: `a5` at the `i`-th
digit past `S + D`, `a4` past the last. -/
theorem add_zfill_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {Z n i : Nat}
    (cx : AddCtx S R0 sp) (hy : AddSum y x1.rep x2.rep smin)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin 0) :: L))
    (hZ : Z = y.rep.val + (max x1.rep.scale x2.rep.scale + (max x1.rep.len x2.rep.len + 1)))
    (hn : max x1.rep.scale x2.rep.scale + n = smin) (hi : i < n)
    (h15 : R 15 = BitVec.ofNat 64 (Z + i)) (h14 : R 14 = BitVec.ofNat 64 (Z + n))
    (hnext : i + 1 < n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin 0) :: L) →
      R' 15 = BitVec.ofNat 64 (Z + (i + 1)) → R' 14 = BitVec.ofNat 64 (Z + n) →
      R' 8 = R 8 → R' 19 = R 19 → DW live S Q 0x8000438c#64 R' M')
    (hexit : i + 1 = n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      AddAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (addDs x1.rep x2.rep smin 0) :: L) →
      R' 8 = R 8 → R' 19 = R 19 → DW live S Q 0x80004398#64 R' M') :
    DW live S Q 0x8000438c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hls := hy.lenScale
  simp only [heapStart, heapEnd] at v1 v2
  have hb' := BcHeap.zeroFill (i := max x1.rep.scale x2.rep.scale + (max x1.rep.len x2.rep.len + 1) + i)
    (v := 0#64) hls hb (by omega) (sbData_ofNat 0)
  rw [show y.rep.val + (max x1.rep.scale x2.rep.scale + (max x1.rep.len x2.rep.len + 1) + i) = Z + i by
    omega] at hb'
  have st' := st.heap cx (M' := writeLog M [(Z + i, 1, 0#64)]) fun a ha =>
    imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  have ea : (upd R 15 (R 15 + 1#64) 15 + sign_extend (m := 64) (4095#12)).toNat = Z + i := by
    simp only [upd_apply, ite_true, h15, se12_fff, inc_dec, BitVec.toNat_ofNat]; omega
  -- `bc_run`'s closing `decide` attempts overflow the kernel on this step: its phases by hand
  dx_run hlive at 0x80004394
  case hS => bsimp [ea]; exact acc_heap hS (by omega) (by omega)
  all_goals (try bsimp [ea, h15, h14, se12_fff, inc_dec])
  bc_run hlive hS [h15, h14] at 0x8000438c 0x80004398
  · intro hne
    bv_nat at hne
    exact hnext (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      (by bsimp [Nat.add_assoc]) (by bsimp [h14]) (by bsimp []) (by bsimp [])
  · intro he
    bv_nat at he
    exact hexit (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb' (by bsimp [])
      (by bsimp [])

/-- The `scale_min` zero fill at `0x8000438c` (`S < scale_min`): `i` zeros
written, then the setup. -/
theorem add_zfill {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {Z n : Nat}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (hZ : Z = y.rep.val + (max x1.rep.scale x2.rep.scale + (max x1.rep.len x2.rep.len + 1)))
    (hn : max x1.rep.scale x2.rep.scale + n = smin) :
    ∀ m i (R : Nat → BitVec 64) (M : Mem), n - i = m → i < n →
      AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin 0) :: L) →
      R 15 = BitVec.ofNat 64 (Z + i) → R 14 = BitVec.ofNat 64 (Z + n) →
      R 8 = BitVec.ofNat 64 (max x1.rep.scale x2.rep.scale) →
      R 19 = BitVec.ofNat 64 (max x1.rep.len x2.rep.len + 1) →
      DW live S Q 0x8000438c#64 R M := by
  intro m
  induction m with
  | zero => intro i R M h1 h2; omega
  | succ m ih =>
    intro i R M hm hi st hb h15 h14 h8 h19
    exact add_zfill_body hlive cx hy st hb hZ hn hi h15 h14
      (fun hi' R' M' st' hb' e15 e14 e8 e19 =>
        ih (i + 1) R' M' (by omega) hi' st' hb' e15 e14 (e8.trans h8) (e19.trans h19))
      (fun _ R' M' st' hb' e8 e19 =>
        add_setup hlive cx hk hy ha st' hb' (e8.trans h8) (e19.trans h19))

/-- After `bc_new_num` at `0x80004368`: `scale_min` back from the frame;
below it the zero fill, otherwise the setup. -/
theorem add_after_new {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : AddSum y x1.rep x2.rep smin) (ha : AddArgs L x1 x2 smin)
    (st : AddAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (addDs x1.rep x2.rep smin 0) :: L))
    (h8 : R 8 = BitVec.ofNat 64 (max x1.rep.scale x2.rep.scale))
    (h19 : R 19 = BitVec.ofNat 64 (max x1.rep.len x2.rep.len + 1))
    (hsm : ldv .ld M (sp - 64 + 8) = BitVec.ofNat 64 smin) :
    DW live S Q 0x80004368#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have yp1 : heapStart ≤ y.rep.p := hn0.shape.pLo
  have yp2 : y.rep.p + 40 ≤ heapEnd := hn0.shape.pHi
  have yp3 : y.rep.p % 8 = 0 := hn0.shape.pAl
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have hls := hy.lenScale
  have hsz := ha.size
  simp only [heapStart, heapEnd] at yp1 yp2 v2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hp := hy.p
  have hv0 : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by rw [← hp]; exact hn0.value
  have h2 := st.r2; have h10 := st.r10
  bc_run hlive hS [h2, h8, h19, hsm, toInt_ofNat_small] at 0x80004398 0x80004370
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · intro _
    exact add_setup hlive cx hk hy ha (st.keeps (by keeps_tac Keeps.refl _ _)) hb
      (by bsimp [h8]) (by bsimp [h19])
  · intro hlt
    have hlt' : max x1.rep.scale x2.rep.scale < smin := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
    bc_run hlive hS [h2, h8, h19, hsm, h10, hv0, subw_ofNat, shl_shr32] at 0x8000438c
    exact add_zfill hlive cx hk hy ha (n := smin - max x1.rep.scale x2.rep.scale) rfl (by omega)
      _ 0 _ _ rfl (by omega) (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [hv0])
      (by bsimp [hv0]) (by bsimp [h8]) (by bsimp [h19])

/-! ## The call of `bc_new_num` -/

/-- The new object is the sum before any position. -/
theorem AddSum.withDs_zero {y : NumObj} {a b : NumRep} {smin : Nat} (h : AddSum y a b smin) :
    withDs y (addDs a b smin 0) = y := by
  obtain ⟨p, rep, sb, db⟩ := y
  have hr := h.rep
  simp only at hr
  subst hr
  simp only [withDs, ← addDs_zero, zeroRep]

/-- The `bc_new_num(D, max S scale_min)` call from `0x8000435c` (`scale_min`
saved at `sp + 8`); out of memory reaches `AddK.oom`. -/
theorem add_call {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 : NumObj}
    {H : Heap} {F : List Blk}
    (cx : AddCtx S R0 sp) (hk : AddK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (ha : AddArgs L x1 x2 smin) (hb : BcHeap S M H F L) (sv : SavedWords M (sp - 64) addSlots R0)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp 96 a → imgM M a = imgM Mt0 a)
    (hkp : Keeps addAll R R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 64))
    (h18 : R 18 = BitVec.ofNat 64 x1.rep.p) (h9 : R 9 = BitVec.ofNat 64 x2.rep.p)
    (h8 : R 8 = BitVec.ofNat 64 (max x1.rep.scale x2.rep.scale))
    (h19 : R 19 = BitVec.ofNat 64 (max x1.rep.len x2.rep.len + 1))
    (h11 : R 11 = BitVec.ofNat 64 (max (max x1.rep.scale x2.rep.scale) smin))
    (h12 : R 12 = BitVec.ofNat 64 smin) :
    DW live S Q 0x8000435c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := ha.size
  have hs1 := (hb.nums x1 ha.m1).shape
  have hs2 := (hb.nums x2 ha.m2).shape
  have := hs1.lenPos
  have hoff : ∀ a, sp - 64 + 8 ≤ a → a < sp - 64 + 16 → OutHeap a := fun a h1 h2 => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hb2 : BcHeap S (writeLog M [(sp - 64 + 8, 8, BitVec.ofNat 64 smin)]) H F L :=
    hb.out_frame (P := fun a => sp - 64 + 8 ≤ a ∧ a < sp - 64 + 16)
      (fun a ha => imgM_store_miss _ _ (by omega)) fun a ha => hoff a ha.1 ha.2
  bc_run hlive hS [h2, h19, h12] at 0x80004250
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hsf' : StackFrame S (sp - 64) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine bc_new_num_spec hlive hb2.newHeap hsf' (len := max x1.rep.len x2.rep.len + 1)
    (scale := max (max x1.rep.scale x2.rep.scale) smin) (by simp only [heapEnd]; omega) (by omega)
    (by omega) _ (by bsimp [h19]) (by bsimp [h11]) (by bsimp [h2]) (by bsimp [])
    ⟨fun R1 Mt1 H1 F1 y hk1 hp1 hr1 => ?_, fun R' Mt' hr2' hout' => ?_⟩
  · bsimp []
    have hy : AddSum y x1.rep x2.rep smin :=
      ⟨by rw [hp1.rep, Nat.max_comm (max x1.rep.scale x2.rep.scale)], addModel hs1 hs2, hsz⟩
    have hmem : ∀ a, OutHeap a → ¬ frameIn (sp - 64) 32 a →
        imgM Mt1 a = imgM (writeLog M [(sp - 64 + 8, 8, BitVec.ofNat 64 smin)]) a :=
      fun a ha hf => hp1.out a ha hf
    have st : AddAt S Mt0 Mt1 R0 R1 sp x1 x2 y.sb.pay :=
      { r2 := by rw [hk1.get 2]; bsimp [h2]
        saved := sv.transport (lo := 24) (top := 64) (hag := fun a h1 h2' => by
          rw [hmem a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
            (by simp only [frameIn]; omega), imgM_store_miss _ _ (by omega)])
        r18 := by rw [hk1.get 18]; bsimp [h18]
        r9 := by rw [hk1.get 9]; bsimp [h9]
        r10 := hr1
        regs := (hk1.mono (by decide)).trans ((by keeps_tac Keeps.refl _ _ : Keeps addAll _ R).trans hkp)
        out := fun a ha hf => by
          rw [hmem a ha (fun h => hf (by simp only [frameIn] at *; omega)),
            imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]
          exact hout a ha hf }
    have hb' := NewNumPost.insert hb2 hp1
    rw [← hy.withDs_zero] at hb'
    refine add_after_new hlive cx hk hy ha st hb' (by rw [hk1.get 8]; bsimp [h8])
      (by rw [hk1.get 19]; bsimp [h19]) ?_
    rw [ldv_congr .ld fun j hj => hmem _ (hoff _ (by omega) (by simp only [widthOfM] at hj; omega))
      (by simp only [frameIn]; omega)]
    exact ldv_store_hit _ _ _
  · refine hk.oom R' Mt' (by rw [hr2']; congr 1) fun a ha hf => ?_
    rw [hout' a ha (fun h => hf (by simp only [frameIn] at *; omega)),
      imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]
    exact hout a ha hf

end Dc.Mach
