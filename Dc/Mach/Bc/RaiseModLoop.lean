import Dc.Mach.Bc.RaiseModBase

/-!
# `bc_raisemod`'s loop (`0x800062cc` to `0x800063b0`)

    62cc while (!bc_is_zero (exponent)) {                       (inlined)
    62f8   bc_divmod (exponent, _two_, &exponent, &parity, 0);
    6310   if (parity != _zero_ && !bc_is_zero (parity)) {        (inlined)
    6348     bc_multiply (temp, power, &temp, rscale);
    635c     bc_divmod (temp, mod, NULL, &temp, scale); }
    6378   bc_multiply (power, power, &power, rscale);
    638c   bc_divmod (power, mod, NULL, &power, scale); }

- `RxNum`: a handle's value with its digit and scale bounds.
- `RxEnv`/`RxCst`: the loop's fixed facts.
- `RxM`: the state between the steps (handles `[power, exponent, temp,
  parity]`, their words and registers); `RxL` adds `s8` (the exponent) at
  the loop's head.
- `rx_body`: one iteration; `rx_loop`: the loop against `Num.raisemodLoop`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## Values and bounds -/

/-- The number a handle names holds `n`: normalized, with an integer digit, at
most `B` digits, scale at most `Sc`. -/
structure RxNum (h : RH) (n : Num) (B Sc : Nat) : Prop where
  num : h.base.rep.num = n
  norm : h.base.rep.Norm
  len : 1 ≤ h.base.rep.len
  size : h.base.rep.len + h.base.rep.scale ≤ B
  scale : h.base.rep.scale ≤ Sc

/-- The number a handle names, as the heap holds it. -/
theorem RxNum.obj {h : RH} {n : Num} {B Sc : Nat} (hv : RxNum h n B Sc) (hs : List RH) :
    RxNum (.own (RH.obj hs h)) n B Sc := by
  cases h <;> exact ⟨hv.num, hv.norm, hv.len, hv.size, hv.scale⟩

/-- The handles hold at most one reference each. -/
theorem rCnt_le (hs : List RH) (p : Nat) : rCnt hs p ≤ hs.length := by
  induction hs with
  | nil => exact Nat.le_refl _
  | cons h hs ih =>
    rw [rCnt_cons, List.length_cons]
    have : RH.cnt p h ≤ 1 := by cases h <;> simp only [RH.cnt] <;> (try split) <;> omega
    omega

/-- A caller's number in the heap. -/
theorem RList.mem_caller (hs : List RH) {L : List NumObj} {y : NumObj} (hy : y ∈ L) :
    rBump hs y ∈ RList hs L :=
  List.mem_append_right _ (List.mem_map_of_mem hy)

/-- `_zero_` in the heap of four handles. -/
theorem KZero.rBump {M : Mem} {z : NumObj} {k : Nat} (hs : List RH) (hl : hs.length ≤ 4)
    (h : KZero M z (k + 4)) : KZero M (rBump hs z) k := by
  have h' : KZero M z (rCnt hs z.rep.p + k) := h.mono (by have := rCnt_le hs z.rep.p; omega)
  exact h'.withRefs

/-- `_zero_`, `_one_`, `_two_` and the multiplication base, as
`bc_raisemod` reads them. -/
structure RxCst (M : Mem) (z o t : NumObj) : Prop where
  zero : KZero M z (2 ^ 30 + 4)
  one : ldv .ld M oneAddr = BitVec.ofNat 64 o.rep.p
  two : ldv .ld M twoAddr = BitVec.ofNat 64 t.rep.p
  mulBase : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80

/-- The constants survive a run that changes only the heap and the window. -/
theorem RxCst.transport {S : Nat → Prop} {Mt0 M : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {z o t : NumObj} (cx : RxCtx S R0 sp W q) (ha : RxCst Mt0 z o t)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) : RxCst M z o t := by
  have hab := cx.above
  simp only [heapEnd] at hab
  have hc : ∀ a, 0x8001cd40 ≤ a → a < 0x8001cdd0 → ¬ (0x8001cd48 ≤ a ∧ a < 0x8001cd58) →
      ¬ (0x8001cdb0 ≤ a ∧ a < 0x8001cdb8) → imgM M a = imgM Mt0 a := fun a h1 h2 h3 h4 =>
    hout a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [frameIn]; omega)
  have hz := ha.zero
  refine ⟨⟨?_, hz.len, hz.scale, hz.ds, hz.neg, hz.refs, hz.room⟩, ?_, ?_, ?_⟩
  · rw [ldv_congr .ld fun j hj => hc _ (by simp only [widthOfM, zeroAddr] at hj ⊢; omega)
      (by simp only [widthOfM, zeroAddr] at hj ⊢; omega) (by simp only [widthOfM, zeroAddr] at hj ⊢; omega)
      (by simp only [widthOfM, zeroAddr] at hj ⊢; omega)]
    exact hz.glob
  · rw [ldv_congr .ld fun j hj => hc _ (by simp only [widthOfM, oneAddr] at hj ⊢; omega)
      (by simp only [widthOfM, oneAddr] at hj ⊢; omega) (by simp only [widthOfM, oneAddr] at hj ⊢; omega)
      (by simp only [widthOfM, oneAddr] at hj ⊢; omega)]
    exact ha.one
  · rw [ldv_congr .ld fun j hj => hc _ (by simp only [widthOfM, twoAddr] at hj ⊢; omega)
      (by simp only [widthOfM, twoAddr] at hj ⊢; omega) (by simp only [widthOfM, twoAddr] at hj ⊢; omega)
      (by simp only [widthOfM, twoAddr] at hj ⊢; omega)]
    exact ha.two
  · rw [ldv_congr .lw fun j hj => hc _ (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)
      (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)
      (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)
      (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)]
    exact ha.mulBase

/-- The loop's fixed facts: the context, the caller's heap `L` of owners
with `mod` (`xm`, normalized, nonzero), `_zero_` and `_two_` in it, the scale
`k` and `rscale` (`rs`), and the bounds `B` (digits of `power` and `temp`),
`Sc` (their scales) and `Ee` (digits of the exponent) small enough for the
callees. -/
structure RxEnv (S : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64) (sp W q : Nat)
    (L : List NumObj) (xm z o t : NumObj) (k rs B Sc Ee : Nat) : Prop where
  cx : RxCtx S R0 sp W q
  cst : RxCst Mt0 z o t
  owns : ∀ y ∈ L, y.Owns
  mm : xm ∈ L
  mz : z ∈ L
  mt : t ∈ L
  nm : xm.rep.Norm
  mag : xm.rep.num.mag ≠ 0
  twoNum : t.rep.num = ⟨false, 2, 0⟩
  twoSize : t.rep.len + t.rep.scale = 1
  twoNorm : t.rep.Norm
  sc : Sc = max rs (xm.rep.scale + k)
  rsk : k ≤ rs
  bnd : xm.rep.len + Sc + 1 ≤ B
  size : 2 * B + 2 + k + xm.rep.len + xm.rep.scale < 2 ^ 24
  sizeE : Ee + 2 < 2 ^ 24

/-! ## Bounds of the products and remainders -/

/-- A product's digits and scale. -/
theorem rx_mul_size {a b y : NumRep} {rs : Nat} (ha : NumShape a) (hb : NumShape b)
    (hy : NumShape y) (hn : y.Norm) (he : y.num = Num.mul a.num b.num rs) :
    y.len + y.scale ≤ max (a.len + a.scale + (b.len + b.scale)) (1 + y.scale) ∧
      y.scale ≤ max rs (max a.scale b.scale) := by
  have hsc : y.scale = min (a.scale + b.scale) (max rs (max a.scale b.scale)) := by
    rw [← NumRep.num_scale, he]; rfl
  refine ⟨NumRep.size_le hy hn ?_, by omega⟩
  rw [he]
  show dval a.ds * dval b.ds / _ < _
  have h1 := NumRep.mag_lt ha
  have h2 := NumRep.mag_lt hb
  calc _ ≤ dval a.ds * dval b.ds := Nat.div_le_self _ _
    _ < 10 ^ (a.len + a.scale) * 10 ^ (b.len + b.scale) :=
      Nat.mul_lt_mul_of_lt_of_le h1 (Nat.le_of_lt h2) (Nat.pow_pos (by decide))
    _ = _ := (Nat.pow_add _ _ _).symm

/-- A remainder's digits: those of the modulus at the remainder's scale, and one. -/
theorem rx_mod_size {xm y : NumRep} {a r : Num} {k : Nat} (hx : NumShape xm) (hy : NumShape y)
    (hn : y.Norm) (he : y.num = r) (hr : Dc.BcModel.ModRes a xm.num k r) :
    y.len + y.scale ≤ xm.len + y.scale + 1 ∧ y.scale = max a.scale (xm.scale + k) := by
  have hsc : y.scale = max a.scale (xm.scale + k) := by
    rw [← NumRep.num_scale, he, hr.scale, NumRep.num_scale]
  refine ⟨?_, hsc⟩
  have hm := hr.mag
  rw [NumRep.num_scale] at hm
  have hE : y.num.mag < 10 ^ (xm.len + xm.scale + (max a.scale (xm.scale + k) - xm.scale - k)) := by
    rw [he, Nat.pow_add]
    refine Nat.lt_of_lt_of_le hm (Nat.mul_le_mul_right _ ?_)
    rw [NumRep.num_mag]; exact Nat.le_of_lt (NumRep.mag_lt hx)
  have := NumRep.size_le hy hn hE
  omega

/-! ## The frame of the loop -/

/-- The loop's fixed registers inside the frame: `s1` (`&_zero_`), `s2`
(`mod`), `s3` (`scale`), `s4` (`rscale`), `s6` (`&_two_`), `s7` (the result
slot). -/
structure RxF (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (xm : NumObj) (k rs : Nat) : Prop where
  ra : RxAt S Mt0 M R0 R sp W rxSlots2
  r9 : R 9 = BitVec.ofNat 64 zeroAddr
  r18 : R 18 = BitVec.ofNat 64 xm.rep.p
  r19 : R 19 = BitVec.ofNat 64 k
  r20 : R 20 = BitVec.ofNat 64 rs
  r22 : R 22 = BitVec.ofNat 64 twoAddr
  r23 : R 23 = BitVec.ofNat 64 q

/-- Through register changes off the fixed ones. -/
theorem RxF.regs {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {xm : NumObj} {k rs : Nat} (h : RxF S Mt0 M R0 R sp W q xm k rs) {ks : List Nat}
    (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ [1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 21, 24, 28, 29, 30, 31] :=
      by decide) :
    RxF S Mt0 M R0 R' sp W q xm k rs where
  ra := h.ra.regs hk fun z hz => by have := hks z hz; simp only [rxAll, List.mem_cons, List.not_mem_nil, or_false] at this ⊢; omega
  r9 := by rw [hk.get 9 fun hm => by have := hks 9 hm; simp at this]; exact h.r9
  r18 := by rw [hk.get 18 fun hm => by have := hks 18 hm; simp at this]; exact h.r18
  r19 := by rw [hk.get 19 fun hm => by have := hks 19 hm; simp at this]; exact h.r19
  r20 := by rw [hk.get 20 fun hm => by have := hks 20 hm; simp at this]; exact h.r20
  r22 := by rw [hk.get 22 fun hm => by have := hks 22 hm; simp at this]; exact h.r22
  r23 := by rw [hk.get 23 fun hm => by have := hks 23 hm; simp at this]; exact h.r23

/-- Through a callee that changes the caller-saved registers and, off the
heap, one word `o` of the frame and the bytes below it. -/
theorem RxF.call {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {xm : NumObj} {k rs : Nat} (cx : RxCtx S R0 sp W q) (h : RxF S Mt0 M R0 R sp W q xm k rs)
    (hk : Keeps binClob R' R)
    (hout : ∀ a, OutHeap a → ¬ (sp - 112 ≤ a ∧ a < sp - 80) →
      ¬ frameIn (sp - 112) (W - 112) a → imgM M' a = imgM M a) :
    RxF S Mt0 M' R0 R' sp W q xm k rs := by
  rx_facts cx
  have hk' : Keeps raCallClob R' R := hk.mono (by decide)
  exact
    { ra := h.ra.call (hsp := by omega) (hW := by omega) (hkp := hk') (hag := hout)
        (hst := fun a h1 _ => outHeap_of_ge (by simp only [heapEnd]; omega))
      r9 := by rw [hk'.get 9 (by decide)]; exact h.r9
      r18 := by rw [hk'.get 18 (by decide)]; exact h.r18
      r19 := by rw [hk'.get 19 (by decide)]; exact h.r19
      r20 := by rw [hk'.get 20 (by decide)]; exact h.r20
      r22 := by rw [hk'.get 22 (by decide)]; exact h.r22
      r23 := by rw [hk'.get 23 (by decide)]; exact h.r23 }

/-- A frame word a callee leaves. -/
theorem rx_word {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp W q : Nat} {M M' : Mem}
    (cx : RxCtx S R0 sp W q) {o : Nat} (ho : o ≤ 24)
    (hag : ∀ a, OutHeap a → sp - 112 + o ≤ a → a < sp - 112 + o + 8 → imgM M' a = imgM M a) :
    ldv .ld M' (sp - 112 + o) = ldv .ld M (sp - 112 + o) := by
  rx_facts cx
  exact ldv_congr .ld fun j hj => hag _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))
    (by omega) (by simp only [widthOfM] at hj; omega)

/-! ## The state between the steps -/

/-- The loop's state: the handles `[power, exponent, temp, parity]` holding
`p`, the exponent `m`, `tv`; their words at `sp - 112 + 0, 8, 24, 16`;
`power` in `s0` and `temp` in `s5`. -/
structure RxM (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (xm : NumObj) (k rs B Sc Ee : Nat)
    (hP hE hT hX : RH) (m : Nat) (p tv : Num) : Prop where
  f : RxF S Mt0 M R0 R sp W q xm k rs
  heap : BcHeap S M H F (RList [hP, hE, hT, hX] L)
  own : RHOwn [hP, hE, hT, hX] L
  okP : RHOK L hP
  okE : RHOK L hE
  okT : RHOK L hT
  okX : RHOK L hX
  ex : hE.p ≠ hX.p
  tx : hT.p ≠ hX.p
  vP : RxNum hP p B Sc
  vT : RxNum hT tv B Sc
  vE : RxNum hE ⟨false, m, 0⟩ Ee 0
  w0 : ldv .ld M (sp - 112 + 0) = BitVec.ofNat 64 hP.p
  w8 : ldv .ld M (sp - 112 + 8) = BitVec.ofNat 64 hE.p
  w16 : ldv .ld M (sp - 112 + 16) = BitVec.ofNat 64 hX.p
  w24 : ldv .ld M (sp - 112 + 24) = BitVec.ofNat 64 hT.p
  r8 : R 8 = BitVec.ofNat 64 hP.p
  r21 : R 21 = BitVec.ofNat 64 hT.p

/-- Through register changes off the state's. -/
theorem RxM.regs {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (h : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv) {ks : List Nat}
    (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 24, 28, 29, 30, 31] :=
      by decide) :
    RxM S Mt0 M R0 R' sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv :=
  { h with
    f := h.f.regs hk fun z hz => by have := hks z hz; simp only [rxAll, List.mem_cons, List.not_mem_nil, or_false] at this ⊢; omega
    r8 := by rw [hk.get 8 fun hm => by have := hks 8 hm; simp at this]; exact h.r8
    r21 := by rw [hk.get 21 fun hm => by have := hks 21 hm; simp at this]; exact h.r21 }

/-- The object a handle names, in the heap. -/
theorem RxM.objP {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (h : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv) :
    RH.obj [hP, hE, hT, hX] hP ∈ RList [hP, hE, hT, hX] L := RH.obj_mem (by simp) h.okP
theorem RxM.objE {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (h : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv) :
    RH.obj [hP, hE, hT, hX] hE ∈ RList [hP, hE, hT, hX] L := RH.obj_mem (by simp) h.okE
theorem RxM.objT {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (h : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv) :
    RH.obj [hP, hE, hT, hX] hT ∈ RList [hP, hE, hT, hX] L := RH.obj_mem (by simp) h.okT
theorem RxM.objX {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (h : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv) :
    RH.obj [hP, hE, hT, hX] hX ∈ RList [hP, hE, hT, hX] L := RH.obj_mem (by simp) h.okX

/-! ## The loop's head (`0x800062cc`): the exponent's zero test -/

/-- **The head**: a zero exponent leaves the loop at `0x800063b4`, any other
goes on to the halving at `0x800062f8`. -/
theorem rx_head {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (st : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv)
    (r24 : R 24 = BitVec.ofNat 64 hE.p)
    (hz : ∀ R', RxM S Mt0 M R0 R' sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv →
      R' 24 = BitVec.ofNat 64 hE.p → m = 0 → DW live S Q 0x800063b4#64 R' M)
    (hnz : ∀ R', RxM S Mt0 M R0 R' sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv →
      R' 24 = BitVec.ofNat 64 hE.p → m ≠ 0 → DW live S Q 0x800062f8#64 R' M) :
    DW live S Q 0x800062cc#64 R M := by
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hm : (RH.obj [hP, hE, hT, hX] hE).rep.num.mag = m := by
    rw [RH.obj_num, st.vE.num]
  refine ztest_800062cc hlive hS (hb.nums _ st.objE) (by rw [RH.obj_p]; exact r24)
    (fun R' hk h0 => hz R' (st.regs hk) (by rw [hk.get 24 (by decide)]; exact r24)
      (by rw [← hm]; exact h0))
    (fun R' hk h0 => hnz R' (st.regs hk) (by rw [hk.get 24 (by decide)]; exact r24)
      (by rw [← hm]; exact h0))

/-- A number a handle owns is apart from every other handle's. -/
theorem RList.own_ne {hs1 hs2 : List RH} {L : List NumObj} {y : NumObj} {h : RH}
    (hd : PDist (RList (hs1 ++ .own y :: hs2) L)) (hm : h ∈ hs1 ++ hs2) (hh : RHOK L h) :
    y.rep.p ≠ h.p := by
  rw [RList.own_split] at hd
  have hne := hd.ne
  cases h with
  | own w =>
    have hw : w ∈ rTemps (hs1 ++ hs2) := List.mem_flatMap.mpr ⟨.own w, hm, by simp [RH.tmp]⟩
    rw [rTemps_append] at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact fun e => hne w (List.mem_append_left _ hw) e.symm
    · exact fun e => hne w (List.mem_append_right _ (List.mem_append_left _ hw)) e.symm
  | ref o =>
    obtain ⟨A, B, e, _⟩ := hh
    have ho : o ∈ L := by rw [e]; simp
    exact fun e => hne (rBump (hs1 ++ hs2) o)
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem ho))) e.symm

/-! ## Halving (`0x800062f8`) -/

/-- The halved exponent's bounds. -/
theorem rx_half_num {x y : NumRep} {m Ee : Nat} (hx : NumShape x) (hxn : x.num = ⟨false, m, 0⟩)
    (hxs : x.len + x.scale ≤ Ee) (hxl : 1 ≤ x.len) (hy : NumShape y) (hn : y.Norm)
    (he : y.num = ⟨false, m / 2, 0⟩) : y.len + y.scale ≤ Ee ∧ y.scale ≤ 0 := by
  have hys : y.scale = 0 := by rw [← NumRep.num_scale, he]
  have hm : m < 10 ^ Ee := by
    have := NumRep.mag_lt hx
    rw [← NumRep.num_mag, hxn] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) hxs)
  have := NumRep.size_le hy hn (E := Ee) (by rw [he]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm)
  omega

/-- **The halving**: `bc_divmod (exponent, _two_, &exponent, &parity, 0)`
replaces the exponent `m` by `m / 2` and the parity by `m % 2`; on to
`0x80006310`. -/
theorem rx_halve {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm z o t : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (env : RxEnv S Mt0 R0 sp W q L xm z o t k rs B Sc Ee) (hoom : DmOom live S Q Mt0 sp W)
    (st : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv)
    (r24 : R 24 = BitVec.ofNat 64 hE.p)
    (hnext : ∀ R' M' H' F' yq yr, RxM S Mt0 M' R0 R' sp W q H' F' L xm k rs B Sc Ee
      hP (.own yq) hT (.own yr) (m / 2) p tv → yr.rep.num = ⟨false, m % 2, 0⟩ →
      DW live S Q 0x80006310#64 R' M') :
    DW live S Q 0x800062f8#64 R M := by
  have cx := env.cx
  rx_facts cx
  have hsf := cx.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.f.ra
  have h2 := ra.r2
  have hcs := env.cst.transport cx ra.out
  have hcst : ∀ b ∈ accAddrs twoAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have hEn := hb.nums _ st.objE
  have hEs := hEn.shape
  have vEn : (RH.obj [hP, hE, hT, hX] hE).rep.num = ⟨false, m, 0⟩ := by
    rw [RH.obj_num]; exact st.vE.num
  have hEl : (RH.obj [hP, hE, hT, hX] hE).rep.len = hE.base.rep.len := RH.obj_len _ _
  have hEc : (RH.obj [hP, hE, hT, hX] hE).rep.scale = hE.base.rep.scale := RH.obj_scale _ _
  have hvs := st.vE.size
  have hvl := st.vE.len
  have hsE := env.sizeE
  have htw : (BitVec.ofNat 64 twoAddr).toNat = twoAddr := rfl
  have hldt : LdOK twoAddr 8 := by simp only [LdOK, twoAddr, tohostAddr]; omega
  bc_run hlive hS [h2, st.f.r22, htw, hcs.two, r24] at 0x80005fd0
  all_goals first | exact hldt | exact hcst | exact frame_acc hsf (by omega) (by omega) | skip
  refine rx_halveH (u1 := RH.obj [hP, hE, hT, hX] hE) (u2 := rBump [hP, hE, hT, hX] t)
    (z := rBump [hP, hE, hT, hX] z) hlive cx hoom ra.out hb st.own st.okE st.okX st.ex
    ⟨st.objE, RList.mem_caller _ env.mt, RList.mem_caller _ env.mz,
      (RH.obj_norm _ _).mpr st.vE.norm, env.twoNorm, by omega,
      by have := env.twoSize; show _ + _ + 0 + t.rep.len + t.rep.scale < _; omega,
      KZero.rBump _ (Nat.le_refl _) hcs.zero, hcs.mulBase, st.own.all⟩
    (by show t.rep.num.mag ≠ 0; rw [env.twoNum]; decide) st.w8 st.w16
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp [r24, RH.obj_p])
    (by bsimp []; rfl) (by bsimp [h2]) (by bsimp [h2]) (by bsimp []) ?_
  intro m' hm R1 M1 H1 F1 yq yr hk1 _ hb1 hq hr hout1
  rw [vEn, show (rBump [hP, hE, hT, hX] t).rep.num = t.rep.num from rfl, env.twoNum,
    Dc.BcModel.divmod_two] at hm
  simp only [Option.some.injEq] at hm
  subst hm
  have hmq : yq ∈ RList [hP, .own yq, hT, .own yr] L :=
    RH.obj_mem (h := .own yq) (by simp) ⟨hq.refs, hq.owns⟩
  have hmr : yr ∈ RList [hP, .own yq, hT, .own yr] L :=
    RH.obj_mem (h := .own yr) (by simp) ⟨hr.refs, hr.owns⟩
  have hqp : yq.rep.p = yq.sb.pay := (hb1.blocks yq hmq).sPay
  have hrp : yr.rep.p = yr.sb.pay := (hb1.blocks yr hmr).sPay
  have hne : yr.rep.p ≠ yq.rep.p := by
    have hd := hb1.pdist
    have e : RList [hP, .own yq, hT, .own yr] L = rTemps [hP] ++ yq ::
        (rTemps [hT, .own yr] ++ L.map (rBump ([hP] ++ [hT, .own yr]))) :=
      RList.own_split [hP] [hT, .own yr] yq L
    rw [e] at hd
    refine hd.ne yr (List.mem_append_right _ (List.mem_append_left _ ?_))
    exact List.mem_flatMap.mpr ⟨.own yr, by simp, by simp [RH.tmp]⟩
  have hag : ∀ a, OutHeap a → ¬ (sp - 112 ≤ a ∧ a < sp - 80) →
      ¬ frameIn (sp - 112) (W - 112) a → imgM M1 a = imgM M a := fun a h1 h2 h3 =>
    hout1 a h1 (by simp only [slotBytes]; omega) (by simp only [slotBytes]; omega) h3
  have hw : ∀ o, o = 0 ∨ o = 24 → ldv .ld M1 (sp - 112 + o) = ldv .ld M (sp - 112 + o) :=
    fun o ho => rx_word cx (by omega) fun a h1 h2' h3 =>
      hout1 a h1 (by simp only [slotBytes]; omega) (by simp only [slotBytes]; omega)
        (by simp only [frameIn]; omega)
  have hhalf := rx_half_num hEs vEn (by rw [hEl, hEc]; exact hvs) (by rw [hEl]; exact hvl)
    (hb1.nums yq hmq).shape hq.norm hq.num
  have f1 := RxF.call cx (st.f.regs (ks := [1, 10, 11, 12, 13, 14]) (by keeps_tac Keeps.refl _ _))
    hk1 hag
  have hown : RHOwn [hP, .own yq, hT, .own yr] L :=
    (show RHOwn ([hP, .own yq, hT] ++ hX :: []) L from
      (show RHOwn ([hP] ++ hE :: [hT, hX]) L from st.own).set hq.owns).set hr.owns
  bsimp []
  exact hnext R1 M1 H1 F1 yq yr
    { f := f1
      heap := hb1
      own := hown
      okP := st.okP
      okE := ⟨hq.refs, hq.owns⟩
      okT := st.okT
      okX := ⟨hr.refs, hr.owns⟩
      ex := fun e => hne e.symm
      tx := fun e => RList.own_ne (hs1 := [hP, .own yq, hT]) (hs2 := [])
        (show PDist (RList ([hP, .own yq, hT] ++ .own yr :: []) L) from hb1.pdist) (by simp) st.okT
        e.symm
      vP := st.vP
      vT := st.vT
      vE := ⟨hq.num, hq.norm, hq.pos, hhalf.1, hhalf.2⟩
      w0 := by rw [hw 0 (.inl rfl)]; exact st.w0
      w8 := by rw [hq.slot, ← hqp]; rfl
      w16 := by rw [hr.slot, ← hrp]; rfl
      w24 := by rw [hw 24 (.inr rfl)]; exact st.w24
      r8 := by rw [hk1.get 8 (by decide)]; bsimp [st.r8]
      r21 := by rw [hk1.get 21 (by decide)]; bsimp [st.r21] } hr.num

/-- A number a handle owns is apart from the caller's. -/
theorem RList.own_ne_caller {hs : List RH} {L : List NumObj} {y w : NumObj}
    (hd : PDist (RList hs L)) (hy : .own y ∈ hs) (hw : w ∈ L) : y.rep.p ≠ w.rep.p := by
  unfold PDist RList at hd
  rw [List.map_append] at hd
  have hyT : y ∈ rTemps hs := List.mem_flatMap.mpr ⟨.own y, hy, by simp [RH.tmp]⟩
  have h1 : y.rep.p ∈ (rTemps hs).map (·.rep.p) := List.mem_map_of_mem hyT
  have h2 :=
    List.mem_map_of_mem (f := fun x : NumObj => x.rep.p) (List.mem_map_of_mem (f := rBump hs) hw)
  exact (List.nodup_append.mp hd).2.2 _ h1 _ h2

/-! ## The parity's test (`0x80006310`) -/

/-- Distinct words of distinct addresses. -/
theorem rx_ofNat_ne {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) :
    BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun e => h (by
  have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega)

/-- **The parity test**: a parity `b` apart from `_zero_`, nonzero, goes on
to the multiplication of `temp` at `0x80006348`; zero skips it to
`0x80006378`. -/
theorem rx_par {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm z o t : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (env : RxEnv S Mt0 R0 sp W q L xm z o t k rs B Sc Ee)
    (st : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv)
    (hxz : hX.p ≠ z.rep.p) {b : Nat} (hxb : hX.base.rep.num.mag = b)
    (hodd : ∀ R', RxM S Mt0 M R0 R' sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv → b ≠ 0 →
      DW live S Q 0x80006348#64 R' M)
    (heven : ∀ R', RxM S Mt0 M R0 R' sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv → b = 0 →
      DW live S Q 0x80006378#64 R' M) :
    DW live S Q 0x80006310#64 R M := by
  have cx := env.cx
  rx_facts cx
  have hsf := cx.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.f.ra
  have h2 := ra.r2
  have hcs := env.cst.transport cx ra.out
  have hcst : ∀ b ∈ accAddrs zeroAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have htz : (BitVec.ofNat 64 zeroAddr).toNat = zeroAddr := rfl
  have hldz : LdOK zeroAddr 8 := by simp only [LdOK, zeroAddr, tohostAddr]; omega
  have hXn := hb.nums _ st.objX
  have hXs := hXn.shape
  have hZs := (hb.nums _ (RList.mem_caller [hP, hE, hT, hX] env.mz)).shape
  have hxp : (RH.obj [hP, hE, hT, hX] hX).rep.p = hX.p := RH.obj_p _ _
  have hzp : (rBump [hP, hE, hT, hX] z).rep.p = z.rep.p := rfl
  have hpX := hXs.pHi
  have hpZ := hZs.pHi
  simp only [heapEnd] at hpX hpZ
  have hne : BitVec.ofNat 64 hX.p ≠ BitVec.ofNat 64 z.rep.p :=
    rx_ofNat_ne (by omega) (by omega) hxz
  have hmag : (RH.obj [hP, hE, hT, hX] hX).rep.num.mag = b := by rw [RH.obj_num]; exact hxb
  bc_run hlive hS [h2, st.w16, st.f.r9, htz, hcs.zero.glob] at 0x8000631c 0x80006378
  all_goals first | exact hldz | exact hcst | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first
    | (intro h; exact absurd h hne)
    | (intro _
       refine ztest_8000631c hlive hS hXn (by bsimp [hxp]) (fun R' hk h0 => heven R' (st.regs (hk.trans
         (by keeps_tac Keeps.refl _ _) : Keeps [13, 14, 15] R' R)) (hmag ▸ h0)) (fun R' hk h0 => hodd R'
         (st.regs (hk.trans (by keeps_tac Keeps.refl _ _) : Keeps [13, 14, 15] R' R)) (hmag ▸ h0)))

/-! ## A product reduced modulo `mod` (`0x80006348`, `0x80006378`) -/

/-- A product of two loop numbers: at most `2 B` digits, scale at most `Sc`. -/
theorem RxEnv.mulB {S : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {L : List NumObj} {xm z o t : NumObj} {k rs B Sc Ee : Nat}
    (env : RxEnv S Mt0 R0 sp W q L xm z o t k rs B Sc Ee) {a b : RH} {va vb : Num}
    (ha : RxNum a va B Sc) (hb : RxNum b vb B Sc) (sha : NumShape a.base.rep)
    (shb : NumShape b.base.rep) {y : NumObj} (hy : y.rep.num = Num.mul va vb rs) (hyn : y.rep.Norm)
    (shy : NumShape y.rep) : y.rep.len + y.rep.scale ≤ 2 * B ∧ y.rep.scale ≤ Sc := by
  rw [← ha.num, ← hb.num] at hy
  have h := rx_mul_size sha shb shy hyn hy
  have := ha.size; have := hb.size; have := ha.scale; have := hb.scale
  have := env.sc; have := env.bnd
  omega

/-- A product reduced modulo `mod`: at most `B` digits, scale at most `Sc`. -/
theorem RxEnv.modB {S : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {L : List NumObj} {xm z o t : NumObj} {k rs B Sc Ee : Nat}
    (env : RxEnv S Mt0 R0 sp W q L xm z o t k rs B Sc Ee) {y y2 : NumObj} {r : Num}
    (hys : y.rep.scale ≤ Sc) (hs : List RH) (shm : NumShape (rBump hs xm).rep)
    (hr : Num.modulo y.rep.num (rBump hs xm).rep.num k = some r) (hy2 : NewNum r y2)
    (shy2 : NumShape y2.rep) : RxNum (.own y2) r B Sc := by
  obtain ⟨r', hr', hm⟩ := Dc.BcModel.modulo_res (a := y.rep.num) (b := (rBump hs xm).rep.num) (k := k)
    env.mag
  rw [hr] at hr'
  cases hr'
  have h := rx_mod_size shm shy2 hy2.norm hy2.num hm
  rw [NumRep.num_scale] at h
  have e1 : (rBump hs xm).rep.len = xm.rep.len := rfl
  have e2 : (rBump hs xm).rep.scale = xm.rep.scale := rfl
  have := env.sc; have := env.bnd
  exact ⟨hy2.num, hy2.norm, hy2.pos, by show y2.rep.len + y2.rep.scale ≤ B; omega,
    by show y2.rep.scale ≤ Sc; omega⟩

/-- **`temp = temp · power % mod`** from `0x80006348`, on to `0x80006378`. -/
theorem rx_tmul {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm z o t : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (env : RxEnv S Mt0 R0 sp W q L xm z o t k rs B Sc Ee) (hoom : DmOom live S Q Mt0 sp W)
    (st : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv)
    (hnext : ∀ R' M' H' F' y, RxM S Mt0 M' R0 R' sp W q H' F' L xm k rs B Sc Ee
      hP hE (.own y) hX m p ((Num.modulo (Num.mul tv p rs) xm.rep.num k).getD tv) →
      DW live S Q 0x80006378#64 R' M') :
    DW live S Q 0x80006348#64 R M := by
  have cx := env.cx
  rx_facts cx
  have hsf := cx.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.f.ra
  have h2 := ra.r2
  have hcs := env.cst.transport cx ra.out
  have shP := (hb.nums _ st.objP).shape
  have shT := (hb.nums _ st.objT).shape
  have shm := (hb.nums _ (RList.mem_caller [hP, hE, hT, hX] env.mm)).shape
  have vP := st.vP
  have vT := st.vT
  have hPn : (RH.obj [hP, hE, hT, hX] hP).rep.num = p := by rw [RH.obj_num]; exact vP.num
  have hTn : (RH.obj [hP, hE, hT, hX] hT).rep.num = tv := by rw [RH.obj_num]; exact vT.num
  have vP' := vP.obj [hP, hE, hT, hX]
  have vT' := vT.obj [hP, hE, hT, hX]
  have hsP : (RH.obj [hP, hE, hT, hX] hP).rep.len + (RH.obj [hP, hE, hT, hX] hP).rep.scale ≤ B :=
    vP'.size
  have hsT : (RH.obj [hP, hE, hT, hX] hT).rep.len + (RH.obj [hP, hE, hT, hX] hT).rep.scale ≤ B :=
    vT'.size
  have hlP : 1 ≤ (RH.obj [hP, hE, hT, hX] hP).rep.len := vP'.len
  have hlT : 1 ≤ (RH.obj [hP, hE, hT, hX] hT).rep.len := vT'.len
  have hsz := env.size; have hbd := env.bnd; have hsc := env.sc; have hrk := env.rsk
  bc_run hlive hS [h2, st.r21, st.r8, st.f.r20] at 0x8000573c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine rx_mulH (hs1 := [hP, hE]) (h := hT) (hs2 := [hX]) (o := 24)
    (u1 := RH.obj [hP, hE, hT, hX] hT) (u2 := RH.obj [hP, hE, hT, hX] hP)
    (z := rBump [hP, hE, hT, hX] z) (k := rs) hlive cx hoom (by omega) rfl ra.out hb st.own st.okT
    ⟨st.objT, st.objP, RList.mem_caller _ env.mz, by omega, by omega, by omega, by omega,
      KZero.rBump _ (Nat.le_refl _) (hcs.zero.mono (by omega)), hcs.mulBase⟩
    st.w24 (by bsimp [h2]) (by bsimp []; try decide) (by bsimp [st.r21, RH.obj_p])
    (by bsimp [st.r8, RH.obj_p]) (by bsimp [h2]) (by bsimp [st.f.r20]) ?_
  intro R1 M1 H1 F1 y hk1 hb1 hmr hout1
  rw [hTn, hPn] at hmr
  have hmy : y ∈ RList [hP, hE, .own y, hX] L := RH.obj_mem (h := .own y) (by simp) ⟨hmr.refs, hmr.owns⟩
  have shy := (hb1.nums y hmy).shape
  have hyB := env.mulB vT' vP' shT shP hmr.num hmr.norm shy
  have hag1 : ∀ a, OutHeap a → ¬ (sp - 112 ≤ a ∧ a < sp - 80) →
      ¬ frameIn (sp - 112) (W - 112) a → imgM M1 a = imgM M a := fun a h1 h2 h3 =>
    hout1 a h1 (by simp only [slotBytes]; omega) h3
  have f1 := RxF.call cx (st.f.regs (ks := [1, 10, 11, 12, 13]) (by keeps_tac Keeps.refl _ _))
    hk1 hag1
  have hown1 : RHOwn [hP, hE, .own y, hX] L :=
    (show RHOwn ([hP, hE] ++ hT :: [hX]) L from st.own).set hmr.owns
  have hS1 : HeapOwn S := fun a h1 h2 => hb1.heap.own a h1 h2
  have h2' := f1.ra.r2
  have hcs1 := env.cst.transport cx f1.ra.out
  have shm := (hb1.nums _ (RList.mem_caller [hP, hE, .own y, hX] env.mm)).shape
  have e1 : (rBump [hP, hE, .own y, hX] xm).rep.len = xm.rep.len := rfl
  have e2 : (rBump [hP, hE, .own y, hX] xm).rep.scale = xm.rep.scale := rfl
  bsimp []
  bc_run hlive hS1 [h2', hmr.slot, f1.r18, f1.r19] at 0x80005fd0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine rx_modH (hs1 := [hP, hE]) (h := .own y) (hs2 := [hX]) (o := 24) (u1 := y)
    (u2 := rBump [hP, hE, .own y, hX] xm) (z := rBump [hP, hE, .own y, hX] z) (k := k)
    hlive cx hoom (by omega) rfl f1.ra.out hb1 hown1 ⟨hmr.refs, hmr.owns⟩
    ⟨hmy, RList.mem_caller _ env.mm, RList.mem_caller _ env.mz, hmr.norm, env.nm, hmr.pos,
      by omega, KZero.rBump _ (Nat.le_refl _) hcs1.zero, hcs1.mulBase, hown1.all⟩ env.mag hmr.slot
    (by bsimp [h2']) (by bsimp []; try decide) (by bsimp [hmr.slot]) (by bsimp [f1.r18]; try rfl)
    (by bsimp []) (by bsimp [h2']) (by bsimp [f1.r19]) ?_
  intro r hr R2 M2 H2 F2 y2 hk2 _ hb2 hres hout2
  have hmy2 : y2 ∈ RList [hP, hE, .own y2, hX] L :=
    RH.obj_mem (h := .own y2) (by simp) ⟨hres.refs, hres.owns⟩
  have hp2 : y2.rep.p = y2.sb.pay := (hb2.blocks y2 hmy2).sPay
  have hw2 : ldv .ld M2 (sp - 112 + 24) = BitVec.ofNat 64 y2.rep.p := by rw [hres.slot, hp2]
  have vT2 := env.modB hyB.2 _ shm hr hres.toNewNum (hb2.nums y2 hmy2).shape
  have hval : (Num.modulo (Num.mul tv p rs) xm.rep.num k).getD tv = r := by
    rw [← hmr.num, show xm.rep.num = (rBump [hP, hE, .own y, hX] xm).rep.num from rfl, hr]; rfl
  have hag2 : ∀ a, OutHeap a → ¬ (sp - 112 ≤ a ∧ a < sp - 80) →
      ¬ frameIn (sp - 112) (W - 112) a → imgM M2 a = imgM M1 a := fun a h1 h2 h3 =>
    hout2 a h1 (by simp only [slotBytes]; omega) h3
  have f2 := RxF.call cx (f1.regs (ks := [1, 10, 11, 12, 13, 14]) (by keeps_tac Keeps.refl _ _))
    hk2 hag2
  have hw : ∀ o, o ≤ 16 → ldv .ld M2 (sp - 112 + o) = ldv .ld M (sp - 112 + o) := fun o ho =>
    (rx_word cx (by omega) fun a h1 h2' h3 => hout2 a h1 (by simp only [slotBytes]; omega)
      (by simp only [frameIn]; omega)).trans
    (rx_word cx (by omega) fun a h1 h2' h3 => hout1 a h1 (by simp only [slotBytes]; omega)
      (by simp only [frameIn]; omega))
  have hown2 : RHOwn [hP, hE, .own y2, hX] L :=
    (show RHOwn ([hP, hE] ++ (.own y) :: [hX]) L from hown1).set hres.owns
  have h2'' := f2.ra.r2
  bsimp []
  bc_run hlive (fun a h1 h2 => hb2.heap.own a h1 h2) [h2'', hw2] at 0x80006378
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact hnext _ M2 H2 F2 y2
    { f := f2.regs (ks := [21]) (by keeps_tac Keeps.refl _ _)
      heap := hb2
      own := hown2
      okP := st.okP
      okE := st.okE
      okT := ⟨hres.refs, hres.owns⟩
      okX := st.okX
      ex := st.ex
      tx := RList.own_ne (hs1 := [hP, hE]) (hs2 := [hX])
        (show PDist (RList ([hP, hE] ++ .own y2 :: [hX]) L) from hb2.pdist) (by simp) st.okX
      vP := st.vP
      vT := by rw [hval]; exact vT2
      vE := st.vE
      w0 := by rw [hw 0 (by omega)]; exact st.w0
      w8 := by rw [hw 8 (by omega)]; exact st.w8
      w16 := by rw [hw 16 (by omega)]; exact st.w16
      w24 := hw2
      r8 := by
        bsimp []; rw [hk2.get 8 (by decide)]; bsimp []; rw [hk1.get 8 (by decide)]; bsimp [st.r8]
      r21 := by bsimp []; try rfl }

/-- **`power = power² % mod`** from `0x80006378`, then the reloads of `exponent` and
`power` and the loop's back edge to `0x800062cc` (the exponent is apart from
`_zero_`). -/
theorem rx_psq {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm z o t : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (env : RxEnv S Mt0 R0 sp W q L xm z o t k rs B Sc Ee) (hoom : DmOom live S Q Mt0 sp W)
    (st : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv)
    (hez : hE.p ≠ z.rep.p)
    (hnext : ∀ R' M' H' F' y, RxM S Mt0 M' R0 R' sp W q H' F' L xm k rs B Sc Ee
      (.own y) hE hT hX m ((Num.modulo (Num.mul p p rs) xm.rep.num k).getD p) tv →
      R' 24 = BitVec.ofNat 64 hE.p → DW live S Q 0x800062cc#64 R' M') :
    DW live S Q 0x80006378#64 R M := by
  have cx := env.cx
  rx_facts cx
  have hsf := cx.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.f.ra
  have h2 := ra.r2
  have hcs := env.cst.transport cx ra.out
  have shP := (hb.nums _ st.objP).shape
  have shT := (hb.nums _ st.objT).shape
  have shm := (hb.nums _ (RList.mem_caller [hP, hE, hT, hX] env.mm)).shape
  have vP := st.vP
  have vT := st.vT
  have hPn : (RH.obj [hP, hE, hT, hX] hP).rep.num = p := by rw [RH.obj_num]; exact vP.num
  have hTn : (RH.obj [hP, hE, hT, hX] hT).rep.num = tv := by rw [RH.obj_num]; exact vT.num
  have vP' := vP.obj [hP, hE, hT, hX]
  have vT' := vT.obj [hP, hE, hT, hX]
  have hsP : (RH.obj [hP, hE, hT, hX] hP).rep.len + (RH.obj [hP, hE, hT, hX] hP).rep.scale ≤ B :=
    vP'.size
  have hsT : (RH.obj [hP, hE, hT, hX] hT).rep.len + (RH.obj [hP, hE, hT, hX] hT).rep.scale ≤ B :=
    vT'.size
  have hlP : 1 ≤ (RH.obj [hP, hE, hT, hX] hP).rep.len := vP'.len
  have hlT : 1 ≤ (RH.obj [hP, hE, hT, hX] hT).rep.len := vT'.len
  have hsz := env.size; have hbd := env.bnd; have hsc := env.sc; have hrk := env.rsk
  bc_run hlive hS [h2, st.r8, st.f.r20] at 0x8000573c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine rx_mulH (hs1 := []) (h := hP) (hs2 := [hE, hT, hX]) (o := 0)
    (u1 := RH.obj [hP, hE, hT, hX] hP) (u2 := RH.obj [hP, hE, hT, hX] hP)
    (z := rBump [hP, hE, hT, hX] z) (k := rs) hlive cx hoom (by omega) rfl ra.out hb st.own st.okP
    ⟨st.objP, st.objP, RList.mem_caller _ env.mz, by omega, by omega, by omega, by omega,
      KZero.rBump _ (Nat.le_refl _) (hcs.zero.mono (by omega)), hcs.mulBase⟩
    st.w0 (by bsimp [h2]) (by bsimp []; try decide) (by bsimp [st.r8, RH.obj_p])
    (by bsimp [st.r8, RH.obj_p]) (by bsimp [h2]) (by bsimp [st.f.r20]) ?_
  intro R1 M1 H1 F1 y hk1 hb1 hmr hout1
  rw [hPn] at hmr
  have hmy : y ∈ RList [.own y, hE, hT, hX] L := RH.obj_mem (h := .own y) (by simp) ⟨hmr.refs, hmr.owns⟩
  have shy := (hb1.nums y hmy).shape
  have hyB := env.mulB vP' vP' shP shP hmr.num hmr.norm shy
  have hag1 : ∀ a, OutHeap a → ¬ (sp - 112 ≤ a ∧ a < sp - 80) →
      ¬ frameIn (sp - 112) (W - 112) a → imgM M1 a = imgM M a := fun a h1 h2 h3 =>
    hout1 a h1 (by simp only [slotBytes]; omega) h3
  have f1 := RxF.call cx (st.f.regs (ks := [1, 10, 11, 12, 13]) (by keeps_tac Keeps.refl _ _))
    hk1 hag1
  have hown1 : RHOwn [.own y, hE, hT, hX] L :=
    (show RHOwn ([] ++ hP :: [hE, hT, hX]) L from st.own).set hmr.owns
  have hS1 : HeapOwn S := fun a h1 h2 => hb1.heap.own a h1 h2
  have h2' := f1.ra.r2
  have hcs1 := env.cst.transport cx f1.ra.out
  have shm := (hb1.nums _ (RList.mem_caller [.own y, hE, hT, hX] env.mm)).shape
  have e1 : (rBump [.own y, hE, hT, hX] xm).rep.len = xm.rep.len := rfl
  have e2 : (rBump [.own y, hE, hT, hX] xm).rep.scale = xm.rep.scale := rfl
  bsimp []
  bc_run hlive hS1 [h2', (show ldv .ld M1 (sp - 112) = _ from hmr.slot), f1.r18, f1.r19] at 0x80005fd0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine rx_modH (hs1 := []) (h := .own y) (hs2 := [hE, hT, hX]) (o := 0) (u1 := y)
    (u2 := rBump [.own y, hE, hT, hX] xm) (z := rBump [.own y, hE, hT, hX] z) (k := k)
    hlive cx hoom (by omega) rfl f1.ra.out hb1 hown1 ⟨hmr.refs, hmr.owns⟩
    ⟨hmy, RList.mem_caller _ env.mm, RList.mem_caller _ env.mz, hmr.norm, env.nm, hmr.pos,
      by omega, KZero.rBump _ (Nat.le_refl _) hcs1.zero, hcs1.mulBase, hown1.all⟩ env.mag hmr.slot
    (by bsimp [h2']) (by bsimp []; try decide) (by bsimp [hmr.slot]) (by bsimp [f1.r18]; try rfl)
    (by bsimp []) (by bsimp [h2']) (by bsimp [f1.r19]) ?_
  intro r hr R2 M2 H2 F2 y2 hk2 _ hb2 hres hout2
  have hmy2 : y2 ∈ RList [.own y2, hE, hT, hX] L :=
    RH.obj_mem (h := .own y2) (by simp) ⟨hres.refs, hres.owns⟩
  have hp2 : y2.rep.p = y2.sb.pay := (hb2.blocks y2 hmy2).sPay
  have hw2 : ldv .ld M2 (sp - 112 + 0) = BitVec.ofNat 64 y2.rep.p := by rw [hres.slot, hp2]
  have vT2 := env.modB hyB.2 _ shm hr hres.toNewNum (hb2.nums y2 hmy2).shape
  have hval : (Num.modulo (Num.mul p p rs) xm.rep.num k).getD p = r := by
    rw [← hmr.num, show xm.rep.num = (rBump [.own y, hE, hT, hX] xm).rep.num from rfl, hr]; rfl
  have hag2 : ∀ a, OutHeap a → ¬ (sp - 112 ≤ a ∧ a < sp - 80) →
      ¬ frameIn (sp - 112) (W - 112) a → imgM M2 a = imgM M1 a := fun a h1 h2 h3 =>
    hout2 a h1 (by simp only [slotBytes]; omega) h3
  have f2 := RxF.call cx (f1.regs (ks := [1, 10, 11, 12, 13, 14]) (by keeps_tac Keeps.refl _ _))
    hk2 hag2
  have hw : ∀ o, 8 ≤ o → o ≤ 24 → ldv .ld M2 (sp - 112 + o) = ldv .ld M (sp - 112 + o) := fun o ho ho' =>
    (rx_word cx (by omega) fun a h1 h2' h3 => hout2 a h1 (by simp only [slotBytes]; omega)
      (by simp only [frameIn]; omega)).trans
    (rx_word cx (by omega) fun a h1 h2' h3 => hout1 a h1 (by simp only [slotBytes]; omega)
      (by simp only [frameIn]; omega))
  have hown2 : RHOwn [.own y2, hE, hT, hX] L :=
    (show RHOwn ([] ++ (.own y) :: [hE, hT, hX]) L from hown1).set hres.owns
  have h2'' := f2.ra.r2
  bsimp []
  have hcs2 := env.cst.transport cx f2.ra.out
  have hcst : ∀ b ∈ accAddrs zeroAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have htz : (BitVec.ofNat 64 zeroAddr).toNat = zeroAddr := rfl
  have hldz : LdOK zeroAddr 8 := by simp only [LdOK, zeroAddr, tohostAddr]; omega
  have hw8 : ldv .ld M2 (sp - 112 + 8) = BitVec.ofNat 64 hE.p := by
    rw [hw 8 (by omega) (by omega)]; exact st.w8
  have shE := (hb2.nums _ (RH.obj_mem (hs := [.own y2, hE, hT, hX]) (by simp) st.okE)).shape
  have shZ := (hb2.nums _ (RList.mem_caller [.own y2, hE, hT, hX] env.mz)).shape
  have hpE := shE.pHi
  have hpZ := shZ.pHi
  rw [RH.obj_p] at hpE
  have hpZ' : (rBump [.own y2, hE, hT, hX] z).rep.p = z.rep.p := rfl
  simp only [heapEnd] at hpE hpZ
  have hne : BitVec.ofNat 64 hE.p ≠ BitVec.ofNat 64 z.rep.p := rx_ofNat_ne (by omega) (by omega) hez
  bc_run hlive (fun a h1 h2 => hb2.heap.own a h1 h2) [h2'', (show ldv .ld M2 (sp - 112) = _ from hw2), hw8, f2.r9, htz, hcs2.zero.glob]
    at 0x800062cc 0x800063b4
  all_goals first | exact hldz | exact hcst | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first
    | (intro h; exact absurd h hne)
    | (intro h; exact absurd hne h)
    | (intro _
       refine hnext _ M2 H2 F2 y2
        { f := f2.regs (ks := [8, 15, 24]) (by keeps_tac Keeps.refl _ _)
          heap := hb2
          own := hown2
          okP := ⟨hres.refs, hres.owns⟩
          okE := st.okE
          okT := st.okT
          okX := st.okX
          ex := st.ex
          tx := st.tx
          vP := by rw [hval]; exact vT2
          vT := st.vT
          vE := st.vE
          w0 := hw2
          w8 := hw8
          w16 := by rw [hw 16 (by omega) (by omega)]; exact st.w16
          w24 := by rw [hw 24 (by omega) (by omega)]; exact st.w24
          r8 := by bsimp []; try rfl
          r21 := by
            bsimp []; rw [hk2.get 21 (by decide)]; bsimp []; rw [hk1.get 21 (by decide)]
            bsimp [st.r21] } (by bsimp []))

/-! ## One iteration and the loop -/

/-- **One iteration** from the halving at `0x800062f8` (exponent `m ≠ 0`)
back to the head `0x800062cc`. -/
theorem rx_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm z o t : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num}
    (env : RxEnv S Mt0 R0 sp W q L xm z o t k rs B Sc Ee) (hoom : DmOom live S Q Mt0 sp W)
    (st : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv)
    (r24 : R 24 = BitVec.ofNat 64 hE.p)
    (hnext : ∀ R' M' H' F' hP' hE' hT' hX', RxM S Mt0 M' R0 R' sp W q H' F' L xm k rs B Sc Ee
      hP' hE' hT' hX' (m / 2) ((Num.modulo (Num.mul p p rs) xm.rep.num k).getD p)
      (if m % 2 = 0 then tv else (Num.modulo (Num.mul tv p rs) xm.rep.num k).getD tv) →
      R' 24 = BitVec.ofNat 64 hE'.p → DW live S Q 0x800062cc#64 R' M') :
    DW live S Q 0x800062f8#64 R M := by
  refine rx_halve hlive env hoom st r24 fun R1 M1 H1 F1 yq yr st1 hyr => ?_
  have hd := st1.heap.pdist
  have hxz : (RH.own yr).p ≠ z.rep.p := RList.own_ne_caller hd (by simp) env.mz
  have hez : (RH.own yq).p ≠ z.rep.p := RList.own_ne_caller hd (by simp) env.mz
  refine rx_par hlive env st1 hxz (b := m % 2) (by show yr.rep.num.mag = _; rw [hyr])
    (fun R2 st2 hb => ?_) (fun R2 st2 hb => ?_)
  · refine rx_tmul hlive env hoom st2 fun R3 M3 H3 F3 y st3 => ?_
    refine rx_psq hlive env hoom st3 hez fun R4 M4 H4 F4 y4 st4 h24 => ?_
    simp only [hb, ↓reduceIte] at hnext
    exact hnext R4 M4 H4 F4 _ _ _ _ st4 h24
  · refine rx_psq hlive env hoom st2 hez fun R4 M4 H4 F4 y4 st4 h24 => ?_
    simp only [hb, ↓reduceIte] at hnext
    exact hnext R4 M4 H4 F4 _ _ _ _ st4 h24

/-- **The loop** from its head `0x800062cc` with the exponent `m`, `power`
`p` and `temp` `tv`: it leaves at `0x800063b4` with `temp` holding
`Num.raisemodLoop`'s result. -/
theorem rx_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {L : List NumObj} {xm z o t : NumObj} {k rs B Sc Ee : Nat}
    (env : RxEnv S Mt0 R0 sp W q L xm z o t k rs B Sc Ee) (hoom : DmOom live S Q Mt0 sp W) :
    ∀ m {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {hP hE hT hX : RH} {p tv : Num},
      RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv →
      R 24 = BitVec.ofNat 64 hE.p →
      (∀ R' M' H' F' hP' hE' hT' hX' m' p', RxM S Mt0 M' R0 R' sp W q H' F' L xm k rs B Sc Ee
        hP' hE' hT' hX' m' p' (Num.raisemodLoop xm.rep.num k rs (m + 1) ⟨false, m, 0⟩ p tv) →
        R' 24 = BitVec.ofNat 64 hE'.p → DW live S Q 0x800063b4#64 R' M') →
      DW live S Q 0x800062cc#64 R M := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro M R H F hP hE hT hX p tv st r24 hexit
    refine rx_head hlive st r24 (fun R' st' r24' h0 => ?_) (fun R' st' r24' h0 => ?_)
    · subst h0
      refine hexit R' M H F hP hE hT hX 0 p ?_ r24'
      rw [Dc.BcModel.raisemodLoop_zero]
      exact st'
    · refine rx_body hlive env hoom st' r24' fun R2 M2 H2 F2 hP2 hE2 hT2 hX2 st2 h24 => ?_
      refine ih (m / 2) (by omega) st2 h24 fun R3 M3 H3 F3 hP3 hE3 hT3 hX3 m3 p3 st3 h3 => ?_
      rw [← Dc.BcModel.raisemodLoop_step _ _ _ _ _ _ h0] at st3
      exact hexit R3 M3 H3 F3 hP3 hE3 hT3 hX3 m3 p3 st3 h3

end Dc.Mach
