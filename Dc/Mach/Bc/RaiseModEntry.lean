import Dc.Mach.Bc.RaiseModExit

/-!
# `bc_raisemod` from its entry (`0x800061c4`)

    61c4 mod == _zero_: -1 (`rx_epi0`); bc_is_zero (mod): -1; expo negative: -1
    623c one reference added to base, expo, _one_, _zero_ (`RList.bump`)
    6298 the scale warnings; a scale in expo: exponent = expo / 1 at scale 0
    62ac exponent == _zero_: the result `_one_` (`rx_exit`); otherwise
         rscale = MAX (scale, base->n_scale), the loop (`rx_loop`), `rx_fin`

- `RList.bump`: one more reference to a caller's number is a reference handle.
- `RxU`: the state during the bumps (`rx_bumps`); `RxB`/`RxW` after them,
  `RxB.warn` through `rt_warn`.
- `RxGo`: the entry's facts once `mod` is nonzero and `expo` non-negative;
  `rx_go`: from `0x800062ac` to the result.
- `RxIn`/`RxP`: the entry's facts and the state after the prologue's
  stores; `rx_scan` (`bc_is_zero (mod)`), `rx_sign`, `rx_m1`/`rx_nodig`.
- `bc_raisemod_spec`: the function against `Num.raisemod` in `DWO`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## References added by the entry -/

/-- **One more reference** to the caller's `y`: its count raised in the
heap is a reference handle added last. -/
theorem RList.bump {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {hs : List RH}
    {L : List NumObj} {y : NumObj} (hb : BcHeap S X M H F (RList hs L)) (hy : y ∈ L)
    {v : BitVec 64} (hv : v.toNat % 2 ^ 32 = y.rep.refs + rCnt hs y.rep.p + 1)
    (hr : y.rep.refs + rCnt hs y.rep.p + 1 < 2 ^ 31) :
    BcHeap S X (writeLog M [(y.rep.p + 12, 4, v)]) H F (RList (hs ++ [.ref y]) L) := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hy
  have hd : ∀ w ∈ A ++ B, w.rep.p ≠ y.rep.p := fun w hw =>
    (PDist.caller hb.pdist).ne w hw
  rw [RList.ref_split] at hb
  rw [← RList.addRef hs hd]
  exact hb.setRefs (k := (rBump hs y).rep.refs + 1) hv hr

/-- The count `bc_raisemod` reads before raising it. -/
theorem RList.refsAt {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {hs : List RH}
    {L : List NumObj} {y : NumObj} (hb : BcHeap S X M H F (RList hs L)) (hy : y ∈ L) :
    ldv .lw M (y.rep.p + 12) = BitVec.ofNat 64 (y.rep.refs + rCnt hs y.rep.p) :=
  (hb.nums _ (RList.mem_caller hs hy)).refs

/-- `RList.bump` with the count `bc_raisemod` stores, for at most three
handles before it. -/
theorem RList.bump1 {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {hs : List RH}
    {L : List NumObj} {y : NumObj} (hb : BcHeap S X M H F (RList hs L)) (hy : y ∈ L)
    (hroom : y.rep.refs + 4 < 2 ^ 31) (hl : hs.length ≤ 3) :
    BcHeap S X (writeLog M [(y.rep.p + 12, 4, BitVec.ofNat 64 (y.rep.refs + rCnt hs y.rep.p + 1))])
      H F (RList (hs ++ [.ref y]) L) := by
  have := rCnt_le hs y.rep.p
  exact RList.bump hb hy (toNat_ofNat_mod32 (by omega)) (by omega)

/-- `addiw a5, a5, 1` of a small count. -/
theorem addiw1_ofNat {c : Nat} (hc : c + 1 < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 c + 1#64)) =
      BitVec.ofNat 64 (c + 1) := by
  rw [show BitVec.ofNat 64 c + 1#64 = BitVec.ofNat 64 (c + 1) by bv_omega]
  exact sxw_ofNat hc

/-- `_two_` has one digit. -/
theorem two_size {o : NumRep} (hs : NumShape o) (hn : o.Norm) (h2 : o.num = ⟨false, 2, 0⟩) :
    o.len + o.scale = 1 := by
  have hsc : o.scale = 0 := by rw [← NumRep.num_scale, h2]
  have := NumRep.size_le hs hn (E := 1) (by rw [h2]; decide)
  rcases Nat.lt_or_ge (o.len + o.scale) 1 with h | h
  · have h0 := NumRep.mag_zero_of hs.dsLen (fun j hj => by omega)
    rw [h2] at h0
    exact absurd h0 (by decide)
  · omega

/-! ## The frame's facts at the entry -/

/-- The constants at the entry. -/
theorem RxArgs.cst {S : Nat → Prop} {M : Mem} {L : List NumObj} {xb xe xm z o t : NumObj} {k : Nat}
    (ha : RxArgs S M L xb xe xm z o t k) : RxCst M z o t :=
  ⟨ha.zero, ha.one, ha.two, ha.mulBase⟩

/-- The stderr stream through writes off the heap's complement and the frame. -/
theorem RxArgs.fdAt {S : Nat → Prop} {R0 : Nat → BitVec 64} {Mt0 M : Mem} {sp W q k : Nat}
    {L : List NumObj} {xb xe xm z o t : NumObj} (cx : RxCtx S R0 sp W q)
    (ha : RxArgs S Mt0 L xb xe xm z o t k)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    FdAt S M stderrAddr 2 := by
  have hfar := cx.far
  simp only [stderrAddr] at hfar
  exact ha.fd.transport fun j hj => hout _
    (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, stderrAddr]; omega)
    (by simp only [frameIn, stderrAddr]; omega)

/-- The result slot through writes off the heap's complement and the frame. -/
theorem RxSlot.transport {S : Nat → Prop} {R0 : Nat → BitVec 64} {Mt0 M : Mem} {sp W q : Nat}
    {L : List NumObj} {xr : NumObj} (cx : RxCtx S R0 sp W q) (hs : RxSlot Mt0 L xr q)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) : RxSlot M L xr q :=
  hs.congr fun a ha => hout a (cx.slot.out a ha) (by
    have := cx.slot.apart; simp only [slotBytes] at ha; simp only [frameIn]; omega)

/-- Through a callee that writes only below the frame. -/
theorem RxAt.below {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    {sp W : Nat} {slots : List (Nat × Nat)} (h : RxAt S Mt0 M R0 R sp W slots)
    (hkp : Keeps raCallClob R' R) (hw : 112 ≤ W)
    (hag : ∀ a, (a < sp - W ∨ sp - 112 ≤ a) → imgM M' a = imgM M a) :
    RxAt S Mt0 M' R0 R' sp W slots where
  r2 := by rw [hkp.get 2]; exact h.r2
  saved := fun p hp => by
    rw [ldv_congr .ld fun j hj => hag _ (.inr (by omega))]
    exact h.saved p hp
  keep := (hkp.mono (by decide)).trans h.keep
  out := fun a ha hf => by
    rw [hag a (by simp only [frameIn] at hf; omega)]
    exact h.out a ha hf

/-! ## After the references -/

/-- The state after the references at `0x80006298` on: the handles `[power,
exponent, temp, parity] = [base, hE, _one_, _zero_]`; `s0` `base`, `s8` the
exponent, `s1` `&_zero_`, `s2` `mod`, `s3` `scale`, `s4` `&_one_`, `s5`
`_one_`, `s7` the result slot. -/
structure RxB (S : Nat → Prop) (X : Raws) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (xb xm z o : NumObj) (k : Nat) (hE : RH) :
    Prop where
  ra : RxAt S Mt0 M R0 R sp W rxSlots1
  r22 : R 22 = R0 22
  heap : BcHeap S X M H F (RList [.ref xb, hE, .ref o, .ref z] L)
  own : RHOwn [.ref xb, hE, .ref o, .ref z] L
  okE : RHOK L hE
  w0 : ldv .ld M (sp - 112 + 0) = BitVec.ofNat 64 xb.rep.p
  w8 : ldv .ld M (sp - 112 + 8) = BitVec.ofNat 64 hE.p
  w16 : ldv .ld M (sp - 112 + 16) = BitVec.ofNat 64 z.rep.p
  w24 : ldv .ld M (sp - 112 + 24) = BitVec.ofNat 64 o.rep.p
  r8 : R 8 = BitVec.ofNat 64 xb.rep.p
  r24 : R 24 = BitVec.ofNat 64 hE.p
  r9 : R 9 = BitVec.ofNat 64 zeroAddr
  r18 : R 18 = BitVec.ofNat 64 xm.rep.p
  r19 : R 19 = BitVec.ofNat 64 k
  r20 : R 20 = BitVec.ofNat 64 oneAddr
  r21 : R 21 = BitVec.ofNat 64 o.rep.p
  r23 : R 23 = BitVec.ofNat 64 q

/-- With the exponent `hE` holding the integer `m` (at most `Ee` digits). -/
structure RxW (S : Nat → Prop) (X : Raws) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (xb xm z o : NumObj) (k Ee : Nat) (hE : RH)
    (m : Nat) : Prop extends RxB S X Mt0 M R0 R sp W q H F L xb xm z o k hE where
  vE : RxNum hE ⟨false, m, 0⟩ Ee 0
  nE : hE.base.rep.Norm

/-- Through register changes off the state's. -/
theorem RxB.regs {S : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xb xm z o : NumObj} {k : Nat} {hE : RH}
    (h : RxB S X Mt0 M R0 R sp W q H F L xb xm z o k hE) {ks : List Nat}
    (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] :=
      by decide) :
    RxB S X Mt0 M R0 R' sp W q H F L xb xm z o k hE :=
  { h with
    ra := h.ra.regs hk fun z hz => by have := hks z hz; simp only [rxAll, List.mem_cons, List.not_mem_nil, or_false] at this ⊢; omega
    r22 := by rw [hk.get 22 fun hm => by have := hks 22 hm; simp at this]; exact h.r22
    r8 := by rw [hk.get 8 fun hm => by have := hks 8 hm; simp at this]; exact h.r8
    r24 := by rw [hk.get 24 fun hm => by have := hks 24 hm; simp at this]; exact h.r24
    r9 := by rw [hk.get 9 fun hm => by have := hks 9 hm; simp at this]; exact h.r9
    r18 := by rw [hk.get 18 fun hm => by have := hks 18 hm; simp at this]; exact h.r18
    r19 := by rw [hk.get 19 fun hm => by have := hks 19 hm; simp at this]; exact h.r19
    r20 := by rw [hk.get 20 fun hm => by have := hks 20 hm; simp at this]; exact h.r20
    r21 := by rw [hk.get 21 fun hm => by have := hks 21 hm; simp at this]; exact h.r21
    r23 := by rw [hk.get 23 fun hm => by have := hks 23 hm; simp at this]; exact h.r23 }

/-- Through register changes off the state's. -/
theorem RxW.regs {S : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xb xm z o : NumObj} {k Ee : Nat} {hE : RH}
    {m : Nat} (h : RxW S X Mt0 M R0 R sp W q H F L xb xm z o k Ee hE m) {ks : List Nat}
    (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] :=
      by decide) :
    RxW S X Mt0 M R0 R' sp W q H F L xb xm z o k Ee hE m :=
  { h.toRxB.regs hk hks with vE := h.vE, nE := h.nE }

/-- A caller's number referenced. -/
theorem RHOK.ofMem {L : List NumObj} {y : NumObj} (hy : y ∈ L) (hr : 1 ≤ y.rep.refs) :
    RHOK L (.ref y) := by
  obtain ⟨A, B, e⟩ := List.append_of_mem hy
  exact ⟨A, B, e, hr⟩

/-- **The exponent `_zero_` itself** at `0x800063bc`: the result `_one_`. -/
theorem rx_one {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj} {hE : RH} (cx : RxCtx S R0 sp W q)
    (ha : RxArgs S Mt0 L xb xe xm z o t k) (hs0 : RxSlot Mt0 L xr q) (hoz : o.rep.p ≠ z.rep.p)
    (st : RxB S X Mt0 M R0 R sp W q H F L xb xm z o k hE)
    (hret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
      RxPost S X Mt0 Mt' H' F' L xr q sp W Num.one Lf y → DW live S Q (R0 1) R' Mt') :
    DW live S Q 0x800063bc#64 R M :=
  rx_exit hlive cx
    { ra := st.ra
      r22 := st.r22
      r23 := st.r23
      heap := st.heap
      own := st.own
      okP := RHOK.ofMem ha.mb ha.rb
      okE := st.okE
      okT := RHOK.ofMem ha.mo ha.ro
      okX := RHOK.ofMem ha.mz ha.zero.refs
      tx := hoz
      num := ha.oneNum
      norm := ha.oneNorm
      len := ha.oneLen
      r8 := st.r8
      r24 := st.r24
      r21 := st.r21 } (hs0.transport cx st.ra.out) hret

/-- **The loop's start** at `0x800062cc`: `s6` saved at `sp - 112 + 48`,
`s4 = rscale`, `s6 = &_two_`; the loop's bounds `Sc = MAX (rscale,
mod->n_scale + scale)`, `B = mod`'s digits `+ Sc + 1 +` base's digits, the
exponent's `Ee`; then `rx_loop` and `rx_fin`. -/
theorem rx_start {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q k Ee m : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj} {hE : RH} (cx : RxCtx S R0 sp W q)
    (ha : RxArgs S Mt0 L xb xe xm z o t k) (hs0 : RxSlot Mt0 L xr q) (hoz : o.rep.p ≠ z.rep.p)
    (hmag : xm.rep.num.mag ≠ 0) (hEe : Ee = xe.rep.len + xe.rep.scale + 1)
    (hoom : DmOom live S (DQ live S Q t0) Mt0 sp W)
    (st : RxW S X Mt0 M R0 R sp W q H F L xb xm z o k Ee hE m) (hne : hE.p ≠ z.rep.p)
    (hk : Keeps [15, 20, 22] R' R) (h20 : R' 20 = BitVec.ofNat 64 (max k xb.rep.scale))
    (h22 : R' 22 = BitVec.ofNat 64 twoAddr)
    (hret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
      RxPost S X Mt0 Mt' H' F' L xr q sp W
        (Num.raisemodLoop xm.rep.num k (max k xb.rep.scale) (m + 1) ⟨false, m, 0⟩ xb.rep.num Num.one)
        Lf y → DW live S (DQ live S Q t0) (R0 1) R' Mt') :
    DW live S (DQ live S Q t0) 0x800062cc#64 R' (writeLog M [(sp - 112 + 48, 8, R0 22)]) := by
  rx_facts cx
  have hb := st.heap.out_frame (MemOnly.store M (sp - 112 + 48) 8 (R0 22)) fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hsz := ha.size
  have shO := (st.heap.nums _ (RList.mem_caller [.ref xb, hE, .ref o, .ref z] ha.mo)).shape
  have shT := (st.heap.nums _ (RList.mem_caller [.ref xb, hE, .ref o, .ref z] ha.mt)).shape
  have hos : o.rep.len + o.rep.scale ≤ 1 := one_size (o := (rBump [.ref xb, hE, .ref o, .ref z] o).rep) shO ha.oneNorm ha.oneNum
  have hos0 : o.rep.scale = 0 := by rw [← NumRep.num_scale, ha.oneNum]; rfl
  have hts : t.rep.len + t.rep.scale = 1 := two_size (o := (rBump [.ref xb, hE, .ref o, .ref z] t).rep) shT ha.twoNorm ha.twoNum
  have hw : ∀ o', o' ≤ 24 → ldv .ld (writeLog M [(sp - 112 + 48, 8, R0 22)]) (sp - 112 + o') =
      ldv .ld M (sp - 112 + o') := fun o' ho' => ldv_ld_miss _ _ (by omega)
  have ra : RxAt S Mt0 (writeLog M [(sp - 112 + 48, 8, R0 22)]) R0 R' sp W rxSlots2 :=
    { r2 := by rw [hk.get 2 (by decide)]; exact st.ra.r2
      saved := st.ra.saved.store 22 48
      keep := (hk.mono (by decide)).trans st.ra.keep
      out := fun a ha' hf => by
        rw [imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]
        exact st.ra.out a ha' hf }
  refine rx_loop (B := xm.rep.len + max (max k xb.rep.scale) (xm.rep.scale + k) + 1 +
      xb.rep.len + xb.rep.scale) (Sc := max (max k xb.rep.scale) (xm.rep.scale + k))
    (z := z) (o := o) (t := t) hlive
    { cx := cx
      cst := ha.cst
      owns := ha.owns
      mm := ha.mm
      mz := ha.mz
      mt := ha.mt
      nm := ha.nm
      mag := hmag
      twoNum := ha.twoNum
      twoSize := hts
      twoNorm := ha.twoNorm
      sc := rfl
      rsk := Nat.le_max_left _ _
      bnd := by omega
      size := by omega
      sizeE := by omega } hoom m
    (hP := .ref xb) (hT := .ref o) (hX := .ref z) (p := xb.rep.num) (tv := Num.one)
    { f :=
        { ra := ra
          r9 := by rw [hk.get 9 (by decide)]; exact st.r9
          r18 := by rw [hk.get 18 (by decide)]; exact st.r18
          r19 := by rw [hk.get 19 (by decide)]; exact st.r19
          r20 := h20
          r22 := h22
          r23 := by rw [hk.get 23 (by decide)]; exact st.r23 }
      heap := hb
      own := st.own
      okP := RHOK.ofMem ha.mb ha.rb
      okE := st.okE
      okT := RHOK.ofMem ha.mo ha.ro
      okX := RHOK.ofMem ha.mz ha.zero.refs
      ex := hne
      tx := hoz
      vP := ⟨rfl, ha.lenb, by show xb.rep.len + xb.rep.scale ≤ _; omega,
        by show xb.rep.scale ≤ _; omega⟩
      vT := ⟨ha.oneNum, ha.oneLen, by show o.rep.len + o.rep.scale ≤ _; omega,
        by show o.rep.scale ≤ _; omega⟩
      vE := st.vE
      nT := ha.oneNorm
      nE := st.nE
      w0 := by rw [hw 0 (by omega)]; exact st.w0
      w8 := by rw [hw 8 (by omega)]; exact st.w8
      w16 := by rw [hw 16 (by omega)]; exact st.w16
      w24 := by rw [hw 24 (by omega)]; exact st.w24
      r8 := by rw [hk.get 8 (by decide)]; exact st.r8
      r21 := by rw [hk.get 21 (by decide)]; exact st.r21 }
    (by rw [hk.get 24 (by decide)]; exact st.r24) ?_
  intro R2 M2 H2 F2 hP2 hE2 hT2 hX2 m2 p2 st2 h24
  exact rx_fin hlive cx st2 h24 (hs0.transport cx st2.f.ra.out) hret

/-- **The loop's setup** from `0x800062ac`: an exponent at `_zero_`'s
pointer gives `_one_` (`rx_one`); otherwise `s6` saved, `rscale = MAX
(scale, base->n_scale)`, `s6 = &_two_`, the loop (`rx_loop`) and its exit
(`rx_fin`). -/
theorem rx_go {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k Ee m : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj} {hE : RH} (cx : RxCtx S R0 sp W q)
    (ha : RxArgs S Mt0 L xb xe xm z o t k) (hs0 : RxSlot Mt0 L xr q) (hoz : o.rep.p ≠ z.rep.p)
    (hmag : xm.rep.num.mag ≠ 0) (hEe : Ee = xe.rep.len + xe.rep.scale + 1)
    (hoom : DmOom live S (DQ live S Q t0) Mt0 sp W)
    (st : RxW S X Mt0 M R0 R sp W q H F L xb xm z o k Ee hE m) (hz : hE.p = z.rep.p → m = 0)
    (hret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
      RxPost S X Mt0 Mt' H' F' L xr q sp W
        (Num.raisemodLoop xm.rep.num k (max k xb.rep.scale) (m + 1) ⟨false, m, 0⟩ xb.rep.num Num.one)
        Lf y → DW live S (DQ live S Q t0) (R0 1) R' Mt') :
    DW live S (DQ live S Q t0) 0x800062ac#64 R M := by
  rx_facts cx
  have hsf := cx.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hcs := ha.cst.transport cx st.ra.out
  have htz : (BitVec.ofNat 64 zeroAddr).toNat = zeroAddr := rfl
  have hldz : LdOK zeroAddr 8 := by simp only [LdOK, zeroAddr, tohostAddr]; omega
  have hcst : ∀ b ∈ accAddrs zeroAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have shE := (hb.nums _ (RH.obj_mem (hs := [.ref xb, hE, .ref o, .ref z]) (by simp) st.okE)).shape
  have shZ := (hb.nums _ (RList.mem_caller [.ref xb, hE, .ref o, .ref z] ha.mz)).shape
  have hpE := shE.pHi
  have hpZ := shZ.pHi
  rw [RH.obj_p] at hpE
  have hpZ' : (rBump [.ref xb, hE, .ref o, .ref z] z).rep.p = z.rep.p := rfl
  rw [hpZ'] at hpZ
  simp only [heapEnd] at hpE hpZ
  bc_run hlive hS [st.r9, htz, hcs.zero.glob, st.r24] at 0x800063bc 0x800062b4
  all_goals first | exact hldz | exact hcst | skip
  · intro he
    have h0 := hz ((ofNat_eq_iff (by omega) (by omega)).mp he).symm
    subst h0
    rw [Dc.BcModel.raisemodLoop_zero] at hret
    exact rx_one hlive cx ha hs0 hoz (st.toRxB.regs (ks := [15]) (by keeps_tac Keeps.refl _ _)) hret
  intro hne
  have hne' : hE.p ≠ z.rep.p := fun e => hne (by rw [e])
  have hxs : ldv .lw M (xb.rep.p + 8) = BitVec.ofNat 64 xb.rep.scale :=
    (hb.nums _ (RList.mem_caller [.ref xb, hE, .ref o, .ref z] ha.mb)).scale
  have hxn := hb.nums _ (RList.mem_caller [.ref xb, hE, .ref o, .ref z] ha.mb)
  have hpb : xb.rep.p + 40 ≤ heapEnd := hxn.shape.pHi
  have hpb' : heapStart ≤ xb.rep.p := hxn.shape.pLo
  simp only [heapEnd, heapStart] at hpb hpb'
  have hsz := ha.size
  have hx8 : (BitVec.ofNat 64 (xb.rep.p + 8)).toNat = xb.rep.p + 8 := by
    simp only [BitVec.toNat_ofNat]; omega
  have hk24 : k < 2 ^ 24 := by omega
  have hsc24 : xb.rep.scale < 2 ^ 24 := by omega
  have hsx := sxw_ofNat (k := xb.rep.scale) (by omega)
  have hti1 := toInt_ofNat_small (k := xb.rep.scale) (by omega)
  have hti2 := toInt_ofNat_small (k := k) (by omega)
  bc_run hlive hS [st.r8, hx8, hxs, st.ra.r2, st.r22, st.r19, hsx, hti1, hti2] at 0x800062cc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | (simp only [LdOK, tohostAddr]; omega) | skip
  · intro hlt
    have hlt' : xb.rep.scale < k := by exact_mod_cast hlt
    bc_run hlive hS [st.r19] at 0x800062cc
    exact rx_start hlive cx ha hs0 hoz hmag hEe hoom st hne' (by keeps_tac Keeps.refl _ _)
      (by bsimp [st.r19]; congr 1; omega) (by bsimp [])
      hret
  · intro hge
    have hge' : k ≤ xb.rep.scale := by
      have : ¬ (xb.rep.scale : Int) < k := hge
      omega
    bc_run hlive hS [] at 0x800062cc
    exact rx_start hlive cx ha hs0 hoz hmag hEe hoom st hne' (by keeps_tac Keeps.refl _ _)
      (by bsimp []; congr 1; omega) (by bsimp []) hret

/-! ## The scale warnings -/

/-- What `bc_raisemod` leaves in the result slot: the loop on the exponent's
integer part (`Dc.BcModel.raisemod_eq`). -/
abbrev rxVal (xb xe xm : NumObj) (k : Nat) : Num :=
  Num.raisemodLoop xm.rep.num k (max k xb.rep.scale) (xe.rep.num.intPart + 1)
    ⟨false, xe.rep.num.intPart, 0⟩ xb.rep.num Num.one

/-- The entry's fixed facts once the `-1` returns are past: the context, the
operands, the result slot, `_one_` apart from `_zero_`, a nonzero modulus, a
non-negative exponent, of integer part `0` at `_zero_`'s pointer, and the
continuations. -/
structure RxGo (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (R0 : Nat → BitVec 64) (Mt0 : Mem) (sp W q k : Nat) (L : List NumObj)
    (xb xe xm z o t xr : NumObj) : Prop where
  cx : RxCtx S R0 sp W q
  ha : RxArgs S Mt0 L xb xe xm z o t k
  hs : RxSlot Mt0 L xr q
  oz : o.rep.p ≠ z.rep.p
  mag : xm.rep.num.mag ≠ 0
  pos : xe.rep.num.neg = false
  zx : xe.rep.p = z.rep.p → xe.rep.num.intPart = 0
  oom : RaOom live S (DQ live S Q t0) Mt0 sp W q
  ret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
    RxPost S X Mt0 Mt' H' F' L xr q sp W (rxVal xb xe xm k) Lf y →
    DW live S (DQ live S Q t0) (R0 1) R' Mt'

set_option maxRecDepth 100000 in
/-- "non-zero scale in base". -/
theorem rxBaseMsg : RtMsg 0x80007e48 22 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- "non-zero scale in modulus". -/
theorem rxModMsg : RtMsg 0x80007e80 25 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **`rt_warn (msg)`** from `bc_raisemod`'s frame: stderr only, off it the
bytes below the frame changed. -/
theorem rx_warn {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k p n : Nat} {L : List NumObj}
    {xb xe xm z o t : NumObj} (cx : RxCtx S R0 sp W q) (ha : RxArgs S Mt0 L xb xe xm z o t k)
    (hm : RtMsg p n) (hn : n < 2 ^ 60)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h2 : (R 2).toNat = sp - 112) (h10 : (R 10).toNat = p) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps raCallClob R' R →
      (∀ a, (a < sp - W ∨ sp - 112 ≤ a) → imgM M' a = imgM M a) →
      DW live S (DQ live S Q t0) (R 1) R' M') :
    DW live S (DQ live S Q t0) 0x80002c50#64 R M := by
  rx_facts cx
  have hsf := cx.frame
  have hfar := cx.far
  exact rt_warn_spec hlive hm hn ((hsf.shrink (m := 112 + 416) (by omega)).sub (by decide))
    (by omega) (ha.fdAt cx hout) R h2 h10 hal fun R1 M1 hk1 ho1 =>
      hk R1 M1 (hk1.mono (by decide)) fun a h => ho1 a (by omega)

/-- The state through `rt_warn`. -/
theorem RxB.warn {S : Nat → Prop} {X : Raws} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xb xm z o : NumObj} {k : Nat} {hE : RH}
    (cx : RxCtx S R0 sp W q) (st : RxB S X Mt0 M R0 R sp W q H F L xb xm z o k hE)
    (hkc : Keeps raCallClob R' R)
    (hag : ∀ a, (a < sp - W ∨ sp - 112 ≤ a) → imgM M' a = imgM M a) :
    RxB S X Mt0 M' R0 R' sp W q H F L xb xm z o k hE := by
  rx_facts cx
  have hw : ∀ o', ldv .ld M' (sp - 112 + o') = ldv .ld M (sp - 112 + o') := fun o' =>
    ldv_congr .ld fun j _ => hag _ (.inr (by omega))
  exact
    { ra := st.ra.below hkc (by omega) hag
      r22 := by rw [hkc.get 22 (by decide)]; exact st.r22
      heap := st.heap.out_frame (P := fun a => sp - W ≤ a ∧ a < sp - 112)
        (fun a h => hag a (by omega))
        fun a h => by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
      own := st.own
      okE := st.okE
      w0 := by rw [hw]; exact st.w0
      w8 := by rw [hw]; exact st.w8
      w16 := by rw [hw]; exact st.w16
      w24 := by rw [hw]; exact st.w24
      r8 := by rw [hkc.get 8 (by decide)]; exact st.r8
      r24 := by rw [hkc.get 24 (by decide)]; exact st.r24
      r9 := by rw [hkc.get 9 (by decide)]; exact st.r9
      r18 := by rw [hkc.get 18 (by decide)]; exact st.r18
      r19 := by rw [hkc.get 19 (by decide)]; exact st.r19
      r20 := by rw [hkc.get 20 (by decide)]; exact st.r20
      r21 := by rw [hkc.get 21 (by decide)]; exact st.r21
      r23 := by rw [hkc.get 23 (by decide)]; exact st.r23 }

/-- **"non-zero scale in modulus"** at `0x800064bc`, then `rx_go`. -/
theorem rx_wm {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj} {hE : RH}
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (st : RxW S X Mt0 M R0 R sp W q H F L xb xm z o k (xe.rep.len + xe.rep.scale + 1) hE
      xe.rep.num.intPart) (hz : hE.p = z.rep.p → xe.rep.num.intPart = 0) :
    DW live S (DQ live S Q t0) 0x800064bc#64 R M := by
  have cx := g.cx
  rx_facts cx
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have h2 := st.ra.r2
  bc_run hlive hS [h2] at 0x80002c50
  refine rx_warn hlive cx g.ha rxModMsg (by decide) st.ra.out (by bsimp [h2]) (by bsimp [])
    (by bsimp []; try decide) fun R1 M1 hk1 ho1 => ?_
  bsimp []
  bc_run hlive hS [] at 0x800062ac
  exact rx_go hlive cx g.ha g.hs g.oz g.mag rfl g.oom.dm
    { st.toRxB.warn cx (hk1.trans (by keeps_tac Keeps.refl _ _)) ho1 with vE := st.vE, nE := st.nE }
    hz g.ret

/-- **The modulus's scale** at `0x800062a4`: a warning (`rx_wm`) or none,
then `rx_go`. -/
theorem rx_wmod {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj} {hE : RH}
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (st : RxW S X Mt0 M R0 R sp W q H F L xb xm z o k (xe.rep.len + xe.rep.scale + 1) hE
      xe.rep.num.intPart) (hz : hE.p = z.rep.p → xe.rep.num.intPart = 0) :
    DW live S (DQ live S Q t0) 0x800062a4#64 R M := by
  have cx := g.cx
  rx_facts cx
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hxn := hb.nums _ (RList.mem_caller [.ref xb, hE, .ref o, .ref z] g.ha.mm)
  have hms : ldv .lw M (xm.rep.p + 8) = BitVec.ofNat 64 xm.rep.scale := hxn.scale
  have hpm : xm.rep.p + 40 ≤ heapEnd := hxn.shape.pHi
  have hpm' : heapStart ≤ xm.rep.p := hxn.shape.pLo
  simp only [heapEnd, heapStart] at hpm hpm'
  have hx8 : (BitVec.ofNat 64 (xm.rep.p + 8)).toNat = xm.rep.p + 8 := by
    simp only [BitVec.toNat_ofNat]; omega
  bc_run hlive hS [st.r18, hx8, hms] at 0x800064bc 0x800062ac
  all_goals first | exact acc_heap hS (by omega) (by omega) | (simp only [LdOK, tohostAddr]; omega) | skip
  · intro _
    exact rx_wm hlive g (st.regs (ks := [15]) (by keeps_tac Keeps.refl _ _)) hz
  · intro _
    exact rx_go hlive cx g.ha g.hs g.oz g.mag rfl g.oom.dm
      (st.regs (ks := [15]) (by keeps_tac Keeps.refl _ _)) hz g.ret

/-- **"non-zero scale in exponent"** at `0x80006490`, then `exponent = expo /
1` at scale 0 (`bc_divide`): a new number holding the integer part in the
exponent's handle; then the modulus's scale at `0x800064b0`. -/
theorem rx_divx {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (st : RxB S X Mt0 M R0 R sp W q H F L xb xm z o k (.ref xe)) :
    DW live S (DQ live S Q t0) 0x80006490#64 R M := by
  have cx := g.cx
  have ha := g.ha
  rx_facts cx
  have hsf := cx.frame
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have h2 := st.ra.r2
  bc_run hlive hS [h2] at 0x80002c50
  refine rx_warn hlive cx ha raScaleMsg (by decide) st.ra.out (by bsimp [h2]) (by bsimp [])
    (by bsimp []; try decide) fun R1 M1 hk1 ho1 => ?_
  bsimp []
  have st1 := st.warn cx (hk1.trans (by keeps_tac Keeps.refl _ _)) ho1
  have hb := st1.heap
  have hcs := ha.cst.transport cx st1.ra.out
  have hto : (BitVec.ofNat 64 oneAddr).toNat = oneAddr := rfl
  have hldo : LdOK oneAddr 8 := by simp only [LdOK, oneAddr, tohostAddr]; omega
  have hcst : ∀ b ∈ accAddrs oneAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have h21 := st1.ra.r2
  have hsz := ha.size
  have hzk := ha.zero
  have hxe := hb.nums _ (RH.obj_mem (hs := [.ref xb, .ref xe, .ref o, .ref z]) (by simp)
    (RHOK.ofMem ha.me ha.re))
  have hxeS := hxe.shape
  have hos := one_size (o := (rBump [.ref xb, .ref xe, .ref o, .ref z] o).rep)
    (hb.nums _ (RList.mem_caller _ ha.mo)).shape ha.oneNorm ha.oneNum
  have hos' : o.rep.len + o.rep.scale ≤ 1 := hos
  bc_run hlive hS [st1.r20, hto, hcs.one, st1.r24, h21] at 0x8000589c
  all_goals first | exact hldo | exact hcst | skip
  refine rx_divH (hs1 := [.ref xb]) (p := xe) (hs2 := [.ref o, .ref z]) (o := 8) (k := 0)
    (u1 := RH.obj [.ref xb, .ref xe, .ref o, .ref z] (.ref xe))
    (u2 := rBump [.ref xb, .ref xe, .ref o, .ref z] o)
    (z := rBump [.ref xb, .ref xe, .ref o, .ref z] z)
    hlive cx g.oom (by omega) rfl st1.ra.out hb st1.own (RHOK.ofMem ha.me ha.re)
    (RH.obj_mem (by simp) (RHOK.ofMem ha.me ha.re)) (RList.mem_caller _ ha.mo)
    (RList.mem_caller _ ha.mz)
    (by show xe.rep.len + xe.rep.scale + 0 + o.rep.len + o.rep.scale < _; omega)
    hcs.zero.glob (by show z.rep.num.mag = 0; rw [NumRep.num_mag, hzk.ds]; rfl)
    ha.lene (by show o.rep.num.mag ≠ 0; rw [ha.oneNum]; decide) st1.w8
    (by bsimp [h21]) (by bsimp []; try decide) (by bsimp [st1.r24]; rfl)
    (by bsimp [hcs.one]; try rfl) (by bsimp [h21]) (by bsimp []) ?_
  intro m' hm R2 M2 H2 F2 y hk2 _ hb2 hres hout2
  bsimp []
  have hm' : m' = ⟨false, xe.rep.num.intPart, 0⟩ := by
    have e : Num.div xe.rep.num Num.one 0 = some m' := by rw [← ha.oneNum]; exact hm
    rw [Dc.BcModel.div_one_int _ g.pos] at e
    exact (Option.some.inj e).symm
  subst hm'
  have hb2' : BcHeap S X M2 H2 F2 (RList [.ref xb, .own y, .ref o, .ref z] L) := hb2
  have hmy : y ∈ RList [.ref xb, .own y, .ref o, .ref z] L :=
    RH.obj_mem (h := .own y) (by simp) ⟨hres.refs, hres.owns⟩
  have hyp : y.rep.p = y.sb.pay := (hb2'.blocks y hmy).sPay
  have hw8 : ldv .ld M2 (sp - 112 + 8) = BitVec.ofNat 64 y.rep.p := by rw [hres.slot, hyp]
  have hxn := hb2'.nums _ (RList.mem_caller [.ref xb, .own y, .ref o, .ref z] ha.mm)
  have hms : ldv .lw M2 (xm.rep.p + 8) = BitVec.ofNat 64 xm.rep.scale := hxn.scale
  have hpm : xm.rep.p + 40 ≤ heapEnd := hxn.shape.pHi
  have hpm' : heapStart ≤ xm.rep.p := hxn.shape.pLo
  simp only [heapEnd, heapStart] at hpm hpm'
  have hx8 : (BitVec.ofNat 64 (xm.rep.p + 8)).toNat = xm.rep.p + 8 := by
    simp only [BitVec.toNat_ofNat]; omega
  have h18 : R2 18 = BitVec.ofNat 64 xm.rep.p := by rw [hk2.get 18 (by decide)]; bsimp [st1.r18]
  have h22 : R2 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk2.get 2 (by decide)]; bsimp [h21]
  have hkc : Keeps raCallClob R2 R1 :=
    (hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  have ra2 := st1.ra.call (hsp := by omega) (hW := by omega) (hkp := hkc)
    (hag := fun a h1 h2' h3 => hout2 a h1 (by simp only [slotBytes]; omega) h3)
    (hst := fun a h1 _ => outHeap_of_ge (by simp only [heapEnd]; omega))
  have hw : ∀ o', o' ≤ 24 → o' ≠ 8 → o' % 8 = 0 →
      ldv .ld M2 (sp - 112 + o') = ldv .ld M1 (sp - 112 + o') :=
    fun o' ho hne h8 => rx_word cx ho fun a h1 h2' h3 => hout2 a h1
      (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)
  have shy := (hb2'.nums y hmy).shape
  have hys : y.rep.scale = 0 := by rw [← NumRep.num_scale, hres.num]
  have hlt : y.rep.num.mag < 10 ^ (xe.rep.len + xe.rep.scale) := by
    rw [hres.num]
    show xe.rep.num.mag / 10 ^ xe.rep.num.scale < _
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
      (NumRep.mag_lt (o := (RH.obj [.ref xb, .ref xe, .ref o, .ref z] (.ref xe)).rep) hxeS)
  have hysz := NumRep.size_le shy hres.norm hlt
  have mk : ∀ R3 : Nat → BitVec 64, Keeps [15, 24] R3 R2 → R3 24 = BitVec.ofNat 64 y.rep.p →
      RxW S X Mt0 M2 R0 R3 sp W q H2 F2 L xb xm z o k (xe.rep.len + xe.rep.scale + 1) (.own y)
        xe.rep.num.intPart := fun R3 hk3 h24 =>
    { ra := ra2.regs hk3
      r22 := by rw [hk3.get 22 (by decide), hkc.get 22 (by decide)]; exact st1.r22
      heap := hb2'
      own := (show RHOwn ([.ref xb] ++ .ref xe :: [.ref o, .ref z]) L from st1.own).set hres.owns
      okE := ⟨hres.refs, hres.owns⟩
      w0 := by rw [hw 0 (by omega) (by omega) rfl]; exact st1.w0
      w8 := hw8
      w16 := by rw [hw 16 (by omega) (by omega) rfl]; exact st1.w16
      w24 := by rw [hw 24 (by omega) (by omega) rfl]; exact st1.w24
      r8 := by rw [hk3.get 8 (by decide), hkc.get 8 (by decide)]; exact st1.r8
      r24 := h24
      r9 := by rw [hk3.get 9 (by decide), hkc.get 9 (by decide)]; exact st1.r9
      r18 := by rw [hk3.get 18 (by decide), hkc.get 18 (by decide)]; exact st1.r18
      r19 := by rw [hk3.get 19 (by decide), hkc.get 19 (by decide)]; exact st1.r19
      r20 := by rw [hk3.get 20 (by decide), hkc.get 20 (by decide)]; exact st1.r20
      r21 := by rw [hk3.get 21 (by decide), hkc.get 21 (by decide)]; exact st1.r21
      r23 := by rw [hk3.get 23 (by decide), hkc.get 23 (by decide)]; exact st1.r23
      vE := ⟨hres.num, hres.pos, by show y.rep.len + y.rep.scale ≤ _; omega,
        by show y.rep.scale ≤ 0; omega⟩
      nE := hres.norm }
  have hz : (RH.own y).p = z.rep.p → xe.rep.num.intPart = 0 := fun e =>
    absurd e (RList.own_ne_caller hb2'.pdist (by simp) ha.mz)
  bc_run hlive hS [h18, hx8, hms, h22, hw8] at 0x800064bc 0x800062ac
  all_goals first | exact acc_heap hS (by omega) (by omega) | (simp only [LdOK, tohostAddr]; omega) | exact frame_acc hsf (by omega) (by omega) | skip
  · intro _
    exact rx_go hlive cx ha g.hs g.oz g.mag rfl g.oom.dm
      (mk _ (by keeps_tac Keeps.refl _ _) (by bsimp [])) hz g.ret
  · intro _
    exact rx_wm hlive g (mk _ (by keeps_tac Keeps.refl _ _) (by bsimp [])) hz

/-- An exponent of scale `0`: the integer it holds. -/
theorem RxB.exp0 {live S : Nat → Prop} {X : Raws} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t0 : String} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap}
    {F : List Blk} {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (st : RxB S X Mt0 M R0 R sp W q H F L xb xm z o k (.ref xe)) (hsc : xe.rep.scale = 0) :
    RxW S X Mt0 M R0 R sp W q H F L xb xm z o k (xe.rep.len + xe.rep.scale + 1) (.ref xe)
      xe.rep.num.intPart := by
  have hnum : xe.rep.num = ⟨false, xe.rep.num.intPart, 0⟩ := by
    have h1 := g.pos
    have h2 : xe.rep.num.scale = 0 := by rw [NumRep.num_scale]; exact hsc
    revert h1 h2
    generalize xe.rep.num = e
    rcases e with ⟨a, b, c⟩
    rintro rfl rfl
    simp [Num.intPart]
  exact { st with
    vE := ⟨hnum, g.ha.lene, by show xe.rep.len + xe.rep.scale ≤ _; omega,
      by show xe.rep.scale ≤ 0; omega⟩
    nE := g.ha.ne }

/-- The exponent's scale `lw a5, 8(s8)` at the state. -/
theorem RxB.expScale {S : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xb xe xm z o : NumObj}
    (st : RxB S X Mt0 M R0 R sp W q H F L xb xm z o k (.ref xe)) (hm : xe ∈ L) (hr : 1 ≤ xe.rep.refs) :
    ldv .lw M (xe.rep.p + 8) = BitVec.ofNat 64 xe.rep.scale ∧
      (BitVec.ofNat 64 (xe.rep.p + 8)).toNat = xe.rep.p + 8 ∧ heapStart ≤ xe.rep.p ∧
      xe.rep.p + 40 ≤ heapEnd := by
  have hn := st.heap.nums _ (RH.obj_mem (hs := [.ref xb, .ref xe, .ref o, .ref z]) (by simp)
    (RHOK.ofMem hm hr))
  have h1 : heapStart ≤ xe.rep.p := hn.shape.pLo
  have h2 : xe.rep.p + 40 ≤ heapEnd := hn.shape.pHi
  refine ⟨hn.scale, ?_, h1, h2⟩
  simp only [heapStart, heapEnd] at h1 h2
  simp only [BitVec.toNat_ofNat]; omega

/-- **The exponent's scale** at `0x8000629c`: none (`rx_wmod`) or a warning
and the division (`rx_divx`). -/
theorem rx_wexp {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (st : RxB S X Mt0 M R0 R sp W q H F L xb xm z o k (.ref xe)) :
    DW live S (DQ live S Q t0) 0x8000629c#64 R M := by
  have cx := g.cx
  rx_facts cx
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  obtain ⟨hes, hx8, hp1, hp2⟩ := st.expScale g.ha.me g.ha.re
  simp only [heapStart, heapEnd] at hp1 hp2
  have hsz := g.ha.size
  have hq := ofNat_eq_zero_iff (show xe.rep.scale < 2 ^ 64 by omega)
  bc_run hlive hS [st.r24, RH.p, hx8, hes, hq] at 0x80006490 0x800062a4
  all_goals first | exact acc_heap hS (by omega) (by omega) | (simp only [LdOK, tohostAddr]; omega) | skip
  · intro _
    exact rx_divx hlive g (st.regs (ks := [15]) (by keeps_tac Keeps.refl _ _))
  · intro h0
    exact rx_wmod hlive g ((st.regs (ks := [15]) (by keeps_tac Keeps.refl _ _)).exp0 g
      (by first | exact h0 | exact hq.mp (Classical.not_not.mp h0))) g.zx

/-- **The base's scale** at `0x80006298` (`a4`): a warning, then the
exponent's scale (`0x80006488`), or straight to `rx_wexp`. -/
theorem rx_wbase {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (st : RxB S X Mt0 M R0 R sp W q H F L xb xm z o k (.ref xe))
    (h14 : R 14 = BitVec.ofNat 64 xb.rep.scale) :
    DW live S (DQ live S Q t0) 0x80006298#64 R M := by
  have cx := g.cx
  rx_facts cx
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have hsz := g.ha.size
  have hq := ofNat_eq_zero_iff (show xb.rep.scale < 2 ^ 64 by omega)
  bc_run hlive hS [h14, hq] at 0x8000647c 0x8000629c
  · intro _
    have h2 := st.ra.r2
    bc_run hlive hS [h2] at 0x80002c50
    refine rx_warn hlive cx g.ha rxBaseMsg (by decide) st.ra.out (by bsimp [h2]) (by bsimp [])
      (by bsimp []; try decide) fun R1 M1 hk1 ho1 => ?_
    bsimp []
    have st1 := st.warn cx (hk1.trans (by keeps_tac Keeps.refl _ _)) ho1
    obtain ⟨hes, hx8, hp1, hp2⟩ := st1.expScale g.ha.me g.ha.re
    simp only [heapStart, heapEnd] at hp1 hp2
    have hq' := ofNat_eq_zero_iff (show xe.rep.scale < 2 ^ 64 by omega)
    bc_run hlive hS [st1.r24, RH.p, hx8, hes, hq'] at 0x800062a4 0x80006490
    all_goals first | exact acc_heap hS (by omega) (by omega) | (simp only [LdOK, tohostAddr]; omega) | skip
    · intro h0
      exact rx_wmod hlive g ((st1.regs (ks := [15]) (by keeps_tac Keeps.refl _ _)).exp0 g
        (by first | exact h0 | exact hq'.mp h0)) g.zx
    · intro _
      exact rx_divx hlive g (st1.regs (ks := [15]) (by keeps_tac Keeps.refl _ _))
  · intro _
    exact rx_wexp hlive g st

/-! ## The references -/

/-- Through a store into the heap. -/
theorem RxAt.heapStore {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {slots : List (Nat × Nat)} (h : RxAt S Mt0 M R0 R sp W slots) (cx : RxCtx S R0 sp W q)
    {a0 w : Nat} (v : BitVec 64) (hlo : heapStart ≤ a0) (hhi : a0 + w ≤ heapEnd) :
    RxAt S Mt0 (writeLog M [(a0, w, v)]) R0 R sp W slots where
  r2 := h.r2
  saved := fun p hp => by
    rx_facts cx
    simp only [heapEnd] at hhi
    rw [ldv_ld_miss _ _ (by omega)]; exact h.saved p hp
  keep := h.keep
  out := fun a ha hf => by
    rw [imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha hlo hhi; omega)]
    exact h.out a ha hf

/-- Through a store of a handle's word (below the saved registers). -/
theorem RxAt.wordStore {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {slots : List (Nat × Nat)} (h : RxAt S Mt0 M R0 R sp W slots) (cx : RxCtx S R0 sp W q)
    {a0 : Nat} (v : BitVec 64) (hlo : sp - 112 ≤ a0) (hhi : a0 + 8 ≤ sp - 80)
    (hs : ∀ p ∈ slots, 32 ≤ p.2 := by decide) :
    RxAt S Mt0 (writeLog M [(a0, 8, v)]) R0 R sp W slots where
  r2 := h.r2
  saved := fun p hp => by
    have := hs p hp
    rw [ldv_ld_miss _ _ (by omega)]; exact h.saved p hp
  keep := h.keep
  out := fun a ha hf => by
    rx_facts cx
    rw [imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]
    exact h.out a ha hf

/-- The state while `bc_raisemod` adds its references (`0x8000623c` to
`0x80006298`): the heap with the reference handles `hs` added so far; `s0`
`base`, `s8` `expo`, `s1` `&_zero_`, `a2` `mod`, `a3` the slot, `a6` `_zero_`. -/
structure RxU (S : Nat → Prop) (X : Raws) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (xb xe xm z : NumObj) (hs : List RH) : Prop where
  ra : RxAt S Mt0 M R0 R sp W rxSlots1
  r22 : R 22 = R0 22
  heap : BcHeap S X M H F (RList hs L)
  r8 : R 8 = BitVec.ofNat 64 xb.rep.p
  r24 : R 24 = BitVec.ofNat 64 xe.rep.p
  r9 : R 9 = BitVec.ofNat 64 zeroAddr
  r12 : R 12 = BitVec.ofNat 64 xm.rep.p
  r13 : R 13 = BitVec.ofNat 64 q
  r16 : R 16 = BitVec.ofNat 64 z.rep.p

/-- A caller's number's struct in the heap. -/
theorem RxU.ptr {S : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xb xe xm z : NumObj} {hs : List RH}
    (st : RxU S X Mt0 M R0 R sp W q H F L xb xe xm z hs) {y : NumObj} (hy : y ∈ L) :
    2147603920 ≤ y.rep.p ∧ y.rep.p + 40 ≤ 2273312768 ∧ y.rep.p % 8 = 0 := by
  have hn := (st.heap.nums _ (RList.mem_caller hs hy)).shape
  have h1 : heapStart ≤ y.rep.p := hn.pLo
  have h2 : y.rep.p + 40 ≤ heapEnd := hn.pHi
  have h3 : y.rep.p % 8 = 0 := hn.pAl
  simp only [heapStart, heapEnd] at h1 h2
  exact ⟨h1, h2, h3⟩

/-- Through register changes off the state's. -/
theorem RxU.regs {S : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xb xe xm z : NumObj} {hs : List RH}
    (st : RxU S X Mt0 M R0 R sp W q H F L xb xe xm z hs) {ks : List Nat} (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ [1, 5, 6, 7, 10, 11, 14, 15, 17, 18, 19, 20, 21, 23, 28, 29, 30, 31] :=
      by decide) :
    RxU S X Mt0 M R0 R' sp W q H F L xb xe xm z hs :=
  { st with
    ra := st.ra.regs hk fun z hz => by have := hks z hz; simp only [rxAll, List.mem_cons, List.not_mem_nil, or_false] at this ⊢; omega
    r22 := by rw [hk.get 22 fun hm => by have := hks 22 hm; simp at this]; exact st.r22
    r8 := by rw [hk.get 8 fun hm => by have := hks 8 hm; simp at this]; exact st.r8
    r24 := by rw [hk.get 24 fun hm => by have := hks 24 hm; simp at this]; exact st.r24
    r9 := by rw [hk.get 9 fun hm => by have := hks 9 hm; simp at this]; exact st.r9
    r12 := by rw [hk.get 12 fun hm => by have := hks 12 hm; simp at this]; exact st.r12
    r13 := by rw [hk.get 13 fun hm => by have := hks 13 hm; simp at this]; exact st.r13
    r16 := by rw [hk.get 16 fun hm => by have := hks 16 hm; simp at this]; exact st.r16 }

/-- Through a store of a handle's word. -/
theorem RxU.word {S : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xb xe xm z : NumObj} {hs : List RH}
    (st : RxU S X Mt0 M R0 R sp W q H F L xb xe xm z hs) (cx : RxCtx S R0 sp W q) {a0 : Nat}
    (v : BitVec 64) (hlo : sp - 112 ≤ a0) (hhi : a0 + 8 ≤ sp - 80) :
    RxU S X Mt0 (writeLog M [(a0, 8, v)]) R0 R sp W q H F L xb xe xm z hs := by
  rx_facts cx
  exact
    { st with
      ra := st.ra.wordStore cx v hlo hhi
      heap := st.heap.out_frame (MemOnly.store M a0 8 v) fun a h => by
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega }

/-- Through one more reference to the caller's `y`. -/
theorem RxU.bump {S : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xb xe xm z : NumObj} {hs : List RH}
    (st : RxU S X Mt0 M R0 R sp W q H F L xb xe xm z hs) (cx : RxCtx S R0 sp W q) {y : NumObj}
    (hy : y ∈ L) (hroom : y.rep.refs + 4 < 2 ^ 31) (hl : hs.length ≤ 3) :
    RxU S X Mt0 (writeLog M [(y.rep.p + 12, 4, BitVec.ofNat 64 (y.rep.refs + rCnt hs y.rep.p + 1))])
      R0 R sp W q H F L xb xe xm z (hs ++ [.ref y]) := by
  obtain ⟨h1, h2, _⟩ := st.ptr hy
  exact
    { st with
      ra := st.ra.heapStore cx _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
      heap := RList.bump1 st.heap hy hroom hl }

/-- The state after the last reference (`_zero_`'s) and the handles' last
two words: `RxB`. -/
theorem RxU.fin {live S : Nat → Prop} {X : Raws} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t0 : String} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q k : Nat} {H : Heap}
    {F : List Blk} {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (st : RxU S X Mt0 M R0 R sp W q H F L xb xe xm z [.ref xb, .ref xe, .ref o])
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (hk : Keeps [15, 18, 23] R' R) (h19 : R' 19 = BitVec.ofNat 64 k)
    (h20 : R' 20 = BitVec.ofNat 64 oneAddr) (h21 : R' 21 = BitVec.ofNat 64 o.rep.p)
    (w0 : ldv .ld M (sp - 112) = BitVec.ofNat 64 xb.rep.p)
    (w8 : ldv .ld M (sp - 112 + 8) = BitVec.ofNat 64 xe.rep.p)
    (h18 : R' 18 = R 12) (h23 : R' 23 = R 13) :
    RxB S X Mt0 (writeLog (writeLog (writeLog M [(sp - 112 + 16, 8, BitVec.ofNat 64 z.rep.p)])
        [(sp - 112 + 24, 8, BitVec.ofNat 64 o.rep.p)])
        [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + rCnt [.ref xb, .ref xe, .ref o] z.rep.p + 1))])
      R0 R' sp W q H F L xb xm z o k (.ref xe) := by
  have cx := g.cx
  have ha := g.ha
  rx_facts cx
  obtain ⟨hz1, hz2, hz3⟩ := st.ptr ha.mz
  have hrz := ha.refs z ha.mz
  have c4 := rCnt_le [.ref xb, .ref xe, .ref o] z.rep.p
  simp only [List.length_cons, List.length_nil] at c4
  have hP : ∀ a, (sp - 112 + 16 ≤ a ∧ a < sp - 112 + 16 + 8) ∨
      (sp - 112 + 24 ≤ a ∧ a < sp - 112 + 24 + 8) → OutHeap a := fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hb4 := RList.bump1 (((st.heap.out_frame
    (MemOnly.store M (sp - 112 + 16) 8 (BitVec.ofNat 64 z.rep.p)) fun a h => hP a (.inl h)).out_frame
    (MemOnly.store _ (sp - 112 + 24) 8 (BitVec.ofNat 64 o.rep.p)) fun a h => hP a (.inr h)))
    ha.mz (by omega) (by simp)
  have ra := ((st.ra.wordStore cx (a0 := sp - 112 + 16) (BitVec.ofNat 64 z.rep.p) (by omega)
    (by omega)).wordStore cx (a0 := sp - 112 + 24) (BitVec.ofNat 64 o.rep.p) (by omega)
    (by omega)).heapStore cx (a0 := z.rep.p + 12) (w := 4)
    (BitVec.ofNat 64 (z.rep.refs + rCnt [.ref xb, .ref xe, .ref o] z.rep.p + 1))
    (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  exact
    { ra := ra.regs hk
      r22 := by rw [hk.get 22 (by decide)]; exact st.r22
      heap := hb4
      own := ⟨fun y hy => by simp at hy, ha.owns⟩
      okE := RHOK.ofMem ha.me ha.re
      w0 := by
        rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
        exact w0
      w8 := by
        rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
        exact w8
      w16 := by
        rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
        exact ldv_store_hit _ _ _
      w24 := by
        rw [ldv_ld_miss _ _ (by omega)]
        exact ldv_store_hit _ _ _
      r8 := by rw [hk.get 8 (by decide)]; exact st.r8
      r24 := by rw [hk.get 24 (by decide)]; exact st.r24
      r9 := by rw [hk.get 9 (by decide)]; exact st.r9
      r18 := by rw [h18]; exact st.r12
      r19 := h19
      r20 := h20
      r21 := h21
      r23 := by rw [h23]; exact st.r13 }

/-- **`_zero_`'s reference** from `0x8000627c` (`s5` `_one_`, `s3` scale,
`a4` the base's scale, `power` and `exponent` stored), then `rx_wbase`. -/
theorem rx_bump4 {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (st : RxU S X Mt0 M R0 R sp W q H F L xb xe xm z [.ref xb, .ref xe, .ref o])
    (h19 : R 19 = BitVec.ofNat 64 k) (h20 : R 20 = BitVec.ofNat 64 oneAddr)
    (h21 : R 21 = BitVec.ofNat 64 o.rep.p) (h14 : R 14 = BitVec.ofNat 64 xb.rep.scale)
    (w0 : ldv .ld M (sp - 112) = BitVec.ofNat 64 xb.rep.p)
    (w8 : ldv .ld M (sp - 112 + 8) = BitVec.ofNat 64 xe.rep.p) :
    DW live S (DQ live S Q t0) 0x8000627c#64 R M := by
  have cx := g.cx
  have ha := g.ha
  rx_facts cx
  have hsf := cx.frame
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  obtain ⟨hz1, hz2, hz3⟩ := st.ptr ha.mz
  have hrz := ha.refs z ha.mz
  have c4 := rCnt_le [.ref xb, .ref xe, .ref o] z.rep.p
  simp only [List.length_cons, List.length_nil] at c4
  have hr := RList.refsAt st.heap ha.mz
  have hx := sxw_ofNat (k := z.rep.refs + rCnt [.ref xb, .ref xe, .ref o] z.rep.p + 1) (by omega)
  have h2 := st.ra.r2
  bc_run hlive hS [st.r16, hr, hx, h2, h21] at 0x80006298
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  exact rx_wbase hlive g (st.fin g (by keeps_tac Keeps.refl _ _) (by bsimp [h19]) (by bsimp [h20])
    (by bsimp [h21]) w0 w8 (by bsimp []) (by bsimp [])) (by bsimp [h14])


/-- **`_one_`'s reference** from `0x80006268` (`power` and `exponent`
stored), then `rx_bump4`. -/
theorem rx_bump3 {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (st : RxU S X Mt0 M R0 R sp W q H F L xb xe xm z [.ref xb, .ref xe])
    (h19 : R 19 = BitVec.ofNat 64 k) (h20 : R 20 = BitVec.ofNat 64 oneAddr)
    (h21 : R 21 = BitVec.ofNat 64 o.rep.p) (h14 : R 14 = BitVec.ofNat 64 xb.rep.scale) :
    DW live S (DQ live S Q t0) 0x80006268#64 R M := by
  have cx := g.cx
  have ha := g.ha
  rx_facts cx
  have hsf := cx.frame
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  obtain ⟨ho1, ho2, ho3⟩ := st.ptr ha.mo
  have hro := ha.refs o ha.mo
  have c3 := rCnt_le [.ref xb, .ref xe] o.rep.p
  simp only [List.length_cons, List.length_nil] at c3
  have hr := RList.refsAt st.heap ha.mo
  have hx := sxw_ofNat (k := o.rep.refs + rCnt [.ref xb, .ref xe] o.rep.p + 1) (by omega)
  have h2 := st.ra.r2
  bc_run hlive hS [h21, hr, hx, h2, st.r8, st.r24] at 0x8000627c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  exact rx_bump4 hlive g
    ((((st.word cx (a0 := sp - 112) _ (by omega) (by omega)).word cx (a0 := sp - 112 + 8) _
      (by omega) (by omega)).bump cx ha.mo (by omega) (by simp)).regs
      (ks := [15]) (by keeps_tac Keeps.refl _ _))
    (by bsimp [h19]) (by bsimp [h20]) (by bsimp [h21]) (by bsimp [h14])
    (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _)
    (by rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _)

/-- **`expo`'s reference** from `0x80006254` (`s3 = scale`, `a4` the base's
scale), then `rx_bump3`. -/
theorem rx_bump2 {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (st : RxU S X Mt0 M R0 R sp W q H F L xb xe xm z [.ref xb])
    (h20 : R 20 = BitVec.ofNat 64 oneAddr) (h21 : R 21 = BitVec.ofNat 64 o.rep.p)
    (h14 : R 14 = BitVec.ofNat 64 k) :
    DW live S (DQ live S Q t0) 0x80006254#64 R M := by
  have cx := g.cx
  have ha := g.ha
  rx_facts cx
  have hsf := cx.frame
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  obtain ⟨he1, he2, he3⟩ := st.ptr ha.me
  obtain ⟨hb1, hb2, hb3⟩ := st.ptr ha.mb
  have hre := ha.refs xe ha.me
  have c2 := rCnt_le [.ref xb] xe.rep.p
  simp only [List.length_cons, List.length_nil] at c2
  have hr := RList.refsAt st.heap ha.me
  have hs : ldv .lw M (xb.rep.p + 8) = BitVec.ofNat 64 xb.rep.scale :=
    (st.heap.nums _ (RList.mem_caller _ ha.mb)).scale
  have hx := sxw_ofNat (k := xe.rep.refs + rCnt [.ref xb] xe.rep.p + 1) (by omega)
  bc_run hlive hS [st.r24, hr, hx, st.r8, hs, h14] at 0x80006268
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  exact rx_bump3 hlive g ((st.bump cx ha.me (by omega) (by simp)).regs
      (ks := [14, 15, 19]) (by keeps_tac Keeps.refl _ _))
    (by bsimp [h14]) (by bsimp [h20]) (by bsimp [h21]) (by bsimp [])

/-- **`base`'s reference** from `0x8000623c` (`s4 = &_one_`, `s5 =
_one_`), then the other three (`rx_bump2`). -/
theorem rx_bumps {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (g : RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr)
    (st : RxU S X Mt0 M R0 R sp W q H F L xb xe xm z []) (h14 : R 14 = BitVec.ofNat 64 k) :
    DW live S (DQ live S Q t0) 0x8000623c#64 R M := by
  have cx := g.cx
  have ha := g.ha
  rx_facts cx
  have hsf := cx.frame
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  obtain ⟨hb1, hb2, hb3⟩ := st.ptr ha.mb
  have hrb := ha.refs xb ha.mb
  have hcs := ha.cst.transport cx st.ra.out
  have hto : (BitVec.ofNat 64 oneAddr).toNat = oneAddr := rfl
  have hldo : LdOK oneAddr 8 := by simp only [LdOK, oneAddr, tohostAddr]; omega
  have hcst : ∀ b ∈ accAddrs oneAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have hr := RList.refsAt st.heap ha.mb
  have hx := sxw_ofNat (k := xb.rep.refs + rCnt [] xb.rep.p + 1) (by simp [rCnt]; omega)
  bc_run hlive hS [st.r8, hr, hx, hcs.one, hto] at 0x80006254
  all_goals first | exact hldo | exact hcst | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  exact rx_bump2 hlive g ((st.bump cx ha.mb (by omega) (by simp)).regs
      (ks := [15, 20, 21]) (by keeps_tac Keeps.refl _ _))
    (by bsimp []) (by bsimp []) (by bsimp [h14])

/-! ## The `-1` returns and the entry -/

/-- **`-1`** from `0x8000646c` (a zero modulus or a negative exponent), the
frame's registers restored; off the frame nothing changed. -/
theorem rx_m1 {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {L : List NumObj} {xr : NumObj}
    {n : Option Num} (cx : RxCtx S R0 sp W q) (hK : RxK live S X Q t0 R0 Mt0 L xr q sp W n)
    (hn : n = none) (hS : HeapOwn S) (ra : RxAt S Mt0 M R0 R sp W rxSlots1) (h22 : R 22 = R0 22)
    (hout : ∀ a, ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    DW live S (DQ live S Q t0) 0x8000646c#64 R M := by
  bc_run hlive hS [] at 0x80006430
  exact rx_epi hlive cx hS ra.saved (by bsimp [ra.r2]) (by keeps_tac ra.keep) (by bsimp [h22])
    fun R' hk h10 => hK.fail hn R' M hk (by rw [h10]; bsimp []) hout

/-- The state from `0x800061e0` to `0x8000623c`: the frame's registers
saved, off the frame nothing changed; `s0` base, `s8` expo, `s1` `&_zero_`,
`a2` mod, `a3` the slot, `a4` scale, `a6` `_zero_`. -/
structure RxP (S : Nat → Prop) (X : Raws) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (xb xe xm z : NumObj) (k : Nat) : Prop where
  ra : RxAt S Mt0 M R0 R sp W rxSlots1
  r22 : R 22 = R0 22
  heap : BcHeap S X M H F L
  out : ∀ a, ¬ frameIn sp W a → imgM M a = imgM Mt0 a
  r8 : R 8 = BitVec.ofNat 64 xb.rep.p
  r24 : R 24 = BitVec.ofNat 64 xe.rep.p
  r9 : R 9 = BitVec.ofNat 64 zeroAddr
  r12 : R 12 = BitVec.ofNat 64 xm.rep.p
  r13 : R 13 = BitVec.ofNat 64 q
  r14 : R 14 = BitVec.ofNat 64 k
  r16 : R 16 = BitVec.ofNat 64 z.rep.p

/-- Through register changes off the state's. -/
theorem RxP.regs {S : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xb xe xm z : NumObj} {k : Nat}
    (st : RxP S X Mt0 M R0 R sp W q H F L xb xe xm z k) {ks : List Nat} (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ [1, 5, 6, 7, 10, 11, 15, 17, 28, 29, 30, 31] := by decide) :
    RxP S X Mt0 M R0 R' sp W q H F L xb xe xm z k :=
  { st with
    ra := st.ra.regs hk fun z hz => by have := hks z hz; simp only [rxAll, List.mem_cons, List.not_mem_nil, or_false] at this ⊢; omega
    r22 := by rw [hk.get 22 fun hm => by have := hks 22 hm; simp at this]; exact st.r22
    r8 := by rw [hk.get 8 fun hm => by have := hks 8 hm; simp at this]; exact st.r8
    r24 := by rw [hk.get 24 fun hm => by have := hks 24 hm; simp at this]; exact st.r24
    r9 := by rw [hk.get 9 fun hm => by have := hks 9 hm; simp at this]; exact st.r9
    r12 := by rw [hk.get 12 fun hm => by have := hks 12 hm; simp at this]; exact st.r12
    r13 := by rw [hk.get 13 fun hm => by have := hks 13 hm; simp at this]; exact st.r13
    r14 := by rw [hk.get 14 fun hm => by have := hks 14 hm; simp at this]; exact st.r14
    r16 := by rw [hk.get 16 fun hm => by have := hks 16 hm; simp at this]; exact st.r16 }

/-- The entry's fixed facts: the context, the operands at the entry's heap,
the result slot, the continuations. -/
structure RxIn (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (R0 : Nat → BitVec 64) (Mt0 : Mem) (sp W q k : Nat) (H0 : Heap)
    (F0 : List Blk) (L : List NumObj) (xb xe xm z o t xr : NumObj) : Prop where
  cx : RxCtx S R0 sp W q
  ha : RxArgs S Mt0 L xb xe xm z o t k
  hs : RxSlot Mt0 L xr q
  hb : BcHeap S X Mt0 H0 F0 L
  hK : RxK live S X Q t0 R0 Mt0 L xr q sp W (Num.raisemod xb.rep.num xe.rep.num xm.rep.num k)

/-- The entry's facts as `RxGo` once the modulus is nonzero and the exponent
non-negative. -/
theorem RxIn.go {live S : Nat → Prop} {X : Raws} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t0 : String} {R0 : Nat → BitVec 64} {Mt0 : Mem} {sp W q k : Nat} {H0 : Heap}
    {F0 : List Blk} {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (h : RxIn live S X Q t0 R0 Mt0 sp W q k H0 F0 L xb xe xm z o t xr)
    (hm : xm.rep.num.mag ≠ 0) (hp : xe.rep.num.neg = false) :
    RxGo live S X Q t0 R0 Mt0 sp W q k L xb xe xm z o t xr where
  cx := h.cx
  ha := h.ha
  hs := h.hs
  oz := fun e => by
    have hoz := h.hb.eq_of_p h.ha.mo h.ha.mz e
    have h1 := h.ha.oneNum
    rw [hoz] at h1
    have h0 : z.rep.num.mag = 0 := by rw [NumRep.num_mag, h.ha.zero.ds]; rfl
    rw [h1] at h0
    exact absurd h0 (by decide)
  mag := hm
  pos := hp
  zx := fun e => by
    have := h.hb.eq_of_p h.ha.me h.ha.mz e
    rw [this]
    show z.rep.num.mag / 10 ^ z.rep.num.scale = 0
    have h0 : z.rep.num.mag = 0 := by rw [NumRep.num_mag, h.ha.zero.ds]; rfl
    rw [h0, Nat.zero_div]
  oom := h.hK.oom
  ret := fun R' Mt' H' F' Lf y hk h10 hp' =>
    h.hK.ret _ (Dc.BcModel.raisemod_eq _ _ _ _ hm hp) R' Mt' H' F' Lf y hk h10 hp'

/-- **The exponent's sign** at `0x80006230` (the modulus nonzero): negative
returns `-1` (`rx_m1`), otherwise the references (`rx_bumps`). -/
theorem rx_sign {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H H0 : Heap} {F F0 : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (hi : RxIn live S X Q t0 R0 Mt0 sp W q k H0 F0 L xb xe xm z o t xr)
    (hm : xm.rep.num.mag ≠ 0) (st : RxP S X Mt0 M R0 R sp W q H F L xb xe xm z k) :
    DW live S (DQ live S Q t0) 0x80006230#64 R M := by
  have cx := hi.cx
  have ha := hi.ha
  rx_facts cx
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have hn := st.heap.nums xe ha.me
  num_facts hn
  have hsg := hn.sign
  cases hneg : xe.rep.neg
  · rw [hneg] at hsg
    bc_run hlive hS [st.r24, hsg] at 0x8000623c
    all_goals first | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
    exact rx_bumps hlive (hi.go hm (by rw [NumRep.num_neg]; exact hneg))
      { ra := st.ra.regs (ks := [11, 15]) (by keeps_tac Keeps.refl _ _)
        r22 := by bsimp [st.r22]
        heap := by rw [RList.nil]; exact st.heap
        r8 := by bsimp [st.r8]
        r24 := by bsimp [st.r24]
        r9 := by bsimp [st.r9]
        r12 := by bsimp [st.r12]
        r13 := by bsimp [st.r13]
        r16 := by bsimp [st.r16] } (by bsimp [st.r14])
  · rw [hneg] at hsg
    bc_run hlive hS [st.r24, hsg] at 0x8000646c
    all_goals first | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
    refine rx_m1 hlive cx hi.hK ?_ hS (st.ra.regs (ks := [11, 15]) (by keeps_tac Keeps.refl _ _))
      (by bsimp [st.r22]) st.out
    have hz : xm.rep.num.isZero = false := by simpa [Num.isZero] using hm
    simp only [Num.raisemod, hz, NumRep.num_neg, hneg]
    rfl

/-- **The modulus's zero scan** from `0x80006214` (`a5` its digit count,
positive): a nonzero digit continues at `rx_sign`, none returns `-1`. -/
theorem rx_scan {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H H0 : Heap} {F F0 : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (hi : RxIn live S X Q t0 R0 Mt0 sp W q k H0 F0 L xb xe xm z o t xr)
    (st : RxP S X Mt0 M R0 R sp W q H F L xb xe xm z k)
    (h15 : R 15 = BitVec.ofNat 64 (xm.rep.len + xm.rep.scale))
    (hpos : 1 ≤ xm.rep.len + xm.rep.scale) :
    DW live S (DQ live S Q t0) 0x80006214#64 R M := by
  have cx := hi.cx
  have ha := hi.ha
  rx_facts cx
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have hn := st.heap.nums xm ha.mm
  num_facts hn
  bc_run hlive hS [st.r12, hn.value] at 0x80006220
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  refine zscan_80006220 hlive hS hn.shape.dig hn.digit (by omega) (by omega) (by omega)
    (fun R' hex kk => ?_) (fun R' hall kk => ?_) (xm.rep.len + xm.rep.scale - 1) 0 _ (by omega)
    (fun j hj => absurd hj (Nat.not_lt_zero _)) (Keeps.refl _ _) (by bsimp [h15])
    (by bsimp [])
  · have hm : xm.rep.num.mag ≠ 0 := by
      obtain ⟨i0, hi0, hnz⟩ := hex
      rw [NumRep.num_mag]
      intro h0
      exact hnz ((dval_eq_zero_iff _).1 h0 i0 (by rw [hn.shape.dsLen]; exact hi0))
    exact rx_sign hlive hi hm (st.regs (ks := [10, 11, 15]) (kk.trans (by keeps_tac Keeps.refl _ _)))
  · have hz : xm.rep.num.mag = 0 := NumRep.mag_zero_of hn.shape.dsLen hall
    refine rx_m1 hlive cx hi.hK ?_ hS (st.ra.regs (ks := [10, 11, 15])
      (kk.trans (by keeps_tac Keeps.refl _ _)))
      (by rw [kk.get 22 (by decide)]; bsimp [st.r22]) st.out
    have hz' : xm.rep.num.isZero = true := by simp [Num.isZero, hz]
    simp only [Num.raisemod, hz', if_true]

theorem word_sub112 {x : Nat} (h : 112 ≤ x) :
    BitVec.ofNat 64 x + 18446744073709551504#64 = BitVec.ofNat 64 (x - 112) := by
  change BitVec.ofNat 64 x + -(112#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le x 112 (by decide) h

/-- The first two saved registers (`s1`, `ra`). -/
abbrev rxPro0 (M : Mem) (sp : Nat) (R : Nat → BitVec 64) : Mem :=
  writeLog (writeLog M [(sp - 112 + 88, 8, R 9)]) [(sp - 112 + 104, 8, R 1)]

/-- The other seven (`s8`, `s0`, `s2`, `s3`, `s4`, `s5`, `s7`). -/
abbrev rxPro (M : Mem) (sp : Nat) (R : Nat → BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M
    [(sp - 112 + 32, 8, R 24)]) [(sp - 112 + 96, 8, R 8)]) [(sp - 112 + 80, 8, R 18)])
    [(sp - 112 + 72, 8, R 19)]) [(sp - 112 + 64, 8, R 20)]) [(sp - 112 + 56, 8, R 21)])
    [(sp - 112 + 40, 8, R 23)]

theorem rxPro0_saved (M : Mem) (sp : Nat) (R : Nat → BitVec 64) :
    SavedWords (rxPro0 M sp R) (sp - 112) rxSlots0 R :=
  ((SavedWords.nil M (sp - 112) R).store 9 88).store 1 104

theorem rxPro_saved {M : Mem} {sp : Nat} {R : Nat → BitVec 64}
    (h : SavedWords M (sp - 112) rxSlots0 R) : SavedWords (rxPro M sp R) (sp - 112) rxSlots1 R :=
  ((((((h.store 24 32).store 8 96).store 18 80).store 19 72).store 20 64).store 21 56).store 23 40

theorem rxPro0_frame {M : Mem} {sp : Nat} (R : Nat → BitVec 64) (hsp : 112 ≤ sp) :
    MemOnly (frameIn sp 112) (rxPro0 M sp R) M := fun a ha => by
  simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]

theorem rxPro_frame {M : Mem} {sp : Nat} (R : Nat → BitVec 64) (hsp : 112 ≤ sp) :
    MemOnly (frameIn sp 112) (rxPro M sp R) M := fun a ha => by
  simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]

/-- **`-1`** from `0x800064e0` (`mod` has no digits): the epilogue. -/
theorem rx_nodig {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H0 : Heap} {F0 : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (hi : RxIn live S X Q t0 R0 Mt0 sp W q k H0 F0 L xb xe xm z o t xr) {H : Heap} {F : List Blk}
    (st : RxP S X Mt0 M R0 R sp W q H F L xb xe xm z k)
    (h15 : R 15 = BitVec.ofNat 64 0) (hz : xm.rep.len + xm.rep.scale = 0) :
    DW live S (DQ live S Q t0) 0x800064e0#64 R M := by
  have cx := hi.cx
  rx_facts cx
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have ra := st.ra
  have h22 := st.r22
  have hout := st.out
  have hn := hi.hb.nums xm hi.ha.mm
  have hm : xm.rep.num.mag = 0 :=
    NumRep.mag_zero_of hn.shape.dsLen fun j hj => absurd hj (by omega)
  have h0 : BitVec.ofNat 64 0 = 0#64 := rfl
  bc_run hlive hS [h15, h0] at 0x80006430
  exact rx_epi hlive cx hS ra.saved (by bsimp [ra.r2]) (by keeps_tac ra.keep) (by bsimp [h22])
    fun R' hk h10 => hi.hK.fail (by
        have hz' : xm.rep.num.isZero = true := by simp [Num.isZero, hm]
        simp only [Num.raisemod, hz', if_true]) R' M hk (by rw [h10]; bsimp []) hout

/-- The state after the prologue's stores. -/
theorem RxP.ofPro {S : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat}
    {H0 : Heap} {F0 : List Blk} {L : List NumObj} {xb xe xm z : NumObj}
    (hsp : heapEnd + 112 ≤ sp) (hW : 112 ≤ W) (hb : BcHeap S X Mt0 H0 F0 L)
    (sv : SavedWords M (sp - 112) rxSlots0 R0) (hfr : MemOnly (frameIn sp 112) M Mt0)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (hkp : Keeps rxAll R R0) (h22 : R 22 = R0 22)
    (h8 : R 8 = BitVec.ofNat 64 xb.rep.p) (h24 : R 24 = BitVec.ofNat 64 xe.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 zeroAddr) (h12 : R 12 = BitVec.ofNat 64 xm.rep.p)
    (h13 : R 13 = BitVec.ofNat 64 q) (h14 : R 14 = BitVec.ofNat 64 k)
    (h16 : R 16 = BitVec.ofNat 64 z.rep.p) :
    RxP S X Mt0 (rxPro M sp R0) R0 R sp W q H0 F0 L xb xe xm z k := by
  have hm := rxPro_frame (M := M) (sp := sp) R0 (by simp only [heapEnd] at hsp; omega)
  simp only [heapEnd] at hsp
  have hmt : MemOnly (frameIn sp 112) (rxPro M sp R0) Mt0 := fun a h => (hm a h).trans (hfr a h)
  have hout : ∀ a, ¬ frameIn sp W a → imgM (rxPro M sp R0) a = imgM Mt0 a := fun a hf =>
    hmt a fun h => hf (by simp only [frameIn] at h ⊢; omega)
  exact
    { ra := { r2 := h2, saved := rxPro_saved sv, keep := hkp, out := fun a _ hf => hout a hf }
      r22 := h22
      heap := hb.out_frame hmt fun a ha' => by
        simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha' ⊢; omega
      out := hout, r8 := h8, r24 := h24, r9 := h9, r12 := h12, r13 := h13, r14 := h14, r16 := h16 }

/-- **The modulus's digit count** from `0x800061e0` (`mod` not `_zero_`, `s1`
and `ra` saved): seven more saved registers; none returns `-1` (`rx_nodig`),
else the zero scan (`rx_scan`). -/
theorem rx_modz {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H0 : Heap} {F0 : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (hi : RxIn live S X Q t0 R0 Mt0 sp W q k H0 F0 L xb xe xm z o t xr)
    (sv : SavedWords M (sp - 112) rxSlots0 R0) (hfr : MemOnly (frameIn sp 112) M Mt0)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (hkp : Keeps [2, 9, 16] R R0)
    (h9 : R 9 = BitVec.ofNat 64 zeroAddr) (h16 : R 16 = BitVec.ofNat 64 z.rep.p)
    (h10 : R0 10 = BitVec.ofNat 64 xb.rep.p) (h11 : R0 11 = BitVec.ofNat 64 xe.rep.p)
    (h12 : R0 12 = BitVec.ofNat 64 xm.rep.p) (h13 : R0 13 = BitVec.ofNat 64 q)
    (h14 : R0 14 = BitVec.ofNat 64 k) :
    DW live S (DQ live S Q t0) 0x800061e0#64 R M := by
  have cx := hi.cx
  have ha := hi.ha
  rx_facts cx
  have hsf := cx.frame
  have hS : HeapOwn S := fun a h1 h2 => hi.hb.heap.own a h1 h2
  have hn := hi.hb.nums xm ha.mm
  num_facts hn
  have hsz := ha.size
  have g1 := hkp.get 1; have g8 := hkp.get 8; have g18 := hkp.get 18; have g19 := hkp.get 19
  have g20 := hkp.get 20; have g21 := hkp.get 21; have g23 := hkp.get 23; have g24 := hkp.get 24
  have g22 := hkp.get 22
  have e10 : R 10 = BitVec.ofNat 64 xb.rep.p := by rw [hkp.get 10]; exact h10
  have e11 : R 11 = BitVec.ofNat 64 xe.rep.p := by rw [hkp.get 11]; exact h11
  have e12 : R 12 = BitVec.ofNat 64 xm.rep.p := by rw [hkp.get 12]; exact h12
  have ea : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 xm.rep.scale) +
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 xm.rep.len)) =
      BitVec.ofNat 64 (xm.rep.len + xm.rep.scale) := by
    rw [addw_ofNat (by omega), Nat.add_comm]
  have t1 := toInt_ofNat_small (k := xm.rep.len + xm.rep.scale) (by omega)
  have z0 : (0#64).toInt = 0 := by decide
  have hl' : ldv .lw M (xm.rep.p + 4) = BitVec.ofNat 64 xm.rep.len := by
    rw [ldv_congr .lw fun j hj => hfr _ fun h => by
      simp only [frameIn, widthOfM] at h hj; omega]
    exact hn.len
  have hs' : ldv .lw M (xm.rep.p + 8) = BitVec.ofNat 64 xm.rep.scale := by
    rw [ldv_congr .lw fun j hj => hfr _ fun h => by
      simp only [frameIn, widthOfM] at h hj; omega]
    exact hn.scale
  bc_run hlive hS [h2, e12, hs', g1, g8, g18, g19, g20, g21, g23, g24, ea, t1, z0]
    at 0x800064e0 0x80006214
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | skip
  · intro hp
    rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega), hl', ea, t1] at hp
    have hz : xm.rep.len + xm.rep.scale = 0 := by omega
    exact rx_nodig hlive hi (RxP.ofPro (by simp only [heapEnd]; omega) (by omega) hi.hb sv hfr
      (by bsimp [h2]) (by keeps_tac (hkp.mono (by decide))) (by bsimp [g22]) (by bsimp [e10])
      (by bsimp [e11]) (by bsimp [h9]) (by bsimp [e12]) (by bsimp []; rw [hkp.get 13]; exact h13)
      (by bsimp []; rw [hkp.get 14]; exact h14) (by bsimp [h16]))
      (by bsimp []; rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega), hl', ea, hz]) hz
  · intro hp
    rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega), hl', ea, t1] at hp
    exact rx_scan hlive hi (RxP.ofPro (by simp only [heapEnd]; omega) (by omega) hi.hb sv hfr (by bsimp [h2])
      (by keeps_tac (hkp.mono (by decide))) (by bsimp [g22]) (by bsimp [e10]) (by bsimp [e11])
      (by bsimp [h9]) (by bsimp [e12]) (by bsimp []; rw [hkp.get 13]; exact h13)
      (by bsimp []; rw [hkp.get 14]; exact h14) (by bsimp [h16]))
      (by bsimp []; rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega), hl', ea]) (by omega)

/-- **`bc_raisemod (base, expo, mod, result, scale)`** at `0x800061c4`:
`Num.raisemod`'s result in the slot (`RxK.ret`), `-1` for a zero modulus or
a negative exponent (`RxK.fail`), or `out_of_memory` (`RxK.oom`). -/
theorem bc_raisemod_spec {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj}
    (cx : RxCtx S R0 sp W q) (ha : RxArgs S Mt0 L xb xe xm z o t k) (hs : RxSlot Mt0 L xr q)
    (hb : BcHeap S X Mt0 H F L)
    (hK : RxK live S X Q t0 R0 Mt0 L xr q sp W (Num.raisemod xb.rep.num xe.rep.num xm.rep.num k))
    (h10 : R0 10 = BitVec.ofNat 64 xb.rep.p) (h11 : R0 11 = BitVec.ofNat 64 xe.rep.p)
    (h12 : R0 12 = BitVec.ofNat 64 xm.rep.p) (h13 : R0 13 = BitVec.ofNat 64 q)
    (h14 : R0 14 = BitVec.ofNat 64 k) :
    DWO live S Q t0 0x800061c4#64 R0 Mt0 := by
  have hi : RxIn live S X Q t0 R0 Mt0 sp W q k H F L xb xe xm z o t xr := ⟨cx, ha, hs, hb, hK⟩
  rx_facts cx
  have hsf := cx.frame
  have hal := cx.al
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hmn := hb.nums xm ha.mm
  num_facts hmn
  have hzn := hb.nums z ha.mz
  num_facts hzn
  have hcst : ∀ b ∈ accAddrs 2147601864 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  have e1 := ofNat_eq_iff (show xm.rep.p < 2 ^ 64 by omega) (show z.rep.p < 2 ^ 64 by omega)
  have hsp := cx.sp0
  have w112 := word_sub112 (x := sp) (by omega)
  bc_run hlive hS [hsp, w112, h12] at 0x800064cc 0x800061e0
  all_goals first | exact hcst | exact frame_acc hsf (by omega) (by omega) | skip
  · intro he
    have hzg : ldv .ld Mt0 2147601864 = BitVec.ofNat 64 z.rep.p := ha.zero.glob
    rw [ldv_ld_miss _ _ (by omega), hzg, e1] at he
    have hxz : xm = z := hb.eq_of_p ha.mm ha.mz he
    have hz : xm.rep.num.mag = 0 := by rw [hxz, NumRep.num_mag, ha.zero.ds]; rfl
    have hm := rxPro0_frame (M := Mt0) (sp := sp) R0 (by omega)
    exact rx_epi0 hlive cx hS (rxPro0_saved Mt0 sp R0) (by bsimp []) (by keeps_tac Keeps.refl _ _)
      fun R' hk' h10' => hK.fail (by
          have hz' : xm.rep.num.isZero = true := by simp [Num.isZero, hz]
          simp only [Num.raisemod, hz', if_true]) R' _ hk' h10'
        fun a hf => hm a fun h => hf (by simp only [frameIn] at h ⊢; omega)
  · intro _
    exact rx_modz hlive hi (rxPro0_saved Mt0 sp R0) (rxPro0_frame R0 (by omega)) (by bsimp [])
      (by keeps_tac Keeps.refl _ _) (by bsimp [])
      (by bsimp []; rw [ldv_ld_miss _ _ (by omega)]; exact ha.zero.glob) h10 h11 h12 h13 h14

end Dc.Mach
