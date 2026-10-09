import Dc.Mach.Bc.RaiseModExit

/-!
# `bc_raisemod` from its entry (`0x800061c4`)

    61c4 mod == _zero_: -1 (`rx_epi0`); bc_is_zero (mod): -1; expo negative: -1
    623c one reference added to base, expo, _one_, _zero_ (`RList.bump`)
    6298 the scale warnings; a scale in expo: exponent = expo / 1 at scale 0
    62ac exponent == _zero_: the result `_one_` (`rx_exit`); otherwise
         rscale = MAX (scale, base->n_scale), the loop (`rx_loop`), `rx_fin`

- `RList.bump`: one more reference to a caller's number is a reference handle.
- `RxW`: the state after the bumps; `RxW.warn` through `rt_warn`.
- `rx_go`: from `0x800062ac` to the result.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## References added by the entry -/

/-- **One more reference** to the caller's `y`: its count raised in the
heap is a reference handle added last. -/
theorem RList.bump {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {hs : List RH}
    {L : List NumObj} {y : NumObj} (hb : BcHeap S M H F (RList hs L)) (hy : y ∈ L)
    {v : BitVec 64} (hv : v.toNat % 2 ^ 32 = y.rep.refs + rCnt hs y.rep.p + 1)
    (hr : y.rep.refs + rCnt hs y.rep.p + 1 < 2 ^ 31) :
    BcHeap S (writeLog M [(y.rep.p + 12, 4, v)]) H F (RList (hs ++ [.ref y]) L) := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hy
  have hd : ∀ w ∈ A ++ B, w.rep.p ≠ y.rep.p := fun w hw =>
    (PDist.caller hb.pdist).ne w hw
  rw [RList.ref_split] at hb
  rw [← RList.addRef hs hd]
  exact hb.setRefs (k := (rBump hs y).rep.refs + 1) hv hr

/-- The count `bc_raisemod` reads before raising it. -/
theorem RList.refsAt {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {hs : List RH}
    {L : List NumObj} {y : NumObj} (hb : BcHeap S M H F (RList hs L)) (hy : y ∈ L) :
    ldv .lw M (y.rep.p + 12) = BitVec.ofNat 64 (y.rep.refs + rCnt hs y.rep.p) :=
  (hb.nums _ (RList.mem_caller hs hy)).refs

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
exponent, temp, parity] = [base, hE, _one_, _zero_]`, the exponent `hE`
holding the integer `m`; `s0` `base`, `s8` the exponent, `s1` `&_zero_`, `s2`
`mod`, `s3` `scale`, `s4` `&_one_`, `s5` `_one_`, `s7` the result slot. -/
structure RxW (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (xb xm z o : NumObj) (k Ee : Nat) (hE : RH)
    (m : Nat) : Prop where
  ra : RxAt S Mt0 M R0 R sp W rxSlots1
  r22 : R 22 = R0 22
  heap : BcHeap S M H F (RList [.ref xb, hE, .ref o, .ref z] L)
  own : RHOwn [.ref xb, hE, .ref o, .ref z] L
  okE : RHOK L hE
  vE : RxNum hE ⟨false, m, 0⟩ Ee 0
  nE : hE.base.rep.Norm
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

/-- Through register changes off the state's. -/
theorem RxW.regs {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xb xm z o : NumObj} {k Ee : Nat} {hE : RH}
    {m : Nat} (h : RxW S Mt0 M R0 R sp W q H F L xb xm z o k Ee hE m) {ks : List Nat}
    (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] :=
      by decide) :
    RxW S Mt0 M R0 R' sp W q H F L xb xm z o k Ee hE m :=
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

/-- A caller's number referenced. -/
theorem RHOK.ofMem {L : List NumObj} {y : NumObj} (hy : y ∈ L) (hr : 1 ≤ y.rep.refs) :
    RHOK L (.ref y) := by
  obtain ⟨A, B, e⟩ := List.append_of_mem hy
  exact ⟨A, B, e, hr⟩

/-- **The exponent `_zero_` itself** at `0x800063bc`: the result `_one_`. -/
theorem rx_one {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k Ee m : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj} {hE : RH} (cx : RxCtx S R0 sp W q)
    (ha : RxArgs S Mt0 L xb xe xm z o t k) (hs0 : RxSlot Mt0 L xr q) (hoz : o.rep.p ≠ z.rep.p)
    (st : RxW S Mt0 M R0 R sp W q H F L xb xm z o k Ee hE m)
    (hret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
      RxPost S Mt0 Mt' H' F' L xr q sp W Num.one Lf y → DW live S Q (R0 1) R' Mt') :
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
theorem rx_start {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q k Ee m : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj} {hE : RH} (cx : RxCtx S R0 sp W q)
    (ha : RxArgs S Mt0 L xb xe xm z o t k) (hs0 : RxSlot Mt0 L xr q) (hoz : o.rep.p ≠ z.rep.p)
    (hmag : xm.rep.num.mag ≠ 0) (hEe : Ee = xe.rep.len + xe.rep.scale + 1)
    (hoom : DmOom live S (DQ live S Q t0) Mt0 sp W)
    (st : RxW S Mt0 M R0 R sp W q H F L xb xm z o k Ee hE m) (hne : hE.p ≠ z.rep.p)
    (hk : Keeps [15, 20, 22] R' R) (h20 : R' 20 = BitVec.ofNat 64 (max k xb.rep.scale))
    (h22 : R' 22 = BitVec.ofNat 64 twoAddr)
    (hret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
      RxPost S Mt0 Mt' H' F' L xr q sp W
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
theorem rx_go {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k Ee m : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {xb xe xm z o t xr : NumObj} {hE : RH} (cx : RxCtx S R0 sp W q)
    (ha : RxArgs S Mt0 L xb xe xm z o t k) (hs0 : RxSlot Mt0 L xr q) (hoz : o.rep.p ≠ z.rep.p)
    (hmag : xm.rep.num.mag ≠ 0) (hEe : Ee = xe.rep.len + xe.rep.scale + 1)
    (hoom : DmOom live S (DQ live S Q t0) Mt0 sp W)
    (st : RxW S Mt0 M R0 R sp W q H F L xb xm z o k Ee hE m) (hz : hE.p = z.rep.p → m = 0)
    (hret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
      RxPost S Mt0 Mt' H' F' L xr q sp W
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
    exact rx_one hlive cx ha hs0 hoz (st.regs (ks := [15]) (by keeps_tac Keeps.refl _ _)) hret
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

end Dc.Mach
