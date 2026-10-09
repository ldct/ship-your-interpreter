import Dc.Mach.Bc.DivRun

/-!
# `bc_divide`'s setup (`0x8000589c` to the loop head `0x80005d4c`)

- `DvBase`: the frame, heap and buffers before the loop's frame words are
  written (`DvFix` without `s16`–`s88`).
- `dvs_init`: the loop's frame words and `qptr` at `0x80005c40`, landing
  `DvAt` at the first iteration.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- The frame, the number heap with the zeroed quotient `y` at its head, the
three raw buffers, before the loop's frame words are written. -/
structure DvBase (S : Nat → Prop) (Mt0 M : Mem) (R0 : Nat → BitVec 64) (sp W : Nat) (D : DvData)
    (H : Heap) (F : List Blk) (Lh : List NumObj) (y : NumObj) : Prop where
  saved : SavedWords M (sp - 208) divSlots R0
  s8 : ldv .ld M (sp - 208 + 8) = BitVec.ofNat 64 D.Bm
  heap : BcHeap S M H F (y :: Lh)
  owns : y.Owns
  qzero : ∀ j, y.rep.ds.getD j 0 = 0
  b1l : D.b1 ∈ H.live
  b2l : D.b2 ∈ H.live
  b3l : D.b3 ∈ H.live
  b1n : D.b1 ∉ F ++ objBlocks (y :: Lh)
  b2n : D.b2 ∉ F ++ objBlocks (y :: Lh)
  b3n : D.b3 ∉ F ++ objBlocks (y :: Lh)
  b12 : D.b1 ≠ D.b2
  b13 : D.b1 ≠ D.b3
  b23 : D.b2 ≠ D.b3
  pPay : D.P = D.b1.pay
  mPay : D.Bm = D.b3.pay
  pIn : ∀ i, i < D.xs.length → D.b1.In (D.P + i)
  nIn : ∀ i, i ≤ D.L → D.b2.In (D.N + i)
  mIn : ∀ i, i ≤ D.L → D.b3.In (D.Bm + i)
  out : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a

/-- `DvBase` through stores to the frame words `sp - 208 + 16 … + 104`. -/
theorem DvBase.slots {S : Nat → Prop} {Mt0 M M' : Mem} {R0 : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj}
    (bs : DvBase S Mt0 M R0 sp W D H F Lh y) (hab : heapEnd + W ≤ sp) (hW : 208 ≤ W)
    (hm : ∀ a, (a < sp - 208 + 16 ∨ sp - 208 + 104 ≤ a) → imgM M' a = imgM M a) :
    DvBase S Mt0 M' R0 sp W D H F Lh y := by
  have hh : ∀ a, a < heapEnd → imgM M' a = imgM M a := fun a h => hm a (.inl (by omega))
  refine { bs with
    saved := bs.saved.transport (lo := 104) (top := 208) (hag := fun a h1 _ => hm a (.inr h1))
    s8 := by rw [ldv_congr .ld fun j hj => hm _ (.inl (by simp only [widthOfM] at hj; omega))]; exact bs.s8
    heap := bs.heap.transportOwn (fun a ha => hh a (AllocByte.bound bs.heap.heap ha).2)
      (fun c hc a ha => hh a (live_in_heap bs.heap.heap (bs.heap.owned_live hc) ha).2)
      (fun j hj => hh _ (by simp only [bcFreeAddr, heapEnd]; omega))
    out := fun a ho hf => (hm a (by simp only [frameIn] at hf; omega)).trans (bs.out a ho hf) }


/-- `subw` of two small naturals, the first not below the second. -/
theorem subw_ofNat_le {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 30) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) -
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 b)) = BitVec.ofNat 64 (a - b) := by
  rw [subw_nat ha (by omega), show ((a : Int) - b) = ((a - b : Nat) : Int) by omega, ofInt_natCast64]

/-- **The loop head at its first iteration** from `DvBase`, the frame words,
the buffers' digits (the window is the dividend's first `L` digits, below
`V`) and the registers. -/
theorem DvBase.at0 {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj}
    (hs : DvShape D) (bs : DvBase S Mt0 M R0 sp W D H F Lh y)
    (hx : ∀ i, i < D.xs.length → imgM M (D.P + i) = BitVec.ofNat 8 (D.xs.getD i 0))
    (hdiv : ∀ i, i < D.L → imgM M (D.N + i) = BitVec.ofNat 8 (D.vs.getD i 0))
    (hsent : imgM M (D.N + D.L) = 0#8) (hqe : D.off + D.Kb + 1 = y.rep.len + y.rep.scale)
    (s16 : ldv .ld M (sp - 208 + 16) = BitVec.ofNat 64 D.L)
    (s24 : ldv .ld M (sp - 208 + 24) = BitVec.ofNat 64 D.L)
    (s32 : ldv .ld M (sp - 208 + 32) = BitVec.ofNat 64 (D.Bm + 1))
    (s40 : ldv .ld M (sp - 208 + 40) = BitVec.ofNat 64 (D.L + 1))
    (s48 : ldv .ld M (sp - 208 + 48) = BitVec.ofNat 64 (D.L + 1))
    (s56 : ldv .ld M (sp - 208 + 56) = BitVec.ofNat 64 D.qv)
    (s64 : ldv .ld M (sp - 208 + 64) = BitVec.ofNat 64 D.b2.pay)
    (s72 : ldv .ld M (sp - 208 + 72) = BitVec.ofNat 64 D.n2p)
    (s80 : ldv .ld M (sp - 208 + 80) = BitVec.ofNat 64 D.n1p)
    (s88 : ldv .ld M (sp - 208 + 88) = BitVec.ofNat 64 D.rs)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h9 : R 9 = BitVec.ofNat 64 0)
    (h18 : R 18 = BitVec.ofNat 64 D.P) (h24 : R 24 = BitVec.ofNat 64 D.N)
    (h17 : R 17 = BitVec.ofNat 64 (D.vs.getD 0 0))
    (h27 : R 27 = BitVec.ofNat 64 (y.rep.val + D.off + 0)) (h26 : R 26 = BitVec.ofNat 64 D.Kb)
    (hkp : Keeps divAll R R0) :
    DvAt S Mt0 M R0 R sp W D H F Lh y y.rep.ds 0 := by
  have hyn := bs.heap.nums y List.mem_cons_self
  have hxl := hs.xl
  have hl := hs.l1
  have hp0 : D.pre 0 % D.V = D.pre 0 := Nat.mod_eq_of_lt hs.first
  have htl : (D.xs.take D.L).length = D.L := by rw [List.length_take]; omega
  refine ⟨⟨bs.saved, bs.s8, s16, s24, s32, s40, s48, s56, s64, s72, s80, s88, bs.heap,
    bs.heap.head_noView bs.owns, bs.owns, hyn.shape.dsLen, fun e he => ?_, hqe, fun j _ => bs.qzero j,
    bs.b1l, bs.b2l, bs.b3l, bs.b1n, bs.b2n, bs.b3n, bs.b12, bs.b13, bs.b23, bs.pPay, bs.mPay,
    bs.pIn, bs.nIn, bs.mIn, hdiv, hsent, bs.out⟩, ⟨fun i hi => ?_, fun i _ hi => hx i hi, fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
    h2, h9, h18, h24, h17, h27, h26, hkp, Nat.zero_le _⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have := bs.qzero i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    omega
  · rw [Nat.add_zero, hx i (by omega), hp0]
    have hd := dvalBE_digit (hs.xd.take D.L) (i := i) (by omega)
    rw [htl] at hd
    simp only [DvData.pre, Nat.add_zero]
    rw [hd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

/-- `DvBase.at0` after the frame-word stores: the contents carried from the
memory before them. -/
theorem DvBase.at0_of {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj}
    (hs : DvShape D) (bs : DvBase S Mt0 M R0 sp W D H F Lh y) (hab : heapEnd + W ≤ sp)
    (hW : 208 ≤ W)
    (hx : ∀ i, i < D.xs.length → imgM M (D.P + i) = BitVec.ofNat 8 (D.xs.getD i 0))
    (hdiv : ∀ i, i < D.L → imgM M (D.N + i) = BitVec.ofNat 8 (D.vs.getD i 0))
    (hsent : imgM M (D.N + D.L) = 0#8) (hqe : D.off + D.Kb + 1 = y.rep.len + y.rep.scale)
    (hm : ∀ a, (a < sp - 208 + 16 ∨ sp - 208 + 104 ≤ a) → imgM M' a = imgM M a)
    (s16 : ldv .ld M' (sp - 208 + 16) = BitVec.ofNat 64 D.L)
    (s24 : ldv .ld M' (sp - 208 + 24) = BitVec.ofNat 64 D.L)
    (s32 : ldv .ld M' (sp - 208 + 32) = BitVec.ofNat 64 (D.Bm + 1))
    (s40 : ldv .ld M' (sp - 208 + 40) = BitVec.ofNat 64 (D.L + 1))
    (s48 : ldv .ld M' (sp - 208 + 48) = BitVec.ofNat 64 (D.L + 1))
    (s56 : ldv .ld M' (sp - 208 + 56) = BitVec.ofNat 64 D.qv)
    (s64 : ldv .ld M' (sp - 208 + 64) = BitVec.ofNat 64 D.b2.pay)
    (s72 : ldv .ld M' (sp - 208 + 72) = BitVec.ofNat 64 D.n2p)
    (s80 : ldv .ld M' (sp - 208 + 80) = BitVec.ofNat 64 D.n1p)
    (s88 : ldv .ld M' (sp - 208 + 88) = BitVec.ofNat 64 D.rs)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h9 : R 9 = BitVec.ofNat 64 0)
    (h18 : R 18 = BitVec.ofNat 64 D.P) (h24 : R 24 = BitVec.ofNat 64 D.N)
    (h17 : R 17 = BitVec.ofNat 64 (D.vs.getD 0 0))
    (h27 : R 27 = BitVec.ofNat 64 (y.rep.val + D.off + 0)) (h26 : R 26 = BitVec.ofNat 64 D.Kb)
    (hkp : Keeps divAll R R0) :
    DvAt S Mt0 M' R0 R sp W D H F Lh y y.rep.ds 0 := by
  have hi := bs.heap.heap
  simp only [heapEnd] at hab
  have inH : ∀ b, b ∈ H.live → ∀ a, b.In a → imgM M' a = imgM M a := fun b hb a ha =>
    hm a (.inl (by have := (live_in_heap hi hb ha).2; simp only [heapEnd] at this; omega))
  exact DvBase.at0 hs (bs.slots (by simp only [heapEnd]; omega) hW hm)
    (fun i hi' => (inH _ bs.b1l _ (bs.pIn i hi')).trans (hx i hi'))
    (fun i hi' => (inH _ bs.b2l _ (bs.nIn i (by omega))).trans (hdiv i hi'))
    ((inH _ bs.b2l _ (bs.nIn _ (Nat.le_refl _))).trans hsent) hqe
    s16 s24 s32 s40 s48 s56 s64 s72 s80 s88 h2 h9 h18 h24 h17 h27 h26 hkp

/-- The loop's frame words from `0x80005c60` (`qptr` in `s11`). -/
theorem dvs_slots {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {y : NumObj} {len1 k : Nat}
    (cx : DvCtx S sp W) (hs : DvShape D) (bs : DvBase S Mt0 M R0 sp W D H F Lh y)
    (hx : ∀ i, i < D.xs.length → imgM M (D.P + i) = BitVec.ofNat 8 (D.xs.getD i 0))
    (hdiv : ∀ i, i < D.L → imgM M (D.N + i) = BitVec.ofNat 8 (D.vs.getD i 0))
    (hsent : imgM M (D.N + D.L) = 0#8)
    (hkb : D.Kb + D.L = len1 + k) (hle : D.L ≤ len1 + k)
    (hqe : D.off + D.Kb + 1 = y.rep.len + y.rep.scale) (hsz : len1 + k < 2 ^ 30)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 D.n1p)
    (h9 : R 9 = BitVec.ofNat 64 D.n2p) (h18 : R 18 = BitVec.ofNat 64 D.P)
    (h19 : R 19 = BitVec.ofNat 64 D.b2.pay) (h21 : R 21 = BitVec.ofNat 64 D.qv)
    (h22 : R 22 = BitVec.ofNat 64 D.rs)
    (h23 : R 23 = BitVec.ofNat 64 D.L) (h24 : R 24 = BitVec.ofNat 64 D.N)
    (h20 : R 20 = BitVec.ofNat 64 (len1 + k))
    (h16 : R 16 = BitVec.ofNat 64 (D.L + 1)) (h17 : R 17 = BitVec.ofNat 64 (D.vs.getD 0 0))
    (h27 : R 27 = BitVec.ofNat 64 (y.rep.val + D.off))
    (hkp : Keeps divAll R R0)
    (hnext : ∀ R' M', DvAt S Mt0 M' R0 R' sp W D H F Lh y y.rep.ds 0 →
      DW live S Q 0x80005d4c#64 R' M') :
    DW live S Q 0x80005c60#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => bs.heap.heap.own a h1 h2
  have hl1 := hs.l1
  have s8 := bs.s8
  have hkL : D.L < 2 ^ 32 := by omega
  have hkL1 : D.L + 1 < 2 ^ 32 := by omega
  bc_run hlive hS [h2, h8, h9, h16, h17, h18, h19, h20, h21, h22, h23, h24, h27, s8,
    shl_shr32 hkL, shl_shr32 hkL1, subw_ofNat_le hle (by omega)] at 0x80005d4c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine hnext _ _ (DvBase.at0_of hs bs (by simp only [heapEnd]; omega) (by omega) hx hdiv hsent hqe
    (fun a ha => by simp (disch := omega) only [imgM_store_miss])
    (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
    (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
    (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
    (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
    (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
    (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
    (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
    (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
    (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
    (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
    (by bsimp [h2]) (by bsimp []) (by bsimp [h18]) (by bsimp [h24]) (by bsimp [h17])
    (by bsimp [h27]) (by bsimp []; congr 1; omega) (by keeps_tac hkp))

/-- **The loop's frame words** at `0x80005c40`: `qptr` (`n_value`, past
`len2 - len1` zeros when `len1 < len2`), `16(sp)`–`88(sp)`, `s1 = 0`,
`s10 = len1 + scale - len2`; the loop head at its first iteration. -/
theorem dvs_init {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {y : NumObj} {len1 k : Nat}
    (cx : DvCtx S sp W) (hs : DvShape D) (bs : DvBase S Mt0 M R0 sp W D H F Lh y)
    (hx : ∀ i, i < D.xs.length → imgM M (D.P + i) = BitVec.ofNat 8 (D.xs.getD i 0))
    (hdiv : ∀ i, i < D.L → imgM M (D.N + i) = BitVec.ofNat 8 (D.vs.getD i 0))
    (hsent : imgM M (D.N + D.L) = 0#8)
    (hoff : D.off = D.L - len1) (hkb : D.Kb + D.L = len1 + k) (hle : D.L ≤ len1 + k)
    (hqe : D.off + D.Kb + 1 = y.rep.len + y.rep.scale) (hsz : len1 + k < 2 ^ 30)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 D.n1p)
    (h9 : R 9 = BitVec.ofNat 64 D.n2p) (h18 : R 18 = BitVec.ofNat 64 D.P)
    (h19 : R 19 = BitVec.ofNat 64 D.b2.pay) (h21 : R 21 = BitVec.ofNat 64 D.qv)
    (hqv : D.qv = y.sb.pay) (h22 : R 22 = BitVec.ofNat 64 D.rs)
    (h23 : R 23 = BitVec.ofNat 64 D.L) (h24 : R 24 = BitVec.ofNat 64 D.N)
    (h26 : R 26 = BitVec.ofNat 64 len1) (h20 : R 20 = BitVec.ofNat 64 (len1 + k))
    (h16 : R 16 = BitVec.ofNat 64 (D.L + 1)) (h17 : R 17 = BitVec.ofNat 64 (D.vs.getD 0 0))
    (hkp : Keeps divAll R R0)
    (hnext : ∀ R' M', DvAt S Mt0 M' R0 R' sp W D H F Lh y y.rep.ds 0 →
      DW live S Q 0x80005d4c#64 R' M') :
    DW live S Q 0x80005c40#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => bs.heap.heap.own a h1 h2
  have hyn := bs.heap.nums y List.mem_cons_self
  num_facts hyn
  have hyp := (bs.heap.blocks y List.mem_cons_self).sPay
  have hval : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by rw [← hyp]; exact hyn.value
  have hl1 := hs.l1
  rw [hqv] at h21
  have hyl1 : y.rep.val + (D.L - len1) < 2 ^ 64 := by omega
  bc_run hlive hS [h2, h21, hval, h23, h26] at 0x80005c60
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro hge
    exact dvs_slots hlive cx hs bs hx hdiv hsent hkb hle hqe hsz (by bsimp [h2]) (by bsimp [h8])
      (by bsimp [h9]) (by bsimp [h18]) (by bsimp [h19]) (by bsimp [h21, hqv]) (by bsimp [h22])
      (by bsimp [h23]) (by bsimp [h24]) (by bsimp [h20]) (by bsimp [h16]) (by bsimp [h17])
      (by bsimp [hoff, show D.L - len1 = 0 by omega]) (by keeps_tac hkp) hnext
  · intro hlt
    bc_run hlive hS [h2, h21, hval, h23, h26, shl_shr32 (show len1 < 2 ^ 32 by omega),
      shl_shr32 (show D.L < 2 ^ 32 by omega), sub_ofNat (show len1 ≤ D.L by omega) (by omega)]
      at 0x80005c60
    exact dvs_slots hlive cx hs bs hx hdiv hsent hkb hle hqe hsz (by bsimp [h2]) (by bsimp [h8])
      (by bsimp [h9]) (by bsimp [h18]) (by bsimp [h19]) (by bsimp [h21, hqv]) (by bsimp [h22])
      (by bsimp [h23]) (by bsimp [h24]) (by bsimp [h20]) (by bsimp [h16]) (by bsimp [h17])
      (by bsimp [hoff]) (by keeps_tac hkp) hnext

end

end Dc.Mach
