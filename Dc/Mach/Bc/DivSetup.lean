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
structure DvBase (S : Nat → Prop) (X : Raws) (Mt0 M : Mem) (R0 : Nat → BitVec 64) (sp W : Nat) (D : DvData)
    (H : Heap) (F : List Blk) (Lh : List NumObj) (y : NumObj) : Prop where
  saved : SavedWords M (sp - 208) divSlots R0
  s8 : ldv .ld M (sp - 208 + 8) = BitVec.ofNat 64 D.Bm
  heap : BcHeap S X M H F (y :: Lh)
  owns : y.Owns
  qzero : ∀ j, y.rep.ds.getD j 0 = 0
  b1l : D.b1 ∈ H.live
  b2l : D.b2 ∈ H.live
  b3l : D.b3 ∈ H.live
  b1n : D.b1 ∉ F ++ objBlocks (y :: Lh) ++ X.bs
  b2n : D.b2 ∉ F ++ objBlocks (y :: Lh) ++ X.bs
  b3n : D.b3 ∉ F ++ objBlocks (y :: Lh) ++ X.bs
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
theorem DvBase.slots {S : Nat → Prop} {X : Raws} {Mt0 M M' : Mem} {R0 : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj}
    (bs : DvBase S X Mt0 M R0 sp W D H F Lh y) (hab : heapEnd + W ≤ sp) (hW : 208 ≤ W)
    (hm : ∀ a, (a < sp - 208 + 16 ∨ sp - 208 + 104 ≤ a) → imgM M' a = imgM M a) :
    DvBase S X Mt0 M' R0 sp W D H F Lh y := by
  have hh : ∀ a, a < heapEnd → imgM M' a = imgM M a := fun a h => hm a (.inl (by omega))
  refine { bs with
    saved := bs.saved.transport (lo := 104) (top := 208) (hag := fun a h1 _ => hm a (.inr h1))
    s8 := by rw [ldv_congr .ld fun j hj => hm _ (.inl (by simp only [widthOfM] at hj; omega))]; exact bs.s8
    heap := bs.heap.transportOwn (fun a ha => hh a (AllocByte.bound bs.heap.heap ha).2)
      (fun c hc a ha => hh a (live_in_heap bs.heap.heap (bs.heap.owned_live hc) ha).2)
      (fun j hj => hh _ (by simp only [bcFreeAddr, heapEnd]; omega))
    out := fun a ho hf => (hm a (by simp only [frameIn] at hf; omega)).trans (bs.out a ho hf) }


/-- A live payload byte is at least 16 bytes into the heap. -/
theorem live_pay_lo {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {b : Blk}
    (hb : b ∈ H.live) {a : Nat} (ha : b.In a) : heapStart + 16 ≤ a := by
  have h1 : 2147603920 ≤ b.h := (hi.blk (List.mem_append_right _ hb)).lo
  simp only [Blk.In, Blk.pay] at ha
  simp only [heapStart]; omega

/-- The bytes the setup's buffer work may change: the three raw buffers and
the stack below the frame. -/
abbrev DvRawBytes (sp W : Nat) (D : DvData) (a : Nat) : Prop :=
  D.b1.In a ∨ D.b2.In a ∨ D.b3.In a ∨ (sp - W ≤ a ∧ a < sp - 208)

/-- `DvBase` through stores to the raw buffers and below the frame. -/
theorem DvBase.raw {S : Nat → Prop} {X : Raws} {Mt0 M M' : Mem} {R0 : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj}
    (bs : DvBase S X Mt0 M R0 sp W D H F Lh y) (hab : heapEnd + W ≤ sp) (hW : 208 ≤ W)
    (hm : MemOnly (DvRawBytes sp W D) M' M) : DvBase S X Mt0 M' R0 sp W D H F Lh y := by
  have hi := bs.heap.heap
  have inH : ∀ b, b ∈ H.live → ∀ a, b.In a → a < heapEnd := fun b hb a ha =>
    (live_in_heap hi hb ha).2
  have hfr : ∀ a, sp - 208 ≤ a → imgM M' a = imgM M a := fun a ha => hm a fun h => by
    rcases h with h | h | h | h
    · have := inH _ bs.b1l a h; omega
    · have := inH _ bs.b2l a h; omega
    · have := inH _ bs.b3l a h; omega
    · omega
  refine { bs with
    saved := bs.saved.transport (lo := 0) (top := 208) (hag := fun a h1 _ => hfr a (by omega))
    s8 := by rw [ldv_congr .ld fun j _ => hfr _ (by omega)]; exact bs.s8
    heap := bs.heap.transportOwn
      (fun a ha => hm a fun h => by
        rcases h with h | h | h | h
        · exact live_not_alloc hi bs.b1l h ha
        · exact live_not_alloc hi bs.b2l h ha
        · exact live_not_alloc hi bs.b3l h ha
        · have := (AllocByte.bound hi ha).2; omega)
      (fun c hc a ha => hm a fun h => by
        have hcl := bs.heap.owned_live hc
        rcases h with h | h | h | h
        · exact live_apart hi bs.b1l hcl (fun e => bs.b1n (e ▸ hc)) h ha
        · exact live_apart hi bs.b2l hcl (fun e => bs.b2n (e ▸ hc)) h ha
        · exact live_apart hi bs.b3l hcl (fun e => bs.b3n (e ▸ hc)) h ha
        · have := live_in_heap hi hcl ha; omega)
      (fun j hj => hm _ fun h => by
        rcases h with h | h | h | h
        · have := live_in_heap hi bs.b1l h; simp only [bcFreeAddr, heapStart, heapEnd] at this; omega
        · have := live_in_heap hi bs.b2l h; simp only [bcFreeAddr, heapStart, heapEnd] at this; omega
        · have := live_in_heap hi bs.b3l h; simp only [bcFreeAddr, heapStart, heapEnd] at this; omega
        · simp only [bcFreeAddr, heapEnd] at h hab; omega)
    out := fun a ho hn => (hm a fun h => by
        rcases h with h | h | h | h
        · exact ho.1 (live_in_heap hi bs.b1l h)
        · exact ho.1 (live_in_heap hi bs.b2l h)
        · exact ho.1 (live_in_heap hi bs.b3l h)
        · exact hn ⟨by omega, by omega⟩).trans (bs.out a ho hn) }

/-- `subw` of two small naturals, the first not below the second. -/
theorem subw_ofNat_le {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 30) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) -
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 b)) = BitVec.ofNat 64 (a - b) := by
  rw [subw_nat ha (by omega), show ((a : Int) - b) = ((a - b : Nat) : Int) by omega, ofInt_natCast64]

/-- **The loop head at its first iteration** from `DvBase`, the frame words,
the buffers' digits (the window is the dividend's first `L` digits, below
`V`) and the registers. -/
theorem DvBase.at0 {S : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj}
    (hs : DvShape D) (bs : DvBase S X Mt0 M R0 sp W D H F Lh y)
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
    DvAt S X Mt0 M R0 R sp W D H F Lh y y.rep.ds 0 := by
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
theorem DvBase.at0_of {S : Nat → Prop} {X : Raws} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj}
    (hs : DvShape D) (bs : DvBase S X Mt0 M R0 sp W D H F Lh y) (hab : heapEnd + W ≤ sp)
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
    DvAt S X Mt0 M' R0 R sp W D H F Lh y y.rep.ds 0 := by
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
theorem dvs_slots {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {y : NumObj} {len1 k : Nat}
    (cx : DvCtx S sp W) (hs : DvShape D) (bs : DvBase S X Mt0 M R0 sp W D H F Lh y)
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
    (hnext : ∀ R' M', DvAt S X Mt0 M' R0 R' sp W D H F Lh y y.rep.ds 0 →
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
theorem dvs_init {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {y : NumObj} {len1 k : Nat}
    (cx : DvCtx S sp W) (hs : DvShape D) (bs : DvBase S X Mt0 M R0 sp W D H F Lh y)
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
    (hnext : ∀ R' M', DvAt S X Mt0 M' R0 R' sp W D H F Lh y y.rep.ds 0 →
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


/-! ## Normalisation (`0x80005be0`) -/

/-- The registers the normalisation may change. -/
abbrev normClob : List Nat := [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 27, 28, 29, 30, 31]

/-- The second `_one_mult` at `0x80005c24`: the divisor's `L` digits at `N`
times `norm`, in place; then `a7 = vs[0]`, `a6 = L + 1`. -/
theorem dvs_norm2 {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {y : NumObj} {vs0 : List Nat} {nm : Nat}
    (cx : DvCtx S sp W) (bs : DvBase S X Mt0 M R0 sp W D H F Lh y)
    (hv0l : vs0.length = D.L) (hv0d : IsDigits vs0) (hv00 : 0 < vs0.getD 0 0)
    (hnm : nm = 10 / (vs0.getD 0 0 + 1)) (hn1 : nm ≠ 1)
    (hV : D.vs = digBE (dvalBE vs0 * nm) D.L) (hL1 : 1 ≤ D.L) (hLs : D.L < 2 ^ 30)
    (hv : ∀ i, i < D.L → imgM M (D.N + i) = BitVec.ofNat 8 (vs0.getD i 0))
    (hsent : imgM M (D.N + D.L) = 0#8)
    (s16 : ldv .ld M (sp - 208 + 16) = BitVec.ofNat 64 (D.L + 1))
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h23 : R 23 = BitVec.ofNat 64 D.L)
    (h24 : R 24 = BitVec.ofNat 64 D.N) (h27 : R 27 = BitVec.ofNat 64 nm)
    (hnext : ∀ R' M', DvBase S X Mt0 M' R0 sp W D H F Lh y →
      (∀ a, ¬ D.b2.In a → ¬ (sp - W ≤ a ∧ a < sp - 208) → imgM M' a = imgM M a) →
      (∀ i, i < D.L → imgM M' (D.N + i) = BitVec.ofNat 8 (D.vs.getD i 0)) →
      imgM M' (D.N + D.L) = 0#8 → R' 17 = BitVec.ofNat 64 (D.vs.getD 0 0) →
      R' 16 = BitVec.ofNat 64 (D.L + 1) → Keeps normClob R' R →
      DW live S Q 0x80005c40#64 R' M') :
    DW live S Q 0x80005c24#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := bs.heap.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hn0 := live_pay_lo hi bs.b2l (bs.nIn 0 (Nat.zero_le _))
  have hnL := live_in_heap hi bs.b2l (bs.nIn D.L (Nat.le_refl _))
  simp only [heapStart, heapEnd, Nat.add_zero] at hn0 hnL hab
  have hd0 := hv0d.getD 0
  obtain ⟨hnp, hn5⟩ := norm_pos hv00 hd0
  have hnm10 : nm < 10 := by omega
  bc_run hlive hS [h2, h23, h24, h27] at 0x80003ebc
  have hoa : OmArgs M D.N D.L nm D.N vs0 :=
    ⟨hv0l, hv0d, hv, hnm10, by omega, by simp only [heapStart]; omega, by simp only [heapEnd]; omega,
      by simp only [heapStart]; omega, by simp only [heapEnd]; omega, .inl rfl, fun h => absurd h hn1⟩
  refine one_mult_spec hlive (cx.om hS (by bsimp [h2]) (by bsimp [])) hoa (by bsimp [])
    (by bsimp []) (by bsimp []) (by bsimp []) fun R1 M1 hk1 hp => ?_
  bsimp []
  -- the product fits: no carry
  have hV0 : dvalBE vs0 * nm < 10 ^ D.L := by
    have hsp := dvalBE_digit hv0d (i := 0) (by omega)
    rw [hv0l, Nat.sub_zero] at hsp
    have hlt := dvalBE_lt hv0d
    rw [hv0l] at hlt
    have hE : 0 < 10 ^ (D.L - 1) := Nat.pow_pos (by decide)
    have hpw : 10 ^ D.L = 10 * 10 ^ (D.L - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have htop : dvalBE vs0 / 10 ^ (D.L - 1) < 10 := by
      rw [Nat.div_lt_iff_lt_mul hE]; omega
    rw [Nat.mod_eq_of_lt htop] at hsp
    have hb := (norm_bounds (E := 10 ^ (D.L - 1)) (Vr := dvalBE vs0 % 10 ^ (D.L - 1)) hv00 hd0
      (Nat.mod_lt _ hE)).1
    have e : dvalBE vs0 * nm = (vs0.getD 0 0 * 10 ^ (D.L - 1) + dvalBE vs0 % 10 ^ (D.L - 1)) *
        (10 / (vs0.getD 0 0 + 1)) := by
      rw [← hnm, ← hsp, Nat.mul_comm (dvalBE vs0 / _), Nat.div_add_mod]
    rw [e, hpw]; exact hb
  have hc0 : dvalBE vs0 * nm / 10 ^ D.L = 0 := Nat.div_eq_of_lt hV0
  have hfr : ∀ a, ¬ D.b2.In a → ¬ (sp - W ≤ a ∧ a < sp - 208) → imgM M1 a = imgM M a := by
    intro a h2' h3
    rcases Nat.lt_or_ge (a + 1) D.N with h | h
    · exact hp.rest a (.inl h) (by simp only [frameIn]; omega)
    rcases Nat.lt_or_ge a (D.N + D.L) with h' | h'
    · rcases Nat.lt_or_ge a D.N with h'' | h''
      · rw [show a = D.N - 1 by omega]; exact hp.keep hc0
      · exfalso; apply h2'
        have := bs.nIn (a - D.N) (by omega)
        rwa [show D.N + (a - D.N) = a by omega] at this
    · exact hp.rest a (.inr h') (by simp only [frameIn]; omega)
  have bs1 := bs.raw (by simp only [heapEnd]; omega) (by omega) fun a ha =>
    hfr a (fun h => ha (.inr (.inl h))) (fun h => ha (.inr (.inr (.inr h))))
  have hvs : ∀ i, i < D.L → imgM M1 (D.N + i) = BitVec.ofNat 8 (D.vs.getD i 0) := fun i hi' => by
    rw [hp.digits i hi', hV, digBE_getD hi']
  have hn00 := live_in_heap hi bs.b2l (bs.nIn 0 (Nat.zero_le _))
  have hl0 : ldv .lbu M1 D.N = BitVec.ofNat 64 (D.vs.getD 0 0) := by
    have := hvs 0 (by omega); rw [Nat.add_zero] at this
    exact lbu_digit (by rw [hV, digBE_getD (by omega)]; exact Nat.mod_lt _ (by decide)) this
  have s16' : ldv .ld M1 (sp - 208 + 16) = BitVec.ofNat 64 (D.L + 1) := by
    rw [ldv_congr .ld fun j hj => hp.rest _ (.inr (by simp only [widthOfM] at hj; omega))
      (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact s16
  have h24' : R1 24 = BitVec.ofNat 64 D.N := by rw [hk1.get 24]; bsimp [h24]
  have h2' : R1 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk1.get 2]; bsimp [h2]
  bc_run hlive hS [h24', h2', hl0, s16'] at 0x80005c40
  all_goals first | exact acc_heap hS (by omega) (by omega) | dc_frame cx.frame | skip
  exact hnext _ _ bs1 hfr hvs
    ((hp.rest _ (.inr (Nat.le_refl _)) (by simp only [frameIn]; omega)).trans hsent)
    (by bsimp []) (by bsimp []) (by
      keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps normClob _ R)))


/-- The dividend buffer's value with its last digit zero: ten times its
first `T - 1` digits, and those below `10^(T-2)` when the first digit is zero. -/
theorem dvx_split {xs : List Nat} (hd : IsDigits xs) (hl : 2 ≤ xs.length)
    (h0 : xs.getD 0 0 = 0) (hz : xs.getD (xs.length - 1) 0 = 0) :
    dvalBE xs = 10 * dvalBE (xs.take (xs.length - 1)) ∧
      dvalBE (xs.take (xs.length - 1)) < 10 ^ (xs.length - 2) := by
  have ht := dvalBE_take hd (xs.length - 1)
  rw [show xs.length - (xs.length - 1) = 1 by omega, Nat.pow_one] at ht
  have hlast := dvalBE_digit hd (i := xs.length - 1) (by omega)
  rw [show xs.length - 1 - (xs.length - 1) = 0 by omega, Nat.pow_zero, Nat.div_one, hz] at hlast
  have hfirst := dvalBE_digit hd (i := 0) (by omega)
  rw [Nat.sub_zero, h0] at hfirst
  have hlt := dvalBE_lt hd
  have hp : 10 ^ xs.length = 10 * 10 ^ (xs.length - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hp2 : 10 ^ (xs.length - 1) = 10 * 10 ^ (xs.length - 2) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hE : 0 < 10 ^ (xs.length - 1) := Nat.pow_pos (by decide)
  have htop : dvalBE xs / 10 ^ (xs.length - 1) < 10 := by rw [Nat.div_lt_iff_lt_mul hE]; omega
  rw [Nat.mod_eq_of_lt htop] at hfirst
  have hX : dvalBE xs < 10 ^ (xs.length - 1) := by
    have := Nat.div_add_mod (dvalBE xs) (10 ^ (xs.length - 1))
    rw [hfirst, Nat.mul_zero, Nat.zero_add] at this
    rw [← this]; exact Nat.mod_lt _ hE
  rw [ht]
  constructor
  · have := Nat.div_add_mod (dvalBE xs) 10; omega
  · rw [Nat.div_lt_iff_lt_mul (by decide)]; omega

/-- The normalised dividend's digits from `_one_mult` of the first `T - 1`. -/
theorem dvx_norm_digit {xs : List Nat} (hd : IsDigits xs) (hl : 2 ≤ xs.length)
    (h0 : xs.getD 0 0 = 0) (hz : xs.getD (xs.length - 1) 0 = 0) (nm : Nat) {i : Nat}
    (hi : i < xs.length - 1) :
    (digBE (dvalBE xs * nm) xs.length).getD i 0 =
      dvalBE (xs.take (xs.length - 1)) * nm / 10 ^ (xs.length - 1 - 1 - i) % 10 := by
  obtain ⟨e, -⟩ := dvx_split hd hl h0 hz
  rw [digBE_getD (by omega), e, show xs.length - 1 - i = (xs.length - 1 - 1 - i) + 1 by omega,
    Nat.pow_succ, Nat.mul_comm 10, Nat.mul_assoc, Nat.mul_comm 10 nm, ← Nat.mul_assoc,
    Nat.mul_div_mul_right _ _ (by decide)]

theorem dvx_norm_last {xs : List Nat} (hd : IsDigits xs) (hl : 2 ≤ xs.length)
    (h0 : xs.getD 0 0 = 0) (hz : xs.getD (xs.length - 1) 0 = 0) (nm : Nat) :
    (digBE (dvalBE xs * nm) xs.length).getD (xs.length - 1) 0 = 0 := by
  obtain ⟨e, -⟩ := dvx_split hd hl h0 hz
  rw [digBE_getD (by omega), e, show xs.length - 1 - (xs.length - 1) = 0 by omega, Nat.pow_zero,
    Nat.div_one, Nat.mul_assoc, Nat.mul_mod_right]


/-- **The normalisation** at `0x80005be0`: `norm = 10 / (v0 + 1)`; unless it
is `1`, `_one_mult` of the dividend's first `T - 1` digits and of the
divisor's `L` digits, in place. -/
theorem dvs_norm {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {y : NumObj} {xs0 vs0 : List Nat}
    (cx : DvCtx S sp W) (bs : DvBase S X Mt0 M R0 sp W D H F Lh y)
    (hx0l : xs0.length = D.xs.length) (hx0d : IsDigits xs0) (hx2 : 2 ≤ xs0.length)
    (hx00 : xs0.getD 0 0 = 0) (hx0z : xs0.getD (xs0.length - 1) 0 = 0)
    (hv0l : vs0.length = D.L) (hv0d : IsDigits vs0) (hv00 : 0 < vs0.getD 0 0)
    (hX : D.xs = digBE (dvalBE xs0 * (10 / (vs0.getD 0 0 + 1))) xs0.length)
    (hV : D.vs = digBE (dvalBE vs0 * (10 / (vs0.getD 0 0 + 1))) D.L) (hL1 : 1 ≤ D.L)
    (hLs : D.L < 2 ^ 30) (hTs : xs0.length < 2 ^ 30)
    (hx : ∀ i, i < xs0.length → imgM M (D.P + i) = BitVec.ofNat 8 (xs0.getD i 0))
    (hv : ∀ i, i < D.L → imgM M (D.N + i) = BitVec.ofNat 8 (vs0.getD i 0))
    (hsent : imgM M (D.N + D.L) = 0#8)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h16 : R 16 = BitVec.ofNat 64 (D.L + 1))
    (h18 : R 18 = BitVec.ofNat 64 D.P) (h23 : R 23 = BitVec.ofNat 64 D.L)
    (h24 : R 24 = BitVec.ofNat 64 D.N) (h25 : R 25 = BitVec.ofNat 64 (xs0.length - 2))
    (hnext : ∀ R' M', DvBase S X Mt0 M' R0 sp W D H F Lh y →
      (∀ i, i < D.xs.length → imgM M' (D.P + i) = BitVec.ofNat 8 (D.xs.getD i 0)) →
      (∀ i, i < D.L → imgM M' (D.N + i) = BitVec.ofNat 8 (D.vs.getD i 0)) →
      imgM M' (D.N + D.L) = 0#8 → R' 17 = BitVec.ofNat 64 (D.vs.getD 0 0) →
      R' 16 = BitVec.ofNat 64 (D.L + 1) → Keeps normClob R' R →
      DW live S Q 0x80005c40#64 R' M') :
    DW live S Q 0x80005be0#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := bs.heap.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hn0 := live_pay_lo hi bs.b2l (bs.nIn 0 (Nat.zero_le _))
  have hnL := live_in_heap hi bs.b2l (bs.nIn D.L (Nat.le_refl _))
  simp only [heapStart, heapEnd, Nat.add_zero] at hn0 hnL hab
  have hd0 := hv0d.getD 0
  obtain ⟨hnp, hn5⟩ := norm_pos hv00 hd0
  have hl0 : ldv .lbu M D.N = BitVec.ofNat 64 (vs0.getD 0 0) := by
    have := hv 0 hL1; rw [Nat.add_zero] at this; exact lbu_digit hd0 this
  bc_run hlive hS [h2, h16, h24, hl0] at 0x80007908
  all_goals first | exact acc_heap hS (by omega) (by omega) | dc_frame cx.frame | skip
  refine divdi3_spec hlive _ (by bsimp []) fun R1 hk1 hr1 => ?_
  bsimp [] at hr1 ⊢
  rw [sdiv_small (by omega) (by omega) (by omega)] at hr1
  generalize hnm : 10 / (vs0.getD 0 0 + 1) = nm at hr1 hX hV hnp hn5
  have s16 : ldv .ld (writeLog (writeLog M [(sp - 208 + 24, 8, BitVec.ofNat 64 (D.L + 1))])
      [(sp - 208 + 16, 8, BitVec.ofNat 64 (vs0.getD 0 0))]) (sp - 208 + 16) =
      BitVec.ofNat 64 (vs0.getD 0 0) := by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]
  have s24 : ldv .ld (writeLog (writeLog M [(sp - 208 + 24, 8, BitVec.ofNat 64 (D.L + 1))])
      [(sp - 208 + 16, 8, BitVec.ofNat 64 (vs0.getD 0 0))]) (sp - 208 + 24) =
      BitVec.ofNat 64 (D.L + 1) := by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk1.get 2]; bsimp [h2]
  bc_run hlive hS [hr1, q2, sxw_ofNat] at 0x80005c40 0x80005c0c
  all_goals first | exact acc_heap hS (by omega) (by omega) | dc_frame cx.frame | skip
  all_goals simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]
  have hm2 : ∀ a, (a < sp - 208 + 16 ∨ sp - 208 + 104 ≤ a) →
      imgM (writeLog (writeLog M [(sp - 208 + 24, 8, BitVec.ofNat 64 (D.L + 1))])
        [(sp - 208 + 16, 8, BitVec.ofNat 64 (vs0.getD 0 0))]) a = imgM M a := fun a ha => by
    simp (disch := omega) only [imgM_store_miss]
  have bs2 := bs.slots (by simp only [heapEnd]; omega) (by omega) hm2
  have inH : ∀ b, b ∈ H.live → ∀ a, b.In a →
      imgM (writeLog (writeLog M [(sp - 208 + 24, 8, BitVec.ofNat 64 (D.L + 1))])
        [(sp - 208 + 16, 8, BitVec.ofNat 64 (vs0.getD 0 0))]) a = imgM M a := fun b hb a ha =>
    hm2 a (.inl (by have := (live_in_heap hi hb ha).2; simp only [heapEnd] at this; omega))
  have hv2 : ∀ i, i < D.L → imgM (writeLog (writeLog M [(sp - 208 + 24, 8, BitVec.ofNat 64 (D.L + 1))])
      [(sp - 208 + 16, 8, BitVec.ofNat 64 (vs0.getD 0 0))]) (D.N + i) =
      BitVec.ofNat 8 (vs0.getD i 0) := fun i hi' =>
    (inH _ bs.b2l _ (bs.nIn i (by omega))).trans (hv i hi')
  have hsent2 := (inH _ bs.b2l _ (bs.nIn _ (Nat.le_refl _))).trans hsent
  have hx2' : ∀ i, i < xs0.length → imgM (writeLog (writeLog M
      [(sp - 208 + 24, 8, BitVec.ofNat 64 (D.L + 1))])
      [(sp - 208 + 16, 8, BitVec.ofNat 64 (vs0.getD 0 0))]) (D.P + i) =
      BitVec.ofNat 8 (xs0.getD i 0) := fun i hi' =>
    (inH _ bs.b1l _ (bs.pIn i (by omega))).trans (hx i hi')
  have K1 : Keeps normClob (upd (upd (upd (upd R1 27 (BitVec.ofNat 64 nm)) 13 1#64) 17
        (BitVec.ofNat 64 (vs0.getD 0 0))) 16 (BitVec.ofNat 64 (D.L + 1))) R := by
    keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps normClob _ R))
  · intro he
    have hn1 : nm = 1 := ofNat64_eq (by omega) (by omega) he
    subst hn1
    rw [Nat.mul_one, digBE_self hx0d] at hX
    rw [Nat.mul_one, ← hv0l, digBE_self hv0d] at hV
    refine hnext _ _ bs2 (fun i hi' => ?_) (fun i hi' => ?_) hsent2 (by bsimp [hV]) (by bsimp []) K1
    · rw [hX] at hi' ⊢; exact hx2' i hi'
    · rw [hV]; exact hv2 i hi'
  · intro hne
    have hn1 : nm ≠ 1 := fun h => hne (by rw [h])
    have h18' : R1 18 = BitVec.ofNat 64 D.P := by rw [hk1.get 18]; bsimp [h18]
    have h25' : R1 25 = BitVec.ofNat 64 (xs0.length - 2) := by rw [hk1.get 25]; bsimp [h25]
    bc_run hlive hS [q2, h18', h25']
      at 0x80003ebc
    all_goals first | dc_frame cx.frame | skip
    have hp0 := live_pay_lo hi bs.b1l (bs.pIn 0 (by omega))
    have hpT := live_in_heap hi bs.b1l (bs.pIn (xs0.length - 1) (by omega))
    simp only [heapStart, heapEnd, Nat.add_zero] at hp0 hpT
    obtain ⟨hX0, hX'⟩ := dvx_split hx0d hx2 hx00 hx0z
    have hpw : 10 ^ (xs0.length - 1) = 10 * 10 ^ (xs0.length - 2) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hc0 : dvalBE (xs0.take (xs0.length - 1)) * nm / 10 ^ (xs0.length - 1) = 0 := by
      refine Nat.div_eq_of_lt ?_
      rw [hpw]
      have : dvalBE (xs0.take (xs0.length - 1)) * nm ≤ dvalBE (xs0.take (xs0.length - 1)) * 5 :=
        Nat.mul_le_mul_left _ hn5
      omega
    refine one_mult_spec hlive (cx.om hS (by bsimp [q2]) (by bsimp [])) (n := xs0.length - 1)
      (d := nm) (p := D.P) (r := D.P) (xs := xs0.take (xs0.length - 1))
      ⟨by rw [List.length_take]; omega, hx0d.take _, fun i hi' => ?_, by omega, by omega,
        by simp only [heapStart]; omega, by simp only [heapEnd]; omega,
        by simp only [heapStart]; omega, by simp only [heapEnd]; omega, .inl rfl,
        fun h => absurd h hn1⟩
      (by bsimp [h18']) (by bsimp [h25']; congr 1; omega) (by bsimp []) (by bsimp [h18'])
      fun R3 M3 hk3 hp => ?_
    · simp (disch := omega) only [imgM_store_miss]
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi', ← List.getD_eq_getElem?_getD]
      exact hx i (by omega)
    bsimp []
    have hm3 : ∀ a, (a < sp - 208 + 16 ∨ sp - 208 + 104 ≤ a) →
        imgM (writeLog (writeLog (writeLog M [(sp - 208 + 24, 8, BitVec.ofNat 64 (D.L + 1))])
          [(sp - 208 + 16, 8, BitVec.ofNat 64 (vs0.getD 0 0))])
          [(sp - 208 + 16, 8, BitVec.ofNat 64 (D.L + 1))]) a = imgM M a := fun a ha => by
      simp (disch := omega) only [imgM_store_miss]
    have bs3 := bs.slots (by simp only [heapEnd]; omega) (by omega) hm3
    have hfr : ∀ a, ¬ D.b1.In a → ¬ (sp - W ≤ a ∧ a < sp - 208) → imgM M3 a = imgM
        (writeLog (writeLog (writeLog M [(sp - 208 + 24, 8, BitVec.ofNat 64 (D.L + 1))])
          [(sp - 208 + 16, 8, BitVec.ofNat 64 (vs0.getD 0 0))])
          [(sp - 208 + 16, 8, BitVec.ofNat 64 (D.L + 1))]) a := by
      intro a h1 h3
      have hrest : ∀ a, (a + 1 < D.P ∨ D.P + (xs0.length - 1) ≤ a) → ¬ (sp - W ≤ a ∧ a < sp - 208) →
          imgM M3 a = imgM (writeLog (writeLog (writeLog M [(sp - 208 + 24, 8, BitVec.ofNat 64 (D.L + 1))])
          [(sp - 208 + 16, 8, BitVec.ofNat 64 (vs0.getD 0 0))])
          [(sp - 208 + 16, 8, BitVec.ofNat 64 (D.L + 1))]) a := fun a h h' => hp.rest a h (by simp only [frameIn]; omega)
      rcases Nat.lt_or_ge (a + 1) D.P with h | h
      · exact hrest a (.inl h) h3
      rcases Nat.lt_or_ge a (D.P + (xs0.length - 1)) with h' | h'
      · rcases Nat.lt_or_ge a D.P with h'' | h''
        · rw [show a = D.P - 1 by omega, hp.keep hc0]
        · exfalso; apply h1
          have := bs.pIn (a - D.P) (by omega)
          rwa [show D.P + (a - D.P) = a by omega] at this
      · exact hrest a (.inr h') h3
    have bs4 := bs3.raw (by simp only [heapEnd]; omega) (by omega) (M' := M3) fun a ha =>
      hfr a (fun h => ha (.inl h)) (fun h => ha (.inr (.inr (.inr h))))
    have K1' : Keeps normClob R1 R :=
      (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps normClob _ R)
    have hb12 := fun a => live_apart (a := a) hi bs.b1l bs.b2l bs.b12
    have hN : ∀ i, i ≤ D.L → D.N + i < heapEnd := fun i hi' =>
      (live_in_heap hi bs.b2l (bs.nIn i hi')).2
    simp only [heapEnd] at hN
    refine dvs_norm2 hlive cx bs4 hv0l hv0d hv00 hnm.symm hn1 hV hL1 hLs
      (fun i hi' => (hfr _ (fun h => hb12 _ h (bs.nIn i (by omega)))
        (by have := hN i (by omega); omega)).trans
        ((hm3 _ (.inl (by have := hN i (by omega); omega))).trans (hv i hi')))
      ((hfr _ (fun h => hb12 _ h (bs.nIn _ (Nat.le_refl _))) (by have := hN _ (Nat.le_refl _); omega)).trans
        ((hm3 _ (.inl (by have := hN _ (Nat.le_refl _); omega))).trans hsent))
      (by rw [ldv_congr .ld fun j hj => hp.rest _ (.inr (by simp only [widthOfM] at hj; omega))
            (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
          simp (disch := omega) only [ldv_ld_miss, ldv_store_hit])
      (by rw [hk3.get 2]; bsimp [q2]) (by rw [hk3.get 23]; bsimp [hk1.get 23, h23])
      (by rw [hk3.get 24]; bsimp [hk1.get 24, h24]) (by rw [hk3.get 27]; bsimp [])
      fun R4 M4 bs5 hfr4 hvs4 hsent4 h17 h16 K4 => hnext R4 M4 bs5 (fun i hi' => ?_) hvs4 hsent4 h17 h16
        (K4.trans (by keeps_tac ((hk3.mono (by decide)).trans (by keeps_tac K1'))))
    have hiT : i < xs0.length := by rw [hx0l]; exact hi'
    have hP := live_in_heap hi bs.b1l (bs.pIn i hi')
    simp only [heapEnd] at hP
    rw [hfr4 _ (fun h => hb12 _ (bs.pIn i hi') h) (by omega), hX]
    rcases Nat.lt_or_ge i (xs0.length - 1) with h | h
    · rw [hp.digits i h, dvx_norm_digit hx0d hx2 hx00 hx0z nm h]
    · rw [show i = xs0.length - 1 by omega, dvx_norm_last hx0d hx2 hx00 hx0z nm,
        hp.rest _ (.inr (Nat.le_refl _)) (by simp only [frameIn]; omega), hm3 _ (.inl (by omega)),
        hx _ (by omega), hx0z]

end

end Dc.Mach
