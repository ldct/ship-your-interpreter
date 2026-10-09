import Dc.Mach.Bc.DivSub
import Dc.BcModel.DivGuess

/-!
# `bc_divide`'s main loop (`0x80005d4c`)

```
80005d38 sb s4,0(s11) ; 80005d3c bltu s10,s5,80005e2c ; 80005d40 lbu a7,0(s8)
80005d44 addi s11,s11,1 ; 80005d48 mv s1,s5
80005d4c slli s9,s1,0x20 ; … ; 80005d84 bne a2,a7,80005cac ; 80005d88 li a2,9
80005cac … jal __divdi3 ; 80005cbc lbu s0,1(s8) ; … jal __muldi3 ×2
80005ce0 … ; 80005d08 bgeu a5,s3,80005d30 ; … ; 80005d28 bltu a3,a6,80005d90
80005d2c addiw s6,s6,-1 ; 80005d30 li s4,0 ; 80005d34 bnez s6,80005d9c
80005d9c … jal _one_mult ; 80005db8 … subtract loop (`DivSub`) …
80005e18 li a5,1 ; 80005e1c beq a0,a5,80005eec ; 80005e20 mv s4,s6
80005e24 sb s4,0(s11) ; 80005e28 bgeu s10,s5,80005d40
80005eec … add-back loop (`DivSub`) … 80005f4c … jal __moddi3 ; 80005f70 sb
```

Iteration `k` divides the window of `L + 1` digits at `P + k` (the
remainder so far, then the next dividend digit) by the divisor's `L`
digits at `N`, stores the digit at `Qb + k`, and leaves the remainder in
the window's `L` low positions.

- `DvData`: the addresses, the divisor `vs` and the normalised dividend `xs`.
- `DvFix`: what the loop keeps (saved registers, slots, heap, buffers).
- `DvWin`: the window and the quotient's digits at iteration `k`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- The registers `bc_divide` changes before its epilogue. -/
abbrev divAll : List Nat :=
  [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
    28, 29, 30, 31]

/-- The prologue's saved registers (offsets from the lowered `sp`). -/
abbrev divSlots : List (Nat × Nat) :=
  [(27, 104), (26, 112), (25, 120), (24, 128), (23, 136), (20, 160), (18, 176), (1, 200),
    (22, 144), (21, 152), (8, 192), (19, 168), (9, 184)]

/-- The loop's data: the dividend buffer `P` (block `b1`) holding the
normalised digits `xs`, the divisor's `L` digits `vs` at `N` (block `b2`),
the product buffer `Bm` (block `b3`), the quotient's first digit at
`Qb = y.val + off`, the last iteration `Kb`, and the words the exit reloads. -/
structure DvData where
  P : Nat
  N : Nat
  Bm : Nat
  off : Nat
  L : Nat
  Kb : Nat
  xs : List Nat
  vs : List Nat
  b1 : Blk
  b2 : Blk
  b3 : Blk
  qv : Nat
  n1p : Nat
  n2p : Nat
  rs : Nat

/-- The divisor's value. -/
abbrev DvData.V (D : DvData) : Nat := dvalBE D.vs

/-- The dividend's prefix entering iteration `k`. -/
abbrev DvData.pre (D : DvData) (k : Nat) : Nat := dvalBE (D.xs.take (D.L + k))

/-- The loop's arithmetic shape. -/
structure DvShape (D : DvData) : Prop where
  vl : D.vs.length = D.L
  vd : IsDigits D.vs
  l1 : 1 ≤ D.L
  v1 : 5 ≤ D.vs.getD 0 0
  xl : D.Kb + D.L + 2 ≤ D.xs.length
  xd : IsDigits D.xs
  first : D.pre 0 < D.V
  small : D.xs.length < 2 ^ 30

/-- **Scratch stores keep the number heap**: stores confined to two raw
buffers and the stack above the heap. -/
theorem BcHeap.scratch {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk}
    {Lo : List NumObj} (h : BcHeap S M H F Lo) {b1 b3 : Blk} (hb1 : b1 ∈ H.live)
    (hn1 : b1 ∉ F ++ objBlocks Lo) (hb3 : b3 ∈ H.live) (hn3 : b3 ∉ F ++ objBlocks Lo)
    (hm : ∀ a, ¬ (b1.In a ∨ b3.In a ∨ heapEnd ≤ a) → imgM M' a = imgM M a) :
    BcHeap S M' H F Lo :=
  h.transportOwn
    (fun a ha => hm a fun hc => by
      rcases hc with hi | hi | hi
      · exact live_not_alloc h.heap hb1 hi ha
      · exact live_not_alloc h.heap hb3 hi ha
      · have := (AllocByte.bound h.heap ha).2; omega)
    (fun c hc a ha => hm a fun hc' => by
      rcases hc' with hi | hi | hi
      · exact live_apart h.heap hb1 (h.owned_live hc) (fun e => hn1 (e ▸ hc)) hi ha
      · exact live_apart h.heap hb3 (h.owned_live hc) (fun e => hn3 (e ▸ hc)) hi ha
      · have := live_in_heap h.heap (h.owned_live hc) ha; omega)
    (fun j hj => hm _ fun hc => by
      rcases hc with hi | hi | hi
      · have := live_in_heap h.heap hb1 hi
        simp only [bcFreeAddr, heapStart, heapEnd] at this; omega
      · have := live_in_heap h.heap hb3 hi
        simp only [bcFreeAddr, heapStart, heapEnd] at this; omega
      · simp only [bcFreeAddr, heapEnd] at hi; omega)

/-- What the loop keeps: the saved registers and slots of the frame, the
number heap with the quotient `y` (digits `ds`) at its head, the three raw
buffers, the divisor, and every byte off the heap and the window. -/
structure DvFix (S : Nat → Prop) (Mt0 M : Mem) (R0 : Nat → BitVec 64) (sp W : Nat) (D : DvData)
    (H : Heap) (F : List Blk) (Lh : List NumObj) (y : NumObj) (ds : List Nat) : Prop where
  saved : SavedWords M (sp - 208) divSlots R0
  s8 : ldv .ld M (sp - 208 + 8) = BitVec.ofNat 64 D.Bm
  s16 : ldv .ld M (sp - 208 + 16) = BitVec.ofNat 64 D.L
  s24 : ldv .ld M (sp - 208 + 24) = BitVec.ofNat 64 D.L
  s32 : ldv .ld M (sp - 208 + 32) = BitVec.ofNat 64 (D.Bm + 1)
  s40 : ldv .ld M (sp - 208 + 40) = BitVec.ofNat 64 (D.L + 1)
  s48 : ldv .ld M (sp - 208 + 48) = BitVec.ofNat 64 (D.L + 1)
  s56 : ldv .ld M (sp - 208 + 56) = BitVec.ofNat 64 D.qv
  s64 : ldv .ld M (sp - 208 + 64) = BitVec.ofNat 64 D.b2.pay
  s72 : ldv .ld M (sp - 208 + 72) = BitVec.ofNat 64 D.n2p
  s80 : ldv .ld M (sp - 208 + 80) = BitVec.ofNat 64 D.n1p
  s88 : ldv .ld M (sp - 208 + 88) = BitVec.ofNat 64 D.rs
  heap : BcHeap S M H F (withDs y ds :: Lh)
  noView : ∀ z ∈ Lh, z.db ≠ y.db
  owns : y.Owns
  qlen : ds.length = y.rep.len + y.rep.scale
  qdig : IsDigits ds
  qend : D.off + D.Kb + 1 = y.rep.len + y.rep.scale
  qzero : ∀ j, j < D.off → ds.getD j 0 = 0
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
  div : ∀ i, i < D.L → imgM M (D.N + i) = BitVec.ofNat 8 (D.vs.getD i 0)
  sent : imgM M (D.N + D.L) = 0#8
  out : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a

/-- The window and the quotient's digits entering iteration `k`. -/
structure DvWin (M : Mem) (D : DvData) (ds : List Nat) (k : Nat) : Prop where
  win : ∀ i, i < D.L → imgM M (D.P + k + i) = BitVec.ofNat 8 (D.pre k % D.V / 10 ^ (D.L - 1 - i) % 10)
  rest : ∀ i, k + D.L ≤ i → i < D.xs.length → imgM M (D.P + i) = BitVec.ofNat 8 (D.xs.getD i 0)
  quot : ∀ j, j < k → ds.getD (D.off + j) 0 = D.pre k / D.V / 10 ^ (k - 1 - j) % 10

/-- The loop head `0x80005d4c` at iteration `k`. -/
structure DvAt (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat) (D : DvData)
    (H : Heap) (F : List Blk) (Lh : List NumObj) (y : NumObj) (ds : List Nat) (k : Nat) : Prop where
  fix : DvFix S Mt0 M R0 sp W D H F Lh y ds
  win : DvWin M D ds k
  r2 : R 2 = BitVec.ofNat 64 (sp - 208)
  r9 : R 9 = BitVec.ofNat 64 k
  r18 : R 18 = BitVec.ofNat 64 D.P
  r24 : R 24 = BitVec.ofNat 64 D.N
  r17 : R 17 = BitVec.ofNat 64 (D.vs.getD 0 0)
  r27 : R 27 = BitVec.ofNat 64 (y.rep.val + D.off + k)
  r26 : R 26 = BitVec.ofNat 64 D.Kb
  regs : Keeps divAll R R0
  kb : k ≤ D.Kb

/-- The bytes the loop's scratch work may change: the dividend and product
buffers and the stack below the frame. -/
abbrev DvScratch (sp W : Nat) (D : DvData) (a : Nat) : Prop :=
  D.b1.In a ∨ D.b3.In a ∨ (sp - W ≤ a ∧ a < sp - 208)

/-- `DvFix` through scratch stores. -/
theorem DvFix.scratch {S : Nat → Prop} {Mt0 M M' : Mem} {R0 : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj} {ds : List Nat}
    (hf : DvFix S Mt0 M R0 sp W D H F Lh y ds) (hab : heapEnd + W ≤ sp) (hW : 208 ≤ W)
    (hm : MemOnly (DvScratch sp W D) M' M) : DvFix S Mt0 M' R0 sp W D H F Lh y ds := by
  have hi := hf.heap.heap
  have inH : ∀ b, b ∈ H.live → ∀ a, b.In a → a < heapEnd := fun b hb a ha =>
    (live_in_heap hi hb ha).2
  have hfr : ∀ a, sp - 208 ≤ a → imgM M' a = imgM M a := fun a ha => hm a fun h => by
    rcases h with h | h | h
    · have := inH _ hf.b1l a h; omega
    · have := inH _ hf.b3l a h; omega
    · omega
  have hld : ∀ o, ldv .ld M' (sp - 208 + o) = ldv .ld M (sp - 208 + o) := fun o =>
    ldv_congr .ld fun j _ => hfr _ (by omega)
  have h2 : ∀ a, D.b2.In a → imgM M' a = imgM M a := fun a ha => hm a fun h => by
    rcases h with h | h | h
    · exact live_apart hi hf.b1l hf.b2l hf.b12 h ha
    · exact live_apart hi hf.b3l hf.b2l (Ne.symm hf.b23) h ha
    · have := inH _ hf.b2l a ha; omega
  refine { hf with
    saved := hf.saved.transport (lo := 0) (top := 208) (hag := fun a h1 _ => hfr a (by omega))
    s8 := by rw [hld]; exact hf.s8
    s16 := by rw [hld]; exact hf.s16
    s24 := by rw [hld]; exact hf.s24
    s32 := by rw [hld]; exact hf.s32
    s40 := by rw [hld]; exact hf.s40
    s48 := by rw [hld]; exact hf.s48
    s56 := by rw [hld]; exact hf.s56
    s64 := by rw [hld]; exact hf.s64
    s72 := by rw [hld]; exact hf.s72
    s80 := by rw [hld]; exact hf.s80
    s88 := by rw [hld]; exact hf.s88
    heap := hf.heap.scratch hf.b1l hf.b1n hf.b3l hf.b3n fun a ha =>
      hm a fun h => ha (by
        rcases h with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (by omega)))
    div := fun i hi' => (h2 _ (hf.nIn i (by omega))).trans (hf.div i hi')
    sent := (h2 _ (hf.nIn _ (Nat.le_refl _))).trans hf.sent
    out := fun a ho hn => (hm a fun h => by
        rcases h with h | h | h
        · exact ho.1 (live_in_heap hi hf.b1l h)
        · exact ho.1 (live_in_heap hi hf.b3l h)
        · exact hn ⟨by omega, by omega⟩).trans (hf.out a ho hn) }

/-- `DvFix` through a store of the quotient digit `d` at position `i ≥ off`. -/
theorem DvFix.setDigit {S : Nat → Prop} {Mt0 M : Mem} {R0 : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj} {ds : List Nat}
    (hf : DvFix S Mt0 M R0 sp W D H F Lh y ds) (hab : heapEnd + W ≤ sp) (hW : 208 ≤ W)
    {i d : Nat} (hi1 : D.off ≤ i) (hi : i < y.rep.len + y.rep.scale) (hd : d < 10)
    {v : BitVec 64} (hv : sbData v = BitVec.ofNat 8 d) :
    DvFix S Mt0 (writeLog M [(y.rep.val + i, 1, v)]) R0 sp W D H F Lh y (ds.set i d) := by
  have hi' := hf.heap.heap
  have hy : withDs y ds ∈ withDs y ds :: Lh := List.mem_cons_self
  have hb := hf.heap.blocks _ hy
  have hdl := hb.dLo; have hdf := hb.dFit
  have hin : y.db.In (y.rep.val + i) := ⟨by simp only [withDs] at hdl; omega,
    by simp only [withDs] at hdf; omega⟩
  have hyl : y.db ∈ H.live := hb.dLive
  have hyo : y.db ∈ F ++ objBlocks (y :: Lh) :=
    List.mem_append_right _ (mem_objBlocks_db List.mem_cons_self hf.owns)
  have hH := live_in_heap hi' hyl hin
  have hm : ∀ a, a ≠ y.rep.val + i → imgM (writeLog M [(y.rep.val + i, 1, v)]) a = imgM M a :=
    fun a ha => imgM_store_miss _ _ (by omega)
  have hfr : ∀ a, sp - 208 ≤ a → imgM (writeLog M [(y.rep.val + i, 1, v)]) a = imgM M a :=
    fun a ha => hm a (by simp only [heapEnd] at hH hab; omega)
  have hld : ∀ o, ldv .ld (writeLog M [(y.rep.val + i, 1, v)]) (sp - 208 + o) =
      ldv .ld M (sp - 208 + o) := fun o => ldv_congr .ld fun j _ => hfr _ (by omega)
  have h2 : ∀ a, D.b2.In a → imgM (writeLog M [(y.rep.val + i, 1, v)]) a = imgM M a :=
    fun a ha => hm a fun e => live_apart hi' hf.b2l hyl (fun e' => hf.b2n (e' ▸ hyo)) ha (e ▸ hin)
  have hset := BcHeap.setDigit (L1 := []) hf.heap (fun z hz => hf.noView z hz)
    (i := i) (d := d) (by simpa only [withDs] using hi) hd hv
  refine { hf with
    saved := hf.saved.transport (lo := 0) (top := 208) (hag := fun a h1 _ => hfr a (by omega))
    s8 := by rw [hld]; exact hf.s8
    s16 := by rw [hld]; exact hf.s16
    s24 := by rw [hld]; exact hf.s24
    s32 := by rw [hld]; exact hf.s32
    s40 := by rw [hld]; exact hf.s40
    s48 := by rw [hld]; exact hf.s48
    s56 := by rw [hld]; exact hf.s56
    s64 := by rw [hld]; exact hf.s64
    s72 := by rw [hld]; exact hf.s72
    s80 := by rw [hld]; exact hf.s80
    s88 := by rw [hld]; exact hf.s88
    heap := hset
    qlen := by rw [List.length_set, hf.qlen]
    qdig := fun e he => by
      rcases List.mem_or_eq_of_mem_set he with he | he
      · exact hf.qdig e he
      · omega
    qzero := fun j hj => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      exact hf.qzero j hj
    div := fun i' hi'' => (h2 _ (hf.nIn i' (by omega))).trans (hf.div i' hi'')
    sent := (h2 _ (hf.nIn _ (Nat.le_refl _))).trans hf.sent
    out := fun a ho hn => (hm a fun e => ho.1 (e ▸ hH)).trans (hf.out a ho hn) }

/-- After the last iteration, at `0x80005e2c`. -/
structure DvExit (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat) (D : DvData)
    (H : Heap) (F : List Blk) (Lh : List NumObj) (y : NumObj) (ds : List Nat) : Prop where
  fix : DvFix S Mt0 M R0 sp W D H F Lh y ds
  win : DvWin M D ds (D.Kb + 1)
  r2 : R 2 = BitVec.ofNat 64 (sp - 208)
  r18 : R 18 = BitVec.ofNat 64 D.P
  regs : Keeps divAll R R0

/-- An iteration's digit computed, the window holding the new remainder:
at `0x80005d38` (digit in `s4`) or `0x80005e20` (digit in `s6`). -/
structure DvMid (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat) (D : DvData)
    (H : Heap) (F : List Blk) (Lh : List NumObj) (y : NumObj) (ds : List Nat) (k : Nat) : Prop where
  fix : DvFix S Mt0 M R0 sp W D H F Lh y ds
  win : ∀ i, i < D.L → imgM M (D.P + (k + 1) + i) =
    BitVec.ofNat 8 (D.pre (k + 1) % D.V / 10 ^ (D.L - 1 - i) % 10)
  rest : ∀ i, k + 1 + D.L ≤ i → i < D.xs.length → imgM M (D.P + i) = BitVec.ofNat 8 (D.xs.getD i 0)
  quot : ∀ j, j < k → ds.getD (D.off + j) 0 = D.pre (k + 1) / D.V / 10 ^ (k - j) % 10
  r2 : R 2 = BitVec.ofNat 64 (sp - 208)
  r9 : R 9 = BitVec.ofNat 64 k
  r21 : R 21 = BitVec.ofNat 64 (k + 1)
  r18 : R 18 = BitVec.ofNat 64 D.P
  r24 : R 24 = BitVec.ofNat 64 D.N
  r27 : R 27 = BitVec.ofNat 64 (y.rep.val + D.off + k)
  r26 : R 26 = BitVec.ofNat 64 D.Kb
  regs : Keeps divAll R R0
  kb : k ≤ D.Kb

/-- The digit `q` stored: the window and quotient entering iteration `k + 1`. -/
theorem DvMid.store {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj} {ds : List Nat} {k : Nat}
    (hs : DvShape D) (st : DvMid S Mt0 M R0 R sp W D H F Lh y ds k) (hab : heapEnd + W ≤ sp)
    (hW : 208 ≤ W) {v : BitVec 64} (hv : sbData v = BitVec.ofNat 8 (D.pre (k + 1) / D.V % 10)) :
    DvFix S Mt0 (writeLog M [(y.rep.val + D.off + k, 1, v)]) R0 sp W D H F Lh y
        (ds.set (D.off + k) (D.pre (k + 1) / D.V % 10)) ∧
      DvWin (writeLog M [(y.rep.val + D.off + k, 1, v)]) D
        (ds.set (D.off + k) (D.pre (k + 1) / D.V % 10)) (k + 1) := by
  have hf := st.fix
  have hk := st.kb
  have he := hf.qend
  have hfx := hf.setDigit hab hW (i := D.off + k) (by omega) (by omega) (Nat.mod_lt _ (by decide)) hv
  rw [← Nat.add_assoc] at hfx
  refine ⟨hfx, ?_⟩
  have hi' := hf.heap.heap
  have hy : withDs y ds ∈ withDs y ds :: Lh := List.mem_cons_self
  have hb := hf.heap.blocks _ hy
  have hdl := hb.dLo; have hdf := hb.dFit
  have hin : y.db.In (y.rep.val + D.off + k) := ⟨by simp only [withDs] at hdl; omega,
    by simp only [withDs] at hdf; omega⟩
  have hyl : y.db ∈ H.live := hb.dLive
  have hyo : y.db ∈ F ++ objBlocks (y :: Lh) :=
    List.mem_append_right _ (mem_objBlocks_db List.mem_cons_self hf.owns)
  have h1 : ∀ a, D.b1.In a → imgM (writeLog M [(y.rep.val + D.off + k, 1, v)]) a = imgM M a :=
    fun a ha => by
      have hne : a ≠ y.rep.val + D.off + k := fun e =>
        live_apart hi' hf.b1l hyl (fun e' => hf.b1n (e' ▸ hyo)) ha (e ▸ hin)
      exact imgM_store_miss _ _ (by omega)
  have hxl := hf.pIn
  have hxl := hs.xl
  refine ⟨fun i hi => ?_, fun i hi1 hi2 => ?_, fun j hj => ?_⟩
  · rw [h1 _ (by rw [Nat.add_assoc]; exact hf.pIn _ (by omega))]; exact st.win i hi
  · rw [h1 _ (hf.pIn _ hi2)]; exact st.rest i (by omega) hi2
  · rw [List.getD_eq_getElem?_getD]
    by_cases e : j = k
    · subst e
      rw [List.getElem?_set_self (by rw [hf.qlen]; omega), Option.getD_some,
        show j + 1 - 1 - j = 0 by omega, Nat.pow_zero, Nat.div_one]
    · rw [List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD, st.quot j (by omega),
        show k + 1 - 1 - j = k - j by omega]

/-- The context the loop's stages share. -/
structure DvCtx (S : Nat → Prop) (sp W : Nat) : Prop where
  frame : StackFrame S sp W
  above : heapEnd + W ≤ sp
  big : 272 ≤ W

theorem DvFix.heapOwn {S : Nat → Prop} {Mt0 M : Mem} {R0 : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj} {ds : List Nat}
    (hf : DvFix S Mt0 M R0 sp W D H F Lh y ds) : HeapOwn S :=
  fun a h1 h2 => hf.heap.heap.own a h1 h2

/-- On to the next iteration from `0x80005d40`. -/
theorem dv_next {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {y : NumObj} {ds : List Nat} {k : Nat}
    (hs : DvShape D) (hf : DvFix S Mt0 M R0 sp W D H F Lh y ds) (hw : DvWin M D ds (k + 1))
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h21 : R 21 = BitVec.ofNat 64 (k + 1))
    (h18 : R 18 = BitVec.ofNat 64 D.P) (h24 : R 24 = BitVec.ofNat 64 D.N)
    (h27 : R 27 = BitVec.ofNat 64 (y.rep.val + D.off + k)) (h26 : R 26 = BitVec.ofNat 64 D.Kb)
    (hk : Keeps divAll R R0) (hk1 : k + 1 ≤ D.Kb)
    (hnext : ∀ R' M' ds', DvAt S Mt0 M' R0 R' sp W D H F Lh y ds' (k + 1) →
      DW live S Q 0x80005d4c#64 R' M') :
    DW live S Q 0x80005d40#64 R M := by
  have hS := hf.heapOwn
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hn := hf.nIn 0 (Nat.zero_le _)
  have hH := live_in_heap hf.heap.heap hf.b2l hn
  simp only [heapStart, heapEnd] at hH
  have l1 : ldv .lbu M D.N = BitVec.ofNat 64 (D.vs.getD 0 0) :=
    lbu_digit (hs.vd.getD 0) (by have := hf.div 0 hs.l1; rwa [Nat.add_zero] at this)
  bc_run hlive hS [h24, l1, h27, h21] at 0x80005d4c
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  exact hnext _ _ _ ⟨hf, hw, by bsimp [h2], by bsimp [h21], by bsimp [h18], by bsimp [h24],
    by bsimp [], by bsimp [h27]; congr 1, by bsimp [h26], by keeps_tac hk, hk1⟩

/-- The continuations of an iteration: the next one, or the loop's exit. -/
structure DvK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (Mt0 : Mem) (R0 : Nat → BitVec 64) (sp W : Nat) (D : DvData) (H : Heap) (F : List Blk)
    (Lh : List NumObj) (y : NumObj) (k : Nat) : Prop where
  next : k + 1 ≤ D.Kb → ∀ R' M' ds', DvAt S Mt0 M' R0 R' sp W D H F Lh y ds' (k + 1) →
    DW live S Q 0x80005d4c#64 R' M'
  exit : k = D.Kb → ∀ R' M' ds', DvExit S Mt0 M' R0 R' sp W D H F Lh y ds' →
    DW live S Q 0x80005e2c#64 R' M'

/-- The digit store at `0x80005d38` (digit in `s4`). -/
theorem dv_store {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {y : NumObj} {ds : List Nat} {k : Nat}
    (cx : DvCtx S sp W) (hs : DvShape D) (st : DvMid S Mt0 M R0 R sp W D H F Lh y ds k)
    (h20 : R 20 = BitVec.ofNat 64 (D.pre (k + 1) / D.V % 10))
    (hk : DvK live S Q Mt0 R0 sp W D H F Lh y k) :
    DW live S Q 0x80005d38#64 R M := by
  have hf := st.fix
  have hS := hf.heapOwn
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hkb := st.kb; have hab := cx.above; have hW := cx.big
  have hy : withDs y ds ∈ withDs y ds :: Lh := List.mem_cons_self
  have hb := hf.heap.blocks _ hy
  have he := hf.qend
  have hdl := hb.dLo; have hdf := hb.dFit
  have hin : y.db.In (y.rep.val + D.off + k) := ⟨by simp only [withDs] at hdl; omega,
    by simp only [withDs] at hdf; omega⟩
  have hH := live_in_heap hf.heap.heap hb.dLive hin
  simp only [heapStart, heapEnd] at hH
  obtain ⟨hf', hw'⟩ := st.store hs cx.above (by omega)
    (v := BitVec.ofNat 64 (D.pre (k + 1) / D.V % 10)) (by rw [sbData_ofNat])
  have hxl := hs.xl; have hsm := hs.small
  have h21 := st.r21; have h26 := st.r26; have h27 := st.r27
  bc_run hlive hS [h20, h27, h21, h26] at 0x80005d40 0x80005e2c
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro hlt
    have hk1 : k = D.Kb := by omega
    subst hk1
    exact hk.exit rfl _ _ _ ⟨hf', hw', st.r2, st.r18, by keeps_tac st.regs⟩
  · intro hge
    have hk1 : k + 1 ≤ D.Kb := by omega
    exact dv_next hlive hs hf' hw' st.r2 (by bsimp [h21])
      st.r18 st.r24 (by bsimp [h27]) (by bsimp [h26]) (by keeps_tac st.regs) hk1 (hk.next hk1)

/-- The digit store at `0x80005e20` (digit in `s6`). -/
theorem dv_store' {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {y : NumObj} {ds : List Nat} {k : Nat}
    (cx : DvCtx S sp W) (hs : DvShape D) (st : DvMid S Mt0 M R0 R sp W D H F Lh y ds k)
    (h22 : R 22 = BitVec.ofNat 64 (D.pre (k + 1) / D.V % 10))
    (hk : DvK live S Q Mt0 R0 sp W D H F Lh y k) :
    DW live S Q 0x80005e20#64 R M := by
  have hf := st.fix
  have hS := hf.heapOwn
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hkb := st.kb; have hab := cx.above; have hW := cx.big
  have hy : withDs y ds ∈ withDs y ds :: Lh := List.mem_cons_self
  have hb := hf.heap.blocks _ hy
  have he := hf.qend
  have hdl := hb.dLo; have hdf := hb.dFit
  have hin : y.db.In (y.rep.val + D.off + k) := ⟨by simp only [withDs] at hdl; omega,
    by simp only [withDs] at hdf; omega⟩
  have hH := live_in_heap hf.heap.heap hb.dLive hin
  simp only [heapStart, heapEnd] at hH
  obtain ⟨hf', hw'⟩ := st.store hs cx.above (by omega)
    (v := BitVec.ofNat 64 (D.pre (k + 1) / D.V % 10)) (by rw [sbData_ofNat])
  have hxl := hs.xl; have hsm := hs.small
  have h21 := st.r21; have h26 := st.r26; have h27 := st.r27
  bc_run hlive hS [h22, h27, h21, h26] at 0x80005d40 0x80005e2c
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro hge
    have hk1 : k + 1 ≤ D.Kb := by omega
    exact dv_next hlive hs hf' hw' st.r2 (by bsimp [h21])
      st.r18 st.r24 (by bsimp [h27]) (by bsimp [h26]) (by keeps_tac st.regs) hk1 (hk.next hk1)
  · intro hlt
    have hk1 : k = D.Kb := by omega
    subst hk1
    exact hk.exit rfl _ _ _ ⟨hf', hw', st.r2, st.r18, by keeps_tac st.regs⟩

/-! ## The guess -/

/-- `slliw` of a small word. -/
theorem slliw_ofNat {a k : Nat} (h : a * 2 ^ k < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) <<< k) =
      BitVec.ofNat 64 (a * 2 ^ k) := by
  have ha : a < 2 ^ 31 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))) h
  have e : BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) <<< k = BitVec.ofNat 32 (a * 2 ^ k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.extractLsb_toNat, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_zero]
    rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a < 2 ^ (31 - 0 + 1) by
      simp only [Nat.sub_zero, Nat.reduceAdd]; omega)]
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp [msb32_small h]
  omega

/-- `addw` of a small integer word and a small natural, with a natural sum. -/
theorem addw_int_nat {u : Int} {b : Nat} (hu1 : -2 ^ 30 ≤ u) (hu2 : u < 2 ^ 30) (hb : b < 2 ^ 30)
    (h0 : 0 ≤ u + b) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofInt 64 u) +
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 b)) = BitVec.ofNat 64 (u + b).toNat := by
  rw [← ofInt_natCast64 b, ← ofInt_natCast64, Int.toNat_of_nonneg h0]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), toInt_ofInt64 (by omega) (by omega)]
  have e : BitVec.extractLsb 31 0 (BitVec.ofInt 64 u) + BitVec.extractLsb 31 0 (BitVec.ofInt 64 (b : Int)) =
      BitVec.ofInt 32 (u + b) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.extractLsb_toNat, BitVec.toNat_ofInt]
    omega
  rw [e, BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- `subw` then `addw` of small naturals with a natural result. -/
theorem subw_addw {a b c : Nat} (ha : a < 2 ^ 29) (hb : b < 2 ^ 29) (hc : c < 2 ^ 29)
    (h : b ≤ a + c) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) - BitVec.extractLsb 31 0 (BitVec.ofNat 64 b))) +
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 c)) = BitVec.ofNat 64 (a + c - b) := by
  rw [subw_nat (by omega) (by omega), addw_int_nat (by omega) (by omega) (by omega) (by omega)]
  congr 1; omega

theorem se12_ffe : sign_extend (m := 64) (0xffe#12) = 18446744073709551614#64 := by decide

/-- `addi r, r, -2` on a word of at least 2. -/
theorem word_sub2 {k : Nat} (h : 2 ≤ k) :
    BitVec.ofNat 64 k + 18446744073709551614#64 = BitVec.ofNat 64 (k - 2) := by
  change BitVec.ofNat 64 k + -(2#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le k 2 (by decide) h

theorem guess0_mul_le (w0 w1 v1 : Nat) : v1 * guess0 w0 w1 v1 ≤ 10 * w0 + w1 := by
  unfold guess0
  split
  · subst w0; omega
  · exact Nat.mul_div_le _ _

/-- The guess's continuations: a zero digit (`0x80005d38`, `s4 = 0`) or a
nonzero one (`0x80005d9c`), in `s6`. -/
structure GuessK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (M : Mem) (R : Nat → BitVec 64) (g : Nat) : Prop where
  zero : g = 0 → ∀ R', Keeps [1, 8, 10, 11, 12, 13, 15, 16, 19, 20, 22] R' R →
    R' 22 = BitVec.ofNat 64 g → R' 20 = 0#64 → DW live S Q 0x80005d38#64 R' M
  pos : g ≠ 0 → ∀ R', Keeps [1, 8, 10, 11, 12, 13, 15, 16, 19, 20, 22] R' R →
    R' 22 = BitVec.ofNat 64 g → DW live S Q 0x80005d9c#64 R' M

/-- The guess's tests from `0x80005cbc` (first guess `g0` in `a2`). -/
theorem dv_guess_test {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64} {P N k w0 w1 w2 v1 v2 : Nat}
    (hw0 : w0 ≤ 9) (hw1 : w1 < 10) (hw2 : w2 < 10) (hv1 : v1 < 10) (hv2 : v2 < 10)
    (hP : 2147603920 ≤ P + k + 2) (hP2 : P + k + 2 < 2273312768)
    (hN : 2147603920 ≤ N + 1) (hN2 : N + 1 < 2273312768) (hk : k + 2 < 2 ^ 31)
    (lw2 : ldv .lbu M (P + k + 2) = BitVec.ofNat 64 w2)
    (lv2 : ldv .lbu M (N + 1) = BitVec.ofNat 64 v2)
    (h12 : R 12 = BitVec.ofNat 64 (guess0 w0 w1 v1)) (h20 : R 20 = BitVec.ofNat 64 v1)
    (h23 : R 23 = BitVec.ofNat 64 (10 * w0 + w1)) (h24 : R 24 = BitVec.ofNat 64 N)
    (h9 : R 9 = BitVec.ofNat 64 k) (h18 : R 18 = BitVec.ofNat 64 P)
    (hc : GuessK live S Q M R (guess w0 w1 w2 v1 v2)) :
    DW live S Q 0x80005cbc#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hg0 := guess0_mul_le w0 w1 v1
  bc_run hlive hS [h12, h20, h23, h24, lv2] at 0x80005ccc
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  apply st_80005ccc hlive
  refine muldi3_spec hlive _ (by bsimp []) fun R1 hk1 hr1 => ?_
  bsimp [] at hr1 ⊢
  rw [mul_ofNat] at hr1
  have hg9 : guess0 w0 w1 v1 ≤ 99 := by
    unfold guess0; split
    · omega
    · exact Nat.le_trans (Nat.div_le_self _ _) (by omega)
  have hvg : v2 * guess0 w0 w1 v1 ≤ 9 * 99 := Nat.mul_le_mul (by omega) hg9
  have hvg1 : v1 * guess0 w0 w1 v1 ≤ 9 * 99 := Nat.mul_le_mul (by omega) hg9
  have q20 : R1 20 = BitVec.ofNat 64 v1 := by rw [hk1.get 20]; bsimp [h20]
  have q22 : R1 22 = BitVec.ofNat 64 (guess0 w0 w1 v1) := by rw [hk1.get 22]; bsimp [h12]
  have q9 : R1 9 = BitVec.ofNat 64 k := by rw [hk1.get 9]; bsimp [h9]
  have q18 : R1 18 = BitVec.ofNat 64 P := by rw [hk1.get 18]; bsimp [h18]
  have q23 : R1 23 = BitVec.ofNat 64 (10 * w0 + w1) := by rw [hk1.get 23]; bsimp [h23]
  bc_run hlive hS [hr1, q20, q22, sxw_ofNat] at 0x80005cdc
  apply st_80005cdc hlive
  refine muldi3_spec hlive _ (by bsimp []) fun R2 hk2 hr2 => ?_
  bsimp [] at hr2 ⊢
  rw [mul_ofNat] at hr2
  have r9 : R2 9 = BitVec.ofNat 64 k := by rw [hk2.get 9]; bsimp [q9]
  have r18 : R2 18 = BitVec.ofNat 64 P := by rw [hk2.get 18]; bsimp [q18]
  have r23 : R2 23 = BitVec.ofNat 64 (10 * w0 + w1) := by rw [hk2.get 23]; bsimp [q23]
  have r19 : R2 19 = BitVec.ofNat 64 (v2 * guess0 w0 w1 v1) := by
    rw [hk2.get 19]; bsimp [hr1]
  have lw2' : ldv .lbu M (P + (k + 2)) = BitVec.ofNat 64 w2 := by rw [← Nat.add_assoc]; exact lw2
  bc_run hlive hS [hr2, r9, r18, r23, r19, lw2', sxw_ofNat, addw_ofNat, shl_shr32,
    subw_ofNat hg0, slliw_ofNat] at 0x80005d0c 0x80005d30
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro hnot
    have hg : guess w0 w1 w2 v1 v2 = guess0 w0 w1 v1 := by
      unfold guess
      simp only [guessHigh, decide_eq_true_eq]
      rw [if_neg (by omega)]
    have r22 : R2 22 = BitVec.ofNat 64 (guess0 w0 w1 v1) := by rw [hk2.get 22]; bsimp [q22]
    bc_run hlive hS [r22] at 0x80005d9c 0x80005d38
    · intro hne
      exact hc.pos (by rw [hg]; intro h0; exact hne (by rw [h0])) _ (by
        keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
          (by keeps_tac Keeps.refl _ _))))) (by bsimp [r22, hg])
    · intro he
      have h0 : guess0 w0 w1 v1 = 0 := ofNat64_eq (by omega) (by omega) (by rw [Classical.not_not.mp he])
      exact hc.zero (by rw [hg, h0]) _ (by
        keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
          (by keeps_tac Keeps.refl _ _))))) (by bsimp [r22, hg]) (by bsimp [])
  · intro hhigh
    have hg1 : 1 ≤ guess0 w0 w1 v1 := by
      refine Nat.pos_of_ne_zero fun h0 => hhigh ?_
      rw [h0, Nat.mul_zero]; exact Nat.zero_le _
    have hv2g : v2 ≤ v2 * guess0 w0 w1 v1 := Nat.le_mul_of_pos_right _ hg1
    have r20 : R2 20 = BitVec.ofNat 64 v1 := by rw [hk2.get 20]; bsimp [q20]
    have q8 : R1 8 = BitVec.ofNat 64 v2 := by rw [hk1.get 8]; bsimp []
    have r8 : R2 8 = BitVec.ofNat 64 v2 := by rw [hk2.get 8]; bsimp [q8]
    have hle : v1 * guess0 w0 w1 v1 ≤ v1 + (10 * w0 + w1) := by omega
    have e1 : v1 * (guess0 w0 w1 v1 - 1) = v1 * guess0 w0 w1 v1 - v1 := Nat.mul_sub_one _ _
    have e2 : v2 * (guess0 w0 w1 v1 - 1) = v2 * guess0 w0 w1 v1 - v2 := Nat.mul_sub_one _ _
    bc_run hlive hS [r20, r8, r19, hr2, r23, subw_addw (show v1 < 2 ^ 29 by omega)
      (show v1 * guess0 w0 w1 v1 < 2 ^ 29 by omega) (show 10 * w0 + w1 < 2 ^ 29 by omega) hle,
      subw_ofNat hv2g, slliw_ofNat, addw_ofNat] at 0x80005d90 0x80005d2c
    all_goals have r22 : R2 22 = BitVec.ofNat 64 (guess0 w0 w1 v1) := by rw [hk2.get 22]; bsimp [q22]
    all_goals have K : Keeps [1, 8, 10, 11, 12, 13, 15, 16, 19, 20, 22] R2 R :=
      (hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))
    · intro hhigh2
      have hg2 : 2 ≤ guess0 w0 w1 v1 := by
        refine Nat.lt_of_not_le fun h1 => ?_
        have : guess0 w0 w1 v1 = 1 := by omega
        rw [this] at hhigh2; omega
      have hg : guess w0 w1 w2 v1 v2 = guess0 w0 w1 v1 - 2 := by
        unfold guess guessStep
        simp only [guessHigh, decide_eq_true_eq, e1, e2]
        have hv1g : v1 ≤ v1 * guess0 w0 w1 v1 := Nat.le_mul_of_pos_right _ hg1
        generalize v1 * guess0 w0 w1 v1 = X at *
        generalize v2 * guess0 w0 w1 v1 = Y at *
        rw [if_pos (by omega), if_pos (by omega)]; omega
      bc_run hlive hS [r22, se12_ffe, word_sub2 hg2, sxw_ofNat] at 0x80005d38 0x80005d9c
      · intro he
        have h0 : guess0 w0 w1 v1 - 2 = 0 := ofNat64_eq (by omega) (by omega) he
        exact hc.zero (by rw [hg, h0]) _ (by keeps_tac K) (by bsimp [hg]) (by bsimp [])
      · intro hne
        exact hc.pos (by rw [hg]; intro h0; exact hne (by rw [h0])) _ (by keeps_tac K)
          (by bsimp [hg])
    · intro hlow
      have hg : guess w0 w1 w2 v1 v2 = guess0 w0 w1 v1 - 1 := by
        unfold guess guessStep
        simp only [guessHigh, decide_eq_true_eq, e1, e2]
        have hv1g : v1 ≤ v1 * guess0 w0 w1 v1 := Nat.le_mul_of_pos_right _ hg1
        generalize v1 * guess0 w0 w1 v1 = X at *
        generalize v2 * guess0 w0 w1 v1 = Y at *
        rw [if_pos (by omega), if_neg (by omega)]
      bc_run hlive hS [r22, se12_fff, word_pred hg1, sxw_ofNat] at 0x80005d9c 0x80005d38
      · intro hne
        exact hc.pos (by rw [hg]; intro h0; exact hne (by rw [h0])) _ (by keeps_tac K)
          (by bsimp [hg])
      · intro he
        have h0 : guess0 w0 w1 v1 - 1 = 0 :=
          ofNat64_eq (by omega) (by omega) (by rw [Classical.not_not.mp he])
        exact hc.zero (by rw [hg, h0]) _ (by keeps_tac K) (by bsimp [hg]) (by bsimp [])

/-- Signed division of small naturals. -/
theorem sdiv_small {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (hb0 : 0 < b) :
    sdivV (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a / b) := by
  rw [sdivV_pp (msb_ofNat_small ha) (msb_ofNat_small hb)]
  unfold udivV
  rw [if_neg (fun h => by
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp at this; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (show a < 2 ^ 64 by omega))]

/-- The window entering iteration `k`: the remainder so far, then the next
dividend digit. -/
abbrev DvData.W (D : DvData) (k : Nat) : Nat := 10 * (D.pre k % D.V) + D.xs.getD (k + D.L) 0

/-- The window's third digit (the byte after the window when `L = 1`). -/
abbrev DvData.w2 (D : DvData) (k : Nat) : Nat :=
  if 2 ≤ D.L then D.W k / 10 ^ (D.L - 2) % 10 else D.xs.getD (k + 2) 0

/-- The divisor's second digit (the sentinel `0` when `L = 1`). -/
abbrev DvData.v2 (D : DvData) : Nat := if 2 ≤ D.L then D.V / 10 ^ (D.L - 2) % 10 else 0

/-- Iteration `k`'s guess. -/
abbrev DvData.g (D : DvData) (k : Nat) : Nat :=
  guess (D.W k / 10 ^ D.L) (D.W k / 10 ^ (D.L - 1) % 10) (D.w2 k) (D.V / 10 ^ (D.L - 1)) D.v2

/-- The registers the guess changes. -/
abbrev guessClob : List Nat := [1, 5, 8, 10, 11, 12, 13, 15, 16, 19, 20, 21, 22, 23, 25]

/-- The digits the guess reads, from the window, the divisor and the sentinel. -/
structure GuessBytes (M : Mem) (D : DvData) (k : Nat) : Prop where
  w0 : ldv .lbu M (D.P + k) = BitVec.ofNat 64 (D.W k / 10 ^ D.L)
  w1 : ldv .lbu M (D.P + (k + 1)) = BitVec.ofNat 64 (D.W k / 10 ^ (D.L - 1) % 10)
  w2 : ldv .lbu M (D.P + k + 2) = BitVec.ofNat 64 (D.w2 k)
  v1 : ldv .lbu M D.N = BitVec.ofNat 64 (D.V / 10 ^ (D.L - 1))
  v2 : ldv .lbu M (D.N + 1) = BitVec.ofNat 64 D.v2
  w0d : D.W k / 10 ^ D.L ≤ 9
  w2d : D.w2 k < 10
  v1d : D.V / 10 ^ (D.L - 1) < 10
  v1p : 5 ≤ D.V / 10 ^ (D.L - 1)
  v2d : D.v2 < 10
  w0v : D.W k / 10 ^ D.L ≤ D.V / 10 ^ (D.L - 1)


/-- The divisor's leading digits, read off its value. -/
theorem DvShape.vtop {D : DvData} (hs : DvShape D) :
    D.vs.getD 0 0 = D.V / 10 ^ (D.L - 1) ∧ D.V < 10 ^ D.L ∧ D.V / 10 ^ (D.L - 1) < 10 := by
  have hlt : D.V < 10 ^ D.L := by have := dvalBE_lt hs.vd; rwa [hs.vl] at this
  have h0 := dvalBE_digit hs.vd (i := 0) (by rw [hs.vl]; exact hs.l1)
  rw [hs.vl, Nat.sub_zero, top_digit hlt hs.l1] at h0
  have hd := hs.vd.getD 0
  exact ⟨h0.symm, hlt, by omega⟩

/-- **The guess's bytes** at the loop head, from the window. -/
theorem GuessBytes.of_at {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj} {ds : List Nat}
    {k : Nat} (hs : DvShape D) (st : DvAt S Mt0 M R0 R sp W D H F Lh y ds k) :
    GuessBytes M D k := by
  obtain ⟨hv0, hV, hv1d⟩ := hs.vtop
  have hl1 := hs.l1
  have hxl := hs.xl
  have hkb := st.kb
  have hv1 : 5 ≤ D.V / 10 ^ (D.L - 1) := hv0 ▸ hs.v1
  have hRV : D.pre k % D.V < D.V := Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.zero_div] at hv1; omega)
  have hx : D.xs.getD (k + D.L) 0 < 10 := hs.xd.getD _
  have hx2 : D.xs.getD (k + 2) 0 < 10 := hs.xd.getD _
  have hW0 : D.W k / 10 ^ D.L = D.pre k % D.V / 10 ^ (D.L - 1) := by
    simp only [DvData.W]
    generalize D.xs.getD (k + D.L) 0 = x at hx
    have := div_shift (D.pre k % D.V) x (D.L - 1) hx
    rwa [show D.L - 1 + 1 = D.L by omega] at this
  have htop := top_digit (Nat.lt_trans hRV hV) hl1
  have hwin := st.win.win
  have hrest := st.win.rest
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hv1d, hv1, ?_, ?_⟩
  · rw [hW0]; apply lbu_digit (by omega)
    have := hwin 0 hl1; rw [Nat.add_zero, Nat.sub_zero, htop] at this; exact this
  · apply lbu_digit (Nat.mod_lt _ (by decide))
    rcases Nat.lt_or_ge 1 D.L with h2 | h2
    · simp only [DvData.W]; rw [win_digit hx h2]
      have := hwin 1 h2; rwa [Nat.add_assoc] at this
    · have e : D.L = 1 := by omega
      simp only [DvData.W]; rw [e, Nat.sub_self, win_last (hs.xd.getD _)]
      exact hrest (k + 1) (by omega) (by omega)
  · have hw2 : D.w2 k < 10 := by
      simp only [DvData.w2]; split
      · exact Nat.mod_lt _ (by decide)
      · exact hx2
    apply lbu_digit hw2
    simp only [DvData.w2]
    rcases Nat.lt_or_ge 2 D.L with h3 | h3
    · rw [if_pos (by omega)]; simp only [DvData.W]; rw [win_digit hx h3]
      exact hwin 2 h3
    · rcases Nat.lt_or_ge 1 D.L with h2 | h2
      · have e : D.L = 2 := by omega
        rw [if_pos (by omega)]; simp only [DvData.W]; rw [e, Nat.sub_self, win_last hx2]
        have := hrest (k + 2) (by omega) (by omega); rwa [Nat.add_assoc]
      · rw [if_neg (by omega)]
        exact hrest (k + 2) (by omega) (by omega)
  · rw [← hv0]; apply lbu_digit (hs.vd.getD 0)
    have := st.fix.div 0 hl1; rwa [Nat.add_zero] at this
  · simp only [DvData.v2]
    rcases Nat.lt_or_ge 1 D.L with h2 | h2
    · rw [if_pos (by omega)]
      have hd := dvalBE_digit hs.vd (i := 1) (by rw [hs.vl]; exact h2)
      rw [hs.vl, show D.L - 1 - 1 = D.L - 2 by omega] at hd
      rw [hd]; exact lbu_digit (hs.vd.getD 1) (st.fix.div 1 h2)
    · rw [if_neg (by omega)]
      have := st.fix.sent; rw [show D.L = 1 by omega] at this
      exact lbu_digit (by decide) this
  · rw [hW0]; have := Nat.mod_lt (D.pre k % D.V / 10 ^ (D.L - 1)) (show 0 < 10 by decide)
    rw [htop] at this; omega
  · simp only [DvData.w2]; split
    · exact Nat.mod_lt _ (by decide)
    · exact hx2
  · simp only [DvData.v2]; split
    · exact Nat.mod_lt _ (by decide)
    · decide
  · rw [hW0]; exact Nat.div_le_div_right (Nat.le_of_lt hRV)

/-- The continuation of the whole guess, from the loop head's registers. -/
structure DvGuessK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (M : Mem) (R : Nat → BitVec 64) (k g : Nat) : Prop where
  zero : g = 0 → ∀ R', Keeps guessClob R' R → R' 20 = 0#64 →
    R' 21 = BitVec.ofNat 64 (k + 1) → R' 22 = BitVec.ofNat 64 g → R' 25 = BitVec.ofNat 64 k →
    DW live S Q 0x80005d38#64 R' M
  pos : g ≠ 0 → ∀ R', Keeps guessClob R' R →
    R' 21 = BitVec.ofNat 64 (k + 1) → R' 22 = BitVec.ofNat 64 g → R' 25 = BitVec.ofNat 64 k →
    DW live S Q 0x80005d9c#64 R' M

/-- The whole guess's continuation, at the tests' entry. -/
theorem DvGuessK.toGuessK {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem} {R Rc : Nat → BitVec 64}
    {k g : Nat} (hc : DvGuessK live S Q M R k g) (hK : Keeps guessClob Rc R)
    (h21 : Rc 21 = BitVec.ofNat 64 (k + 1)) (h25 : Rc 25 = BitVec.ofNat 64 k) :
    GuessK live S Q M Rc g where
  zero hg R' hR h22 h20 := hc.zero hg R' ((hR.mono (by decide)).trans hK) h20
    (by rw [hR.get 21]; exact h21) h22 (by rw [hR.get 25]; exact h25)
  pos hg R' hR h22 := hc.pos hg R' ((hR.mono (by decide)).trans hK)
    (by rw [hR.get 21]; exact h21) h22 (by rw [hR.get 25]; exact h25)

/-- **The guess** from the loop head `0x80005d4c`: the window's top two
digits, the first guess (`9` or a division), then the tests. -/
theorem dv_guess_head {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64} {P N k w0 w1 w2 v1 v2 : Nat}
    (hw0 : w0 ≤ v1) (hw1 : w1 < 10) (hw2 : w2 < 10) (hv1 : v1 < 10) (hv0 : 0 < v1) (hv2 : v2 < 10)
    (hP0 : 2147603920 ≤ P) (hP2 : P + k + 2 < 2273312768)
    (hN : 2147603920 ≤ N) (hN2 : N + 1 < 2273312768) (hk : k + 2 < 2 ^ 31)
    (lw0 : ldv .lbu M (P + k) = BitVec.ofNat 64 w0)
    (lw1 : ldv .lbu M (P + (k + 1)) = BitVec.ofNat 64 w1)
    (lw2 : ldv .lbu M (P + k + 2) = BitVec.ofNat 64 w2)
    (lv2 : ldv .lbu M (N + 1) = BitVec.ofNat 64 v2)
    (h9 : R 9 = BitVec.ofNat 64 k) (h17 : R 17 = BitVec.ofNat 64 v1)
    (h18 : R 18 = BitVec.ofNat 64 P) (h24 : R 24 = BitVec.ofNat 64 N)
    (hc : DvGuessK live S Q M R k (guess w0 w1 w2 v1 v2)) :
    DW live S Q 0x80005d4c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h9, h17, h18, lw0, lw1, shl_shr32, sxw_ofNat, addw_ofNat, slliw_ofNat]
    at 0x80005cb4 0x80005cbc
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro hne
    have hne' : w0 ≠ v1 := fun h => hne (by rw [h])
    have hg0 : guess0 w0 w1 v1 = (10 * w0 + w1) / v1 := by unfold guess0; rw [if_neg hne']
    bc_run hlive hS [] at 0x80005cb4
    apply st_80005cb4 hlive
    refine divdi3_spec hlive _ (by bsimp []) fun R1 hk1 hr1 => ?_
    bsimp [] at hr1 ⊢
    rw [show w1 + (w0 * 2 ^ 2 + w0) * 2 ^ 1 = 10 * w0 + w1 by omega,
      sdiv_small (by omega) (by omega) hv0] at hr1
    have hq : (10 * w0 + w1) / v1 < 2 ^ 31 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    bc_run hlive hS [hr1, sxw_ofNat] at 0x80005cbc
    have K : Keeps guessClob _ R := (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
    refine dv_guess_test hlive hS (by omega) hw1 hw2 hv1 hv2 (by omega) hP2 (by omega) hN2 hk lw2
      lv2 (by bsimp [hg0]) (by bsimp []; rw [hk1.get 20]; bsimp []) (by bsimp []; rw [hk1.get 23]; bsimp []; congr 1; omega)
      (by bsimp []; rw [hk1.get 24]; bsimp [h24]) (by bsimp []; rw [hk1.get 9]; bsimp [h9])
      (by bsimp []; rw [hk1.get 18]; bsimp [h18])
      (hc.toGuessK (by keeps_tac K) (by bsimp []; rw [hk1.get 21]; bsimp [])
        (by bsimp []; rw [hk1.get 25]; bsimp []))
  · intro he
    have he' : w0 = v1 := ofNat64_eq (by omega) (by omega) (Classical.not_not.mp he)
    have hg0 : guess0 w0 w1 v1 = 9 := by unfold guess0; rw [if_pos he']
    bc_run hlive hS [] at 0x80005cbc
    refine dv_guess_test hlive hS (by omega) hw1 hw2 hv1 hv2 (by omega) hP2 (by omega) hN2 hk lw2
      lv2 (by bsimp [hg0]) (by bsimp []) (by bsimp []; congr 1; omega)
      (by bsimp [h24]) (by bsimp [h9]) (by bsimp [h18])
      (hc.toGuessK (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp []))

/-- One more dividend digit. -/
theorem DvShape.pre_succ {D : DvData} (hs : DvShape D) {k : Nat} (hk : k ≤ D.Kb) :
    D.pre (k + 1) = 10 * D.pre k + D.xs.getD (k + D.L) 0 := by
  have hl := hs.xl
  have hi : D.L + k < D.xs.length := by omega
  simp only [DvData.pre]
  rw [show D.L + (k + 1) = D.L + k + 1 by omega, List.take_succ, List.getElem?_eq_getElem hi,
    Option.toList_some, dvalBE_append]
  simp only [List.length_singleton, Nat.pow_one, dvalBE, List.foldl_cons, List.foldl_nil,
    Nat.mul_zero, Nat.zero_add]
  rw [List.getD_eq_getElem?_getD, show k + D.L = D.L + k by omega, List.getElem?_eq_getElem hi,
    Option.getD_some, Nat.mul_comm]

/-- The divisor is positive. -/
theorem DvShape.vpos {D : DvData} (hs : DvShape D) : 0 < D.V := by
  obtain ⟨hv0, -, -⟩ := hs.vtop
  have := hs.v1
  rw [hv0] at this
  exact Nat.pos_of_ne_zero fun h => by rw [h, Nat.zero_div] at this; omega

/-- The window is below ten divisors: its quotient is one digit. -/
theorem DvShape.W_lt {D : DvData} (hs : DvShape D) (k : Nat) : D.W k < 10 * D.V := by
  have hR := Nat.mod_lt (D.pre k) hs.vpos
  have hx : D.xs.getD (k + D.L) 0 < 10 := hs.xd.getD _
  simp only [DvData.W]; omega

/-- The quotient and remainder of the longer prefix, from the window. -/
theorem DvShape.pre_succ_div {D : DvData} (hs : DvShape D) {k : Nat} (hk : k ≤ D.Kb) :
    D.pre (k + 1) / D.V = 10 * (D.pre k / D.V) + D.W k / D.V ∧
      D.pre (k + 1) % D.V = D.W k % D.V := by
  rw [hs.pre_succ hk]; exact div_snoc hs.vpos

/-- **The window as one number**: the `L + 1` bytes from `P + k` are the
digits of `W k`. -/
theorem DvShape.winW {D : DvData} {M : Mem} {ds : List Nat} {k : Nat} (hs : DvShape D)
    (hw : DvWin M D ds k) (hk : k ≤ D.Kb) :
    ∀ i, i ≤ D.L → imgM M (D.P + k + i) = BitVec.ofNat 8 (D.W k / 10 ^ (D.L - i) % 10) := by
  intro i hi
  have hx : D.xs.getD (k + D.L) 0 < 10 := hs.xd.getD _
  have hl := hs.xl
  have hl1 := hs.l1
  simp only [DvData.W]
  rcases Nat.lt_or_ge i D.L with h | h
  · rw [win_digit hx h]; exact hw.win i h
  · have e : i = D.L := by omega
    subst e
    rw [Nat.sub_self, win_last hx, Nat.add_assoc, Nat.add_comm k]
    exact hw.rest _ (by omega) (by omega)

/-- The scratch bytes of one iteration: the window, the product buffer and
the stack below the frame. -/
abbrev DvTouch (sp W : Nat) (D : DvData) (k a : Nat) : Prop :=
  (D.P + k ≤ a ∧ a ≤ D.P + k + D.L) ∨ D.b3.In a ∨ (sp - W ≤ a ∧ a < sp - 208)

/-- **An iteration's result**: the window replaced by the remainder `W k % V`
(below its top byte), registers for the store. -/
theorem DvMid.of_touch {S : Nat → Prop} {Mt0 M0 M : Mem} {R0 R R' : Nat → BitVec 64}
    {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj}
    {ds : List Nat} {k : Nat} (hs : DvShape D) (cx : DvCtx S sp W)
    (st : DvAt S Mt0 M0 R0 R sp W D H F Lh y ds k) (hm : MemOnly (DvTouch sp W D k) M M0)
    (hwin : ∀ i, i < D.L → imgM M (D.P + (k + 1) + i) =
      BitVec.ofNat 8 (D.W k % D.V / 10 ^ (D.L - 1 - i) % 10))
    (h2 : R' 2 = BitVec.ofNat 64 (sp - 208)) (h9 : R' 9 = BitVec.ofNat 64 k)
    (h21 : R' 21 = BitVec.ofNat 64 (k + 1)) (h18 : R' 18 = BitVec.ofNat 64 D.P)
    (h24 : R' 24 = BitVec.ofNat 64 D.N) (h27 : R' 27 = BitVec.ofNat 64 (y.rep.val + D.off + k))
    (h26 : R' 26 = BitVec.ofNat 64 D.Kb) (hk : Keeps divAll R' R0) :
    DvMid S Mt0 M R0 R' sp W D H F Lh y ds k := by
  have hkb := st.kb
  have hl := hs.xl
  obtain ⟨hq, hr⟩ := hs.pre_succ_div hkb
  have hd : D.W k / D.V < 10 :=
    (Nat.div_lt_iff_lt_mul hs.vpos).mpr (by have := hs.W_lt k; omega)
  refine ⟨st.fix.scratch cx.above (by have := cx.big; omega) (hm.mono fun a ha => ?_),
    fun i hi => by rw [hr]; exact hwin i hi, fun i hi1 hi2 => ?_, fun j hj => ?_,
    h2, h9, h21, h18, h24, h27, h26, hk, hkb⟩
  · rcases ha with ha | ha | ha
    · refine .inl ?_
      have := st.fix.pIn (a - D.P) (by omega)
      rwa [show D.P + (a - D.P) = a by omega] at this
    · exact .inr (.inl ha)
    · exact .inr (.inr ha)
  · have hne : ¬ DvTouch sp W D k (D.P + i) := by
      intro h
      rcases h with h | h | h
      · omega
      · exact live_apart st.fix.heap.heap st.fix.b1l st.fix.b3l st.fix.b13 (st.fix.pIn _ hi2) h
      · have := live_in_heap st.fix.heap.heap st.fix.b1l (st.fix.pIn _ hi2)
        have := cx.above; simp only [heapEnd] at *; omega
    rw [hm _ hne]
    exact st.win.rest i (by omega) hi2
  · rw [st.win.quot j hj, hq, show k - j = k - 1 - j + 1 by omega, Nat.pow_succ',
      ← Nat.div_div_eq_div_mul, Nat.add_comm (10 * _), Nat.add_mul_div_left _ _ (by decide : 0 < 10),
      Nat.div_eq_of_lt hd, Nat.zero_add]

/-- **The guess's bounds**: the true digit `W k / V` or one more, at most `9`. -/
theorem DvShape.g_bounds {D : DvData} (hs : DvShape D) (k : Nat) :
    D.W k / D.V ≤ D.g k ∧ D.g k ≤ D.W k / D.V + 1 ∧ D.g k ≤ 9 := by
  obtain ⟨hv0, hV, -⟩ := hs.vtop
  have h5 : 5 ≤ D.V / 10 ^ (D.L - 1) := hv0 ▸ hs.v1
  have hV1 : 5 * 10 ^ (D.L - 1) ≤ D.V :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mp h5
  exact guess_window (b := D.xs.getD (k + 2) 0) hs.l1 hV1 hV (hs.W_lt k)

/-- **The guess** at iteration `k`'s loop head. -/
theorem dv_guess {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {y : NumObj} {ds : List Nat} {k : Nat}
    (hs : DvShape D) (st : DvAt S Mt0 M R0 R sp W D H F Lh y ds k)
    (hc : DvGuessK live S Q M R k (D.g k)) :
    DW live S Q 0x80005d4c#64 R M := by
  have gb := GuessBytes.of_at hs st
  have hf := st.fix
  have hi := hf.heap.heap
  have hl := hs.xl; have hsm := hs.small; have hkb := st.kb; have hl1 := hs.l1
  have hp0 := live_in_heap hi hf.b1l (hf.pIn 0 (by omega))
  have hp2 := live_in_heap hi hf.b1l (hf.pIn (k + 2) (by omega))
  have hn0 := live_in_heap hi hf.b2l (hf.nIn 0 (Nat.zero_le _))
  have hn1 := live_in_heap hi hf.b2l (hf.nIn 1 hl1)
  simp only [heapStart, heapEnd] at hp0 hp2 hn0 hn1
  have hw1 : D.W k / 10 ^ (D.L - 1) % 10 < 10 := Nat.mod_lt _ (by decide)
  have hv1 : 0 < D.V / 10 ^ (D.L - 1) := by have := gb.v1p; omega
  exact dv_guess_head hlive hf.heapOwn gb.w0v hw1 gb.w2d gb.v1d hv1 gb.v2d (by omega) (by omega)
    (by omega) (by omega) (by omega) gb.w0 gb.w1 gb.w2 gb.v2 st.r9
    (by rw [st.r17, hs.vtop.1]) st.r18 st.r24 hc

/-- **A zero digit**: the window already below the divisor; the remainder
is the window, unchanged. -/
theorem dv_zero {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap}
    {F : List Blk} {Lh : List NumObj} {y : NumObj} {ds : List Nat} {k : Nat}
    (cx : DvCtx S sp W) (hs : DvShape D) (st : DvAt S Mt0 M R0 R sp W D H F Lh y ds k)
    (hk : DvK live S Q Mt0 R0 sp W D H F Lh y k) (hg : D.g k = 0)
    (K : Keeps guessClob R' R) (h20 : R' 20 = 0#64) (h21 : R' 21 = BitVec.ofNat 64 (k + 1)) :
    DW live S Q 0x80005d38#64 R' M := by
  have hb := (hs.g_bounds k).1
  rw [hg] at hb
  have hq : D.W k / D.V = 0 := Nat.le_zero.mp hb
  have hlt : D.W k < D.V := by
    rcases (Nat.lt_or_ge (D.W k) D.V) with h | h
    · exact h
    · have := Nat.div_pos h hs.vpos; omega
  have hwW := hs.winW st.win st.kb
  refine dv_store hlive cx hs (DvMid.of_touch hs cx st (MemOnly.refl _ _) (fun i hi => ?_)
    (by rw [K.get 2]; exact st.r2) (by rw [K.get 9]; exact st.r9) h21
    (by rw [K.get 18]; exact st.r18) (by rw [K.get 24]; exact st.r24)
    (by rw [K.get 27]; exact st.r27) (by rw [K.get 26]; exact st.r26)
    ((K.mono (by decide)).trans st.regs)) ?_ hk
  · rw [Nat.mod_eq_of_lt hlt, show D.P + (k + 1) + i = D.P + k + (i + 1) by omega,
      hwW (i + 1) (by omega), show D.L - (i + 1) = D.L - 1 - i by omega]
  · rw [h20, (hs.pre_succ_div st.kb).1, hq, Nat.add_zero, Nat.mul_mod_right]

/-- The low digits of an add-back are the addition's. -/
theorem addBack_getD_lt {s v : List Nat} (hs : s.length = v.length + 1) {j : Nat}
    (hj : j < v.length) : (addBack s v).getD j 0 = (addLE (s.take v.length) v 0).getD j 0 := by
  have hl : (addLE (s.take v.length) v 0).length = v.length + 1 :=
    by rw [addLE_length _ _ _ (by simp only [List.length_take]; omega)]; simp only [List.length_take]; omega
  unfold addBack
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_take]; omega),
    List.getElem?_take_of_lt hj, ← List.getD_eq_getElem?_getD]

/-- Two runs of bytes in distinct live blocks do not overlap. -/
theorem live_ranges_apart {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {b c : Blk} (hb : b ∈ H.live) (hc : c ∈ H.live) (hne : b ≠ c) {x y n m : Nat}
    (hx : ∀ i, i ≤ n → b.In (x + i)) (hy : ∀ i, i ≤ m → c.In (y + i)) :
    x + n < y ∨ y + m < x := by
  rcases Nat.lt_or_ge (x + n) y with h | h
  · exact .inl h
  rcases Nat.lt_or_ge (y + m) x with h' | h'
  · exact .inr h'
  exfalso
  rcases Nat.le_total x y with h2 | h2
  · have e1 := hx (y - x) (by omega)
    have e2 := hy 0 (Nat.zero_le _)
    rw [show x + (y - x) = y by omega] at e1; rw [Nat.add_zero] at e2
    exact live_apart hi hb hc hne e1 e2
  · have e1 := hx 0 (Nat.zero_le _)
    have e2 := hy (x - y) (by omega)
    rw [show y + (x - y) = x by omega] at e2; rw [Nat.add_zero] at e1
    exact live_apart hi hb hc hne e1 e2

/-- The loop's state at a memory changed only on the iteration's scratch. -/
theorem DvAt.fix_touch {S : Nat → Prop} {Mt0 M0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj}
    {ds : List Nat} {k : Nat} (hs : DvShape D) (cx : DvCtx S sp W)
    (st : DvAt S Mt0 M0 R0 R sp W D H F Lh y ds k) (hm : MemOnly (DvTouch sp W D k) M M0) :
    DvFix S Mt0 M R0 sp W D H F Lh y ds := by
  have hkb := st.kb
  have hl := hs.xl
  refine st.fix.scratch cx.above (by have := cx.big; omega) (hm.mono fun a ha => ?_)
  rcases ha with ha | ha | ha
  · refine .inl ?_
    have := st.fix.pIn (a - D.P) (by omega)
    rwa [show D.P + (a - D.P) = a by omega] at this
  · exact .inr (.inl ha)
  · exact .inr (.inr ha)

/-- The window's digits, low first. -/
abbrev DvData.wL (D : DvData) (k : Nat) : List Nat := BcModel.digLE (D.W k) (D.L + 1)

/-- The product's digits, low first. -/
abbrev DvData.mL (D : DvData) (k : Nat) : List Nat := BcModel.digLE (D.V * D.g k) (D.L + 1)

/-- The divisor's digits, low first. -/
abbrev DvData.vL (D : DvData) : List Nat := BcModel.digLE D.V D.L

/-- **Iteration `k`'s step**, in the window's, product's and divisor's
digit lists. -/
theorem DvShape.step {D : DvData} (hs : DvShape D) (k : Nat) :
    dvalLE (D.wL k) = D.W k ∧ dvalLE D.vL = D.V ∧ StepRes (D.wL k) (D.mL k) D.vL (D.g k) := by
  obtain ⟨-, hV, -⟩ := hs.vtop
  obtain ⟨hlo, hhi, h9⟩ := hs.g_bounds k
  have hW := hs.W_lt k
  have hp : 10 ^ (D.L + 1) = 10 * 10 ^ D.L := Nat.pow_succ'
  have hw : dvalLE (D.wL k) = D.W k := by
    simp only [DvData.wL]; rw [BcModel.digLE_val, Nat.mod_eq_of_lt (by omega)]
  have hv : dvalLE D.vL = D.V := by simp only [DvData.vL]; rw [BcModel.digLE_val, Nat.mod_eq_of_lt hV]
  have hVg : D.V * D.g k ≤ D.V * 9 := Nat.mul_le_mul_left _ h9
  have hm : dvalLE (D.mL k) = D.V * D.g k := by
    simp only [DvData.mL]; rw [BcModel.digLE_val, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hw, hv, step_spec (BcModel.digLE_digits _ _) (BcModel.digLE_digits _ _) (BcModel.digLE_digits _ _)
    (by simp only [DvData.wL, DvData.vL, BcModel.digLE_length]) (by simp only [DvData.mL, DvData.vL, BcModel.digLE_length])
    (by rw [hm, hv]) (by rw [hv]; exact hs.vpos) (by rw [hw, hv]; exact hlo)
    (by rw [hw, hv]; exact hhi)⟩

/-- **The new window** from the step's digits at the window's low `L` bytes. -/
theorem DvShape.win_of_step {D : DvData} {M : Mem} {k : Nat} (hs : DvShape D)
    (hb : ∀ j, j < D.L → imgM M (D.P + k + D.L - j) =
      BitVec.ofNat 8 ((stepWin (D.wL k) (D.mL k) D.vL).getD j 0)) :
    ∀ i, i < D.L → imgM M (D.P + (k + 1) + i) =
      BitVec.ofNat 8 (D.W k % D.V / 10 ^ (D.L - 1 - i) % 10) := by
  obtain ⟨hw, hv, sr⟩ := hs.step k
  intro i hi
  have e := hb (D.L - 1 - i) (by omega)
  rw [show D.P + k + D.L - (D.L - 1 - i) = D.P + (k + 1) + i by omega, dvalLE_getD sr.digits,
    sr.val, hw, hv] at e
  exact e

/-- The digit iteration `k` stores. -/
theorem DvShape.digit {D : DvData} (hs : DvShape D) {k : Nat} (hk : k ≤ D.Kb) :
    D.pre (k + 1) / D.V % 10 = D.W k / D.V := by
  have hd : D.W k / D.V < 10 :=
    (Nat.div_lt_iff_lt_mul hs.vpos).mpr (by have := hs.W_lt k; omega)
  rw [(hs.pre_succ_div hk).1, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

/-- The state after the subtraction, at `0x80005e18`. -/
structure DvSubd (S : Nat → Prop) (Mt0 M0 M : Mem) (R0 Rh R : Nat → BitVec 64) (sp W : Nat)
    (D : DvData) (H : Heap) (F : List Blk) (Lh : List NumObj) (y : NumObj) (ds : List Nat)
    (k : Nat) : Prop where
  head : DvAt S Mt0 M0 R0 Rh sp W D H F Lh y ds k
  g0 : 1 ≤ D.g k
  touch : MemOnly (DvTouch sp W D k) M M0
  sub : ∀ i, i ≤ D.L → imgM M (D.P + k + D.L - i) =
    BitVec.ofNat 8 ((subLE (D.wL k) (D.mL k) 0).getD i 0)
  r10 : R 10 = BitVec.ofNat 64 (subBorrow (D.wL k) (D.mL k) 0)
  r22 : R 22 = BitVec.ofNat 64 (D.g k)
  r25 : R 25 = BitVec.ofNat 64 (D.P + (k + D.L))
  r2 : R 2 = BitVec.ofNat 64 (sp - 208)
  r9 : R 9 = BitVec.ofNat 64 k
  r21 : R 21 = BitVec.ofNat 64 (k + 1)
  r18 : R 18 = BitVec.ofNat 64 D.P
  r24 : R 24 = BitVec.ofNat 64 D.N
  r27 : R 27 = BitVec.ofNat 64 (y.rep.val + D.off + k)
  r26 : R 26 = BitVec.ofNat 64 D.Kb
  regs : Keeps divAll R R0

/-- The state after the add-back, at `0x80005f44`: the new window in place
below its top byte, the digit `g - 1` in `s4`. -/
structure DvAdded (S : Nat → Prop) (Mt0 M0 M : Mem) (R0 Rh R : Nat → BitVec 64) (sp W : Nat)
    (D : DvData) (H : Heap) (F : List Blk) (Lh : List NumObj) (y : NumObj) (ds : List Nat)
    (k : Nat) : Prop where
  head : DvAt S Mt0 M0 R0 Rh sp W D H F Lh y ds k
  touch : MemOnly (DvTouch sp W D k) M M0
  win : ∀ i, i < D.L → imgM M (D.P + (k + 1) + i) =
    BitVec.ofNat 8 (D.W k % D.V / 10 ^ (D.L - 1 - i) % 10)
  r2 : R 2 = BitVec.ofNat 64 (sp - 208)
  r9 : R 9 = BitVec.ofNat 64 k
  r21 : R 21 = BitVec.ofNat 64 (k + 1)
  r18 : R 18 = BitVec.ofNat 64 D.P
  r24 : R 24 = BitVec.ofNat 64 D.N
  r27 : R 27 = BitVec.ofNat 64 (y.rep.val + D.off + k)
  r26 : R 26 = BitVec.ofNat 64 D.Kb
  r25 : R 25 = BitVec.ofNat 64 (D.P + (k + D.L))
  r20 : R 20 = BitVec.ofNat 64 (D.pre (k + 1) / D.V % 10)
  regs : Keeps divAll R R0

/-- **After the add-back**: the final carry bumps the window's top byte
(mod 10), then the digit store. -/
theorem dv_added {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M0 M2 : Mem} {R0 Rh R2 : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap}
    {F : List Blk} {Lh : List NumObj} {y : NumObj} {ds : List Nat} {k : Nat}
    (cx : DvCtx S sp W) (hs : DvShape D)
    (st : DvAdded S Mt0 M0 M2 R0 Rh R2 sp W D H F Lh y ds k)
    (hk : DvK live S Q Mt0 R0 sp W D H F Lh y k) :
    DW live S Q 0x80005f44#64 R2 M2 := by
  have hf2 := st.head.fix_touch hs cx st.touch
  have hS := hf2.heapOwn
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hkb := st.head.kb
  have hl1 := hs.l1; have hxl := hs.xl; have hsm := hs.small
  have hi := hf2.heap.heap
  have hp0 := live_in_heap hi hf2.b1l (hf2.pIn k (by omega))
  have hpL := live_in_heap hi hf2.b1l (hf2.pIn (k + D.L) (by omega))
  simp only [heapStart, heapEnd] at hp0 hpL
  have hsp := cx.frame.lo; have hsp2 := cx.frame.hi; have hab := cx.above; have hW := cx.big
  simp only [heapEnd, htx] at hab hsp
  have touch2 := st.touch
  have hwin := st.win
  have q2 := st.r2; have q9 := st.r9; have q21 := st.r21; have q18 := st.r18; have q24 := st.r24
  have q27 := st.r27; have q26 := st.r26; have q25 := st.r25; have q20 := st.r20
  have qregs := st.regs
  have t24 := hf2.s24
  bc_run hlive hS [] at 0x80005d38 0x80005f6c
  · intro _
    exact dv_store hlive cx hs (DvMid.of_touch hs cx st.head touch2 hwin (by bsimp [q2])
      (by bsimp [q9]) (by bsimp [q21]) (by bsimp [q18]) (by bsimp [q24]) (by bsimp [q27])
      (by bsimp [q26]) (by keeps_tac qregs)) (by bsimp [q20]) hk
  · intro _
    bc_run hlive hS [q2, q25, t24, se12_fff, word_pred hl1, shl_shr32, sxw_ofNat,
      sub_ofNat (show D.L - 1 ≤ D.P + (k + D.L) by omega) (by omega),
      word_pred (show 1 ≤ D.P + (k + D.L) - (D.L - 1) by omega)] at 0x80005f6c
    all_goals first | exact acc_heap hS (by omega) (by omega) | dc_frame cx.frame | skip
    apply st_80005f6c hlive
    refine moddi3_spec hlive _ (by bsimp []) fun R3 hk3 _ => ?_
    bsimp []
    have r25 : R3 25 = BitVec.ofNat 64 (D.P + (k + D.L) - (D.L - 1)) := by
      rw [hk3.get 25]; bsimp []
    bc_run hlive hS [r25, se12_fff, word_pred (show 1 ≤ D.P + (k + D.L) - (D.L - 1) by omega)]
      at 0x80005d38
    all_goals first | exact acc_heap hS (by omega) (by omega) | skip
    have touch3 := ((MemOnly.store M2 (D.P + (k + D.L) - (D.L - 1) - 1) 1 (R3 10)).mono
      fun b hb => (show DvTouch sp W D k b from .inl ⟨by omega, by omega⟩)).trans touch2
    exact dv_store hlive cx hs (DvMid.of_touch hs cx st.head touch3
      (fun i hi => by rw [imgM_store_miss _ _ (by omega)]; exact hwin i hi)
      (by rw [hk3.get 2]; bsimp [q2]) (by rw [hk3.get 9]; bsimp [q9])
      (by rw [hk3.get 21]; bsimp [q21]) (by rw [hk3.get 18]; bsimp [q18])
      (by rw [hk3.get 24]; bsimp [q24]) (by rw [hk3.get 27]; bsimp [q27])
      (by rw [hk3.get 26]; bsimp [q26])
      ((hk3.mono (by decide)).trans (by keeps_tac qregs)))
      (by rw [hk3.get 20]; bsimp [q20]) hk

/-- **After the subtraction**: store the guess, or add the divisor back and
store one less. -/
theorem dv_after_sub {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M0 M : Mem} {R0 Rh R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap}
    {F : List Blk} {Lh : List NumObj} {y : NumObj} {ds : List Nat} {k : Nat}
    (cx : DvCtx S sp W) (hs : DvShape D)
    (st : DvSubd S Mt0 M0 M R0 Rh R sp W D H F Lh y ds k)
    (hk : DvK live S Q Mt0 R0 sp W D H F Lh y k) :
    DW live S Q 0x80005e18#64 R M := by
  have hf := st.head.fix_touch hs cx st.touch
  have hS := hf.heapOwn
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨hw, hv, sr⟩ := hs.step k
  have hb1 := subBorrow_le (D.wL k) (D.mL k) 0 (by decide)
  have h10 := st.r10
  have hkb := st.head.kb
  bc_run hlive hS [h10] at 0x80005eec 0x80005e20
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro he
    have h1 : subBorrow (D.wL k) (D.mL k) 0 = 1 := ofNat64_eq (by omega) (by decide) he
    have hdig : D.g k - 1 = D.W k / D.V := by
      have := sr.dig; rw [h1, hw, hv] at this; exact this
    have hg1 := st.g0
    have hl1 := hs.l1; have hxl := hs.xl; have hsm := hs.small
    have hi := hf.heap.heap
    have hp0 := live_in_heap hi hf.b1l (hf.pIn k (by omega))
    have hpL := live_in_heap hi hf.b1l (hf.pIn (k + D.L) (by omega))
    have hn0 := live_in_heap hi hf.b2l (hf.nIn 0 (Nat.zero_le _))
    have hnL := live_in_heap hi hf.b2l (hf.nIn D.L (Nat.le_refl _))
    simp only [heapStart, heapEnd] at hp0 hpL hn0 hnL
    have hsp := cx.frame.lo; have hsp2 := cx.frame.hi; have hab := cx.above; have hW := cx.big
    simp only [heapEnd, htx] at hab hsp
    have h2 := st.r2; have h22 := st.r22; have h24 := st.r24; have h25 := st.r25
    have s24 := hf.s24; have s16 := hf.s16
    have hg9 := (hs.g_bounds k).2.2
    bc_run hlive hS [h2, h22, h24, h25, s24, s16, se12_fff, word_pred hg1, word_pred hl1,
      sxw_ofNat] at 0x80005f14
    all_goals first | exact acc_heap hS (by omega) (by omega) | dc_frame cx.frame | skip
    · intro h0; exact absurd (ofNat64_eq (by omega) (by decide) h0) (by omega)
    intro _
    bc_run hlive hS [h2, h24, h25, s16, se12_fff, word_pred hl1] at 0x80005f14
    all_goals first | exact acc_heap hS (by omega) (by omega) | dc_frame cx.frame | skip
    have hvl : D.vL.length = D.L := by simp only [DvData.vL, BcModel.digLE_length]
    have hsl : (subLE (D.wL k) (D.mL k) 0).length = D.L + 1 := by
      rw [subLE_length _ _ _ (by simp only [DvData.wL, DvData.mL, BcModel.digLE_length])]
      simp only [DvData.wL, BcModel.digLE_length]
    have hda : DaArgs M (D.P + k) D.N D.L (subLE (D.wL k) (D.mL k) 0) D.vL := by
      refine ⟨hsl, hvl, subLE_digits _ _ _ (BcModel.digLE_digits _ _) (BcModel.digLE_digits _ _)
        (by decide), BcModel.digLE_digits _ _, st.sub, fun j hj => ?_, by omega, by omega,
        by omega, by omega, ?_, hl1⟩
      · have hd := dvalBE_digit hs.vd (i := D.L - 1 - j) (by rw [hs.vl]; omega)
        rw [hs.vl, show D.L - 1 - (D.L - 1 - j) = j by omega] at hd
        rw [show D.N + D.L - 1 - j = D.N + (D.L - 1 - j) by omega, hf.div _ (by omega)]
        simp only [DvData.vL]; rw [BcModel.digLE_getD _ _ _ hj, ← hd]
      · rcases live_ranges_apart hi hf.b1l hf.b2l hf.b12 (x := D.P + k) (n := D.L) (y := D.N)
          (m := D.L) (fun i hi => by rw [Nat.add_assoc]; exact hf.pIn _ (by omega)) hf.nIn with h | h
        · exact .inl h
        · exact .inr (by omega)
    refine dadd_loop hlive hS hda (fun R2 M2 dp => ?_) _ 0 _ _ rfl
      ⟨by bsimp []; congr 1; omega, by bsimp []; congr 1; omega, by bsimp [carryAt_zero],
        by bsimp [], by bsimp [], by bsimp [h10, h1], Keeps.refl _ _, hl1,
        fun i hi => absurd hi (Nat.not_lt_zero _), MemOnly.refl _ _⟩
    have touch2 : MemOnly (DvTouch sp W D k) M2 M0 :=
      (dp.only.mono fun a ha => .inl ⟨by omega, by omega⟩).trans st.touch
    have hbw : stepWin (D.wL k) (D.mL k) D.vL = addBack (subLE (D.wL k) (D.mL k) 0) D.vL := by
      unfold stepWin; rw [if_pos h1]
    have hwin := hs.win_of_step (M := M2) fun j hj => by
      rw [hbw, addBack_getD_lt (by rw [hsl, hvl]) (by rw [hvl]; exact hj), hvl]
      exact dp.done j hj
    exact dv_added hlive cx hs ⟨st.head, touch2, hwin, by rw [dp.regs.get 2]; bsimp [h2],
      by rw [dp.regs.get 9]; bsimp [st.r9], by rw [dp.regs.get 21]; bsimp [st.r21],
      by rw [dp.regs.get 18]; bsimp [st.r18], by rw [dp.regs.get 24]; bsimp [h24],
      by rw [dp.regs.get 27]; bsimp [st.r27], by rw [dp.regs.get 26]; bsimp [st.r26],
      by rw [dp.regs.get 25]; bsimp [h25],
      by rw [dp.regs.get 20, hs.digit hkb, ← hdig]; bsimp [],
      (dp.regs.mono (by decide)).trans (by keeps_tac st.regs)⟩ hk
  · intro hne
    have h0 : subBorrow (D.wL k) (D.mL k) 0 = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with h | h
      · exact h
      · exact absurd (by rw [h]) hne
    have hsw : stepWin (D.wL k) (D.mL k) D.vL = subLE (D.wL k) (D.mL k) 0 := by
      unfold stepWin; rw [if_neg (by omega)]
    have hdig : D.g k = D.W k / D.V := by
      have := sr.dig; rw [h0, Nat.sub_zero, hw, hv] at this; exact this
    refine dv_store' hlive cx hs (DvMid.of_touch hs cx st.head st.touch
      (hs.win_of_step fun j hj => by rw [hsw]; exact st.sub j (by omega))
      (by bsimp [st.r2]) (by bsimp [st.r9]) (by bsimp [st.r21]) (by bsimp [st.r18])
      (by bsimp [st.r24]) (by bsimp [st.r27]) (by bsimp [st.r26]) (by keeps_tac st.regs)) ?_ hk
    bsimp [st.r22]; rw [hs.digit hkb, hdig]

end Dc.Mach
