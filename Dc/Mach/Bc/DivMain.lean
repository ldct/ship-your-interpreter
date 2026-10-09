import Dc.Mach.Bc.DivSub

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

end Dc.Mach
