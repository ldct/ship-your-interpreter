import Dc.Mach.Bc.DivMain
import Dc.Mach.Bc.AddSub
import Dc.Mach.Bc.Init

/-!
# `bc_divide`'s tail (`0x80005a90`)

```
80005a90 lw a3,0(s0) ; lw a1,0(s1) ; ld a2,_zero_ ; ld a5,32(s5)
80005aa4 sub a3,a3,a1 ; snez a3,a3 ; sw a3,0(s5) ; beq a2,s5,80005b8c
80005ab4 … bc_is_zero (qval), inlined (0x80005ad4) ; 80005b8c sw zero,0(s5)
80005ae4 … _bc_rm_leading_zeros (qval), inlined (0x80005b0c)
80005b14 mv a0,s6 ; jal bc_free_num ; 80005b1c ld a0,8(sp) ; sd s5,0(s6)
80005b24 jal free (mval) ; jal free (num1) ; jal free (num2)
80005b38 li a0,0 ; 80005b3c … epilogue, ret
```

- `DivCtx`: the frame, the result slot and the constants.
- `DivKW`: the continuations (quotient, division by zero, `out_of_memory`).
- `BinPostW.freeRaw`, `dvt_free`: `free` of a raw buffer keeps the result.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- `bc_divide`'s fixed context: the frame (`208` bytes and the callees'
below it), the result slot, the constants `_zero_` is read from. -/
structure DivCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp q W : Nat) : Prop where
  frame : StackFrame S sp W
  above : heapEnd + W ≤ sp
  big : 272 ≤ W
  slot : PtrSlot S q
  slotOut : ∀ a, slotBytes q a → OutHeap a
  slotApart : q + 8 ≤ sp - W ∨ sp ≤ q
  consts : ∀ a, constBytes a → S a
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0

/-- The loop's context. -/
theorem DivCtx.dv {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp q W : Nat}
    (cx : DivCtx S R0 sp q W) : DvCtx S sp W := ⟨cx.frame, cx.above, cx.big⟩

/-- `bc_divide`'s continuations for the quotient `n` (`none`: division by
zero): the new number in the slot and `a0 = 0`; `a0 = -1` with only the
window changed; or `out_of_memory`. -/
structure DivKW (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (L1 L2 : List NumObj) (x : NumObj) (q sp W : Nat)
    (n : Option Num) : Prop where
  ret : ∀ m, n = some m → ∀ R' Mt' H F L y, Keeps binClob R' R0 → R' 10 = 0#64 →
    BinPostW S Mt0 Mt' H F L1 L2 x q sp W m L y → DW live S Q (R0 1) R' Mt'
  zero : n = none → ∀ R' Mt', Keeps binClob R' R0 → R' 10 = 0xffffffffffffffff#64 →
    (∀ a, ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) → DW live S Q (R0 1) R' Mt'
  oom : ∀ R' Mt' sp', sp - W ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
    (∀ a, OutHeap a → ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) →
    DW live S Q 0x80002bcc#64 R' Mt'

/-- The epilogue's second half from `0x80005b5c`: `s7`–`s11` back, `ret`. -/
theorem dvt_epi2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 L : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (sv : SavedWords M (sp - 208) divSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 208))
    (h1 : R 1 = R0 1) (h8 : R 8 = R0 8) (h9 : R 9 = R0 9) (h18 : R 18 = R0 18)
    (h19 : R 19 = R0 19) (h20 : R 20 = R0 20) (h21 : R 21 = R0 21) (h22 : R 22 = R0 22)
    (h10 : R 10 = 0#64) (hkp : Keeps divAll R R0) (hS : HeapOwn S)
    (hp : BinPostW S Mt0 M H F L1 L2 xr q sp W m L y) :
    DW live S Q 0x80005b5c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hal := cx.al
  have g23 := sv.get 23 136; have g24 := sv.get 24 128; have g25 := sv.get 25 120
  have g26 := sv.get 26 112; have g27 := sv.get 27 104
  bc_run hlive hS [h1, h2, g23, g24, g25, g26, g27]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk.ret m hn _ _ H F L y (Keeps.unwind
    (saved := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp)) (by bsimp [h10]) hp
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, h1, h8, h9, h18, h19, h20, h21, h22, g23, g24, g25, g26, g27]
  all_goals (try (congr 1; omega))

/-- The epilogue from `0x80005b38`: `a0 = 0`, `ra`, `s0`–`s6` back. -/
theorem dvt_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 L : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (sv : SavedWords M (sp - 208) divSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 208))
    (hkp : Keeps divAll R R0) (hS : HeapOwn S)
    (hp : BinPostW S Mt0 M H F L1 L2 xr q sp W m L y) :
    DW live S Q 0x80005b38#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have g1 := sv.get 1 200; have g8 := sv.get 8 192; have g9 := sv.get 9 184
  have g18 := sv.get 18 176; have g19 := sv.get 19 168; have g20 := sv.get 20 160
  have g21 := sv.get 21 152; have g22 := sv.get 22 144
  bc_run hlive hS [h2, g1, g8, g9, g18, g19, g20, g21, g22] at 0x80005b5c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact dvt_epi2 hlive cx hk hn sv (by bsimp [h2]) (by bsimp [g1]) (by bsimp [g8])
    (by bsimp [g9]) (by bsimp [g18]) (by bsimp [g19]) (by bsimp [g20]) (by bsimp [g21])
    (by bsimp [g22]) (by bsimp []) (by keeps_tac hkp) hS hp

/-- **`free` of a raw buffer keeps the result**: the heap by
`BcHeap.freeRaw`, the slot and the bytes off the heap by the frame. -/
theorem BinPostW.freeRaw {S : Nat → Prop} {Mt0 M M' : Mem} {H H' : Heap} {F : List Blk}
    {L1 L2 L : List NumObj} {x y : NumObj} {q sp W : Nat} {n : Num} {lpre lpost : List Blk}
    {b : Blk} (hp : BinPostW S Mt0 M H F L1 L2 x q sp W n L y)
    (hout : ∀ a, slotBytes q a → OutHeap a)
    (hl : H.live = lpre ++ b :: lpost) (hno : b ∉ F ++ objBlocks (y :: L))
    (hf : FreePost S M M' H H' b lpre lpost) :
    BinPostW S Mt0 M' H' F L1 L2 x q sp W n L y where
  heap := hp.heap.freeRaw hl hno hf
  rest := hp.rest
  num := hp.num
  norm := hp.norm
  pos := hp.pos
  refs := hp.refs
  owns := hp.owns
  slot := by
    rw [ldv_congr .ld fun j hj => hf.frame _ (OutHeap.not_alloc hp.heap.heap
      (hout _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩))]
    exact hp.slot
  out := fun a ha hs hfr => (hf.frame a (OutHeap.not_alloc hp.heap.heap ha)).trans (hp.out a ha hs hfr)

/-- **A `free` call on a raw buffer** with the result in hand: the
continuation gets the result at the new allocator state, the frame off the
allocator's bytes, and the other live blocks. -/
theorem dvt_free {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L1 L2 L : List NumObj}
    {x y : NumObj} {q sp W : Nat} {n : Num} {b : Blk}
    (hp : BinPostW S Mt0 M H F L1 L2 x q sp W n L y) (hout : ∀ a, slotBytes q a → OutHeap a)
    (hb : b ∈ H.live) (hno : b ∉ F ++ objBlocks (y :: L))
    (h10 : R 10 = BitVec.ofNat 64 b.pay) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H', Keeps [14, 15] R' R → BinPostW S Mt0 M' H' F L1 L2 x q sp W n L y →
      (∀ a, ¬ AllocByte H a → imgM M' a = imgM M a) → (∀ c ∈ H.live, c ≠ b → c ∈ H'.live) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80000a0c#64 R M := by
  obtain ⟨lpre, lpost, hl⟩ := List.append_of_mem hb
  refine free_spec hlive hp.heap.heap hl R h10 hal fun R' M' hk' hf => ?_
  refine hk R' M' _ hk' (hp.freeRaw hout hl hno hf) hf.frame fun c hc hne => ?_
  rw [hf.live]
  rw [hl] at hc
  rcases List.mem_append.mp hc with h | h
  · exact List.mem_append_left _ h
  · rcases List.mem_cons.mp h with h' | h'
    · exact absurd h' hne
    · exact List.mem_append_right _ h'

/-- A stack byte above the heap is off the allocator. -/
theorem DivCtx.stack_out {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp q W : Nat}
    (cx : DivCtx S R0 sp q W) {a : Nat} (ha : sp - W ≤ a) : OutHeap a := by
  have hab := cx.above; have hsl := cx.frame.lo
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hab ⊢
  simp only [tohostAddr] at hsl
  omega

/-- The three raw buffers after the result: live, none of the heap's, apart. -/
structure DvRaw (H : Heap) (F : List Blk) (L : List NumObj) (b1 b2 b3 : Blk) : Prop where
  l1 : b1 ∈ H.live
  l2 : b2 ∈ H.live
  l3 : b3 ∈ H.live
  n1 : b1 ∉ F ++ objBlocks L
  n2 : b2 ∉ F ++ objBlocks L
  n3 : b3 ∉ F ++ objBlocks L
  d12 : b1 ≠ b2
  d13 : b1 ≠ b3
  d23 : b2 ≠ b3

/-- **The frees** from `0x80005b1c`: the quotient into the slot, then
`free (mval)`, `free (num1)`, `free (num2)`, the epilogue. -/
theorem dvt_frees {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 L : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num} {b1 b2 b3 : Blk}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (sv : SavedWords M (sp - 208) divSlots R0) (s8 : ldv .ld M (sp - 208 + 8) = BitVec.ofNat 64 b3.pay)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h21 : R 21 = BitVec.ofNat 64 y.sb.pay)
    (h22 : R 22 = BitVec.ofNat 64 q) (h18 : R 18 = BitVec.ofNat 64 b1.pay)
    (h19 : R 19 = BitVec.ofNat 64 b2.pay) (hkp : Keeps divAll R R0)
    (hraw : DvRaw H F (y :: L) b1 b2 b3)
    (hp : BinPostW S Mt0 (writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)]) H F L1 L2 xr q sp W m L y) :
    DW live S Q 0x80005b1c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hap := cx.slotApart
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hp.heap.heap.own a h1 h2
  have hout := cx.slotOut
  have sv0 := sv.transport (lo := 104) (top := 208)
    (M' := writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)])
    (hag := fun a h1 h2' => imgM_store_miss _ _ (by omega))
  bc_run hlive hS [h2, s8, h21, h22] at 0x80005b24
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hq.acc | skip
  apply st_80005b24 hlive
  refine dvt_free hlive hp hout hraw.l3 hraw.n3 (by bsimp []) (by bsimp [])
    fun R1 M1 H1 hk1 hp1 hfr1 hlv1 => ?_
  bsimp []
  have sv1 := sv0.transport (lo := 104) (top := 208) (M' := M1)
    (hag := fun a h1 h2' => hfr1 a (OutHeap.not_alloc hp.heap.heap (cx.stack_out (by omega))))
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk1.get 2]; bsimp [h2]
  have q18 : R1 18 = BitVec.ofNat 64 b1.pay := by rw [hk1.get 18]; bsimp [h18]
  have q19 : R1 19 = BitVec.ofNat 64 b2.pay := by rw [hk1.get 19]; bsimp [h19]
  bc_run hlive hS [q18] at 0x80005b2c
  apply st_80005b2c hlive
  have hS1 : HeapOwn S := fun a h1 h2 => hp1.heap.heap.own a h1 h2
  refine dvt_free hlive hp1 hout (hlv1 _ hraw.l1 hraw.d13) hraw.n1 (by bsimp []) (by bsimp [])
    fun R2 M2 H2 hk2 hp2 hfr2 hlv2 => ?_
  bsimp []
  have sv2 := sv1.transport (lo := 104) (top := 208) (M' := M2)
    (hag := fun a h1 h2' => hfr2 a (OutHeap.not_alloc hp1.heap.heap (cx.stack_out (by omega))))
  have r19 : R2 19 = BitVec.ofNat 64 b2.pay := by rw [hk2.get 19]; bsimp [q19]
  bc_run hlive hS1 [r19] at 0x80005b34
  apply st_80005b34 hlive
  have hS2 : HeapOwn S := fun a h1 h2 => hp2.heap.heap.own a h1 h2
  refine dvt_free hlive hp2 hout (hlv2 _ (hlv1 _ hraw.l2 hraw.d23) (Ne.symm hraw.d12)) hraw.n2
    (by bsimp []) (by bsimp []) fun R3 M3 H3 hk3 hp3 hfr3 _ => ?_
  bsimp []
  have sv3 := sv2.transport (lo := 104) (top := 208) (M' := M3)
    (hag := fun a h1 h2' => hfr3 a (OutHeap.not_alloc hp2.heap.heap (cx.stack_out (by omega))))
  have hS3 : HeapOwn S := fun a h1 h2 => hp3.heap.heap.own a h1 h2
  exact dvt_epi hlive cx hk hn sv3 (by rw [hk3.get 2]; bsimp [hk2.get 2, q2])
    ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac
      ((hk1.mono (by decide)).trans (by keeps_tac hkp)))))) hS3 hp3

/-- A block outside `L1 ++ x :: L2`'s objects is outside `L1 ++ x' :: L2`'s
when `x'` has `x`'s blocks, and outside `L1 ++ L2`'s. -/
theorem not_objBlocks_mid {L1 L2 : List NumObj} {x x' : NumObj} {F : List Blk} {b : Blk}
    (hx : x'.blocks = x.blocks) (h : b ∉ F ++ objBlocks (L1 ++ x :: L2)) :
    b ∉ F ++ objBlocks (L1 ++ x' :: L2) := by
  simp only [objBlocks_append, objBlocks_cons, hx] at h ⊢; exact h

theorem not_objBlocks_drop {L1 L2 : List NumObj} {x : NumObj} {F : List Blk} {b : Blk}
    (h : b ∉ F ++ objBlocks (L1 ++ x :: L2)) : b ∉ x.sb :: F ++ objBlocks (L1 ++ L2) := by
  intro hb
  apply h
  simp only [objBlocks_append, objBlocks_cons, List.mem_append, List.mem_cons] at hb ⊢
  rcases hb with (hb | hb) | hb | hb
  · exact .inr (.inr (.inl (by rw [hb]; exact x.sb_mem_blocks)))
  · exact .inl hb
  · exact .inr (.inl hb)
  · exact .inr (.inr (.inr hb))

/-- The raw buffers after `bc_free_num` lowered `x`'s count. -/
theorem DvRaw.dec {H : Heap} {F : List Blk} {L1 L2 : List NumObj} {x y : NumObj} {b1 b2 b3 : Blk}
    (h : DvRaw H F (y :: (L1 ++ x :: L2)) b1 b2 b3) :
    DvRaw H F (y :: (L1 ++ x.decRef :: L2)) b1 b2 b3 := by
  have e : ∀ b, b ∉ F ++ objBlocks (y :: (L1 ++ x :: L2)) →
      b ∉ F ++ objBlocks (y :: (L1 ++ x.decRef :: L2)) := fun b hb => by
    rw [← List.cons_append] at hb ⊢; exact not_objBlocks_mid (x := x) (x' := x.decRef) rfl hb
  exact ⟨h.l1, h.l2, h.l3, e _ h.n1, e _ h.n2, e _ h.n3, h.d12, h.d13, h.d23⟩

/-- The raw buffers after `bc_free_num` released `x`. -/
theorem DvRaw.rel {S : Nat → Prop} {Mt Mt' : Mem} {H H' : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x y : NumObj} {q sp : Nat} {b1 b2 b3 : Blk}
    (h : DvRaw H F (y :: (L1 ++ x :: L2)) b1 b2 b3)
    (hrp : ReleasePost S Mt Mt' H H' F (y :: L1) L2 x q sp) :
    DvRaw H' (x.sb :: F) (y :: (L1 ++ L2)) b1 b2 b3 := by
  have hl : ∀ b, b ∈ H.live → b ∉ F ++ objBlocks (y :: (L1 ++ x :: L2)) → b ∈ H'.live := by
    intro b hb hn
    by_cases ho : x.Owns
    · refine ((hrp.owned ho).2.1 b).mpr ⟨hb, fun e => hn ?_⟩
      rw [e]
      exact List.mem_append_right _ (mem_objBlocks_db (L := y :: (L1 ++ x :: L2))
        (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)) ho)
    · rw [hrp.view ho]; exact hb
  have e : ∀ b, b ∉ F ++ objBlocks (y :: (L1 ++ x :: L2)) →
      b ∉ x.sb :: F ++ objBlocks (y :: (L1 ++ L2)) := fun b hb => by
    rw [← List.cons_append] at hb ⊢; exact not_objBlocks_drop hb
  exact ⟨hl _ h.l1 h.n1, hl _ h.l2 h.n2, hl _ h.l3 h.n3, e _ h.n1, e _ h.n2, e _ h.n3,
    h.d12, h.d13, h.d23⟩

/-- **`bc_free_num (quot)`** at `0x80005b14`, then the frees. -/
theorem dvt_freenum {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num} {b1 b2 b3 : Blk}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (sv : SavedWords M (sp - 208) divSlots R0) (s8 : ldv .ld M (sp - 208 + 8) = BitVec.ofNat 64 b3.pay)
    (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2))) (hr : ResSlot M L1 xr q)
    (hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hnum : y.rep.num = m) (hnorm : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1)
    (hyo : y.Owns) (hraw : DvRaw H F (y :: (L1 ++ xr :: L2)) b1 b2 b3)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h21 : R 21 = BitVec.ofNat 64 y.sb.pay)
    (h22 : R 22 = BitVec.ofNat 64 q) (h18 : R 18 = BitVec.ofNat 64 b1.pay)
    (h19 : R 19 = BitVec.ofNat 64 b2.pay) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005b14#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hap := cx.slotApart
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hxn := hb.nums xr (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have hxp : heapStart ≤ xr.rep.p ∧ xr.rep.p + 16 ≤ heapEnd :=
    ⟨hxn.shape.pLo, by have := hxn.shape.pHi; omega⟩
  bc_run hlive hS [h22, h2] at 0x800048c0
  have hsf' : StackFrame S (sp - 208) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  have e : FreeEntry S M H F (y :: L1) L2 xr q (sp - 208) :=
    FreeEntry.of_slot hb hr (hr.noView_cons hb hyo) hq cx.slotOut hsf' (by simp only [heapEnd]; omega)
      (by omega)
  have hst : ∀ {M' : Mem}, (∀ a, sp - 208 ≤ a → a < sp → imgM M' a = imgM M a) →
      SavedWords M' (sp - 208) divSlots R0 ∧ ldv .ld M' (sp - 208 + 8) = BitVec.ofNat 64 b3.pay :=
    fun hag => ⟨sv.transport (lo := 104) (top := 208) (hag := fun a h1 h2' => hag a (by omega) (by omega)),
      by rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact s8⟩
  refine bc_free_num_spec hlive e _ (by bsimp [h22]) (by bsimp [h2]) (by bsimp [])
    ⟨fun hx2 R1 Mt1 hk1 hb1 _ hmo => ?_, fun hx1 R1 Mt1 H1 hk1 hrp => ?_⟩
  · bsimp []
    obtain ⟨sv1, s81⟩ := hst (M' := Mt1) fun a h1 h2' => hmo a fun hc => by
      rcases hc with hc | hc
      · simp only [refsBytes, heapStart, heapEnd] at hc hxp; omega
      · simp only [slotBytes] at hc; omega
    exact dvt_frees hlive cx hk hn sv1 s81 (by rw [hk1.get 2]; bsimp [h2])
      (by rw [hk1.get 21]; bsimp [h21]) (by rw [hk1.get 22]; bsimp [h22])
      (by rw [hk1.get 18]; bsimp [h18]) (by rw [hk1.get 19]; bsimp [h19])
      ((hk1.mono (by decide)).trans (by keeps_tac hkp)) hraw.dec
      (binPost_dec cx.slotOut hout hb1 hmo hxp hnum hnorm hpos hrefs hyo hx2)
  · bsimp []
    obtain ⟨sv1, s81⟩ := hst (M' := Mt1) fun a h1 h2' => hrp.frame a fun hc => by
      have hout' : OutHeap a := cx.stack_out (by omega)
      rcases hc with hc | hc | hc | hc | hc
      · exact OutHeap.not_alloc hb.heap hout' hc
      · exact hout'.1 (live_in_heap hb.heap (hb.blocks xr (List.mem_cons_of_mem _
          (List.mem_append_right _ List.mem_cons_self))).sLive hc)
      · simp only [slotBytes] at hc; omega
      · simp only [frameIn] at hc; omega
      · exact hout'.2.2 hc
    exact dvt_frees hlive cx hk hn sv1 s81 (by rw [hk1.get 2]; bsimp [h2])
      (by rw [hk1.get 21]; bsimp [h21]) (by rw [hk1.get 22]; bsimp [h22])
      (by rw [hk1.get 18]; bsimp [h18]) (by rw [hk1.get 19]; bsimp [h19])
      ((hk1.mono (by decide)).trans (by keeps_tac hkp)) (hraw.rel hrp)
      (binPost_rel cx.slotOut hout hb hrp cx.above ⟨by omega, by omega⟩ hnum hnorm hpos hrefs hyo hx1)

end

end Dc.Mach
