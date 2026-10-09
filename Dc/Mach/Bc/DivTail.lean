import Dc.Mach.Bc.DivMain
import Dc.Mach.Bc.AddSub
import Dc.Mach.Bc.Init
import Dc.Mach.Bc.HeapNe

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


/-! ## The quotient's leading-zero trim, inlined (`0x80005ae4`) -/

/-- The trim loop at `0x80005b0c` (rotated: `n_value` advanced first, the
stores after the length test): `j` leading zeros dropped from the object in
`s5`, digit `j` zero too. -/
theorem dvtrim_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt : Mem} {Rb : Nat → BitVec 64} {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} (hS : HeapOwn S) (hr : Rb 21 = BitVec.ofNat 64 x.rep.p)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem) (j : Nat), Keeps [11, 13, 14, 15] R' Rb →
      BcHeap S M' H F (L1 ++ { x with rep := x.rep.drop j } :: L2) →
      lzCount (x.rep.len - 1) x.rep.ds = j →
      MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M' Mt →
      DW live S Q 0x80005b14#64 R' M') :
    ∀ n j (R : Nat → BitVec 64) (M : Mem), x.rep.len - 1 - j = n → j < x.rep.len →
      Keeps [11, 13, 14, 15] R Rb →
      BcHeap S M H F (L1 ++ { x with rep := x.rep.drop j } :: L2) →
      MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M Mt →
      R 15 = BitVec.ofNat 64 (x.rep.val + j) → R 13 = BitVec.ofNat 64 (x.rep.len - j) →
      R 11 = BitVec.ofNat 64 1 → (∀ i, i ≤ j → x.rep.ds.getD i 0 = 0) →
      DW live S Q 0x80005b0c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro n
  induction n with
  | zero =>
    intro j R M hn hj kk hb hmo h15 h13 h11 hz
    have hn0 := hb.nums _ (List.mem_append_right _ List.mem_cons_self)
    num_facts hn0
    have v5 := hn0.shape.vHi; have v7 := hn0.shape.size
    have v8 : 1 ≤ x.rep.len := by omega
    have v9 := hn0.shape.vLo; have v6 := hn0.shape.ptrLe
    have vl := hn0.shape.dsLen
    simp only [NumRep.drop, List.length_drop, heapEnd, heapStart] at v5 v7 v8 v9 v6 vl
    bc_run hlive hS [h15, h13, h11, toInt_ofNat_small] at 0x80005b14 0x80005af8
    · intro hc; exfalso; omega
    · intro _
      exact hnext _ _ j (by keeps_tac kk) hb
        (lzCount_eq _ _ _ (by omega) (by omega) (fun i hi => hz i (by omega)) (.inl (by omega))) hmo
  | succ n ih =>
    intro j R M hn hj kk hb hmo h15 h13 h11 hz
    have hn0 := hb.nums _ (List.mem_append_right _ List.mem_cons_self)
    num_facts hn0
    have v5 := hn0.shape.vHi; have v7 := hn0.shape.size
    have v8 : 1 ≤ x.rep.len := by omega
    have v9 := hn0.shape.vLo; have v6 := hn0.shape.ptrLe
    have vl := hn0.shape.dsLen
    simp only [NumRep.drop, List.length_drop, heapEnd, heapStart] at v5 v7 v8 v9 v6 vl
    have hrr : R 21 = BitVec.ofNat 64 x.rep.p := by rw [kk.get 21 (by decide)]; exact hr
    have hpl := hn0.shape.pLo; have hph := hn0.shape.pHi
    simp only [NumRep.drop, heapStart, heapEnd] at hpl hph
    bc_run hlive hS [h15, h13, h11, toInt_ofNat_small] at 0x80005b14 0x80005af8
    · intro hc
      have hb' := hb.advanceAt (v1 := BitVec.ofNat 64 (x.rep.len - j - 1))
        (v2 := BitVec.ofNat 64 (x.rep.val + j + 1)) (by simp only [NumRep.drop]; omega)
        (by simp only [NumRep.drop]; rw [toNat_ofNat_mod32 (by omega)])
        (by simp only [NumRep.drop])
      simp only [NumRep.drop_drop] at hb'
      have hp' : ({ x with rep := x.rep.drop j } : NumObj).rep.p = x.rep.p := rfl
      rw [hp'] at hb'
      have hmo' : MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd)
          (writeLog (writeLog M [(x.rep.p + 4, 4, BitVec.ofNat 64 (x.rep.len - j - 1))])
            [(x.rep.p + 32, 8, BitVec.ofNat 64 (x.rep.val + j + 1))]) Mt := fun a ha => by
        rw [imgM_store_miss _ _ (by simp only [heapStart, heapEnd] at ha; omega),
          imgM_store_miss _ _ (by simp only [heapStart, heapEnd] at ha; omega)]
        exact hmo a ha
      have hn1 := hb'.nums _ (List.mem_append_right _ List.mem_cons_self)
      have hl1 := hn1.lbu (i := 0) (by simp only [NumRep.drop]; omega)
      simp only [NumRep.drop, Nat.add_zero, List.getD_eq_getElem?_getD, List.getElem?_drop,
        ← Nat.add_assoc] at hl1
      have hd := hn1.getD_lt 0
      simp only [NumRep.drop, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero] at hd
      bc_run hlive hS [h15, h13, h11, hrr] at 0x80005b04
      bc_run hlive hS [h11, hl1] at 0x80005b14 0x80005b0c
      · intro hne
        bv_nat at hne
        rw [Nat.mod_eq_of_lt (by omega)] at hne
        exact hnext _ _ (j + 1) (by keeps_tac kk) hb'
          (lzCount_eq _ _ _ (by omega) (by omega) (fun i hi => by
              rcases Nat.lt_or_ge i (j + 1) with h | h
              · exact hz i (by omega)
              · rw [show i = j by omega]; exact hz j (by omega))
            (.inr (by rw [List.getD_eq_getElem?_getD]; exact hne))) hmo'
      · intro he
        bv_nat at he
        rw [Classical.not_not, Nat.mod_eq_of_lt (by omega)] at he
        refine ih (j + 1) _ _ (by omega) (by omega) (by keeps_tac kk) hb' hmo'
          (by bsimp [Nat.add_assoc]) (by bsimp [Nat.sub_sub]) (by bsimp [h11]) fun i hi => ?_
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hz i (by omega)
        · rw [show i = j + 1 by omega, List.getD_eq_getElem?_getD]; exact he
    · intro hc; exfalso; omega


/-- **The quotient's leading-zero trim at `0x80005ae4`** (`a5 = n_value`,
the struct in `s5`): `NumRep.rmLeadingZeros` as `drop j`. -/
theorem dvtrim {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} (hb : BcHeap S M H F (L1 ++ x :: L2)) (hr : R 21 = BitVec.ofNat 64 x.rep.p)
    (h15 : R 15 = BitVec.ofNat 64 x.rep.val) (hpos : 1 ≤ x.rep.len)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem) (j : Nat), Keeps [11, 13, 14, 15] R' R →
      BcHeap S M' H F (L1 ++ { x with rep := x.rep.drop j } :: L2) →
      lzCount (x.rep.len - 1) x.rep.ds = j →
      MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M' M →
      DW live S Q 0x80005b14#64 R' M') :
    DW live S Q 0x80005ae4#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hb0 : BcHeap S M H F (L1 ++ { x with rep := x.rep.drop 0 } :: L2) := by
    rw [NumRep.drop_zero]; exact hb
  have hn := hb.nums _ (List.mem_append_right _ List.mem_cons_self)
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  num_facts hn
  have hlen := hn.len
  have hmo0 : MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M M := fun a _ => rfl
  have vl := hn.shape.dsLen
  have hl0 := hn.lbu (i := 0) (by omega)
  have hd := hn.getD_lt 0
  simp only [Nat.add_zero] at hl0 hd
  bc_run hlive hS [hr, h15, hl0] at 0x80005b14 0x80005aec
  · intro hne
    bv_nat at hne
    rw [Nat.mod_eq_of_lt (by omega)] at hne
    exact hnext _ _ 0 (by keeps_tac Keeps.refl _ _) hb0
      (lzCount_eq _ _ _ (by omega) (by omega) (fun i hi => absurd hi (by omega)) (.inr hne)) hmo0
  · intro he
    bv_nat at he
    rw [Classical.not_not, Nat.mod_eq_of_lt (by omega)] at he
    bc_run hlive hS [hr, h15, hlen] at 0x80005b0c
    exact dvtrim_loop hlive hS hr hnext _ 0 _ _ rfl (by omega)
      (by keeps_tac Keeps.refl _ _) hb0 hmo0 (by bsimp [h15]) (by bsimp []) (by bsimp [])
      fun i hi => by rw [show i = 0 by omega]; exact he


/-! ## From the sign store to `bc_free_num (quot)` -/

/-- Inside `bc_divide`'s tail: `sp` lowered by 208, the saved registers and
the product buffer's pointer in the frame, the slot holding the old result,
off the heap only the slot and the window changed, the raw buffers' pointers
in `s2`/`s3`, the slot pointer in `s6`. -/
structure DvtAt (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W : Nat)
    (L1 : List NumObj) (xr : NumObj) (b1 b2 b3 : Blk) : Prop where
  saved : SavedWords M (sp - 208) divSlots R0
  s8 : ldv .ld M (sp - 208 + 8) = BitVec.ofNat 64 b3.pay
  slot : ResSlot M L1 xr q
  out : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a
  r2 : R 2 = BitVec.ofNat 64 (sp - 208)
  r22 : R 22 = BitVec.ofNat 64 q
  r18 : R 18 = BitVec.ofNat 64 b1.pay
  r19 : R 19 = BitVec.ofNat 64 b2.pay
  regs : Keeps divAll R R0

/-- `DvtAt` through changes of the argument registers. -/
theorem DvtAt.keeps {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp q W : Nat}
    {L1 : List NumObj} {xr : NumObj} {b1 b2 b3 : Blk}
    (st : DvtAt S Mt0 M R0 R sp q W L1 xr b1 b2 b3) (hk : Keeps [10, 11, 12, 13, 14, 15] R' R) :
    DvtAt S Mt0 M R0 R' sp q W L1 xr b1 b2 b3 :=
  { st with
    r2 := by rw [hk.get 2]; exact st.r2
    r22 := by rw [hk.get 22]; exact st.r22
    r18 := by rw [hk.get 18]; exact st.r18
    r19 := by rw [hk.get 19]; exact st.r19
    regs := (hk.mono (by decide)).trans st.regs }

/-- `DvtAt` through changes on the heap. -/
theorem DvtAt.heap {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    {L1 : List NumObj} {xr : NumObj} {b1 b2 b3 : Blk} (cx : DivCtx S R0 sp q W)
    (st : DvtAt S Mt0 M R0 R sp q W L1 xr b1 b2 b3)
    (hmo : MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M' M) :
    DvtAt S Mt0 M' R0 R sp q W L1 xr b1 b2 b3 := by
  have hab := cx.above; have hW := cx.big
  have hst : ∀ a, sp - 208 ≤ a → imgM M' a = imgM M a := fun a h => hmo a fun h' => by
    simp only [heapStart, heapEnd] at h' hab; omega
  have hq : ∀ a, slotBytes q a → imgM M' a = imgM M a := fun a h => hmo a (cx.slotOut a h).1
  refine ⟨st.saved.transport (lo := 104) (top := 208) (hag := fun a h1 _ => hst a (by omega)),
    ?_, ⟨st.slot.refs, ?_, st.slot.noView⟩, fun a ha h1 h2 => (hmo a ha.1).trans (st.out a ha h1 h2),
    st.r2, st.r22, st.r18, st.r19, st.regs⟩
  · rw [ldv_congr .ld fun j hj => hst _ (by omega)]; exact st.s8
  · rw [ldv_congr .ld fun j hj => hq _ (by simp only [slotBytes, widthOfM] at hj ⊢; omega)]
    exact st.slot.word

/-- The raw buffers with the head relabelled on the same blocks. -/
theorem DvRaw.head {H : Heap} {F : List Blk} {L : List NumObj} {y y' : NumObj} {b1 b2 b3 : Blk}
    (h : DvRaw H F (y :: L) b1 b2 b3) (hx : y'.blocks = y.blocks) : DvRaw H F (y' :: L) b1 b2 b3 := by
  have e : ∀ b, b ∉ F ++ objBlocks (y :: L) → b ∉ F ++ objBlocks (y' :: L) := fun b hb => by
    simpa only [objBlocks_cons, hx] using hb
  exact ⟨h.l1, h.l2, h.l3, e _ h.n1, e _ h.n2, e _ h.n3, h.d12, h.d13, h.d23⟩

/-- After the trim, at `0x80005b14`: `j` leading zeros dropped. -/
theorem dvt_trimmed {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W j : Nat} {L1 L2 : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num} {b1 b2 b3 : Blk}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (st : DvtAt S Mt0 M R0 R sp q W L1 xr b1 b2 b3)
    (hb : BcHeap S M H F ({ y with rep := y.rep.drop j } :: (L1 ++ xr :: L2)))
    (hj : lzCount (y.rep.len - 1) y.rep.ds = j) (hnum : y.rep.num = m)
    (hdl : y.rep.ds.length = y.rep.len + y.rep.scale) (hpos : 1 ≤ y.rep.len)
    (hrefs : y.rep.refs = 1) (hyo : y.Owns) (hraw : DvRaw H F (y :: (L1 ++ xr :: L2)) b1 b2 b3)
    (h21 : R 21 = BitVec.ofNat 64 y.sb.pay) :
    DW live S Q 0x80005b14#64 R M := by
  obtain ⟨hn', hnorm, -, hpos'⟩ := NumRep.rmLeadingZeros_spec hdl hpos
  have e : y.rep.rmLeadingZeros = y.rep.drop j := by rw [NumRep.rmLeadingZeros, hj]
  rw [e] at hn' hnorm hpos'
  exact dvt_freenum (y := { y with rep := y.rep.drop j }) hlive cx hk hn st.saved st.s8 hb st.slot
    st.out (hn'.trans hnum) hnorm hpos' hrefs hyo (hraw.head rfl) st.r2 h21 st.r22 st.r18 st.r19
    st.regs

/-- The trim from `0x80005ae4`, then `bc_free_num (quot)`. -/
theorem dvt_trim {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num} {b1 b2 b3 : Blk}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (st : DvtAt S Mt0 M R0 R sp q W L1 xr b1 b2 b3)
    (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2))) (hnum : y.rep.num = m)
    (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns)
    (hraw : DvRaw H F (y :: (L1 ++ xr :: L2)) b1 b2 b3)
    (h21 : R 21 = BitVec.ofNat 64 y.sb.pay) (h15 : R 15 = BitVec.ofNat 64 y.rep.val) :
    DW live S Q 0x80005ae4#64 R M := by
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hdl := (hb.nums y List.mem_cons_self).shape.dsLen
  have hb0 : BcHeap S M H F ([] ++ y :: (L1 ++ xr :: L2)) := hb
  refine dvtrim hlive hb0 (by rw [h21, hyp]) h15 hpos fun R' M' j kk hb' hj hmo => ?_
  have h21' : R' 21 = BitVec.ofNat 64 y.sb.pay := by rw [kk.get 21 (by decide)]; exact h21
  exact dvt_trimmed hlive cx hk hn ((st.heap cx hmo).keeps (kk.mono (by decide))) hb' hj hnum hdl hpos
    hrefs hyo hraw h21'


/-- A zero quotient made positive at `0x80005b8c`, then the trim. -/
theorem dvt_pos {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num} {b1 b2 b3 : Blk}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (st : DvtAt S Mt0 M R0 R sp q W L1 xr b1 b2 b3)
    (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hnum : ({ y.rep with neg := false } : NumRep).num = m)
    (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns)
    (hraw : DvRaw H F (y :: (L1 ++ xr :: L2)) b1 b2 b3)
    (h21 : R 21 = BitVec.ofNat 64 y.sb.pay) (h15 : R 15 = BitVec.ofNat 64 y.rep.val) :
    DW live S Q 0x80005b8c#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hys := (hb.nums y List.mem_cons_self).shape
  have yp1 := hys.pLo; have yp2 := hys.pHi; have yp3 := hys.pAl
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  simp only [heapStart, heapEnd] at yp1 yp2
  have hb' := BcHeap.setSign (L1 := []) hb (v := 0#64) false (by decide)
  rw [hyp] at hb'
  simp only [List.nil_append] at hb'
  rw [hyp] at yp1 yp2 yp3
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h21] at 0x80005ae4
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  exact dvt_trim (y := { y with rep := { y.rep with neg := false } }) hlive cx hk hn
    (st.heap cx fun a ha => imgM_store_miss _ _ (by simp only [heapStart, heapEnd] at ha; omega))
    hb' hnum hpos hrefs hyo (hraw.head rfl) (by bsimp [h21]) (by bsimp [h15])

/-- The inlined `bc_is_zero (qval)` scan at `0x80005ad4`: the first `i`
digits zero, `k + 1` left, `a3` at digit `i`. All digits zero reach
`0x80005b8c`; a nonzero digit `0x80005ae4`. -/
theorem dvt_scan {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {o : NumRep} {Rb : Nat → BitVec 64} (hS : HeapOwn S) (hn : NumAt M o)
    (hz : ∀ R', Keeps [12, 13, 14] R' Rb → (∀ j, j < o.len + o.scale → o.ds.getD j 0 = 0) →
      DW live S Q 0x80005b8c#64 R' M)
    (hnz : ∀ R', Keeps [12, 13, 14] R' Rb → dval o.ds ≠ 0 → DW live S Q 0x80005ae4#64 R' M) :
    ∀ k i (R : Nat → BitVec 64), o.len + o.scale = i + k + 1 → (∀ j, j < i → o.ds.getD j 0 = 0) →
      Keeps [12, 13, 14] R Rb → R 12 = BitVec.ofNat 64 (k + 1) →
      R 13 = BitVec.ofNat 64 (o.val + i) → DW live S Q 0x80005ad4#64 R M := by
  num_facts hn
  have hdl := hn.shape.dsLen
  have hnz' : ∀ i, i < o.len + o.scale → o.ds.getD i 0 ≠ 0 → dval o.ds ≠ 0 := fun i hi hne e =>
    hne ((dval_eq_zero_iff _).1 e i (by omega))
  intro k
  induction k with
  | zero =>
    intro i R hi hz0 kk hc hp
    have hl := hn.lbu (i := i) (by omega)
    have hd := hn.getD_lt i
    bc_run hlive hS [hc, hp, hl] at 0x80005ad0 0x80005ae4
    all_goals first | exact acc_heap hS (by omega) (by omega) | skip
    · intro h0
      bsimp [ofNat_eq_zero_iff (show o.ds.getD i 0 < 2 ^ 64 by omega)] at h0
      bc_run hlive hS [hc, hp] at 0x80005b8c 0x80005ad4
      exact hz _ (by keeps_tac kk) fun j hj => by
        rcases Nat.lt_or_ge j i with h1 | h1
        · exact hz0 j h1
        · rw [show j = i by omega]; exact h0
    · intro h0
      bsimp [ofNat_eq_zero_iff (show o.ds.getD i 0 < 2 ^ 64 by omega)] at h0
      exact hnz _ (by keeps_tac kk) (hnz' i (by omega) h0)
  | succ k ih =>
    intro i R hi hz0 kk hc hp
    have hl := hn.lbu (i := i) (by omega)
    have hd := hn.getD_lt i
    bc_run hlive hS [hc, hp, hl] at 0x80005ad0 0x80005ae4
    all_goals first | exact acc_heap hS (by omega) (by omega) | skip
    · intro h0
      bsimp [ofNat_eq_zero_iff (show o.ds.getD i 0 < 2 ^ 64 by omega)] at h0
      bc_run hlive hS [hc, hp] at 0x80005b8c 0x80005ad4
      refine ih (i + 1) _ (by omega) (fun j hj => ?_) (by keeps_tac kk)
        (by bsimp [show k + 1 + 1 - 1 = k + 1 by omega]) (by bsimp [Nat.add_assoc])
      rcases Nat.lt_or_ge j i with h1 | h1
      · exact hz0 j h1
      · rw [show j = i by omega]; exact h0
    · intro h0
      bsimp [ofNat_eq_zero_iff (show o.ds.getD i 0 < 2 ^ 64 by omega)] at h0
      exact hnz _ (by keeps_tac kk) (hnz' i (by omega) h0)


/-- The sign word `snez` leaves. -/
theorem snezWord_toNat (c : Bool) :
    (BitVec.ofNat 64 (if c = true then 1 else 0)).toNat % 2 ^ 32 = c.toNat := by
  cases c <;> decide

/-- The zero test from `0x80005ab4` (the quotient's sign stored): `bc_is_zero
(qval)` from `a3 = n_value`; a zero made positive, then the trim. -/
theorem dvt_test {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num} {b1 b2 b3 : Blk}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (st : DvtAt S Mt0 M R0 R sp q W L1 xr b1 b2 b3)
    (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (h21 : R 21 = BitVec.ofNat 64 y.sb.pay) (h15 : R 15 = BitVec.ofNat 64 y.rep.val)
    (hnum : dval y.rep.ds ≠ 0 → y.rep.num = m)
    (hnum0 : dval y.rep.ds = 0 → ({ y.rep with neg := false } : NumRep).num = m)
    (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns)
    (hraw : DvRaw H F (y :: (L1 ++ xr :: L2)) b1 b2 b3) :
    DW live S Q 0x80005ab4#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hyn := hb.nums y List.mem_cons_self
  num_facts hyn
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hl : ldv .lw M (y.sb.pay + 4) = BitVec.ofNat 64 y.rep.len := by rw [← hyp]; exact hyn.len
  have hs : ldv .lw M (y.sb.pay + 8) = BitVec.ofNat 64 y.rep.scale := by
    rw [← hyp]; exact hyn.scale
  have hdl := hyn.shape.dsLen
  have yp1 := hyn.shape.pLo; have yp2 := hyn.shape.pHi; have yp3 := hyn.shape.pAl
  rw [hyp] at yp1 yp2 yp3
  simp only [heapStart, heapEnd] at yp1 yp2
  bc_run hlive hS [h21, h15, hl, hs,
    addw_ofNat (show y.rep.scale + y.rep.len < 2 ^ 31 by omega)] at 0x80005ad4 0x80005b88
  all_goals try (exact acc_heap hS (by omega) (by omega))
  · intro _
    refine dvt_scan hlive hS hyn (fun R' kk hall => ?_) (fun R' kk hnz => ?_)
      (y.rep.len + y.rep.scale - 1) 0 _ (by omega) (fun j hj => absurd hj (Nat.not_lt_zero _))
      (Keeps.refl _ _) (by bsimp []; congr 1; omega) (by bsimp [])
    · exact dvt_pos hlive cx hk hn (st.keeps ((kk.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
        hb (hnum0 ((dval_eq_zero_iff _).2 fun j hj => hall j (by omega))) hpos hrefs hyo hraw
        (by rw [kk.get 21 (by decide)]; bsimp [h21]) (by rw [kk.get 15 (by decide)]; bsimp [h15])
    · exact dvt_trim hlive cx hk hn (st.keeps ((kk.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
        hb (hnum hnz) hpos hrefs hyo hraw
        (by rw [kk.get 21 (by decide)]; bsimp [h21]) (by rw [kk.get 15 (by decide)]; bsimp [h15])
  · intro hc
    exfalso
    rw [toInt_ofNat_small (show y.rep.scale + y.rep.len < 2 ^ 63 by omega)] at hc
    simp at hc
    omega



/-- **The sign** at `0x80005a90`: `n1.sign != n2.sign` into the quotient
(not `_zero_`), then the zero test. -/
theorem dvt_sign {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr y x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num} {b1 b2 b3 : Blk}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (st : DvtAt S Mt0 M R0 R sp q W L1 xr b1 b2 b3)
    (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hx1 : x1 ∈ L1 ++ xr :: L2) (hx2 : x2 ∈ L1 ++ xr :: L2) (hz : z ∈ L1 ++ xr :: L2)
    (hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h9 : R 9 = BitVec.ofNat 64 x2.rep.p)
    (h21 : R 21 = BitVec.ofNat 64 y.sb.pay)
    (hnum : dval y.rep.ds ≠ 0 → ({ y.rep with neg := x1.rep.neg != x2.rep.neg } : NumRep).num = m)
    (hnum0 : dval y.rep.ds = 0 → ({ y.rep with neg := false } : NumRep).num = m)
    (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns)
    (hraw : DvRaw H F (y :: (L1 ++ xr :: L2)) b1 b2 b3) :
    DW live S Q 0x80005a90#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ hx1)
  num_facts hn1
  have hn2 := hb.nums x2 (List.mem_cons_of_mem _ hx2)
  num_facts hn2
  have hyn := hb.nums y List.mem_cons_self
  num_facts hyn
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hzn := hb.nums z (List.mem_cons_of_mem _ hz)
  num_facts hzn
  have hne := hb.p_ne hz
  rw [hyp] at hne
  have hne' : ¬ BitVec.ofNat 64 z.rep.p = BitVec.ofNat 64 y.sb.pay := fun e =>
    hne ((ofNat_eq_iff (by omega) (by omega)).mp e).symm
  have hval : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by rw [← hyp]; exact hyn.value
  have hzg' : ldv .ld M 2147601864 = BitVec.ofNat 64 z.rep.p := hzg
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hcst : ∀ b ∈ accAddrs 2147601864 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  have yp1 := hyn.shape.pLo; have yp2 := hyn.shape.pHi; have yp3 := hyn.shape.pAl
  rw [hyp] at yp1 yp2 yp3
  simp only [heapStart, heapEnd] at yp1 yp2
  bc_run hlive hS [h8, h9, h21, hn1.sign, hn2.sign, hzg', hval, snez_signs, hne'] at 0x80005ab4
  all_goals try (exact hcst)
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr, zeroAddr] at *; omega)
  have hb' := BcHeap.setSign (L1 := []) hb (x1.rep.neg != x2.rep.neg) (snezWord_toNat _)
  rw [hyp] at hb'
  simp only [List.nil_append] at hb'
  exact dvt_test (y := { y with rep := { y.rep with neg := x1.rep.neg != x2.rep.neg } }) hlive cx hk hn
    ((st.heap cx fun a ha => imgM_store_miss _ _ (by simp only [heapStart, heapEnd] at ha; omega)).keeps
      (by keeps_tac Keeps.refl _ _))
    hb' (by bsimp [h21]) (by bsimp []) hnum hnum0 hpos hrefs hyo (hraw.head rfl)


/-- The slot keeps its word while only the heap and the window change. -/
theorem ResSlot.of_dvFix {S : Nat → Prop} {Mt0 M : Mem} {R0 : Nat → BitVec 64} {sp q W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh L1 : List NumObj} {y x : NumObj} {ds : List Nat}
    (cx : DivCtx S R0 sp q W) (fx : DvFix S Mt0 M R0 sp W D H F Lh y ds)
    (h : ResSlot Mt0 L1 x q) : ResSlot M L1 x q := by
  have hap := cx.slotApart
  refine ⟨h.refs, ?_, h.noView⟩
  rw [ldv_congr .ld fun j hj => fx.out _ (cx.slotOut _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩)
    (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
  exact h.word

/-- **The loop's exit** at `0x80005e2c`: `s5`, `s3`, `s1`, `s0`, `s6` reloaded
(the quotient, `num2`, both operands, the slot), then the sign. -/
theorem dvt_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr y x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num}
    {D : DvData} {ds : List Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (ex : DvExit S Mt0 M R0 R sp W D H F (L1 ++ xr :: L2) y ds)
    (hr0 : ResSlot Mt0 L1 xr q) (hqv : D.qv = y.sb.pay) (hn1 : D.n1p = x1.rep.p)
    (hn2 : D.n2p = x2.rep.p) (hrs : D.rs = q)
    (hx1 : x1 ∈ L1 ++ xr :: L2) (hx2 : x2 ∈ L1 ++ xr :: L2) (hz : z ∈ L1 ++ xr :: L2)
    (hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p)
    (hnum : dval ds ≠ 0 → ({ y.rep with ds := ds, neg := x1.rep.neg != x2.rep.neg } : NumRep).num = m)
    (hnum0 : dval ds = 0 → ({ y.rep with ds := ds, neg := false } : NumRep).num = m)
    (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) :
    DW live S Q 0x80005e2c#64 R M := by
  have fx := ex.fix
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => fx.heap.heap.own a h1 h2
  have h2 := ex.r2
  have s56 := fx.s56; have s64 := fx.s64; have s72 := fx.s72; have s80 := fx.s80; have s88 := fx.s88
  rw [hqv] at s56; rw [hn2] at s72; rw [hn1] at s80; rw [hrs] at s88
  bc_run hlive hS [h2, s56, s64, s72, s80, s88] at 0x80005a90
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dvt_sign (y := withDs y ds) hlive cx hk hn ⟨fx.saved, by rw [fx.s8, fx.mPay],
      ResSlot.of_dvFix cx fx hr0, fun a ha _ hf => fx.out a ha hf, by bsimp [h2], by bsimp [],
      by bsimp [ex.r18, fx.pPay], by bsimp [], ?_⟩
    fx.heap hx1 hx2 hz hzg (by bsimp []) (by bsimp []) (by bsimp []) hnum hnum0 hpos hrefs fx.owns
    (DvRaw.head ⟨fx.b1l, fx.b2l, fx.b3l, fx.b1n, fx.b2n, fx.b3n, fx.b12, fx.b13, fx.b23⟩ rfl)
  exact (by keeps_tac Keeps.refl _ _ : Keeps divAll _ R).trans ex.regs

end

end Dc.Mach
