import Dc.Mach.Bc.RaiseEntry
import Dc.Mach.Bc.Int2Num

/-!
# Callee contexts from a caller's frame

A caller with `sp` lowered by `F` bytes inside its window `W` (`CallerCtx`)
calls the library with `sp - F` and the window `W - F`. The result slot is a
word of the frame (`CallerCtx.slot`) or a slot apart from the window that
the caller was given (`DmSlot.lift`).

- `CallerCtx.mul`, `.bin`, `.div`, `.dm`, `.i2n`, `.ra`: the contexts of
  `bc_multiply`, `bc_add`/`bc_sub`, `bc_divide`, `bc_divmod`, `bc_int2num`,
  `bc_raise`.
- `CallerCtx.oom`: `out_of_memory` from a callee, as the caller's.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A caller's window `W` below `sp`, over the heap. -/
structure CallerCtx (S : Nat → Prop) (sp W : Nat) : Prop where
  frame : StackFrame S sp W
  above : heapEnd + W ≤ sp
  mulBase : ∀ a, mulBaseAddr ≤ a → a < mulBaseAddr + 4 → S a
  consts : ∀ a, constBytes a → S a

/-- The facts of `CallerCtx` as `omega` sees them. -/
macro "cf_facts " cx:term : tactic =>
  `(tactic| (have _hsf := ($cx).frame
             have _hsl := _hsf.lo; have _hsh := _hsf.hi; have _hsa := _hsf.al
             have _hab := ($cx).above
             simp only [heapEnd] at _hab
             have _htx : tohostAddr = 0x8001ad00 := rfl))

/-- The window below the frame. -/
theorem CallerCtx.inner {S : Nat → Prop} {sp W : Nat} (cx : CallerCtx S sp W) {F : Nat}
    (hF : F ≤ W) (h16 : F % 16 = 0) : StackFrame S (sp - F) (W - F) := by
  cf_facts cx
  exact ⟨fun a h1 h2 => cx.frame.own a (by omega) (by omega), by omega, by omega, by omega⟩

/-- A word of the frame (`o + 8 ≤ F`) as a result slot. -/
theorem CallerCtx.slot {S : Nat → Prop} {sp W : Nat} (cx : CallerCtx S sp W) {F o : Nat}
    (hF : F ≤ W) (ho : o + 8 ≤ F) (ho8 : o % 8 = 0) (h16 : F % 16 = 0) :
    DmSlot S (sp - F) (W - F) (sp - F + o) := by
  cf_facts cx
  exact ⟨⟨fun i hi => cx.frame.own _ (by omega) (by omega), by omega, by omega, by omega⟩,
    fun a ha => by simp only [slotBytes] at ha; simp only [OutHeap, heapStart, heapEnd,
      freeListAddr, bcFreeAddr]; omega, .inr (by omega)⟩

/-- A slot apart from the caller's window, for a callee below the frame. -/
theorem DmSlot.lift {S : Nat → Prop} {sp W q F : Nat} (h : DmSlot S sp W q) (hF : F ≤ W) :
    DmSlot S (sp - F) (W - F) q :=
  ⟨h.slot, h.out, by have := h.apart; omega⟩

/-- `bc_multiply`'s context. -/
theorem CallerCtx.mul {S : Nat → Prop} {sp W : Nat} (cx : CallerCtx S sp W) {F q : Nat}
    {R : Nat → BitVec 64} (hF : F + 320 ≤ W) (h16 : F % 16 = 0) (hq : DmSlot S (sp - F) (W - F) q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - F)) (hal : (R 1).toNat % 4 = 0) :
    MulCtx S R (sp - F) q (W - F) := by
  cf_facts cx
  exact ⟨cx.inner (by omega) h16, by simp only [heapEnd]; omega, by omega, hq.slot, hq.out,
    hq.apart, cx.mulBase, cx.consts, h2, hal⟩

/-- `bc_add`'s and `bc_sub`'s context. -/
theorem CallerCtx.bin {S : Nat → Prop} {sp W : Nat} (cx : CallerCtx S sp W) {F q : Nat}
    {R : Nat → BitVec 64} (hF : F + 176 ≤ W) (h16 : F % 16 = 0) (hq : DmSlot S (sp - F) (W - F) q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - F)) (hal : (R 1).toNat % 4 = 0) :
    BinCtx S R (sp - F) q := by
  cf_facts cx
  exact ⟨⟨fun a h1 h2 => cx.frame.own a (by omega) (by omega), by omega, by omega, by omega⟩,
    by simp only [heapEnd]; omega, hq.slot, hq.out, by have := hq.apart; omega, h2, hal⟩

/-- `bc_divide`'s context. -/
theorem CallerCtx.div {S : Nat → Prop} {sp W : Nat} (cx : CallerCtx S sp W) {F q : Nat}
    {R : Nat → BitVec 64} (hF : F + 272 ≤ W) (h16 : F % 16 = 0) (hq : DmSlot S (sp - F) (W - F) q)
    (hz : q + 8 ≤ zeroAddr ∨ zeroAddr + 8 ≤ q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - F)) (hal : (R 1).toNat % 4 = 0) :
    DivCtx S R (sp - F) q (W - F) := by
  cf_facts cx
  exact ⟨cx.inner (by omega) h16, by simp only [heapEnd]; omega, by omega, hq.slot, hq.out,
    hq.apart, hz, cx.consts, h2, hal⟩

/-- `bc_divmod`'s context. -/
theorem CallerCtx.dm {S : Nat → Prop} {sp W : Nat} (cx : CallerCtx S sp W) {F : Nat}
    {R : Nat → BitVec 64} (hF : F + 176 + rmStack (2 ^ 30) ≤ W) (h16 : F % 16 = 0)
    (h2 : R 2 = BitVec.ofNat 64 (sp - F)) (hal : (R 1).toNat % 4 = 0) :
    DmCtx S R (sp - F) (W - F) := by
  cf_facts cx
  exact ⟨cx.inner (by omega) h16, by simp only [heapEnd]; omega, by omega, cx.mulBase, cx.consts,
    h2, hal⟩

/-- `bc_int2num`'s context. -/
theorem CallerCtx.i2n {S : Nat → Prop} {sp W : Nat} (cx : CallerCtx S sp W) {F q : Nat}
    {R : Nat → BitVec 64} {v : Int} (hF : F + 128 ≤ W) (h16 : F % 16 = 0)
    (hq : DmSlot S (sp - F) (W - F) q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - F)) (hal : (R 1).toNat % 4 = 0)
    (hvl : -2 ^ 31 < v) (hvh : v < 2 ^ 31) :
    I2NCtx S R (sp - F) q v := by
  cf_facts cx
  exact ⟨⟨fun a h1 h2 => cx.frame.own a (by omega) (by omega), by omega, by omega, by omega⟩,
    by simp only [heapEnd]; omega, hq.slot, hq.out, by have := hq.apart; omega, h2, hal, hvl, hvh⟩

/-- `bc_raise`'s context. -/
theorem CallerCtx.ra {S : Nat → Prop} {sp W : Nat} (cx : CallerCtx S sp W) {F q : Nat}
    {R : Nat → BitVec 64} (hF : F + 512 + rmStack (2 ^ 30) ≤ W) (h16 : F % 16 = 0)
    (hfar : stderrAddr + 4 ≤ sp - W) (hq : DmSlot S (sp - F) (W - F) q)
    (hz : q + 8 ≤ zeroAddr ∨ zeroAddr + 8 ≤ q) (ho : q + 8 ≤ oneAddr ∨ oneAddr + 8 ≤ q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - F)) (hal : (R 1).toNat % 4 = 0) :
    RaCtx S R (sp - F) (W - F) q := by
  cf_facts cx
  exact ⟨cx.inner (by omega) h16, by simp only [heapEnd]; omega, by omega, by omega, cx.mulBase,
    cx.consts, h2, hal, hq, hz, ho⟩

/-- `out_of_memory` from a callee below the frame, as the caller's: off the
heap, the bytes outside the caller's window agree with the caller's entry. -/
theorem CallerCtx.oom {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {Mt0 M : Mem} {sp W F : Nat} {P : Nat → Prop}
    (h : ∀ R' Mt' sp', sp - W ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
      (∀ a, OutHeap a → ¬ P a → ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) →
      DW live S Q 0x80002bcc#64 R' Mt')
    (hF : F ≤ W)
    (houtM : ∀ a, OutHeap a → ¬ P a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    ∀ R' Mt' sp', sp - F - (W - F) ≤ sp' → sp' ≤ sp - F → R' 2 = BitVec.ofNat 64 sp' →
      (∀ a, OutHeap a → ¬ P a → ¬ frameIn (sp - F) (W - F) a → imgM Mt' a = imgM M a) →
      DW live S Q 0x80002bcc#64 R' Mt' :=
  fun R' Mt' sp' h1 h2 hr2 hout => h R' Mt' sp' (by omega) (by omega) hr2 fun a ha hp hf => by
    rw [hout a ha hp (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
    exact houtM a ha hp hf

end Dc.Mach
