import Dc.Mach.Bc.KaraZeroRef
import Dc.Mach.Bc.KaraTrimChain

/-!
# `_bc_rec_mul`'s Karatsuba step: the second length dispatch

Both `u` routes reach the same test of `lb` against the half `n`: at
`0x80004e64` when `u1` is a view (`bge s5, s0`), at `0x800053bc` when `u1` is
a reference to `_zero_` (`blt s5, s0`). Both select the struct source of
`v`'s high half at `0x800053c0` (`n ≤ lb`) or the `_zero_` reference at
`0x80004e68` (`lb < n`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-! ## The step's scratch region

Every struct source and view of the step changes only the allocator's own
words, the number heap and `_bc_Free_list`. One `MemOnly KTouch` composes
those frames, and the step's globals and stack frame are off it. -/

/-- The bytes a struct source or a view may change. -/
def KTouch (a : Nat) : Prop :=
  (freeListAddr ≤ a ∧ a < freeListAddr + 16) ∨ (heapStart ≤ a ∧ a < heapEnd) ∨ bcFreeBytes a

theorem not_alloc_of_not_touch {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {a : Nat} (h : ¬ KTouch a) : ¬ AllocByte H a := fun hal => by
  rcases AllocByte.glob_or_heap hi hal with h' | h'
  · exact h (.inl h')
  · exact h (.inr (.inl h'))

/-- An allocator-relative frame is a scratch frame. -/
theorem memOnly_touch_of_alloc {S : Nat → Prop} {Mt M : Mem} {H : Heap} (hi : HeapInv S Mt H)
    (h : ∀ a, ¬ AllocByte H a → imgM M a = imgM Mt a) : MemOnly KTouch M Mt :=
  fun a ha => h a (not_alloc_of_not_touch hi ha)

/-- A view site's frame is a scratch frame. -/
theorem ViewStruct.touch {S : Nat → Prop} {Mt M : Mem} {H H' : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} (hvs : ViewStruct S Mt M H H' F F' sb L)
    (hb : BcHeap S Mt H F L) : MemOnly KTouch M Mt := by
  intro a ha
  have hbf := hvs.inv.blk (List.mem_append_right _ hvs.live)
  have hlo := hbf.lo; have htop := hbf.top; have hfin := hbf.fin
  simp only [heapStart] at hlo
  simp only [heapEnd] at htop
  have hpl : 2147603920 ≤ sb.pay := by
    have e1 : sb.pay = sb.h + 16 := rfl
    omega
  refine hvs.base a (not_alloc_of_not_touch hb.heap ha) (fun hin => ?_)
    (fun hg => ha (.inr (.inr hg)))
  simp only [Blk.In] at hin
  exact ha (.inr (.inl (by simp only [heapStart, heapEnd]; omega)))

/-- A doubleword at `_zero_`'s slot survives the scratch. -/
theorem ldv_zero_touch {M Mt : Mem} (h : MemOnly KTouch M Mt) :
    ldv .ld M zeroAddr = ldv .ld Mt zeroAddr :=
  ldv_congr .ld fun j hj => h _ (by
    simp only [KTouch, bcFreeBytes, bcFreeAddr, freeListAddr, heapStart, heapEnd, zeroAddr,
      widthOfM] at hj ⊢
    omega)

/-- A word at `mulBase`'s slot survives the scratch. -/
theorem ldv_mulBase_touch {M Mt : Mem} (h : MemOnly KTouch M Mt) :
    ldv .lw M mulBaseAddr = ldv .lw Mt mulBaseAddr :=
  ldv_congr .lw fun j hj => h _ (by
    simp only [KTouch, bcFreeBytes, bcFreeAddr, freeListAddr, heapStart, heapEnd, mulBaseAddr,
      widthOfM] at hj ⊢
    omega)

/-- Bytes above the heap survive the scratch. -/
theorem touch_above {M Mt : Mem} (h : MemOnly KTouch M Mt) {a : Nat} (ha : heapEnd ≤ a) :
    imgM M a = imgM Mt a :=
  h a (by simp only [KTouch, bcFreeBytes, bcFreeAddr, freeListAddr, heapStart, heapEnd] at ha ⊢
          omega)

/-- One view pushed onto the step's object list. -/
theorem KList_push (x : NumObj) (hs : List Hd) (A B : List NumObj) (z : NumObj) :
    x :: KList [] hs A B z = KList [] (some x :: hs) A B z := by
  rw [KList, KList, zeroCount_some, temps_some]
  simp only [List.nil_append, List.cons_append, List.append_assoc]

/-- **The length dispatch at `0x80004e64`**, reached with `u1` a view. -/
theorem kdisp_80004e64 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64} {n lb : Nat}
    (h21 : R 21 = BitVec.ofNat 64 lb) (h8 : R 8 = BitVec.ofNat 64 n)
    (hlbb : lb < 2 ^ 31) (hnb : n < 2 ^ 31)
    (hge : n ≤ lb → DW live S Q 0x800053c0#64 R M)
    (hlt : lb < n → DW live S Q 0x80004e68#64 R M) :
    DW live S Q 0x80004e64#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h21, h8, toInt_ofNat_small] at 0x800053c0 0x80004e68
  · intro hc
    exact hge (by omega)
  · intro hc
    exact hlt (by omega)

/-- **The length dispatch at `0x800053bc`**, reached with `u1` a reference to
`_zero_`. -/
theorem kdisp_800053bc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64} {n lb : Nat}
    (h21 : R 21 = BitVec.ofNat 64 lb) (h8 : R 8 = BitVec.ofNat 64 n)
    (hlbb : lb < 2 ^ 31) (hnb : n < 2 ^ 31)
    (hge : n ≤ lb → DW live S Q 0x800053c0#64 R M)
    (hlt : lb < n → DW live S Q 0x80004e68#64 R M) :
    DW live S Q 0x800053bc#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h21, h8, toInt_ofNat_small] at 0x80004e68 0x800053c0
  · intro hc
    exact hlt (by omega)
  · intro hc
    exact hge (by omega)

end Dc.Mach
