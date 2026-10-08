import Dc.Mach.Bc.SimpMul
import Dc.Mach.Bc.AddSub
import Dc.Mach.Bc.Init

/-!
# `_bc_rec_mul` (`lib/number.c`)

`_bc_rec_mul(u, ulen, v, vlen, prod, full_scale)` at `0x80004bd0` stores in
`*prod` a new number of `ulen + vlen + 1` digits (scale 0) whose value is the
product of the first `ulen` digits of `u` and the first `vlen` of `v`.

- `RmCtx`: the stack window `W` (its 192-byte frame and the callees' below),
  the result slot `q`, the owned `mul_base_digits` and constant words.
- `RmArgs`/`RmPost`/`RmK`: the operands, the result and the continuations.
- `RmAt`: the state inside the function, after the prologue.
- The base case (`_bc_simp_mul`, inlined): `bc_new_num`, the setup of the
  column loop (`sm_cols`), the final carry and the epilogue.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- `mul_base_digits` (`.data`, initially `80`). -/
abbrev mulBaseAddr : Nat := 0x8001cd40

/-- `_bc_rec_mul`'s fixed context: the stack window `W` (the 192-byte frame
and what the callees use below it), the result slot `q` off the heap and
apart from the window, the owned globals it reads, the entry's `sp` and
return address. -/
structure RmCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp q W : Nat) : Prop where
  frame : StackFrame S sp W
  above : heapEnd + W ≤ sp
  big : 224 ≤ W
  slot : PtrSlot S q
  slotOut : ∀ a, slotBytes q a → OutHeap a
  slotApart : q + 8 ≤ sp - W ∨ sp ≤ q
  mulBase : ∀ a, mulBaseAddr ≤ a → a < mulBaseAddr + 4 → S a
  consts : ∀ a, constBytes a → S a
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0

/-- The operands: the first `ulen` digits of `u` and `vlen` of `v`, numbers
of the heap; `mul_base_digits` is `80`. -/
structure RmArgs (M : Mem) (L : List NumObj) (u v : NumObj) (ulen vlen : Nat) : Prop where
  mu : u ∈ L
  mv : v ∈ L
  ul1 : 1 ≤ ulen
  vl1 : 1 ≤ vlen
  ul : ulen ≤ u.rep.len + u.rep.scale
  vl : vlen ≤ v.rep.len + v.rep.scale
  size : ulen + vlen < 2 ^ 30
  mulBase : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80

/-- The result: a new number `y` (one reference, scale `0`,
`ulen + vlen + 1` digits) holding the product heads the heap, its struct is
in the slot, and off the heap only the slot and the window changed. -/
structure RmPost (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (u v : NumRep) (ulen vlen q sp W : Nat) (y : NumObj) : Prop where
  heap : BcHeap S M H F (y :: L)
  owns : y.Owns
  refs : y.rep.refs = 1
  neg : y.rep.neg = false
  len : y.rep.len = ulen + vlen + 1
  scale : y.rep.scale = 0
  val : dvalBE y.rep.ds = dvalBE (u.ds.take ulen) * dvalBE (v.ds.take vlen)
  slot : ldv .ld M q = BitVec.ofNat 64 y.sb.pay
  out : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM M0 a

/-- The continuations: the result, or `out_of_memory` with `sp` inside the
window. -/
structure RmK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (M0 : Mem) (L : List NumObj) (u v : NumRep) (ulen vlen q sp W : Nat) :
    Prop where
  ret : ∀ R' M' H F y, Keeps binClob R' R0 → RmPost S M0 M' H F L u v ulen vlen q sp W y →
    DW live S Q (R0 1) R' M'
  oom : ∀ R' M' sp', sp - W ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
    (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M' a = imgM M0 a) →
    DW live S Q 0x80002bcc#64 R' M'

/-- The registers saved by the prologue (offsets from the lowered `sp`). -/
abbrev rmSlots : List (Nat × Nat) :=
  [(22, 128), (8, 176), (1, 184), (21, 136), (20, 144), (18, 160), (9, 168)]

/-- The registers saved further on (`s3`, `s7`–`s11`). -/
abbrev rmSlots2 : List (Nat × Nat) :=
  [(27, 88), (23, 120), (26, 96), (19, 152), (25, 104), (24, 112)]

/-- Every register `_bc_rec_mul` may change before its epilogue. -/
abbrev rmAll : List Nat :=
  [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31]

/-- Inside `_bc_rec_mul` after the prologue: `sp` lowered by 192, the
prologue's saved registers in the frame, and off the heap only the slot and
the window changed. -/
structure RmAt (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W : Nat) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 192)
  saved : SavedWords M (sp - 192) rmSlots R0
  regs : Keeps rmAll R R0
  out : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM M0 a

/-- The epilogue at `0x80004d84` (`s3`, `s7`–`s11` already restored). -/
theorem rm_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W ulen vlen : Nat} {L : List NumObj}
    {u v : NumRep} {y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L u v ulen vlen q sp W)
    (st : RmAt S M0 M R0 R sp q W)
    (h19 : R 19 = R0 19) (h23 : R 23 = R0 23) (h24 : R 24 = R0 24) (h25 : R 25 = R0 25)
    (h26 : R 26 = R0 26) (h27 : R 27 = R0 27)
    (hp : RmPost S M0 M H F L u v ulen vlen q sp W y) :
    DW live S Q 0x80004d84#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hp.heap.heap.own a h1 h2
  have e1 := st.saved.get 1 184
  have e8 := st.saved.get 8 176
  have e9 := st.saved.get 9 168
  have e18 := st.saved.get 18 160
  have e20 := st.saved.get 20 144
  have e21 := st.saved.get 21 136
  have e22 := st.saved.get 22 128
  have h2 := st.r2
  have hal := cx.al
  bc_run hlive hS [h2, e1, e8, e9, e18, e20, e21, e22]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk.ret _ _ H F y (Keeps.unwind (saved := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27])
    ?_ (hk := by keeps_tac Keeps.refl _ _) (hkp := st.regs)) hp
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, h19, h23, h24, h25, h26, h27]
  rw [show sp - 192 + 192 = sp by omega]

/-- `RmAt` through memory writes that keep the saved words and the bytes
off the heap, the slot and the window. -/
theorem RmAt.mem {S : Nat → Prop} {M0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    (st : RmAt S M0 M R0 R sp q W)
    (hsv : ∀ a, sp - 192 + 128 ≤ a → a < sp - 192 + 192 → imgM M' a = imgM M a)
    (hag : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M' a = imgM M a) :
    RmAt S M0 M' R0 R sp q W :=
  { st with
    saved := st.saved.transport (lo := 128) (top := 192) (hag := hsv)
    out := fun a ha hs hf => (hag a ha hs hf).trans (st.out a ha hs hf) }

/-- `RmAt` through register changes off `sp`. -/
theorem RmAt.keeps {S : Nat → Prop} {M0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp q W : Nat}
    (st : RmAt S M0 M R0 R sp q W) (hk : Keeps rmAll R' R) (h2 : R' 2 = R 2) :
    RmAt S M0 M R0 R' sp q W :=
  { st with
    r2 := h2.trans st.r2
    regs := hk.trans st.regs }

/-- The final carry (zero) stored at `0x80004d74` into the product's first
digit, then the epilogue. -/
theorem rm_fin2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L uo.rep vo.rep la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W)
    (hla : la ≤ uo.rep.len + uo.rep.scale) (hlb : lb ≤ vo.rep.len + vo.rep.scale)
    (hlb1 : 1 ≤ lb) (hla1 : 1 ≤ la)
    (hdu : IsDigits uo.rep.ds) (hdv : IsDigits vo.rep.ds)
    (hul : uo.rep.ds.length = uo.rep.len + uo.rep.scale)
    (hvl : vo.rep.ds.length = vo.rep.len + vo.rep.scale)
    (h13 : R 13 = 0#64) (h15 : R 15 = BitVec.ofNat 64 (y.rep.val + 1))
    (h19 : R 19 = R0 19) (h23 : R 23 = R0 23) (h24 : R 24 = R0 24) (h25 : R 25 = R0 25)
    (h26 : R 26 = R0 26) (h27 : R 27 = R0 27)
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0)
    (hb : BcHeap S M H F (withDs y (colDs uo.rep vo.rep la lb (la + lb)) :: L))
    (hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay) :
    DW live S Q 0x80004d74#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hys' := (hb.nums _ List.mem_cons_self).shape
  have y1 := hys'.vLo; have y2 := hys'.vHi
  simp only [withDs, heapStart, heapEnd] at y1 y2
  have hq0 := cx.slotOut q ⟨Nat.le_refl _, by omega⟩
  have hq7 := cx.slotOut (q + 7) ⟨by omega, by omega⟩
  have hqa := cx.slotApart
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hq0 hq7
  have hc0 := colSt_carry uo.rep.ds vo.rep.ds (la := la) (lb := lb) (by omega) (by omega) hlb1 hdu hdv
  have hval := colSt_final uo.rep.ds vo.rep.ds (la := la) (lb := lb) (by omega) (by omega) hlb1
  rw [hc0] at hval
  bc_run hlive hS [st.r2, h13, h15, word_pred (show 1 ≤ y.rep.val + 1 by omega), Nat.add_sub_cancel]
    at 0x80004d84
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hb1 := hb.out_frame (MemOnly.store M (sp - 192 + 24) 8 (BitVec.ofNat 64 y.rep.val))
    fun a ha => by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hb2 := BcHeap.storeRev hyo (xs := []) (a := 0) (d := 0)
    (D := (colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb (la + lb)).1)
    (by simpa [colDs] using hb1) (by simp only [withDs, List.length_nil]; omega) (by decide)
    (v := 0#64) (by decide)
  simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at hb2
  refine rm_epi hlive cx hk (y := withDs y (0 ::
      (colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb (la + lb)).1)) (H := H) (F := F)
    ((st.mem (fun a h1 h2 => ?_) fun a ha _ hf => ?_).keeps (by keeps_tac Keeps.refl _ _) (by bsimp []))
    (by bsimp [h19]) (by bsimp [h23]) (by bsimp [h24]) (by bsimp [h25]) (by bsimp [h26])
    (by bsimp [h27]) ⟨hb2, hyo, hyr, hyn, hyl, hys, hval, ?_, fun a ha hs hf => ?_⟩
  · rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  · simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, frameIn] at ha hf
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hq
  · simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, frameIn] at ha hf
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
    exact st.out a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega) hs
      (by simp only [frameIn]; omega)

/-- The base case's last store at `0x80004d44`: the final carry (zero) into
the product's first digit, `s3`, `s7`–`s11` restored, then the epilogue. -/
theorem rm_fin {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L uo.rep vo.rep la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W) (sv : SavedWords M (sp - 192) rmSlots2 R0)
    (hla : la ≤ uo.rep.len + uo.rep.scale) (hlb : lb ≤ vo.rep.len + vo.rep.scale)
    (hlb1 : 1 ≤ lb) (hla1 : 1 ≤ la) (hN : la + lb < 2 ^ 30)
    (hdu : IsDigits uo.rep.ds) (hdv : IsDigits vo.rep.ds)
    (hul : uo.rep.ds.length = uo.rep.len + uo.rep.scale)
    (hvl : vo.rep.ds.length = vo.rep.len + vo.rep.scale)
    (hP : ldv .ld M (sp - 192 + 24) = BitVec.ofNat 64 (y.rep.val + (la + lb)))
    (h18 : R 18 = BitVec.ofNat 64 (la + lb))
    (h26 : R 26 = BitVec.ofNat 64
      (colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb (la + lb)).2)
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0)
    (hb : BcHeap S M H F (withDs y (colDs uo.rep vo.rep la lb (la + lb)) :: L))
    (hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay) :
    DW live S Q 0x80004d44#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hys' := (hb.nums _ List.mem_cons_self).shape
  have y1 := hys'.vLo; have y2 := hys'.vHi
  simp only [withDs, heapStart, heapEnd] at y1 y2
  have hc0 := colSt_carry uo.rep.ds vo.rep.ds (la := la) (lb := lb) (by omega) (by omega) hlb1 hdu hdv
  rw [hc0] at h26
  have h2 := st.r2
  bc_run hlive hS [h2, h18, h26, hP, sv.get 19 152, sv.get 23 120, sv.get 24 112, sv.get 25 104,
    sv.get 26 96, sv.get 27 88, sxw_pred (show 1 ≤ la + lb by omega) (by omega),
    zext32_ofNat (show la + lb - 1 < 2 ^ 32 by omega),
    sub_ofNat (show la + lb - 1 ≤ y.rep.val + (la + lb) by omega) (by omega)] at 0x80004d74
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact rm_fin2 hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _) (by bsimp [])) hla hlb hlb1 hla1
    hdu hdv hul hvl (by bsimp []) (by bsimp []; congr 1; omega) (by bsimp []) (by bsimp [])
    (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) hyo hyr hyn hyl hys hb hq

end Dc.Mach
