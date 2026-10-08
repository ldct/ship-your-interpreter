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
  [(8, 176), (1, 184), (22, 128), (21, 136), (20, 144), (18, 160), (9, 168)]

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
    (st : RmAt S M0 M R0 R sp q W) (hsv : SavedWords M' (sp - 192) rmSlots R0)
    (hag : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M' a = imgM M a) :
    RmAt S M0 M' R0 R sp q W :=
  { st with
    saved := hsv
    out := fun a ha hs hf => (hag a ha hs hf).trans (st.out a ha hs hf) }

/-- A store apart from every saved slot keeps the saved words. -/
theorem SavedWords.storeAway {M : Mem} {fr : Nat} {slots : List (Nat × Nat)} {R0 : Nat → BitVec 64}
    (h : SavedWords M fr slots R0) {a w : Nat} (v : BitVec 64)
    (hd : ∀ p ∈ slots, fr + p.2 + 8 ≤ a ∨ a + w ≤ fr + p.2) :
    SavedWords (writeLog M [(a, w, v)]) fr slots R0 := by
  intro p hp
  rw [ldv_ld_miss _ _ (by have := hd p hp; omega)]; exact h p hp

/-- A frame store apart from every saved slot keeps the saved words. -/
theorem SavedWords.storeFrame {M : Mem} {fr : Nat} {slots : List (Nat × Nat)} {R0 : Nat → BitVec 64}
    (h : SavedWords M fr slots R0) (o : Nat) (v : BitVec 64)
    (hd : ∀ p ∈ slots, p.2 + 8 ≤ o ∨ o + 8 ≤ p.2 := by decide) :
    SavedWords (writeLog M [(fr + o, 8, v)]) fr slots R0 :=
  h.storeAway v fun p hp => by have := hd p hp; omega

/-- The registers saved after the prologue still hold their entry values. -/
structure RmKept (R R0 : Nat → BitVec 64) : Prop where
  k19 : R 19 = R0 19
  k23 : R 23 = R0 23
  k24 : R 24 = R0 24
  k25 : R 25 = R0 25
  k26 : R 26 = R0 26
  k27 : R 27 = R0 27

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
    ((st.mem (st.saved.transport (lo := 128) (top := 192) (hag := fun a h1 h2 => ?_))
      fun a ha _ hf => ?_).keeps (by keeps_tac Keeps.refl _ _) (by bsimp []))
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

theorem ex_add (a b : BitVec 64) :
    BitVec.extractLsb 31 0 (a + b) = BitVec.extractLsb 31 0 a + BitVec.extractLsb 31 0 b := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-- The column loop's `subw` of the stored `addiw` and `pvptr`. -/
theorem subw_ptr1 {P V k : Nat} (hk : k ≤ P) :
    subw (BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (subw (BitVec.ofNat 64 P) (BitVec.ofNat 64 V) + 1#64))) (BitVec.ofNat 64 (P - k)) =
      subw (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 V) := by
  simp only [subw, ex_sx, ex_add, e_ofNat, show BitVec.extractLsb 31 0 (1#64) = 1#32 from rfl]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub, BitVec.toNat_add]
  omega

/-- The column loop entered at `0x80004cb4` with the product `y` fresh (all
zeros) at the head of the heap, run to the final carry. -/
theorem rm_cols_call {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L uo.rep vo.rep la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W) (sv : SavedWords M (sp - 192) rmSlots2 R0)
    (huL : uo ∈ L) (hvL : vo ∈ L)
    (hla : la ≤ uo.rep.len + uo.rep.scale) (hlb : lb ≤ vo.rep.len + vo.rep.scale)
    (hla1 : 1 ≤ la) (hlb1 : 1 ≤ lb) (hN : la + lb < 2 ^ 30) (hm : 90 * min la lb < 2 ^ 30)
    (hr : ColRegs R uo.rep vo.rep la lb (y.rep.val + (la + lb)) (sp - 192) 0 0)
    (h0 : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p)
    (h8 : ldv .ld M (sp - 192 + 8) =
      subw (BitVec.ofNat 64 (y.rep.val + (la + lb))) (BitVec.ofNat 64 lb))
    (h10 : ldv .ld M (sp - 192 + 16) = BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (subw (BitVec.ofNat 64 (y.rep.val + (la + lb))) (BitVec.ofNat 64 lb) + 1#64)))
    (hP : ldv .ld M (sp - 192 + 24) = BitVec.ofNat 64 (y.rep.val + (la + lb)))
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0)
    (hyd : y.rep.ds = List.replicate (la + lb + 1) 0)
    (hb : BcHeap S M H F (y :: L)) (hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay) :
    DW live S Q 0x80004cb4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hab := cx.above
  simp only [heapEnd] at hab
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hys' := (hb.nums _ List.mem_cons_self).shape
  have y1 := hys'.vLo; have y2 := hys'.vHi
  simp only [heapStart, heapEnd] at y1 y2
  have hq0 := cx.slotOut q ⟨Nat.le_refl _, by omega⟩
  have hq7 := cx.slotOut (q + 7) ⟨by omega, by omega⟩
  have hqa := cx.slotApart
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hq0 hq7
  have hu := hb.nums uo (List.mem_cons_of_mem _ huL)
  have hv := hb.nums vo (List.mem_cons_of_mem _ hvL)
  have hsf' : StackFrame S (sp - 192 + 192) 192 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine sm_cols hlive hS hyo huL hvL hla hlb hla1 hlb1 (by omega) hm (by omega) rfl hsf'
    (by simp only [heapEnd]; omega) (fun k hk => subw_ptr hk) (fun k hk => ?_) (M0 := M) (R0 := R)
    (fun R' M' hk' hr' hb' hmo => ?_) (la + lb) 0 R M (by omega) (by omega) (Keeps.refl _ _)
    hr (by simpa [colDs, colSt, withDs, ← hyd] using hb) (MemOnly.refl _ _) h0 h8 h10
  · exact subw_ptr1 hk
  · have hag : ∀ a, ¬ accBytes y.rep a → imgM M' a = imgM M a := hmo
    have hdu : IsDigits uo.rep.ds := hu.shape.dig
    have hdv : IsDigits vo.rep.ds := hv.shape.dig
    refine rm_fin hlive cx hk ((st.mem (st.saved.transport (lo := 128) (top := 192)
        (hag := fun a h1 h2 => hag a (by simp only [accBytes]; omega)))
        fun a ha _ _ => hag a (by simp only [OutHeap, heapStart, heapEnd] at ha; simp only [accBytes]; omega)).keeps
        (hk'.mono (by decide)) (hk'.get 2))
      (sv.transport (lo := 88) (top := 160) (hag := fun a h1 h2 => hag a (by simp only [accBytes]; omega)))
      hla hlb hlb1 hla1 hN hdu hdv hu.shape.dsLen hv.shape.dsLen ?_ hr'.r18 hr'.r26 hyo hyr hyn hyl hys hb' ?_
    · rw [ldv_congr .ld fun j hj => hag _ (by simp only [accBytes, widthOfM] at hj ⊢; omega)]; exact hP
    · rw [ldv_congr .ld fun j hj => hag _ (by simp only [accBytes, widthOfM] at hj ⊢; omega)]; exact hq

/-- The second half of the column loop's setup, `0x80004c80`–`0x80004cb4`. -/
theorem rm_setup2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L uo.rep vo.rep la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W) (sv : SavedWords M (sp - 192) [(19, 152), (25, 104), (24, 112)] R0)
    (k23 : R 23 = R0 23) (k26 : R 26 = R0 26) (k27 : R 27 = R0 27)
    (huL : uo ∈ L) (hvL : vo ∈ L)
    (hla : la ≤ uo.rep.len + uo.rep.scale) (hlb : lb ≤ vo.rep.len + vo.rep.scale)
    (hla1 : 1 ≤ la) (hlb1 : 1 ≤ lb) (hN : la + lb < 2 ^ 30) (hm : 90 * min la lb < 2 ^ 30)
    (h0 : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p)
    (h10 : ldv .ld M (sp - 192 + 16) = BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (subw (BitVec.ofNat 64 (y.rep.val + (la + lb))) (BitVec.ofNat 64 lb) + 1#64)))
    (hP : ldv .ld M (sp - 192 + 24) = BitVec.ofNat 64 (y.rep.val + (la + lb)))
    (r2 : R 2 = BitVec.ofNat 64 (sp - 192)) (r20 : R 20 = BitVec.ofNat 64 la)
    (r21 : R 21 = BitVec.ofNat 64 lb) (r22 : R 22 = BitVec.ofNat 64 (la + lb))
    (r24 : R 24 = BitVec.ofNat 64 uo.rep.val) (r25 : R 25 = BitVec.ofNat 64 vo.rep.val)
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0)
    (hyd : y.rep.ds = List.replicate (la + lb + 1) 0)
    (hb : BcHeap S M H F (y :: L)) (hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay) :
    DW live S Q 0x80004c80#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hys' := (hb.nums _ List.mem_cons_self).shape
  have y1 := hys'.vLo; have y2 := hys'.vHi
  simp only [heapStart, heapEnd] at y1 y2
  have hv := hb.nums vo (List.mem_cons_of_mem _ hvL)
  have v1 := hv.shape.vLo; have v2 := hv.shape.vHi
  simp only [heapStart, heapEnd] at v1 v2
  have hq0 := cx.slotOut q ⟨Nat.le_refl _, by omega⟩
  have hq7 := cx.slotOut (q + 7) ⟨by omega, by omega⟩
  have hqa := cx.slotApart
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hq0 hq7
  bc_run hlive hS [r2, r20, r21, r22, r24, r25, hP, k23, k26, k27, word_pred,
    sub_ofNat (show 1 ≤ lb by omega) (by omega)] at 0x80004cb4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hfr : ∀ a, ¬ frameIn sp W a → ∀ (v1 v2 v3 v4 : BitVec 64),
      imgM (writeLog (writeLog (writeLog (writeLog M [(sp - 192 + 96, 8, v1)])
        [(sp - 192 + 120, 8, v2)]) [(sp - 192 + 88, 8, v3)]) [(sp - 192 + 8, 8, v4)]) a = imgM M a :=
    fun a ha _ _ _ _ => by
      simp only [frameIn] at ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
        imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  refine rm_cols_call hlive cx hk
    ((st.mem ((((st.saved.storeFrame 96 _).storeFrame 120 _).storeFrame 88 _).storeFrame 8 _)
      fun a _ _ hf => hfr a hf _ _ _ _).keeps (by keeps_tac Keeps.refl _ _) (by bsimp []))
    ((((sv.store 26 96).store 23 120).store 27 88).storeFrame 8 _)
    huL hvL hla hlb hla1 hlb1 hN hm
    { r18 := by bsimp []
      r26 := by bsimp []
      r19 := by bsimp []
      r20 := by bsimp []
      r21 := by bsimp [r21]
      r22 := by bsimp [r22]
      r24 := by bsimp [r24]
      r25 := by bsimp [r25]
      r9 := by bsimp []; congr 1; omega
      r8 := by bsimp []
      r2 := by bsimp [r2] }
    ?_ ?_ ?_ ?_ hyo hyr hyn hyl hys hyd
    (hb.out_frame (P := frameIn sp W) (fun a ha => hfr a ha _ _ _ _) fun a ha => by
      simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha ⊢; omega) ?_
  all_goals simp (disch := omega) only [ldv_ld_miss, ldv_ld_hit_eq]
  · exact h0
  · exact h10
  · exact hP
  · exact hq

/-- The column loop's setup, `0x80004c6c`–`0x80004c80`. -/
theorem rm_setup1b {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L uo.rep vo.rep la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W) (sv : SavedWords M (sp - 192) [(25, 104), (24, 112)] R0)
    (k19 : R 19 = R0 19) (k23 : R 23 = R0 23) (k26 : R 26 = R0 26) (k27 : R 27 = R0 27)
    (huL : uo ∈ L) (hvL : vo ∈ L)
    (hla : la ≤ uo.rep.len + uo.rep.scale) (hlb : lb ≤ vo.rep.len + vo.rep.scale)
    (hla1 : 1 ≤ la) (hlb1 : 1 ≤ lb) (hN : la + lb < 2 ^ 30) (hm : 90 * min la lb < 2 ^ 30)
    (h0 : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p)
    (hP : ldv .ld M (sp - 192 + 24) = BitVec.ofNat 64 (y.rep.val + (la + lb)))
    (r2 : R 2 = BitVec.ofNat 64 (sp - 192)) (r20 : R 20 = BitVec.ofNat 64 la)
    (r21 : R 21 = BitVec.ofNat 64 lb) (r22 : R 22 = BitVec.ofNat 64 (la + lb))
    (r18 : R 18 = BitVec.ofNat 64 vo.rep.p) (r24 : R 24 = BitVec.ofNat 64 uo.rep.val)
    (r15 : R 15 = BitVec.ofNat 64 (y.rep.val + (la + lb)))
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0)
    (hyd : y.rep.ds = List.replicate (la + lb + 1) 0)
    (hb : BcHeap S M H F (y :: L)) (hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay) :
    DW live S Q 0x80004c6c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hv := hb.nums vo (List.mem_cons_of_mem _ hvL)
  have v3 := hv.shape.pLo; have v4 := hv.shape.pHi
  simp only [heapStart, heapEnd] at v3 v4
  bc_run hlive hS [r2, r21, r18, r15, k19, hv.value] at 0x80004c80
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hfr : ∀ a, ¬ frameIn sp W a → ∀ (v1 v2 : BitVec 64),
      imgM (writeLog (writeLog M [(sp - 192 + 152, 8, v1)]) [(sp - 192 + 16, 8, v2)]) a = imgM M a :=
    fun a ha _ _ => by
      simp only [frameIn] at ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hq0 := cx.slotOut q ⟨Nat.le_refl _, by omega⟩
  have hq7 := cx.slotOut (q + 7) ⟨by omega, by omega⟩
  have hqa := cx.slotApart
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hq0 hq7
  refine rm_setup2 hlive cx hk
    ((st.mem ((st.saved.storeFrame 152 _).storeFrame 16 _)
      fun a _ _ hf => hfr a hf _ _).keeps (by keeps_tac Keeps.refl _ _) (by bsimp []))
    ((sv.store 19 152).storeFrame 16 _)
    (by bsimp [k23]) (by bsimp [k26]) (by bsimp [k27])
    huL hvL hla hlb hla1 hlb1 hN hm ?_ ?_ ?_ (by bsimp [r2]) (by bsimp [r20]) (by bsimp [r21])
    (by bsimp [r22]) (by bsimp [r24]) (by bsimp []) hyo hyr hyn hyl hys hyd
    (hb.out_frame (P := frameIn sp W) (fun a ha => hfr a ha _ _) fun a ha => by
      simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha ⊢; omega) ?_
  all_goals simp (disch := omega) only [ldv_ld_miss, ldv_ld_hit_eq]
  · exact h0
  · exact hP
  · exact hq

/-- The first half of the column loop's setup, `0x80004c58`–`0x80004c80`. -/
theorem rm_setup1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L uo.rep vo.rep la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W) (kp : RmKept R R0)
    (huL : uo ∈ L) (hvL : vo ∈ L)
    (hla : la ≤ uo.rep.len + uo.rep.scale) (hlb : lb ≤ vo.rep.len + vo.rep.scale)
    (hla1 : 1 ≤ la) (hlb1 : 1 ≤ lb) (hN : la + lb < 2 ^ 30) (hm : 90 * min la lb < 2 ^ 30)
    (h0 : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p)
    (hP : ldv .ld M (sp - 192 + 24) = BitVec.ofNat 64 (y.rep.val + (la + lb)))
    (r2 : R 2 = BitVec.ofNat 64 (sp - 192)) (r20 : R 20 = BitVec.ofNat 64 la)
    (r21 : R 21 = BitVec.ofNat 64 lb) (r22 : R 22 = BitVec.ofNat 64 (la + lb))
    (r18 : R 18 = BitVec.ofNat 64 vo.rep.p)
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0)
    (hyd : y.rep.ds = List.replicate (la + lb + 1) 0)
    (hb : BcHeap S M H F (y :: L)) (hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay) :
    DW live S Q 0x80004c58#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hu := hb.nums uo (List.mem_cons_of_mem _ huL)
  have hv := hb.nums vo (List.mem_cons_of_mem _ hvL)
  have u3 := hu.shape.pLo; have u4 := hu.shape.pHi
  have v3 := hv.shape.pLo; have v4 := hv.shape.pHi
  simp only [heapStart, heapEnd] at u3 u4 v3 v4
  have hq0 := cx.slotOut q ⟨Nat.le_refl _, by omega⟩
  have hq7 := cx.slotOut (q + 7) ⟨by omega, by omega⟩
  have hqa := cx.slotApart
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hq0 hq7
  bc_run hlive hS [r2, r20, r21, r22, r18, h0, hP, kp.k19, kp.k24, kp.k25, ldv_ld_miss, ldv_ld_hit_eq,
    hu.value, hv.value] at 0x80004c6c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hfr : ∀ a, ¬ frameIn sp W a → ∀ (v1 v2 : BitVec 64),
      imgM (writeLog (writeLog M [(sp - 192 + 112, 8, v1)]) [(sp - 192 + 104, 8, v2)]) a = imgM M a :=
    fun a ha _ _ => by
      simp only [frameIn] at ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  refine rm_setup1b hlive cx hk
    ((st.mem ((st.saved.storeFrame 112 _).storeFrame 104 _)
      fun a _ _ hf => hfr a hf _ _).keeps (by keeps_tac Keeps.refl _ _) (by bsimp []))
    (((SavedWords.nil _ _ R0).store 24 112).store 25 104)
    (by bsimp [kp.k19]) (by bsimp [kp.k23]) (by bsimp [kp.k26]) (by bsimp [kp.k27])
    huL hvL hla hlb hla1 hlb1 hN hm ?_ ?_ (by bsimp [r2]) (by bsimp [r20]) (by bsimp [r21])
    (by bsimp [r22]) (by bsimp [r18]) (by bsimp []) (by bsimp []) hyo hyr hyn hyl hys hyd
    (hb.out_frame (P := frameIn sp W) (fun a ha => hfr a ha _ _) fun a ha => by
      simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha ⊢; omega) ?_
  all_goals simp (disch := omega) only [ldv_ld_miss, ldv_ld_hit_eq]
  · exact h0
  · exact hP
  · exact hq

/-- The base case after `bc_new_num` returned the product `y` at
`0x80004c40`: `*prod = y`, the column loop's pointers and saved registers. -/
theorem rm_setup {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L uo.rep vo.rep la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W) (kp : RmKept R R0)
    (huL : uo ∈ L) (hvL : vo ∈ L)
    (hla : la ≤ uo.rep.len + uo.rep.scale) (hlb : lb ≤ vo.rep.len + vo.rep.scale)
    (hla1 : 1 ≤ la) (hlb1 : 1 ≤ lb) (hN : la + lb < 2 ^ 30) (hm : 90 * min la lb < 2 ^ 30)
    (h0 : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p)
    (h10 : R 10 = BitVec.ofNat 64 y.sb.pay) (h8 : R 8 = BitVec.ofNat 64 (la + lb + 1))
    (h22 : R 22 = BitVec.ofNat 64 (la + lb)) (h20 : R 20 = BitVec.ofNat 64 la)
    (h21 : R 21 = BitVec.ofNat 64 lb) (h18 : R 18 = BitVec.ofNat 64 vo.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 q)
    (hy : y.rep = zeroRep y.sb.pay y.db.pay (la + lb + 1) 0)
    (hb : BcHeap S M H F (y :: L)) :
    DW live S Q 0x80004c40#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hyn := hb.nums _ List.mem_cons_self
  have hys' := hyn.shape
  have y1 := hys'.vLo; have y2 := hys'.vHi; have y3 := hys'.pLo; have y4 := hys'.pHi
  simp only [heapStart, heapEnd] at y1 y2 y3 y4
  have hyp : y.rep.p = y.sb.pay := by rw [hy]; rfl
  have hyv := hyn.value
  rw [hyp] at hyv y3 y4
  have hu := hb.nums uo (List.mem_cons_of_mem _ huL)
  have hv := hb.nums vo (List.mem_cons_of_mem _ hvL)
  have u3 := hu.shape.pLo; have u4 := hu.shape.pHi
  have v3 := hv.shape.pLo; have v4 := hv.shape.pHi
  simp only [heapStart, heapEnd] at u3 u4 v3 v4
  have hq0 := cx.slotOut q ⟨Nat.le_refl _, by omega⟩
  have hq7 := cx.slotOut (q + 7) ⟨by omega, by omega⟩
  have hqa := cx.slotApart
  have hqs := cx.slot
  have q1 := hqs.lo; have q2 := hqs.hi; have q3 := hqs.al
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hq0 hq7
  bc_run hlive hS [st.r2, h10, h8, h22, h20, h21, h18, h9, h0, hyv, hu.value, hv.value, kp.k19,
    kp.k23, kp.k24, kp.k25, kp.k26, kp.k27, toInt_ofNat_small, Nat.add_sub_cancel] at 0x80004c58
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hqs.acc | skip
  · intro hc; omega
  intro _
  have hfr : ∀ a, ¬ frameIn sp W a → ¬ slotBytes q a → ∀ (v1 v2 : BitVec 64),
      imgM (writeLog (writeLog M [(q, 8, v1)]) [(sp - 192 + 24, 8, v2)]) a = imgM M a :=
    fun a ha hs _ _ => by
      simp only [frameIn, slotBytes] at ha hs
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hyd : y.rep.ds = List.replicate (la + lb + 1) 0 := by rw [hy]; simp [zeroRep]
  refine rm_setup1 hlive cx hk
    ((st.mem ((st.saved.storeAway _ fun p hp => ?_).storeFrame 24 _)
      fun a _ hs hf => hfr a hf hs _ _).keeps (by keeps_tac Keeps.refl _ _) (by bsimp []))
    ⟨by bsimp [kp.k19], by bsimp [kp.k23], by bsimp [kp.k24], by bsimp [kp.k25], by bsimp [kp.k26],
      by bsimp [kp.k27]⟩
    huL hvL hla hlb hla1 hlb1 hN hm ?_ ?_ (by bsimp [st.r2]) (by bsimp [h20]) (by bsimp [h21])
    (by bsimp [h22]) (by bsimp [h18])
    (show y.rep.ptr ≠ 0 by have : y.rep.ptr = y.rep.val := by rw [hy]; rfl
                           omega)
    (by rw [hy]; rfl) (by rw [hy]; rfl) (by rw [hy]; rfl) (by rw [hy]; rfl) hyd
    (hb.out_frame (P := fun a => frameIn sp W a ∨ slotBytes q a)
      (fun a ha => hfr a (fun h => ha (.inl h)) (fun h => ha (.inr h)) _ _) fun a ha => by
        rcases ha with ha | ha
        · simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha ⊢; omega
        · exact cx.slotOut a ha) ?_
  · simp only [rmSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  all_goals simp (disch := omega) only [ldv_ld_miss, ldv_ld_hit_eq]
  exact h0

/-- **The base case** at `0x80004c30` (`_bc_simp_mul`, inlined):
`bc_new_num(ulen + vlen + 1, 0)`, the column loop, the final carry. -/
theorem rm_base {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L uo.rep vo.rep la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W) (kp : RmKept R R0)
    (huL : uo ∈ L) (hvL : vo ∈ L)
    (hla : la ≤ uo.rep.len + uo.rep.scale) (hlb : lb ≤ vo.rep.len + vo.rep.scale)
    (hla1 : 1 ≤ la) (hlb1 : 1 ≤ lb) (hN : la + lb < 2 ^ 30) (hm : 90 * min la lb < 2 ^ 30)
    (h0 : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p)
    (h22 : R 22 = BitVec.ofNat 64 (la + lb)) (h20 : R 20 = BitVec.ofNat 64 la)
    (h21 : R 21 = BitVec.ofNat 64 lb) (h18 : R 18 = BitVec.ofNat 64 vo.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 q) (hb : BcHeap S M H F L) :
    DW live S Q 0x80004c30#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  bc_run hlive hS [h22, sxw_ofNat] at 0x80004c3c
  apply st_80004c3c hlive
  have hsf' : StackFrame S (sp - 192) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine bc_new_num_spec (len := la + lb + 1) (scale := 0) hlive hb.newHeap hsf' (by simp only [heapEnd]; omega) (by omega)
    (Nat.le_add_left _ _) _ (by bsimp []) (by bsimp []) (by bsimp [st.r2]) (by bsimp [])
    ⟨fun R1 Mt1 H1 F1 x hk1 hp1 hr1 => ?_, fun R' Mt' hr2 hout => ?_⟩
  · have hag : ∀ a, OutHeap a → ¬ frameIn (sp - 192) 32 a → imgM Mt1 a = imgM M a := hp1.out
    refine rm_setup hlive cx hk
      ((st.mem (st.saved.transport (lo := 128) (top := 192) (hag := fun a h1 h2 => hag a (by
          simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [frameIn]; omega)))
        fun a ha _ hf => hag a ha (by simp only [frameIn] at hf ⊢; omega)).keeps
        (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
        (by rw [hk1.get 2]; bsimp []))
      ⟨by rw [hk1.get 19]; bsimp [kp.k19], by rw [hk1.get 23]; bsimp [kp.k23],
        by rw [hk1.get 24]; bsimp [kp.k24], by rw [hk1.get 25]; bsimp [kp.k25],
        by rw [hk1.get 26]; bsimp [kp.k26], by rw [hk1.get 27]; bsimp [kp.k27]⟩
      huL hvL hla hlb hla1 hlb1 hN hm ?_ hr1 (by rw [hk1.get 8]; bsimp [])
      (by rw [hk1.get 22]; bsimp [h22]) (by rw [hk1.get 20]; bsimp [h20])
      (by rw [hk1.get 21]; bsimp [h21]) (by rw [hk1.get 18]; bsimp [h18])
      (by rw [hk1.get 9]; bsimp [h9]) hp1.rep (NewNumPost.insert hb hp1)
    rw [ldv_congr .ld fun j hj => hag _ (by
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, widthOfM] at hj ⊢; omega)
      (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact h0
  · refine hk.oom R' Mt' (sp - 192 - 32) (by omega) (by omega) hr2 fun a ha hs hf => ?_
    rw [hout a ha fun h => hf (by simp only [frameIn] at *; omega)]
    exact st.out a ha hs hf

/-- `addi sp, sp, -192`. -/
theorem word_sub192 {x : Nat} (h : 192 ≤ x) :
    BitVec.ofNat 64 x + 18446744073709551424#64 = BitVec.ofNat 64 (x - 192) := by
  change BitVec.ofNat 64 x + -(192#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le x 192 (by decide) h

theorem sra80_31 : shift_bits_right_arith (BitVec.extractLsb 31 0 80#64) 31#5 = 0#32 := by decide
theorem quarter80 : BitVec.signExtend 64 (shift_bits_right_arith (BitVec.extractLsb 31 0
    (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64
      (BitVec.extractLsb 31 0 0#64 >>> 30)) + BitVec.extractLsb 31 0 80#64))) 2#5) = 20#64 := by
  decide

/-- The Karatsuba case at `0x80004db0`, entered after the prologue with both
operands of at least `20` digits and `80` digits together. -/
def RmKara (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (M0 : Mem) (L : List NumObj) (uo vo : NumObj) (la lb q sp W : Nat) :
    Prop :=
  ∀ R M H F, RmAt S M0 M R0 R sp q W → RmKept R R0 → 80 ≤ la + lb → 20 ≤ la → 20 ≤ lb →
    ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p →
    R 22 = BitVec.ofNat 64 (la + lb) → R 20 = BitVec.ofNat 64 la → R 21 = BitVec.ofNat 64 lb →
    R 18 = BitVec.ofNat 64 vo.rep.p → R 9 = BitVec.ofNat 64 q → BcHeap S M H F L →
    DW live S Q 0x80004db0#64 R M

/-- The threshold test at `0x80004c10`: the base case when
`ulen + vlen < 80` or either length is below `20`, else the Karatsuba case. -/
theorem rm_disp {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L uo.rep vo.rep la lb q sp W)
    (hkara : RmKara live S Q R0 M0 L uo vo la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W) (kp : RmKept R R0)
    (huL : uo ∈ L) (hvL : vo ∈ L)
    (hla : la ≤ uo.rep.len + uo.rep.scale) (hlb : lb ≤ vo.rep.len + vo.rep.scale)
    (hla1 : 1 ≤ la) (hlb1 : 1 ≤ lb) (hN : la + lb < 2 ^ 30)
    (h0 : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p) (h16 : R 16 = 80#64)
    (h11 : R 11 = BitVec.ofNat 64 la) (h13 : R 13 = BitVec.ofNat 64 lb)
    (h22 : R 22 = BitVec.ofNat 64 (la + lb)) (h20 : R 20 = BitVec.ofNat 64 la)
    (h21 : R 21 = BitVec.ofNat 64 lb) (h18 : R 18 = BitVec.ofNat 64 vo.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 q) (hb : BcHeap S M H F L) :
    DW live S Q 0x80004c10#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have base : ∀ R', Keeps [14, 15] R' R → (la + lb < 80 ∨ la < 20 ∨ lb < 20) →
      DW live S Q 0x80004c30#64 R' M := fun R' hk' hc =>
    rm_base hlive cx hk (st.keeps (hk'.mono (by decide)) (hk'.get 2))
      ⟨(hk'.get 19).trans kp.k19, (hk'.get 23).trans kp.k23, (hk'.get 24).trans kp.k24,
        (hk'.get 25).trans kp.k25, (hk'.get 26).trans kp.k26, (hk'.get 27).trans kp.k27⟩
      huL hvL hla hlb hla1 hlb1 hN (by omega) h0 ((hk'.get 22).trans h22)
      ((hk'.get 20).trans h20) ((hk'.get 21).trans h21) ((hk'.get 18).trans h18)
      ((hk'.get 9).trans h9) hb
  have kara : ∀ R', Keeps [14, 15] R' R → 80 ≤ la + lb → 20 ≤ la → 20 ≤ lb →
      DW live S Q 0x80004db0#64 R' M := fun R' hk' c1 c2 c3 =>
    hkara R' M H F (st.keeps (hk'.mono (by decide)) (hk'.get 2))
      ⟨(hk'.get 19).trans kp.k19, (hk'.get 23).trans kp.k23, (hk'.get 24).trans kp.k24,
        (hk'.get 25).trans kp.k25, (hk'.get 26).trans kp.k26, (hk'.get 27).trans kp.k27⟩ c1 c2 c3 h0
      ((hk'.get 22).trans h22) ((hk'.get 20).trans h20) ((hk'.get 21).trans h21)
      ((hk'.get 18).trans h18) ((hk'.get 9).trans h9) hb
  bc_run hlive hS [h16, h22, h11, h13, toInt_ofNat_small, sxw_ofNat] at 0x80004c30 0x80004c14
  · intro hc
    exact base R (Keeps.refl _ _) (Or.inl (by omega))
  intro hc
  bc_run hlive hS [h16, h22, h11, h13, toInt_ofNat_small, sxw_ofNat, sra80_31, quarter80] at
    0x80004c30 0x80004db0 0x80004da8
  · intro hc2
    bc_run hlive hS [h13, toInt_ofNat_small, sxw_ofNat] at 0x80004c30 0x80004db0
    · intro hc3
      exact base _ (by keeps_tac Keeps.refl _ _) (Or.inr (Or.inr (by omega)))
    · intro hc3
      exact kara _ (by keeps_tac Keeps.refl _ _) (by omega) (by omega) (by omega)
  intro hc2
  bc_run hlive hS [h11, toInt_ofNat_small, sxw_ofNat, quarter80] at 0x80004c30 0x80004db0
  · intro hc3
    exact kara _ (by keeps_tac Keeps.refl _ _) (by omega) (by omega) (by omega)
  · intro hc3
    exact base _ (by keeps_tac Keeps.refl _ _) (Or.inr (Or.inl (by omega)))

/-- **The entry** at `0x80004bd0`: the prologue, then the threshold test. -/
theorem rm_entry {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M L uo.rep vo.rep la lb q sp W)
    (hkara : RmKara live S Q R0 M L uo vo la lb q sp W)
    (ha : RmArgs M L uo vo la lb) (hb : BcHeap S M H F L)
    (h10 : R0 10 = BitVec.ofNat 64 uo.rep.p) (h11 : R0 11 = BitVec.ofNat 64 la)
    (h12 : R0 12 = BitVec.ofNat 64 vo.rep.p) (h13 : R0 13 = BitVec.ofNat 64 lb)
    (h14 : R0 14 = BitVec.ofNat 64 q) :
    DW live S Q 0x80004bd0#64 R0 M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hmb := ha.mulBase
  have h2 := cx.sp0
  have hN := ha.size
  bc_run hlive hS [] at 0x80004bd4
  apply st_80004bd4 hlive
  · bsimp []; bc_addr
  · bsimp []; intro b hb; have := of_mem_accAddrs hb
    exact cx.mulBase b (by simp only [mulBaseAddr]; omega) (by simp only [mulBaseAddr]; omega)
  simp only [mulBaseAddr] at hmb
  bsimp [hmb]
  bc_run hlive hS [h2, h10, h11, h12, h13, h14, word_sub192] at 0x80004c10
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have sv := ((((((((SavedWords.nil M (sp - 192) R0).store 9 168).store 18 160).store 20 144).store
    21 136).store 22 128).store 1 184).store 8 176).storeAway (a := sp - 192) (w := 8)
    (BitVec.ofNat 64 uo.rep.p) fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  refine rm_disp hlive cx hk hkara
    { r2 := by bsimp [], saved := sv, regs := by keeps_tac Keeps.refl _ _
      out := fun a _ _ hf => by
        simp only [frameIn] at hf
        repeat rw [imgM_store_miss _ _ (by omega)] }
    ⟨by bsimp [], by bsimp [], by bsimp [], by bsimp [], by bsimp [], by bsimp []⟩
    ha.mu ha.mv ha.ul ha.vl ha.ul1 ha.vl1 hN (ldv_store_hit _ _ _) (by bsimp [])
    (by bsimp [h11]) (by bsimp [h13]) (by bsimp [h11, h13, addw_ofNat (show la + lb < 2 ^ 31 by omega)])
    (by bsimp [h11]) (by bsimp [h13]) (by bsimp [h12]) (by bsimp [h14])
    (hb.out_frame (P := fun a => frameIn sp W a) (fun a ha => by
      simp only [frameIn] at ha
      repeat rw [imgM_store_miss _ _ (by omega)]) fun a ha => by
        simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha ⊢; omega)

end Dc.Mach
