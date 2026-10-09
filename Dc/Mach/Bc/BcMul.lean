import Dc.Mach.Bc.KaraCase

/-!
# `bc_multiply` (`lib/number.c`, `0x8000573c`)

```
8000573c addi sp,sp,-96 ; 80005740 sd s5,40(sp) ; 80005744 mv s5,a1 ; 80005748 lw a4,8(a0)
8000574c lw a5,8(s5) ; 80005750 lw a1,4(a0) ; 80005754 sd s4,48(sp) ; 80005758 lw s4,4(s5)
8000575c sd s1,72(sp) ; 80005760 sd s2,64(sp) ; 80005764 sd s6,32(sp) ; 80005768 sd ra,88(sp)
8000576c sd s0,80(sp) ; 80005770 sd s3,56(sp) ; 80005774 mv s2,a2 ; 80005778 addw a1,a1,a4
8000577c addw s6,a4,a5 ; 80005780 addw s4,s4,a5 ; 80005784 mv s1,a3 ; 80005788 blt a5,a3,80005790
8000578c mv s1,a5 ; 80005790 sext.w a5,s1 ; 80005794 bge a5,a4,8000579c ; 80005798 mv s1,a4
8000579c sext.w a5,s1 ; 800057a0 bge s6,a5,800057a8 ; 800057a4 mv s1,s6
800057a8 addi a4,sp,24 ; 800057ac mv a3,s4 ; 800057b0 mv a2,s5 ; 800057b4 sd a1,8(sp)
800057b8 sd a0,0(sp) ; 800057bc jal _bc_rec_mul
800057c0 ld a0,0(sp) ; 800057c4 ld s0,24(sp) ; 800057c8 ld a1,8(sp) ; 800057cc lw a3,0(s5)
800057d0 lw a2,0(a0) ; 800057d4 ld a5,24(s0) ; 800057d8 addw a4,a1,s4 ; 800057dc sub a2,a2,a3
800057e0 addiw a4,a4,1 ; 800057e4 snez a2,a2 ; 800057e8 subw a4,a4,s6 ; 800057ec sw a2,0(s0)
800057f0 sw s1,8(s0) ; 800057f4 sw a4,4(s0) ; 800057f8 sd a5,32(s0) ; 800057fc lbu a3,0(a5)
80005800 mv s3,s1 ; 80005804 li a2,1 ; 80005808 bnez a3,80005828
8000580c bge a2,a4,80005828 ; 80005810 addi a5,a5,1 ; 80005814 addiw a4,a4,-1
80005818 sd a5,32(s0) ; 8000581c sw a4,4(s0) ; 80005820 lbu a3,0(a5) ; 80005824 beqz a3,8000580c
80005828 auipc a4,0x17 ; 8000582c ld a4,1440(a4) (_zero_) ; 80005830 beq s0,a4,80005894
80005834 lw a3,4(s0) ; 80005838 addw a3,a3,s3 ; 8000583c mv a4,a3 ; 80005840 bgtz a3,8000584c
80005844 j 80005890 ; 80005848 beqz a4,80005894 ; 8000584c lbu a3,0(a5)
80005850 addiw a4,a4,-1 ; 80005854 addi a5,a5,1 ; 80005858 beqz a3,80005848
8000585c mv a0,s2 ; 80005860 jal bc_free_num ; 80005864 ld ra,88(sp) ; 80005868 sd s0,0(s2)
8000586c ld s0,80(sp) … 80005884 ld s6,32(sp) ; 80005888 addi sp,sp,96 ; 8000588c ret
80005890 bnez a3,8000585c ; 80005894 sw zero,0(s0) ; 80005898 j 8000585c
```

`_bc_rec_mul` multiplies all the digits of both operands into a new number of
`len1 + scale1 + len2 + scale2 + 1` digits; `bc_multiply` relabels it with
`len1 + len2 + 1` integer digits and the product scale (dropping the digits
past it), trims leading zeros (`ktrimLoop_8000580c`), makes a zero positive,
frees the old `*prod` and stores the product there.

- `MulCtx`: the stack window `W` (the 96-byte frame and `_bc_rec_mul`'s
  window below it), the result slot, the globals `_bc_rec_mul` reads.
- `MulArgs`: the operands, `_zero_` with room for `_bc_rec_mul`'s references.
- The result is `BinPostW`/`BinKW` (`AddSub.lean`) over the window `W`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- `bc_multiply`'s fixed context: the stack window `W` (the 96-byte frame
and `_bc_rec_mul`'s window below it) above the heap, the result slot `q` off
the heap and apart from the window, the globals `_bc_rec_mul` reads, the
entry's `sp` and return address. -/
structure MulCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp q W : Nat) : Prop where
  frame : StackFrame S sp W
  above : heapEnd + W ≤ sp
  big : 320 ≤ W
  slot : PtrSlot S q
  slotOut : ∀ a, slotBytes q a → OutHeap a
  slotApart : q + 8 ≤ sp - W ∨ sp ≤ q
  mulBase : ∀ a, mulBaseAddr ≤ a → a < mulBaseAddr + 4 → S a
  consts : ∀ a, constBytes a → S a
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0

/-- The operands: two numbers of the heap with a digit each, `_zero_` of the
heap with room for the references `_bc_rec_mul` takes, `mul_base_digits` at
`80`, the product scale `k` an `int`. -/
structure MulArgs (M : Mem) (L : List NumObj) (x1 x2 z : NumObj) (k : Nat) : Prop where
  m1 : x1 ∈ L
  m2 : x2 ∈ L
  mz : z ∈ L
  p1 : 1 ≤ x1.rep.len + x1.rep.scale
  p2 : 1 ≤ x2.rep.len + x2.rep.scale
  size : x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale) < 2 ^ 30
  scale : k < 2 ^ 31
  zero : KZero M z (4 * (x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale)) + 8)
  mulBase : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80

/-- The registers `bc_multiply` changes before its epilogue. -/
abbrev mulAll : List Nat :=
  [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 28, 29, 30, 31]

/-- The registers free between the prologue and the epilogue. -/
abbrev mulTmp : List Nat :=
  [1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 28, 29, 30, 31]

/-- The prologue's saved registers (offsets from the lowered `sp`). -/
abbrev mulSlots : List (Nat × Nat) :=
  [(19, 56), (8, 80), (1, 88), (22, 32), (18, 64), (9, 72), (20, 48), (21, 40)]

/-- Inside `bc_multiply`: `sp` lowered by 96, the saved registers in the
frame, `s2` the slot, and off the heap only the window changed. -/
structure MulAt (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W : Nat) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 96)
  saved : SavedWords M (sp - 96) mulSlots R0
  r18 : R 18 = BitVec.ofNat 64 q
  regs : Keeps mulAll R R0
  out : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a

/-- `MulAt` through changes of the free registers. -/
theorem MulAt.keeps {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp q W : Nat}
    (st : MulAt S Mt0 M R0 R sp q W) (hk : Keeps mulTmp R' R) : MulAt S Mt0 M R0 R' sp q W :=
  { st with
    r2 := by rw [hk.get 2]; exact st.r2
    r18 := by rw [hk.get 18]; exact st.r18
    regs := (hk.mono (by decide)).trans st.regs }

/-- `MulAt` through memory changes off the saved words and, off the heap,
inside the window. -/
theorem MulAt.mem {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    (st : MulAt S Mt0 M R0 R sp q W)
    (hsv : ∀ a, sp - 96 + 32 ≤ a → a < sp - 96 + 96 → imgM M' a = imgM M a)
    (hm : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M' a = imgM M a) :
    MulAt S Mt0 M' R0 R sp q W :=
  { st with
    saved := st.saved.transport (lo := 32) (top := 96) (hag := fun a h1 h2 => hsv a h1 h2)
    out := fun a ha hf => (hm a ha hf).trans (st.out a ha hf) }

/-! ## The product's value -/

/-- The product scale `bc_multiply` computes. -/
abbrev mulScale (s1 s2 k : Nat) : Nat := min (s1 + s2) (max (max k s2) s1)

/-- The product relabelled: `len1 + len2 + 1` integer digits, scale `ps`,
the digits past it dropped, the sign `b`. -/
abbrev mulRep (o : NumRep) (b : Bool) (l ps : Nat) : NumRep :=
  { o with neg := b, len := l, scale := ps, ds := o.ds.take (l + ps) }

/-- The relabelled product's magnitude: `Num.mul`'s. -/
theorem mulRep_mag {o : NumRep} (hs : NumShape o) {b : Bool} {a1 a2 : Num} {l1 l2 ps : Nat}
    (hlen : o.len = l1 + a1.scale + (l2 + a2.scale) + 1) (hsc : o.scale = 0)
    (hval : dval o.ds = a1.mag * a2.mag) (hps : ps ≤ a1.scale + a2.scale) :
    dval (mulRep o b (l1 + l2 + 1) ps).ds = a1.mag * a2.mag / 10 ^ (a1.scale + a2.scale - ps) := by
  have e := dval_div_take o.ds hs.dig (l1 + l2 + 1 + ps)
  rw [hs.dsLen, hlen, hsc, hval,
    show l1 + a1.scale + (l2 + a2.scale) + 1 + 0 - (l1 + l2 + 1 + ps) = a1.scale + a2.scale - ps by
      omega] at e
  exact e.symm

/-! ## Stores into the product's struct -/

/-- `n_scale`, `n_len` and `n_value` (`= n_ptr`) rewritten: the number cut to
its first `l + ps` digits. -/
theorem NumAt.relabel {Mt : Mem} {o : NumRep} (h : NumAt Mt o) {l ps : Nat} {v1 v2 : BitVec 64}
    (hl : 1 ≤ l) (hle : l + ps ≤ o.len + o.scale)
    (h1 : v1.toNat % 2 ^ 32 = ps) (h2 : v2.toNat % 2 ^ 32 = l) :
    NumAt (writeLog (writeLog (writeLog Mt [(o.p + 8, 4, v1)]) [(o.p + 4, 4, v2)])
      [(o.p + 32, 8, BitVec.ofNat 64 o.val)])
      { o with len := l, scale := ps, ds := o.ds.take (l + ps) } := by
  have hs := h.shape
  have hsep := hs.sep; have hpl := hs.ptrLe; have hvh := hs.vHi; have hsz := hs.size
  have hshape : NumShape { o with len := l, scale := ps, ds := o.ds.take (l + ps) } :=
    { hs with
      dsLen := by simp only [List.length_take, hs.dsLen]; omega
      dig := fun e he => hs.dig e (List.mem_of_mem_take he)
      size := by simp only; omega
      vHi := by simp only; omega
      sep := by simp only; omega
      emptyScale := fun h => absurd h (by simp only; omega)
      emptyIn := fun h => absurd h (by simp only; omega) }
  refine ⟨hshape, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega),
      ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega),
      ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.sign
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]
    exact ldv_lw_hitN _ rfl (k := l) h2 (by omega)
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega),
      ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]
    exact ldv_lw_hitN _ rfl (k := ps) h1 (by omega)
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega),
      ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega),
      ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.refs
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega),
      ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega),
      ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.ptr
  · exact ldv_store_hit _ _ _
  · simp only at hi ⊢
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega), h.digit i (by omega), getD_take hi]

/-- The relabelling on the heap's head object. -/
theorem BcHeap.relabel {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (x :: L)) {l ps a : Nat} {v1 v2 : BitVec 64}
    (ha : x.rep.p = a) (hl : 1 ≤ l) (hle : l + ps ≤ x.rep.len + x.rep.scale)
    (h1 : v1.toNat % 2 ^ 32 = ps) (h2 : v2.toNat % 2 ^ 32 = l) :
    BcHeap S (writeLog (writeLog (writeLog Mt [(a + 8, 4, v1)]) [(a + 4, 4, v2)])
      [(a + 32, 8, BitVec.ofNat 64 x.rep.val)]) H F
      ({ x with rep := { x.rep with len := l, scale := ps, ds := x.rep.ds.take (l + ps) } } :: L) := by
  subst ha
  have h' : BcHeap S Mt H F ([] ++ x :: L) := h
  have hx : x ∈ x :: L := List.mem_cons_self
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  have hsp := hxb.sPay; have hsz := hxb.sSz; have hdf := hxb.dFit; have hdl := hxb.dLo
  have hfin : x.sb.fin = x.sb.pay + x.sb.sz := rfl
  have hin : ∀ a, x.rep.p + 4 ≤ a ∧ a < x.rep.p + 40 → x.sb.In a := fun a ha => ⟨by omega, by omega⟩
  have hsep := hn.shape.sep; have hpl := hn.shape.ptrLe
  exact BcHeap.update h' rfl rfl rfl ⟨hxb.sLive, hxb.dLive, hxb.sPay, hxb.sSz, hxb.dPay,
      by simp only; omega, by simp only; omega⟩
    (hn.relabel hl hle h1 h2) (P := fun a => x.rep.p + 4 ≤ a ∧ a < x.rep.p + 40)
    (fun a ha => by
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
        imgM_store_miss _ _ (by omega)])
    fun a ha => h'.sb_writeOK (hin a ha)

/-- A struct of the heap is not `_zero_`'s: their payloads differ. -/
theorem BcHeap.p_ne {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {x z : NumObj} (h : BcHeap S Mt H F (x :: L)) (hz : z ∈ L) :
    x.rep.p ≠ z.rep.p := by
  have hx := h.blocks x List.mem_cons_self
  have hzb := h.blocks z (List.mem_cons_of_mem _ hz)
  have hd := h.distinct
  rw [List.nodup_append] at hd
  have hne : x.sb ≠ z.sb := by
    intro e
    have hd2 : (x.blocks ++ objBlocks L).Nodup := hd.2.1
    exact (List.nodup_append.mp hd2).2.2 x.sb x.sb_mem_blocks z.sb (mem_objBlocks hz) e
  intro e
  have hsx := hx.sSz; have hsz := hzb.sSz
  rw [hx.sPay, hzb.sPay] at e
  exact live_apart h.heap hx.sLive hzb.sLive hne (a := x.sb.pay)
    ⟨Nat.le_refl _, by simp only [Blk.fin, Blk.pay] at hsx ⊢; omega⟩
    ⟨by omega, by simp only [Blk.fin, Blk.pay] at hsx hsz e ⊢; omega⟩

/-! ## The tail: `bc_free_num(prod)`, the store, the epilogue -/

/-- The end of the epilogue at `0x80005878`: `s3`–`s6` back, the return. -/
theorem bmul_epi2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 L : List NumObj} {xr y : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : MulCtx S R0 sp q W) (hk : BinKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (sv : SavedWords M (sp - 96) mulSlots R0)
    (h1 : R 1 = R0 1) (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (h8 : R 8 = R0 8) (h9 : R 9 = R0 9)
    (h18 : R 18 = R0 18) (hkp : Keeps mulAll R R0) (hS : HeapOwn S)
    (hp : BinPostW S Mt0 M H F L1 L2 xr q sp W n L y) :
    DW live S Q 0x80005878#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hal := cx.al
  bc_run hlive hS [h1, h2, sv.get 19 56, sv.get 20 48, sv.get 21 40, sv.get 22 32]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk.ret _ _ H F L y (Keeps.unwind (saved := [1, 2, 8, 9, 18, 19, 20, 21, 22]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp)) hp
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, h1, h8, h9, h18, sv.get 19 56, sv.get 20 48, sv.get 21 40, sv.get 22 32]
  all_goals (try (congr 1; omega))

/-- The epilogue at `0x80005864` after `bc_free_num`: the product into the
slot, `ra`, `s0`–`s2` back. -/
theorem bmul_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 L : List NumObj} {xr y : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : MulCtx S R0 sp q W) (hk : BinKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (sv : SavedWords M (sp - 96) mulSlots R0)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (h8 : R 8 = BitVec.ofNat 64 y.sb.pay)
    (h18 : R 18 = BitVec.ofNat 64 q) (hkp : Keeps mulAll R R0) (hS : HeapOwn S)
    (hp : BinPostW S Mt0 (writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)]) H F L1 L2 xr q sp W n L y) :
    DW live S Q 0x80005864#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hap := cx.slotApart
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have sv' := sv.transport (lo := 32) (top := 96)
    (M' := writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)])
    (hag := fun a h1 h2' => imgM_store_miss _ _ (by omega))
  bc_run hlive hS [h2, h8, h18, sv.get 1 88] at 0x80005878
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hq.acc | skip
  exact bmul_epi2 hlive cx hk sv' (by bsimp []) (by bsimp [h2])
    (by bsimp []; exact sv'.get 8 80) (by bsimp []; exact sv'.get 9 72)
    (by bsimp []; exact sv'.get 18 64)
    ((by keeps_tac Keeps.refl _ _ : Keeps mulAll _ R).trans hkp) hS hp

/-- The slot keeps its word while only the heap and the window change. -/
theorem ResSlot.of_mulAt {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    {L1 : List NumObj} {x : NumObj} (cx : MulCtx S R0 sp q W) (st : MulAt S Mt0 M R0 R sp q W)
    (h : ResSlot Mt0 L1 x q) : ResSlot M L1 x q := by
  have hap := cx.slotApart
  refine ⟨h.refs, ?_, h.noView⟩
  rw [ldv_congr .ld fun j hj => st.out _ (cx.slotOut _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩)
    (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
  exact h.word

/-- The tail at `0x8000585c`: `bc_free_num(prod)`, then the epilogue. -/
theorem bmul_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj} {xr y : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : MulCtx S R0 sp q W) (hk : BinKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (st : MulAt S Mt0 M R0 R sp q W) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (h8 : R 8 = BitVec.ofNat 64 y.sb.pay)
    (hnum : y.rep.num = n) (hnorm : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1)
    (hyo : y.Owns) :
    DW live S Q 0x8000585c#64 R M := by
  have hr := ResSlot.of_mulAt cx st hr0
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hap := cx.slotApart
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.r2; have h18 := st.r18
  have hxn := hb.nums xr (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have hxp : heapStart ≤ xr.rep.p ∧ xr.rep.p + 16 ≤ heapEnd :=
    ⟨hxn.shape.pLo, by have := hxn.shape.pHi; omega⟩
  bc_run hlive hS [h18, h2] at 0x800048c0
  have hsf' : StackFrame S (sp - 96) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  have e : FreeEntry S M H F (y :: L1) L2 xr q (sp - 96) :=
    FreeEntry.of_slot hb hr (hr.noView_cons hb hyo) hq cx.slotOut hsf' (by simp only [heapEnd]; omega)
      (by omega)
  have hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a :=
    fun a ha _ hf => st.out a ha hf
  refine bc_free_num_spec hlive e _ (by bsimp [h18]) (by bsimp [h2]) (by bsimp [])
    ⟨fun hx2 R1 Mt1 hk1 hb1 _ hmo => ?_, fun hx1 R1 Mt1 H1 hk1 hrp => ?_⟩
  · bsimp []
    have sv := st.saved.transport (lo := 32) (top := 96) (M' := Mt1) (hag := fun a h1 h2' =>
      hmo a fun hc => by
        rcases hc with hc | hc
        · simp only [refsBytes, heapStart, heapEnd] at hc hxp; omega
        · simp only [slotBytes] at hc; omega)
    exact bmul_epi hlive cx hk sv (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8])
      (by rw [hk1.get 18]; bsimp [h18])
      (((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps mulAll _ R)).trans st.regs) hS
      (binPost_dec cx.slotOut hout hb1 hmo hxp hnum hnorm hpos hrefs hyo hx2)
  · bsimp []
    have sv := st.saved.transport (lo := 32) (top := 96) (M' := Mt1) (hag := fun a h1 h2' =>
      hrp.frame a fun hc => by
        have hout : OutHeap a := by
          simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
        rcases hc with hc | hc | hc | hc | hc
        · exact OutHeap.not_alloc hb.heap hout hc
        · exact hout.1 (live_in_heap hb.heap (hb.blocks xr (List.mem_cons_of_mem _
            (List.mem_append_right _ List.mem_cons_self))).sLive hc)
        · simp only [slotBytes] at hc; omega
        · simp only [frameIn] at hc; omega
        · exact hout.2.2 hc)
    exact bmul_epi hlive cx hk sv (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8])
      (by rw [hk1.get 18]; bsimp [h18])
      (((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps mulAll _ R)).trans st.regs)
      (fun a h1 h2 => hrp.heap.heap.own a h1 h2)
      (binPost_rel cx.slotOut hout hb hrp cx.above ⟨by omega, by omega⟩ hnum hnorm hpos hrefs hyo hx1)

/-! ## `bc_is_zero (pval)`, inlined -/

/-- The digit scan at `0x8000584c`: the first `i` digits zero, `k + 1` left,
`a5` at digit `i`. All digits zero reach `0x80005894`; a nonzero digit
`0x8000585c`. -/
theorem bmul_scan {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {o : NumRep} {Rb : Nat → BitVec 64} (hS : HeapOwn S) (hn : NumAt M o)
    (hz : ∀ R', Keeps [13, 14, 15] R' Rb → (∀ j, j < o.len + o.scale → o.ds.getD j 0 = 0) →
      DW live S Q 0x80005894#64 R' M)
    (hnz : ∀ R', Keeps [13, 14, 15] R' Rb → dval o.ds ≠ 0 → DW live S Q 0x8000585c#64 R' M) :
    ∀ k i (R : Nat → BitVec 64), o.len + o.scale = i + k + 1 → (∀ j, j < i → o.ds.getD j 0 = 0) →
      Keeps [13, 14, 15] R Rb → R 14 = BitVec.ofNat 64 (k + 1) →
      R 15 = BitVec.ofNat 64 (o.val + i) → DW live S Q 0x8000584c#64 R M := by
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
    bc_run hlive hS [hc, hp, hl] at 0x80005848 0x8000585c
    all_goals first | exact acc_heap hS (by omega) (by omega) | skip
    · intro h0
      bsimp [ofNat_eq_zero_iff (show o.ds.getD i 0 < 2 ^ 64 by omega)] at h0
      bc_run hlive hS [hc, hp] at 0x80005894 0x8000584c
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
    bc_run hlive hS [hc, hp, hl] at 0x80005848 0x8000585c
    all_goals first | exact acc_heap hS (by omega) (by omega) | skip
    · intro h0
      bsimp [ofNat_eq_zero_iff (show o.ds.getD i 0 < 2 ^ 64 by omega)] at h0
      bc_run hlive hS [hc, hp] at 0x80005894 0x8000584c
      refine ih (i + 1) _ (by omega) (fun j hj => ?_) (by keeps_tac kk)
        (by bsimp [show k + 1 + 1 - 1 = k + 1 by omega]) (by bsimp [Nat.add_assoc])
      rcases Nat.lt_or_ge j i with h1 | h1
      · exact hz0 j h1
      · rw [show j = i by omega]; exact h0
    · intro h0
      bsimp [ofNat_eq_zero_iff (show o.ds.getD i 0 < 2 ^ 64 by omega)] at h0
      exact hnz _ (by keeps_tac kk) (hnz' i (by omega) h0)

/-- A zero made positive at `0x80005894`, then the tail. -/
theorem bmul_pos {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj} {xr y : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : MulCtx S R0 sp q W) (hk : BinKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (st : MulAt S Mt0 M R0 R sp q W) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (h8 : R 8 = BitVec.ofNat 64 y.sb.pay)
    (hnum : ({ y.rep with neg := false } : NumRep).num = n) (hnorm : y.rep.Norm)
    (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x80005894#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
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
  bc_run hlive hS [h8] at 0x8000585c
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  exact bmul_tail hlive cx hk
    (st.mem (fun a h1 h2 => imgM_store_miss _ _ (by omega)) fun a ha _ => imgM_store_miss _ _ (by
      simp only [OutHeap, heapStart, heapEnd] at ha; omega))
    hb' hr0 (by bsimp [h8]) hnum hnorm hpos hrefs hyo

/-- The zero test from `0x80005828`: the product (not `_zero_`) is scanned
from `a5 = n_value`; a zero is made positive. -/
theorem bmul_zero {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj} {xr y z : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : MulCtx S R0 sp q W) (hk : BinKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (st : MulAt S Mt0 M R0 R sp q W) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hz : z ∈ L1 ++ xr :: L2)
    (hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p)
    (h8 : R 8 = BitVec.ofNat 64 y.sb.pay) (h19 : R 19 = BitVec.ofNat 64 y.rep.scale)
    (h15 : R 15 = BitVec.ofNat 64 y.rep.val)
    (hnum : dval y.rep.ds ≠ 0 → y.rep.num = n)
    (hnum0 : dval y.rep.ds = 0 → ({ y.rep with neg := false } : NumRep).num = n)
    (hnorm : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x80005828#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn := hb.nums y List.mem_cons_self
  num_facts hn
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hzn := hb.nums z (List.mem_cons_of_mem _ hz)
  num_facts hzn
  have hne := hb.p_ne hz
  rw [hyp] at hne
  have hne' : ¬ BitVec.ofNat 64 y.sb.pay = BitVec.ofNat 64 z.rep.p := fun e =>
    hne ((ofNat_eq_iff (by omega) (by omega)).mp e)
  have hl : ldv .lw M (y.sb.pay + 4) = BitVec.ofNat 64 y.rep.len := by rw [← hyp]; exact hn.len
  have hzg' : ldv .ld M 2147601864 = BitVec.ofNat 64 z.rep.p := hzg
  have hdl := hn.shape.dsLen
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hcst : ∀ b ∈ accAddrs 2147601864 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  have hyp1 := hn.shape.pLo; have hyp2 := hn.shape.pHi; have hyp3 := hn.shape.pAl
  rw [hyp] at hyp1 hyp2 hyp3
  simp only [heapStart, heapEnd] at hyp1 hyp2
  bc_run hlive hS [h8, h15, h19, hzg', hne', hl,
    addw_ofNat (show y.rep.len + y.rep.scale < 2 ^ 31 by omega)] at 0x80005840
  all_goals try (exact hcst)
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr, zeroAddr] at *; omega)
  bc_run hlive hS [h8, h15, h19, hl, addw_ofNat (show y.rep.len + y.rep.scale < 2 ^ 31 by omega)]
    at 0x8000584c 0x80005890
  all_goals try (exact acc_heap hS (by omega) (by omega))
  · intro _
    refine bmul_scan hlive hS hn (fun R' kk hall => ?_) (fun R' kk hnz => ?_)
      (y.rep.len + y.rep.scale - 1) 0 _ (by omega) (fun j hj => absurd hj (Nat.not_lt_zero _))
      (Keeps.refl _ _) (by bsimp []; congr 1; omega) (by bsimp [h15])
    · exact bmul_pos hlive cx hk (st.keeps ((kk.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) hb hr0 (by rw [kk.get 8 (by decide)]; bsimp [h8])
        (hnum0 ((dval_eq_zero_iff _).2 fun j hj => hall j (by omega))) hnorm hpos hrefs hyo
    · exact bmul_tail hlive cx hk (st.keeps ((kk.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) hb hr0 (by rw [kk.get 8 (by decide)]; bsimp [h8])
        (hnum hnz) hnorm hpos hrefs hyo
  · intro hc
    exfalso
    rw [toInt_ofNat_small (show y.rep.len + y.rep.scale < 2 ^ 63 by omega)] at hc
    simp at hc
    omega

/-! ## The leading-zero trim, inlined -/

/-- After the trim at `0x80005828`: `j` leading zeros dropped. -/
theorem bmul_trimmed {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W j : Nat} {L1 L2 : List NumObj} {xr y z : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : MulCtx S R0 sp q W) (hk : BinKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (st : MulAt S Mt0 M R0 R sp q W)
    (hb : BcHeap S M H F ({ y with rep := y.rep.drop j } :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hz : z ∈ L1 ++ xr :: L2)
    (hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p) (hj : lzCount (y.rep.len - 1) y.rep.ds = j)
    (h8 : R 8 = BitVec.ofNat 64 y.sb.pay) (h19 : R 19 = BitVec.ofNat 64 y.rep.scale)
    (h15 : R 15 = BitVec.ofNat 64 (y.rep.val + j))
    (hnum : dval y.rep.ds ≠ 0 → y.rep.num = n)
    (hnum0 : dval y.rep.ds = 0 → ({ y.rep with neg := false } : NumRep).num = n)
    (hdl : y.rep.ds.length = y.rep.len + y.rep.scale)
    (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x80005828#64 R M := by
  obtain ⟨hn, hnorm, -, hpos'⟩ := NumRep.rmLeadingZeros_spec hdl hpos
  have e : y.rep.rmLeadingZeros = y.rep.drop j := by rw [NumRep.rmLeadingZeros, hj]
  rw [e] at hn hnorm hpos'
  have em : dval (y.rep.drop j).ds = dval y.rep.ds := congrArg Dc.Num.mag hn
  refine bmul_zero (y := { y with rep := y.rep.drop j }) hlive cx hk st hb hr0 hz hzg h8 h19 h15
    (fun h0 => hn.trans (hnum (em ▸ h0))) (fun h0 => ?_) hnorm hpos' hrefs hyo
  rw [← hnum0 (em ▸ h0)]
  show (⟨false, dval (y.rep.drop j).ds, (y.rep.drop j).scale⟩ : Dc.Num) = ⟨false, dval y.rep.ds, y.rep.scale⟩
  rw [em]; rfl

/-- The trim from `0x800057fc`: the first digit, `s3 = s1`, then the loop
`ktrimLoop_8000580c`. -/
theorem bmul_trim {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj} {xr y z : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : MulCtx S R0 sp q W) (hk : BinKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (st : MulAt S Mt0 M R0 R sp q W) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hz : z ∈ L1 ++ xr :: L2)
    (hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p)
    (h8 : R 8 = BitVec.ofNat 64 y.sb.pay) (h9 : R 9 = BitVec.ofNat 64 y.rep.scale)
    (h14 : R 14 = BitVec.ofNat 64 y.rep.len) (h15 : R 15 = BitVec.ofNat 64 y.rep.val)
    (hnum : dval y.rep.ds ≠ 0 → y.rep.num = n)
    (hnum0 : dval y.rep.ds = 0 → ({ y.rep with neg := false } : NumRep).num = n)
    (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x800057fc#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn := hb.nums y List.mem_cons_self
  num_facts hn
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hdl := hn.shape.dsLen
  have hl0 := hn.lbu (i := 0) (by omega)
  have hd := hn.getD_lt 0
  simp only [Nat.add_zero] at hl0 hd
  have hr8 : R 8 = BitVec.ofNat 64 y.rep.p := by rw [h8, hyp]
  have hb0 : BcHeap S M H F ([] ++ { y with rep := y.rep.drop 0 } :: (L1 ++ xr :: L2)) := by
    rw [NumRep.drop_zero]; exact hb
  have hmo0 : MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M M := fun a _ => rfl
  have hfr : ∀ {M' : Mem}, MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M' M →
      MulAt S Mt0 M' R0 R sp q W := fun hmo => st.mem
    (fun a h1 h2 => hmo a fun h => by
      have hsf := cx.frame; have := hsf.lo; have hab := cx.above; have hW := cx.big
      simp only [heapStart, heapEnd] at h hab; omega)
    fun a ha _ => hmo a fun h => ha.1 h
  have hzg' : ∀ {M' : Mem}, MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M' M →
      ldv .ld M' zeroAddr = BitVec.ofNat 64 z.rep.p := fun hmo => by
    rw [ldv_congr .ld fun j hj => hmo _ fun h => by
      simp only [heapStart, heapEnd, zeroAddr, widthOfM] at h hj; omega]
    exact hzg
  bc_run hlive hS [h15, hl0, h9, h14] at 0x8000580c 0x80005828
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro hne
    bv_nat at hne
    rw [Nat.mod_eq_of_lt (by omega)] at hne
    exact bmul_trimmed hlive cx hk ((hfr hmo0).keeps (by keeps_tac Keeps.refl _ _))
      (by simpa only [List.nil_append] using hb0) hr0 hz hzg
      (lzCount_eq _ _ _ (by omega) (by omega) (fun i hi => absurd hi (by omega)) (.inr hne))
      (by bsimp [h8]) (by bsimp [h9]) (by bsimp [h15]) hnum hnum0 hdl hpos hrefs hyo
  · intro he
    bv_nat at he
    rw [Classical.not_not, Nat.mod_eq_of_lt (by omega)] at he
    refine ktrimLoop_8000580c hlive hS (by bsimp [hr8]) (fun R' M' j kk hb' hj hmo h15' => ?_) _ 0 _ _
      rfl (by omega) (Keeps.refl _ _) hb0 hmo0 (by bsimp [h15]) (by bsimp [h14]) (by bsimp [])
      fun i hi => by rw [show i = 0 by omega]; exact he
    exact bmul_trimmed hlive cx hk ((hfr hmo).keeps ((kk.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))
      (by simpa only [List.nil_append] using hb') hr0 hz (hzg' hmo) hj
      (by rw [kk.get 8 (by decide)]; bsimp [h8]) (by rw [kk.get 19 (by decide)]; bsimp [h9]) h15'
      hnum hnum0 hdl hpos hrefs hyo

/-! ## After `_bc_rec_mul` -/

/-- The relabelled product (sign `b`, `l` integer digits, scale `ps`). -/
abbrev mulObj (y : NumObj) (b : Bool) (l ps : Nat) : NumObj :=
  { y with rep := { y.rep with neg := b, len := l, scale := ps, ds := y.rep.ds.take (l + ps) } }

/-- The relabelled product denotes `n`: with its sign if nonzero, positive
if zero. -/
structure MulNum (y : NumObj) (b : Bool) (l ps : Nat) (n : Num) : Prop where
  nz : dval (y.rep.ds.take (l + ps)) ≠ 0 → (mulObj y b l ps).rep.num = n
  z : dval (y.rep.ds.take (l + ps)) = 0 → (mulObj y false l ps).rep.num = n

/-- `_bc_rec_mul`'s product relabelled denotes `Num.mul`. -/
theorem MulNum.of_prod {y : NumObj} {u v : NumRep} {k : Nat} (hs : NumShape y.rep)
    (hu : u.ds.length = u.len + u.scale) (hv : v.ds.length = v.len + v.scale)
    (hy : KProd u v (u.len + u.scale) (v.len + v.scale) y) :
    MulNum y (u.neg != v.neg) (u.len + v.len + 1) (mulScale u.scale v.scale k) (Num.mul u.num v.num k) := by
  have hps : mulScale u.scale v.scale k ≤ u.scale + v.scale := by simp only [mulScale]; omega
  have hval : dval y.rep.ds = u.num.mag * v.num.mag := by
    have e := hy.val
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at e
    exact e
  have hm := mulRep_mag (b := u.neg != v.neg) (a1 := u.num) (a2 := v.num)
    (l1 := u.len) (l2 := v.len) hs (by rw [hy.len]; rfl) hy.scale hval hps
  have hmag : dval (y.rep.ds.take (u.len + v.len + 1 + mulScale u.scale v.scale k)) =
      (Num.mul u.num v.num k).mag := by
    rw [num_mul_mag]
    refine hm.trans ?_
    show _ / 10 ^ (u.scale + v.scale - _) = _ / 10 ^ (u.scale + v.scale - _)
    congr 2
    simp only [mulScale, NumRep.num]; omega
  have hsc : (Num.mul u.num v.num k).scale = mulScale u.scale v.scale k := by
    rw [num_mul_scale]; simp only [mulScale, NumRep.num]; omega
  have hneg : (Num.mul u.num v.num k).neg =
      if (Num.mul u.num v.num k).mag == 0 then false else (u.neg != v.neg) := rfl
  have key : ∀ (N : Dc.Num) (b : Bool) (m s : Nat), N.neg = b → N.mag = m → N.scale = s →
      (⟨b, m, s⟩ : Dc.Num) = N := by
    rintro ⟨_, _, _⟩ b m s rfl rfl rfl; rfl
  refine ⟨fun h0 => key _ _ _ _ ?_ hmag.symm hsc, fun h0 => key _ _ _ _ ?_ hmag.symm hsc⟩
  · rw [hneg, ← hmag]
    simp only [beq_iff_eq, h0, if_false]
  · rw [hneg, ← hmag, h0]; rfl

/-- The four stores at `0x800057ec`: sign, `n_scale`, `n_len`, `n_value`;
then the trim. -/
theorem bmul_store {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W l ps : Nat} {L1 L2 : List NumObj}
    {xr y z : NumObj} {H : Heap} {F : List Blk} {b : Bool} {n : Num}
    (cx : MulCtx S R0 sp q W) (hk : BinKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (st : MulAt S Mt0 M R0 R sp q W) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hz : z ∈ L1 ++ xr :: L2)
    (hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p)
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyv : y.rep.val = y.rep.ptr)
    (hl : 1 ≤ l) (hle : l + ps ≤ y.rep.len + y.rep.scale)
    (hnum : MulNum y b l ps n)
    (h8 : R 8 = BitVec.ofNat 64 y.sb.pay) (h12 : R 12 = signWord b)
    (h9 : R 9 = BitVec.ofNat 64 ps) (h14 : R 14 = BitVec.ofNat 64 l)
    (h15 : R 15 = BitVec.ofNat 64 y.rep.val) :
    DW live S Q 0x800057ec#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hyn := hb.nums y List.mem_cons_self
  num_facts hyn
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have yp1 := hyn.shape.pLo; have yp2 := hyn.shape.pHi; have yp3 := hyn.shape.pAl
  rw [hyp] at yp1 yp2 yp3
  simp only [heapStart, heapEnd] at yp1 yp2
  bc_run hlive hS [h8, h12, h9, h14, h15] at 0x800057fc
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  have hb1 := BcHeap.setSign (L1 := []) hb b (signWord_toNat b)
  rw [hyp] at hb1
  simp only [List.nil_append] at hb1
  have hb2 := hb1.relabel (l := l) (ps := ps) hyp hl hle (toNat_ofNat_mod32 (by omega))
    (toNat_ofNat_mod32 (by omega))
  have hb3 : BcHeap S (writeLog (writeLog (writeLog (writeLog M [(y.sb.pay, 4, signWord b)])
      [(y.sb.pay + 8, 4, BitVec.ofNat 64 ps)]) [(y.sb.pay + 4, 4, BitVec.ofNat 64 l)])
      [(y.sb.pay + 32, 8, BitVec.ofNat 64 y.rep.val)]) H F
      (mulObj y b l ps :: (L1 ++ xr :: L2)) := hb2
  have hmo : ∀ a, (a < y.sb.pay ∨ y.sb.pay + 40 ≤ a) →
      imgM (writeLog (writeLog (writeLog (writeLog M [(y.sb.pay, 4, signWord b)])
        [(y.sb.pay + 8, 4, BitVec.ofNat 64 ps)]) [(y.sb.pay + 4, 4, BitVec.ofNat 64 l)])
        [(y.sb.pay + 32, 8, BitVec.ofNat 64 y.rep.val)]) a = imgM M a := fun a ha => by
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  exact bmul_trim (y := mulObj y b l ps) hlive cx hk
    (st.mem (fun a h1 h2 => hmo a (.inr (by omega)))
      fun a ha _ => hmo a (by simp only [OutHeap, heapStart, heapEnd] at ha; omega))
    hb3 hr0 hz
    (by rw [ldv_congr .ld fun j hj => hmo _ (by simp only [zeroAddr, widthOfM] at hj ⊢; omega)]; exact hzg)
    (by bsimp [h8]) (by bsimp [h9]) (by bsimp [h14]) (by bsimp [h15])
    hnum.nz hnum.z hl hyr hyo

/-- After `_bc_rec_mul` at `0x800057c0`: the operands' signs, the product's
`n_ptr`, `len1 + len2 + 1`. -/
theorem bmul_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W k : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr y z : NumObj} {H : Heap} {F : List Blk}
    (cx : MulCtx S R0 sp q W)
    (hk : BinKW live S Q R0 Mt0 L1 L2 xr q sp W (Num.mul x1.rep.num x2.rep.num k))
    (st : MulAt S Mt0 M R0 R sp q W) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hx1 : x1 ∈ L1 ++ xr :: L2) (hx2 : x2 ∈ L1 ++ xr :: L2)
    (hz : z ∈ L1 ++ xr :: L2) (hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p)
    (hy : KProd x1.rep x2.rep (x1.rep.len + x1.rep.scale) (x2.rep.len + x2.rep.scale) y)
    (hsz : x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale) + 1 < 2 ^ 30)
    (s0 : ldv .ld M (sp - 96) = BitVec.ofNat 64 x1.rep.p)
    (s8 : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 (x1.rep.len + x1.rep.scale))
    (s24 : ldv .ld M (sp - 96 + 24) = BitVec.ofNat 64 y.sb.pay)
    (h9 : R 9 = BitVec.ofNat 64 (mulScale x1.rep.scale x2.rep.scale k))
    (h20 : R 20 = BitVec.ofNat 64 (x2.rep.len + x2.rep.scale)) (h21 : R 21 = BitVec.ofNat 64 x2.rep.p)
    (h22 : R 22 = BitVec.ofNat 64 (x1.rep.scale + x2.rep.scale)) :
    DW live S Q 0x800057c0#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ hx1)
  num_facts hn1
  have hn2 := hb.nums x2 (List.mem_cons_of_mem _ hx2)
  num_facts hn2
  have hyn := hb.nums y List.mem_cons_self
  num_facts hyn
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hpt : ldv .ld M (y.sb.pay + 24) = BitVec.ofNat 64 y.rep.val := by
    rw [← hyp, hyn.ptr, hy.vptr]
  have yp1 := hyn.shape.pLo; have yp2 := hyn.shape.pHi; have yp3 := hyn.shape.pAl
  rw [hyp] at yp1 yp2 yp3
  simp only [heapStart, heapEnd] at yp1 yp2
  have h2 := st.r2
  have hd1 := hn1.shape.dsLen; have hd2 := hn2.shape.dsLen
  have hys := hy.scale; have hyl := hy.len
  have hnum := MulNum.of_prod (k := k) hyn.shape hd1 hd2 hy
  have hsx := sxw_ofNat (show x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale) + 1 < 2 ^ 31 by omega)
  have hsub := subw_nat (show x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale) + 1 < 2 ^ 30 by omega)
    (show x1.rep.scale + x2.rep.scale < 2 ^ 30 by omega)
  have hl : ((↑(x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale) + 1) : Int) -
      ↑(x1.rep.scale + x2.rep.scale)) = ↑(x1.rep.len + x2.rep.len + 1) := by omega
  rw [hl, ofInt_natCast64] at hsub
  bc_run hlive hS [h2, s0, s8, s24, hn1.sign, hn2.sign, hpt, h20, h21, h22, snez_signs,
    addw_ofNat (show x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale) < 2 ^ 31 by omega), hsx,
    hsub] at 0x800057ec
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | skip
  have hps : mulScale x1.rep.scale x2.rep.scale k ≤ x1.rep.scale + x2.rep.scale := by
    simp only [mulScale]; omega
  exact bmul_store hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hz hzg hy.owns hy.refs
    hy.vptr (by omega) (by rw [hyl, hys]; omega) hnum (by bsimp []) (by bsimp [])
    (by bsimp [h9]) (by bsimp []) (by bsimp [])

end Dc.Mach
