import Dc.Mach.Bc.AddSub

/-!
# `bc_add` (`lib/number.c`, `0x80005634`)

```
80005634 lw a4,0(a0) ; 80005638 lw a5,0(a1) ; 8000563c addi sp,sp,-48
80005640 sd s0,32(sp) ; 80005644 sd s1,24(sp) ; 80005648 sd ra,40(sp)
8000564c mv s0,a0 ; 80005650 mv s1,a2 ; 80005654 beq a4,a5,800056a0
80005658 li a2,0 ; 8000565c sd s2,16(sp) ; 80005660 sd a3,8(sp) ; 80005664 mv s2,a1
80005668 jal _bc_do_compare.part.0 ; 8000566c ld a3,8(sp) ; 80005670 beqz a0,800056f4
80005674 li a5,1 ; 80005678 mv a2,a3 ; 8000567c beq a0,a5,800056d4
80005680 mv a1,s0 ; 80005684 mv a0,s2 ; 80005688 jal _bc_do_sub ; 8000568c lw a5,0(s2)
80005690 mv s0,a0 ; 80005694 ld s2,16(sp) ; 80005698 sw a5,0(a0) ; 8000569c j 800056b4
800056a0 mv a2,a3 ; 800056a4 jal _bc_do_add ; 800056a8 lw a5,0(s0) ; 800056ac mv s0,a0
800056b0 sw a5,0(a0) ; 800056b4 mv a0,s1 ; 800056b8 jal bc_free_num ; 800056bc ld ra,40(sp)
800056c0 sd s0,0(s1) ; 800056c4 ld s0,32(sp) ; 800056c8 ld s1,24(sp) ; 800056cc addi sp,sp,48
800056d0 ret
800056d4 mv a1,s2 ; 800056d8 mv a0,s0 ; 800056dc jal _bc_do_sub ; 800056e0 lw a5,0(s0)
800056e4 ld s2,16(sp) ; 800056e8 mv s0,a0 ; 800056ec sw a5,0(a0) ; 800056f0 j 800056b4
800056f4 lw a5,8(s2) ; 800056f8 mv s2,a5 ; 800056fc bge a5,a3,80005704 ; 80005700 mv s2,a3
80005704 lw a5,8(s0) ; 80005708 sext.w a4,s2 ; 8000570c bge a4,a5,80005714 ; 80005710 mv s2,a5
80005714 sext.w a1,s2 ; 80005718 li a0,1 ; 8000571c jal bc_new_num ; 80005720 mv s0,a0
80005724 ld a0,32(a0) ; 80005728 addiw a2,s2,1 ; 8000572c li a1,0 ; 80005730 jal memset
80005734 ld s2,16(sp) ; 80005738 j 800056b4
```

Equal signs: `_bc_do_add` with `n1`'s sign. Different signs: `_bc_do_compare`
of the magnitudes, then `_bc_do_sub` of the larger minus the smaller with the
larger's sign, or a zero at the result scale. Then `bc_free_num(result)` and
the new number into `*result`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- The epilogue at `0x800056bc` after `bc_free_num`: the new number into the
slot, `ra`, `s0`, `s1` back. -/
theorem badd_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 L : List NumObj} {xr y : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (sv : SavedWords M (sp - 48) [(1, 40), (9, 24), (8, 32)] R0)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h8 : R 8 = BitVec.ofNat 64 y.sb.pay)
    (h9 : R 9 = BitVec.ofNat 64 q) (h18 : R 18 = R0 18) (hkp : Keeps binAll R R0)
    (hS : HeapOwn S)
    (hp : BinPost S Mt0 (writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)]) H F L1 L2 xr q sp n L y) :
    DW live S Q 0x800056bc#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have hap := cx.slotApart
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hal := cx.al
  have sv' := sv.transport (lo := 24) (top := 48)
    (M' := writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)])
    (hag := fun a h1 h2' => imgM_store_miss _ _ (by omega))
  have e1 := sv.get 1 40; have e8 := sv'.get 8 32; have e9 := sv'.get 9 24
  bc_run hlive hS [h2, h8, h9, e1, e8, e9]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hq.acc | exact hal | skip
  rw [sv'.get 8 32, sv'.get 9 24]
  refine hk.ret _ _ H F L y (Keeps.unwind (saved := [1, 2, 8, 9, 18]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp)) hp
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, h18]
  all_goals (try (congr 1; omega))

/-- The tail at `0x800056b4`: `bc_free_num(result)`, then the epilogue. -/
theorem badd_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj} {xr y : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (h8 : R 8 = BitVec.ofNat 64 y.sb.pay) (h18 : R 18 = R0 18)
    (hnum : y.rep.num = n) (hnorm : y.rep.Norm) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x800056b4#64 R M := by
  have hr := ResSlot.of_out cx st hr0
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have hap := cx.slotApart
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.r2; have h9 := st.r9
  have hxn := hb.nums xr (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have hxp : heapStart ≤ xr.rep.p ∧ xr.rep.p + 16 ≤ heapEnd :=
    ⟨hxn.shape.pLo, by have := hxn.shape.pHi; omega⟩
  bc_run hlive hS [h9, h2] at 0x800048c0
  have hsf' : StackFrame S (sp - 48) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  have e : FreeEntry S M H F (y :: L1) L2 xr q (sp - 48) :=
    FreeEntry.of_slot hb hr (hr.noView_cons hb hyo) hq cx.slotOut hsf' (by simp only [heapEnd]; omega) (by omega)
  refine bc_free_num_spec hlive e _ (by bsimp [h9]) (by bsimp [h2]) (by bsimp [])
    ⟨fun hx2 R1 Mt1 hk1 hb1 _ hmo => ?_, fun hx1 R1 Mt1 H1 hk1 hrp => ?_⟩
  · bsimp []
    have sv := st.saved.transport (lo := 24) (top := 48) (M' := Mt1) (hag := fun a h1 h2' =>
      hmo a fun hc => by
        rcases hc with hc | hc
        · simp only [refsBytes, heapStart, heapEnd] at hc hxp; omega
        · simp only [slotBytes] at hc; omega)
    exact badd_epi hlive cx hk sv (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8])
      (by rw [hk1.get 9]; bsimp [h9]) (by rw [hk1.get 18]; bsimp [h18])
      (((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps binAll _ R)).trans st.regs) hS
      (binPost_dec cx.slotOut (fun a ha _ hf => st.out a ha hf) hb1 hmo hxp hnum hnorm hrefs hyo hx2)
  · bsimp []
    have sv := st.saved.transport (lo := 24) (top := 48) (M' := Mt1) (hag := fun a h1 h2' =>
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
    exact badd_epi hlive cx hk sv (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8])
      (by rw [hk1.get 9]; bsimp [h9]) (by rw [hk1.get 18]; bsimp [h18])
      (((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps binAll _ R)).trans st.regs)
      (fun a h1 h2 => hrp.heap.heap.own a h1 h2)
      (binPost_rel cx.slotOut (fun a ha _ hf => st.out a ha hf) hb hrp cx.above hnum hnorm hrefs hyo hx1)

/-- The sign `b` stored into the new number `y` (positive, value `v`, scale
`s`), then the tail. -/
theorem badd_signed {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Num} {v s : Nat}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (h8 : R 8 = BitVec.ofNat 64 y.sb.pay) (h18 : R 18 = R0 18)
    (b : Bool) (hnum : y.rep.num = ⟨false, v, s⟩) (hn : (⟨b, v, s⟩ : Num) = n)
    (hnorm : y.rep.Norm) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x800056b4#64 R (writeLog M [(y.sb.pay, 4, signWord b)]) := by
  have hys := (hb.nums y List.mem_cons_self).shape
  have yp1 := hys.pLo; have yp2 := hys.pHi
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hb' := BcHeap.setSign (L1 := []) hb b (signWord_toNat _)
  rw [hyp] at hb'
  simp only [List.nil_append] at hb'
  exact badd_tail hlive cx hk (st.call cx.above (Keeps.refl _ _) fun a ha _ =>
      imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha yp1 yp2; omega))
    hb' hr0 h8 h18 (by rw [NumRep.num_withNeg hnum, hn]) hnorm hrefs hyo

/-- After `_bc_do_add` at `0x800056a8`: `n1`'s sign onto the new number. -/
theorem badd_add_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj}
    {x1 xr y : NumObj} {H : Heap} {F : List Blk} {n : Num} {v s : Nat}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hx1 : x1 ∈ L1 ++ xr :: L2)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 y.sb.pay)
    (h18 : R 18 = R0 18) (hnum : y.rep.num = ⟨false, v, s⟩) (hn : (⟨x1.rep.neg, v, s⟩ : Num) = n)
    (hnorm : y.rep.Norm) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x800056a8#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ hx1)
  num_facts hn1
  have sg := hn1.sign
  have hys := (hb.nums y List.mem_cons_self).shape
  have yp1 := hys.pLo; have yp2 := hys.pHi; have yp3 := hys.pAl
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  simp only [heapStart, heapEnd] at yp1 yp2
  bc_run hlive hS [h8, h10, sg] at 0x800056b4
  exact badd_signed hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 (by bsimp [h10])
    (by bsimp [h18]) x1.rep.neg hnum hn hnorm hrefs hyo

/-- After `_bc_do_sub(n1, n2)` at `0x800056e0`: `n1`'s sign, `s2` back. -/
theorem badd_gt_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj}
    {x1 xr y : NumObj} {H : Heap} {F : List Blk} {n : Num} {v s : Nat}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hx1 : x1 ∈ L1 ++ xr :: L2)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 y.sb.pay)
    (hs2 : ldv .ld M (sp - 48 + 16) = R0 18)
    (hnum : y.rep.num = ⟨false, v, s⟩) (hn : (⟨x1.rep.neg, v, s⟩ : Num) = n)
    (hnorm : y.rep.Norm) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x800056e0#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ hx1)
  num_facts hn1
  have sg := hn1.sign
  have hys := (hb.nums y List.mem_cons_self).shape
  have yp1 := hys.pLo; have yp2 := hys.pHi; have yp3 := hys.pAl
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  simp only [heapStart, heapEnd] at yp1 yp2
  have h2 := st.r2
  bc_run hlive hS [h8, h10, h2, sg, hs2] at 0x800056b4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact badd_signed hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 (by bsimp [h10])
    (by bsimp []) x1.rep.neg hnum hn hnorm hrefs hyo

/-- After `_bc_do_sub(n2, n1)` at `0x8000568c`: `n2`'s sign, `s2` back. -/
theorem badd_lt_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj}
    {x2 xr y : NumObj} {H : Heap} {F : List Blk} {n : Num} {v s : Nat}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hx2 : x2 ∈ L1 ++ xr :: L2)
    (h18 : R 18 = BitVec.ofNat 64 x2.rep.p) (h10 : R 10 = BitVec.ofNat 64 y.sb.pay)
    (hs2 : ldv .ld M (sp - 48 + 16) = R0 18)
    (hnum : y.rep.num = ⟨false, v, s⟩) (hn : (⟨x2.rep.neg, v, s⟩ : Num) = n)
    (hnorm : y.rep.Norm) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x8000568c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn2 := hb.nums x2 (List.mem_cons_of_mem _ hx2)
  num_facts hn2
  have sg := hn2.sign
  have hys := (hb.nums y List.mem_cons_self).shape
  have yp1 := hys.pLo; have yp2 := hys.pHi; have yp3 := hys.pAl
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  simp only [heapStart, heapEnd] at yp1 yp2
  have h2 := st.r2
  bc_run hlive hS [h18, h10, h2, sg, hs2] at 0x800056b4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact badd_signed hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 (by bsimp [h10])
    (by bsimp []) x2.rep.neg hnum hn hnorm hrefs hyo

/-- Equal signs, from `0x800056a0`: `_bc_do_add(n1, n2, scale_min)`. -/
theorem badd_add {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (Num.add x1.rep.num x2.rep.num smin))
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin)
    (hl : 1 ≤ x1.rep.len ∧ 1 ≤ x2.rep.len) (hs : x1.rep.neg = x2.rep.neg)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 x1.rep.p)
    (h11 : R 11 = BitVec.ofNat 64 x2.rep.p) (h13 : R 13 = BitVec.ofNat 64 smin)
    (h18 : R 18 = R0 18) :
    DW live S Q 0x800056a0#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 ha.m1).shape
  have hs2 := (hb.nums x2 ha.m2).shape
  have h2 := st.r2
  simp only [heapEnd] at hab
  bc_run hlive hS [h13, h2] at 0x80004304
  refine bc_do_add_spec hlive (sp := sp - 48) ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega),
      by omega, by omega, by omega⟩, by simp only [heapEnd]; omega, by bsimp [h2], by bsimp []; try decide⟩
    ⟨ha.m1, ha.m2, hl.1, hl.2, ha.size⟩ hb (by bsimp [h10]) (by bsimp [h11]) (by bsimp [h13])
    ⟨fun R1 Mt1 H1 F1 y hk1 h10' hp => ?_, fun R1 Mt1 hr2 hout => ?_⟩
  · bsimp []
    exact badd_add_ret hlive cx hk (st.call cx.above
        ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
        fun a ha hf => hp.out a ha fun h => hf (by simp only [frameIn] at *; omega))
      hp.heap hr0 ha.m1 (by rw [hk1.get 8]; bsimp [h8]) h10' (by rw [hk1.get 18]; bsimp [h18])
      hp.num (by rw [NumRep.num_eq, NumRep.num_eq, num_add_same hs1.dsLen hs2.dsLen hs]; rfl)
      hp.norm hp.refs hp.owns
  · exact hk.oom R1 Mt1 (sp - 48 - 96) (by omega) (by omega) hr2 fun a ha hf =>
      (hout a ha fun h => hf (by simp only [frameIn] at *; omega)).trans (st.out a ha hf)

/-- `n2`'s magnitude below `n1`'s: `n2` is not longer. -/
theorem len_le_of_gt {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hnb : b.Norm)
    (hc : Dc.Num.cmpMag a.num b.num = .gt) : b.len ≤ a.len :=
  Nat.not_lt.mp fun hl => by
    have hp := len_pos_of_gt ha hc
    rw [cmpMag_of_len_lt ha hb hnb (fun h0 => absurd h0 (by omega)) hl] at hc; cases hc

/-- `n1`'s magnitude below `n2`'s: `n1` is not longer. -/
theorem len_le_of_lt {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hna : a.Norm)
    (hc : Dc.Num.cmpMag a.num b.num = .lt) : a.len ≤ b.len :=
  Nat.not_lt.mp fun hl => by
    have hp := len_pos_of_lt hb hc
    rw [cmpMag_of_len_gt ha hb hna (fun h0 => absurd h0 (by omega)) hl] at hc; cases hc

/-- `|n1| > |n2|` with different signs, from `0x800056d4`: `_bc_do_sub(n1, n2)`. -/
theorem badd_gt {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (Num.add x1.rep.num x2.rep.num smin))
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg ≠ x2.rep.neg)
    (hc : Dc.Num.cmpMag x1.rep.num x2.rep.num = .gt)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hs2 : ldv .ld M (sp - 48 + 16) = R0 18)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h18 : R 18 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 smin) :
    DW live S Q 0x800056d4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 ha.m1).shape
  have hs2' := (hb.nums x2 ha.m2).shape
  have hle := len_le_of_gt hs1 hs2' ha.n2 hc
  have hsz := ha.size
  have h2 := st.r2
  simp only [heapEnd] at hab
  bc_run hlive hS [h8, h18, h2] at 0x800045e8
  refine bc_do_sub_spec hlive (sp := sp - 48) (smin := smin) ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega),
      by omega, by omega, by omega⟩, by simp only [heapEnd]; omega, by bsimp [h2], by bsimp []; try decide⟩
    ⟨ha.m1, ha.m2, hle, by omega, len_pos_of_gt hs1 hc⟩ hb (by bsimp [h8]) (by bsimp [h18])
      (by bsimp [h12])
    ⟨fun R1 Mt1 H1 F1 y hk1 h10' hp => ?_, fun R1 Mt1 hr2 hout => ?_⟩
  · bsimp []
    have hm : ∀ a, OutHeap a → ¬ frameIn (sp - 48) 128 a → imgM Mt1 a = imgM M a := hp.out
    exact badd_gt_ret hlive cx hk (st.call cx.above
        ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) hm)
      hp.heap hr0 ha.m1 (by rw [hk1.get 8]; bsimp [h8]) h10'
      (by rw [ldv_congr .ld fun j hj => hm _ (by
            simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]; exact hs2)
      hp.num (by rw [NumRep.num_eq, NumRep.num_eq,
        num_add_gt hs1.dsLen hs2'.dsLen hs1.dig hs2'.dig hs hc]; rfl) hp.norm hp.refs hp.owns
  · exact hk.oom R1 Mt1 (sp - 48 - 128) (by omega) (by omega) hr2 fun a ha hf =>
      (hout a ha fun h => hf (by simp only [frameIn] at *; omega)).trans (st.out a ha hf)

/-- `|n1| < |n2|` with different signs, from `0x80005680`: `_bc_do_sub(n2, n1)`. -/
theorem badd_lt {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (Num.add x1.rep.num x2.rep.num smin))
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg ≠ x2.rep.neg)
    (hc : Dc.Num.cmpMag x1.rep.num x2.rep.num = .lt)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hs2 : ldv .ld M (sp - 48 + 16) = R0 18)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h18 : R 18 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 smin) :
    DW live S Q 0x80005680#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 ha.m1).shape
  have hs2' := (hb.nums x2 ha.m2).shape
  have hle := len_le_of_lt hs1 hs2' ha.n1 hc
  have hsz := ha.size
  have h2 := st.r2
  simp only [heapEnd] at hab
  bc_run hlive hS [h8, h18, h2] at 0x800045e8
  refine bc_do_sub_spec hlive (sp := sp - 48) (smin := smin) ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega),
      by omega, by omega, by omega⟩, by simp only [heapEnd]; omega, by bsimp [h2], by bsimp []; try decide⟩
    ⟨ha.m2, ha.m1, hle, by omega, len_pos_of_lt hs2' hc⟩ hb (by bsimp [h18]) (by bsimp [h8])
      (by bsimp [h12])
    ⟨fun R1 Mt1 H1 F1 y hk1 h10' hp => ?_, fun R1 Mt1 hr2 hout => ?_⟩
  · bsimp []
    have hm : ∀ a, OutHeap a → ¬ frameIn (sp - 48) 128 a → imgM Mt1 a = imgM M a := hp.out
    exact badd_lt_ret hlive cx hk (st.call cx.above
        ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) hm)
      hp.heap hr0 ha.m2 (by rw [hk1.get 18]; bsimp [h18]) h10'
      (by rw [ldv_congr .ld fun j hj => hm _ (by
            simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]; exact hs2)
      hp.num (by rw [resScale_comm, NumRep.num_eq, NumRep.num_eq,
        num_add_lt hs1.dsLen hs2'.dsLen hs1.dig hs2'.dig hs hc]; rfl) hp.norm hp.refs hp.owns
  · exact hk.oom R1 Mt1 (sp - 48 - 128) (by omega) (by omega) hr2 fun a ha hf =>
      (hout a ha fun h => hf (by simp only [frameIn] at *; omega)).trans (st.out a ha hf)

/-! ## Equal magnitudes, different signs: a zero -/

/-- The zero `bc_new_num(1, scale)` returned, at the result scale. -/
theorem zeroRep_num {p ptr s : Nat} : (zeroRep p ptr 1 s).num = Num.zero s := by
  simp only [NumRep.num, zeroRep, Num.zero, dval_eq_dvalBE, dvalBE_replicate_zero]

/-- After `bc_new_num` at `0x80005720`: `memset(n_value, 0, scale + 1)`,
`s2` back, then the tail. -/
theorem badd_zero_fill {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q sc : Nat} {L1 L2 : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Num}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hy : y.rep = zeroRep y.sb.pay y.db.pay 1 sc)
    (hn : Num.zero sc = n) (hsc : sc + 1 < 2 ^ 31)
    (h10 : R 10 = BitVec.ofNat 64 y.sb.pay) (h18 : R 18 = BitVec.ofNat 64 sc)
    (hs2 : ldv .ld M (sp - 48 + 16) = R0 18) :
    DW live S Q 0x80005720#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums y List.mem_cons_self
  num_facts hn0
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hv0 : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by rw [← hyp]; exact hn0.value
  have hls : y.rep.len + y.rep.scale = 1 + sc := by rw [hy]; rfl
  simp only [heapEnd] at hab
  have h2 := st.r2
  bc_run hlive hS [h10, h18, hv0, sxw_ofNat] at 0x80000890
  have hob : OwnedBytes S y.rep.val (sc + 1) :=
    ⟨fun i hi => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
      by omega⟩
  refine memset_spec hlive hob _ (by bsimp [hv0]) (by bsimp [h18]; try (congr 1; omega))
    (by bsimp []) fun R1 Mt1 hk1 hf => ?_
  bsimp []
  have hf' : Filled Mt1 M y.rep.val (1 + sc) fun _ => 0#8 := by
    rw [Nat.add_comm]; exact hf
  have hb' := BcHeap.zeroAgain hb hy hf'
  have hm : ∀ a, OutHeap a → imgM Mt1 a = imgM M a := fun a ha => hf.rest a (by
    simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  have hs2' : ldv .ld Mt1 (sp - 48 + 16) = R0 18 := by
    rw [ldv_congr .ld fun j hj => hm _ (by
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)]
    exact hs2
  have r2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp [h2]
  have r8 : R1 8 = BitVec.ofNat 64 y.sb.pay := by rw [hk1.get 8]; bsimp [h10]
  bc_run hlive hS [r2, r8, hs2'] at 0x800056b4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hS' : HeapOwn S := fun a h1 h2 => hb'.heap.own a h1 h2
  exact badd_tail hlive cx hk (st.call cx.above
      (by keeps_tac ((hk1.mono (by decide) : Keeps binTmp R1 _).trans
        (by keeps_tac Keeps.refl _ _ : Keeps binTmp _ R))) fun a ha _ => hm a ha)
    hb' hr0 (by bsimp [r8]) (by bsimp []) (by rw [hy, zeroRep_num, hn])
    (by rw [hy]; exact Or.inl (Nat.le_refl 1)) (by rw [hy]; rfl)
    (by show y.rep.ptr ≠ 0; rw [hy]; show y.db.h + 16 ≠ 0; omega)

/-- `bc_new_num(1, scale)` from `0x80005714` with the result scale in `s2`. -/
theorem badd_zero_new {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q sc : Nat} {L1 L2 : List NumObj}
    {xr : NumObj} {H : Heap} {F : List Blk} {n : Num}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hn : Num.zero sc = n) (hsc : sc + 1 < 2 ^ 31)
    (h18 : R 18 = BitVec.ofNat 64 sc) (hs2 : ldv .ld M (sp - 48 + 16) = R0 18) :
    DW live S Q 0x80005714#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.r2
  bc_run hlive hS [h18, h2, sxw_ofNat] at 0x80004250
  have hsf' : StackFrame S (sp - 48) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine bc_new_num_spec hlive hb.newHeap hsf' (len := 1) (scale := sc)
    (by simp only [heapEnd]; omega) (by omega) (by omega) _ (by bsimp []) (by bsimp [h18])
    (by bsimp [h2]) (by bsimp []) ⟨fun R1 Mt1 H1 F1 y hk1 hp1 hr1 => ?_, fun R' Mt' hr2' hout' => ?_⟩
  · bsimp []
    have hm : ∀ a, OutHeap a → ¬ frameIn (sp - 48) 128 a → imgM Mt1 a = imgM M a :=
      fun a ha hf => hp1.out a ha fun h => hf (by simp only [frameIn] at *; omega)
    exact badd_zero_fill hlive cx hk (st.call cx.above
        ((hk1.mono (by decide) : Keeps binTmp R1 _).trans (by keeps_tac Keeps.refl _ _)) hm)
      (NewNumPost.insert hb hp1) hr0 hp1.rep hn hsc hr1 (by rw [hk1.get 18]; bsimp [h18])
      (by rw [ldv_congr .ld fun j hj => hm _ (by
            simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]; exact hs2)
  · exact hk.oom R' Mt' (sp - 48 - 32) (by omega) (by omega) hr2' fun a ha hf =>
      (hout' a ha fun h => hf (by simp only [frameIn] at *; omega)).trans (st.out a ha hf)

/-- The larger of `max scale2 scale_min` and `n1`'s scale into `s2`, from
`0x80005704`. -/
theorem badd_zero_mid {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk} {n : Num}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hn : Num.zero (resScale x1.rep.scale x2.rep.scale smin) = n)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h18 : R 18 = BitVec.ofNat 64 (max x2.rep.scale smin))
    (hs2 : ldv .ld M (sp - 48 + 16) = R0 18) :
    DW live S Q 0x80005704#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 ha.m1
  num_facts hn1
  have c1 := hn1.scale
  have hsz := ha.size
  bc_run hlive hS [h8, h18, c1, sxw_ofNat, toInt_ofNat_small] at 0x80005714
  · intro hge
    have hge' : x1.rep.scale ≤ max x2.rep.scale smin := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hge); omega
    exact badd_zero_new hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hn
      (by simp only [resScale]; omega) (by bsimp [h18]; congr 1; simp only [resScale]; omega) hs2
  · intro hlt
    have hlt' : max x2.rep.scale smin < x1.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
    bc_run hlive hS [h8, h18, c1, sxw_ofNat] at 0x80005714
    exact badd_zero_new hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hn
      (by simp only [resScale]; omega) (by bsimp [c1]; congr 1; simp only [resScale]; omega) hs2

/-- Equal magnitudes, different signs, from `0x800056f4`: the larger of
`n2`'s scale and `scale_min` into `s2`. -/
theorem badd_zero {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (Num.add x1.rep.num x2.rep.num smin))
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg ≠ x2.rep.neg)
    (hc : Dc.Num.cmpMag x1.rep.num x2.rep.num = .eq)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hs2 : ldv .ld M (sp - 48 + 16) = R0 18)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h18 : R 18 = BitVec.ofNat 64 x2.rep.p)
    (h13 : R 13 = BitVec.ofNat 64 smin) :
    DW live S Q 0x800056f4#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn2 := hb.nums x2 ha.m2
  num_facts hn2
  have c2 := hn2.scale
  have hsz := ha.size
  have hn : Num.zero (resScale x1.rep.scale x2.rep.scale smin) = Num.add x1.rep.num x2.rep.num smin :=
    (num_add_eq hs hc).symm
  bc_run hlive hS [h18, h13, c2, toInt_ofNat_small] at 0x80005704
  · intro hge
    have hge' : smin ≤ x2.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hge); omega
    exact badd_zero_mid hlive cx hk ha (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hn
      (by bsimp [h8]) (by bsimp [c2]; congr 1; omega) hs2
  · intro hlt
    have hlt' : x2.rep.scale < smin := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
    bc_run hlive hS [h18, h13, c2] at 0x80005704
    exact badd_zero_mid hlive cx hk ha (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hn
      (by bsimp [h8]) (by bsimp [h13]; congr 1; omega) hs2

/-! ## The comparison and the entry -/

/-- After `_bc_do_compare` at `0x8000566c`: `scale_min` back from the frame,
then the zero, `n1 - n2` or `n2 - n1`. -/
theorem badd_cmp {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (Num.add x1.rep.num x2.rep.num smin))
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg ≠ x2.rep.neg)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hs2 : ldv .ld M (sp - 48 + 16) = R0 18)
    (hsm : ldv .ld M (sp - 48 + 8) = BitVec.ofNat 64 smin)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h18 : R 18 = BitVec.ofNat 64 x2.rep.p)
    (h10 : R 10 = ordWord (Dc.Num.cmpMag x1.rep.num x2.rep.num)) :
    DW live S Q 0x8000566c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.r2
  have htx : tohostAddr = 0x8001ad00 := rfl
  rcases hc : Dc.Num.cmpMag x1.rep.num x2.rep.num with _ | _ | _ <;> rw [hc] at h10 <;>
    simp only [ordWord] at h10
  · iterate 3 (all_goals (try (bc_run hlive hS [h2, h10, hsm] at 0x80005680)))
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact badd_lt hlive cx hk ha hs hc (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hs2
      (by bsimp [h8]) (by bsimp [h18]) (by bsimp [])
  · iterate 3 (all_goals (try (bc_run hlive hS [h2, h10, hsm] at 0x800056f4)))
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact badd_zero hlive cx hk ha hs hc (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hs2
      (by bsimp [h8]) (by bsimp [h18]) (by bsimp [])
  · iterate 3 (all_goals (try (bc_run hlive hS [h2, h10, hsm] at 0x800056d4)))
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact badd_gt hlive cx hk ha hs hc (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hs2
      (by bsimp [h8]) (by bsimp [h18]) (by bsimp [])

/-- Different signs, from `0x80005658`: `s2` and `scale_min` saved, then
`_bc_do_compare(n1, n2, FALSE, FALSE)`. -/
theorem badd_ne {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (Num.add x1.rep.num x2.rep.num smin))
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg ≠ x2.rep.neg)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 x1.rep.p)
    (h11 : R 11 = BitVec.ofNat 64 x2.rep.p) (h13 : R 13 = BitVec.ofNat 64 smin)
    (h18 : R 18 = R0 18) :
    DW live S Q 0x80005658#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.r2
  have hpro : MemOnly (fun a => sp - 48 ≤ a ∧ a < sp - 24) (writeLog (writeLog M
      [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 13)]) M := fun a ha => by
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hb' := hb.out_frame hpro fun a ha => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hn1 := hb'.nums x1 ha.m1
  have hn2 := hb'.nums x2 ha.m2
  bc_run hlive hS [h2, h11] at 0x80003fb0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hs2 : ldv .ld (writeLog (writeLog M [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 13)])
      (sp - 48 + 16) = R0 18 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit, h18]
  have hsm : ldv .ld (writeLog (writeLog M [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 13)])
      (sp - 48 + 8) = BitVec.ofNat 64 smin := by
    rw [ldv_store_hit, h13]
  refine do_compare_spec hlive hS hn1 hn2 ha.n1 ha.n2 ha.e1 ha.e2 (u := false) _ (by bsimp [h10])
    (by bsimp [h11]) (by bsimp []) (by bsimp []; try decide) fun R1 hk1 h10' => ?_
  bsimp []
  exact badd_cmp hlive cx hk ha hs
    (st.low ((hk1.mono (by decide) : Keeps binTmp R1 _).trans (by keeps_tac Keeps.refl _ _)) hpro)
    hb' hr0 hs2 hsm (by rw [hk1.get 8]; bsimp [h8]) (by rw [hk1.get 18]; bsimp [h11]) h10'

/-- The sign test at `0x80005654`: `a4`, `a5` the operands' sign words. -/
theorem badd_dispatch {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (Num.add x1.rep.num x2.rep.num smin))
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin)
    (hadd : x1.rep.neg = x2.rep.neg → 1 ≤ x1.rep.len ∧ 1 ≤ x2.rep.len)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 x1.rep.p)
    (h11 : R 11 = BitVec.ofNat 64 x2.rep.p) (h13 : R 13 = BitVec.ofNat 64 smin)
    (h18 : R 18 = R0 18) (h14 : R 14 = signWord x1.rep.neg) (h15 : R 15 = signWord x2.rep.neg) :
    DW live S Q 0x80005654#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  cases e1 : x1.rep.neg <;> cases e2 : x2.rep.neg <;> rw [e1] at h14 <;> rw [e2] at h15 <;>
    simp only [signWord_false, signWord_true] at h14 h15
  all_goals bc_run hlive hS [h14, h15] at 0x800056a0 0x80005658
  all_goals first
    | exact badd_add hlive cx hk ha (hadd (by rw [e1, e2])) (by rw [e1, e2]) (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0
        (by bsimp [h8]) (by bsimp [h10]) (by bsimp [h11]) (by bsimp [h13]) (by bsimp [h18])
    | exact badd_ne hlive cx hk ha (by rw [e1, e2]; decide) (st.keeps (by keeps_tac Keeps.refl _ _))
        hb hr0 (by bsimp [h8]) (by bsimp [h10]) (by bsimp [h11]) (by bsimp [h13]) (by bsimp [h18])

/-- **`bc_add(n1, n2, result, scale_min)`** at `0x80005634`, for two
normalized numbers of the heap and the result slot `q` holding `x` of the
heap: the new number for `Num.add n1 n2 scale_min` in the slot, `x` freed
once (`BinK.ret`), or `out_of_memory` (`BinK.oom`). -/
theorem bc_add_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj} {x1 x2 xr : NumObj}
    {H : Heap} {F : List Blk}
    (cx : BinCtx S R sp q) (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin)
    (hadd : x1.rep.neg = x2.rep.neg → 1 ≤ x1.rep.len ∧ 1 ≤ x2.rep.len)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr q)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 q) (h13 : R 13 = BitVec.ofNat 64 smin)
    (hk : BinK live S Q R M L1 L2 xr q sp (Num.add x1.rep.num x2.rep.num smin)) :
    DW live S Q 0x80005634#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 ha.m1
  have hn2 := hb.nums x2 ha.m2
  num_facts hn1
  num_facts hn2
  have sg1 := hn1.sign; have sg2 := hn2.sign
  have h2 := cx.sp0
  have sv := (((SavedWords.nil M (sp - 48) R).store 8 32).store 9 24).store 1 40
  have hpro : MemOnly (frameIn sp 48) (writeLog (writeLog (writeLog M
      [(sp - 48 + 32, 8, R 8)]) [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)]) M :=
    fun a ha => by
      simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hb' := hb.out_frame hpro fun a ha => by
    simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha ⊢; omega
  have st : ∀ R', R' 2 = BitVec.ofNat 64 (sp - 48) → R' 9 = BitVec.ofNat 64 q →
      Keeps binAll R' R → BinAt S M (writeLog (writeLog (writeLog M
        [(sp - 48 + 32, 8, R 8)]) [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)]) R R' sp q :=
    fun R' r2 r9 hkp =>
      { r2 := r2, saved := sv, r9 := r9, regs := hkp
        out := fun a _ hf => hpro a fun h => hf (by simp only [frameIn] at *; omega) }
  bc_run hlive hS [h2, h10, h11, h12, sg1, sg2, word_sub48] at 0x80005654
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact badd_dispatch hlive cx hk ha hadd (st _ (by bsimp []) (by bsimp [h12])
    (by keeps_tac Keeps.refl _ _)) hb' hr (by bsimp [h10]) (by bsimp [h10]) (by bsimp [h11])
    (by bsimp [h13]) (by bsimp []) (by bsimp [sg1]) (by bsimp [sg2])

end Dc.Mach
