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
    (hr0 : ResSlot Mt0 xr q) (h8 : R 8 = BitVec.ofNat 64 y.sb.pay) (h18 : R 18 = R0 18)
    (hnum : y.rep.num = n) (hnorm : y.rep.Norm) (hrefs : y.rep.refs = 1) :
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
    FreeEntry.of_slot hb hr hq cx.slotOut hsf' (by simp only [heapEnd]; omega) (by omega)
  refine bc_free_num_spec hlive e _ (by bsimp [h9]) (by bsimp [h2]) (by bsimp [])
    ⟨fun _ R1 Mt1 hk1 hb1 _ hmo => ?_, fun _ R1 Mt1 H1 hk1 hrp => ?_⟩
  · bsimp []
    have sv := st.saved.transport (lo := 24) (top := 48) (M' := Mt1) (hag := fun a h1 h2' =>
      hmo a fun hc => by
        rcases hc with hc | hc
        · simp only [refsBytes, heapStart, heapEnd] at hc hxp; omega
        · simp only [slotBytes] at hc; omega)
    exact badd_epi hlive cx hk sv (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8])
      (by rw [hk1.get 9]; bsimp [h9]) (by rw [hk1.get 18]; bsimp [h18])
      (((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps binAll _ R)).trans st.regs) hS
      (binPost_dec cx.slotOut (fun a ha _ hf => st.out a ha hf) hb1 hmo hxp hnum hnorm hrefs)
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
      (binPost_rel cx.slotOut (fun a ha _ hf => st.out a ha hf) hb hrp cx.above hnum hnorm hrefs)

/-- After `_bc_do_add` at `0x800056a8`: `n1`'s sign onto the new number. -/
theorem badd_add_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj}
    {x1 xr y : NumObj} {H : Heap} {F : List Blk} {n : Num} {v s : Nat}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 xr q) (hx1 : x1 ∈ L1 ++ xr :: L2)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 y.sb.pay)
    (h18 : R 18 = R0 18) (hnum : y.rep.num = ⟨false, v, s⟩) (hn : (⟨x1.rep.neg, v, s⟩ : Num) = n)
    (hnorm : y.rep.Norm) (hrefs : y.rep.refs = 1) :
    DW live S Q 0x800056a8#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hab := cx.above
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ hx1)
  num_facts hn1
  have sg := hn1.sign
  have hys := (hb.nums y List.mem_cons_self).shape
  have yp1 := hys.pLo; have yp2 := hys.pHi; have yp3 := hys.pAl
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  simp only [heapStart, heapEnd] at yp1 yp2 hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h8, h10, sg] at 0x800056b4
  have hb' := BcHeap.setSign (L1 := []) hb x1.rep.neg (signWord_toNat _)
  rw [hyp] at hb'
  simp only [List.nil_append] at hb'
  exact badd_tail hlive cx hk (st.call cx.above (by keeps_tac Keeps.refl _ _) fun a ha _ =>
      imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega))
    hb' hr0 (by bsimp [h10]) (by bsimp [h18]) (by rw [NumRep.num_withNeg hnum, hn])
    hnorm hrefs

/-- Equal signs, from `0x800056a0`: `_bc_do_add(n1, n2, scale_min)`. -/
theorem badd_add {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (Num.add x1.rep.num x2.rep.num smin))
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg = x2.rep.neg)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 xr q)
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
    ⟨ha.m1, ha.m2, ha.size⟩ hb (by bsimp [h10]) (by bsimp [h11]) (by bsimp [h13])
    ⟨fun R1 Mt1 H1 F1 y hk1 h10' hp => ?_, fun R1 Mt1 hr2 hout => ?_⟩
  · bsimp []
    exact badd_add_ret hlive cx hk (st.call cx.above
        ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
        fun a ha hf => hp.out a ha fun h => hf (by simp only [frameIn] at *; omega))
      hp.heap hr0 ha.m1 (by rw [hk1.get 8]; bsimp [h8]) h10' (by rw [hk1.get 18]; bsimp [h18])
      hp.num (by rw [NumRep.num_eq, NumRep.num_eq, num_add_same hs1.dsLen hs2.dsLen hs]; rfl)
      hp.norm hp.refs
  · exact hk.oom R1 Mt1 (sp - 48 - 96) (by omega) (by omega) hr2 fun a ha hf =>
      (hout a ha fun h => hf (by simp only [frameIn] at *; omega)).trans (st.out a ha hf)

end Dc.Mach
