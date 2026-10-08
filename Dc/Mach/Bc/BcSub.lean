import Dc.Mach.Bc.BcAdd

/-!
# `bc_sub` (`lib/number.c`, `0x80004ac4`)

```
80004ac4 lw a6,0(a0) ; 80004ac8 lw a4,0(a1) ; 80004acc addi sp,sp,-48
80004ad0 sd s0,32(sp) ; 80004ad4 sd s1,24(sp) ; 80004ad8 sd ra,40(sp)
80004adc mv s0,a0 ; 80004ae0 mv s1,a2 ; 80004ae4 bne a6,a4,80004b34
80004ae8 li a2,0 ; 80004aec sd a3,8(sp) ; 80004af0 sd a1,0(sp)
80004af4 jal _bc_do_compare.part.0 ; 80004af8 ld a5,0(sp) ; 80004afc ld a3,8(sp)
80004b00 beqz a0,80004b84 ; 80004b04 li a4,1 ; 80004b08 mv a2,a3 ; 80004b0c beq a0,a4,80004b68
80004b10 mv a1,s0 ; 80004b14 mv a0,a5 ; 80004b18 jal _bc_do_sub ; 80004b1c ld a5,0(sp)
80004b20 mv s0,a0 ; 80004b24 lw a5,0(a5) ; 80004b28 seqz a5,a5 ; 80004b2c sw a5,0(a0)
80004b30 j 80004b48
80004b34 mv a2,a3 ; 80004b38 jal _bc_do_add ; 80004b3c lw a5,0(s0) ; 80004b40 mv s0,a0
80004b44 sw a5,0(a0) ; 80004b48 mv a0,s1 ; 80004b4c jal bc_free_num ; 80004b50 ld ra,40(sp)
80004b54 sd s0,0(s1) ; 80004b58 ld s0,32(sp) ; 80004b5c ld s1,24(sp) ; 80004b60 addi sp,sp,48
80004b64 ret
80004b68 mv a1,a5 ; 80004b6c mv a0,s0 ; 80004b70 jal _bc_do_sub ; 80004b74 lw a5,0(s0)
80004b78 mv s0,a0 ; 80004b7c sw a5,0(a0) ; 80004b80 j 80004b48
80004b84 lw a5,8(a5) ; 80004b88 mv a2,a5 ; 80004b8c bge a5,a3,80004b94 ; 80004b90 mv a2,a3
80004b94 lw a5,8(s0) ; 80004b98 sext.w a4,a2 ; 80004b9c bge a4,a5,80004ba4 ; 80004ba0 mv a2,a5
80004ba4 sext.w a1,a2 ; 80004ba8 li a0,1 ; 80004bac sw a2,0(sp) ; 80004bb0 jal bc_new_num
80004bb4 lw a2,0(sp) ; 80004bb8 mv s0,a0 ; 80004bbc ld a0,32(a0) ; 80004bc0 addiw a2,a2,1
80004bc4 li a1,0 ; 80004bc8 jal memset ; 80004bcc j 80004b48
```

Different signs: `_bc_do_add` with `n1`'s sign. Equal signs: `_bc_do_compare`
of the magnitudes, then `_bc_do_sub` of the larger minus the smaller (`n1`'s
sign, or the opposite of `n2`'s), or a zero at the result scale. `n2` and
`scale_min` live in the frame across the comparison, the zero's scale across
`bc_new_num`. The shared layer is `AddSub.lean`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-! ## `bc_sub` as the machine computes it

`_bc_do_compare` decides by integer length first (`NumRep.cmpRep`), so an
empty operand against a zero one takes a subtraction route: the magnitude is
`0` and the sign is the route's. `NumRep.subM` is that result; it is
`Num.sub` whenever the lengths agree or an empty operand meets a nonzero one
(`subM_eq`). -/

/-- `bc_sub (a, b, smin)` as the machine computes it. -/
def NumRep.subM (a b : NumRep) (smin : Nat) : Num :=
  if a.neg = b.neg ∧ a.len ≠ b.len then
    if a.len < b.len then
      ⟨!b.neg, dvalBE (subDigits b.len b.scale b.ds a.len a.scale a.ds smin),
        resScale a.scale b.scale smin⟩
    else
      ⟨a.neg, dvalBE (subDigits a.len a.scale a.ds b.len b.scale b.ds smin),
        resScale a.scale b.scale smin⟩
  else Num.sub a.num b.num smin

theorem NumRep.subM_of_len {a b : NumRep} (smin : Nat) (h : ¬ (a.neg = b.neg ∧ a.len ≠ b.len)) :
    a.subM b smin = Num.sub a.num b.num smin := by
  unfold NumRep.subM; rw [if_neg h]

theorem NumRep.subM_eq {a b : NumRep} (smin : Nat) (ha : NumShape a) (hb : NumShape b)
    (hna : a.Norm) (hnb : b.Norm)
    (hla : a.len = 0 → 0 < dval b.ds) (hlb : b.len = 0 → 0 < dval a.ds) :
    a.subM b smin = Num.sub a.num b.num smin := by
  unfold NumRep.subM
  split
  · rename_i h
    split
    · rename_i hl
      have hc := cmpMag_of_len_lt ha hb hnb hla hl
      rw [NumRep.num_eq, NumRep.num_eq] at hc ⊢
      rw [num_sub_lt ha.dsLen hb.dsLen ha.dig hb.dig h.1 hc]
    · rename_i hl
      have hc := cmpMag_of_len_gt ha hb hna hlb (by omega)
      rw [NumRep.num_eq, NumRep.num_eq] at hc ⊢
      rw [num_sub_gt ha.dsLen hb.dsLen ha.dig hb.dig h.1 hc]
  · rfl

/-- `bc_sub`'s operands as the machine needs them: normalised, not both
empty. -/
structure BinArgsM (L : List NumObj) (x1 x2 : NumObj) (smin : Nat) : Prop where
  m1 : x1 ∈ L
  m2 : x2 ∈ L
  n1 : x1.rep.Norm
  n2 : x2.rep.Norm
  size : max x1.rep.len x2.rep.len + 1 + max smin (max x1.rep.scale x2.rep.scale) < 2 ^ 31
  ne : 1 ≤ x1.rep.len ∨ 1 ≤ x2.rep.len

theorem BinArgs.toM {L : List NumObj} {x1 x2 : NumObj} {smin : Nat} (h : BinArgs L x1 x2 smin)
    (hs2 : NumShape x2.rep) : BinArgsM L x1 x2 smin :=
  ⟨h.m1, h.m2, h.n1, h.n2, h.size, len_one_of_nonzero hs2 h.e1⟩

/-- The length-first comparison answered `gt`. -/
theorem repGt_facts {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hnb : b.Norm)
    (hs : a.neg = b.neg) (hc : a.cmpRep b = .gt) (smin : Nat) :
    b.len ≤ a.len ∧ 1 ≤ a.len ∧
      (⟨a.neg, dvalBE (subDigits a.len a.scale a.ds b.len b.scale b.ds smin),
        resScale a.scale b.scale smin⟩ : Num) = a.subM b smin := by
  unfold NumRep.cmpRep at hc
  split at hc
  · rename_i hl
    refine ⟨len_le_of_gt ha hb hnb hc, len_pos_of_gt ha hc, ?_⟩
    rw [NumRep.subM_of_len smin (fun h => h.2 hl), NumRep.num_eq, NumRep.num_eq]
    rw [NumRep.num_eq, NumRep.num_eq] at hc
    rw [num_sub_gt ha.dsLen hb.dsLen ha.dig hb.dig hs hc]
  · rename_i hl
    have hgt := Nat.compare_eq_gt.1 hc
    refine ⟨by omega, by omega, ?_⟩
    unfold NumRep.subM
    rw [if_pos ⟨hs, hl⟩, if_neg (by omega)]

/-- The length-first comparison answered `lt`. -/
theorem repLt_facts {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hna : a.Norm)
    (hs : a.neg = b.neg) (hc : a.cmpRep b = .lt) (smin : Nat) :
    a.len ≤ b.len ∧ 1 ≤ b.len ∧
      (⟨!b.neg, dvalBE (subDigits b.len b.scale b.ds a.len a.scale a.ds smin),
        resScale b.scale a.scale smin⟩ : Num) = a.subM b smin := by
  unfold NumRep.cmpRep at hc
  split at hc
  · rename_i hl
    refine ⟨len_le_of_lt ha hb hna hc, len_pos_of_lt hb hc, ?_⟩
    rw [NumRep.subM_of_len smin (fun h => h.2 hl), resScale_comm, NumRep.num_eq, NumRep.num_eq]
    rw [NumRep.num_eq, NumRep.num_eq] at hc
    rw [num_sub_lt ha.dsLen hb.dsLen ha.dig hb.dig hs hc]
  · rename_i hl
    have hlt := Nat.compare_eq_lt.1 hc
    refine ⟨by omega, by omega, ?_⟩
    unfold NumRep.subM
    rw [if_pos ⟨hs, hl⟩, if_pos hlt, resScale_comm]

/-- The length-first comparison answered `eq`: the lengths agree and so do
the magnitudes. -/
theorem repEq_facts {a b : NumRep} (hs : a.neg = b.neg) (hc : a.cmpRep b = .eq) (smin : Nat) :
    Num.zero (resScale a.scale b.scale smin) = a.subM b smin := by
  unfold NumRep.cmpRep at hc
  split at hc
  · rename_i hl
    rw [NumRep.subM_of_len smin (fun h => h.2 hl), NumRep.num_eq, NumRep.num_eq]
    rw [NumRep.num_eq, NumRep.num_eq] at hc
    rw [num_sub_eq hs hc]
  · rename_i hl
    exact absurd (Nat.compare_eq_eq.1 hc) hl

/-- The epilogue at `0x80004b50` after `bc_free_num`: the new number into the
slot, `ra`, `s0`, `s1` back. -/
theorem bsub_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 L : List NumObj} {xr y : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (sv : SavedWords M (sp - 48) [(1, 40), (9, 24), (8, 32)] R0)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h8 : R 8 = BitVec.ofNat 64 y.sb.pay)
    (h9 : R 9 = BitVec.ofNat 64 q) (h18 : R 18 = R0 18) (hkp : Keeps binAll R R0)
    (hS : HeapOwn S)
    (hp : BinPost S Mt0 (writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)]) H F L1 L2 xr q sp n L y) :
    DW live S Q 0x80004b50#64 R M := by
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

/-- The tail at `0x80004b48`: `bc_free_num(result)`, then the epilogue. -/
theorem bsub_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj} {xr y : NumObj}
    {H : Heap} {F : List Blk} {n : Num}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (h8 : R 8 = BitVec.ofNat 64 y.sb.pay) (h18 : R 18 = R0 18)
    (hnum : y.rep.num = n) (hnorm : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x80004b48#64 R M := by
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
    exact bsub_epi hlive cx hk sv (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8])
      (by rw [hk1.get 9]; bsimp [h9]) (by rw [hk1.get 18]; bsimp [h18])
      (((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps binAll _ R)).trans st.regs) hS
      (binPost_dec cx.slotOut (fun a ha _ hf => st.out a ha hf) hb1 hmo hxp hnum hnorm hpos hrefs hyo hx2)
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
    exact bsub_epi hlive cx hk sv (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8])
      (by rw [hk1.get 9]; bsimp [h9]) (by rw [hk1.get 18]; bsimp [h18])
      (((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps binAll _ R)).trans st.regs)
      (fun a h1 h2 => hrp.heap.heap.own a h1 h2)
      (binPost_rel cx.slotOut (fun a ha _ hf => st.out a ha hf) hb hrp cx.above hnum hnorm hpos hrefs hyo hx1)

/-- The sign `b` stored into the new number `y` (positive, value `v`, scale
`s`), then the tail. -/
theorem bsub_signed {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Num} {v s : Nat}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (h8 : R 8 = BitVec.ofNat 64 y.sb.pay) (h18 : R 18 = R0 18)
    (b : Bool) (hnum : y.rep.num = ⟨false, v, s⟩) (hn : (⟨b, v, s⟩ : Num) = n)
    (hnorm : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x80004b48#64 R (writeLog M [(y.sb.pay, 4, signWord b)]) := by
  have hys := (hb.nums y List.mem_cons_self).shape
  have yp1 := hys.pLo; have yp2 := hys.pHi
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hb' := BcHeap.setSign (L1 := []) hb b (signWord_toNat _)
  rw [hyp] at hb'
  simp only [List.nil_append] at hb'
  exact bsub_tail hlive cx hk (st.call cx.above (Keeps.refl _ _) fun a ha _ =>
      imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha yp1 yp2; omega))
    hb' hr0 h8 h18 (by rw [NumRep.num_withNeg hnum, hn]) hnorm hpos hrefs hyo

/-- After `_bc_do_add` at `0x80004b3c`: `n1`'s sign onto the new number. -/
theorem bsub_add_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj}
    {x1 xr y : NumObj} {H : Heap} {F : List Blk} {n : Num} {v s : Nat}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hx1 : x1 ∈ L1 ++ xr :: L2)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 y.sb.pay)
    (h18 : R 18 = R0 18) (hnum : y.rep.num = ⟨false, v, s⟩) (hn : (⟨x1.rep.neg, v, s⟩ : Num) = n)
    (hnorm : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x80004b3c#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ hx1)
  num_facts hn1
  have sg := hn1.sign
  have hys := (hb.nums y List.mem_cons_self).shape
  have yp1 := hys.pLo; have yp2 := hys.pHi; have yp3 := hys.pAl
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  simp only [heapStart, heapEnd] at yp1 yp2
  bc_run hlive hS [h8, h10, sg] at 0x80004b48
  exact bsub_signed hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 (by bsimp [h10])
    (by bsimp [h18]) x1.rep.neg hnum hn hnorm hpos hrefs hyo

/-- After `_bc_do_sub(n1, n2)` at `0x80004b74`: `n1`'s sign. -/
theorem bsub_gt_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj}
    {x1 xr y : NumObj} {H : Heap} {F : List Blk} {n : Num} {v s : Nat}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hx1 : x1 ∈ L1 ++ xr :: L2)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 y.sb.pay)
    (h18 : R 18 = R0 18)
    (hnum : y.rep.num = ⟨false, v, s⟩) (hn : (⟨x1.rep.neg, v, s⟩ : Num) = n)
    (hnorm : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x80004b74#64 R M := by
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
  bc_run hlive hS [h8, h10, sg] at 0x80004b48
  exact bsub_signed hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 (by bsimp [h10])
    (by bsimp [h18]) x1.rep.neg hnum hn hnorm hpos hrefs hyo


/-- After `_bc_do_sub(n2, n1)` at `0x80004b1c`: `n2` back from the frame, the
opposite of its sign onto the new number. -/
theorem bsub_lt_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {L1 L2 : List NumObj}
    {x2 xr y : NumObj} {H : Heap} {F : List Blk} {n : Num} {v s : Nat}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hx2 : x2 ∈ L1 ++ xr :: L2)
    (hx2f : ldv .ld M (sp - 48) = BitVec.ofNat 64 x2.rep.p)
    (h10 : R 10 = BitVec.ofNat 64 y.sb.pay) (h18 : R 18 = R0 18)
    (hnum : y.rep.num = ⟨false, v, s⟩) (hn : (⟨!x2.rep.neg, v, s⟩ : Num) = n)
    (hnorm : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) (hyo : y.Owns) :
    DW live S Q 0x80004b1c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn2 := hb.nums x2 (List.mem_cons_of_mem _ hx2)
  num_facts hn2
  have sg := hn2.sign
  have hys := (hb.nums y List.mem_cons_self).shape
  have yp1 := hys.pLo; have yp2 := hys.pHi; have yp3 := hys.pAl
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  simp only [heapStart, heapEnd] at yp1 yp2
  have h2 := st.r2
  cases e : x2.rep.neg <;> rw [e] at sg <;> simp only [signWord_false, signWord_true] at sg
  · bc_run hlive hS [h2, h10, hx2f, sg] at 0x80004b48
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact bsub_signed hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 (by bsimp [h10])
      (by bsimp [h18]) true hnum (by rw [← hn, e]; rfl) hnorm hpos hrefs hyo
  · bc_run hlive hS [h2, h10, hx2f, sg] at 0x80004b48
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact bsub_signed hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 (by bsimp [h10])
      (by bsimp [h18]) false hnum (by rw [← hn, e]; rfl) hnorm hpos hrefs hyo

/-- Different signs, from `0x80004b34`: `_bc_do_add(n1, n2, scale_min)`. -/
theorem bsub_add {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (x1.rep.subM x2.rep smin))
    (ha : BinArgsM (L1 ++ xr :: L2) x1 x2 smin)
    (hl : 1 ≤ x1.rep.len ∧ 1 ≤ x2.rep.len) (hs : x1.rep.neg ≠ x2.rep.neg)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 x1.rep.p)
    (h11 : R 11 = BitVec.ofNat 64 x2.rep.p) (h13 : R 13 = BitVec.ofNat 64 smin)
    (h18 : R 18 = R0 18) :
    DW live S Q 0x80004b34#64 R M := by
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
    exact bsub_add_ret hlive cx hk (st.call cx.above
        ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
        fun a ha hf => hp.out a ha fun h => hf (by simp only [frameIn] at *; omega))
      hp.heap hr0 ha.m1 (by rw [hk1.get 8]; bsimp [h8]) h10' (by rw [hk1.get 18]; bsimp [h18])
      hp.num (by rw [NumRep.subM_of_len _ (fun h => hs h.1), NumRep.num_eq, NumRep.num_eq,
        num_sub_diff hs1.dsLen hs2.dsLen hs]; rfl)
      hp.norm hp.pos hp.refs hp.owns
  · exact hk.oom R1 Mt1 (sp - 48 - 96) (by omega) (by omega) hr2 fun a ha hf =>
      (hout a ha fun h => hf (by simp only [frameIn] at *; omega)).trans (st.out a ha hf)

/-- `|n1| > |n2|` with equal signs, from `0x80004b68`: `_bc_do_sub(n1, n2)`. -/
theorem bsub_gt {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (x1.rep.subM x2.rep smin))
    (ha : BinArgsM (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg = x2.rep.neg)
    (hc : x1.rep.cmpRep x2.rep = .gt)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h15 : R 15 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 smin) (h18 : R 18 = R0 18) :
    DW live S Q 0x80004b68#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 ha.m1).shape
  have hs2' := (hb.nums x2 ha.m2).shape
  obtain ⟨hle, hpos, hval⟩ := repGt_facts hs1 hs2' ha.n2 hs hc smin
  have hsz := ha.size
  have h2 := st.r2
  simp only [heapEnd] at hab
  bc_run hlive hS [h8, h15, h2] at 0x800045e8
  refine bc_do_sub_spec hlive (sp := sp - 48) (smin := smin) ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega),
      by omega, by omega, by omega⟩, by simp only [heapEnd]; omega, by bsimp [h2], by bsimp []; try decide⟩
    ⟨ha.m1, ha.m2, hle, by omega, hpos⟩ hb (by bsimp [h8]) (by bsimp [h15])
      (by bsimp [h12])
    ⟨fun R1 Mt1 H1 F1 y hk1 h10' hp => ?_, fun R1 Mt1 hr2 hout => ?_⟩
  · bsimp []
    have hm : ∀ a, OutHeap a → ¬ frameIn (sp - 48) 128 a → imgM Mt1 a = imgM M a := hp.out
    exact bsub_gt_ret hlive cx hk (st.call cx.above
        ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) hm)
      hp.heap hr0 ha.m1 (by rw [hk1.get 8]; bsimp [h8]) h10' (by rw [hk1.get 18]; bsimp [h18])
      hp.num hval hp.norm hp.pos hp.refs hp.owns
  · exact hk.oom R1 Mt1 (sp - 48 - 128) (by omega) (by omega) hr2 fun a ha hf =>
      (hout a ha fun h => hf (by simp only [frameIn] at *; omega)).trans (st.out a ha hf)

/-- `|n1| < |n2|` with equal signs, from `0x80004b10`: `_bc_do_sub(n2, n1)`. -/
theorem bsub_lt {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (x1.rep.subM x2.rep smin))
    (ha : BinArgsM (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg = x2.rep.neg)
    (hc : x1.rep.cmpRep x2.rep = .lt)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hx2f : ldv .ld M (sp - 48) = BitVec.ofNat 64 x2.rep.p)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h15 : R 15 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 smin) (h18 : R 18 = R0 18) :
    DW live S Q 0x80004b10#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 ha.m1).shape
  have hs2' := (hb.nums x2 ha.m2).shape
  obtain ⟨hle, hpos, hval⟩ := repLt_facts hs1 hs2' ha.n1 hs hc smin
  have hsz := ha.size
  have h2 := st.r2
  simp only [heapEnd] at hab
  bc_run hlive hS [h8, h15, h2] at 0x800045e8
  refine bc_do_sub_spec hlive (sp := sp - 48) (smin := smin) ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega),
      by omega, by omega, by omega⟩, by simp only [heapEnd]; omega, by bsimp [h2], by bsimp []; try decide⟩
    ⟨ha.m2, ha.m1, hle, by omega, hpos⟩ hb (by bsimp [h15]) (by bsimp [h8])
      (by bsimp [h12])
    ⟨fun R1 Mt1 H1 F1 y hk1 h10' hp => ?_, fun R1 Mt1 hr2 hout => ?_⟩
  · bsimp []
    have hm : ∀ a, OutHeap a → ¬ frameIn (sp - 48) 128 a → imgM Mt1 a = imgM M a := hp.out
    exact bsub_lt_ret hlive cx hk (st.call cx.above
        ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) hm)
      hp.heap hr0 ha.m2
      (by rw [ldv_congr .ld fun j hj => hm _ (by
            simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]; exact hx2f)
      h10' (by rw [hk1.get 18]; bsimp [h18])
      hp.num hval hp.norm hp.pos hp.refs hp.owns
  · exact hk.oom R1 Mt1 (sp - 48 - 128) (by omega) (by omega) hr2 fun a ha hf =>
      (hout a ha fun h => hf (by simp only [frameIn] at *; omega)).trans (st.out a ha hf)

/-! ## Equal magnitudes, equal signs: a zero -/

/-- After `bc_new_num` at `0x80004bb4`: the scale back from the frame,
`memset(n_value, 0, scale + 1)`, then the tail. -/
theorem bsub_zero_fill {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q sc : Nat} {L1 L2 : List NumObj}
    {xr y : NumObj} {H : Heap} {F : List Blk} {n : Num}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (y :: (L1 ++ xr :: L2)))
    (hr0 : ResSlot Mt0 L1 xr q) (hy : y.rep = zeroRep y.sb.pay y.db.pay 1 sc)
    (hn : Num.zero sc = n) (hsc : sc + 1 < 2 ^ 31)
    (h10 : R 10 = BitVec.ofNat 64 y.sb.pay) (h18 : R 18 = R0 18)
    (hsw : ldv .lw M (sp - 48) = BitVec.ofNat 64 sc) :
    DW live S Q 0x80004bb4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums y List.mem_cons_self
  num_facts hn0
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hv0 : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by rw [← hyp]; exact hn0.value
  have hls : y.rep.len + y.rep.scale = 1 + sc := by rw [hy]; rfl
  simp only [heapEnd] at hab
  have h2 := st.r2
  bc_run hlive hS [h2, h10, hsw, hv0, sxw_ofNat] at 0x80000890
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hob : OwnedBytes S y.rep.val (sc + 1) :=
    ⟨fun i hi => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
      by omega⟩
  refine memset_spec hlive hob _ (by bsimp [hv0]) (by bsimp [hsw]; try (congr 1; omega))
    (by bsimp []) fun R1 Mt1 hk1 hf => ?_
  bsimp []
  have hf' : Filled Mt1 M y.rep.val (1 + sc) fun _ => 0#8 := by
    rw [Nat.add_comm]; exact hf
  have hb' := BcHeap.zeroAgain hb hy hf'
  have hm : ∀ a, OutHeap a → imgM Mt1 a = imgM M a := fun a ha => hf.rest a (by
    simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  have r2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp [h2]
  have r8 : R1 8 = BitVec.ofNat 64 y.sb.pay := by rw [hk1.get 8]; bsimp [h10]
  bc_run hlive hS [r2, r8] at 0x80004b48
  exact bsub_tail hlive cx hk (st.call cx.above
      (by keeps_tac ((hk1.mono (by decide) : Keeps binTmp R1 _).trans
        (by keeps_tac Keeps.refl _ _ : Keeps binTmp _ R))) fun a ha _ => hm a ha)
    hb' hr0 (by bsimp [r8]) (by rw [hk1.get 18]; bsimp [h18]) (by rw [hy, zeroRep_num, hn])
    (by rw [hy]; exact Or.inl (Nat.le_refl 1)) (by rw [hy]; exact Nat.le_refl 1)
    (by rw [hy]; rfl)
    (by show y.rep.ptr ≠ 0; rw [hy]; show y.db.h + 16 ≠ 0; omega)

/-- The scale into the frame and `bc_new_num(1, scale)`, from `0x80004ba4`. -/
theorem bsub_zero_new {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q sc : Nat} {L1 L2 : List NumObj}
    {xr : NumObj} {H : Heap} {F : List Blk} {n : Num}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hn : Num.zero sc = n) (hsc : sc + 1 < 2 ^ 31)
    (h12 : R 12 = BitVec.ofNat 64 sc) (h18 : R 18 = R0 18) :
    DW live S Q 0x80004ba4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.r2
  bc_run hlive hS [h12, h2, sxw_ofNat] at 0x80004250
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hpro : MemOnly (fun a => sp - 48 ≤ a ∧ a < sp - 24)
      (writeLog M [(sp - 48, 4, BitVec.ofNat 64 sc)]) M := fun a ha => by
    rw [imgM_store_miss _ _ (by omega)]
  have hb' := hb.out_frame hpro fun a ha => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hsw : ldv .lw (writeLog M [(sp - 48, 4, BitVec.ofNat 64 sc)]) (sp - 48) = BitVec.ofNat 64 sc :=
    ldv_lw_hitN _ rfl (toNat_ofNat_mod32 (by omega)) (by omega)
  have hsf' : StackFrame S (sp - 48) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine bc_new_num_spec hlive hb'.newHeap hsf' (len := 1) (scale := sc)
    (by simp only [heapEnd]; omega) (by omega) (by omega) _ (by bsimp []) (by bsimp [h12])
    (by bsimp [h2]) (by bsimp []) ⟨fun R1 Mt1 H1 F1 y hk1 hp1 hr1 => ?_, fun R' Mt' hr2' hout' => ?_⟩
  · bsimp []
    have hm : ∀ a, OutHeap a → ¬ frameIn (sp - 48) 128 a →
        imgM Mt1 a = imgM (writeLog M [(sp - 48, 4, BitVec.ofNat 64 sc)]) a :=
      fun a ha hf => hp1.out a ha fun h => hf (by simp only [frameIn] at *; omega)
    exact bsub_zero_fill hlive cx hk ((st.low (Keeps.refl _ _) hpro).call cx.above
        ((hk1.mono (by decide) : Keeps binTmp R1 _).trans (by keeps_tac Keeps.refl _ _)) hm)
      (NewNumPost.insert hb' hp1) hr0 hp1.rep hn hsc hr1 (by rw [hk1.get 18]; bsimp [h18])
      (by rw [ldv_congr .lw fun j hj => hm _ (by
            simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]; exact hsw)
  · exact hk.oom R' Mt' (sp - 48 - 32) (by omega) (by omega) hr2' fun a ha hf =>
      (hout' a ha fun h => hf (by simp only [frameIn] at *; omega)).trans
        ((hpro a fun h => hf (by simp only [frameIn] at *; omega)).trans (st.out a ha hf))

/-- The larger of `max scale2 scale_min` and `n1`'s scale into `a2`, from
`0x80004b94`. -/
theorem bsub_zero_mid {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk} {n : Num}
    (cx : BinCtx S R0 sp q) (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp n)
    (ha : BinArgsM (L1 ++ xr :: L2) x1 x2 smin)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hn : Num.zero (resScale x1.rep.scale x2.rep.scale smin) = n)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (max x2.rep.scale smin)) (h18 : R 18 = R0 18) :
    DW live S Q 0x80004b94#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 ha.m1
  num_facts hn1
  have c1 := hn1.scale
  have hsz := ha.size
  bc_run hlive hS [h8, h12, c1, sxw_ofNat, toInt_ofNat_small] at 0x80004ba4
  · intro hge
    have hge' : x1.rep.scale ≤ max x2.rep.scale smin := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hge); omega
    exact bsub_zero_new hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hn
      (by simp only [resScale]; omega) (by bsimp [h12]; congr 1; simp only [resScale]; omega)
      (by bsimp [h18])
  · intro hlt
    have hlt' : max x2.rep.scale smin < x1.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
    bc_run hlive hS [h8, h12, c1, sxw_ofNat] at 0x80004ba4
    exact bsub_zero_new hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hn
      (by simp only [resScale]; omega) (by bsimp [c1]; congr 1; simp only [resScale]; omega)
      (by bsimp [h18])

/-- Equal magnitudes, equal signs, from `0x80004b84`: the larger of `n2`'s
scale and `scale_min` into `a2`. -/
theorem bsub_zero {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (x1.rep.subM x2.rep smin))
    (ha : BinArgsM (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg = x2.rep.neg)
    (hc : x1.rep.cmpRep x2.rep = .eq)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h15 : R 15 = BitVec.ofNat 64 x2.rep.p)
    (h13 : R 13 = BitVec.ofNat 64 smin) (h18 : R 18 = R0 18) :
    DW live S Q 0x80004b84#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn2 := hb.nums x2 ha.m2
  num_facts hn2
  have c2 := hn2.scale
  have hsz := ha.size
  have hn : Num.zero (resScale x1.rep.scale x2.rep.scale smin) = x1.rep.subM x2.rep smin :=
    repEq_facts hs hc smin
  bc_run hlive hS [h15, h13, c2, toInt_ofNat_small] at 0x80004b94
  · intro hge
    have hge' : smin ≤ x2.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hge); omega
    exact bsub_zero_mid hlive cx hk ha (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hn
      (by bsimp [h8]) (by bsimp [c2]; congr 1; omega) (by bsimp [h18])
  · intro hlt
    have hlt' : x2.rep.scale < smin := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
    bc_run hlive hS [h15, h13, c2] at 0x80004b94
    exact bsub_zero_mid hlive cx hk ha (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hn
      (by bsimp [h8]) (by bsimp [h13]; congr 1; omega) (by bsimp [h18])

/-! ## The comparison and the entry -/

/-- After `_bc_do_compare` at `0x80004af8`: `n2` and `scale_min` back from the
frame, then the zero, `n1 - n2` or `n2 - n1`. -/
theorem bsub_cmp {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (x1.rep.subM x2.rep smin))
    (ha : BinArgsM (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg = x2.rep.neg)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hx2f : ldv .ld M (sp - 48) = BitVec.ofNat 64 x2.rep.p)
    (hsm : ldv .ld M (sp - 48 + 8) = BitVec.ofNat 64 smin)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h18 : R 18 = R0 18)
    (h10 : R 10 = ordWord (x1.rep.cmpRep x2.rep)) :
    DW live S Q 0x80004af8#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.r2
  have htx : tohostAddr = 0x8001ad00 := rfl
  rcases hc : x1.rep.cmpRep x2.rep with _ | _ | _ <;> rw [hc] at h10 <;>
    simp only [ordWord] at h10
  · iterate 3 (all_goals (try (bc_run hlive hS [h2, h10, hx2f, hsm] at 0x80004b10)))
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact bsub_lt hlive cx hk ha hs hc (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0 hx2f
      (by bsimp [h8]) (by bsimp []) (by bsimp []) (by bsimp [h18])
  · iterate 3 (all_goals (try (bc_run hlive hS [h2, h10, hx2f, hsm] at 0x80004b84)))
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact bsub_zero hlive cx hk ha hs hc (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0
      (by bsimp [h8]) (by bsimp []) (by bsimp []) (by bsimp [h18])
  · iterate 3 (all_goals (try (bc_run hlive hS [h2, h10, hx2f, hsm] at 0x80004b68)))
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact bsub_gt hlive cx hk ha hs hc (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0
      (by bsimp [h8]) (by bsimp []) (by bsimp []) (by bsimp [h18])

/-- Equal signs, from `0x80004ae8`: `scale_min` and `n2` saved, then
`_bc_do_compare(n1, n2, FALSE, FALSE)`. -/
theorem bsub_eq {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (x1.rep.subM x2.rep smin))
    (ha : BinArgsM (L1 ++ xr :: L2) x1 x2 smin) (hs : x1.rep.neg = x2.rep.neg)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 x1.rep.p)
    (h11 : R 11 = BitVec.ofNat 64 x2.rep.p) (h13 : R 13 = BitVec.ofNat 64 smin)
    (h18 : R 18 = R0 18) :
    DW live S Q 0x80004ae8#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.r2
  have hpro : MemOnly (fun a => sp - 48 ≤ a ∧ a < sp - 24) (writeLog (writeLog M
      [(sp - 48 + 8, 8, R 13)]) [(sp - 48, 8, R 11)]) M := fun a ha => by
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hb' := hb.out_frame hpro fun a ha => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hn1 := hb'.nums x1 ha.m1
  have hn2 := hb'.nums x2 ha.m2
  bc_run hlive hS [h2] at 0x80003fb0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hx2f : ldv .ld (writeLog (writeLog M [(sp - 48 + 8, 8, R 13)]) [(sp - 48, 8, R 11)])
      (sp - 48) = BitVec.ofNat 64 x2.rep.p := by
    rw [ldv_store_hit, h11]
  have hsm : ldv .ld (writeLog (writeLog M [(sp - 48 + 8, 8, R 13)]) [(sp - 48, 8, R 11)])
      (sp - 48 + 8) = BitVec.ofNat 64 smin := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit, h13]
  refine do_compare_rep hlive hS hn1 hn2 ha.n1 ha.n2 ha.ne (u := false) _ (by bsimp [h10])
    (by bsimp [h11]) (by bsimp []) (by bsimp []; try decide) fun R1 hk1 h10' => ?_
  bsimp []
  exact bsub_cmp hlive cx hk ha hs
    (st.low ((hk1.mono (by decide) : Keeps binTmp R1 _).trans (by keeps_tac Keeps.refl _ _)) hpro)
    hb' hr0 hx2f hsm (by rw [hk1.get 8]; bsimp [h8]) (by rw [hk1.get 18]; bsimp [h18]) h10'

/-- The sign test at `0x80004ae4`: `a6`, `a4` the operands' sign words. -/
theorem bsub_dispatch {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj}
    {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : BinCtx S R0 sp q)
    (hk : BinK live S Q R0 Mt0 L1 L2 xr q sp (x1.rep.subM x2.rep smin))
    (ha : BinArgsM (L1 ++ xr :: L2) x1 x2 smin)
    (hadd : x1.rep.neg ≠ x2.rep.neg → 1 ≤ x1.rep.len ∧ 1 ≤ x2.rep.len)
    (st : BinAt S Mt0 M R0 R sp q) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h10 : R 10 = BitVec.ofNat 64 x1.rep.p)
    (h11 : R 11 = BitVec.ofNat 64 x2.rep.p) (h13 : R 13 = BitVec.ofNat 64 smin)
    (h18 : R 18 = R0 18) (h16 : R 16 = signWord x1.rep.neg) (h14 : R 14 = signWord x2.rep.neg) :
    DW live S Q 0x80004ae4#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  cases e1 : x1.rep.neg <;> cases e2 : x2.rep.neg <;> rw [e1] at h16 <;> rw [e2] at h14 <;>
    simp only [signWord_false, signWord_true] at h16 h14
  all_goals bc_run hlive hS [h16, h14] at 0x80004b34 0x80004ae8
  all_goals first
    | exact bsub_eq hlive cx hk ha (by rw [e1, e2]) (st.keeps (by keeps_tac Keeps.refl _ _)) hb hr0
        (by bsimp [h8]) (by bsimp [h10]) (by bsimp [h11]) (by bsimp [h13]) (by bsimp [h18])
    | exact bsub_add hlive cx hk ha (hadd (by rw [e1, e2]; decide)) (by rw [e1, e2]; decide)
        (st.keeps (by keeps_tac Keeps.refl _ _))
        hb hr0 (by bsimp [h8]) (by bsimp [h10]) (by bsimp [h11]) (by bsimp [h13]) (by bsimp [h18])

/-- **`bc_sub(n1, n2, result, scale_min)`** at `0x80004ac4` as the machine
computes it, for two normalized numbers of the heap, not both empty, and the
result slot `q` holding `x` of the heap: the new number for
`NumRep.subM n1 n2 scale_min` in the slot, `x` freed once (`BinK.ret`), or
`out_of_memory` (`BinK.oom`). -/
theorem bc_sub_specM {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj} {x1 x2 xr : NumObj}
    {H : Heap} {F : List Blk}
    (cx : BinCtx S R sp q) (ha : BinArgsM (L1 ++ xr :: L2) x1 x2 smin)
    (hadd : x1.rep.neg ≠ x2.rep.neg → 1 ≤ x1.rep.len ∧ 1 ≤ x2.rep.len)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr q)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 q) (h13 : R 13 = BitVec.ofNat 64 smin)
    (hk : BinK live S Q R M L1 L2 xr q sp (x1.rep.subM x2.rep smin)) :
    DW live S Q 0x80004ac4#64 R M := by
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
  bc_run hlive hS [h2, h10, h11, h12, sg1, sg2, word_sub48] at 0x80004ae4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact bsub_dispatch hlive cx hk ha hadd (st _ (by bsimp []) (by bsimp [h12])
    (by keeps_tac Keeps.refl _ _)) hb' hr (by bsimp [h10]) (by bsimp [h10]) (by bsimp [h11])
    (by bsimp [h13]) (by bsimp []) (by bsimp [sg1]) (by bsimp [sg2])

/-- **`bc_sub(n1, n2, result, scale_min)`** at `0x80004ac4`: the new number
for `Num.sub n1 n2 scale_min`, when an operand without integer digits meets a
nonzero one (`BinArgs.e1`/`.e2`). -/
theorem bc_sub_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {sp q smin : Nat} {L1 L2 : List NumObj} {x1 x2 xr : NumObj}
    {H : Heap} {F : List Blk}
    (cx : BinCtx S R sp q) (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin)
    (hadd : x1.rep.neg ≠ x2.rep.neg → 1 ≤ x1.rep.len ∧ 1 ≤ x2.rep.len)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr q)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 q) (h13 : R 13 = BitVec.ofNat 64 smin)
    (hk : BinK live S Q R M L1 L2 xr q sp (Num.sub x1.rep.num x2.rep.num smin)) :
    DW live S Q 0x80004ac4#64 R M := by
  have hs1 := (hb.nums x1 ha.m1).shape
  have hs2 := (hb.nums x2 ha.m2).shape
  refine bc_sub_specM hlive cx (ha.toM hs2) hadd hb hr h10 h11 h12 h13 ?_
  rwa [NumRep.subM_eq smin hs1 hs2 ha.n1 ha.n2 ha.e1 ha.e2]

end Dc.Mach
