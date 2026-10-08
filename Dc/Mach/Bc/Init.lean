import Dc.Mach.Bc.NumStore

/-!
# `bc_init_numbers` (`lib/number.c`)

```
80004948 addi sp,sp,-16 ; 8000494c li a1,0 ; 80004950 li a0,1 ; 80004954 sd ra,8(sp)
80004958 jal bc_new_num ; 8000495c auipc a5,0x18 ; 80004960 sd a0,1132(a5) (_zero_)
80004964 li a1,0 ; 80004968 li a0,1 ; 8000496c jal bc_new_num ; 80004970 ld a5,32(a0)
80004974 auipc a4,0x18 ; 80004978 sd a0,1100(a4) (_one_) ; 8000497c li a0,1
80004980 sb a0,0(a5) ; 80004984 li a1,0 ; 80004988 jal bc_new_num ; 8000498c ld a5,32(a0)
80004990 auipc a4,0x18 ; 80004994 sd a0,1064(a4) (_two_) ; 80004998 li a4,2
8000499c sb a4,0(a5) ; 800049a0 ld ra,8(sp) ; 800049a4 addi sp,sp,16 ; 800049a8 ret
```

`bc_init_numbers_spec`: three numbers `0`, `1`, `2` (`InitPost`), their
structs' addresses in `_zero_`, `_one_`, `_two_`, or `out_of_memory`.
Each `bc_new_num(1, 0)` call goes through `init_call`; the segments between
calls (`init_zero`, `init_one`, `init_two`) carry `InitAt`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The bytes of the three constant pointers `_two_`, `_one_`, `_zero_`. -/
abbrev constBytes (a : Nat) : Prop := twoAddr ≤ a ∧ a < zeroAddr + 8

theorem constBytes_out {a : Nat} (h : constBytes a) : OutHeap a := by
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at h ⊢
  have h2 : twoAddr = 0x8001cdb8 := rfl
  have h0 : zeroAddr = 0x8001cdc8 := rfl
  omega

/-- The registers `bc_init_numbers` may change. -/
abbrev initClob : List Nat := [10, 11, 12, 13, 14, 15]

/-- `bc_init_numbers`'s result: the heap extended by `0`, `1` and `2`
(`n_len = 1`, `n_scale = 0`, `n_refs = 1`), their structs in the three
globals. -/
structure InitPost (S : Nat → Prop) (Mt0 Mt : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (sp : Nat) (z o t : NumObj) : Prop where
  heap : BcHeap S Mt H F (t :: o :: z :: L)
  zero : z.rep = zeroRep z.sb.pay z.db.pay 1 0
  one : o.rep = { zeroRep o.sb.pay o.db.pay 1 0 with ds := [1] }
  two : t.rep = { zeroRep t.sb.pay t.db.pay 1 0 with ds := [2] }
  gZero : ldv .ld Mt zeroAddr = BitVec.ofNat 64 z.sb.pay
  gOne : ldv .ld Mt oneAddr = BitVec.ofNat 64 o.sb.pay
  gTwo : ldv .ld Mt twoAddr = BitVec.ofNat 64 t.sb.pay
  out : OutFrame (fun a => frameIn sp 48 a ∨ constBytes a) Mt Mt0

/-- `bc_init_numbers`'s continuations. -/
structure InitK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (L : List NumObj) (sp : Nat) : Prop where
  ret : ∀ R' Mt' H' F' z o t, Keeps initClob R' R0 → InitPost S Mt0 Mt' H' F' L sp z o t →
    DW live S Q (R0 1) R' Mt'
  oom : ∀ R' Mt', R' 2 = BitVec.ofNat 64 (sp - 48) →
    OutFrame (fun a => frameIn sp 48 a ∨ constBytes a) Mt' Mt0 →
    DW live S Q 0x80002bcc#64 R' Mt'

/-- `bc_init_numbers`'s fixed context: its 48-byte stack window (its own
16 bytes and `bc_new_num`'s 32), above the heap, the owned constant words,
and the entry's `sp` and return address. -/
structure InitCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp : Nat) : Prop where
  frame : StackFrame S sp 48
  above : heapEnd + 48 ≤ sp
  consts : ∀ a, constBytes a → S a
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0

/-- Inside `bc_init_numbers` (after its prologue): `sp` lowered by 16, the
return address saved at `sp - 8`, callee-kept registers unchanged, and only
the stack window and the constant words changed off the heap. -/
structure InitAt (S : Nat → Prop) (Mt0 Mt : Mem) (R0 R : Nat → BitVec 64) (sp : Nat) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 16)
  ra : ldv .ld Mt (sp - 8) = R0 1
  regs : ∀ z, z ≠ 1 → z ≠ 2 → z ∉ initClob → R z = R0 z
  out : OutFrame (fun a => frameIn sp 48 a ∨ constBytes a) Mt Mt0

/-- `InitAt` across straight-line code that writes only clobbered registers,
the return-address register, and bytes off the saved word. -/
theorem InitAt.step {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp : Nat}
    (st : InitAt S Mt0 M R0 R sp) (hr2 : R' 2 = R 2) (hk : Keeps (1 :: initClob) R' R)
    (hra : ldv .ld M' (sp - 8) = ldv .ld M (sp - 8))
    (hout : ∀ a, OutHeap a → ¬ frameIn sp 48 a → ¬ constBytes a → imgM M' a = imgM M a) :
    InitAt S Mt0 M' R0 R' sp where
  r2 := hr2.trans st.r2
  ra := hra.trans st.ra
  regs z z1 z2 zc := (hk z (by simp only [initClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at zc ⊢; omega)).trans (st.regs z z1 z2 zc)
  out a ha hf := (hout a ha (fun h => hf (.inl h)) fun h => hf (.inr h)).trans (st.out a ha hf)

/-- Entering `bc_init_numbers`'s body after its prologue. -/
theorem InitAt.enter {S : Nat → Prop} {Mt M : Mem} {R R' : Nat → BitVec 64} {sp : Nat}
    (hr2 : R' 2 = BitVec.ofNat 64 (sp - 16)) (hra : ldv .ld M (sp - 8) = R 1)
    (hk : Keeps (1 :: 2 :: initClob) R' R) (hout : MemOnly (frameIn sp 48) M Mt) :
    InitAt S Mt M R R' sp where
  r2 := hr2
  ra := hra
  regs z z1 z2 zc := hk z (by
    simp only [initClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at zc ⊢; omega)
  out a _ hf := hout a fun h => hf (.inl h)

/-- Leaving `bc_init_numbers`: `ra` and `sp` restored, the rest kept. -/
theorem InitAt.keeps {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp : Nat}
    (st : InitAt S Mt0 M R0 R sp) (h1 : R' 1 = R0 1) (h2 : R' 2 = R0 2)
    (hk : Keeps (1 :: 2 :: initClob) R' R) : Keeps initClob R' R0 := fun z hz => by
  by_cases z1 : z = 1
  · subst z1; exact h1
  by_cases z2 : z = 2
  · subst z2; exact h2
  refine (hk z ?_).trans (st.regs z z1 z2 hz)
  simp only [initClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz ⊢; omega

/-- **A `bc_new_num(1, 0)` call from `bc_init_numbers`** (at `0x80004250`):
the heap gains a fresh zero `x`, `InitAt` survives, the constant words are
untouched; out of memory reaches `InitK.oom`. -/
theorem init_call {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 Mc : Mem} {R0 Rc : Nat → BitVec 64} {sp : Nat} {L0 L : List NumObj} {H : Heap}
    {F : List Blk} (cx : InitCtx S R0 sp) (hk : InitK live S Q R0 Mt0 L0 sp)
    (hb : BcHeap S Mc H F L) (st : InitAt S Mt0 Mc R0 Rc sp)
    (h10 : Rc 10 = BitVec.ofNat 64 1) (h11 : Rc 11 = BitVec.ofNat 64 0)
    (hal : (Rc 1).toNat % 4 = 0)
    (hret : ∀ R1 Mt1 H1 F1 x, BcHeap S Mt1 H1 F1 (x :: L) →
      x.rep = zeroRep x.sb.pay x.db.pay 1 0 → R1 10 = BitVec.ofNat 64 x.sb.pay →
      InitAt S Mt0 Mt1 R0 R1 sp → (∀ a, constBytes a → imgM Mt1 a = imgM Mc a) →
      DW live S Q (Rc 1) R1 Mt1) :
    DW live S Q 0x80004250#64 Rc Mc := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapEnd] at hab
  have hsf' : StackFrame S (sp - 16) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine bc_new_num_spec hlive hb.newHeap hsf' (by simp only [heapEnd]; omega) (by decide)
    (Nat.le_refl _) Rc h10 h11 st.r2 hal ⟨fun R1 Mt1 H1 F1 x hk1 hp1 hr1 => ?_, fun R' Mt' hr2 hout => ?_⟩
  · refine hret R1 Mt1 H1 F1 x (NewNumPost.insert hb hp1) hp1.rep hr1 ?_ fun a ha => ?_
    · refine st.step (hk1.get 2) (fun z hz => hk1 z fun h => hz (List.mem_cons_of_mem _ h)) ?_
        fun a ha _ _ => hp1.out a ha fun h => by simp only [frameIn] at *; omega
      refine ldv_congr .ld fun j hj => hp1.out _ ?_ ?_
      · simp only [widthOfM] at hj
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
      · simp only [frameIn, widthOfM] at *; omega
    · exact hp1.out a (constBytes_out ha) fun h => by
        simp only [frameIn, constBytes] at h ha
        have h0 : zeroAddr = 0x8001cdc8 := rfl
        omega
  · refine hk.oom R' Mt' (by rw [hr2, show sp - 16 - 32 = sp - 48 by omega]) fun a ha hf => ?_
    rw [hout a ha fun h => hf (.inl (by simp only [frameIn] at *; omega))]
    exact st.out a ha hf

/-- Where a fresh `bc_new_num(1, 0)` result lives: its struct and one-byte
digit buffer in the heap, and the struct's `n_value` word. -/
structure FreshAt (M : Mem) (x : NumObj) : Prop where
  val : x.rep.val = x.db.pay
  p : x.rep.p = x.sb.pay
  dLo : heapStart ≤ x.db.pay
  dHi : x.db.pay + 1 ≤ heapEnd
  sLo : heapStart ≤ x.sb.pay
  sHi : x.sb.pay + 40 ≤ heapEnd
  sAl : x.sb.pay % 8 = 0
  value : ldv .ld M (x.sb.pay + 32) = BitVec.ofNat 64 x.db.pay

theorem FreshAt.of_heap {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {x : NumObj} (hb : BcHeap S M H F (x :: L)) (hx : x.rep = zeroRep x.sb.pay x.db.pay 1 0) :
    FreshAt M x := by
  have hn := hb.nums x List.mem_cons_self
  have hs := hn.shape
  have hv : x.rep.val = x.db.pay := by rw [hx]; rfl
  have hp : x.rep.p = x.sb.pay := by rw [hx]; rfl
  have hl : x.rep.len + x.rep.scale = 1 := by rw [hx]; rfl
  have h1 := hs.vLo; have h2 := hs.vHi; have h3 := hs.pLo; have h4 := hs.pHi; have h5 := hs.pAl
  have h6 := hs.ptrLe
  have hval := hn.value
  rw [hp, hv] at hval
  exact ⟨hv, hp, by omega, by omega, by omega, by omega, by omega, hval⟩

/-- The pointer to a fresh `bc_new_num(1, 0)` result stored in a constant
word, then its digit set to `d`. -/
theorem init_store {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {x : NumObj} (hb : BcHeap S M H F (x :: L)) (hx : x.rep = zeroRep x.sb.pay x.db.pay 1 0)
    {g : Nat} (hg1 : twoAddr ≤ g) (hg2 : g ≤ zeroAddr) {d : Nat} (hd : d < 10) :
    BcHeap S (writeLog (writeLog M [(g, 8, BitVec.ofNat 64 x.sb.pay)])
      [(x.db.pay, 1, BitVec.ofNat 64 d)]) H F
      ({ x with rep := { x.rep with ds := x.rep.ds.set 0 d } } :: L) := by
  have fa := FreshAt.of_heap hb hx
  have hb1 := hb.out_frame (MemOnly.store M g 8 (BitVec.ofNat 64 x.sb.pay)) fun a ha =>
    constBytes_out ⟨by omega, by simp only [zeroAddr] at *; omega⟩
  have hb2 := BcHeap.setDigit (L1 := []) hb1 (i := 0) (d := d) (by rw [hx]; simp [zeroRep]) hd
    (v := BitVec.ofNat 64 d) (by
      rw [sbData_eq]; apply BitVec.eq_of_toNat_eq
      simp only [lo8, toNat_setWidth8, BitVec.toNat_ofNat]; omega)
  rw [fa.val] at hb2
  exact hb2

/-- Off the heap and the constant words, the two stores of `init_store`
change nothing. -/
theorem init_store_out {M : Mem} {x : NumObj} (fa : FreshAt M x) {g : Nat} (hg1 : twoAddr ≤ g)
    (hg2 : g ≤ zeroAddr) (d : Nat) :
    ∀ a, OutHeap a → ¬ constBytes a →
      imgM (writeLog (writeLog M [(g, 8, BitVec.ofNat 64 x.sb.pay)])
        [(x.db.pay, 1, BitVec.ofNat 64 d)]) a = imgM M a := by
  intro a ha hc
  have h1 := fa.dLo; have h2 := fa.dHi
  simp only [OutHeap, constBytes, heapStart, heapEnd] at *
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by simp only [zeroAddr] at *; omega)]

/-- `bc_init_numbers`'s result from the heap after the third call: `_two_`
stored and its digit set. -/
theorem init_post {S : Nat → Prop} {Mt0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {sp : Nat} {z o t : NumObj} (hb : BcHeap S M H F (t :: o :: z :: L))
    (ht : t.rep = zeroRep t.sb.pay t.db.pay 1 0)
    (ho : o.rep = { zeroRep o.sb.pay o.db.pay 1 0 with ds := [1] })
    (hz : z.rep = zeroRep z.sb.pay z.db.pay 1 0)
    (gz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.sb.pay)
    (go : ldv .ld M oneAddr = BitVec.ofNat 64 o.sb.pay)
    (hout : OutFrame (fun a => frameIn sp 48 a ∨ constBytes a) M Mt0) :
    InitPost S Mt0 (writeLog (writeLog M [(twoAddr, 8, BitVec.ofNat 64 t.sb.pay)])
      [(t.db.pay, 1, BitVec.ofNat 64 2)]) H F L sp z o
      { t with rep := { t.rep with ds := t.rep.ds.set 0 2 } } := by
  have fa := FreshAt.of_heap hb ht
  have h1 := fa.dLo
  simp only [heapStart] at h1
  exact
    { heap := init_store hb ht (Nat.le_refl _) (by decide) (by decide)
      zero := hz
      one := ho
      two := by dsimp only; rw [ht]; rfl
      gZero := by
        rw [ldv_ld_miss _ _ (by simp only [zeroAddr]; omega), ldv_ld_miss _ _ (by decide)]
        exact gz
      gOne := by
        rw [ldv_ld_miss _ _ (by simp only [oneAddr]; omega), ldv_ld_miss _ _ (by decide)]
        exact go
      gTwo := by
        rw [ldv_ld_miss _ _ (by simp only [twoAddr]; omega)]
        exact ldv_store_hit _ _ _
      out := fun a ha hf =>
        (init_store_out fa (Nat.le_refl _) (by decide) 2 a ha fun h => hf (.inr h)).trans
          (hout a ha hf) }

/-- After the third call, from `0x8000498c`: `_two_`, its digit, and the
epilogue. -/
theorem init_two {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp : Nat} {L : List NumObj} {H : Heap}
    {F : List Blk} {z o t : NumObj} (cx : InitCtx S R0 sp) (hk : InitK live S Q R0 Mt0 L sp)
    (hb : BcHeap S M H F (t :: o :: z :: L)) (ht : t.rep = zeroRep t.sb.pay t.db.pay 1 0)
    (ho : o.rep = { zeroRep o.sb.pay o.db.pay 1 0 with ds := [1] })
    (hz : z.rep = zeroRep z.sb.pay z.db.pay 1 0)
    (gz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.sb.pay)
    (go : ldv .ld M oneAddr = BitVec.ofNat 64 o.sb.pay)
    (hr10 : R 10 = BitVec.ofNat 64 t.sb.pay) (st : InitAt S Mt0 M R0 R sp) :
    DW live S Q 0x8000498c#64 R M := by
  have fa := FreshAt.of_heap hb ht
  have hval := fa.value
  have h1 := fa.dLo; have h2 := fa.dHi; have h3 := fa.sLo; have h4 := fa.sHi; have h5 := fa.sAl
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapStart, heapEnd] at h1 h2 h3 h4 hab
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hr2 := st.r2
  have hra : ldv .ld M (sp - 16 + 8) = R0 1 := by rw [show sp - 16 + 8 = sp - 8 by omega]; exact st.ra
  have hal := cx.al
  bc_run hlive hS [hr10, hval, hr2, hra, ldv_ld_miss]
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | exact fun b hb' => cx.consts b (by
        have := of_mem_accAddrs hb'
        have e0 : zeroAddr = 0x8001cdc8 := rfl; have e2 : twoAddr = 0x8001cdb8 := rfl
        simp only [constBytes]; omega)
    | exact hal
    | skip
  exact hk.ret _ _ H F z o _
    (st.keeps (by bsimp []) (by bsimp [cx.sp0]; congr 1; omega) (by keeps_tac Keeps.refl _ _))
    (init_post hb ht ho hz gz go st.out)

/-- After the second call, from `0x80004970`: `_one_`, its digit, and the
third call. -/
theorem init_one {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp : Nat} {L : List NumObj} {H : Heap}
    {F : List Blk} {z o : NumObj} (cx : InitCtx S R0 sp) (hk : InitK live S Q R0 Mt0 L sp)
    (hb : BcHeap S M H F (o :: z :: L)) (ho : o.rep = zeroRep o.sb.pay o.db.pay 1 0)
    (hz : z.rep = zeroRep z.sb.pay z.db.pay 1 0)
    (gz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.sb.pay)
    (hr10 : R 10 = BitVec.ofNat 64 o.sb.pay) (st : InitAt S Mt0 M R0 R sp) :
    DW live S Q 0x80004970#64 R M := by
  have fa := FreshAt.of_heap hb ho
  have hval := fa.value
  have h1 := fa.dLo; have h2 := fa.dHi; have h3 := fa.sLo; have h4 := fa.sHi; have h5 := fa.sAl
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapStart, heapEnd] at h1 h2 h3 h4 hab
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hr2 := st.r2
  bc_run hlive hS [hr10, hval, hr2] at 0x80004988
  all_goals first
    | exact fun b hb' => cx.consts b (by
        have := of_mem_accAddrs hb'
        have e0 : zeroAddr = 0x8001cdc8 := rfl; have e2 : twoAddr = 0x8001cdb8 := rfl
        simp only [constBytes]; omega)
    | skip
  apply st_80004988 hlive
  have e0 : zeroAddr = 0x8001cdc8 := rfl; have e1 : oneAddr = 0x8001cdc0 := rfl
  have e2 : twoAddr = 0x8001cdb8 := rfl
  have hb' := init_store hb ho (g := oneAddr) (by decide) (by decide) (d := 1) (by decide)
  refine init_call hlive cx hk hb' (st.step (by bsimp []) (by keeps_tac Keeps.refl _ _)
      (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)])
      fun a ha _ hc => init_store_out fa (g := oneAddr) (by decide) (by decide) 1 a ha hc)
    (by bsimp []) (by bsimp []) (by bsimp []; try decide)
    fun R1 Mt1 H1 F1 t hb3 ht hr10' st3 hc => ?_
  bsimp []
  have gz' : ldv .ld Mt1 zeroAddr = BitVec.ofNat 64 z.sb.pay := by
    rw [ldv_congr .ld fun j hj => hc _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩,
      ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
    exact gz
  have go' : ldv .ld Mt1 oneAddr = BitVec.ofNat 64 o.sb.pay := by
    rw [ldv_congr .ld fun j hj => hc _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩,
      ldv_ld_miss _ _ (by omega)]
    exact ldv_store_hit _ _ _
  exact init_two hlive cx hk hb3 ht (by dsimp only; rw [ho]; rfl) hz gz' go' hr10' st3

/-- After the first call, from `0x8000495c`: `_zero_` and the second call. -/
theorem init_zero {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp : Nat} {L : List NumObj} {H : Heap}
    {F : List Blk} {z : NumObj} (cx : InitCtx S R0 sp) (hk : InitK live S Q R0 Mt0 L sp)
    (hb : BcHeap S M H F (z :: L)) (hz : z.rep = zeroRep z.sb.pay z.db.pay 1 0)
    (hr10 : R 10 = BitVec.ofNat 64 z.sb.pay) (st : InitAt S Mt0 M R0 R sp) :
    DW live S Q 0x8000495c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapEnd] at hab
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hr2 := st.r2
  bc_run hlive hS [hr10, hr2] at 0x8000496c
  all_goals first
    | exact fun b hb' => cx.consts b (by
        have := of_mem_accAddrs hb'
        have e0 : zeroAddr = 0x8001cdc8 := rfl; have e2 : twoAddr = 0x8001cdb8 := rfl
        simp only [constBytes]; omega)
    | skip
  apply st_8000496c hlive
  have e0 : zeroAddr = 0x8001cdc8 := rfl; have e2 : twoAddr = 0x8001cdb8 := rfl
  have hb' := hb.out_frame (MemOnly.store M zeroAddr 8 (BitVec.ofNat 64 z.sb.pay)) fun a ha =>
    constBytes_out ⟨by omega, ha.2⟩
  refine init_call hlive cx hk hb' (st.step (by bsimp []) (by keeps_tac Keeps.refl _ _)
      (by rw [ldv_ld_miss _ _ (by omega)])
      fun a _ _ hc => imgM_store_miss _ _ (by simp only [constBytes] at hc; omega))
    (by bsimp []) (by bsimp []) (by bsimp []; try decide)
    fun R1 Mt1 H1 F1 o hb2 ho hr10' st2 hc => ?_
  bsimp []
  have gz : ldv .ld Mt1 zeroAddr = BitVec.ofNat 64 z.sb.pay := by
    rw [ldv_congr .ld fun j hj => hc _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩]
    exact ldv_store_hit _ _ _
  exact init_one hlive cx hk hb2 ho hz gz hr10' st2

/-- **`bc_init_numbers`** at `0x80004948`: three `bc_new_num(1, 0)` calls make
`0`, `1`, `2` (`InitPost`), stored in `_zero_`, `_one_`, `_two_`; or
`out_of_memory`. -/
theorem bc_init_numbers_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} {F : List Blk} {L : List NumObj}
    (hb : BcHeap S Mt H F L) {sp : Nat} {R : Nat → BitVec 64} (cx : InitCtx S R sp)
    (hk : InitK live S Q R Mt L sp) :
    DW live S Q 0x80004948#64 R Mt := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapEnd] at hab
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := cx.sp0
  bc_run hlive hS [h2] at 0x80004958
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  apply st_80004958 hlive
  have hfr : MemOnly (frameIn sp 48) (writeLog Mt [(sp - 16 + 8, 8, R 1)]) Mt :=
    (MemOnly.store Mt _ 8 _).mono fun a ha => by simp only [frameIn] at *; omega
  have hb' := hb.out_frame hfr fun a ha => by
    simp only [OutHeap, frameIn, heapStart, heapEnd, freeListAddr, bcFreeAddr] at *; omega
  refine init_call hlive cx hk hb'
    (InitAt.enter (by bsimp [h2]) (by rw [show sp - 8 = sp - 16 + 8 by omega]; exact ldv_store_hit _ _ _)
      (by keeps_tac Keeps.refl _ _) hfr)
    (by bsimp []) (by bsimp []) (by bsimp []; try decide)
    fun R1 Mt1 H1 F1 z hb1 hz hr10 st1 _ => ?_
  bsimp []
  exact init_zero hlive cx hk hb1 hz hr10 st1

end Dc.Mach
