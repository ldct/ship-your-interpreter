import Dc.Mach.Bc.Free
import Dc.Mach.Bc.New

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
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `_two_`, `_one_`, `_zero_`. -/
abbrev twoAddr : Nat := 0x8001cdb8
abbrev oneAddr : Nat := 0x8001cdc0
abbrev zeroAddr : Nat := 0x8001cdc8

/-- The bytes of the three constant pointers. -/
abbrev constBytes (a : Nat) : Prop := twoAddr ≤ a ∧ a < zeroAddr + 8

theorem constBytes_out {a : Nat} (h : constBytes a) : OutHeap a := by
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, twoAddr, zeroAddr] at *
  omega

/-- A number heap supplies `bc_new_num`'s precondition. -/
theorem BcHeap.newHeap {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S Mt H F L) : NewHeap S Mt H F :=
  { inv := h.heap
    dead := h.dead
    deadOK := h.deadLive
    nodup := (List.nodup_append.mp h.distinct).1
    glob := h.globOwn }

/-- Every byte of a live block lies in the heap. -/
theorem live_in_heap {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {b : Blk}
    (hb : b ∈ H.live) {a : Nat} (ha : b.In a) : heapStart ≤ a ∧ a < heapEnd := by
  have fb := hi.blk (List.mem_append_right _ hb)
  have h1 : 2147603920 ≤ b.h := fb.lo
  have h2 : b.fin ≤ H.brk := fb.fin
  have h3 : H.brk ≤ 2273312768 := fb.top
  have hp : b.pay = b.h + 16 := rfl
  simp only [Blk.In] at ha
  simp only [heapStart, heapEnd]
  omega

/-- A number heap survives any memory change confined to bytes outside the
heap and the allocator's and `_bc_Free_list`'s words. -/
theorem BcHeap.out_frame {S : Nat → Prop} {Mt Mt' : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S Mt H F L) {P : Nat → Prop} (hfr : MemOnly P Mt' Mt)
    (hP : ∀ a, P a → OutHeap a) : BcHeap S Mt' H F L :=
  h.transport (fun a ha => hfr a fun hp => OutHeap.not_alloc h.heap (hP a hp) ha)
    (fun b hb a ha => hfr a fun hp => (hP a hp).1 (live_in_heap h.heap hb ha))
    (fun j hj => hfr _ fun hp => (hP _ hp).2.2 ⟨by omega, by omega⟩)

/-- A digit byte rewritten. -/
theorem NumAt.setDigit {Mt : Mem} {o : NumRep} (h : NumAt Mt o) {i d : Nat}
    (hi : i < o.len + o.scale) (hd : d < 10) {v : BitVec 64} (hv : sbData v = BitVec.ofNat 8 d) :
    NumAt (writeLog Mt [(o.val + i, 1, v)]) { o with ds := o.ds.set i d } := by
  have hs := h.shape
  have hsep := hs.sep; have hpl := hs.ptrLe
  have hshape : NumShape { o with ds := o.ds.set i d } :=
    { hs with
      dsLen := by simp only [List.length_set]; exact hs.dsLen
      dig := fun e he => by
        rcases List.mem_or_eq_of_mem_set he with he | rfl
        · exact hs.dig e he
        · exact hd }
  have hmiss : ∀ off, off < 40 → o.val + i < o.p + off ∨ o.p + off + 1 ≤ o.val + i := by
    intro off hoff; omega
  refine ⟨hshape, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.sign
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.len
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.scale
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.refs
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.ptr
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.value
  · by_cases hji : j = i
    · subst hji
      rw [imgM_sb, hv]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hs.dsLen]; exact hj),
        Option.getD_some]
    · rw [imgM_store_miss _ _ (by omega)]
      rw [h.digit j hj]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hji)]

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

/-- The memory frame of a `bc_new_num` call made from `bc_init_numbers`'s
frame, composed with the earlier part of the run. -/
theorem OutFrame.compose {fr fr' : Nat → Prop} {M2 M1 M0 : Mem} (h2 : OutFrame fr' M2 M1)
    (h1 : OutFrame fr M1 M0) (hsub : ∀ a, fr' a → fr a) : OutFrame fr M2 M0 :=
  fun a ha hf => (h2 a ha fun h => hf (hsub a h)).trans (h1 a ha hf)

/-- **`bc_init_numbers`** at `0x80004948`. -/
theorem bc_init_numbers_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} {F : List Blk} {L : List NumObj}
    (hb : BcHeap S Mt H F L) {sp : Nat} (hsf : StackFrame S sp 48) (hsp : heapEnd + 48 ≤ sp)
    (hg : ∀ a, constBytes a → S a)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : InitK live S Q R Mt L sp) :
    DW live S Q 0x80004948#64 R Mt := by
  have hi := hb.heap
  have hspl := hsf.hi; have hspa := hsf.al; have hslo := hsf.lo
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapEnd] at hsp
  have hsf' : StackFrame S (sp - 16) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  have hgo : ∀ x, constBytes x → OutHeap x := fun x hx => constBytes_out hx
  -- the prologue and the first call
  bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [h2] at 0x80004958
  all_goals try (exact frame_acc hsf (by omega) (by omega))
  generalize hM0 : writeLog Mt [(sp - 16 + 8, 8, R 1)] = M0 at *
  have hM0f : MemOnly (frameIn sp 48) M0 Mt := by
    rw [← hM0]; exact (MemOnly.store Mt _ 8 _).mono fun a ha => by simp only [frameIn] at *; omega
  have hra0 : ldv .ld M0 (sp - 8) = R 1 := by
    rw [← hM0, show sp - 8 = sp - 16 + 8 by omega, ldv_store_hit]
  have hb0 : BcHeap S M0 H F L :=
    hb.out_frame hM0f fun a ha => by
      simp only [OutHeap, frameIn, heapStart, heapEnd, freeListAddr, bcFreeAddr] at *; omega
  apply st_80004958 hlive
  refine bc_new_num_spec hlive hb0.newHeap hsf' (by simp only [heapEnd]; omega) (by decide)
    (Nat.le_refl _) _ (by bsimp []) (by bsimp []) (by bsimp [h2]) (by bsimp []) ⟨?_, ?_⟩
  rotate_left
  · -- out of memory in the first call
    intro R' Mt' hr2 hout
    refine hk.oom R' Mt' (by rw [hr2]; congr 1; omega) fun a ha hf => ?_
    rw [hout a ha fun h => hf (.inl (by simp only [frameIn] at *; omega))]
    exact hM0f a fun h => hf (.inl h)
  intro R1 Mt1 H1 F1 z hk1 hp1 hr1
  have hb1 := NewNumPost.insert hb0 hp1
  have hr12 : R1 2 = BitVec.ofNat 64 (sp - 16) := by rw [hk1.get 2]; bsimp [h2]
  have hr11 : R1 1 = 0x8000495c#64 := by rw [hk1.get 1]; bsimp []
  have hra1 : ldv .ld Mt1 (sp - 8) = R 1 := by
    rw [ldv_congr .ld fun j hj => hp1.out _ ?_ ?_]; exact hra0
    · simp only [widthOfM] at hj
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
    · simp only [frameIn, widthOfM] at *; omega
  -- `_zero_ := a0`, then the second call
  bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [hr12, hr1] at 0x8000496c
  all_goals try (exact fun b hb' => hg b (by have := of_mem_accAddrs hb'; simp only [constBytes]; omega))
  generalize hM1 : writeLog Mt1 [(zeroAddr, 8, BitVec.ofNat 64 z.sb.pay)] = M1 at *
  have hM1f : MemOnly constBytes M1 Mt1 := by
    rw [← hM1]; exact (MemOnly.store Mt1 _ 8 _).mono fun a ha => by simp only [constBytes] at *; omega
  have hb1' : BcHeap S M1 H1 F1 (z :: L) := hb1.out_frame hM1f hgo
  have hz1 : ldv .ld M1 zeroAddr = BitVec.ofNat 64 z.sb.pay := by rw [← hM1, ldv_store_hit]
  have hra1' : ldv .ld M1 (sp - 8) = R 1 := by
    rw [ldv_congr .ld fun j hj => hM1f _ fun h => by
      simp only [widthOfM, constBytes] at *; omega]; exact hra1
  apply st_8000496c hlive
  refine bc_new_num_spec hlive hb1'.newHeap hsf' (by simp only [heapEnd]; omega) (by decide)
    (Nat.le_refl _) _ (by bsimp []) (by bsimp []) (by bsimp [hr12]) (by bsimp []) ⟨?_, ?_⟩
  rotate_left
  · intro R' Mt' hr2 hout
    refine hk.oom R' Mt' (by rw [hr2]; congr 1; omega) fun a ha hf => ?_
    rw [hout a ha fun h => hf (.inl (by simp only [frameIn] at *; omega)),
      hM1f a fun h => hf (.inr h), hp1.out a ha fun h => hf (.inl (by simp only [frameIn] at *; omega))]
    exact hM0f a fun h => hf (.inl h)
  intro R2 Mt2 H2 F2 o hk2 hp2 hr2a
  have hb2 := NewNumPost.insert hb1' hp2
  have hr22 : R2 2 = BitVec.ofNat 64 (sp - 16) := by rw [hk2.get 2]; bsimp [hr12]
  have ho := hp2.num
  rw [hp2.rep] at ho
  have hov : ldv .ld Mt2 (o.sb.pay + 32) = BitVec.ofNat 64 o.db.pay := by
    have := ho.value; simpa [zeroRep] using this
  have hz2 : ldv .ld Mt2 zeroAddr = BitVec.ofNat 64 z.sb.pay := by
    rw [ldv_congr .ld fun j hj => hp2.out _ (hgo _ (by simp only [widthOfM, constBytes] at *; omega))
      (by simp only [frameIn, widthOfM] at *; omega)]; exact hz1
  have hra2 : ldv .ld Mt2 (sp - 8) = R 1 := by
    rw [ldv_congr .ld fun j hj => hp2.out _ ?_ ?_]; exact hra1'
    · simp only [widthOfM] at hj
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
    · simp only [frameIn, widthOfM] at *; omega
  num_facts ho
  -- `_one_ := a0`, `_one_->n_value[0] = 1`, then the third call
  bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [hr22, hr2a, hov] at 0x80004988
  all_goals try (exact fun b hb' => hg b (by have := of_mem_accAddrs hb'; simp only [constBytes]; omega))
  all_goals try (exact acc_heap (fun a h1 h2 => hp2.inv.own a h1 h2) (by simp only [zeroRep] at *; omega)
    (by simp only [zeroRep] at *; omega))
  -- WIP (uncompiled): store `_one_`, the digit byte (`NumAt.setDigit`, then
  -- `BcHeap.update`), the third call, `_two_`, its digit, and the epilogue.
  all_goals exact (by assumption)

end Dc.Mach
