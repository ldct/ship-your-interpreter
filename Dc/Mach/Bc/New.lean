import Dc.Mach.Bc.Heap

/-!
# `bc_new_num` (`lib/number.c`)

```
80004250 addi sp,sp,-32 ; 80004254 sd s0,16(sp) ; 80004258 auipc s0,0x19
8000425c ld s0,-1192(s0) (_bc_Free_list) ; 80004260 sd ra,24(sp) ; 80004264 mv a5,a0
80004268 beqz s0,800042c8 ; 8000426c ld a4,16(s0) ; 80004270 auipc a3,0x19
80004274 sd a4,-1216(a3) (_bc_Free_list = n_next)
80004278 addw a2,a5,a1 ; 8000427c li a4,1 ; 80004280 mv a0,a2 ; 80004284 sw zero,0(s0)
80004288 sw a5,4(s0) ; 8000428c sw a1,8(s0) ; 80004290 sw a4,12(s0) ; 80004294 sd a2,0(sp)
80004298 jal malloc ; 8000429c sd a0,24(s0) ; 800042a0 ld a2,0(sp) ; 800042a4 beqz a0,800042f4
800042a8 sd a0,32(s0) ; 800042ac li a1,0 ; 800042b0 jal memset ; 800042b4 ld ra,24(sp)
800042b8 mv a0,s0 ; 800042bc ld s0,16(sp) ; 800042c0 addi sp,sp,32 ; 800042c4 ret
800042c8 sd a0,0(sp) ; 800042cc li a0,40 ; 800042d0 sd a1,8(sp) ; 800042d4 jal malloc
800042d8 ld a5,0(sp) ; 800042dc ld a1,8(sp) ; 800042e0 mv s0,a0 ; 800042e4 bnez a0,80004278
800042e8 jal out_of_memory … ; 800042f4 jal out_of_memory …
```

`bc_new_num_spec`: `NewNumPost` (`Heap.lean`), or `out_of_memory` when
`malloc` fails.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The registers `bc_new_num` may change. -/
abbrev newClob : List Nat := [10, 11, 12, 13, 14, 15]

/-- `bc_new_num`'s continuations from entry registers `R0`, memory `Mt0`, heap
`H0`, dead chain `F0`, stack pointer `sp`. -/
structure NewNumK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (H0 : Heap) (F0 : List Blk) (sp len scale : Nat) : Prop where
  ret : ∀ R' Mt' H' F' x, Keeps newClob R' R0 →
    NewNumPost S Mt0 Mt' H0 H' F0 F' (frameIn sp 32) len scale x →
    R' 10 = BitVec.ofNat 64 x.sb.pay → DW live S Q (R0 1) R' Mt'
  oom : ∀ R' Mt', R' 2 = BitVec.ofNat 64 (sp - 32) → OutFrame (frameIn sp 32) Mt' Mt0 →
    DW live S Q 0x80002bcc#64 R' Mt'

/-- The state of `bc_new_num` once it has its struct block `sb` (live in `H`,
off the dead chain `F`): the frame holds `s0` and `ra`, and the memory and
heap relate to the entry's. -/
structure NewBase (S : Nat → Prop) (Mt0 Mt : Mem) (H0 H : Heap) (F0 F : List Blk)
    (R0 : Nat → BitVec 64) (sp : Nat) (sb : Blk) (len scale : Nat) : Prop where
  inv : HeapInv S Mt H
  sLive : sb ∈ H.live
  sSz : 40 ≤ sb.sz
  dead : DeadChain Mt bcFreeAddr F
  deadOK : ∀ b ∈ F, b ∈ H.live ∧ b ≠ sb ∧ 40 ≤ b.sz
  ra : ldv .ld Mt (sp - 8) = R0 1
  s0 : ldv .ld Mt (sp - 16) = R0 8
  live : LiveFrame H0 sb Mt Mt0
  out : OutFrame (frameIn sp 32) Mt Mt0
  liveSub : ∀ c ∈ H0.live, c ∈ H.live
  src : ∀ H' db, H'.live = db :: H.live →
    NewSrc H0 H' F0 F ⟨zeroRep sb.pay db.pay len scale, sb, db⟩

/-- The state at the digit buffer's `malloc` call (`0x80004298`): the struct
holds the sign, lengths and reference count, the frame `len + scale`. -/
structure NewPrep (S : Nat → Prop) (Mt0 Mt : Mem) (H0 H : Heap) (F0 F : List Blk)
    (R0 : Nat → BitVec 64) (sp : Nat) (sb : Blk) (len scale : Nat) : Prop
    extends NewBase S Mt0 Mt H0 H F0 F R0 sp sb len scale where
  wSign : ldv .lw Mt sb.pay = 0#64
  wLen : ldv .lw Mt (sb.pay + 4) = BitVec.ofNat 64 len
  wScale : ldv .lw Mt (sb.pay + 8) = BitVec.ofNat 64 scale
  wRefs : ldv .lw Mt (sb.pay + 12) = BitVec.ofNat 64 1
  nw : ldv .ld Mt (sp - 32) = BitVec.ofNat 64 (len + scale)

/-- The digit buffer's `malloc`, its zeroing and the return, from `0x80004298`. -/
theorem new_num_digits {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {Mt0 Mt : Mem} {H0 H : Heap} {F0 F : List Blk}
    {R0 : Nat → BitVec 64} {sp : Nat} {sb : Blk} {len scale : Nat}
    (hp : NewPrep S Mt0 Mt H0 H F0 F R0 sp sb len scale) (hsf : StackFrame S sp 32)
    (hsp : heapEnd + 32 ≤ sp) (hls : len + scale < 2 ^ 31) (hl1 : 1 ≤ len)
    (hk : NewNumK live S Q R0 Mt0 H0 F0 sp len scale) (hal : (R0 1).toNat % 4 = 0)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 (len + scale))
    (h8 : R 8 = BitVec.ofNat 64 sb.pay) (h2 : R 2 = BitVec.ofNat 64 (sp - 32))
    (hkeep : Keeps [1, 2, 8, 10, 11, 12, 13, 14, 15] R R0) (h20 : R0 2 = BitVec.ofNat 64 sp) :
    DW live S Q 0x80004298#64 R Mt := by
  have hi := hp.inv
  have fb := hi.blk (List.mem_append_right _ hp.sLive)
  have hsl := fb.lo; have hsf2 := fb.fin; have hst := fb.top; have hsa := fb.al
  have hsz := hp.sSz
  simp only [heapStart, heapEnd, Blk.fin, Blk.pay] at hsl hsf2 hst hsp
  have hspl := hsf.hi; have hspa := hsf.al
  have hpl : 2147603936 ≤ sb.pay := by simp only [Blk.pay]; omega
  have hph : sb.pay + 40 ≤ 2273312768 := by simp only [Blk.pay]; omega
  have hpa : sb.pay % 16 = 0 := by simp only [Blk.pay]; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  apply st_80004298 hlive
  refine malloc_spec hlive hi (n := len + scale) (by omega) _ (by bsimp [h10]) (by bsimp []) ?_
  intro R1 Mt1 H1 hk1 hpost
  bsimp []
  have r8 : R1 8 = BitVec.ofNat 64 sb.pay := by rw [hk1.get 8]; bsimp [h8]
  have r2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  -- the frame survives `malloc`
  have hst1 : ∀ a, frameIn sp 32 a → imgM Mt1 a = imgM Mt a := fun a ha =>
    hpost.frame a (OutHeap.not_alloc hi ⟨by simp only [heapStart, heapEnd]; omega,
      by simp only [freeListAddr]; omega, by simp only [bcFreeAddr]; omega⟩)
  have hnw : ldv .ld Mt1 (sp - 32) = BitVec.ofNat 64 (len + scale) := by
    rw [ldv_congr .ld fun j hj => hst1 _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩]; exact hp.nw
  cases hres : hpost.res with
  | null e1 e2 e3 =>
    iterate 2 all_goals (try bc_run hlive (fun a h1 h2 => hi.own a h1 h2)
      [r8, r2, hnw, e1, ldv_ld_miss] at 0x80002bcc)
    all_goals try (exact frame_acc hsf (by omega) (by omega))
    refine hk.oom _ _ (by bsimp [r2]) fun a ha hf => ?_
    have hna : ¬ (heapStart ≤ a ∧ a < heapEnd) := ha.1
    simp only [heapStart, heapEnd] at hna
    rw [imgM_store_miss _ _ (by omega), hpost.frame a (OutHeap.not_alloc hi ha)]
    exact hp.out a ha hf
  | block db e1 e2 e3 e4 e5 =>
    have hi1 := hpost.inv
    have hdb : db ∈ H1.live := by rw [e3]; exact List.mem_cons_self
    have fd := hi1.blk (List.mem_append_right _ hdb)
    have hdl := fd.lo; have hdf := fd.fin; have hdt := fd.top; have hda := fd.al
    have hdpl : 2147603936 ≤ db.pay := by simp only [Blk.pay, heapStart] at hdl ⊢; omega
    have hdph : db.pay + (len + scale) ≤ 2273312768 := by
      simp only [Blk.pay, Blk.fin, heapEnd] at hdf hdt ⊢; omega
    have hsb1 : sb ∈ H1.live := by rw [e3]; exact List.mem_cons_of_mem _ hp.sLive
    bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [r8, r2, hnw, e1, ldv_ld_miss] at 0x80000890
    all_goals try (exact frame_acc hsf (by omega) (by omega))
    · intro hc; bv_nat at hc; omega
    intro _
    bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [r8, r2, hnw, e1, ldv_ld_miss] at 0x80000890
    refine memset_spec hlive (d := db.pay) (n := len + scale)
      ⟨fun i hi' => hi1.own _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega),
        by omega, by omega⟩ _ (by bsimp [e1])
      (by bsimp []) (by bsimp []) ?_
    intro R3 Mt3 hk3 hfill
    -- memory after the two stores and `memset`, byte by byte
    have hM3 : ∀ a, ¬ (db.pay ≤ a ∧ a < db.pay + (len + scale)) →
        ¬ (sb.pay + 24 ≤ a ∧ a < sb.pay + 40) → imgM Mt3 a = imgM Mt1 a := by
      intro a h1 h2
      rw [hfill.rest a (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
    have hstk : ∀ a, sp - 32 ≤ a → a + 8 ≤ sp → ldv .ld Mt3 a = ldv .ld Mt a := fun a h1 h2 =>
      ldv_congr .ld fun j hj => by
        simp only [widthOfM] at hj
        rw [hM3 _ (by omega) (by omega)]
        exact hst1 _ ⟨by omega, by omega⟩
    have hra : ldv .ld Mt3 (sp - 32 + 24) = R0 1 :=
      (hstk _ (by omega) (by omega)).trans (by rw [show sp - 32 + 24 = sp - 8 by omega]; exact hp.ra)
    have hs0 : ldv .ld Mt3 (sp - 32 + 16) = R0 8 :=
      (hstk _ (by omega) (by omega)).trans (by rw [show sp - 32 + 16 = sp - 16 by omega]; exact hp.s0)
    have hsp32 : sp - 32 + 32 = sp := by omega
    bsimp []
    bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [hk3.get 2, hk3.get 8, hk1.get 2, hk1.get 8, h8, h2,
      hra, hs0, hal, hsp32]
    all_goals try (exact frame_acc hsf (by omega) (by omega))
    -- where things are
    have hdnot : db ∉ H.live := hi1.head_not_mem e3
    have apart1 : ∀ c ∈ H1.live, ∀ d ∈ H1.live, c ≠ d → ∀ a, c.In a → ¬ d.In a :=
      fun c hc d hd hne a h1 h2 => live_apart hi1 hc hd hne h1 h2
    have hsd : sb ≠ db := fun e => hdnot (e ▸ hp.sLive)
    have hsfin : sb.fin = sb.pay + sb.sz := rfl
    have hdfin : db.fin = db.pay + db.sz := rfl
    have hsap : sb.fin ≤ db.h ∨ db.fin ≤ sb.h :=
      apart_of_mem hi1.apart (List.mem_append_right _ hsb1) (List.mem_append_right _ hdb) hsd
    have hsh : sb.pay = sb.h + 16 := rfl
    have hdh : db.pay = db.h + 16 := rfl
    have hsdisj : db.pay + (len + scale) ≤ sb.pay ∨ sb.pay + 40 ≤ db.pay := by omega
    -- bytes of the struct below `n_ptr` are as before `malloc`
    have hlow : ∀ a, sb.pay ≤ a → a < sb.pay + 24 → imgM Mt3 a = imgM Mt a := by
      intro a h1 h2
      have hsa : sb.In a := ⟨h1, by omega⟩
      rw [hM3 a (by omega) (by omega)]
      exact hpost.frame a (live_not_alloc hi hp.sLive hsa)
    have hrest : ∀ a, sb.pay ≤ a → a < sb.pay + 40 → imgM Mt3 a =
        imgM (writeLog (writeLog Mt1 [(sb.pay + 24, 8, BitVec.ofNat 64 db.pay)])
          [(sb.pay + 32, 8, BitVec.ofNat 64 db.pay)]) a := fun a h1 h2 =>
      hfill.rest a (by omega)
    have hshape : NumShape (zeroRep sb.pay db.pay len scale) :=
      { dsLen := by simp [zeroRep]
        dig := fun d hd => by simp only [zeroRep, List.mem_replicate] at hd; omega
        lenPos := hl1
        size := hls
        refsLt := show 1 < 2 ^ 31 by decide
        pAl := by simp only [zeroRep]; omega
        pLo := by simp only [zeroRep, heapStart]; omega
        pHi := by simp only [zeroRep, heapEnd]; omega
        ptrLe := Nat.le_refl _
        vLo := by simp only [zeroRep, heapStart]; omega
        vHi := by simp only [zeroRep, heapEnd]; omega
        sep := by simp only [zeroRep]; omega }
    have hnum : NumAt Mt3 (zeroRep sb.pay db.pay len scale) := by
      refine ⟨hshape, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi' => ?_⟩
      · show ldv .lw Mt3 sb.pay = signWord false
        rw [signWord_false, ← hp.wSign]
        exact ldv_congr .lw fun j hj => hlow _ (by omega) (by simp only [widthOfM] at hj; omega)
      · show ldv .lw Mt3 (sb.pay + 4) = BitVec.ofNat 64 len
        rw [← hp.wLen]
        exact ldv_congr .lw fun j hj => hlow _ (by omega) (by simp only [widthOfM] at hj; omega)
      · show ldv .lw Mt3 (sb.pay + 8) = BitVec.ofNat 64 scale
        rw [← hp.wScale]
        exact ldv_congr .lw fun j hj => hlow _ (by omega) (by simp only [widthOfM] at hj; omega)
      · show ldv .lw Mt3 (sb.pay + 12) = BitVec.ofNat 64 1
        rw [← hp.wRefs]
        exact ldv_congr .lw fun j hj => hlow _ (by omega) (by simp only [widthOfM] at hj; omega)
      · show ldv .ld Mt3 (sb.pay + 24) = BitVec.ofNat 64 db.pay
        rw [ldv_congr .ld fun j hj => hrest _ (by omega) (by simp only [widthOfM] at hj; omega),
          ldv_ld_miss _ _ (by omega), ldv_store_hit]
      · show ldv .ld Mt3 (sb.pay + 32) = BitVec.ofNat 64 db.pay
        rw [ldv_congr .ld fun j hj => hrest _ (by omega) (by simp only [widthOfM] at hj; omega),
          ldv_store_hit]
      · show imgM Mt3 (db.pay + i) = _
        rw [hfill.fill i hi']
        simp [zeroRep, List.getElem?_replicate, show i < len + scale from hi']
    refine hk.ret _ Mt3 H1 F ⟨zeroRep sb.pay db.pay len scale, sb, db⟩ ?_ ?_ (by bsimp [])
    · intro z hz
      simp only [newClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rcases (show z = 1 ∨ z = 2 ∨ z = 8 ∨ (z ≠ 1 ∧ z ≠ 2 ∧ z ≠ 8) by omega) with
        rfl | rfl | rfl | ⟨z1, z2, z8⟩
      · bsimp []
      · bsimp [h20]
      · bsimp []
      · simp only [upd_apply, z1, z2, z8, hz.1, ite_false]
        rw [hk3 z (by simp; omega)]
        simp only [upd_apply, z1, hz.1, hz.2.1, hz.2.2.1, ite_false]
        rw [hk1 z (by simp [mallocClob]; omega)]
        simp only [upd_apply, z1, ite_false]
        exact hkeep z (by simp; omega)
    · -- a live block of `H1` other than `sb`, `db` is unchanged since `malloc`
      have hothers : ∀ c ∈ H.live, c ≠ sb → ∀ a, c.In a → imgM Mt3 a = imgM Mt a := by
        intro c hc hcs a ha
        have hc1 : c ∈ H1.live := by rw [e3]; exact List.mem_cons_of_mem _ hc
        have hcd : c ≠ db := fun e => hdnot (e ▸ hc)
        rw [hM3 a (fun h => apart1 c hc1 db hdb hcd a ha ⟨h.1, by omega⟩)
          (fun h => apart1 c hc1 sb hsb1 hcs a ha ⟨by omega, by omega⟩)]
        exact hpost.frame a (live_not_alloc hi hc ha)
      have hout : ∀ a, OutHeap a → imgM Mt3 a = imgM Mt a := by
        intro a ha
        have hna : ¬ (heapStart ≤ a ∧ a < heapEnd) := ha.1
        simp only [heapStart, heapEnd] at hna
        rw [hM3 a (by omega) (by omega)]
        exact hpost.frame a (OutHeap.not_alloc hi ha)
      refine ⟨hi1.transport fun a ha => ?_, ?_, hnum, rfl, hp.sSz, e2, hp.src H1 db e3,
        fun c hc hcs a ha => (hothers c (hp.liveSub c hc) hcs a ha).trans (hp.live c hc hcs a ha),
        fun a ha hf => (hout a ha).trans (hp.out a ha hf)⟩
      · refine hM3 a (fun h => live_not_alloc hi1 hdb ⟨h.1, by omega⟩ ha)
          (fun h => live_not_alloc hi1 hsb1 ⟨by omega, by omega⟩ ha)
      · refine hp.dead.frame ?_ fun b hb j hj => ?_
        · refine ldv_congr .ld fun j hj => ?_
          simp only [widthOfM, bcFreeAddr] at hj ⊢
          rw [hM3 _ (by omega) (by omega)]
          refine hpost.frame _ fun ha => ?_
          rcases AllocByte.glob_or_heap hi ha with h | h <;>
            simp only [freeListAddr, heapStart, heapEnd] at h <;> omega
        · obtain ⟨hbH, hbs, hbz⟩ := hp.deadOK b hb
          exact hothers b hbH hbs _ ⟨by omega, by simp only [Blk.fin, Blk.pay]; omega⟩

/-- The struct's fields, from `0x80004278` (the struct block `sb` in `s0`). -/
theorem new_num_fields {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {Mt0 Mt : Mem} {H0 H : Heap} {F0 F : List Blk}
    {R0 : Nat → BitVec 64} {sp : Nat} {sb : Blk} {len scale : Nat}
    (hb : NewBase S Mt0 Mt H0 H F0 F R0 sp sb len scale) (hsf : StackFrame S sp 32)
    (hsp : heapEnd + 32 ≤ sp) (hls : len + scale < 2 ^ 31) (hl1 : 1 ≤ len)
    (hk : NewNumK live S Q R0 Mt0 H0 F0 sp len scale) (hal : (R0 1).toNat % 4 = 0)
    (R : Nat → BitVec 64) (h15 : R 15 = BitVec.ofNat 64 len) (h11 : R 11 = BitVec.ofNat 64 scale)
    (h8 : R 8 = BitVec.ofNat 64 sb.pay) (h2 : R 2 = BitVec.ofNat 64 (sp - 32))
    (hkeep : Keeps [1, 2, 8, 10, 11, 12, 13, 14, 15] R R0) (h20 : R0 2 = BitVec.ofNat 64 sp) :
    DW live S Q 0x80004278#64 R Mt := by
  have hi := hb.inv
  have fb := hi.blk (List.mem_append_right _ hb.sLive)
  have hsl := fb.lo; have hsf2 := fb.fin; have hst := fb.top; have hsa := fb.al
  have hsz := hb.sSz
  simp only [heapStart, heapEnd, Blk.fin, Blk.pay] at hsl hsf2 hst hsp
  have hspl := hsf.hi; have hspa := hsf.al
  have hpl : 2147603936 ≤ sb.pay := by simp only [Blk.pay]; omega
  have hph : sb.pay + 40 ≤ 2273312768 := by simp only [Blk.pay]; omega
  have hpa : sb.pay % 16 = 0 := by simp only [Blk.pay]; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [h15, h11, h8, h2, addw_ofNat] at 0x80004298
  all_goals try (exact frame_acc hsf (by omega) (by omega))
  generalize hM2 : writeLog (writeLog (writeLog (writeLog (writeLog Mt [(sb.pay, 4, 0#64)])
    [(sb.pay + 4, 4, BitVec.ofNat 64 len)]) [(sb.pay + 8, 4, BitVec.ofNat 64 scale)])
    [(sb.pay + 12, 4, 1#64)]) [(sp - 32, 8, BitVec.ofNat 64 (len + scale))] = Mt2
  have hsfin : sb.fin = sb.pay + sb.sz := rfl
  have hout2 : ∀ a, ¬ (sb.pay ≤ a ∧ a < sb.pay + 16) → ¬ (sp - 32 ≤ a ∧ a < sp - 24) →
      imgM Mt2 a = imgM Mt a := by
    intro a h1 h2
    rw [← hM2]
    repeat rw [imgM_store_miss _ _ (by omega)]
  have hstk : ∀ a, sp - 24 ≤ a → a + 8 ≤ sp → ldv .ld Mt2 a = ldv .ld Mt a := fun a h1 h2 =>
    ldv_congr .ld fun j hj => hout2 _ (by omega) (by simp only [widthOfM] at hj; omega)
  have hbase : NewBase S Mt0 Mt2 H0 H F0 F R0 sp sb len scale :=
    { inv := hi.transport fun a ha => hout2 a
        (fun h => live_not_alloc hi hb.sLive ⟨h.1, by omega⟩ ha)
        (fun h => OutHeap.not_alloc hi ⟨by simp only [heapStart, heapEnd]; omega,
          by simp only [freeListAddr]; omega, by simp only [bcFreeAddr]; omega⟩ ha)
      sLive := hb.sLive
      sSz := hb.sSz
      dead := hb.dead.frame
        (ldv_congr .ld fun j hj => by
          simp only [widthOfM] at hj
          exact hout2 _ (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega))
        fun b hb' j hj => by
          obtain ⟨hbH, hbs, hbz⟩ := hb.deadOK b hb'
          have fbb := hi.blk (List.mem_append_right _ hbH)
          have h1 : 2147603920 ≤ b.h := fbb.lo
          have h2 : b.fin ≤ H.brk := fbb.fin
          have h3 : H.brk ≤ 2273312768 := fbb.top
          have hbp : b.pay = b.h + 16 := rfl
          have hbf : b.fin = b.h + 16 + b.sz := rfl
          refine hout2 _ (fun h => live_apart hi hbH hb.sLive hbs ⟨by omega, by omega⟩ ⟨h.1, by omega⟩)
            (by omega)
      deadOK := hb.deadOK
      ra := (hstk _ (by omega) (by omega)).trans hb.ra
      s0 := (hstk _ (by omega) (by omega)).trans hb.s0
      live := fun c hc hcs a ha => by
        rw [hout2 a (fun h => live_apart hi (hb.liveSub c hc) hb.sLive hcs ha ⟨h.1, by omega⟩)
          (fun h => by
            have fcc := hi.blk (List.mem_append_right _ (hb.liveSub c hc))
            have := fcc.top; have := fcc.fin
            simp only [heapEnd, Blk.fin, Blk.pay, Blk.In] at *; omega)]
        exact hb.live c hc hcs a ha
      out := fun a ha hf => by
        have hna : ¬ (heapStart ≤ a ∧ a < heapEnd) := ha.1
        simp only [heapStart, heapEnd] at hna
        rw [hout2 a (by omega) (by simp only [frameIn] at hf; omega)]
        exact hb.out a ha hf
      liveSub := hb.liveSub
      src := hb.src }
  refine new_num_digits hlive (hp := { hbase with
      wSign := ?_, wLen := ?_, wScale := ?_, wRefs := ?_, nw := ?_ }) hsf hsp hls hl1 hk hal _
    (by bsimp []) (by bsimp [h8]) (by bsimp [h2]) (by keeps_tac hkeep) h20
  all_goals rw [← hM2]
  all_goals simp (disch := omega) only [ldv_lw_miss, ldv_ld_miss, ldv_store_hit]
  · exact ldv_lw_hitN _ rfl (by simp) (by decide)
  · exact ldv_lw_hitN _ rfl (toNat_ofNat_mod32 (by omega)) (by omega)
  · exact ldv_lw_hitN _ rfl (toNat_ofNat_mod32 (by omega)) (by omega)
  · exact ldv_lw_hitN _ rfl (by simp) (by decide)

/-- The frame after `bc_new_num`'s prologue: `s0` and `ra` saved, nothing else
changed. -/
structure NewFrame (Mt0 Mt : Mem) (R0 : Nat → BitVec 64) (sp : Nat) : Prop where
  ra : ldv .ld Mt (sp - 8) = R0 1
  s0 : ldv .ld Mt (sp - 16) = R0 8
  rest : ∀ a, ¬ frameIn sp 32 a → imgM Mt a = imgM Mt0 a

/-- The entry's heap: the allocator invariant, the dead chain `F` of distinct
live blocks of at least 40 bytes, and ownership of `_bc_Free_list`. -/
structure NewHeap (S : Nat → Prop) (Mt : Mem) (H : Heap) (F : List Blk) : Prop where
  inv : HeapInv S Mt H
  dead : DeadChain Mt bcFreeAddr F
  deadOK : ∀ b ∈ F, b ∈ H.live ∧ 40 ≤ b.sz
  nodup : F.Nodup
  glob : ∀ a, bcFreeAddr ≤ a → a < bcFreeAddr + 8 → S a

/-- Reusing the head `sb` of `_bc_Free_list`, from `0x8000426c`. -/
theorem new_num_reuse {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {Mt0 Mt : Mem} {H : Heap} {sb : Blk} {F' : List Blk}
    (hh : NewHeap S Mt0 H (sb :: F')) {R0 : Nat → BitVec 64} {sp len scale : Nat}
    (hfr : NewFrame Mt0 Mt R0 sp) (hsf : StackFrame S sp 32) (hsp : heapEnd + 32 ≤ sp)
    (hls : len + scale < 2 ^ 31) (hl1 : 1 ≤ len) (hal : (R0 1).toNat % 4 = 0)
    (h20 : R0 2 = BitVec.ofNat 64 sp) (hk : NewNumK live S Q R0 Mt0 H (sb :: F') sp len scale)
    (R : Nat → BitVec 64) (h8 : R 8 = BitVec.ofNat 64 sb.pay) (h15 : R 15 = BitVec.ofNat 64 len)
    (h11 : R 11 = BitVec.ofNat 64 scale) (h2 : R 2 = BitVec.ofNat 64 (sp - 32))
    (hkeep : Keeps [1, 2, 8, 10, 11, 12, 13, 14, 15] R R0) :
    DW live S Q 0x8000426c#64 R Mt := by
  have hi := hh.inv
  have hspl := hsf.hi; have hspa := hsf.al
  simp only [heapEnd] at hsp
  have htx : tohostAddr = 0x8001ad00 := rfl
  have ⟨hsbL, hsbz⟩ := hh.deadOK sb List.mem_cons_self
  have fbb := hi.blk (List.mem_append_right _ hsbL)
  have hsl : 2147603920 ≤ sb.h := fbb.lo
  have hsf2 : sb.fin ≤ H.brk := fbb.fin
  have hst : H.brk ≤ 2273312768 := fbb.top
  have hsa : sb.h % 16 = 0 := fbb.al
  have hbp : sb.pay = sb.h + 16 := rfl
  have hbf : sb.fin = sb.h + 16 + sb.sz := rfl
  have hpl : 2147603936 ≤ sb.pay := by omega
  have hph : sb.pay + 40 ≤ 2273312768 := by omega
  have hpa : sb.pay % 16 = 0 := by omega
  have hdt : DeadChain Mt0 (sb.pay + 16) F' := by cases hh.dead with | cons _ h => exact h
  have hnx : ldv .ld Mt (sb.pay + 16) = BitVec.ofNat 64 (deadHead F') := by
    rw [ldv_congr .ld fun j hj => hfr.rest _ (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact hdt.head
  have hgl' : ∀ b ∈ accAddrs 2147601840 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hh.glob b (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega)
  bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [h8, h2, hnx] at 0x80004278
  all_goals try exact hgl'
  generalize hM1 : writeLog Mt [(2147601840, 8, BitVec.ofNat 64 (deadHead F'))] = Mt1
  have hM1a : ∀ a, ¬ (2147601840 ≤ a ∧ a < 2147601848) → imgM Mt1 a = imgM Mt a := by
    intro a h1; rw [← hM1]; exact imgM_store_miss _ _ (by omega)
  have hM1b : ∀ a, ¬ (2147601840 ≤ a ∧ a < 2147601848) → ¬ frameIn sp 32 a →
      imgM Mt1 a = imgM Mt0 a := fun a h1 h2 => (hM1a a h1).trans (hfr.rest a h2)
  have hstk : ∀ a, sp - 32 ≤ a → a + 8 ≤ sp → ldv .ld Mt1 a = ldv .ld Mt a := fun a h1 h2 =>
    ldv_congr .ld fun j hj => hM1a _ (by simp only [widthOfM] at hj; omega)
  have hnd := List.nodup_cons.1 hh.nodup
  refine new_num_fields hlive (F := F') (H := H) (sb := sb) ?_ hsf (by simp only [heapEnd]; omega) hls hl1
    hk hal _ (by bsimp [h15]) (by bsimp [h11]) (by bsimp [h8]) (by bsimp [h2]) (by keeps_tac hkeep) h20
  exact
    { inv := hi.transport fun a ha => hM1b a
        (fun h => by rcases AllocByte.glob_or_heap hi ha with h' | h' <;>
          simp only [freeListAddr, heapStart, heapEnd] at h' <;> omega)
        (fun h => by rcases AllocByte.glob_or_heap hi ha with h' | h' <;>
          simp only [freeListAddr, heapStart, heapEnd, frameIn] at h' h <;> omega)
      sLive := hsbL
      sSz := hsbz
      dead := hdt.move (by rw [← hM1, ldv_store_hit]; exact hdt.head.symm) fun b hb j hj => by
        have ⟨hbL, _⟩ := hh.deadOK b (List.mem_cons_of_mem _ hb)
        have fb2 := hi.blk (List.mem_append_right _ hbL)
        have h1 : 2147603920 ≤ b.h := fb2.lo
        have h2' : b.fin ≤ H.brk := fb2.fin
        have hbp : b.pay = b.h + 16 := rfl
        have hbf : b.fin = b.h + 16 + b.sz := rfl
        exact hM1b _ (by omega) (by simp only [frameIn]; omega)
      deadOK := fun b hb => ⟨(hh.deadOK b (List.mem_cons_of_mem _ hb)).1,
        fun e => hnd.1 (e ▸ hb), (hh.deadOK b (List.mem_cons_of_mem _ hb)).2⟩
      ra := (hstk _ (by omega) (by omega)).trans hfr.ra
      s0 := (hstk _ (by omega) (by omega)).trans hfr.s0
      live := fun c hc hcs a ha => by
        have fc := hi.blk (List.mem_append_right _ hc)
        have h1 : 2147603920 ≤ c.h := fc.lo
        have h2' : c.fin ≤ H.brk := fc.fin
        have hcp : c.pay = c.h + 16 := rfl
        simp only [Blk.In] at ha
        exact hM1b a (by omega) (by simp only [frameIn]; omega)
      out := fun a ha hf => hM1b a (fun h => ha.2.2 (by simp only [bcFreeAddr]; omega)) hf
      liveSub := fun c hc => hc
      src := fun H' db e => .reuse rfl e }

/-- A fresh struct from `malloc(40)` (`_bc_Free_list` empty), from `0x800042c8`. -/
theorem new_num_fresh {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {Mt0 Mt : Mem} {H : Heap}
    (hh : NewHeap S Mt0 H []) {R0 : Nat → BitVec 64} {sp len scale : Nat}
    (hfr : NewFrame Mt0 Mt R0 sp) (hsf : StackFrame S sp 32) (hsp : heapEnd + 32 ≤ sp)
    (hls : len + scale < 2 ^ 31) (hl1 : 1 ≤ len) (hal : (R0 1).toNat % 4 = 0)
    (h20 : R0 2 = BitVec.ofNat 64 sp) (hk : NewNumK live S Q R0 Mt0 H [] sp len scale)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 len) (h11 : R 11 = BitVec.ofNat 64 scale)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (hkeep : Keeps [1, 2, 8, 10, 11, 12, 13, 14, 15] R R0) :
    DW live S Q 0x800042c8#64 R Mt := by
  have hi := hh.inv
  have hspl := hsf.hi; have hspa := hsf.al
  simp only [heapEnd] at hsp
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [h2, h10, h11] at 0x8000096c
  all_goals try (exact frame_acc hsf (by omega) (by omega))
  generalize hMf : writeLog (writeLog Mt [(sp - 32, 8, BitVec.ofNat 64 len)])
    [(sp - 32 + 8, 8, BitVec.ofNat 64 scale)] = Mf
  have hMfa : ∀ a, ¬ frameIn sp 32 a → imgM Mf a = imgM Mt0 a := by
    intro a h1
    rw [← hMf, imgM_store_miss _ _ (by simp only [frameIn] at h1; omega),
      imgM_store_miss _ _ (by simp only [frameIn] at h1; omega)]
    exact hfr.rest a h1
  have hnotA : ∀ a, frameIn sp 32 a → ¬ AllocByte H a := fun a hf ha => by
    rcases AllocByte.glob_or_heap hi ha with h' | h' <;>
      simp only [freeListAddr, heapStart, heapEnd, frameIn] at h' hf <;> omega
  have hiF : HeapInv S Mf H := hi.transport fun a ha => hMfa a fun h => hnotA a h ha
  refine malloc_spec hlive hiF (n := 40) (by decide) _ (by bsimp []) (by bsimp []) ?_
  intro R1 Mt1 H1 hk1 hpost
  bsimp []
  have hstk : ∀ a, sp - 32 ≤ a → a + 8 ≤ sp → ldv .ld Mt1 a = ldv .ld Mf a := fun a h1 h2 =>
    ldv_congr .ld fun j hj => hpost.frame _ (hnotA _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩)
  have w0 : ldv .ld Mt1 (sp - 32) = BitVec.ofNat 64 len := by
    rw [hstk _ (by omega) (by omega), ← hMf, ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have w8 : ldv .ld Mt1 (sp - 32 + 8) = BitVec.ofNat 64 scale := by
    rw [hstk _ (by omega) (by omega), ← hMf, ldv_store_hit]
  have r2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  cases hres : hpost.res with
  | null e1 e2 e3 =>
    iterate 2 all_goals (try bc_run hlive (fun a h1 h2 => hi.own a h1 h2)
      [r2, w0, w8, e1] at 0x80002bcc)
    all_goals try (exact frame_acc hsf (by omega) (by omega))
    refine hk.oom _ _ (by bsimp [r2]) fun a ha hf => ?_
    rw [hpost.frame a (OutHeap.not_alloc hiF ha), hMfa a hf]
  | block sb e1 e2 e3 e4 e5 =>
    have hi1 := hpost.inv
    have hsb1 : sb ∈ H1.live := by rw [e3]; exact List.mem_cons_self
    have fbb := hi1.blk (List.mem_append_right _ hsb1)
    have hsl : 2147603920 ≤ sb.h := fbb.lo
    have hsf2 : sb.fin ≤ H1.brk := fbb.fin
    have hst : H1.brk ≤ 2273312768 := fbb.top
    have hsz : 40 ≤ sb.sz := e2
    have hbp : sb.pay = sb.h + 16 := rfl
    have hbf : sb.fin = sb.h + 16 + sb.sz := rfl
    have hpl : 2147603936 ≤ sb.pay := by omega
    have hph : sb.pay + 40 ≤ 2273312768 := by omega
    bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [r2, w0, w8, e1] at 0x80004278
    all_goals try (exact frame_acc hsf (by omega) (by omega))
    rotate_left
    · intro hc; bv_nat at hc; simp only [Nat.mod_eq_of_lt (show sb.pay < 2 ^ 64 by omega)] at hc
      omega
    intro _
    have hlive1 : ∀ c ∈ H.live, ∀ a, c.In a → imgM Mt1 a = imgM Mt0 a := fun c hc a ha => by
      have fc := hi.blk (List.mem_append_right _ hc)
      have h1 : 2147603920 ≤ c.h := fc.lo
      have h2' : c.fin ≤ H.brk := fc.fin
      have h3 : H.brk ≤ 2273312768 := fc.top
      have hcp : c.pay = c.h + 16 := rfl
      simp only [Blk.In] at ha
      rw [hpost.frame a (live_not_alloc hiF hc ⟨ha.1, ha.2⟩)]
      exact hMfa a (by simp only [frameIn]; omega)
    have hkk : Keeps [1, 2, 8, 10, 11, 12, 13, 14, 15] R1 R0 :=
      ((Keeps.mono hk1 (by decide)).trans (by keeps_tac Keeps.refl _ _)).trans hkeep
    refine new_num_fields hlive (F := []) (H := H1) (sb := sb) ?_ hsf (by simp only [heapEnd]; omega)
      hls hl1 hk hal _ ?_ ?_ ?_ (by bsimp [r2]) (by keeps_tac hkk) h20
    rotate_left
    · bsimp [w0]
    · bsimp [w8]
    · bsimp [e1]
    have h0 : ldv .ld Mt0 bcFreeAddr = 0#64 := hh.dead.head
    exact
      { inv := hi1
        sLive := hsb1
        sSz := hsz
        dead := .nil (by
          rw [← h0]
          refine ldv_congr .ld fun j hj => ?_
          simp only [widthOfM] at hj
          rw [hpost.frame _ fun ha => by
            rcases AllocByte.glob_or_heap hiF ha with h' | h' <;>
              simp only [freeListAddr, heapStart, heapEnd, bcFreeAddr] at h' <;> omega]
          exact hMfa _ (by simp only [frameIn, bcFreeAddr]; omega))
        deadOK := fun b hb => by cases hb
        ra := by
          rw [hstk _ (by omega) (by omega), ← hMf, ldv_ld_miss _ _ (by omega),
            ldv_ld_miss _ _ (by omega)]
          exact hfr.ra
        s0 := by
          rw [hstk _ (by omega) (by omega), ← hMf, ldv_ld_miss _ _ (by omega),
            ldv_ld_miss _ _ (by omega)]
          exact hfr.s0
        live := fun c hc _ a ha => hlive1 c hc a ha
        out := fun a ha hf => by
          rw [hpost.frame a (OutHeap.not_alloc hiF ha)]; exact hMfa a hf
        liveSub := fun c hc => by rw [e3]; exact List.mem_cons_of_mem _ hc
        src := fun H' db e => .fresh rfl rfl (by rw [e, e3]) }

/-- **`bc_new_num(len, scale)`** at `0x80004250`, `1 ≤ len`,
`len + scale < 2^31`, with a 32-byte stack frame above the heap: returns in
`a0` a zero number (`NewNumPost`: struct from the head of `_bc_Free_list` or
fresh, digit buffer fresh, `n_refs = 1`), or reaches `out_of_memory`;
clobbers `a0`–`a5`. -/
theorem bc_new_num_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} {F : List Blk} (hh : NewHeap S Mt H F)
    {sp len scale : Nat} (hsf : StackFrame S sp 32) (hsp : heapEnd + 32 ≤ sp)
    (hls : len + scale < 2 ^ 31) (hl1 : 1 ≤ len)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 len) (h11 : R 11 = BitVec.ofNat 64 scale)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : NewNumK live S Q R Mt H F sp len scale) :
    DW live S Q 0x80004250#64 R Mt := by
  have hi := hh.inv
  have hspl := hsf.hi; have hspa := hsf.al
  have hsp' := hsp
  simp only [heapEnd] at hsp'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hfw : ldv .ld Mt 2147601840 = BitVec.ofNat 64 (deadHead F) := hh.dead.head
  have hfr : NewFrame Mt (writeLog (writeLog Mt [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)])
      R sp :=
    { ra := by rw [show sp - 8 = sp - 32 + 24 by omega, ldv_store_hit]
      s0 := by rw [show sp - 16 = sp - 32 + 16 by omega, ldv_ld_miss _ _ (by omega), ldv_store_hit]
      rest := fun a ha => by
        simp only [frameIn] at ha
        rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)] }
  bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [h2] at 0x8000425c
  all_goals try (exact frame_acc hsf (by omega) (by omega))
  apply st_8000425c hlive
  · bsimp []; bc_addr
  · bsimp []; intro b hb; have := of_mem_accAddrs hb
    exact hh.glob b (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega)
  bsimp [hfw]
  bc_run hlive (fun a h1 h2 => hi.own a h1 h2) [h2, h10, hfw] at 0x8000426c 0x800042c8
  all_goals try (exact frame_acc hsf (by omega) (by omega))
  · -- `_bc_Free_list` empty
    intro h0
    rcases hFe : F with _ | ⟨b, F'⟩
    · rw [hFe] at hh hk
      exact new_num_fresh hlive hh hfr hsf hsp hls hl1 hal h2 hk _ (by bsimp [h10]) (by bsimp [h11])
        (by bsimp []) (by keeps_tac Keeps.refl _ _)
    · exfalso
      rw [hFe] at h0
      have fbb := hi.blk (List.mem_append_right _ (hh.deadOK b (by rw [hFe]; exact List.mem_cons_self)).1)
      have h1 : 2147603920 ≤ b.h := fbb.lo
      have h2' : b.fin ≤ H.brk := fbb.fin
      have h3 : H.brk ≤ 2273312768 := fbb.top
      have hbf : b.fin = b.h + 16 + b.sz := rfl
      simp only [deadHead, Blk.pay] at h0
      bv_nat at h0
      simp only [Nat.mod_eq_of_lt (show b.h + 16 < 2 ^ 64 by omega)] at h0
      omega
  · -- reuse the head
    intro h0
    rcases hFe : F with _ | ⟨sb, F'⟩
    · rw [hFe] at h0; exact absurd rfl h0
    rw [hFe] at hh hk
    exact new_num_reuse hlive hh hfr hsf hsp hls hl1 hal h2 hk _ (by bsimp [hFe, deadHead])
      (by bsimp [h10]) (by bsimp [h11]) (by bsimp []) (by keeps_tac Keeps.refl _ _)

end Dc.Mach
