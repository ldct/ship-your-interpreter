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

/-- The state at the digit buffer's `malloc` call (`0x80004298`): the struct
block `sb` (live in `H`, off the dead chain `F`) holds the sign, lengths and
reference count; the frame holds `len + scale`, `s0` and `ra`. -/
structure NewPrep (S : Nat → Prop) (Mt0 Mt : Mem) (H0 H : Heap) (F0 F : List Blk)
    (R0 : Nat → BitVec 64) (sp : Nat) (sb : Blk) (len scale : Nat) : Prop where
  inv : HeapInv S Mt H
  sLive : sb ∈ H.live
  sSz : 40 ≤ sb.sz
  dead : DeadChain Mt bcFreeAddr F
  deadOK : ∀ b ∈ F, b ∈ H.live ∧ b ≠ sb ∧ 40 ≤ b.sz
  wSign : ldv .lw Mt sb.pay = 0#64
  wLen : ldv .lw Mt (sb.pay + 4) = BitVec.ofNat 64 len
  wScale : ldv .lw Mt (sb.pay + 8) = BitVec.ofNat 64 scale
  wRefs : ldv .lw Mt (sb.pay + 12) = BitVec.ofNat 64 1
  nw : ldv .ld Mt (sp - 32) = BitVec.ofNat 64 (len + scale)
  ra : ldv .ld Mt (sp - 8) = R0 1
  s0 : ldv .ld Mt (sp - 16) = R0 8
  live : LiveFrame H0 sb Mt Mt0
  out : OutFrame (frameIn sp 32) Mt Mt0
  liveSub : ∀ c ∈ H0.live, c ∈ H.live
  src : ∀ H' db, H'.live = db :: H.live →
    NewSrc H0 H' F0 F ⟨zeroRep sb.pay db.pay len scale, sb, db⟩

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

end Dc.Mach
