import Dc.Mach.DcDumpBase

/-!
# `dc_dump_num` (M9)

See `DcDumpBase.lean` for the C source.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The window of `dc_dump_num`'s callees below its 80-byte frame. -/
abbrev dnW : Nat := 176 + rmStack (2 ^ 30)

/-- `dc_dump_num`'s stack. -/
abbrev dnN : Nat := 80 + dnW

/-- **Inside `dc_dump_num`'s frame**: `sp` lowered by 80, `s1`, `s0`, `ra`
saved at `56`, `64`, `72`, off the heap and the globals only the stack
changed. -/
structure DnAt (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp : Nat) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 80)
  w56 : ldv .ld M (sp - 80 + 56) = R0 9
  w64 : ldv .ld M (sp - 80 + 64) = R0 8
  w72 : ldv .ld M (sp - 80 + 72) = R0 1
  keep : Keeps (2 :: 8 :: 9 :: cClob) R R0
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp dnN a → imgM M a = imgM M0 a

/-- `bc_init_num` with `_zero_`'s address kept by the new constants. -/
theorem dn_init {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) {q : Nat} (hq : PtrSlot S q)
    (hqh : heapEnd ≤ q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' L' C', Keeps [14, 15] R' R → DcAt S M' H F L' C' G (.num C.z.rep.p :: hs) st →
      C'.z.rep.p = C.z.rep.p → HsKeep ⟨L, G.strs⟩ ⟨L', G.strs⟩ hs →
      ldv .ld M' q = BitVec.ofNat 64 C.z.rep.p →
      (∀ a, OutHeap a → ¬ slotBytes q a → imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x800049bc#64 R M :=
  dc_init_num_spec hlive h hhs hq hqh R h10 hal fun R' M' L' C' hk' hd hkeep hw hfr =>
    hk R' M' L' C' hk' hd (h.zeroP_eq hd (ldv_congr .ld fun j hj =>
      hfr _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, widthOfM,
          dc_addrs] at hj ⊢; omega)
        (fun hs => by simp only [slotBytes, widthOfM, dc_addrs, heapEnd] at hs hj hqh; omega)))
      hkeep hw hfr

/-- **The prologue and the three `bc_init_num`** (`0x80002aa4` to
`0x80002ad4`): `value`, `obase`, `digit` hold `_zero_`. -/
theorem dn_pro {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {xp : Nat}
    (h : DcAt S M H F L C G (.num xp :: hs) st) (hhs : hs.length ≤ 2 ^ 20) {sp : Nat}
    (hsf : StackFrame S sp dnN) (hab : heapEnd + dnN ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 xp)
    (h11 : R 11 = 0#64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R1 M1 L1 C1, DnAt S M M1 R R1 sp → R1 8 = 0#64 →
      DcAt S M1 H F L1 C1 G (.num C.z.rep.p :: .num C.z.rep.p :: .num C.z.rep.p :: .num xp :: hs) st →
      C1.z.rep.p = C.z.rep.p → HsKeep ⟨L, G.strs⟩ ⟨L1, G.strs⟩ (.num xp :: hs) →
      ldv .ld M1 (sp - 80 + 8) = BitVec.ofNat 64 xp →
      ldv .ld M1 (sp - 80 + 24) = BitVec.ofNat 64 C.z.rep.p →
      ldv .ld M1 (sp - 80 + 32) = BitVec.ofNat 64 C.z.rep.p →
      ldv .ld M1 (sp - 80 + 40) = BitVec.ofNat 64 C.z.rep.p →
      DWO live S Q t 0x80002ad4#64 R1 M1) :
    DWO live S Q t 0x80002aa4#64 R M := by
  have hNW : dnN = 80 + (176 + rmStack (2 ^ 30)) := rfl
  rw [hNW] at hsf hab
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  bc_run hlive hS [h2, h10, h11, word_sub80 (x := sp) (by omega)] at 0x800049bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hab2 : heapEnd ≤ sp - 80 := by simp only [heapEnd]; omega
  have hP : ∀ a, frameIn sp 80 a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
     (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  generalize hM1 : writeLog (writeLog (writeLog (writeLog M [(sp - 80 + 8, 8, BitVec.ofNat 64 xp)])
    [(sp - 80 + 72, 8, R 1)]) [(sp - 80 + 64, 8, R 8)]) [(sp - 80 + 56, 8, R 9)] = M1
  have hm1 : MemOnly (frameIn sp 80) M1 M := fun a ha => by
    rw [← hM1]; simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have m8 : ldv .ld M1 (sp - 80 + 8) = BitVec.ofNat 64 xp := by
    rw [← hM1, ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_store_hit]
  have m72 : ldv .ld M1 (sp - 80 + 72) = R 1 := by
    rw [← hM1, ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have m64 : ldv .ld M1 (sp - 80 + 64) = R 8 := by
    rw [← hM1, ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have m56 : ldv .ld M1 (sp - 80 + 56) = R 9 := by rw [← hM1, ldv_store_hit]
  have h1 := h.outWrite hm1 hP
  have hlen : (GV.num xp :: hs).length ≤ 2 ^ 30 := by simp only [List.length_cons]; omega
  have slot : ∀ o, o + 8 ≤ 80 → o % 8 = 0 → PtrSlot S (sp - 80 + o) := fun o ho h8 =>
    hsf.slot (by omega) (by omega) (by omega)
  -- the words of the frame outside the three slots
  have keepW : ∀ (M' M'' : Mem) (o : Nat), (∀ a, OutHeap a → ¬ slotBytes (sp - 80 + o) a →
      imgM M'' a = imgM M' a) → ∀ o', o' + 8 ≤ 80 → (o' + 8 ≤ o ∨ o + 8 ≤ o') →
      ldv .ld M'' (sp - 80 + o') = ldv .ld M' (sp - 80 + o') := fun M' M'' o hm o' h1 h2 =>
    ldv_congr .ld fun j hj => hm _ (above_sp hab2 (by omega)).1
      (fun hs => by simp only [slotBytes, widthOfM] at hs hj; omega)
  refine dn_init hlive h1 hlen (slot 24 (by omega) rfl) (by simp only [heapEnd]; omega) _
    (by bsimp []) (by bsimp []) fun R2 M2 L2 C2 hk2 hd2 hz2 hkp2 hw2 hfr2 => ?_
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 80) := by rw [hk2.get 2 (by decide)]; bsimp []
  have hS2 : HeapOwn S := fun a h1 h2 => hd2.heap.heap.own a h1 h2
  bsimp []
  bc_run hlive hS2 [q2] at 0x800049bc
  have hlen2 : (GV.num C.z.rep.p :: GV.num xp :: hs).length ≤ 2 ^ 30 := by
    simp only [List.length_cons]; omega
  refine dn_init hlive hd2 hlen2 (slot 32 (by omega) rfl) (by simp only [heapEnd]; omega) _
    (by bsimp []) (by bsimp []) fun R3 M3 L3 C3 hk3 hd3 hz3 hkp3 hw3 hfr3 => ?_
  rw [hz2] at hd3 hw3
  have q3 : R3 2 = BitVec.ofNat 64 (sp - 80) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
  have hS3 : HeapOwn S := fun a h1 h2 => hd3.heap.heap.own a h1 h2
  bsimp []
  bc_run hlive hS3 [q3] at 0x800049bc
  have hlen3 : (GV.num C.z.rep.p :: GV.num C.z.rep.p :: GV.num xp :: hs).length ≤ 2 ^ 30 := by
    simp only [List.length_cons]; omega
  refine dn_init hlive hd3 hlen3 (slot 40 (by omega) rfl) (by simp only [heapEnd]; omega) _
    (by bsimp []) (by bsimp []) fun R4 M4 L4 C4 hk4 hd4 hz4 hkp4 hw4 hfr4 => ?_
  rw [hz3, hz2] at hd4 hw4
  bsimp []
  have k4 : Keeps (2 :: 8 :: 9 :: cClob) R4 R :=
    (hk4.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac
      ((hk3.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac
        ((hk2.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac Keeps.refl _ _)))))
  have q4 : R4 2 = BitVec.ofNat 64 (sp - 80) := by rw [hk4.get 2 (by decide)]; bsimp [q3]
  have q8 : R4 8 = 0#64 := by
    rw [hk4.get 8 (by decide)]; bsimp [hk3.get 8 (by decide), hk2.get 8 (by decide)]
  have hout : ∀ a, OutHeap a → ¬ frameIn sp 80 a → imgM M4 a = imgM M a := fun a ho hf => by
    rw [hfr4 a ho (fun hs => hf (by simp only [slotBytes, frameIn] at hs ⊢; omega)),
      hfr3 a ho (fun hs => hf (by simp only [slotBytes, frameIn] at hs ⊢; omega)),
      hfr2 a ho (fun hs => hf (by simp only [slotBytes, frameIn] at hs ⊢; omega))]
    exact hm1 a hf
  have w24 : ldv .ld M4 (sp - 80 + 24) = BitVec.ofNat 64 C.z.rep.p := by
    rw [keepW M3 M4 40 hfr4 24 (by omega) (by omega), keepW M2 M3 32 hfr3 24 (by omega) (by omega)]
    exact hw2
  have w32 : ldv .ld M4 (sp - 80 + 32) = BitVec.ofNat 64 C.z.rep.p := by
    rw [keepW M3 M4 40 hfr4 32 (by omega) (by omega)]; exact hw3
  have wO : ∀ o', o' + 8 ≤ 24 ∨ 48 ≤ o' → o' + 8 ≤ 80 →
      ldv .ld M4 (sp - 80 + o') = ldv .ld M1 (sp - 80 + o') := fun o' ho h80 => by
    rw [keepW M3 M4 40 hfr4 o' h80 (by omega), keepW M2 M3 32 hfr3 o' h80 (by omega),
      keepW M1 M2 24 hfr2 o' h80 (by omega)]
  refine hk R4 M4 L4 C4 ⟨q4,
      by rw [wO 56 (by omega) (by omega)]; exact m56, by rw [wO 64 (by omega) (by omega)]; exact m64,
      by rw [wO 72 (by omega) (by omega)]; exact m72,
      k4,
      fun a ho hg hf => hout a ho fun hf' => hf (by simp only [frameIn, dnN, dnW] at hf' ⊢; omega)⟩
    q8 hd4 (by rw [hz4, hz3, hz2])
    ((hkp2.trans (hkp3.mono fun g hg => List.mem_cons_of_mem _ hg)).trans
      (hkp4.mono fun g hg => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg)))
    (by rw [wO 8 (by omega) (by omega)]; exact m8) w24 w32 hw4

end Dc.Mach
