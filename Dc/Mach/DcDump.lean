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

theorem perm_rev3 {α : Type} (a b c : α) (l : List α) : (a :: b :: c :: l).Perm (c :: b :: a :: l) :=
  ((List.Perm.cons a (List.Perm.swap c b l)).trans (List.Perm.swap c a (b :: l))).trans
    (List.Perm.cons c (List.Perm.swap b a l))

theorem perm_4th {α : Type} (a b c d : α) (l : List α) :
    (a :: b :: c :: d :: l).Perm (d :: a :: b :: c :: l) :=
  ((List.Perm.cons a (List.Perm.cons b (List.Perm.swap d c l))).trans
    (List.Perm.cons a (List.Perm.swap d b (c :: l)))).trans (List.Perm.swap d a (b :: c :: l))

/-- A word of the frame through a step that kept the bytes off the heap, the
globals and `P`. -/
theorem dn_ld {M M' : Mem} {sp o : Nat} (hab : heapEnd ≤ sp - 80) (P : Nat → Prop)
    (hM : ∀ a, OutHeap a → ¬ DcGlob a → ¬ P a → imgM M' a = imgM M a)
    (hP : ∀ j, j < 8 → ¬ P (sp - 80 + o + j)) : ldv .ld M' (sp - 80 + o) = ldv .ld M (sp - 80 + o) :=
  ldv_congr .ld fun j hj =>
    hM _ (above_sp hab (by omega)).1 (above_sp hab (by omega)).2.1 (hP j hj)

/-- **The frame through a callee** that changed, off the heap and the
globals, only its window and `dc_dump_num`'s four slots. -/
theorem DnAt.next {S : Nat → Prop} {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp : Nat}
    (hfr : DnAt S M0 M R0 R sp) (hab : heapEnd ≤ sp - 80)
    (hM : ∀ a, OutHeap a → ¬ DcGlob a → ¬ (sp - 80 - dnW ≤ a ∧ a < sp - 32) → imgM M' a = imgM M a)
    (k : Keeps (2 :: 8 :: 9 :: cClob) R' R) (r2 : R' 2 = BitVec.ofNat 64 (sp - 80)) :
    DnAt S M0 M' R0 R' sp where
  r2 := r2
  w56 := (dn_ld hab _ hM fun j hj h => by omega).trans hfr.w56
  w64 := (dn_ld hab _ hM fun j hj h => by omega).trans hfr.w64
  w72 := (dn_ld hab _ hM fun j hj h => by omega).trans hfr.w72
  keep := k.trans hfr.keep
  out := fun a ho hg hf => (hM a ho hg fun h => hf (by simp only [frameIn, dnN] at h ⊢; omega)).trans
    (hfr.out a ho hg hf)

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

/-- **`bc_divide (dcvalue, _one_, &value, 0)`, the sign, the toss**
(`0x80002ad4` to `0x80002af8`): `value` holds the integer part, made
positive; the handle `dcvalue` released. -/
theorem dn_div {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {xp zp sp : Nat}
    {R0 R : Nat → BitVec 64} {n : Dc.Num}
    (hfr : DnAt S M0 M R0 R sp) (r8 : R 8 = 0#64)
    (h : DcAt S M H F L C G (.num zp :: .num zp :: .num zp :: .num xp :: hs) st) (hz : C.z.rep.p = zp)
    (hx : (GV.num xp).Den ⟨L, G.strs⟩ (.num n)) (hwid : n.wid < 2 ^ 20)
    (hsf : StackFrame S sp dnN) (hab : heapEnd + dnN ≤ sp)
    (m8 : ldv .ld M (sp - 80 + 8) = BitVec.ofNat 64 xp)
    (m24 : ldv .ld M (sp - 80 + 24) = BitVec.ofNat 64 zp)
    (m32 : ldv .ld M (sp - 80 + 32) = BitVec.ofNat 64 zp)
    (m40 : ldv .ld M (sp - 80 + 40) = BitVec.ofNat 64 zp)
    (hk : ∀ R' M' H' F' L' C' pv, DnAt S M0 M' R0 R' sp → R' 8 = 0#64 →
      DcAt S M' H' F' L' C' G (.num pv :: .num zp :: .num zp :: hs) st →
      (GV.num pv).Den ⟨L', G.strs⟩ (.num ⟨false, n.intPart, 0⟩) →
      ldv .ld M' (sp - 80 + 24) = BitVec.ofNat 64 pv →
      ldv .ld M' (sp - 80 + 32) = BitVec.ofNat 64 zp →
      ldv .ld M' (sp - 80 + 40) = BitVec.ofNat 64 zp → DWO live S Q t 0x80002af8#64 R' M')
    (hoom : ∀ R' M' sp', OomAt S sp dnN M0 (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80002ad4#64 R M := by
  have hsf' := hsf; have hab' := hab
  have hNW : dnN = 80 + (176 + rmStack (2 ^ 30)) := rfl
  have hWv : dnW = 176 + rmStack (2 ^ 30) := rfl
  rw [hNW] at hsf' hab'
  have hsl := hsf'.lo; have hsh := hsf'.hi; have hsa := hsf'.al
  simp only [heapEnd] at hab'
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 80 := by simp only [heapEnd]; omega
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hG := h.glob
  have q2 := hfr.r2
  have how : ldv .ld M 2147601856 = BitVec.ofNat 64 C.o.rep.p := h.view.ow
  bc_run hlive hS [q2, m8, how] at 0x8000589c
  all_goals first | exact frame_acc hsf' (by omega) (by omega) | skip
  obtain ⟨L1, L2, xr, rfl, rfl⟩ := h.handle_num
  obtain ⟨x, hxL, rfl, hxn⟩ := hx.numObj
  have hxm : xr ∈ L1 ++ xr :: L2 := List.mem_append_right _ List.mem_cons_self
  have hr2 := h.zero_refs hxm hz.symm
  have hn1 := h.heap.nums x hxL
  have hno := h.heap.nums C.o h.den.mo
  have w1 := NumRep.len_le_wid hn1.shape (h.den.norm x hxL)
  have w2 := NumRep.len_le_wid hno.shape (h.den.norm _ h.den.mo)
  rw [hxn] at w1
  rw [h.den.ov] at w2
  have hd1 : decLen 1 = 1 := by unfold decLen; simp
  have hone : Dc.Num.one.wid = 1 := by simp only [Dc.Num.wid, Dc.Num.one, hd1]
  rw [hone] at w2
  obtain ⟨m, hm, hmm, hms⟩ := Dc.BcModel.div_one_zero n
  refine bc_divide_spec hlive (W := dnW) (sp := sp - 80) (q := sp - 80 + 24) (k := 0) (z := C.z)
    (x1 := x) (x2 := C.o) (n := some m)
    ⟨StackFrame.sub (m := 80) (n := dnW) hsf (by decide), by simp only [heapEnd, dnW]; omega,
      by simp only [dnW]; omega, hsf'.slot (by omega) (by omega) (by omega),
      fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega),
      .inr (by omega), .inr (by simp only [dc_addrs]; omega),
      fun a ha => hG a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega),
      by bsimp [q2], by bsimp []⟩
    ⟨fun m' hm' R3 Mt H3 F3 L3 y hk3 h30 hp => ?_, fun hnone => (Option.some_ne_none m hnone).elim,
      fun R3 Mt sp' o1 o2 hr2' hout => ?_⟩
    ⟨by rw [hxn, h.den.ov, hm], hxL, h.den.mo, h.den.mz, fun e => absurd e (by omega), by omega, h.view.zw,
      h.den.pos x hxL⟩
    (by rw [h.den.zv]; rfl) h.heap (h.resSlot m24) (by bsimp []) (by bsimp []) (by bsimp [])
    (by bsimp [])
  · -- the integer part, made positive; the handle `dcvalue` released
    obtain rfl := Option.some.inj hm'
    have hy := hp.heap.nums y List.mem_cons_self
    num_facts hy
    have hsy := (hp.heap.blocks y List.mem_cons_self).sPay
    have w24 : ldv .ld Mt (sp - 80 + 24) = BitVec.ofNat 64 y.rep.p := by rw [hp.slot, hsy]
    have q3 : R3 2 = BitVec.ofNat 64 (sp - 80) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
    have r83 : R3 8 = 0#64 := by rw [hk3.get 8 (by decide)]; bsimp [r8]
    have hS3 : HeapOwn S := fun a e1 e2 => hp.heap.heap.own a e1 e2
    bsimp []
    bc_run hlive hS3 [q3, r83, w24] at 0x800048c0
    all_goals first | exact frame_acc hsf' (by omega) (by omega) |
      exact acc_heap hS3 (by omega) (by omega) | skip
    generalize hM3 : writeLog Mt [(y.rep.p, 4, 0#64)] = M3
    bc_run hlive hS3 [q3] at 0x800048c0
    have hb3 : BcHeap S (G.raws M) M3 H3 F3
        ([] ++ { y with rep := { y.rep with neg := false } } :: L3) := by
      rw [← hM3]; exact (hp.heap : BcHeap S (G.raws M) Mt H3 F3 ([] ++ y :: L3)).setSign false (by decide)
    have e3 : ∀ a, OutHeap a → ¬ (frameIn (sp - 80) dnW a ∨ slotBytes (sp - 80 + 24) a) →
        imgM M3 a = imgM M a := fun a ho hn => by
      rw [← hM3, imgM_store_miss _ _ (by
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ho; omega)]
      exact hp.out a ho (fun h => hn (.inr h)) (fun h => hn (.inl h))
    obtain ⟨C3, hd3, hkp3⟩ := h.newNum hp.rest hb3 hp.refs hp.norm hp.pos hp.owns fun a ha =>
      e3 a ha.outHeap fun h => by
        have := ha.lt; simp only [frameIn, slotBytes, heapStart, dnW] at h this; omega
    have g8 : ldv .ld M3 (sp - 80 + 8) = BitVec.ofNat 64 x.rep.p :=
      (dn_ld hab2 _ (fun a ho _ hn => e3 a ho hn) fun j hj h => by
        simp only [frameIn, slotBytes] at h; omega).trans m8
    have hS3' : HeapOwn S := fun a e1 e2 => hd3.heap.heap.own a e1 e2
    refine bc_free_num_dcK hlive (hd3.perm (perm_4th _ _ _ _ _))
      (hsf'.slot (by omega) (by omega) (by omega)) (by simp only [heapEnd]; omega) g8
      (hsf'.within (m := 80) (n := 32) (by omega) (by decide)) (by simp only [heapEnd]; omega)
      (.inr (by omega)) _ ?f10 ?f2 ?fal fun R6 M6 H6 F6 L6 C6 hk6 hd6 hout6 hkp6 => ?_
    case f10 => bsimp [q3]
    case f2 => bsimp [q3]
    case fal => bsimp []
    have q6 : R6 2 = BitVec.ofNat 64 (sp - 80) := by rw [hk6.get 2 (by decide)]; bsimp [q3]
    have r86 : R6 8 = 0#64 := by rw [hk6.get 8 (by decide)]; bsimp [r83]
    have hS6 : HeapOwn S := fun a e1 e2 => hd6.heap.heap.own a e1 e2
    bsimp []
    bc_run hlive hS6 [] at 0x80002af8
    have e6 : ∀ a, OutHeap a → ¬ DcGlob a → ¬ (sp - 80 - dnW ≤ a ∧ a < sp - 32) →
        imgM M6 a = imgM M a := fun a ho hg hn => by
      rw [hout6 a ho hg (fun h => hn (by simp only [frameIn, dnW] at h ⊢; omega))
        (fun h => hn (by simp only [slotBytes] at h; omega))]
      exact e3 a ho fun h => hn (by
        rcases h with h | h <;> simp only [frameIn, slotBytes, dnW] at h ⊢ <;> omega)
    have f6 : ∀ o, 16 ≤ o → o + 8 ≤ 80 → ldv .ld M6 (sp - 80 + o) = ldv .ld M3 (sp - 80 + o) :=
      fun o h1 h2 => dn_ld hab2 (fun a => frameIn (sp - 80) 32 a ∨ slotBytes (sp - 80 + 8) a)
        (fun a ho hg hn => hout6 a ho hg (fun h => hn (.inl h)) (fun h => hn (.inr h)))
        fun j hj h => by rcases h with h | h <;> simp only [frameIn, slotBytes] at h <;> omega
    have k6 : Keeps (2 :: 8 :: 9 :: cClob) R6 R :=
      (hk6.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac
        ((hk3.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    have hden : (GV.num y.rep.p).Den ⟨L6, G.strs⟩ (.num ⟨false, n.intPart, 0⟩) := by
      refine hkp6 _ List.mem_cons_self _ ⟨_, List.mem_cons_self, rfl, ?_⟩
      have e1 := congrArg Dc.Num.mag hp.num
      have e2 := congrArg Dc.Num.scale hp.num
      simp only [NumRep.num] at e1 e2 ⊢
      rw [e1, e2, hmm, hms]
    refine hk R6 M6 H6 F6 L6 C6 y.rep.p (hfr.next hab2 e6 k6 q6) r86 hd6 hden ?_ ?_ ?_
    · rw [f6 24 (by omega) (by omega), ← hM3, ldv_store_miss .ld Mt _ (by omega)]; exact w24
    · rw [f6 32 (by omega) (by omega), dn_ld hab2 _ (fun a ho _ hn => e3 a ho hn) fun j hj h => by
        simp only [frameIn, slotBytes] at h; omega]
      exact m32
    · rw [f6 40 (by omega) (by omega), dn_ld hab2 _ (fun a ho _ hn => e3 a ho hn) fun j hj h => by
        simp only [frameIn, slotBytes] at h; omega]
      exact m40
  · bc_run hlive hS [] at 0x80001e74
    refine hoom R3 Mt sp' ⟨by simp only [dnN]; omega, by omega, hr2', fun a ho hg hf _ => ?_⟩
    rw [hout a ho (fun hs => hf (by simp only [slotBytes, frameIn, dnN] at hs ⊢; omega))
      (fun hs => hf (by simp only [frameIn, dnN] at hs ⊢; omega))]
    exact hfr.out a ho hg hf

/-- **The digit loop's head** (`0x80002b08`): the handles `digit`, `value`
(the quotient `v` left), `obase` (`256`) in their slots, the cells from `s0`
holding the digits pushed. -/
structure DnLoop (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp : Nat) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs : List GV) (st : St)
    (pd pv pb n0 v : Nat) (cells : List Blk) (ds : List Nat) (p : Nat) : Prop where
  fr : DnAt S M0 M R0 R sp
  h : DcAt S M H F L C G (.num pd :: .num pv :: .num pb :: hs) st
  dv : (GV.num pv).Den ⟨L, G.strs⟩ (.num ⟨false, v, 0⟩)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num ⟨false, 256, 0⟩)
  w24 : ldv .ld M (sp - 80 + 24) = BitVec.ofNat 64 pv
  w32 : ldv .ld M (sp - 80 + 32) = BitVec.ofNat 64 pb
  w40 : ldv .ld M (sp - 80 + 40) = BitVec.ofNat 64 pd
  s0 : R 8 = BitVec.ofNat 64 p
  stk : DnStk H F L G M cells ds p
  inv : DumpInv n0 v ds
  cont : ds ≠ [] → v ≠ 0
  vle : v ≤ n0

/-- `_bc_rec_mul`'s base word, off every byte `dc_dump_num` changes. -/
theorem DnAt.mulBase {S : Nat → Prop} {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp : Nat}
    (hfr : DnAt S M0 M R0 R sp) (hab : heapEnd + dnN ≤ sp) (hmb : MulBase S M0) : MulBase S M :=
  hmb.transport fun a e1 e2 => hfr.out a
    (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, mulBaseAddr] at e1 e2 ⊢; omega)
    (by simp only [DcGlob, dc_addrs, mulBaseAddr] at e1 e2 ⊢; omega)
    (by simp only [frameIn, heapEnd, mulBaseAddr] at e1 e2 hab ⊢; omega)

/-- **`bc_int2num (&obase, 256)`** (`0x80002af8` to the loop head): `obase`
holds `256`, no digit pushed. -/
theorem dn_i2n {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pv zp sp n0 : Nat}
    {R0 R : Nat → BitVec 64}
    (hfr : DnAt S M0 M R0 R sp) (h : DcAt S M H F L C G (.num pv :: .num zp :: .num zp :: hs) st)
    (hv : (GV.num pv).Den ⟨L, G.strs⟩ (.num ⟨false, n0, 0⟩))
    (hsf : StackFrame S sp dnN) (hab : heapEnd + dnN ≤ sp)
    (m24 : ldv .ld M (sp - 80 + 24) = BitVec.ofNat 64 pv)
    (m32 : ldv .ld M (sp - 80 + 32) = BitVec.ofNat 64 zp)
    (m40 : ldv .ld M (sp - 80 + 40) = BitVec.ofNat 64 zp)
    (hk : ∀ R' M' H' F' L' C' pb, DnLoop S M0 M' R0 R' sp H' F' L' C' G hs st zp pv pb n0 n0 [] [] 0 →
      DWO live S Q t 0x80002b08#64 R' M')
    (hoom : ∀ R' M' sp', OomAt S sp dnN M0 (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80002af8#64 R M := by
  have hsf' := hsf; have hab' := hab
  have hNW : dnN = 80 + (176 + rmStack (2 ^ 30)) := rfl
  have hWv : dnW = 176 + rmStack (2 ^ 30) := rfl
  rw [hNW] at hsf' hab'
  have hsl := hsf'.lo; have hsh := hsf'.hi; have hsa := hsf'.al
  simp only [heapEnd] at hab'
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 80 := by simp only [heapEnd]; omega
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have q2 := hfr.r2
  bc_run hlive hS [q2] at 0x8000690c
  refine dc_int2num_spec hlive (v := 256) (h.perm (List.Perm.swap _ _ _))
    (hsf'.slot (by omega) (by omega) (by omega)) (by simp only [heapEnd]; omega) m32
    (hsf'.within (m := 80) (n := 128) (by omega) (by decide)) (by simp only [heapEnd]; omega)
    (.inr (by omega)) _ (by bsimp [q2]) (by bsimp []; rfl) (by bsimp [q2]) (by bsimp []) (by decide)
    (by decide) (fun R1 M1 H1 F1 L1 C1 y hk1 hd1 hnum hw1 hout1 hkp1 => ?_)
    (fun R1 M1 hr2 hout1 => ?_)
  · have q1 : R1 2 = BitVec.ofNat 64 (sp - 80) := by rw [hk1.get 2 (by decide)]; bsimp [q2]
    have hS1 : HeapOwn S := fun a e1 e2 => hd1.heap.heap.own a e1 e2
    bsimp []
    bc_run hlive hS1 [] at 0x80002b08
    have e1 : ∀ a, OutHeap a → ¬ DcGlob a → ¬ (sp - 80 - dnW ≤ a ∧ a < sp - 32) →
        imgM M1 a = imgM M a := fun a ho _ hn =>
      hout1 a ho (fun h => hn (by simp only [slotBytes] at h; omega))
        (fun h => hn (by simp only [frameIn, dnW] at h ⊢; omega))
    have f1 : ∀ o, o + 8 ≤ 80 → (o + 8 ≤ 32 ∨ 40 ≤ o) →
        ldv .ld M1 (sp - 80 + o) = ldv .ld M (sp - 80 + o) := fun o h1 h2 =>
      dn_ld hab2 (fun a => slotBytes (sp - 80 + 32) a ∨ frameIn (sp - 80) 128 a)
        (fun a ho _ hn => hout1 a ho (fun h => hn (.inl h)) (fun h => hn (.inr h)))
        fun j hj h => by rcases h with h | h <;> simp only [slotBytes, frameIn] at h <;> omega
    have k1 : Keeps (2 :: 8 :: 9 :: cClob) (upd R1 8 0#64) R :=
      Keeps.upd _ (by decide) ((hk1.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans
        (by keeps_tac Keeps.refl _ _))
    have hvb : (GV.num y.rep.p).Den ⟨y :: L1, G.strs⟩ (.num ⟨false, 256, 0⟩) :=
      ⟨y, List.mem_cons_self, rfl, by rw [hnum]; rfl⟩
    have hP : (GV.num y.rep.p :: .num pv :: .num zp :: hs).Perm (.num zp :: .num pv :: .num y.rep.p :: hs) :=
      perm_rev3 _ _ _ _
    exact hk _ M1 H1 F1 (y :: L1) C1 y.rep.p ⟨hfr.next hab2 e1 k1 (by bsimp [q1]), hd1.perm hP,
      hkp1 _ List.mem_cons_self _ hv, hvb, (f1 24 (by omega) (by omega)).trans m24, hw1,
      (f1 40 (by omega) (by omega)).trans m40, by bsimp [], DnStk.nil _ _ _ _ _, DumpInv.start n0,
      fun h => (h rfl).elim, Nat.le_refl _⟩
  · bc_run hlive hS [] at 0x80001e74
    refine hoom _ M1 (sp - 80 - 128) ⟨by simp only [dnN, dnW]; omega, by omega, hr2,
      fun a ho hg hf _ => ?_⟩
    rw [hout1 a ho (fun h => hf (by simp only [slotBytes, frameIn, dnN] at h ⊢; omega))
      (fun h => hf (by simp only [frameIn, dnN, dnW] at h ⊢; omega))]
    exact hfr.out a ho hg hf

/-- **After `bc_divmod`** (`0x80002b20`): the quotient `v` in `value`, the
digit `d` in `digit`. -/
structure DnMid (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp : Nat) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs : List GV) (st : St)
    (pd pv pb v d : Nat) (cells : List Blk) (ds : List Nat) (p : Nat) : Prop where
  fr : DnAt S M0 M R0 R sp
  h : DcAt S M H F L C G (.num pd :: .num pv :: .num pb :: hs) st
  dv : (GV.num pv).Den ⟨L, G.strs⟩ (.num ⟨false, v, 0⟩)
  dd : (GV.num pd).Den ⟨L, G.strs⟩ (.num ⟨false, d, 0⟩)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num ⟨false, 256, 0⟩)
  w24 : ldv .ld M (sp - 80 + 24) = BitVec.ofNat 64 pv
  w32 : ldv .ld M (sp - 80 + 32) = BitVec.ofNat 64 pb
  w40 : ldv .ld M (sp - 80 + 40) = BitVec.ofNat 64 pd
  s0 : R 8 = BitVec.ofNat 64 p
  stk : DnStk H F L G M cells ds p

/-- **`bc_divmod (value, obase, &value, &digit, 0)`** (`0x80002b08` to
`0x80002b20`): `v / 256` in `value`, `v % 256` in `digit`; the cells kept as
raw blocks. -/
theorem dn_dm {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pd pv pb n0 v sp p : Nat}
    {R0 R : Nat → BitVec 64} {cells : List Blk} {ds : List Nat}
    (hl : DnLoop S M0 M R0 R sp H F L C G hs st pd pv pb n0 v cells ds p)
    (hmb : MulBase S M0) (hsz : decLen n0 < 2 ^ 20) (hhs : hs.length + 3 ≤ 2 ^ 20)
    (hsf : StackFrame S sp dnN) (hab : heapEnd + dnN ≤ sp)
    (hk : ∀ R' M' H' F' L' C' pd' pv', DnMid S M0 M' R0 R' sp H' F' L' C' G hs st pd' pv' pb
      (v / 256) (v % 256) cells ds p → DWO live S Q t 0x80002b20#64 R' M')
    (hoom : ∀ R' M' sp', OomAt S sp dnN M0 (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80002b08#64 R M := by
  have hsf' := hsf; have hab' := hab
  have hNW : dnN = 80 + (176 + rmStack (2 ^ 30)) := rfl
  have hWv : dnW = 176 + rmStack (2 ^ 30) := rfl
  rw [hNW] at hsf' hab'
  have hsl := hsf'.lo; have hsh := hsf'.hi; have hsa := hsf'.al
  simp only [heapEnd] at hab'
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 80 := by simp only [heapEnd]; omega
  have h := hl.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hG := h.glob
  have q2 := hl.fr.r2
  bc_run hlive hS [q2, hl.w24, hl.w32] at 0x80005fd0
  all_goals first | exact frame_acc hsf' (by omega) (by omega) | skip
  obtain ⟨xv, hxv, rfl, hxvn⟩ := hl.dv.numObj
  obtain ⟨xb, hxb, rfl, hxbn⟩ := hl.db.numObj
  obtain ⟨L1, L2, xd, hL, rfl⟩ := h.handle_num
  have hxd : xd ∈ L := hL ▸ List.mem_append_right _ List.mem_cons_self
  have hlen : (GV.num xd.rep.p :: GV.num xv.rep.p :: GV.num xb.rep.p :: hs).length ≤ 2 ^ 20 := by
    simp only [List.length_cons]; omega
  have w1 := NumRep.len_le_wid (h.heap.nums xv hxv).shape (h.den.norm xv hxv)
  have w2 := NumRep.len_le_wid (h.heap.nums xb hxb).shape (h.den.norm xb hxb)
  rw [hxvn] at w1
  rw [hxbn] at w2
  have d1 : decLen v ≤ decLen n0 := decLen_mono hl.vle
  have d2 : decLen 256 = 3 := by simp [decLen]
  simp only [Dc.Num.wid, d2] at w1 w2
  have hdm : Dc.Num.divmod xv.rep.num xb.rep.num 0 =
      some (⟨false, v / 256, 0⟩, ⟨false, v % 256, 0⟩) := by
    rw [hxvn, hxbn]; exact Dc.BcModel.divmodInt v 256 (by decide)
  have hmb1 := hl.fr.mulBase hab hmb
  refine bc_divmod_spec hlive (W := dnW) (sp := sp - 80) (k := 0) (z := C.z) (xq := xv) (xr := xd)
    (qq := sp - 80 + 24) (qr := sp - 80 + 40)
    ⟨StackFrame.sub (m := 80) (n := dnW) hsf (by decide), by simp only [heapEnd, dnW]; omega,
      Nat.le_refl _, hmb1.own, fun a ha => hG a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega),
      by bsimp [q2], by bsimp []⟩
    ⟨hxv, hxb, h.den.mz, h.den.norm xv hxv, h.den.norm xb hxb, h.den.pos xv hxv, by omega,
      (h.kzero hlen).mono (by omega), hmb1.word, h.den.owns⟩
    ⟨⟨hsf'.slot (by omega) (by omega) (by omega),
        fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega), .inr (by omega)⟩,
      ⟨hsf'.slot (by omega) (by omega) (by omega),
        fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega), .inr (by omega)⟩,
      .inl (by omega), by omega, hxv, hxd, h.den.live xv hxv, h.den.live xd hxd,
      fun e => h.refs2 hxd (by subst e; simp only [List.count_cons_self]; omega), hl.w24, hl.w40⟩
    (h.withCells hl.stk)
    ⟨fun m hm R4 Mt H4 F4 Lf yq yr hk4 h40 hp => ?_, fun hz => absurd (hdm.symm.trans hz) (by simp),
      fun R4 Mt sp' o1 o2 hr2' hout => ?_⟩
    (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
  · rw [hdm] at hm
    obtain rfl := Option.some.inj hm
    obtain ⟨Lm, hd1, hd2⟩ := hp.mid
    obtain ⟨C4, hd4, hkp4⟩ := h.newNum2 hd1 hd2 hp.heap.dropCells hp.quo.toNewNum hp.rem.toNewNum
      fun a ha => hp.out a ha.outHeap
        (fun h => by have := ha.lt; simp only [slotBytes, heapStart] at h this; omega)
        (fun h => by have := ha.lt; simp only [slotBytes, heapStart] at h this; omega)
        (fun h => by have := ha.lt; simp only [frameIn, heapStart, dnW] at h this; omega)
    have e4 : ∀ a, OutHeap a → ¬ DcGlob a → ¬ (sp - 80 - dnW ≤ a ∧ a < sp - 32) →
        imgM Mt a = imgM M a := fun a ho _ hn =>
      hp.out a ho (fun h => hn (by simp only [slotBytes] at h; omega))
        (fun h => hn (by simp only [slotBytes] at h; omega))
        (fun h => hn (by simp only [frameIn] at h ⊢; omega))
    have k4 : Keeps (2 :: 8 :: 9 :: cClob) R4 R :=
      (hk4.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac Keeps.refl _ _)
    have hbq := hp.heap.blocks yq (List.mem_cons_of_mem _ List.mem_cons_self)
    have hbr := hp.heap.blocks yr List.mem_cons_self
    refine hk R4 Mt H4 F4 (yr :: yq :: Lf) C4 yr.rep.p yq.rep.p
      ⟨hl.fr.next hab2 e4 k4 (by rw [hk4.get 2 (by decide)]; bsimp [q2]),
        hd4.perm (List.Perm.swap _ _ _),
        ⟨yq, List.mem_cons_of_mem _ List.mem_cons_self, rfl, hp.quo.num⟩,
        ⟨yr, List.mem_cons_self, rfl, hp.rem.num⟩,
        hkp4 _ List.mem_cons_self _ hl.db,
        by rw [hp.quo.slot, hbq.sPay], ?_, by rw [hp.rem.slot, hbr.sPay],
        by rw [hk4.get 8 (by decide)]; bsimp [hl.s0], hl.stk.ofRaw hp.heap⟩
    rw [dn_ld hab2 (fun a => slotBytes (sp - 80 + 24) a ∨ slotBytes (sp - 80 + 40) a ∨
        frameIn (sp - 80) dnW a)
      (fun a ho _ hn => hp.out a ho (fun h => hn (.inl h)) (fun h => hn (.inr (.inl h)))
        (fun h => hn (.inr (.inr h))))
      fun j hj h => by rcases h with h | h | h <;> simp only [slotBytes, frameIn] at h <;> omega]
    exact hl.w32
  · bc_run hlive hS [] at 0x80001e74
    refine hoom R4 Mt sp' ⟨by simp only [dnN]; omega, by omega, hr2', fun a ho hg hf _ => ?_⟩
    rw [hout a ho (fun h => hf (by simp only [frameIn, dnN] at h ⊢; omega))]
    exact hl.fr.out a ho hg hf

end Dc.Mach
