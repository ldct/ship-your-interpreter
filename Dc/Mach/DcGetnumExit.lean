import Dc.Mach.DcGetnumLoop

/-!
# `dc_getnum`: the exit (M9)

From `0x80002840` `dc_getnum` frees `temp`, `build` and `base`, stores the
character it read last through `readahead` (when non-`NULL`), and returns
`{DC_NUMBER, result}`.

- `RaOK`: the `readahead` word, four bytes of the caller's frame.
- `GnX`: the state at `0x80002840`.
- `gn_exit`: the exit.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open VsaIris.Interp (imgLE imgLE_store4_hit imgLE_store_miss ldv_ld_imgW imgW_lo32)

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **The `readahead` word**: four owned bytes above `dc_getnum`'s frame. -/
structure RaOK (S : Nat → Prop) (sp ra : Nat) : Prop where
  own : ∀ a, ra ≤ a → a < ra + 4 → S a
  al : ra % 4 = 0
  lo : sp ≤ ra
  hi : ra + 4 ≤ 2281701376

/-- The bytes of the `readahead` word (none for `NULL`). -/
def RaB (ra a : Nat) : Prop := ra ≠ 0 ∧ ra ≤ a ∧ a < ra + 4

/-- **The state at the exit** `0x80002840`: `result` holds `n`, `temp` a
handle or `NULL`, `build` and `base` a handle each; the reader after `jE`. -/
structure GnX (S : Nat → Prop) (M0 : Mem) (R0 : Nat → BitVec 64) (sp : Nat) (G : DcG)
    (hs0 : List GV) (st : St) (o : StrObj) (j0 ra : Nat) (s6 : BitVec 64) (L0 : List NumObj)
    (R : Nat → BitVec 64) (M : Mem) (jE : Nat) (n : Num) (og : Option Nat) (H : Heap) (F : List Blk)
    (L : List NumObj) (C : BcConsts) (pr pd pb : Nat) : Prop where
  fr : CFr InP 144 gnSv M0 M R0 R sp
  h : DcAt S M H F L C G (.num pr :: .num pd :: .num pb :: (slotHs og ++ hs0)) st
  w16 : ldv .ld M (sp - 144 + 16) = BitVec.ofNat 64 pr
  w24 : ldv .ld M (sp - 144 + 24) = BitVec.ofNat 64 pd
  w32 : ldv .ld M (sp - 144 + 32) = BitVec.ofNat 64 (og.getD 0)
  w8 : ldv .ld M (sp - 144 + 8) = BitVec.ofNat 64 pb
  dr : (GV.num pr).Den ⟨L, G.strs⟩ (.num n)
  keep : HsKeep ⟨L0, G.strs⟩ ⟨L, G.strs⟩ hs0
  regs : GnRegs R ra s6
  rd : GnRd M R o j0 jE

theorem gnSv_below : ∀ q ∈ gnSv, q.1 + 8 ≤ 144 := by
  intro q hq; simp only [gnSv, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem slotHs_perm3 (a b c : GV) (og : Option Nat) (l : List GV) :
    (a :: b :: c :: (slotHs og ++ l)).Perm (slotHs og ++ a :: b :: c :: l) := by
  cases og with
  | none => exact List.Perm.refl _
  | some x => exact List.perm_middle (l₁ := [a, b, c])

/-- `dc_getnum`'s epilogue from `0x80002860`: `ra`, `s0` restored, the
return word's low half `1`. -/
theorem gn_epi1 {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {sp : Nat} (hsf : StackFrame S sp 144)
    {R0 R : Nat → BitVec 64} {M : Mem} (q2 : R 2 = BitVec.ofNat 64 (sp - 144))
    (s1 : ldv .ld M (sp - 144 + 136) = R0 1) (s8 : ldv .ld M (sp - 144 + 128) = R0 8)
    (hk : ∀ R', Keeps [1, 8, 15] R' R → R' 1 = R0 1 → R' 8 = R0 8 →
      DWO live S Q t 0x80002870#64 R' (writeLog M [(sp - 144 + 48, 4, 1#64)])) :
    DWO live S Q t 0x80002860#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [q2, s1, s8] at 0x80002870
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp [])

/-- `dc_getnum`'s return from `0x80002870`: `a0` the return word, `a1`
`result`, `s1`…`s7` restored, the frame popped. -/
theorem gn_epi2 {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {sp : Nat} (hsf : StackFrame S sp 144)
    {R0 R : Nat → BitVec 64} {M : Mem} {pr : Nat} (q2 : R 2 = BitVec.ofNat 64 (sp - 144))
    (sv : ∀ q ∈ gnSv, ldv .ld M (sp - 144 + q.1) = R0 q.2)
    (w16 : ldv .ld M (sp - 144 + 16) = BitVec.ofNat 64 pr) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [2, 9, 10, 11, 18, 19, 20, 21, 22, 23] R' R → R' 2 = BitVec.ofNat 64 sp →
      (∀ z ∈ [9, 18, 19, 20, 21, 22, 23], R' z = R0 z) → R' 10 = ldv .ld M (sp - 144 + 48) →
      R' 11 = BitVec.ofNat 64 pr → DWO live S Q t (R 1) R' M) :
    DWO live S Q t 0x80002870#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have s9 := sv (0x78, 9) (by decide)
  have s18 := sv (0x70, 18) (by decide)
  have s19 := sv (0x68, 19) (by decide)
  have s20 := sv (0x60, 20) (by decide)
  have s21 := sv (0x58, 21) (by decide)
  have s22 := sv (0x50, 22) (by decide)
  have s23 := sv (0x48, 23) (by decide)
  simp only at s9 s18 s19 s20 s21 s22 s23
  bc_run hlive hS [q2, s9, s18, s19, s20, s21, s22, s23, w16]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []; rw [Nat.sub_add_cancel (by omega)]) (fun z hz => ?_) (by bsimp [])
    (by bsimp [])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bsimp []

theorem ld_lo32_store4 (Mt : Mem) (a : Nat) (v : BitVec 64) :
    (ldv .ld (writeLog Mt [(a, 4, v)]) a).toNat % 2 ^ 32 = v.toNat % 2 ^ 32 := by
  rw [ldv_ld_imgW, imgW_lo32, imgLE_store4_hit]

/-- **`dc_getnum`'s tail** from `0x80002860`, the handles freed and the
`readahead` word stored: the return. -/
theorem gn_tail {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {ra : Nat} {L0 : List NumObj} (cx : CfCtx S 144 sp)
    (hra : ra = 0 ∨ RaOK S sp ra) (h02 : R0 2 = BitVec.ofNat 64 sp) (hal0 : (R0 1).toNat % 4 = 0)
    {R3 : Nat → BitVec 64} {M3 M4 : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
    {pr : Nat} {n : Num} {pw : BitVec 64} {rw : Nat}
    (fr3 : CFr InP 144 gnSv M0 M3 R0 R3 sp) (h4 : DcAt S M4 H F L C G (.num pr :: hs0) st)
    (sv4 : ∀ q ∈ gnSv, ldv .ld M4 (sp - 144 + q.1) = R0 q.2)
    (w4 : ldv .ld M4 (sp - 144 + 16) = BitVec.ofNat 64 pr) (p4 : ldv .ld M4 inPtrAddr = pw)
    (ra4 : ra ≠ 0 → imgLE (imgM M4) ra 4 = rw)
    (out4 : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp (144 + cfW) a → ¬ InP a → ¬ RaB ra a →
      imgM M4 a = imgM M0 a)
    (dr : (GV.num pr).Den ⟨L, G.strs⟩ (.num n)) (keep : HsKeep ⟨L0, G.strs⟩ ⟨L, G.strs⟩ hs0)
    (hk : ∀ R' M' H' F' L' C', Keeps cClob R' R0 → R' 2 = R0 2 →
      DcAt S M' H' F' L' C' G (.num pr :: hs0) st → (GV.num pr).Den ⟨L', G.strs⟩ (.num n) →
      HsKeep ⟨L0, G.strs⟩ ⟨L', G.strs⟩ hs0 → R' 11 = BitVec.ofNat 64 pr → (R' 10).toNat % 2 ^ 32 = 1 →
      ldv .ld M' inPtrAddr = pw → (ra ≠ 0 → imgLE (imgM M') ra 4 = rw) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp (144 + cfW) a → ¬ InP a → ¬ RaB ra a →
        imgM M' a = imgM M0 a) →
      DWO live S Q t (R0 1) R' M') :
    DWO live S Q t 0x80002860#64 R3 M4 := by
  have hab := cx.abv
  have hab' := cx.ab
  have hsf := cx.sf
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab hab'
  have hsf1 : StackFrame S sp 144 := cx.sf.within (m := 0) (n := 144) (by omega) (by decide)
  have hS : HeapOwn S := fun a e1 e2 => h4.heap.heap.own a e1 e2
  refine gn_epi1 hlive hS hsf1 fr3.r2 (sv4 (0x88, 1) (by decide)) (sv4 (0x80, 8) (by decide))
    fun R1 k1 e1 e8 => ?_
  have sm : ∀ q ∈ gnSv, ldv .ld (writeLog M4 [(sp - 144 + 48, 4, 1#64)]) (sp - 144 + q.1) = R0 q.2 :=
    fun q hq => by
      have := gnSv_above (o := 48) (by omega) q hq
      rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega)]; exact sv4 q hq
  have m16 : ldv .ld (writeLog M4 [(sp - 144 + 48, 4, 1#64)]) (sp - 144 + 16) = BitVec.ofNat 64 pr := by
    rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega)]; exact w4
  have hS1 : HeapOwn S := hS
  have q21 : R1 2 = BitVec.ofNat 64 (sp - 144) := (k1.get 2).trans fr3.r2
  refine gn_epi2 hlive hS1 hsf1 q21 sm m16 (by rw [e1]; exact hal0) fun R2 k2 e2 es e10 e11 => ?_
  have hmo : MemOnly (fun a => sp - 144 + 48 ≤ a ∧ a < sp - 144 + 48 + 4)
      (writeLog M4 [(sp - 144 + 48, 4, 1#64)]) M4 := fun a ha =>
    imgM_store_miss _ _ (by omega)
  have h5 := h4.outWrite hmo fun a ha => (above_sp (sp := sp - 144) (by simp only [heapEnd]; omega)
    (by omega)).imp_right And.left
  rw [e1]
  refine hk R2 _ H F L C (Keeps.restoreAll (rs := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23])
    (((k2.mono (by decide)).trans (k1.mono (by decide))).trans (fr3.keep.mono (by decide))) fun z hz => ?_)
    (e2.trans h02.symm) h5 dr keep e11 (by rw [e10, ld_lo32_store4]; rfl)
    (by rw [ldv_store_miss _ _ _ (by simp only [widthOfM, inPtrAddr]; omega)]; exact p4)
    (fun hr0 => by
      rcases hra with e | hr
      · exact absurd e hr0
      · have := hr.lo
        rw [imgLE_store_miss _ _ (by omega)]; exact ra4 hr0)
    fun a ho hg hf hp hr => by
      rw [imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]; exact out4 a ho hg hf hp hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [k2.get 1, e1]
  · rw [e2, h02]
  · rw [k2.get 8, e8]
  all_goals exact es _ (by decide)

/-- **`dc_getnum`'s exit** from `0x80002840`: `temp`, `build`, `base` freed,
the last character through `readahead`, `{DC_NUMBER, result}` returned with
`result`'s reference. -/
theorem gn_exit {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (cx : CfCtx S 144 sp) (hra : ra = 0 ∨ RaOK S sp ra)
    (h02 : R0 2 = BitVec.ofNat 64 sp) (hal0 : (R0 1).toNat % 4 = 0)
    {R : Nat → BitVec 64} {M : Mem} {jE : Nat} {n : Num} {og : Option Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {pr pd pb : Nat}
    (hX : GnX S M0 R0 sp G hs0 st o j0 ra s6 L0 R M jE n og H F L C pr pd pb)
    (hk : ∀ R' M' H' F' L' C', Keeps cClob R' R0 → R' 2 = R0 2 →
      DcAt S M' H' F' L' C' G (.num pr :: hs0) st → (GV.num pr).Den ⟨L', G.strs⟩ (.num n) →
      HsKeep ⟨L0, G.strs⟩ ⟨L', G.strs⟩ hs0 → R' 11 = BitVec.ofNat 64 pr → (R' 10).toNat % 2 ^ 32 = 1 →
      ldv .ld M' inPtrAddr = BitVec.ofNat 64 (o.tb.pay + j0 + min (jE + 1) (rdW o j0).length) →
      (ra ≠ 0 → imgLE (imgM M') ra 4 = (chW (rdW o j0)[jE]?).toNat % 2 ^ 32) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp (144 + cfW) a → ¬ InP a → ¬ RaB ra a →
        imgM M' a = imgM M0 a) →
      DWO live S Q t (R0 1) R' M') :
    DWO live S Q t 0x80002840#64 R M := by
  have hab := cx.abv
  have hab' := cx.ab
  have hW : cfW = 176 + rmStack (2 ^ 30) := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hsf := cx.sf
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab hab'
  have hcab : heapEnd + cfW ≤ sp - 144 := by simp only [heapEnd]; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h := hX.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have q2 := hX.fr.r2
  bc_run hlive hS [q2] at 0x800048c0
  refine cf_freeO hlive cx (hX.fr.regs (by keeps_tac Keeps.refl _ _)) (h.perm (slotHs_perm3 _ _ _ _ _))
    (gnSv_above (by omega)) (o := 32) (by omega) (by omega) hX.w32 (by bsimp [q2]) (by bsimp [])
    fun R1 M1 H1 F1 L1 C1 hk1 fr1 h1 _ ho1 hkp1 => ?_
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  have q21 := fr1.r2
  bsimp []
  bc_run hlive hS1 [q21] at 0x800048c0
  refine cf_free hlive cx (fr1.regs (by keeps_tac Keeps.refl _ _)) (h1.perm (List.Perm.swap _ _ _))
    (gnSv_above (by omega)) (o := 24) (by omega) (by omega) ((ho1.word cx.abv (by omega)).trans hX.w24)
    (by bsimp [q21]) (by bsimp []) fun R2 M2 H2 F2 L2 C2 hk2 fr2 h2 _ ho2 hkp2 => ?_
  have hS2 : HeapOwn S := fun a e1 e2 => h2.heap.heap.own a e1 e2
  have q22 := fr2.r2
  bsimp []
  bc_run hlive hS2 [q22] at 0x800048c0
  refine cf_free hlive cx (fr2.regs (by keeps_tac Keeps.refl _ _)) (h2.perm (List.Perm.swap _ _ _))
    (gnSv_above (by omega)) (o := 8) (by omega) (by omega)
    ((ho2.word cx.abv (by omega)).trans ((ho1.word cx.abv (by omega)).trans hX.w8))
    (by bsimp [q22]) (by bsimp []) fun R3 M3 H3 F3 L3 C3 hk3 fr3 h3 _ ho3 hkp3 => ?_
  have hS3 : HeapOwn S := fun a e1 e2 => h3.heap.heap.own a e1 e2
  have q23 := fr3.r2
  have kk : Keeps cClob R3 R :=
    (hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac
      ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))))
  have r19 : R3 19 = BitVec.ofNat 64 ra := (kk.get 19).trans hX.regs.r19
  have r8 : R3 8 = chW (rdW o j0)[jE]? := (kk.get 8).trans hX.rd.ch
  have l16 : ldv .ld M3 (sp - 144 + 16) = BitVec.ofNat 64 pr :=
    (ho3.word cx.abv (by omega)).trans ((ho2.word cx.abv (by omega)).trans
      ((ho1.word cx.abv (by omega)).trans hX.w16))
  have hsv3 := fr3.saved
  have p3 : ldv .ld M3 inPtrAddr = BitVec.ofNat 64 (o.tb.pay + j0 + min (jE + 1) (rdW o j0).length) :=
    (ho3.inP hcab).trans ((ho2.inP hcab).trans ((ho1.inP hcab).trans hX.rd.ptr))
  have dr3 : (GV.num pr).Den ⟨L3, G.strs⟩ (.num n) :=
    hkp3 _ (by simp) _ (hkp2 _ (by simp) _ (hkp1 _ (by simp) _ hX.dr))
  have hsub : ∀ g ∈ hs0, ∀ l : List GV, g ∈ l ++ hs0 := fun g hg l => List.mem_append_right _ hg
  have keep3 : HsKeep ⟨L0, G.strs⟩ ⟨L3, G.strs⟩ hs0 :=
    hX.keep.trans (((hkp1.mono fun g hg => hsub g hg [_, _, _]).trans
      (hkp2.mono fun g hg => hsub g hg [_, _])).trans (hkp3.mono fun g hg => hsub g hg [_]))
  have l16 : ldv .ld M3 (sp - 144 + 16) = BitVec.ofNat 64 pr :=
    (ho3.word cx.abv (by omega)).trans ((ho2.word cx.abv (by omega)).trans
      ((ho1.word cx.abv (by omega)).trans hX.w16))
  bsimp []
  bc_run hlive hS3 [q23, r19] at 0x80002860
  · intro e0
    have er : ra = 0 := by
      rcases hra with e | hr
      · exact e
      · have := hr.hi
        have := congrArg BitVec.toNat e0
        simp only [BitVec.toNat_ofNat] at this; omega
    exact gn_tail hlive cx hra h02 hal0 fr3 h3 hsv3 l16 p3 (fun hr0 => absurd er hr0)
      (fun a ho hg hf hp _ => fr3.out a ho hg hf hp) dr3 keep3 hk
  · intro e0
    have hr : RaOK S sp ra := by
      rcases hra with rfl | hr
      · exact absurd rfl e0
      · exact hr
    have hro := hr.own; have hral := hr.al; have hrlo := hr.lo; have hrhi := hr.hi
    bc_run hlive hS3 [q23, r19, r8] at 0x80002860
    · exact fun b hb => by have := of_mem_accAddrs hb; exact hro b (by omega) (by omega)
    have hmo : MemOnly (fun a => ra ≤ a ∧ a < ra + 4) (writeLog M3 [(ra, 4, chW (rdW o j0)[jE]?)]) M3 :=
      fun a ha => imgM_store_miss _ _ (by omega)
    refine gn_tail hlive cx hra h02 hal0 fr3 (h3.outWrite hmo fun a ha =>
        (above_sp (sp := sp) (by simp only [heapEnd]; omega) (Nat.le_trans hrlo ha.1)).imp_right And.left)
      (fun q hq => by
        have := gnSv_below q hq
        rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega)]; exact hsv3 q hq)
      (by rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega)]; exact l16)
      (by rw [ldv_store_miss _ _ _ (by simp only [widthOfM, inPtrAddr]; omega)]; exact p3)
      (fun _ => imgLE_store4_hit _ _ _) (fun a ho hg hf hp hra' => ?_) dr3 keep3 hk
    rw [imgM_store_miss _ _ (by simp only [RaB] at hra'; omega)]
    exact fr3.out a ho hg hf hp

end Dc.Mach
