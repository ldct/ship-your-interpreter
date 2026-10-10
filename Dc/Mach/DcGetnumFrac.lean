import Dc.Mach.DcGetnumExit
import Dc.Mach.DcDivrem

/-!
# `dc_getnum`: the sign and the fraction's entry and exit (M9)

- `cf_sd`: a frame slot stored by the function itself; `cf_copy`:
  `bc_copy_num` from a dc function's frame.
- `gn_sign`: `result = _zero_ - result` (`0x800029ac`).
- `gn_fentry`: from `.` (`0x800028e0`): `build`, `temp` freed, `divisor =
  _one_`, `build = _zero_`, into the fraction loop.
- `gn_fexit`: `build = build / divisor` at scale `k`, `result += build`;
  `divisor`'s reference is lost (`DcG.lk`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **A slot of the frame stored by the function itself** (`sd`, below the
saved words): the frame kept, the state kept, the slot's word. -/
theorem cf_sd {S : Nat → Prop} {P : Nat → Prop} {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem}
    {R0 R : Nat → BitVec 64} {sp o : Nat} {v : BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (cx : CfCtx S fs sp) (hfr : CFr P fs sv M0 M R0 R sp) (h : DcAt S M H F L C G hs st)
    (hsv : ∀ q ∈ sv, o + 8 ≤ q.1) (ho : o + 8 ≤ fs) :
    CFr P fs sv M0 (writeLog M [(sp - fs + o, 8, v)]) R0 R sp ∧
      DcAt S (writeLog M [(sp - fs + o, 8, v)]) H F L C G hs st ∧
      ldv .ld (writeLog M [(sp - fs + o, 8, v)]) (sp - fs + o) = v ∧
      CfOut M (writeLog M [(sp - fs + o, 8, v)]) sp fs o := by
  have hab := cx.abv
  have hab' := cx.ab
  have hO : CfOut M (writeLog M [(sp - fs + o, 8, v)]) sp fs o := fun a _ _ _ hs' =>
    imgM_store_miss _ _ (by simp only [slotBytes, widthOfM] at hs'; omega)
  refine ⟨hfr.next hab (by omega) hsv ho hO (Keeps.refl _ _), h.outWrite (P := slotBytes (sp - fs + o))
    (fun a ha => imgM_store_miss _ _ (by simp only [slotBytes, widthOfM] at ha; omega))
    (fun a ha => ?_), ldv_store_hit _ _ _, hO⟩
  have := above_sp (sp := sp - fs) hab (a := a) (by simp only [slotBytes] at ha; omega)
  exact ⟨this.1, this.2.1⟩

/-- **`bc_copy_num (x)`** from a dc function's frame: one more reference,
the frame kept. -/
theorem cf_copy {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {P : Nat → Prop} {fs : Nat} {sv : List (Nat × Nat)}
    {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV}
    {st : St} {sp : Nat} {R0 R : Nat → BitVec 64} {x : NumObj}
    (hfr : CFr P fs sv M0 M R0 R sp) (hab : heapEnd ≤ sp - fs) (h : DcAt S M H F L C G hs st)
    (hhs : hs.length ≤ 2 ^ 30)
    (hx : x ∈ L) (h10 : R 10 = BitVec.ofNat 64 x.rep.p) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' L' C', Keeps [15] R' R → CFr P fs sv M0 M' R0 R' sp →
      DcAt S M' H F L' C' G (.num x.rep.p :: hs) st → C'.z.rep.p = C.z.rep.p →
      (GV.num x.rep.p).Den ⟨L', G.strs⟩ (.num x.rep.num) → HsKeep ⟨L, G.strs⟩ ⟨L', G.strs⟩ hs →
      (∀ a, OutHeap a → imgM M' a = imgM M a) → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x800049ac#64 R M :=
  dc_copy_spec hlive h hhs hx R h10 hal fun R' M' L' C' k h' hd hkp hout => by
    have k' : Keeps cClob R' R := k.mono (by decide)
    have hO : ∀ a, OutHeap a → ¬ DcGlob a → imgM M' a = imgM M a := fun a ho _ => hout a ho
    refine hk R' M' L' C' k { hfr.regs k' with
        saved := fun q hq => (ldv_congr .ld fun j _ => hout _ (outHeap_of_ge (by omega))).trans
          (hfr.saved q hq)
        out := fun a ho hg hf hp => (hout a ho).trans (hfr.out a ho hg hf hp) } h'
      (h.zeroP_eq h' (ldv_congr .ld fun j hj => hout _ (by
        simp only [widthOfM] at hj
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, zeroAddr]; omega))) hd hkp hout

/-- **The sign** (`0x800029ac`): `result = _zero_ - result`. -/
theorem gn_sign {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (cx : CfCtx S 144 sp) (hoom : GnOom live S Q t M0 sp)
    {R : Nat → BitVec 64} {M : Mem} {jE : Nat} {n : Num} {og : Option Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {pr pd pb : Nat}
    (hX : GnX S M0 R0 sp G hs0 st o j0 ra s6 L0 R M jE n og H F L C pr pd pb)
    (hk : ∀ R' M' H' F' L' C' pr',
      GnX S M0 R0 sp G hs0 st o j0 ra s6 L0 R' M' jE (Num.sub (Num.zero 0) n 0) og H' F' L' C' pr' pd pb →
      DWO live S Q t 0x80002840#64 R' M') :
    DWO live S Q t 0x800029ac#64 R M := by
  have hab := cx.abv
  have hab' := cx.ab
  have hsf := cx.sf
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab hab'
  have hcab : heapEnd + cfW ≤ sp - 144 := by simp only [heapEnd]; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h := hX.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have q2 := hX.fr.r2
  have r20 : R 20 = 0x8001cdc8#64 := hX.regs.r20
  have zw : ldv .ld M 0x8001cdc8 = BitVec.ofNat 64 C.z.rep.p := h.view.zw
  have w16 := hX.w16
  have hG : ∀ a, DcGlob a → S a := h.glob
  bc_run hlive hS [q2, r20, zw, w16] at 0x80004ac4
  case hLDS =>
    intro b hb; have := of_mem_accAddrs hb; exact hG b (by simp only [DcGlob, dc_addrs]; omega)
  case hk.hLDS => exact frame_acc hsf (by omega) (by omega)
  refine cf_sub hlive cx (hX.fr.regs (by keeps_tac Keeps.refl _ _)) h (gnSv_above (by omega)) (o := 16)
    (by omega) (by omega) w16 ⟨C.z, h.den.mz, rfl, h.den.zv⟩ hX.dr (smin := 0) (by decide)
    (by bsimp []) (by bsimp []) (by bsimp [q2]) (by bsimp [] <;> rfl) (by bsimp [])
    (fun R1 M1 H1 F1 L1 C1 y hk1 fr1 h1 hn1 hw1 ho1 hkp1 => ?_) hoom
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS1 [] at 0x80002840
  have kk : Keeps cClob R1 R := (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  have hsub : ∀ g ∈ slotHs og ++ hs0, ∀ l : List GV, g ∈ l ++ (slotHs og ++ hs0) :=
    fun g hg l => List.mem_append_right _ hg
  exact hk R1 M1 H1 F1 (y :: L1) C1 y.rep.p
    { fr := fr1
      h := h1
      w16 := hw1
      w24 := (ho1.word cx.abv (by omega)).trans hX.w24
      w32 := (ho1.word cx.abv (by omega)).trans hX.w32
      w8 := (ho1.word cx.abv (by omega)).trans hX.w8
      dr := ⟨y, List.mem_cons_self, rfl, hn1⟩
      keep := hX.keep.trans (hkp1.mono fun g hg => by simp [hg])
      regs := hX.regs.keep kk
      rd := ⟨hX.rd.le, (kk.get 8).trans hX.rd.ch, (ho1.inP hcab).trans hX.rd.ptr⟩ }

/-- The fraction's value: `u / ib ^ k` at scale `k`. -/
def fracQ (ib u k : Nat) : Num := ⟨false, u * 10 ^ k / ib ^ k, k⟩

theorem num_div_frac {ib : Nat} (hib : 0 < ib) (u k : Nat) :
    Num.div ⟨false, u, 0⟩ ⟨false, ib ^ k, 0⟩ k = some (fracQ ib u k) := by
  have : ib ^ k ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos hib)
  simp only [Num.div, fracQ, beq_iff_eq, this, ↓reduceIte, Nat.zero_add, Nat.pow_zero, Nat.mul_one,
    bne_self_eq_false, Option.some.injEq, Num.mk.injEq, and_true]
  split <;> rfl

/-- **The fraction's exit** (`0x80002980`): `build = build / divisor` at
scale `k`, `result += build`; `divisor`'s reference is lost. -/
theorem gn_fexit {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (cx : CfCtx S 144 sp) (hoom : GnOom live S Q t M0 sp)
    (hl : G.lk.length < 2 ^ 29)
    {R : Nat → BitVec 64} {M : Mem} {jE k vI u : Nat} {og : Option Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {pr pd pv pb : Nat}
    (hF : GnF S M0 R0 sp G hs0 st ra s6 L0 R M k vI u og H F L C pr pd pv pb) (hrd : GnRd M R o j0 jE)
    (hsz : (⟨false, u, 0⟩ : Num).wid + k + (⟨false, st.ibase ^ k, 0⟩ : Num).wid < 2 ^ 27)
    (hk : ∀ R' M' H' F' L' C' pr' pd',
      GnX S M0 R0 sp { G with lk := pv :: G.lk } hs0 st o j0 ra s6 L0 R' M' jE
        (Num.add ⟨false, vI, 0⟩ (fracQ st.ibase u k) 0) og H' F' L' C' pr' pd' pb →
      DWO live S Q t 0x800029a8#64 R' M') :
    DWO live S Q t 0x80002980#64 R M := by
  have hab := cx.abv
  have hab' := cx.ab
  have hsf := cx.sf
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab hab'
  have hcab : heapEnd + cfW ≤ sp - 144 := by simp only [heapEnd]; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h := hF.h
  have hib := h.den.ibase
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have q2 := hF.fr.r2
  have r9 := hF.r9
  have l40 := hF.w40
  have l24 := hF.w24
  bc_run hlive hS [q2, r9, l40, l24] at 0x8000589c
  any_goals (exact frame_acc hsf (by omega) (by omega))
  refine cf_div hlive cx (hF.fr.regs (by keeps_tac Keeps.refl _ _)) (h.perm (List.Perm.swap _ _ _))
    (gnSv_above (by omega)) (o := 24) (by omega) (by omega) l24 hF.dd hF.dv
    (num_div_frac (by omega) u k) hsz (fun e => hF.z0 (by
      simp only at e
      rcases Nat.pow_eq_one.mp e with e1 | e1
      · omega
      · exact e1))
    (by bsimp []) (by bsimp []) (by bsimp [q2]) (by bsimp []) (by bsimp [])
    (fun R1 M1 H1 F1 L1 C1 y hk1 fr1 h1 hn1 hw1 ho1 hkp1 => ?_) hoom
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  have q21 := fr1.r2
  have l16 : ldv .ld M1 (sp - 144 + 16) = BitVec.ofNat 64 pr := (ho1.word cx.abv (by omega)).trans hF.w16
  bsimp []
  bc_run hlive hS1 [q21, hw1, l16] at 0x80005634
  any_goals (exact frame_acc hsf (by omega) (by omega))
  refine cf_add hlive cx (fr1.regs (by keeps_tac Keeps.refl _ _)) (h1.perm (List.Perm.swap _ _ _))
    (gnSv_above (by omega)) (o := 16) (by omega) (by omega) l16 (hkp1 _ (by simp) _ hF.dr)
    ⟨y, List.mem_cons_self, rfl, hn1⟩ (smin := 0) (by decide)
    (by bsimp []) (by bsimp []) (by bsimp [q21]) (by bsimp [] <;> rfl) (by bsimp [])
    (fun R2 M2 H2 F2 L2 C2 y2 hk2 fr2 h2 hn2 hw2 ho2 hkp2 => ?_) hoom
  have kk : Keeps cClob R2 R :=
    (hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  have hsub : ∀ g ∈ hs0, ∀ l : List GV, g ∈ l ++ hs0 := fun g hg l => List.mem_append_right _ hg
  have hsub' : ∀ g ∈ hs0, ∀ l : List GV, g ∈ l ++ (slotHs og ++ hs0) := fun g hg l =>
    List.mem_append_right _ (List.mem_append_right _ hg)
  bsimp []
  exact hk R2 M2 H2 F2 (y2 :: L2) C2 y2.rep.p y.rep.p
    { fr := fr2
      h := (h2.perm (List.perm_middle (l₁ := [_, _]))).leak hl
      w16 := hw2
      w24 := (ho2.word cx.abv (by omega)).trans hw1
      w32 := (ho2.word cx.abv (by omega)).trans ((ho1.word cx.abv (by omega)).trans hF.w32)
      w8 := (ho2.word cx.abv (by omega)).trans ((ho1.word cx.abv (by omega)).trans hF.w8)
      dr := ⟨y2, List.mem_cons_self, rfl, hn2⟩
      keep := hF.keep.trans ((hkp1.mono fun g hg => hsub' g hg [_, _, _]).trans
        (hkp2.mono fun g hg => hsub' g hg [_, _, _]))
      regs := hF.regs.keep kk
      rd := ⟨hrd.le, (kk.get 8).trans hrd.ch, (ho2.inP hcab).trans ((ho1.inP hcab).trans hrd.ptr)⟩ }

/-- **The fraction's entry** (`0x800028e0`, after `.`): `build`, `temp`
freed, `divisor = _one_`, `build = _zero_`, `s1 = 0`. -/
theorem gn_fentry {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (gx : GnCtx S M0 sp G o j0) (hhs : hs0.length + 6 ≤ 2 ^ 20)
    {R : Nat → BitVec 64} {M : Mem} {j v : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {pr pt pd pb : Nat}
    (hI : GnI S M0 R0 sp G hs0 st o j0 ra s6 L0 R M j v H F L C pr pt pd pb)
    (hk : ∀ R' M' H' F' L' C' pd' pv',
      GnF S M0 R0 sp G hs0 st ra s6 L0 R' M' 0 v 0 none H' F' L' C' pr pd' pv' pb →
      R' 8 = R 8 → ldv .ld M' inPtrAddr = ldv .ld M inPtrAddr →
      DWO live S Q t 0x80002968#64 R' M') :
    DWO live S Q t 0x800028e0#64 R M := by
  have cx := gx.cx
  have hab := cx.abv
  have hab' := cx.ab
  have hsf := cx.sf
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab hab'
  have hcab : heapEnd + cfW ≤ sp - 144 := by simp only [heapEnd]; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h := hI.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have q2 := hI.fr.r2
  bc_run hlive hS [q2] at 0x800048c0
  refine cf_free hlive cx (hI.fr.regs (by keeps_tac Keeps.refl _ _)) (h.perm (perm_rev3 _ _ _ _))
    (gnSv_above (by omega)) (o := 24) (by omega) (by omega) hI.w24 (by bsimp [q2]) (by bsimp [])
    fun R1 M1 H1 F1 L1 C1 hk1 fr1 h1 _ ho1 hkp1 => ?_
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  have q21 := fr1.r2
  bsimp []
  bc_run hlive hS1 [q21] at 0x800048c0
  refine cf_free hlive cx (fr1.regs (by keeps_tac Keeps.refl _ _)) h1
    (gnSv_above (by omega)) (o := 32) (by omega) (by omega) ((ho1.word cx.abv (by omega)).trans hI.w32)
    (by bsimp [q21]) (by bsimp []) fun R2 M2 H2 F2 L2 C2 hk2 fr2 h2 z2 ho2 hkp2 => ?_
  have hS2 : HeapOwn S := fun a e1 e2 => h2.heap.heap.own a e1 e2
  have q22 := fr2.r2
  have hG : ∀ a, DcGlob a → S a := h2.glob
  have ow : ldv .ld M2 0x8001cdc0 = BitVec.ofNat 64 C2.o.rep.p := h2.view.ow
  bsimp []
  bc_run hlive hS2 [q22, ow] at 0x800049ac
  refine cf_copy hlive (fr2.sregs ((by keeps_tac Keeps.refl _ _ : Keeps [9, 21, 10, 1] _ R2).mono (by decide))
      (by bsimp [])) cx.abv h2 (by simp only [List.length_cons]; omega) h2.den.mo (by bsimp [])
    (by bsimp []) fun R3 M3 L3 C3 k3 fr3 h3 ez3 hd3 hkp3 hout3 => ?_
  have e10 : R3 10 = BitVec.ofNat 64 C2.o.rep.p := by rw [k3.get 10]; bsimp []
  have q23 : R3 2 = BitVec.ofNat 64 (sp - 144) := by rw [k3.get 2]; bsimp [q22]
  have hS3 : HeapOwn S := fun a e1 e2 => h3.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS3 [q23, e10] at 0x80002908
  case hk.hS => exact frame_acc hsf (by omega) (by omega)
  obtain ⟨fr4, h4, w4, ho4⟩ := cf_sd (v := BitVec.ofNat 64 C2.o.rep.p) (o := 40) cx fr3 h3 (gnSv_above (by omega))
    (by omega)
  generalize writeLog M3 [(sp - 144 + 40, 8, BitVec.ofNat 64 C2.o.rep.p)] = M4 at fr4 h4 w4 ho4 ⊢
  have kk3 : Keeps (9 :: 21 :: cClob) R3 R :=
    (k3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac
      ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))))
  have r20 : R3 20 = 0x8001cdc8#64 := (kk3.get 20).trans hI.regs.r20
  have zw : ldv .ld M4 0x8001cdc8 = BitVec.ofNat 64 C3.z.rep.p := h4.view.zw
  have hS4 : HeapOwn S := fun a e1 e2 => h4.heap.heap.own a e1 e2
  have hG4 : ∀ a, DcGlob a → S a := h4.glob
  bc_run hlive hS4 [q23, r20, zw] at 0x800049ac
  case hk.hk.hLDS =>
    intro b hb; have := of_mem_accAddrs hb; exact hG4 b (by simp only [DcGlob, dc_addrs]; omega)
  refine cf_copy hlive (fr4.sregs ((by keeps_tac Keeps.refl _ _ : Keeps [23, 10, 1] _ R3).mono (by decide))
      (by bsimp [])) cx.abv h4 (by simp only [List.length_cons]; omega) h4.den.mz (by bsimp [])
    (by bsimp []) fun R5 M5 L5 C5 k5 fr5 h5 ez5 hd5 hkp5 hout5 => ?_
  have e10' : R5 10 = BitVec.ofNat 64 C3.z.rep.p := by rw [k5.get 10]; bsimp []
  have q25 : R5 2 = BitVec.ofNat 64 (sp - 144) := by rw [k5.get 2]; bsimp [q23]
  have hS5 : HeapOwn S := fun a e1 e2 => h5.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS5 [q25, e10'] at 0x80002918
  case hk.hS => exact frame_acc hsf (by omega) (by omega)
  obtain ⟨fr6, h6, w6, ho6⟩ := cf_sd (v := BitVec.ofNat 64 C3.z.rep.p) (o := 24) cx fr5 h5 (gnSv_above (by omega))
    (by omega)
  generalize writeLog M5 [(sp - 144 + 24, 8, BitVec.ofNat 64 C3.z.rep.p)] = M6 at fr6 h6 w6 ho6 ⊢
  have hS6 : HeapOwn S := fun a e1 e2 => h6.heap.heap.own a e1 e2
  bc_run hlive hS6 [] at 0x80002968
  have kk5 : Keeps (9 :: 21 :: 23 :: cClob) R5 R :=
    (k5.mono (by decide)).trans (by keeps_tac ((kk3.mono (by decide))))
  have gO : ∀ {Ma Mb : Mem}, (∀ a, OutHeap a → imgM Mb a = imgM Ma a) → ∀ o', o' + 8 ≤ 144 →
      ldv .ld Mb (sp - 144 + o') = ldv .ld Ma (sp - 144 + o') := fun hout o' _ =>
    ldv_congr .ld fun j _ => hout _ (outHeap_of_ge (by omega))
  have gP : ∀ {Ma Mb : Mem}, (∀ a, OutHeap a → imgM Mb a = imgM Ma a) →
      ldv .ld Mb inPtrAddr = ldv .ld Ma inPtrAddr := fun hout =>
    ldv_congr .ld fun j hj => hout _ (InP.off (by simp only [InP, widthOfM] at hj ⊢; omega)).1
  have chn : ∀ o', o' + 8 ≤ 144 → (o' + 8 ≤ 24 ∨ 48 ≤ o') →
      ldv .ld M6 (sp - 144 + o') = ldv .ld M (sp - 144 + o') := fun o' h1 h2 =>
    (ho6.word cx.abv (by omega)).trans ((gO hout5 o' h1).trans ((ho4.word cx.abv (by omega)).trans
      ((gO hout3 o' h1).trans ((ho2.word cx.abv (by omega)).trans (ho1.word cx.abv (by omega))))))
  have hsub : ∀ g ∈ hs0, ∀ l : List GV, g ∈ l ++ hs0 := fun g hg l => List.mem_append_right _ hg
  have hpr : ∀ l : List GV, GV.num pr ∈ l ++ GV.num pr :: GV.num pb :: hs0 := fun l => by simp
  have hpb : ∀ l : List GV, GV.num pb ∈ l ++ GV.num pr :: GV.num pb :: hs0 := fun l => by simp
  refine hk R5 M6 H2 F2 L5 C5 C3.z.rep.p C2.o.rep.p
    { fr := fr6
      h := h6.perm (List.perm_middle (l₁ := [_, _]))
      w16 := (chn 16 (by omega) (.inl (by omega))).trans hI.w16
      w24 := w6
      w32 := (ho6.word cx.abv (by omega)).trans ((gO hout5 32 (by omega)).trans
        ((ho4.word cx.abv (by omega)).trans ((gO hout3 32 (by omega)).trans z2)))
      w40 := (ho6.word cx.abv (by omega)).trans ((gO hout5 40 (by omega)).trans w4)
      w8 := (chn 8 (by omega) (.inl (by omega))).trans hI.w8
      dr := hkp5 _ (hpr [_]) _ (hkp3 _ (hpr []) _ (hkp2 _ (hpr []) _ (hkp1 _ (hpr [_]) _ hI.dr)))
      dd := by have := h4.den.zv; rw [this] at hd5; exact hd5
      dv := hkp5 _ List.mem_cons_self _ (by
        have := h2.den.ov; rw [this] at hd3; simpa [Num.one] using hd3)
      db := hkp5 _ (hpb [_]) _ (hkp3 _ (hpb []) _ (hkp2 _ (hpb []) _ (hkp1 _ (hpb [_]) _ hI.db)))
      keep := hI.keep.trans ((((hkp1.mono fun g hg => hsub g hg [_, _, _]).trans
        (hkp2.mono fun g hg => hsub g hg [_, _])).trans (hkp3.mono fun g hg => hsub g hg [_, _])).trans
        (hkp5.mono fun g hg => hsub g hg [_, _, _]))
      regs := ⟨(kk5.get 18).trans hI.regs.r18, (kk5.get 19).trans hI.regs.r19, (kk5.get 20).trans hI.regs.r20,
        by rw [k5.get 21]; bsimp []; rw [k3.get 21]; bsimp [],
        (kk5.get 22).trans hI.regs.r22, by rw [k5.get 23]; bsimp []⟩
      r9 := by rw [k5.get 9]; bsimp []; rw [k3.get 9]; bsimp []
      z0 := fun _ => ez5.symm }
    ((kk5.get 8))
    ((ho6.inP hcab).trans ((gP hout5).trans ((ho4.inP hcab).trans ((gP hout3).trans
      ((ho2.inP hcab).trans (ho1.inP hcab))))))

end Dc.Mach
