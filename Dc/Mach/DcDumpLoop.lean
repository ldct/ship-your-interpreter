import Dc.Mach.DcDump

/-!
# `dc_dump_num`'s loops (M9)

- `dn_cell`: the cell `dc_malloc` returns, holding the digit and the old top,
  then `bc_is_zero (value)`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **A digit pushed** (`0x80002b20` to `0x80002b4c`): `dc_malloc (16)`,
`bc_num2long (digit)` stored in the cell with the old top, then
`bc_is_zero (value)`. -/
theorem dn_cell {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pd pv pb v d sp p : Nat}
    {R0 R : Nat → BitVec 64} {cells : List Blk} {ds : List Nat}
    (hm : DnMid S M0 M R0 R sp H F L C G hs st pd pv pb v d cells ds p) (hd : d < 256)
    (hsf : StackFrame S sp dnN) (hab : heapEnd + dnN ≤ sp)
    (hk : ∀ R' M' H' c, DnMid S M0 M' R0 R' sp H' F L C G hs st pd pv pb v d (c :: cells) (d :: ds)
      c.pay → R' 10 = boolWord (Dc.Num.isZero ⟨false, v, 0⟩) → DWO live S Q t 0x80002b4c#64 R' M')
    (hoom : ∀ R' M' sp', OomAt S sp dnN M0 (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80002b20#64 R M := by
  have hsf' := hsf; have hab' := hab
  have hNW : dnN = 80 + (176 + rmStack (2 ^ 30)) := rfl
  rw [hNW] at hsf' hab'
  have hsl := hsf'.lo; have hsh := hsf'.hi; have hsa := hsf'.al
  simp only [heapEnd] at hab'
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 80 := by simp only [heapEnd]; omega
  have h := hm.h
  have hi := h.heap.heap
  have hS : HeapOwn S := fun a e1 e2 => hi.own a e1 e2
  have q2 := hm.fr.r2
  obtain ⟨xd, hxd, rfl, hxdn⟩ := hm.dd.numObj
  obtain ⟨xv, hxv, rfl, hxvn⟩ := hm.dv.numObj
  bc_run hlive hS [q2] at 0x80001ea0
  refine dc_malloc_spec hlive hi (n := 16) (by decide)
    (hsf'.within (m := 80) (n := 16) (by omega) (by decide)) (by simp only [heapEnd]; omega) _
    ?a10 ?a2 ?aal (fun R1 M1 H1 c hk1 hp1 h10 => ?_) (fun R1 M1 hr2 hout => ?_)
  case a10 => bsimp []
  case a2 => bsimp [q2]
  case aal => bsimp []
  · obtain ⟨h1, hf1⟩ := h.malloc hp1 (by decide) (by simp only [heapEnd]; omega)
    have hi1 := h1.heap.heap
    have sk1 := hm.stk.malloc hi hp1 (by simp only [heapEnd]; omega)
    have hcs := hm.stk.not_mem hi hp1 (by decide)
    have hcz := hp1.size
    have hcl := live_in_heap hi1 hf1.live (a := c.pay) ⟨Nat.le_refl _, by simp only [Blk.pay, Blk.fin]; omega⟩
    have hch := live_in_heap hi1 hf1.live (a := c.pay + 15) ⟨by simp only [Blk.pay]; omega, by simp only [Blk.pay, Blk.fin]; omega⟩
    simp only [heapStart, heapEnd] at hcl hch
    have hcal : c.h % 16 = 0 := (hi1.blk (List.mem_append_right _ hf1.live)).al
    have hcp : c.pay = c.h + 16 := rfl
    have e1 : ∀ a, OutHeap a → ¬ frameIn (sp - 80) 16 a → imgM M1 a = imgM M a :=
      fun a ho hf => hp1.frame a (OutHeap.not_alloc hi ho) hf
    have f1 : ∀ o, o + 8 ≤ 80 → ldv .ld M1 (sp - 80 + o) = ldv .ld M (sp - 80 + o) := fun o ho =>
      dn_ld hab2 (frameIn (sp - 80) 16) (fun a ho' _ hn => e1 a ho' hn) fun j hj h => by
        simp only [frameIn] at h; omega
    have q1 : R1 2 = BitVec.ofNat 64 (sp - 80) := by rw [hk1.get 2 (by decide)]; bsimp [q2]
    have r81 : R1 8 = BitVec.ofNat 64 p := by rw [hk1.get 8 (by decide)]; bsimp [hm.s0]
    have g40 := (f1 40 (by omega)).trans hm.w40
    have hS1 : HeapOwn S := fun a e1 e2 => hi1.own a e1 e2
    bsimp []
    bc_run hlive hS1 [q1, r81, h10, g40] at 0x800065a0
    all_goals first | exact frame_acc hsf' (by omega) (by omega) | skip
    refine bc_num2long_spec hlive hS1 (h1.heap.nums xd hxd) (h1.den.pos xd hxd) _ ?b10 ?bal
      fun R2 hk2 h20 => ?_
    case b10 => bsimp []
    case bal => bsimp []
    rw [hxdn, Dc.BcModel.toLong_int d (by omega), ofInt_natCast64] at h20
    have q2' : R2 2 = BitVec.ofNat 64 (sp - 80) := by rw [hk2.get 2 (by decide)]; bsimp [q1]
    have r28 : R2 8 = BitVec.ofNat 64 c.pay := by rw [hk2.get 8 (by decide)]; bsimp [h10]
    have r29 : R2 9 = BitVec.ofNat 64 p := by rw [hk2.get 9 (by decide)]; bsimp [r81]
    have g24 := (f1 24 (by omega)).trans hm.w24
    bsimp []
    bc_run hlive hS1 [q2', r28, r29, h20, g24] at 0x80004a10
    all_goals first | exact frame_acc hsf' (by omega) (by omega) |
      exact acc_heap hS1 (by omega) (by omega) | (simp only [StOK, htx, Blk.pay] at hcl ⊢; omega) | skip
    generalize hM2 : writeLog (writeLog M1 [(c.pay + 8, 8, BitVec.ofNat 64 p)])
      [(c.pay, 4, BitVec.ofNat 64 d)] = M2
    have hm2 : MemOnly c.In M2 M1 := fun a ha => by
      simp only [Blk.In, Blk.pay, Blk.fin] at ha hcz
      rw [← hM2, imgM_store_miss _ _ (by simp only [Blk.pay] at hcl ⊢; omega),
        imgM_store_miss _ _ (by simp only [Blk.pay] at hcl ⊢; omega)]
    have h2 := h1.rawWrite hf1 hm2
    have hw : ldv .lw M2 c.pay = BitVec.ofNat 64 d := by
      rw [← hM2]; exact ldv_lw_hitN _ rfl (by simp only [BitVec.toNat_ofNat]; omega) (by omega)
    have hl : ldv .ld M2 (c.pay + 8) = BitVec.ofNat 64 p := by
      rw [← hM2, ldv_ld_miss _ _ (by omega), ldv_store_hit]
    have sk2 := sk1.push hi1 hf1 hcs hcz hd hm2 hw hl
    have e2' : ∀ a, OutHeap a → ¬ frameIn (sp - 80) 16 a → imgM M2 a = imgM M a := fun a ho hn => by
      rw [hm2 a fun ha => by
        have := live_in_heap hi1 hf1.live ha
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ho this; omega]
      exact e1 a ho hn
    have e2 : ∀ a, OutHeap a → ¬ DcGlob a → ¬ (sp - 80 - dnW ≤ a ∧ a < sp - 32) →
        imgM M2 a = imgM M a := fun a ho _ hn =>
      e2' a ho fun h => hn (by simp only [frameIn, dnW] at h ⊢; omega)
    have hS2 : HeapOwn S := fun a e1 e2 => h2.heap.heap.own a e1 e2
    have hnv := h2.heap.nums xv hxv
    have hz : ldv .ld M2 zeroAddr = BitVec.ofNat 64 xv.rep.p → xv.rep.num.isZero = true := fun e => by
      have hzn := h2.heap.nums C.z h2.den.mz
      have p1 := hnv.shape.pLo; have p2 := hnv.shape.pHi
      have p3 := hzn.shape.pLo; have p4 := hzn.shape.pHi
      have e' := h2.view.zw.symm.trans e
      have hp : C.z.rep.p = xv.rep.p := by
        have := congrArg BitVec.toNat e'
        simp only [BitVec.toNat_ofNat] at this
        omega
      rw [← h2.heap.eq_of_p h2.den.mz hxv hp, h2.den.zv]; rfl
    refine bc_is_zero_spec hlive hS2 hnv (h2.den.pos xv hxv)
      (fun b e1 e2 => h2.glob b (by simp only [DcGlob, dc_addrs]; omega)) hz _ ?c10 ?cal
      fun R3 hk3 h30 => ?_
    case c10 => bsimp []
    case cal => bsimp []
    rw [hxvn] at h30
    have k3 : Keeps (2 :: 8 :: 9 :: cClob) R3 R :=
      (hk3.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac
        ((hk2.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac
          ((hk1.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac Keeps.refl _ _)))))
    have w2 : ∀ o, o + 8 ≤ 80 → ldv .ld M2 (sp - 80 + o) = ldv .ld M (sp - 80 + o) := fun o ho =>
      dn_ld hab2 (frameIn (sp - 80) 16) (fun a ho _ hn => e2' a ho hn) fun j hj h => by
        simp only [frameIn] at h; omega
    bsimp []
    exact hk R3 M2 H1 c ⟨hm.fr.next hab2 e2 k3 (by rw [hk3.get 2 (by decide)]; bsimp [q2']), h2,
      hm.dv, hm.dd, hm.db, (w2 24 (by omega)).trans hm.w24, (w2 32 (by omega)).trans hm.w32,
      (w2 40 (by omega)).trans hm.w40, by rw [hk3.get 8 (by decide)]; bsimp [r28], sk2⟩ h30
  · refine hoom R1 M1 (sp - 80 - 16) ⟨by simp only [dnN, dnW]; omega, by omega, hr2,
      fun a ho hg hf _ => ?_⟩
    rw [hout a (OutHeap.not_alloc hi ho) fun h => hf (by simp only [frameIn, dnN, dnW] at h ⊢; omega)]
    exact hm.fr.out a ho hg hf

end Dc.Mach
