import Dc.Mach.EvalTos1

/-!
# `DC_EVALTOS`'s nested evaluation: after the call (M10)

After the nested `evalstr (s9)` returned (`0x80001804`, status in `a0`):
the string the nested activation leaves in the slot is freed
(`rt_call_free`, to `0x80001810` with the status in `a4`); then `DC_OKAY`
continues at the test `0x800017d0`, `DC_QUIT` with `unwind_depth > 0`
returns `DC_QUIT` with one level less (`0x8000185c`), with
`unwind_depth = 0` ends the activation's loop (`0x8000156c`)
(`ev_after_call`). `EvRetK`: the activation's return with a status.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t : String} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
  {st : St} {sp : Nat}

/-- After `dc_free_str` (`0x80001894`): `a4` the status saved at `sp + 8`,
on to `0x80001810`. -/
theorem rt_ld_status (hlive : ∀ p ∈ dcText, live p.1) (hown : ∀ b, sp ≤ b → b < sp + 88 → S b)
    (hlo : tohostAddr + 16 ≤ sp) (htop : sp + 176 ≤ 0x88000000) {R : Nat → BitVec 64} {w : BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp)
    (h8 : ldv .ld M (sp + 8) = w)
    (hk : ∀ R2, Keeps [14] R2 R → R2 14 = w → DWO live S Q t 0x80001810#64 R2 M) :
    DWO live S Q t 0x80001894#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h8' : BitVec.ofNat 64 sp + 8#64 = BitVec.ofNat 64 (sp + 8) := by
    rw [show (8#64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
  bc_run hlive hlive [h2, h8, h8'] at 0x80001810
  all_goals first
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | (simp only [LdOK, BitVec.toNat_ofNat]; rw [htx] at hlo ⊢; omega)
    | skip
  exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp [])

/-- **The nested activation's string freed** (`0x80001804`, the slot
`sp + 32` holding `.str p`, the status in `a0`): to `0x80001810` with the
status in `a4`. -/
theorem rt_call_free (hlive : ∀ p ∈ dcText, live p.1) {p : Nat} {hs' : List GV}
    (h : DcAt S M H F L C G (.str p :: hs') st) (hd : DatAt M (sp + 32) (.str p))
    (hown : ∀ b, sp ≤ b → b < sp + 88 → S b) (htop : sp + 176 ≤ 0x88000000)
    (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp) (h23 : R 23 = 2#64)
    (hk : ∀ R2 M2 H2 G', Keeps (1 :: 14 :: 15 :: freeStrClob) R2 R → R2 14 = R 10 →
      SameNodes G G' → DcAt S M2 H2 F L C G' hs' st → StrPin G.strs G'.strs hs' →
      (∀ a, OutHeap a → ¬ (DcGlob a ∧ ¬ PinWords a) → ¬ frameIn sp 32 a →
        ¬ (sp ≤ a ∧ a < sp + 88) → imgM M2 a = imgM M a) →
      DWO live S Q t 0x80001810#64 R2 M2) :
    DWO live S Q t 0x80001804#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab; simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hlw : ldv .lw M (sp + 32) = 2#64 := hd.lw
  have hpt := hd.ptr
  rw [show sp + 32 + 8 = sp + 40 by omega] at hpt
  have hq40 : PtrSlot S (sp + 40) := ⟨fun i hi => hown (sp + 40 + i) (by omega) (by omega), by omega,
    by simp only [tohostAddr] at hsl ⊢; omega, by omega⟩
  have h40 : BitVec.ofNat 64 sp + 40#64 = BitVec.ofNat 64 (sp + 40) := by
    rw [show (40#64) = BitVec.ofNat 64 40 from rfl, BitVec.ofNat_add_ofNat]
  bc_run hlive hS [h2, h23, hlw, h40] at 0x800039a4
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | skip
  bc_run hlive hS [h2, h23, hlw, h40] at 0x800039a4
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | skip
  generalize hM1 : writeLog M [(sp + 8, 8, R 10)] = M1
  have hm1 : MemOnly (fun a => sp + 8 ≤ a ∧ a < sp + 16) M1 M := fun a ha => by
    rw [← hM1, imgM_store_miss _ _ (by omega)]
  have hP : ∀ a, (sp + 8 ≤ a ∧ a < sp + 16) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    have := above_sp (sp := sp) (a := a) (by simp only [heapEnd]; omega) (by omega)
    ⟨this.1, this.2.1⟩
  have h1 := h.outWrite hm1 hP
  have hw : ldv .ld M1 (sp + 40) = BitVec.ofNat 64 p := by
    rw [← hM1, ldv_ld_miss _ _ (by omega)]; exact hpt
  refine dc_free_str_spec hlive h1 hq40 hw hsf hab _ ?_ ?_ ?_
    fun R1 M2 H2 G' k1 hsn h2' hso hpin => ?_
  · bsimp []
  · bsimp [h2]
  · bsimp []
  bsimp []
  have h8 : ldv .ld M2 (sp + 8) = R 10 := by
    rw [ldv_congr .ld fun j hj => hso _ (outHeap_of_ge (by simp only [heapEnd]; omega))
      (fun hg => by have := hg.1.lt; simp only [heapStart] at this; omega)
      (fun hf => by simp only [frameIn] at hf; omega), ← hM1, ldv_store_hit]
  have e2 : R1 2 = BitVec.ofNat 64 sp := by rw [k1.get 2 (by decide)]; bsimp [h2]
  refine rt_ld_status hlive hown (by simp only [tohostAddr] at hsl ⊢; omega) htop e2 h8 fun R3 k3 e14 => ?_
  refine hk R3 M2 H2 G' ?_ ?_ hsn h2' hpin ?_
  · keeps_tac ((k3.mono (by decide)).trans ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  · rw [e14]
  · exact fun a e1 e2 e3 e4 =>
      (hso a e1 e2 e3).trans (hm1 a fun h => e4 ⟨by omega, by omega⟩)

/-- **After the nested evaluation, `DC_OKAY`** (`0x80001810`, `a4 = 0`):
`a2 = 0`, the test at `0x800017d0`. -/
theorem ev_after_ok (hlive : ∀ p ∈ dcText, live p.1) {R : Nat → BitVec 64} (h14 : R 14 = 0#64)
    (hk : ∀ R2, Keeps [12, 15] R2 R → R2 12 = 0#64 → DWO live S Q t 0x800017d0#64 R2 M) :
    DWO live S Q t 0x80001810#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h14] at 0x800017d0
  all_goals first | (intro hc; exact absurd hc (by decide)) | intro _ | skip
  bc_run hlive hlive [h14] at 0x800017d0
  exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp [])

end

/-- **After the nested evaluation, `DC_QUIT`** (`0x80001810`, `a4 = 4`):
with `unwind_depth = 0` the loop's exit; else `unwind_depth - 1` stored and
the activation returns `DC_QUIT` (`0x8000185c`). -/
theorem ev_after_quit {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1) {sp W d k q : Nat} {M0 : Mem}
    {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
    {G : DcG} {hs xs : List GV} {st : St} {f : Frame} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o) (h14 : R 14 = 4#64)
    (h0 : st.unwind = 0 → ∀ R2, Keeps [15] R2 R → DWO live S Q t 0x8000156c#64 R2 M)
    (h1 : 0 < st.unwind → ∀ R2 M1, Keeps [10, 14, 15] R2 R → R2 10 = 4#64 →
      EvAt S sp W d k q M0 R0 R2 M1 H F L C G hs xs { st with unwind := st.unwind - 1 } f o →
      DWO live S Q t 0x8000185c#64 R2 M1) :
    DWO live S Q t 0x80001810#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hG := ev.dc.glob
  have hu := ev.dc.view.unwind
  have hur := ev.dc.den.unwind
  have ti : (BitVec.ofNat 64 st.unwind).toInt = st.unwind := toInt_ofNat_small (by omega)
  bc_run hlive hlive [h14] at 0x80001818
  all_goals first | (intro hc; exact absurd hc (by decide)) | intro _ | skip
  bc_run hlive hlive [hu, ti] at 0x8000156c 0x80001824
  all_goals first
    | (intro b hb; have := of_mem_accAddrs hb; exact hG b (by simp only [DcGlob, dc_addrs]; omega))
    | skip
  all_goals first | (intro hc; exfalso; omega) | intro _ | skip
  · rename_i hle
    have h00 : st.unwind = 0 := by simp at hle; omega
    exact h0 h00 _ (by keeps_tac Keeps.refl _ _)
  · rename_i hgt
    have hpos : 0 < st.unwind := by simp at hgt; omega
    bc_run hlive hlive [hu, ti] at 0x8000185c
    all_goals first
      | (intro b hb; have := of_mem_accAddrs hb; exact hG b (by simp only [DcGlob, dc_addrs]; omega))
      | skip
    generalize hM1 : writeLog M [(2147601800, 4, BitVec.ofNat 64 (st.unwind - 1))] = M1
    have hm1 : MemOnly (fun a => unwindAddr ≤ a ∧ a < unwindAddr + 4) M1 M := fun a ha => by
      rw [← hM1, imgM_store_miss _ _ (by simp only [unwindAddr] at ha; omega)]
    have hv : ldv .lw M1 unwindAddr = BitVec.ofNat 64 (st.unwind - 1) := by
      rw [← hM1]; exact ldv_lw_hitN _ rfl (by simp only [BitVec.toNat_ofNat]; omega) (by omega)
    exact h1 hpos _ M1 (by keeps_tac Keeps.refl _ _) (by bsimp [])
      ((ev.setUnwind hm1 hv (by omega)).mod (by keeps_tac Keeps.refl _ _))

end Dc.Mach
