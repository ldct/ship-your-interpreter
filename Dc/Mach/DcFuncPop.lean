import Dc.Mach.DcFuncArm0
import Dc.Mach.DcPop
import Dc.Mach.DcTop

/-!
# Popping into `dc_func`'s frame (M10)

Most arms start `dc_pop (&datum)` or `dc_top_of_stack (&datum)` with the
datum slot at `sp + 16` of `dc_func`'s frame, then branch on the status.
`fn_pop`/`fn_top` run that prefix from the call (`JalAt`) and the branch
(`BnezAt`): the empty-stack route continues at the branch target, the
other with the popped handle `g` denoting the top `v`, in the slot.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `dc_func`'s datum slot (`sp + 16` of its frame). -/
abbrev fnSlot (sp : Nat) : Nat := sp - 192 + 16

theorem FnAt.slot {S : Nat → Prop} {sp W : Nat} {M0 M : Mem} {R0 R : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) : DatSlot S (sp - 192) (fnSlot sp) := by
  have hsf := hc.frame
  have hl := hsf.lo; have hh := hsf.hi; have ha := hsf.al; have hb := hc.big
  have htx : tohostAddr = 0x8001ad00 := rfl
  show DatSlot S (sp - 192) (sp - 192 + 16)
  exact ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩

/-- The frame after `dc_pop`/`dc_top_of_stack` into the slot. -/
theorem FnAt.popped {S : Nat → Prop} {sp W : Nat} {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W) (k : Keeps popClob R' R)
    (hout : PopOut (sp - 192) (fnSlot sp) M' M) : FnAt S sp W M0 R0 R' M' := by
  have hh := hc.room
  have hl := hc.frame.lo
  have hb := hc.big
  have hab : heapEnd ≤ sp - 192 := by simp only [heapEnd] at hh ⊢; omega
  refine { hc with
    r2 := (k.get 2 (by decide)).trans hc.r2
    ra := ?_
    keep := (k.mono (by decide)).trans hc.keep
    out := ?_ }
  · rw [← hc.ra]
    exact ldv_congr .ld fun j hj => by
      have := above_sp hab (a := sp - 192 + 184 + j) (by omega)
      exact hout _ this.1 this.2.1 (this.2.2 _) (Or.inr (by simp only [fnSlot]; omega))
  · intro a e1 e2 e3 e4
    simp only [frameIn] at e4
    exact (hout a e1 e2 (fun hf => by simp only [frameIn] at hf; omega)
      (by simp only [fnSlot]; omega)).trans (hc.out a e1 e2 e3 (by simp only [frameIn]; omega))

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t : String} {st : St} {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {G : DcG} {hs : List GV} {sp W : Nat} {R0 R : Nat → BitVec 64}

/-- **`dc_pop (&datum)`** as `fn_pop`, the popped route also given `a0 = 0`
(`DC_SUCCESS`, which `X` passes on to `dc_int2data`). -/
theorem fn_pop0 (hlive : ∀ p ∈ dcText, live p.1) {p tgt0 : Nat}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (h10 : R 10 = BitVec.ofNat 64 (fnSlot sp)) (hp : (p + 4) % 4 = 0 ∧ p + 4 < 2 ^ 64)
    (hj : JalAt live S Q p 0x8000310c) (hb : BnezAt live S Q (p + 4) tgt0)
    (hempty : st.stack = [] → ∀ R' M', FnAt S sp W M0 R0 R' M' → DcAt S M' H F L C G hs st →
      DWO live S Q t (BitVec.ofNat 64 tgt0) R' M')
    (hne : ∀ R' M' H' (G' : DcG) g v st', st = st'.push v →
      (∃ c, G = { G' with stk := (c, g) :: G'.stk }) → FnAt S sp W M0 R0 R' M' →
      DcAt S M' H' F L C G' (g :: hs) st' → g.Den ⟨L, G'.strs⟩ v → DatAt M' (fnSlot sp) g →
      R' 10 = 0#64 → DWO live S Q t (BitVec.ofNat 64 (p + 8)) R' M') :
    DWO live S Q t (BitVec.ofNat 64 p) R M := by
  refine hj t R M fun R1 k1 e1 => ?_
  have hc1 := hc.mod (k1.mono (by decide))
  refine dc_pop_spec hlive h (hc1.cf (Wc := 336) hW) (hc1.cab hW) hc1.slot R1
    (by rw [k1.get 10 (by decide)]; exact h10) hc1.r2
    (by rw [e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp.2]; exact hp.1)
    (fun R' M' H' G' g v st' est eG k2 e10 h' hd hout => ?_)
    (fun he R' M' k2 e10 h' hout => ?_)
  · rw [e1]
    have hc2 := hc1.popped hW k2 hout
    have hv : g.Den ⟨L, G'.strs⟩ v := by
      obtain ⟨c, rfl⟩ := eG
      have hden := h.den.stk
      subst est
      cases hden with | cons hh _ => exact hh
    refine hb t R' M' (fun hne' => absurd e10 hne') fun _ => ?_
    exact hne R' M' H' G' g v st' est eG hc2 h' hv hd e10
  · rw [e1]
    exact hb t R' M' (fun _ => hempty he R' M' (hc1.popped hW k2 hout) h')
      fun e => absurd (e10.symm.trans e) (by decide)

/-- **`dc_pop (&datum)`**: `fn_pop0` without the status word. -/
theorem fn_pop (hlive : ∀ p ∈ dcText, live p.1) {p tgt0 : Nat}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (h10 : R 10 = BitVec.ofNat 64 (fnSlot sp)) (hp : (p + 4) % 4 = 0 ∧ p + 4 < 2 ^ 64)
    (hj : JalAt live S Q p 0x8000310c) (hb : BnezAt live S Q (p + 4) tgt0)
    (hempty : st.stack = [] → ∀ R' M', FnAt S sp W M0 R0 R' M' → DcAt S M' H F L C G hs st →
      DWO live S Q t (BitVec.ofNat 64 tgt0) R' M')
    (hne : ∀ R' M' H' (G' : DcG) g v st', st = st'.push v →
      (∃ c, G = { G' with stk := (c, g) :: G'.stk }) → FnAt S sp W M0 R0 R' M' →
      DcAt S M' H' F L C G' (g :: hs) st' → g.Den ⟨L, G'.strs⟩ v → DatAt M' (fnSlot sp) g →
      DWO live S Q t (BitVec.ofNat 64 (p + 8)) R' M') :
    DWO live S Q t (BitVec.ofNat 64 p) R M :=
  fn_pop0 hlive h hc hW h10 hp hj hb hempty
    fun R' M' H' G' g v st' est eG hc' h' hv hd _ => hne R' M' H' G' g v st' est eG hc' h' hv hd

/-- **`dc_top_of_stack (&datum)`** from its call at `p`, the status tested
at `p + 4` (`bnez a0, tgt0`). -/
theorem fn_top (hlive : ∀ p ∈ dcText, live p.1) {p tgt0 : Nat}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (h10 : R 10 = BitVec.ofNat 64 (fnSlot sp)) (hp : (p + 4) % 4 = 0 ∧ p + 4 < 2 ^ 64)
    (hj : JalAt live S Q p 0x80002e8c) (hb : BnezAt live S Q (p + 4) tgt0)
    (hempty : st.stack = [] → ∀ R' M', FnAt S sp W M0 R0 R' M' → DcAt S M' H F L C G hs st →
      DWO live S Q t (BitVec.ofNat 64 tgt0) R' M')
    (hne : ∀ R' M' c g v rest, G.stk = (c, g) :: rest → st.stack.head? = some v →
      FnAt S sp W M0 R0 R' M' → DcAt S M' H F L C G hs st → g.Den ⟨L, G.strs⟩ v →
      DatAt M' (fnSlot sp) g → DWO live S Q t (BitVec.ofNat 64 (p + 8)) R' M') :
    DWO live S Q t (BitVec.ofNat 64 p) R M := by
  refine hj t R M fun R1 k1 e1 => ?_
  have hc1 := hc.mod (k1.mono (by decide))
  refine dc_top_spec hlive h (hc1.cf (Wc := 336) hW) (hc1.cab hW) hc1.slot R1
    (by rw [k1.get 10 (by decide)]; exact h10) hc1.r2
    (by rw [e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp.2]; exact hp.1)
    (fun R' M' c g rest hst k2 e10 h' hd hout => ?_)
    (fun he R' M' k2 e10 h' hout => ?_)
  · rw [e1]
    have hc2 := hc1.popped hW k2 hout
    have hden := h.den.stk
    rw [hst] at hden
    obtain ⟨v, rest', hsv, hv⟩ : ∃ v rest', st.stack = v :: rest' ∧ g.Den ⟨L, G.strs⟩ v := by
      revert hden; generalize st.stack = l; intro hden
      cases hden with | cons hh _ => exact ⟨_, _, rfl, hh⟩
    refine hb t R' M' (fun hne' => absurd e10 hne') fun _ => ?_
    exact hne R' M' c g v rest hst (by rw [hsv]; rfl) hc2 h' hv hd
  · rw [e1]
    exact hb t R' M' (fun _ => hempty he R' M' (hc1.popped hW k2 hout) h')
      fun e => absurd (e10.symm.trans e) (by decide)

end

end Dc.Mach
