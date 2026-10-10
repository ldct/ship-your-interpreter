import Dc.Mach.DcFuncArmV4
import Dc.Mach.DcClear
import Dc.Mach.DcDup

/-!
# `dc_func`'s stack arms `c` and `d` (M10)

`c` is `dc_clear_stack ()`; `d` copies the top datum (`dc_top_of_stack`),
takes one more reference (`dc_dup`) and pushes it (`dc_push`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {M0 : Mem} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {hs : List GV} {sp W : Nat} {R0 : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- `c` (`0x80001154`): `dc_clear_stack ()`, `DC_OKAY`. -/
theorem fa_c (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {G : DcG}
    {R : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 80 ≤ W)
    (hk : FnK live S Q t0 st (dcFunc 70 st 99 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001154#64 R M := by
  have hr : dcFunc 70 st 99 peek neg = .ok { st with stack := [] } := rfl
  rw [hr] at hk
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := hc.r2
  bc_run hlive hlive [] at 0x80002cf0
  refine dc_clear_stack_spec hlive h (hc.cf (Wc := 80) (by omega)) (hc.cab (by omega)) _
    (by bsimp [e2]) (by bsimp []) fun R1 M1 H1 F1 L1 C1 G1 k1 e1 hsn h1 hout hpin => ?_
  have hc1 := hc.callS (R' := R1) (Wc := 80) (by omega)
    (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (e1.trans (by bsimp [])) hout
  bsimp []
  bc_run hlive hlive [] at 0x80000c10
  exact fa_ok (st' := { st with stack := [] }) hlive (ex := []) h1 hc1 hk (.ok _) (by simp)
    (by rw [hsn.lk]; exact Nat.le_add_right _ _) hpin

/-- `d` (`0x80001188`): the top datum pushed again with one more reference. -/
theorem fa_d (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {G : DcG}
    {R : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length ≤ 2 ^ 30)
    (hk : FnK live S Q t0 st (dcFunc 70 st 100 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001188#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := hc.r2
  bc_run hlive hlive [e2] at 0x8000118c
  refine fn_top (p := 0x8000118c) (tgt0 := 0x80000c10) hlive h (hc.mod (by keeps_tac Keeps.refl _ _))
    (by omega) (by bsimp []) (by decide) ?_ ?_ ?_ ?_
  fn_pop_sites st_8000118c st_80001190
  · intro he R1 M1 hc1 h1
    have hr : dcFunc 70 st 100 peek neg = .ok st := by
      cases st with | mk stk => simp only at he; subst he; rfl
    rw [hr] at hk
    exact fa_ok hlive (ex := []) h1 hc1 hk (.ok _) (by simp) (by simp) (StrPin.refl _ _)
  · intro R1 M1 c g v rest _ hhd hc1 h1 hv hd
    obtain ⟨tl, htl⟩ : ∃ tl, st.stack = v :: tl := by
      revert hhd; cases st.stack with
      | nil => intro e; cases e
      | cons a l => intro e; cases e; exact ⟨l, rfl⟩
    have hr : dcFunc 70 st 100 peek neg = .ok (st.push v) := by
      cases st with | mk stk => simp only at htl; subst htl; rfl
    rw [hr] at hk
    simp only [Nat.reduceAdd]
    fv_frame hc1
    have e21 := hc1.r2
    have htg := hd.tag
    have hpt := hd.ptr
    simp only [fnSlot] at htg hpt
    rw [show sp - 192 + 16 + 8 = sp - 192 + 24 by omega] at hpt
    bc_run hlive hlive [e21, hpt] at 0x800020a0
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine dc_dup_spec hlive h1 hhs hv (hc1.cf (Wc := 16) (by omega)) (hc1.cab (by omega)) _
      ⟨by bsimp []; exact htg, by bsimp []⟩ (by bsimp [e21]) (by bsimp [])
      fun R2 M2 L2 C2 G2 k2 hd2 hsn h2 hv2 hout2 hpin2 => ?_
    have hc2 := hc1.callS (R' := R2) (Wc := 16) (by omega)
      (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      ((k2.get 2 (by decide)).trans (by bsimp [])) hout2
    bsimp []
    bc_run hlive hlive [] at 0x80002da4
    refine dc_push_spec hlive h2 hv2 (hc2.cf (Wc := 64) (by omega)) (hc2.cab (by omega)) _
      ⟨by bsimp []; exact hd2.tag, by bsimp []; exact hd2.ptr⟩ (by bsimp [hc2.r2]) (by bsimp [])
      (fun R3 M3 H3 c3 k3 h3 hout3 => ?_) (fun R3 M3 e3 hout3 => ?_)
    · have hc3 := hc2.callS (R' := R3) (Wc := 64) (by omega)
        (by keeps_tac ((k3.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
        ((k3.get 2 (by decide)).trans (by bsimp [])) hout3
      bsimp []
      bc_run hlive hlive [] at 0x80000c10
      exact fa_ok (st' := st.push v) hlive (ex := []) h3 hc3 hk (.ok _) (by simp)
        (by simp only []; rw [hsn.lk]; exact Nat.le_add_right _ _) hpin2
    · exact hc2.oom ho (Wc := 64) (by omega) (by omega) (by omega) e3
        fun a e1 e2 _ e4 => hout3 a e1 e2 e4

end

end Dc.Mach
