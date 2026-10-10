import Dc.Mach.DcFuncArmV5
import Dc.Mach.DcPrintAll

/-!
# `dc_func`'s printing arms `f`, `p`, `n` (M10)

`f` is `dc_printall (dc_obase)`; `p` prints the top datum in place with a
newline (`dc_top_of_stack`, `dc_print (…, DC_WITHNL, DC_KEEP)`); `n` pops it and
prints it without one, releasing it (`dc_print (…, DC_NONL, DC_TOSS)`). The
SizeBound premises bound the printed numbers' widths; `errno`'s bytes are
owned since `out_char`'s first call clears it (`herr`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- A printing callee's out-of-memory exit (`OomAt` over `out_char`'s words). -/
theorem FnAt.oomOc {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {sp W Wc sp' : Nat} {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {t' : String}
    (hc : FnAt S sp W M0 R0 R M) (ho : FnOom live S Q sp W M0) (hW : 192 + Wc ≤ W)
    (o : OomAt S (sp - 192) Wc M ocG sp' R' M') : DWO live S Q t' 0x80001e74#64 R' M' :=
  hc.oom ho hW o.lo o.hi o.r2 fun a e1 e2 e3 e4 => o.out a e1 e2 e4 e3

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {M0 : Mem} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {hs : List GV} {sp W : Nat} {R0 : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- `f` (`0x80000eb4`): `dc_printall (dc_obase)`, `DC_OKAY`. -/
theorem fa_f {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {G : DcG}
    {R : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + (32 + prN) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0) (hhs : hs.length ≤ 2 ^ 20)
    (hw : ∀ v ∈ st.stack, ∀ n, v = .num n → n.wid < 2 ^ 20)
    (herr : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 102 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000eb4#64 R M := by
  have hr : dcFunc 70 st 102 peek neg = .ok (st.emit (paOut st.obase st.stack)) := rfl
  rw [hr] at hk
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hG := h.glob
  have hv : ldv .lw M 0x8001cd34 = BitVec.ofNat 64 st.obase := h.view.obase
  have e2 := hc.r2
  bc_run hlive hS [hv] at 0x800038a4
  refine dc_printall_spec hlive h hhs hw (hc.mulBase hmb) h.den.obase.1 h.den.obase.2 herr
    (hc.cf (Wc := 32 + prN) (by omega)) (hc.cab (by omega)) _ (by bsimp [e2]) (by bsimp [])
    (by bsimp []) (fun R1 M1 H1 F1 L1 C1 G1 k1 e1 hsn h1 hpin hout => ?_)
    (fun t' R' M' sp' o => hc.oomOc ho (Wc := 32 + prN) (by omega) o)
  have hc1 := hc.call (R' := R1) (Wc := 32 + prN) (by omega)
    (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (e1.trans (by bsimp [])) hout
  bsimp []
  bc_run hlive hlive [] at 0x80000c10
  rw [String.append_assoc, ← outStr_append]
  exact fa_ok (st' := st.emit (paOut st.obase st.stack)) hlive (ex := []) (h1.emit _) hc1 hk
    (.ok _) (by simp) (by rw [hsn.lk]; exact Nat.le_add_right _ _) hpin

/-- `p` (`0x8000115c`): the top datum printed in place with a newline. -/
theorem fa_p {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {G : DcG}
    {R : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 + prN ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0) (hhs : hs.length ≤ 2 ^ 20)
    (hw : ∀ n rest, st.stack = .num n :: rest → n.wid < 2 ^ 20)
    (herr : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 112 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x8000115c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := hc.r2
  bc_run hlive hlive [e2] at 0x80001160
  refine fn_top (p := 0x80001160) (tgt0 := 0x80000c10) hlive h (hc.mod (by keeps_tac Keeps.refl _ _))
    (by omega) (by bsimp []) (by decide) ?_ ?_ ?_ ?_
  fn_pop_sites st_80001160 st_80001164
  · intro he R1 M1 hc1 h1
    have hr : dcFunc 70 st 112 peek neg = .ok st := by
      cases st with | mk stk => simp only at he; subst he; rfl
    rw [hr] at hk
    exact fa_ok hlive (ex := []) h1 hc1 hk (.ok _) (by simp) (by simp) (StrPin.refl _ _)
  · intro R1 M1 c g v rest _ hhd hc1 h1 hv hd
    obtain ⟨tl, htl⟩ : ∃ tl, st.stack = v :: tl := by
      revert hhd; cases st.stack with
      | nil => intro e; cases e
      | cons a l => intro e; cases e; exact ⟨l, rfl⟩
    have hr : dcFunc 70 st 112 peek neg = .ok (st.emit (Dc.Val.out 70 st.obase v ++ [10])) := by
      cases st with | mk stk => simp only at htl; subst htl; rfl
    rw [hr] at hk
    simp only [Nat.reduceAdd]
    fv_frame hc1
    have e21 := hc1.r2
    have htg := hd.tag
    have hpt := hd.ptr
    simp only [fnSlot] at htg hpt
    rw [show sp - 192 + 16 + 8 = sp - 192 + 24 by omega] at hpt
    have hS : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
    have hG := h1.glob
    have hob : ldv .lw M1 0x8001cd34 = BitVec.ofNat 64 st.obase := h1.view.obase
    bc_run hlive hS [e21, hpt, hob] at 0x8000200c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine dc_print_spec hlive h1 (keep := true) (nl := true) (fun e => absurd e (by decide)) hv hhs
      (fun n e => hw n tl (e ▸ htl)) (hc1.mulBase hmb) h1.den.obase.1 h1.den.obase.2 herr
      (hc1.cf (Wc := prN) (by omega)) (hc1.cab (by omega)) _ (by bsimp [e21])
      (by bsimp []; exact htg) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
      (fun R2 M2 H2 F2 L2 C2 G2 k2 e2' hsn h2 hout hpin => ?_)
      (fun t' R' M' sp' o => hc1.oomOc ho (Wc := prN) (by omega) o)
    have hc2 := hc1.call (R' := R2) (Wc := prN) (by omega)
      (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (e2'.trans (by bsimp [])) hout
    bsimp []
    bc_run hlive hlive [] at 0x80000c10
    rw [String.append_assoc, ← outStr_append]
    exact fa_ok (st' := st.emit (Dc.Val.out 70 st.obase v ++ [10])) hlive (ex := []) (h2.emit _)
      hc2 hk (.ok _) (by simp) (by rw [hsn.lk]; exact Nat.le_add_right _ _) hpin

/-- `n` (`0x80001128`): the popped datum printed without a newline and released. -/
theorem fa_n {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {G : DcG}
    {R : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 + prN ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0) (hhs : hs.length + 1 ≤ 2 ^ 20)
    (hw : ∀ n rest, st.stack = .num n :: rest → n.wid < 2 ^ 20)
    (herr : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 110 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001128#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := hc.r2
  bc_run hlive hlive [e2] at 0x8000112c
  refine fn_pop (p := 0x8000112c) (tgt0 := 0x80000c10) hlive h (hc.mod (by keeps_tac Keeps.refl _ _))
    (by omega) (by bsimp []) (by decide) ?_ ?_ ?_ ?_
  fn_pop_sites st_8000112c st_80001130
  · intro he R1 M1 hc1 h1
    have hr : dcFunc 70 st 110 peek neg = .ok st := by
      cases st with | mk stk => simp only at he; subst he; rfl
    rw [hr] at hk
    exact fa_ok hlive (ex := []) h1 hc1 hk (.ok _) (by simp) (by simp) (StrPin.refl _ _)
  · intro R1 M1 H1 G1 g v st1 est eG hc1 h1 hv hd
    subst est
    obtain ⟨c, rfl⟩ := eG
    have hr : dcFunc 70 (st1.push v) 110 peek neg = .ok (st1.emit (Dc.Val.out 70 st1.obase v)) := rfl
    rw [hr] at hk
    simp only [Nat.reduceAdd]
    fv_frame hc1
    have e21 := hc1.r2
    have htg := hd.tag
    have hpt := hd.ptr
    simp only [fnSlot] at htg hpt
    rw [show sp - 192 + 16 + 8 = sp - 192 + 24 by omega] at hpt
    have hS : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
    have hG := h1.glob
    have hob : ldv .lw M1 0x8001cd34 = BitVec.ofNat 64 st1.obase := h1.view.obase
    bc_run hlive hS [e21, hpt, hob] at 0x8000200c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine dc_print_spec hlive h1 (keep := false) (nl := false) (fun _ => rfl) hv (by simp; omega)
      (fun n e => hw n st1.stack (by rw [e]; rfl)) (hc1.mulBase hmb) h1.den.obase.1
      h1.den.obase.2 herr (hc1.cf (Wc := prN) (by omega)) (hc1.cab (by omega)) _ (by bsimp [e21])
      (by bsimp []; exact htg) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
      (fun R2 M2 H2 F2 L2 C2 G2 k2 e2' hsn h2 hout hpin => ?_)
      (fun t' R' M' sp' o => hc1.oomOc ho (Wc := prN) (by omega) o)
    have hc2 := hc1.call (R' := R2) (Wc := prN) (by omega)
      (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (e2'.trans (by bsimp [])) hout
    bsimp []
    bc_run hlive hlive [] at 0x80000c10
    rw [nlBytes, if_neg (by decide), List.append_nil, String.append_assoc, ← outStr_append]
    exact fa_ok (st' := st1.emit (Dc.Val.out 70 st1.obase v)) hlive (ex := []) (h2.emit _)
      hc2 hk (.ok _) (by simp) (by rw [hsn.lk]; exact Nat.le_add_right _ _) hpin

end

end Dc.Mach
