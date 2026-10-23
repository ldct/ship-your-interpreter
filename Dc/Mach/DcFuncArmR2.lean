import Dc.Mach.DcFuncArmR1
import Dc.Mach.DcCmpop
import Dc.Mach.DcFuncArmV1

/-!
# `dc_func`'s comparison arms and `R` (M10)

`<`, `=` and `>` (with `peekc` the register): end of input returns
`DC_EOF_ERROR`; otherwise `dc_cmpop ()` (`fn_cmp`, the `negcmp` flag spilled
at `sp + 0` across the call) and the ordering's test against `!negcmp`
selects `DC_EVALREG` or `DC_EATONE`. Each arm decides its test on the three
orderings and both flags. `R` pops a datum, `dc_num2int`s a number (`0`
for a string, whose handle the arm loses) and calls `dc_stack_rotate`
(`fn_rot`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

section

variable {al : Nat} {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 t : String} {st : St} {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {G : DcG} {hs : List GV} {sp W : Nat} {R0 R : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- **`dc_cmpop ()`** from `dc_func`'s frame, `negcmp` spilled at `sp + 0`:
the ordering in `a0`, the flag still in the frame. -/
theorem fn_cmp (hlive : ∀ p ∈ dcText, live p.1) {w : BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 400 ≤ W)
    (hw : ldv .ld M (sp - 192 + 0) = w) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' (G' : DcG), Keeps (1 :: 2 :: opClob) R' R → FnAt S sp W M0 R0 R' M' →
      G'.lk = G.lk → G'.strs = G.strs → R' 10 = ordWord (cmpop st).1 →
      DcAt S M' H' F' L' C' G' hs (cmpop st).2 → ldv .ld M' (sp - 192 + 0) = w →
      DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x8000345c#64 R M :=
  dc_cmpop_spec hlive h (hc.cf hW) (hc.cab hW) R hc.r2 hal
    fun R' M' H' F' L' C' G' k _ e2 elk estr e10 h' hout =>
      hk R' M' H' F' L' C' G' k (hc.callS hW (k.mono (by decide)) e2 hout) elk estr e10 h'
        ((hc.ldKeep hout).trans hw)

/-- `DC_EOF_ERROR` (`0x80001264`) for a comparison or register command at
end of input. -/
theorem fa_eof (hlive : ∀ p ∈ dcText, live p.1) {r : Res} (hr : r = .eofError)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q al t0 st r G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001264#64 R M := by
  subst hr
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [] at 0x80000c14
  exact fa_code hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hk .eofError (by bsimp [])

theorem dcFunc_lt (st : St) (r : Nat) (neg : Bool) :
    dcFunc 70 st 60 (some r) neg = if ((cmpop st).1 == .lt) == !neg then .evalReg (cmpop st).2 r
      else .eatOne (cmpop st).2 := by
  unfold dcFunc; dsimp only; rcases cmpop st with ⟨o, s'⟩; rfl

theorem dcFunc_eq (st : St) (r : Nat) (neg : Bool) :
    dcFunc 70 st 61 (some r) neg = if ((cmpop st).1 == .eq) == !neg then .evalReg (cmpop st).2 r
      else .eatOne (cmpop st).2 := by
  unfold dcFunc; dsimp only; rcases cmpop st with ⟨o, s'⟩; rfl

theorem dcFunc_gt (st : St) (r : Nat) (neg : Bool) :
    dcFunc 70 st 62 (some r) neg = if ((cmpop st).1 == .gt) == !neg then .evalReg (cmpop st).2 r
      else .eatOne (cmpop st).2 := by
  unfold dcFunc; dsimp only; rcases cmpop st with ⟨o, s'⟩; rfl

theorem cmpop_out (st : St) : (cmpop st).2.out = st.out := by
  unfold cmpop; split <;> rfl

theorem chW_ne {r : Nat} (hr : r < 256) : ¬ BitVec.ofNat 64 r = 18446744073709551615#64 := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- **A comparison arm's call** (`li a5, -1; beq a1, a5`, `sd a2, 0(sp)`,
`jal dc_cmpop` from `p`): the ordering at the return `p + 16`. -/
theorem fn_cmp_call (hlive : ∀ p ∈ dcText, live p.1) {r : Nat}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 400 ≤ W)
    (h1 : R 1 = BitVec.ofNat 64 r) (hr : r % 4 = 0 ∧ r < 2 ^ 64)
    (hk : ∀ R' M' H' F' L' C' (G' : DcG), FnAt S sp W M0 R0 R' M' →
      G'.lk = G.lk → G'.strs = G.strs → R' 10 = ordWord (cmpop st).1 →
      DcAt S M' H' F' L' C' G' hs (cmpop st).2 → ldv .ld M' (sp - 192 + 0) = R 12 →
      DWO live S Q t (BitVec.ofNat 64 r) R' M') :
    DWO live S Q t 0x8000345c#64 R (writeLog M [(sp - 192, 8, R 12)]) :=
  fn_cmp hlive (h.fnStore hc (a := sp - 192) (by omega) (R 12))
    (hc.store (a := sp - 192) (by omega) (by have := hc.frame.lo; omega) (R 12)) hW
    (by simp only [Nat.add_zero]; exact ldv_store_hit _ _ _)
    (by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr.2]; exact hr.1)
    fun R' M' H' F' L' C' G' k hc' elk estr e10 h' hw => by
      rw [h1]; exact hk R' M' H' F' L' C' G' hc' elk estr e10 h' hw

set_option hygiene false in
/-- A comparison arm (model lemma `dl`, `dc_cmpop`'s return address `ret`):
end of input, then the call and the decided test over the three orderings
and both flags. -/
macro "fr_cmp_arm " dl:ident ret:num : tactic =>
  `(tactic| (
      have htx : tohostAddr = 0x8001ad00 := rfl
      have hsl := hc.frame.lo; have hsh := hc.frame.hi; have hbig := hc.big; have hroom := hc.room
      have hsf : StackFrame S sp 192 := hc.frame.mono hc.big
      have hsa := hc.frame.al
      have e2 := hc.r2
      cases peek with
      | none =>
        bc_run hlive hlive [h11, chW] at 0x80001264
        exact fa_eof hlive rfl h (hc.mod (by keeps_tac Keeps.refl _ _)) hk
      | some r =>
        have hr := hpk r rfl
        rw [$dl:term] at hk
        rw [← cmpop_out st]
        bc_run hlive hlive [h11, chW, chW_ne hr, e2] at 0x8000345c
        bc_run hlive hlive [e2] at 0x8000345c
        all_goals try exact frame_acc hsf (by omega) (by omega)
        refine fn_cmp_call hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hW (r := $ret) (by bsimp [])
          (by decide) fun R' M' H' F' L' C' G' hc' elk estr e10 h' hw => ?_
        simp only [upd_apply, Nat.reduceEqDiff, ite_false, h12] at hw
        simp only [Nat.add_zero] at hw
        generalize cmpop st = p at hk e10 h' ⊢
        obtain ⟨o, s'⟩ := p
        cases o <;> cases neg <;> simp only [boolWord] at hw <;>
          dsimp only at hk <;> (first | rw [ite_T (by decide)] at hk | rw [ite_F (by decide)] at hk) <;>
          (bc_run hlive hlive [hw, e10, ordWord, hc'.r2] at 0x80000c14) <;>
          (try bc_run hlive hlive [] at 0x80000c14)
        all_goals try exact frame_acc hsf (by omega) (by omega)
        all_goals first
            | exact (hc'.mod (by keeps_tac Keeps.refl _ _)).close hlive hk (.evalReg _ _) (ex := []) h'
                (by simp) (by simp [elk]) (StrPin.of_eq estr _) (by bsimp [])
            | exact (hc'.mod (by keeps_tac Keeps.refl _ _)).close hlive hk (.eatOne _) (ex := []) h'
                (by simp) (by simp [elk]) (StrPin.of_eq estr _) (by bsimp [])))

/-- `>` (`0x80000d38`): `DC_EVALREG` when the top is greater (`!negcmp`), else `DC_EATONE`. -/
theorem fa_gt (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 400 ≤ W)
    (h11 : R 11 = chW peek) (h12 : R 12 = boolWord neg) (hpk : ∀ r, peek = some r → r < 256)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 62 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000d38#64 R M := by
  fr_cmp_arm dcFunc_gt 0x80000d48

/-- `=` (`0x80000d64`). -/
theorem fa_eq (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 400 ≤ W)
    (h11 : R 11 = chW peek) (h12 : R 12 = boolWord neg) (hpk : ∀ r, peek = some r → r < 256)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 61 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000d64#64 R M := by
  fr_cmp_arm dcFunc_eq 0x80000d74

/-- `<` (`0x80000d90`). -/
theorem fa_lt (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 400 ≤ W)
    (h11 : R 11 = chW peek) (h12 : R 12 = boolWord neg) (hpk : ∀ r, peek = some r → r < 256)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 60 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000d90#64 R M := by
  fr_cmp_arm dcFunc_lt 0x80000da0

theorem dcFunc_R_nil (he : st.stack = []) : dcFunc 70 st 82 peek neg = .ok st := by
  obtain ⟨stk⟩ := st; simp only at he; subst he; rfl

theorem dcFunc_R_cons (st : St) (v : Val) : dcFunc 70 (st.push v) 82 peek neg =
    .ok { st with stack := rotate (valInt 0 v) st.stack } := by
  cases st; rfl

/-- **`dc_stack_rotate (n)` then `DC_OKAY`** (`0x80001050`). -/
theorem fn_rot (hlive : ∀ p ∈ dcText, live p.1) {n : Int} (hn1 : -2147483648 ≤ n)
    (hn2 : n < 2147483648) {s : St} {G' : DcG} {ex : List GV} {H' : Heap} {F' : List Blk}
    {L' : List NumObj} {C' : BcConsts}
    (h : DcAt S M H' F' L' C' G' (ex ++ hs) s) (hc : FnAt S sp W M0 R0 R M)
    (h10 : R 10 = BitVec.ofInt 64 n)
    (hk : FnK live S Q al t0 st (.ok { s with stack := rotate n s.stack }) G hs sp W M0 R0)
    (hex : ex.length ≤ 2) (hlk : G'.lk.length + ex.length ≤ G.lk.length + al)
    (estr : G.strs = G'.strs) :
    DWO live S Q (t0 ++ Dc.outStr s.out) 0x80001050#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hg := h.stkGeo
  bc_run hlive hlive [] at 0x80003768
  refine dc_stack_rotate_spec hlive h hn1 hn2 _ (by bsimp [h10]) (by bsimp [])
    fun R1 M1 l' k1 _ hm h1 => ?_
  bsimp []
  bc_run hlive hlive [] at 0x80000c10
  have hc1 := (hc.mod (R' := R1) (by keeps_tac ((k1.mono (by decide)).trans
    (by keeps_tac Keeps.refl _ _)))).call (Wc := 0) (M' := M1) (by have := hc.big; omega)
    (Keeps.refl _ _) rfl fun a e1 e2 _ _ => hm a fun hl => StkLinks.off hg hl e1 e2
  exact fa_ok (st' := { s with stack := rotate n s.stack }) hlive h1 hc1 hk (.ok _) hex hlk
    (StrPin.of_eq estr.symm _)

theorem fR_num (hlive : ∀ p ∈ dcText, live p.1) (hW : 192 + 336 ≤ W) :
    PopNumK live S Q al t0 st (dcFunc 70 st 82 peek neg) G hs F L C sp W M0 R0 0x80001044#64 := by
  intro R' M' H' G' x st' est elk estr hx hc' h' htg hpt hk
  subst est
  rw [dcFunc_R_cons] at hk
  fr_ctx
  bc_run hlive hS [e2', htg, hpt] at 0x80002648
  all_goals try exact frame_acc hsf (by omega) (by omega)
  bc_run hlive hS [e2', htg, hpt] at 0x80002648
  all_goals try exact frame_acc hsf (by omega) (by omega)
  refine fn_n2i hlive h' hx (hc'.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by bsimp [])
    (by bsimp []) (by bsimp []) fun R2 M2 H2 F2 L2 C2 k2 hc2 e10 h2 _ => ?_
  bsimp []
  have hrg := Num.toInt_range x.rep.num
  bc_run hlive hlive [] at 0x80001050
  exact fn_rot (s := st') (n := x.rep.num.toInt.1) (ex := []) hlive (by omega) (by omega) h2 (hc2.mod (by keeps_tac Keeps.refl _ _))
    (by bsimp [e10]) hk (by simp) (by simp [elk]) estr

theorem fR_str (hlive : ∀ p ∈ dcText, live p.1) (hW : 192 + 336 ≤ W) (hal1 : 1 ≤ al) :
    PopStrK live S Q al t0 st (dcFunc 70 st 82 peek neg) G hs F L C sp W M0 R0 0x80001044#64 := by
  intro R' M' H' G' o st' est elk estr ho hc' h' htg _ e10 hk
  subst est
  rw [dcFunc_R_cons] at hk
  fr_ctx
  bc_run hlive hS [e2', htg] at 0x80001050
  all_goals try exact frame_acc hsf (by omega) (by omega)
  exact fn_rot (s := st') (n := 0) (ex := [_]) hlive (by decide) (by decide) h'
    (hc'.mod (by keeps_tac Keeps.refl _ _)) (by bsimp [e10]; rfl) hk (by simp) (by simp [elk]; omega)
    estr

/-- `R` (`0x80001038`): pop, `dc_stack_rotate` by the number (`0` for a
string). -/
theorem fa_R (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (hal1 : 1 ≤ al) (hk : FnK live S Q al t0 st (dcFunc 70 st 82 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001038#64 R M := by
  fr_pre 0x8000103c
  refine fn_pop_arm (p := 0x8000103c) hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hW (by bsimp [])
    (by decide) ?_ ?_ dcFunc_R_nil hk (fR_num hlive hW) (fR_str hlive hW hal1)
  fr_pop_sites 0x80001044

end

end Dc.Mach
