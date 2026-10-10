import Dc.Mach.DcFuncArmR2
import Dc.Mach.DcRegSet
import Dc.Mach.DcRegPop
import Dc.Mach.DcRegGet

/-!
# `dc_func`'s register arms (M10)

`s`, `S` (with `peekc` the register) spill the register at `sp + 0`, pop a
datum (`fn_popW`, which also keeps that word) and call `dc_register_set` /
`dc_register_push`; `L` calls `dc_register_pop` and pushes the value. All
return `DC_EATONE` (`fa_eat`, `0x80000d5c`), or `DC_EOF_ERROR` at end of
input (`fa_eof`).
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

/-- `DC_EATONE` (`0x80000d5c`). -/
theorem fa_eat (hlive : ∀ p ∈ dcText, live p.1) {st' : St} {r : Res} {H' : Heap} {F' : List Blk}
    {L' : List NumObj} {C' : BcConsts} {G' : DcG} {ex : List GV}
    (h : DcAt S M H' F' L' C' G' (ex ++ hs) st') (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q al t0 st r G hs sp W M0 R0) (hf : FnOut st r 1 st') (hex : ex.length ≤ 2)
    (hlk : G'.lk.length + ex.length ≤ G.lk.length + al) (hpin : StrPin G.strs G'.strs hs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000d5c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [] at 0x80000c14
  exact (hc.mod (by keeps_tac Keeps.refl _ _)).close hlive hk hf h hex hlk hpin (by bsimp [])

/-- A word of `dc_func`'s frame below the slot through `dc_pop`'s stores. -/
theorem FnAt.popKeep {S : Nat → Prop} {sp W : Nat} {M0 M M' : Mem} {R0 R : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) {o : Nat} (ho : o + 8 ≤ 16) (hout : PopOut (sp - 192) (fnSlot sp) M' M) :
    ldv .ld M' (sp - 192 + o) = ldv .ld M (sp - 192 + o) := by
  have hh := hc.room
  have hb := hc.big
  have hab : heapEnd ≤ sp - 192 := by simp only [heapEnd] at hh ⊢; omega
  exact ldv_congr .ld fun j hj => by
    have := above_sp hab (a := sp - 192 + o + j) (by omega)
    exact hout _ this.1 this.2.1 (this.2.2 _) (.inl (by simp only [fnSlot, widthOfM] at hj ⊢; omega))

/-- **`dc_pop (&datum)`** as `fn_pop0`, the status tested by a branch `hb`
at `p + 4` (`bnez` to `tE`, or `beqz` to `tN`), the popped route also keeping
the frame words below the slot. -/
theorem fn_popW (hlive : ∀ p ∈ dcText, live p.1) {p tE tN : Nat}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (h10 : R 10 = BitVec.ofNat 64 (fnSlot sp)) (hp : (p + 4) % 4 = 0 ∧ p + 4 < 2 ^ 64)
    (hj : JalAt live S Q p 0x8000310c)
    (hb : ∀ t R M, (R 10 ≠ 0#64 → DWO live S Q t (BitVec.ofNat 64 tE) R M) →
      (R 10 = 0#64 → DWO live S Q t (BitVec.ofNat 64 tN) R M) →
      DWO live S Q t (BitVec.ofNat 64 (p + 4)) R M)
    (hempty : st.stack = [] → ∀ R' M', FnAt S sp W M0 R0 R' M' → DcAt S M' H F L C G hs st →
      DWO live S Q t (BitVec.ofNat 64 tE) R' M')
    (hne : ∀ R' M' H' (G' : DcG) g v st', st = st'.push v →
      (∃ c, G = { G' with stk := (c, g) :: G'.stk }) → FnAt S sp W M0 R0 R' M' →
      DcAt S M' H' F L C G' (g :: hs) st' → g.Den ⟨L, G'.strs⟩ v → DatAt M' (fnSlot sp) g →
      (∀ o, o + 8 ≤ 16 → ldv .ld M' (sp - 192 + o) = ldv .ld M (sp - 192 + o)) →
      DWO live S Q t (BitVec.ofNat 64 tN) R' M') :
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
    exact hne R' M' H' G' g v st' est eG hc2 h' hv hd fun o ho => hc1.popKeep ho hout
  · rw [e1]
    exact hb t R' M' (fun _ => hempty he R' M' (hc1.popped hW k2 hout) h')
      fun e => absurd (e10.symm.trans e) (by decide)

theorem regSet_out (st : St) (r : Nat) (v : Val) : (regSet st r v).out = st.out := by
  unfold regSet; split <;> rfl

theorem dcFunc_s_nil {r : Nat} (he : st.stack = []) : dcFunc 70 st 115 (some r) neg = .eatOne st := by
  obtain ⟨stk⟩ := st; simp only at he; subst he; rfl

theorem dcFunc_s_cons (st : St) (v : Val) (r : Nat) :
    dcFunc 70 (st.push v) 115 (some r) neg = .eatOne (regSet st r v) := by
  cases st; rfl

set_option hygiene false in
/-- The `jal dc_pop` / `bnez a0, DC_EATONE` pair of an arm (`q` after the branch). -/
macro "fr_pop_sites_eat " q:num : tactic =>
  `(tactic| (
    · intro t R M k
      have htx : tohostAddr = 0x8001ad00 := rfl
      bc_run hlive hlive [] at 0x8000310c
      exact k _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
    · intro t R M k1 k2
      simp only [Nat.reduceAdd] at k1 k2 ⊢
      have htx : tohostAddr = 0x8001ad00 := rfl
      bc_run hlive hlive [] at 0x80000d5c $q
      all_goals first | exact k1 | exact k2 | exact fun hn => k2 (Classical.not_not.mp hn)))

/-- `s` after the pop (`0x80000edc`): `dc_register_set (r, datum)`, then
`DC_EATONE`. -/
theorem fs_set (hlive : ∀ p ∈ dcText, live p.1) {r : Nat} (hr : r < 256) {R' : Nat → BitVec 64}
    {M' : Mem} {H' : Heap} {G' : DcG} {g : GV} {v : Val} {st' : St}
    (h' : DcAt S M' H' F L C G' (g :: hs) st') (hv : g.Den ⟨L, G'.strs⟩ v)
    (hc' : FnAt S sp W M0 R0 R' M') (hW : 192 + 336 ≤ W) (ho : FnOom live S Q sp W M0)
    (hd : DatAt M' (fnSlot sp) g) (hw : ldv .ld M' (sp - 192) = BitVec.ofNat 64 r)
    (hk : FnK live S Q al t0 st (.eatOne (regSet st' r v)) G hs sp W M0 R0)
    (elk : G.lk = G'.lk) (estr : G.strs = G'.strs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000edc#64 R' M' := by
  fr_ctx
  have htg : ldv .ld M' (sp - 192 + 16) = ldv .ld M' (fnSlot sp) := rfl
  have hpt : ldv .ld M' (sp - 192 + 24) = BitVec.ofNat 64 g.ptr := hd.ptr
  bc_run hlive hS [e2', hw, hpt, htg] at 0x80002fd8
  all_goals try exact frame_acc hsf (by omega) (by omega)
  rw [← regSet_out st' r v]
  refine dc_register_set_spec hlive h' hv hr (hc'.cf (Wc := 80) (by omega)) (hc'.cab (by omega)) _
    (by bsimp []) ⟨by bsimp []; exact hd.tag, by bsimp []⟩ (by bsimp [e2']) (by bsimp [])
    (fun R2 M2 H2 F2 L2 C2 G2 k2 h2 hout hpin hlk => ?_)
    fun R2 M2 sp' e1 e2 e3 hout => hc'.oom ho (Wc := 80) (by omega) e1 e2 e3
      fun a a1 a2 _ a4 => hout a a1 a2 a4
  bsimp []
  bc_run hlive hlive [] at 0x80000c14
  exact ((hc'.mod (by keeps_tac Keeps.refl _ _)).callS (Wc := 80) (by omega)
    (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (by bsimp []; rw [k2.get 2 (by decide)]; bsimp []) hout).close hlive hk (.eatOne _) (ex := []) h2
    (by simp) (by simp [hlk, elk]) (by rw [estr]; exact hpin) (by bsimp [])

/-- `s` (`0x80000ec4`): pop into register `peekc` (`regSet`), `DC_EATONE`. -/
theorem fa_s (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (h11 : R 11 = chW peek) (hpk : ∀ r, peek = some r → r < 256)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 115 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000ec4#64 R M := by
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
    bc_run hlive hlive [h11, chW, chW_ne hr, e2] at 0x80000ed4
    bc_run hlive hlive [h11, e2] at 0x80000ed4
    all_goals try exact frame_acc hsf (by omega) (by omega)
    refine fn_popW (p := 0x80000ed4) (tE := 0x80000d5c) (tN := 0x80000edc) hlive
      (h.fnStore hc (a := sp - 192) (by omega) _)
      ((hc.store (a := sp - 192) (by omega) (by omega) _).mod (by keeps_tac Keeps.refl _ _)) hW
      (by bsimp []) (by decide) ?_ ?_ ?_ ?_
    fr_pop_sites_eat 0x80000edc
    · intro he R' M' hc' h'
      rw [dcFunc_s_nil he] at hk
      exact fa_eat hlive (ex := []) h' hc' hk (.eatOne _) (by simp) (by simp) (StrPin.refl _ _)
    · intro R' M' H' G' g v st' est eG hc' h' hv hd hkeep
      have hw := hkeep 0 (by omega)
      subst est
      rw [dcFunc_s_cons] at hk
      obtain ⟨c, rfl⟩ := eG
      simp only [Nat.add_zero] at hw
      exact fs_set (st' := st') (G' := G') hlive hr h' hv hc' hW ho hd (hw.trans (ldv_store_hit _ _ _)) hk rfl rfl

theorem dcFunc_S_nil {r : Nat} (he : st.stack = []) : dcFunc 70 st 83 (some r) neg = .eatOne st := by
  obtain ⟨stk⟩ := st; simp only at he; subst he; rfl

theorem dcFunc_S_cons (st : St) (v : Val) (r : Nat) :
    dcFunc 70 (st.push v) 83 (some r) neg = .eatOne (st.setReg r (⟨some v, []⟩ :: st.regs r)) := by
  cases st; rfl

/-- `S` after the pop (`0x80001020`): `dc_register_push (r, datum)`, then
`DC_EATONE`. -/
theorem fS_push (hlive : ∀ p ∈ dcText, live p.1) {r : Nat} (hr : r < 256) {R' : Nat → BitVec 64}
    {M' : Mem} {H' : Heap} {G' : DcG} {g : GV} {v : Val} {st' : St}
    (h' : DcAt S M' H' F L C G' (g :: hs) st') (hv : g.Den ⟨L, G'.strs⟩ v)
    (hc' : FnAt S sp W M0 R0 R' M') (hW : 192 + 336 ≤ W) (ho : FnOom live S Q sp W M0)
    (hd : DatAt M' (fnSlot sp) g) (hw : ldv .ld M' (sp - 192) = BitVec.ofNat 64 r)
    (hk : FnK live S Q al t0 st (.eatOne (st'.setReg r (⟨some v, []⟩ :: st'.regs r))) G hs sp W M0 R0)
    (elk : G.lk = G'.lk) (estr : G.strs = G'.strs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80001020#64 R' M' := by
  fr_ctx
  have htg : ldv .ld M' (sp - 192 + 16) = ldv .ld M' (fnSlot sp) := rfl
  have hpt : ldv .ld M' (sp - 192 + 24) = BitVec.ofNat 64 g.ptr := hd.ptr
  bc_run hlive hS [e2', hw, hpt, htg] at 0x80002e24
  all_goals try exact frame_acc hsf (by omega) (by omega)
  show DWO live S Q (t0 ++ Dc.outStr (st'.setReg r (⟨some v, []⟩ :: st'.regs r)).out) _ _ _
  refine dc_register_push_spec hlive h' hr ⟨hd.tag, hd.ptr⟩ hv (hc'.cf (Wc := 48) (by omega))
    (hc'.cab (by omega)) _ (by bsimp []) (by bsimp []) (by bsimp []; exact hd.ptr.symm) (by bsimp [e2'])
    (by bsimp []) (fun R2 M2 H2 c k2 h2 hout => ?_)
    fun R2 M2 sp' e1 e2 e3 hout => hc'.oom ho (Wc := 48) (by omega) e1 e2 e3
      fun a a1 a2 _ a4 => hout a a1 a2 a4
  bsimp []
  bc_run hlive hlive [] at 0x80000c14
  exact ((hc'.mod (by keeps_tac Keeps.refl _ _)).callS (Wc := 48) (by omega)
    (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (by bsimp []; rw [k2.get 2 (by decide)]; bsimp []) hout).close hlive hk (.eatOne _) (ex := []) h2
    (by simp) (by simp [DcG.setReg, elk]) (StrPin.of_eq (by simp [DcG.setReg, estr]) _) (by bsimp [])

/-- `S` (`0x80001008`): pop, push a new level of register `peekc`,
`DC_EATONE`. -/
theorem fa_S (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (h11 : R 11 = chW peek) (hpk : ∀ r, peek = some r → r < 256)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 83 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001008#64 R M := by
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
    bc_run hlive hlive [h11, chW, chW_ne hr, e2] at 0x80001018
    bc_run hlive hlive [h11, e2] at 0x80001018
    all_goals try exact frame_acc hsf (by omega) (by omega)
    refine fn_popW (p := 0x80001018) (tE := 0x80000d5c) (tN := 0x80001020) hlive
      (h.fnStore hc (a := sp - 192) (by omega) _)
      ((hc.store (a := sp - 192) (by omega) (by omega) _).mod (by keeps_tac Keeps.refl _ _)) hW
      (by bsimp []) (by decide) ?_ ?_ ?_ ?_
    fr_pop_sites_eat 0x80001020
    · intro he R' M' hc' h'
      rw [dcFunc_S_nil he] at hk
      exact fa_eat hlive (ex := []) h' hc' hk (.eatOne _) (by simp) (by simp) (StrPin.refl _ _)
    · intro R' M' H' G' g v st' est eG hc' h' hv hd hkeep
      have hw := hkeep 0 (by omega)
      subst est
      rw [dcFunc_S_cons] at hk
      obtain ⟨c, rfl⟩ := eG
      simp only [Nat.add_zero] at hw
      exact fS_push (st' := st') (G' := G') hlive hr h' hv hc' hW ho hd
        (hw.trans (ldv_store_hit _ _ _)) hk rfl rfl

theorem dcFunc_L_some {r : Nat} {ent : Entry} {es : List Entry} {v : Val}
    (he : st.regs r = ent :: es) (hv : ent.val = some v) :
    dcFunc 70 st 76 (some r) neg = .eatOne ((st.setReg r es).push v) := by
  obtain ⟨val, arr⟩ := ent
  simp only at hv; subst hv
  unfold dcFunc; dsimp only; rw [he]; rfl

theorem dcFunc_L_none {r : Nat} (h : ∀ ent es, st.regs r = ent :: es → ent.val = none) :
    dcFunc 70 st 76 (some r) neg = .eatOne st := by
  unfold dcFunc; dsimp only
  cases hr : st.regs r with
  | nil => rfl
  | cons e es =>
    obtain ⟨val, arr⟩ := e
    have := h _ _ hr; simp only at this; subst this; rfl

/-- **`dc_push (datum)` then `DC_EATONE`** (the slot's words loaded at `p`,
`dc_push` called at `p + 8`, `li a0, 1; j` after): the code `L` and `l`
share (`0x80000f48`). -/
theorem fL_push (hlive : ∀ p ∈ dcText, live p.1) {R' : Nat → BitVec 64}
    {M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG} {g : GV}
    {v : Val} {st' : St} {r : Res}
    (h' : DcAt S M' H' F' L' C' G' (g :: hs) st') (hv : g.Den ⟨L', G'.strs⟩ v)
    (hc' : FnAt S sp W M0 R0 R' M') (hW : 192 + 336 ≤ W) (ho : FnOom live S Q sp W M0)
    (hd : DatAt M' (fnSlot sp) g) (hr : r = .eatOne (st'.push v))
    (hk : FnK live S Q al t0 st r G hs sp W M0 R0)
    (elk : G'.lk = G.lk) (hpin : StrPin G.strs G'.strs hs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000f48#64 R' M' := by
  subst hr
  fr_ctx
  have htg : ldv .ld M' (sp - 192 + 16) = ldv .ld M' (fnSlot sp) := rfl
  have hpt : ldv .ld M' (sp - 192 + 24) = BitVec.ofNat 64 g.ptr := hd.ptr
  bc_run hlive hS [e2', hpt, htg] at 0x80002da4
  all_goals try exact frame_acc hsf (by omega) (by omega)
  show DWO live S Q (t0 ++ Dc.outStr (st'.push v).out) _ _ _
  refine dc_push_spec hlive h' hv (hc'.cf (Wc := 64) (by omega)) (hc'.cab (by omega)) _
    ⟨by bsimp []; exact hd.tag, by bsimp []⟩ (by bsimp [e2']) (by bsimp [])
    (fun R2 M2 H2 c k2 h2 hout => ?_)
    fun R2 M2 e2 hout => hc'.oom ho (Wc := 64) (by omega) (by omega) (by omega) e2
      fun a a1 a2 _ a4 => hout a a1 a2 a4
  bsimp []
  bc_run hlive hlive [] at 0x80000c14
  exact ((hc'.mod (by keeps_tac Keeps.refl _ _)).callS (Wc := 64) (by omega)
    (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (by bsimp []; rw [k2.get 2 (by decide)]; bsimp []) hout).close hlive hk (.eatOne _) (ex := []) h2
    (by simp) (by simp [elk]) hpin (by bsimp [])

/-- `L` (`0x80000f30`): `dc_register_pop (peekc, &datum)`, its value pushed,
`DC_EATONE`; an empty register or a level without value leaves the state. -/
theorem fa_L (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (h11 : R 11 = chW peek) (hpk : ∀ r, peek = some r → r < 256)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 76 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000f30#64 R M := by
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
    bc_run hlive hlive [h11, chW, chW_ne hr, e2] at 0x80003670
    bc_run hlive hlive [h11, e2] at 0x80003670
    refine dc_register_pop_spec hlive h hr (hc.cf (Wc := 336) hW) (hc.cab hW) hc.slot _
      (by bsimp []; rfl) (by bsimp []) (by bsimp [e2]) (by bsimp [])
      (fun R' M' H' F' L' C' G' g ent es v he hv k2 e10 h' hden _ hpin hlk hd hout => ?_)
      fun hn R' M' k2 e10 h' hout => ?_
    · have hc' := (hc.mod (by keeps_tac Keeps.refl _ _)).popped hW k2 hout
      bsimp []
      rw [dcFunc_L_some he hv] at hk
      bc_run hlive hlive [e10] at 0x80000f48
      exact fL_push (st' := st.setReg r es) hlive h' hden (hc'.mod (by keeps_tac Keeps.refl _ _)) hW ho
        hd rfl hk hlk (fun o ho' hh => hpin o ho' (List.mem_cons_of_mem _ hh))
    · have hc' := (hc.mod (by keeps_tac Keeps.refl _ _)).popped hW k2 hout
      bsimp []
      rw [dcFunc_L_none hn] at hk
      bc_run hlive hlive [e10] at 0x80000d5c
      exact fa_eat hlive (ex := []) h' (hc'.mod (by keeps_tac Keeps.refl _ _)) hk (.eatOne _)
        (by simp) (by simp) (StrPin.refl _ _)

/-- **Out of memory inside `dc_register_get`** (`0x80002bcc`, `j` to
`dc_memfail`): the bytes it changes are its frame's and the slot's. -/
theorem fn_getOom (hlive : ∀ p ∈ dcText, live p.1) {sp' : Nat} {R' : Nat → BitVec 64} {M M' : Mem}
    {t' : String} (hc : FnAt S sp W M0 R0 R M) (ho : FnOom live S Q sp W M0) (hW : 192 + 336 ≤ W)
    (e1 : sp - 192 - 336 ≤ sp') (e2 : sp' ≤ sp - 192) (e3 : R' 2 = BitVec.ofNat 64 sp')
    (hout : GetOut (sp - 192) (fnSlot sp) M' M) : DWO live S Q t' 0x80002bcc#64 R' M' := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [] at 0x80001e74
  have hb := hc.big
  have hl := hc.frame.lo
  exact ho t' R' M' sp' ⟨by omega, by omega, e3, fun a a1 a2 a3 a4 =>
    (hout a a1 a2 (fun hf => a3 (by simp only [frameIn] at hf ⊢; omega))
      (by simp only [frameIn, fnSlot] at a3 ⊢; omega)).trans (hc.out a a1 a2 a4 a3)⟩

theorem dcFunc_l_some {r : Nat} {v : Val} (hg : regGet st r = some v) :
    dcFunc 70 st 108 (some r) neg = .eatOne (st.push v) := by
  unfold dcFunc; dsimp only; rw [hg]; rfl

theorem dcFunc_l_none {r : Nat} (hg : regGet st r = none) :
    dcFunc 70 st 108 (some r) neg = .eatOne st := by
  unfold dcFunc; dsimp only; rw [hg]; rfl

/-- `l` (`0x80001220`): `dc_register_get (peekc, &datum)` pushed (`fL_push`),
`DC_EATONE`. -/
theorem fa_l (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length ≤ 2 ^ 30) (h11 : R 11 = chW peek)
    (hpk : ∀ r, peek = some r → r < 256)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 108 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001220#64 R M := by
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
    bc_run hlive hlive [h11, chW, chW_ne hr, e2] at 0x80002f18
    bc_run hlive hlive [h11, e2] at 0x80002f18
    refine dc_register_get_spec hlive h hhs hr (hc.cf (Wc := 336) hW) (hc.cab hW) hc.slot _
      (by bsimp []; rfl) (by bsimp []) (by bsimp [e2]) (by bsimp [])
      (fun R' M' H' F' L' C' G' g v hg k2 e10 hsn h' hden hd hout hpin => ?_)
      (fun hg R' M' k2 e10 h' hout => ?_)
      fun R' M' sp' e1 e2 e3 hout => fn_getOom hlive (hc.mod (by keeps_tac Keeps.refl _ _)) ho hW
        e1 e2 e3 hout
    · have hc' := (hc.mod (by keeps_tac Keeps.refl _ _)).popped hW k2 hout
      bsimp []
      rw [dcFunc_l_some hg] at hk
      bc_run hlive hlive [e10] at 0x80000f48
      exact fL_push hlive h' hden (hc'.mod (by keeps_tac Keeps.refl _ _)) hW ho hd rfl hk hsn.lk hpin
    · have hc' := (hc.mod (by keeps_tac Keeps.refl _ _)).popped hW k2 hout
      bsimp []
      rw [dcFunc_l_none hg] at hk
      bc_run hlive hlive [e10] at 0x80000c14
      try bc_run hlive hlive [] at 0x80000c14
      exact (hc'.mod (by keeps_tac Keeps.refl _ _)).close hlive hk (.eatOne _) (ex := []) h'
        (by simp) (by simp) (StrPin.refl _ _) (by bsimp [])

end

end Dc.Mach
