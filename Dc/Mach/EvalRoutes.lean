import Dc.Mach.EvalAdv

/-!
# `evalstr`'s status routes without callees (M10)

Machine-only spans from the status dispatch to a loop test or the exit:
`DC_OKAY` (`s0 = s7`), `DC_NEGCMP` (`s0 = s7`, `next_negcmp = 1`),
`DC_EVALTOS` (`s0 = s7`, `s9 = sp + 32`, to the `DC_EVALTOS` code),
`DC_EATONE` (two characters on, or the end at `EOF`), the `DC_QUIT` test.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t : String} {R : Nat → BitVec 64} {M : Mem}

/-- `DC_OKAY` after a character with a lookahead: `s0 = s7`, `a2 = 0`, the
test at `0x800017d0`. -/
theorem rt_ok_mid (hlive : ∀ p ∈ dcText, live p.1) (h10 : R 10 = BitVec.ofNat 64 0)
    (cs : EvConsts R)
    (hk : ∀ R2, Keeps [8, 10, 12, 15] R2 R → R2 8 = R 23 → R2 12 = 0#64 →
      DWO live S Q t 0x800017d0#64 R2 M) :
    DWO live S Q t 0x80001528#64 R M :=
  evm_0 hlive h10 cs fun R1 k1 => by
    have htx : tohostAddr = 0x8001ad00 := rfl
    bc_run hlive hlive [] at 0x800017d0
    exact hk _ (by keeps_tac ((k1.mono (by decide)).trans (Keeps.refl _ _)))
      (by bsimp []; exact k1.get 23 (by decide)) (by bsimp [])

/-- `DC_NEGCMP` after a character with a lookahead: `s0 = s7`, `a2 = 1`. -/
theorem rt_neg_mid (hlive : ∀ p ∈ dcText, live p.1) (h10 : R 10 = BitVec.ofNat 64 9)
    (cs : EvConsts R)
    (hk : ∀ R2, Keeps [8, 10, 12, 15] R2 R → R2 8 = R 23 → R2 12 = 1#64 →
      DWO live S Q t 0x800015a0#64 R2 M) :
    DWO live S Q t 0x80001528#64 R M :=
  evm_9 hlive h10 cs fun R1 k1 => by
    have htx : tohostAddr = 0x8001ad00 := rfl
    bc_run hlive hlive [] at 0x800015a0
    exact hk _ (by keeps_tac ((k1.mono (by decide)).trans (Keeps.refl _ _)))
      (by bsimp []; exact k1.get 23 (by decide)) (by bsimp [])

/-- `DC_NEGCMP` after the last character: `s0 = s7`, `a2 = 1`. -/
theorem rt_neg_last (hlive : ∀ p ∈ dcText, live p.1) (h10 : R 10 = BitVec.ofNat 64 9)
    (cs : EvConsts R)
    (hk : ∀ R2, Keeps [8, 10, 12, 15] R2 R → R2 8 = R 23 → R2 12 = 1#64 →
      DWO live S Q t 0x800015a0#64 R2 M) :
    DWO live S Q t 0x80001728#64 R M :=
  evl_9 hlive h10 cs fun R1 k1 => by
    have htx : tohostAddr = 0x8001ad00 := rfl
    bc_run hlive hlive [] at 0x800015a0
    exact hk _ (by keeps_tac ((k1.mono (by decide)).trans (Keeps.refl _ _)))
      (by bsimp []; exact k1.get 23 (by decide)) (by bsimp [])

/-- `DC_EVALTOS`: `s0 = s7`, `s9 = sp + 32`, to the `DC_EVALTOS` code. -/
theorem rt_tos_mid (hlive : ∀ p ∈ dcText, live p.1) (h10 : R 10 = BitVec.ofNat 64 3)
    (cs : EvConsts R)
    (hk : ∀ R2, Keeps [8, 10, 15, 25] R2 R → R2 8 = R 23 → R2 25 = R 2 + 32#64 →
      DWO live S Q t 0x80001748#64 R2 M) :
    DWO live S Q t 0x80001528#64 R M :=
  evm_3 hlive h10 cs fun R1 k1 => by
    have htx : tohostAddr = 0x8001ad00 := rfl
    bc_run hlive hlive [] at 0x80001748
    exact hk _ (by keeps_tac ((k1.mono (by decide)).trans (Keeps.refl _ _)))
      (by bsimp []; exact k1.get 23 (by decide)) (by bsimp []; rw [k1.get 2 (by decide)])

/-- `DC_EVALTOS` after the last character. -/
theorem rt_tos_last (hlive : ∀ p ∈ dcText, live p.1) (h10 : R 10 = BitVec.ofNat 64 3)
    (cs : EvConsts R)
    (hk : ∀ R2, Keeps [8, 10, 15, 25] R2 R → R2 8 = R 23 → R2 25 = R 2 + 32#64 →
      DWO live S Q t 0x80001748#64 R2 M) :
    DWO live S Q t 0x80001728#64 R M :=
  evl_3 hlive h10 cs fun R1 k1 => by
    have htx : tohostAddr = 0x8001ad00 := rfl
    bc_run hlive hlive [] at 0x80001748
    exact hk _ (by keeps_tac ((k1.mono (by decide)).trans (Keeps.refl _ _)))
      (by bsimp []; exact k1.get 23 (by decide)) (by bsimp []; rw [k1.get 2 (by decide)])

/-- `DC_EATONE` after a character with a lookahead `p` (the word at
`sp + 28`): two characters on, `a2 = 0`, the test at `0x80001718`. -/
theorem rt_eat_mid (hlive : ∀ p ∈ dcText, live p.1) {sp p : Nat} (h10 : R 10 = BitVec.ofNat 64 1)
    (cs : EvConsts R) (h2 : R 2 = BitVec.ofNat 64 (sp - 176)) (hsf : StackFrame S sp 176)
    (hpk : ldv .lw M (sp - 176 + 28) = BitVec.ofNat 64 p) (hp : p < 256)
    (hk : ∀ R2, Keeps [8, 10, 12, 14, 15] R2 R → R2 8 = R 8 + 2#64 → R2 12 = 0#64 →
      DWO live S Q t 0x80001718#64 R2 M) :
    DWO live S Q t 0x80001528#64 R M :=
  evm_1 hlive h10 cs fun R1 k1 => by
    have htx : tohostAddr = 0x8001ad00 := rfl
    have e2 : R1 2 = BitVec.ofNat 64 (sp - 176) := (k1.get 2 (by decide)).trans h2
    have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
    bc_run hlive hlive [e2, hpk] at 0x80001718
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals first
      | (intro hc; exfalso; have := congrArg BitVec.toNat hc; simp at this; omega)
      | intro _
    bc_run hlive hlive [e2, hpk] at 0x80001718
    exact hk _ (by keeps_tac ((k1.mono (by decide)).trans (Keeps.refl _ _)))
      (by bsimp []; rw [k1.get 8 (by decide)]) (by bsimp [])

end

end Dc.Mach
