import Dc.Mach.DcGetnumSpec
import Dc.Mach.Format

/-!
# `dc_func`'s dispatch (M10)

`dc_func (c, peekc, negcmp)` (`0x80000b9c`) opens a 192-byte frame, spills
`ra`, and jumps through the table at `0x80007f5c` on `c - 9` (`c` in
`9..126`; others go to the default arm at `0x80000c30`). `dcf_disp_tac` runs
one concrete character's dispatch: the prologue, the `.rodata` table load
(`stR_80000bc8`, its word decided once), and the `jr` to the arm. The
generated lemmas `dcf_disp_<c>` (`DcFuncDisp.lean`,
`scripts/dc/gen_dcf_disp.py`) instantiate it per character.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

set_option hygiene false in
/-- The table dispatch of one character: from `dc_func`'s entry to the arm
`tgt`, the table word at `addr` being `val`. -/
macro "dcf_disp_tac " addr:num val:num tgt:num : tactic =>
  `(tactic| (
    have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
    simp only [heapEnd] at hab
    bc_run hlive hS [h2, h10, word_sub192 (x := sp) (by omega)]
    any_goals (exact frame_acc hsf (by omega) (by omega))
    gnorm
    bc_run hlive hS [] at 0x80000bc8
    dx_ro hlive
    · gnorm; decide
    · gnorm; decide +kernel
    gnorm
    rw [show ldvf .lw dcROImg $addr = BitVec.ofNat 64 $val by decide +kernel]
    dx_run hlive at $tgt
    exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp [h10])))

end Dc.Mach
