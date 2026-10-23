import Dc.Mach.Tohost

/-!
# dc's console and exit on HTIF

`DWO live S Q t pc R Mt` is a printing dc run (`SWPO`,
`VsaIris/Vsa/SymRunO.lean`): a `DW` run whose end condition is a printing
local run from the end values with the console at `t`. Every step lemma of
the table (`Steps/*.lean`) applies to it unchanged (`DWO` unfolds to `DW`);
at a `tohost` store of a putchar word the generated `stP_<pc>`
(`Tohost.lean`) prints one byte and continues with the console advanced.

The console stores are `fputc` (`0x80000620`) and `putchar` (`0x80000650`) on
`stdout`, and the inline stores of `emit_unsigned`/`format.constprop.0`. The
exit store is `_exit`'s (`0x800005c8`): its next step halts the machine with
the code in the exit word (`dcExit_haltFact`, over `exit_haltFact`); `abort`
and `__assert_fail` store the constant exit word for code 134.
-/

namespace Dc.Mach

open Iris VsaIris VsaIris.Inst VsaIris.Sym Vsa.MemRepr

/-- A printing dc run at a symbolic state, the console at `t`. -/
abbrev DWO (live : Nat → Prop) (S : Nat → Prop)
    (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (t : String) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  SWPO live dcText dcRegs S Q t

/-- `fputc`'s console store. -/
abbrev fputcSite : TohostSite := tohost_80000620
/-- `putchar`'s console store. -/
abbrev putcharSite : TohostSite := tohost_80000650
/-- `_exit`'s store (`sd a5,1852(a4)`, `a4 = 0x8001a5c4`). -/
abbrev exitSite : TohostSite := tohost_800005c8

/-- **dc's exit.** At `_exit`'s store with the exit word for `e` in `a5`
(and `a4` its base), the machine's next step halts with code `e`, reporting
the output so far. -/
theorem dcExit_haltFact (live : Nat → Prop) (hlive : ∀ p ∈ dcText, live p.1) (e : BitVec 64)
    (he : e.toNat < 2 ^ 47) (q0 q1 q2 : DFrac) :
    HaltFact (vsaModel live)
      ((VsaIris.PC, q0, BitVec.ofNat 64 exitSite.pc) :: exitSite.regsRead q1 q2 (exitWord e))
      (codeFoot exitSite.pc exitSite.code) e.toNat :=
  exit_haltFact live exitSite tohost_800005c8_cert e he q0 q1 q2
    (fun p hp => hlive _ (tohost_800005c8_code p hp))

end Dc.Mach
