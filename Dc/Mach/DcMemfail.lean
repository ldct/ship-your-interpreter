import Dc.Mach.DcMakeString
import Dc.Mach.Stubs

/-!
# `dc_memfail` (M9)

    dc_memfail ():
      fprintf (stderr, "%s: out of memory\n", progname);
      exit (EXIT_FAILURE);

`dc_memfail_spec`: from the `progname` word and `stderr`'s descriptor, the
run reaches `_exit`'s `tohost` store with the exit word of status 1
(`dcExit_haltFact` halts the machine there). Every `dc_malloc` failure and
every `bc` out-of-memory route ends here.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `"%s: out of memory\n"`. -/
theorem memfailMsg : ProgMsg 0x80007c10 16 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

/-- `dc_memfail` from `0x80001e84` (`a0 = stderr`, `a2 = progname`): the
frame, `fprintf`, `exit(1)`. -/
theorem mf_call {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat}
    (hfd : FdAt S M stderrAddr 2) (hsf : StackFrame S sp 320) (hfar : stderrAddr + 4 ≤ sp - 320)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 stderrAddr)
    (h12 : R 12 = BitVec.ofNat 64 dcNameAddr)
    (hk : ∀ R' M', R' 15 = exitWord 1#64 → R' 14 = exitSite.base → DWO live S Q t 0x800005c8#64 R' M') :
    DWO live S Q t 0x80001e84#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, h10, h12] at 0x80000774
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine fprintf_prog_spec hlive memfailMsg (by decide) (hsf.sub (m := 16) (n := 304) (by decide))
    ?far (hfd.transport fun j hj => imgM_store_miss _ _ (by
      simp only [stderrAddr] at hfar ⊢; omega)) _ ?a ?b ?c ?d ?e fun R3 M3 hk3 _ => ?_
  case far => rw [Nat.sub_sub]; simp only [stderrAddr] at hfar ⊢; omega
  case a => bsimp []
  case b => bsimp [h10]
  case c => bsimp []
  case d => bsimp [h12]
  case e => bsimp []
  have q2 : R3 2 = BitVec.ofNat 64 (sp - 16) := by rw [hk3.get 2 (by decide)]; bsimp []
  bsimp []
  bc_run hlive hlive [q2] at 0x800005d0
  refine exit_spec hlive (sp := sp - 16) ((hsf.sub (m := 16) (n := 304) (by decide)).shrink (by decide)) _
    (by bsimp [q2]) fun R4 M4 e15 e14 => hk R4 M4 ?_ e14
  rw [e15]; bsimp []; rfl

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **`dc_memfail ()`** at `0x80001e74`: the message to `stderr`, then
`exit(1)` to its `tohost` store. -/
theorem dc_memfail_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat}
    (hG : ∀ a, DcGlob a → S a) (hpn : ldv .ld M prognameAddr = BitVec.ofNat 64 dcNameAddr)
    (hfd : FdAt S M stderrAddr 2) (hsf : StackFrame S sp 320) (hfar : stderrAddr + 4 ≤ sp - 320)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hk : ∀ R' M', R' 15 = exitWord 1#64 → R' 14 = exitSite.base → DWO live S Q t 0x800005c8#64 R' M') :
    DWO live S Q t 0x80001e74#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hlive [h2, hpn, stderr_word] at 0x80001e7c
  bsimp []
  bc_run hlive hlive [h2, hpn, stderr_word] at 0x80001e80
  bsimp []
  bc_run hlive hlive [h2, hpn, stderr_word] at 0x80001e84
  exact mf_call hlive hfd hsf hfar _ (by bsimp [h2]) (by bsimp []) (by bsimp []) hk

end Dc.Mach
