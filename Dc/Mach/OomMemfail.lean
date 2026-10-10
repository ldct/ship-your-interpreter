import Dc.Mach.DcBinop
import Dc.Mach.DcMemfail

/-!
# Out of memory ends in `exit(1)` (M10/M11)

An out-of-memory continuation (`OomAt` from a memory `M0` whose `progname`
word and `stderr` descriptor are dc's, with a stack frame `StackFrame S sp' 320`
below the callee's `sp'`) runs `dc_memfail` to `_exit`'s store with status 1:
`oom_memfail`. `OomAt` keeps the two words (`PinWords`) unless its
exemption `P` covers them. The frame's alignment (`sp' % 16 = 0`) comes from
the caller: `OomAt` and the callee out-of-memory continuations do not carry
it, so a consumer that only has `OomAt` for an unknown `sp'` cannot use this.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **Out of memory, then `exit(1)`**: from `OomAt` (exemption `P` off the
`PinWords`) over a memory `M0` with dc's `progname` and `stderr` words. -/
theorem oom_memfail {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {sp W sp' : Nat} {M0 M' : Mem}
    {P : Nat → Prop} {R' : Nat → BitVec 64}
    (hG : ∀ a, DcGlob a → S a) (hpn : ldv .ld M0 prognameAddr = BitVec.ofNat 64 dcNameAddr)
    (hfd : FdAt S M0 stderrAddr 2) (hab : heapEnd ≤ sp - W) (hP : ∀ a, PinWords a → ¬ P a)
    (ho : OomAt S sp W M0 P sp' R' M') (hsf : StackFrame S sp' 320) (hfar : stderrAddr + 4 ≤ sp' - 320)
    (hex : ∀ R'' M'', R'' 15 = exitWord 1#64 → R'' 14 = exitSite.base →
      DWO live S Q t 0x800005c8#64 R'' M'') :
    DWO live S Q t 0x80001e74#64 R' M' := by
  have pin : ∀ a, PinWords a → imgM M' a = imgM M0 a := fun a hp =>
    ho.out a (DcGlob.outHeap (by simp only [PinWords, DcGlob] at hp ⊢; omega)) (fun hc => hc.2 hp)
      (fun hf => by simp only [frameIn, PinWords, dc_addrs, heapEnd] at hf hp hab; omega) (hP a hp)
  refine dc_memfail_spec hlive hG ?_ ?_ hsf hfar R' ho.r2 hex
  · rw [ldv_congr .ld fun j hj => pin _ (by simp only [PinWords, widthOfM, dc_addrs] at hj ⊢; omega)]
    exact hpn
  · exact { hfd with
      val := by
        rw [ldv_congr .lw fun j hj => pin _ (by
          simp only [PinWords, widthOfM, stderrAddr, dc_addrs] at hj ⊢; omega)]
        exact hfd.val }

end Dc.Mach
