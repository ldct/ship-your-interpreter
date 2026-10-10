import Dc.Mach.DcFuncCtx
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
`fnOomA_memfail` gives `dc_func`'s out-of-memory continuation from the state
at its entry for every 16-aligned `sp'` (`FnOomA`). **Open (alignment):**
`FnOom` quantifies over all `sp'`; closing `FnOom` from `FnOomA` needs
`sp' % 16 = 0` threaded through the out-of-memory continuations (the bc
layer's `CallerCtx.oom`/`HcOom` up to `OomAt`), see the M9 ledger entry of
`dc_memfail_spec`.
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

/-- A 320-byte frame below an aligned `sp'` inside the window `W` of a frame
`W + 320` bytes deep. -/
theorem StackFrame.below {S : Nat → Prop} {sp W sp' : Nat} (hsf : StackFrame S sp (W + 320))
    (hlo : sp - W ≤ sp') (hhi : sp' ≤ sp) (hal : sp' % 16 = 0) : StackFrame S sp' 320 := by
  have hl := hsf.lo; have hh := hsf.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  rw [htx] at hl
  have hl' : 0x8001ad00 + 16 + 320 + W ≤ sp := by omega
  have hlo' : 0x8001ad00 + 16 + 320 ≤ sp' := Nat.le_trans (Nat.le_sub_of_add_le hl') hlo
  refine ⟨fun a e1 e2 => hsf.own a ?_ (by omega), by rw [htx]; exact hlo', by omega, hal⟩
  rw [Nat.sub_add_eq]; exact Nat.le_trans (Nat.sub_le_sub_right hlo 320) e1

/-- `dc_func`'s out-of-memory continuation for 16-aligned stack pointers. -/
def FnOomA (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (sp W : Nat) (M0 : Mem) : Prop :=
  ∀ t' R' M' sp', sp' % 16 = 0 → OomAt S sp W M0 ocG sp' R' M' → DWO live S Q t' 0x80001e74#64 R' M'

/-- **`dc_func`'s out-of-memory continuation, aligned**, from the state at its
entry (`progname` and `stderr` through `DcAt`) with 320 bytes of stack below
its `W`-byte window. -/
theorem fnOomA_memfail {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {sp W : Nat} {M0 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M0 H F L C G hs st) (hsf : StackFrame S sp (W + 320)) (hab : heapEnd + W + 320 ≤ sp)
    (hex : ∀ t R'' M'', R'' 15 = exitWord 1#64 → R'' 14 = exitSite.base →
      DWO live S Q t 0x800005c8#64 R'' M'') :
    FnOomA live S Q sp W M0 := fun t R' M' sp' hal ho => by
  have hl := hsf.lo; have hh := hsf.hi
  have hlo := ho.lo; have hhi := ho.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapEnd] at hab
  have hsf' : StackFrame S sp' 320 := hsf.below hlo hhi hal
  refine oom_memfail (sp := sp) (W := W) (sp' := sp') (P := ocG) hlive h.glob h.view.prog h.errFile
    (Nat.le_sub_of_add_le (by simp only [heapEnd]; omega)) (fun a hp hc => ?_) ho hsf'
    (Nat.le_sub_of_add_le (by
      have hq : 2273312768 + 320 ≤ sp' :=
        Nat.le_trans (Nat.le_sub_of_add_le (show 2273312768 + 320 + W ≤ sp by omega)) hlo
      exact Nat.le_trans (by decide) hq)) (hex t)
  simp only [ocG, PinWords, stdoutFile, lineMaxAddr, errnoAddr, outColAddr, dc_addrs] at hc hp; omega

end Dc.Mach
