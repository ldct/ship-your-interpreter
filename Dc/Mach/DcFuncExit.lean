import Dc.Mach.DcFuncBase
import Dc.Mach.Bc.KaraEntry

/-!
# `dc_func`'s exits and its out-of-table dispatch (M10)

`fn_epi` is the shared epilogue at `0x80000c14` (`ra` reloaded from the
frame, the frame popped, `ret`); `fn_ret0` the `DC_OKAY` exit at
`0x80000c10`. `dcf_disp_out`: a character outside `9..126` goes to the
default arm at `0x80000c30`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `dc_func`'s epilogue at `0x80000c14`. -/
theorem fn_epi {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} {ra : BitVec 64}
    (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 192)) (f : ldv .ld M (sp - 192 + 184) = ra)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp → DWO live S Q t ra R' M) :
    DWO live S Q t 0x80000c14#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, f]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) ?_
  bsimp []; rw [Nat.sub_add_cancel (by omega)]

/-- `DC_OKAY` at `0x80000c10`: `a0 = 0`, then the epilogue. -/
theorem fn_ret0 {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} {ra : BitVec 64}
    (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 192)) (f : ldv .ld M (sp - 192 + 184) = ra)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 10] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp → R' 10 = 0#64 →
      DWO live S Q t ra R' M) :
    DWO live S Q t 0x80000c10#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [] at 0x80000c14
  exact fn_epi hlive hsf hab _ (by bsimp [h2]) f hal fun R' k e1 e2 =>
    hk R' ((k.mono (ks' := [1, 2, 10]) (by decide)).trans (by keeps_tac Keeps.refl _ _)) e1 e2 (by rw [k.get 10 (by decide)]; bsimp [])

theorem disp_out_lt {c : Nat} (hc : c < 256) (hout : c < 9 ∨ 126 < c) :
    117 < (BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (BitVec.ofNat 64 (c + 18446744073709551607)))).toNat := by
  rcases hout with h | h
  · have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · have e : BitVec.ofNat 64 (c + 18446744073709551607) = BitVec.ofNat 64 (c - 9) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
    rw [e, exw_ofNat (by omega), sext32_ofNat (by omega), BitVec.toNat_ofNat]; omega

/-- A character outside `9..126` goes to the default arm at `0x80000c30`. -/
theorem dcf_disp_out {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp c : Nat}
    (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp) (hc : c < 256) (hout : c < 9 ∨ 126 < c)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 c)
    (hk : ∀ R', Keeps [2, 13, 14, 15] R' R → R' 2 = BitVec.ofNat 64 (sp - 192) → R' 13 = R 10 →
      DWO live S Q t 0x80000c30#64 R' (writeLog M [(sp - 192 + 184, 8, R 1)])) :
    DWO live S Q t 0x80000b9c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  bc_run hlive hlive [h2, h10, word_sub192 (x := sp) (by omega)] at 0x80000bb0
  any_goals (exact frame_acc hsf (by omega) (by omega))
  have hl := disp_out_lt hc hout
  bc_run hlive hlive [hl] at 0x80000c30
  exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp [h10])

end Dc.Mach
