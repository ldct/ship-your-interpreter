import Dc.Mach.EvalBase
import Dc.Mach.BootStart

/-!
# The stack bound (M11)

`evalstr`'s entry from the boot has `sp = __stack_top - 48` (`main`'s 32-byte
frame and `dc_evalstr`'s 16), and everything down to `__heap_end` is its
stack (`evW` bytes). `EvalstrSpec` asks of an evaluation nesting `d` deep:

* `176 * (d + 1) + 1216 + rmStack (2 ^ 30) ≤ W` — `d + 1` `evalstr` frames of
  176 bytes, `dc_func`'s 192 and the deepest number chain below it
  (`bc_raise`/`bc_divide` … `_bc_rec_mul` at every Karatsuba level of the
  largest operand, `rmStack (2 ^ 30) = 224 + 192 * 58`);
* the printing chains `192 + 336 + prN` and `192 + 336 + dnN` above `d + 1`
  frames.

`rmDepth_2_30` evaluates the Karatsuba depth (58 levels); `dc_stack_bound`
checks the three inequalities at `dcD = 47589`, the nesting bound
`DcAdmissible` asks for (`8 MiB - 48 = 176 * 47590 + 12720`).
-/

namespace Dc.Mach

/-- `evalstr`'s `sp` at the boot's call. -/
abbrev evSp : Nat := 0x87ffffd0

/-- The stack below it, to `__heap_end`. -/
abbrev evW : Nat := evSp - heapEnd

/-- **The nesting bound** of an admissible program. -/
abbrev dcD : Nat := 47589

/-- Karatsuba levels below `2^30` digits. -/
theorem rmDepth_2_30 : rmDepth (2 ^ 30) = 58 := by
  repeat (rw [rmDepth]; simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceDiv, Nat.reduceAdd,
    Nat.reduceLT, ↓reduceIte])

theorem rmStack_2_30 : rmStack (2 ^ 30) = 11360 := by
  rw [rmStack, rmDepth_2_30]

/-- **The stack bound**: `evalstr`'s premises at nesting `dcD`. -/
theorem dc_stack_bound :
    176 * (dcD + 1) + 1216 + rmStack (2 ^ 30) ≤ evW ∧ 176 * (dcD + 1) + 192 + 336 + prN ≤ evW ∧
      176 * (dcD + 1) + 192 + 336 + dnN ≤ evW := by
  simp only [prN, onN, onW, dnN, dnW, rmStack_2_30]
  refine ⟨by decide, by decide, by decide⟩

end Dc.Mach
