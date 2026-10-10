import Dc.Mach.Stdio

/-!
# The libc stubs (`dc-port/libc/libc.c`)

Leaf functions that return a constant or their argument (`getenv`, `system`,
`getc`, `ungetc`, `fflush`, `fclose`, `ferror`, `fileno`, `isatty`, `perror`,
`fopen`, `signal`), and the exits (`_exit`, `exit`, `abort`, `__assert_fail`),
which run to their `tohost` store with the exit word in `a5` and the store's
base in `a4`; `dcExit_haltFact` (`Htif.lean`) takes the machine from there.

`strtol` is reached only through `getenv`, which always fails; it has no spec.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The continuation of a leaf call: at the return address with the
registers outside `ks` unchanged and `post` on the result. -/
abbrev LeafRet (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R : Nat → BitVec 64) (Mt : Mem) (ks : List Nat) (post : (Nat → BitVec 64) → Prop) : Prop :=
  ∀ R', Keeps ks R' R → post R' → DW live S Q (R 1) R' Mt

/-- Run a leaf function to its `ret` and hand the result to `hk`. -/
macro "dc_leaf " hlive:term:max hk:term:max : tactic =>
  `(tactic| (dx_run $hlive; exact $hk _ (by keeps_tac Keeps.refl _ _) (by dc_simp []; try decide)))

section Leaves

variable {live : Nat → Prop} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
  (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)

include hlive hal

/-- `getenv(name)` at `0x8000084c`: `NULL`. -/
theorem getenv_spec (hk : LeafRet live S Q R Mt [10] fun R' => R' 10 = 0#64) :
    DW live S Q 0x8000084c#64 R Mt := by dc_leaf hlive hk

/-- `system(cmd)` at `0x80000854`: `-1`. -/
theorem system_spec (hk : LeafRet live S Q R Mt [10] fun R' => R' 10 = BitVec.allOnes 64) :
    DW live S Q 0x80000854#64 R Mt := by dc_leaf hlive hk

/-- `getc(f)` at `0x80000700`: `EOF` (`-1`). -/
theorem getc_spec (hk : LeafRet live S Q R Mt [10] fun R' => R' 10 = BitVec.allOnes 64) :
    DW live S Q 0x80000700#64 R Mt := by dc_leaf hlive hk

/-- `ungetc(c, f)` at `0x80000708`: returns `c`. -/
theorem ungetc_spec (hk : LeafRet live S Q R Mt [] fun R' => R' 10 = R 10) :
    DW live S Q 0x80000708#64 R Mt := by dc_leaf hlive hk

/-- `fflush(f)` at `0x8000070c`: `0`. -/
theorem fflush_spec (hk : LeafRet live S Q R Mt [10] fun R' => R' 10 = 0#64) :
    DW live S Q 0x8000070c#64 R Mt := by dc_leaf hlive hk

/-- `fclose(f)` at `0x80000714`: `0`. -/
theorem fclose_spec (hk : LeafRet live S Q R Mt [10] fun R' => R' 10 = 0#64) :
    DW live S Q 0x80000714#64 R Mt := by dc_leaf hlive hk

/-- `ferror(f)` at `0x8000071c`: `0`. -/
theorem ferror_spec (hk : LeafRet live S Q R Mt [10] fun R' => R' 10 = 0#64) :
    DW live S Q 0x8000071c#64 R Mt := by dc_leaf hlive hk

/-- `isatty(fd)` at `0x8000072c`: `fd < 3` (signed). -/
theorem isatty_spec (hk : LeafRet live S Q R Mt [10] fun R' => R' 10 = sltiV (R 10) 3#64) :
    DW live S Q 0x8000072c#64 R Mt := by dc_leaf hlive hk

/-- `perror(s)` at `0x80000734`: nothing. -/
theorem perror_spec (hk : LeafRet live S Q R Mt [] fun _ => True) :
    DW live S Q 0x80000734#64 R Mt := by dc_leaf hlive hk

/-- `fopen(path, mode)` at `0x80000738`: `NULL`. -/
theorem fopen_spec (hk : LeafRet live S Q R Mt [10] fun R' => R' 10 = 0#64) :
    DW live S Q 0x80000738#64 R Mt := by dc_leaf hlive hk

/-- `signal(sig, f)` at `0x80000740`: `SIG_DFL` (`0`). -/
theorem signal_spec (hk : LeafRet live S Q R Mt [10] fun R' => R' 10 = 0#64) :
    DW live S Q 0x80000740#64 R Mt := by dc_leaf hlive hk

end Leaves

/-- `fileno(f)` at `0x80000724`: the stream's descriptor. -/
theorem fileno_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {f fd : Nat} (hfd : FdAt S Mt f fd)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 f) (hal : (R 1).toNat % 4 = 0)
    (hk : LeafRet live S Q R Mt [10] fun R' => R' 10 = BitVec.ofNat 64 fd) :
    DW live S Q 0x80000724#64 R Mt := by
  have hlo := hfd.lo
  have hhi := hfd.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive
  all_goals (try (dc_simp [h10]; simp only [LdOK]; omega))
  all_goals (try (dc_simp [h10]; exact accOwn hfd.own))
  exact hk _ (by keeps_tac Keeps.refl _ _) (by dc_simp [h10, hfd.val])

/-! ## The exits -/

/-- `_exit`'s exit word: `(code as uint32) << 1 | 1`. -/
theorem exit_word (a : BitVec 64) :
    (a <<< 32) >>> 31 ||| 1#64 = exitWord (a &&& 4294967295#64) := by
  unfold exitWord
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_and,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show (4294967295#64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := a.isLt
  omega

/-- **`_exit(code)`** at `0x800005b8`: runs to its `tohost` store with the exit
word of `code` (as `uint32`) in `a5`. -/
theorem exit_raw_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64)
    (hk : ∀ R', Keeps [14, 15] R' R → R' 14 = exitSite.base →
      R' 15 = exitWord (R 10 &&& 4294967295#64) → DW live S Q 0x800005c8#64 R' Mt) :
    DW live S Q 0x800005b8#64 R Mt := by
  dx_run hlive at 0x800005c8
  exact hk _ (by keeps_tac Keeps.refl _ _) (by dc_simp []; rfl) (by dc_simp []; exact exit_word _)

/-- **`abort()`** at `0x800005dc`: runs to its `tohost` store with the exit word
of 134. -/
theorem abort_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64)
    (hk : ∀ R', Keeps [14, 15] R' R → R' 14 = tohost_800005e4.base →
      R' 15 = exitWord 134#64 → DW live S Q 0x800005e4#64 R' Mt) :
    DW live S Q 0x800005dc#64 R Mt := by
  dx_run hlive at 0x800005e4
  exact hk _ (by keeps_tac Keeps.refl _ _) (by dc_simp []; rfl) (by dc_simp []; rfl)

/-- **`__assert_fail()`** at `0x800005ec`: as `abort`. -/
theorem assert_fail_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64)
    (hk : ∀ R', Keeps [14, 15] R' R → R' 14 = tohost_800005f4.base →
      R' 15 = exitWord 134#64 → DW live S Q 0x800005f4#64 R' Mt) :
    DW live S Q 0x800005ec#64 R Mt := by
  dx_run hlive at 0x800005f4
  exact hk _ (by keeps_tac Keeps.refl _ _) (by dc_simp []; rfl) (by dc_simp []; rfl)

/-- **`exit(code)`** at `0x800005d0`: pushes `ra` in a 16-byte frame and runs
`_exit`. -/
theorem exit_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp : Nat} (hfr : StackFrame S sp 16)
    (R : Nat → BitVec 64) (hsp : (R 2).toNat = sp)
    (hk : ∀ R' Mt', R' 15 = exitWord (R 10 &&& 4294967295#64) → R' 14 = exitSite.base →
      DW live S Q 0x800005c8#64 R' Mt') :
    DW live S Q 0x800005d0#64 R Mt := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive at 0x800005b8
  all_goals (try dc_frame hfr)
  refine exit_raw_spec hlive _ fun R' _ h14 h15 => hk R' _ ?_ h14
  rw [h15]; dc_simp []

end Dc.Mach
