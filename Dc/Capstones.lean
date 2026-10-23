import Dc.EndToEnd
import Dc.Mach.EvalCheck

/-!
# Capstones: the binary on concrete programs

For a program whose evaluation terminates within fuel `N`, `admCheck N prog`
decides `DcAdmissible prog` by one evaluation (`DcAdmissible.of_check`,
through the stabilization of the budgets, `Dc/Mach/EvalStable.lean`, and the
computed per-call premise, `Dc/Mach/EvalCheck.lean`). `Dc.endToEnd` then
gives the binary's behaviour: it halts with the semantics' output (or runs
out of heap), and every clean halt prints exactly that output.
-/

namespace Dc

open Dc.Mach Vsa.Machine

/-- `DcAdmissible`, decided at fuel `N` for a program that terminates by then. -/
def admCheck (N : Nat) (prog : List Nat) : Bool :=
  decide (prog.length < 8192) && !prog.contains 0 && prog.all (· < 256) &&
  (run 70 N St.init ⟨prog, 1, false⟩).isSome &&
  decide (nestDepth 70 N St.init ⟨prog, 1, false⟩ ≤ dcD) &&
  decide (leakCount 70 N St.init ⟨prog, 1, false⟩ ≤ dcK) &&
  decide (tailMax 70 N St.init ⟨prog, 1, false⟩ < 2 ^ 31) &&
  allCallsB 70 fnSizeB N St.init ⟨prog, 1, false⟩

theorem DcAdmissible.of_check {N : Nat} {prog : List Nat} (h : admCheck N prog = true) :
    DcAdmissible prog := by
  simp only [admCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hl, hz⟩, hb⟩, hr⟩, hn⟩, hk⟩, ht⟩, hc⟩ := h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hr
  exact
    { len := hl
      nz := fun h0 => by simp_all
      byte := hb
      nest := nestBound_of_run hx hn
      leak := leakBound_of_run hx hk
      size := size_of_run hx hc
      tail := tailBound_of_run hx ht }

/-- **A capstone**: from `admCheck` and `runOut` at fuel `N`, the binary
halts with the output `out` (or exhausts the heap), and prints `out` in
every clean halt. -/
theorem capstone {N : Nat} {prog out : List Nat} (ha : admCheck N prog = true)
    (hr : runOut 70 N prog = some out) :
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out := by
  have e := endToEnd prog (DcAdmissible.of_check ha)
  have ho := runOut_spec hr
  refine ⟨e.1 out ho.1, fun s hs => ?_⟩
  obtain ⟨out', h1, rfl⟩ := e.2.1 s hs
  rw [ho.2 _ h1]

end Dc

/-! ## The validation programs

The programs of `scripts/dc/gen_validation.py`, each with the output the
semantics gives it (`runOut`, checked by the kernel), which is the output
the RISC-V binary printed in the ELF difftest. All 25 are admissible
(`admCheck`). `tail` (`[1+ d 1000>a]sa 0 lax p`, a thousand tail calls) has
no capstone: its evaluation nests too deeply for the kernel's `decide`
without a raised recursion limit.
-/

namespace Dc.Capstones

open Dc.Mach Vsa.Machine

/-- `[hello, world]p` prints
```
hello, world
```
-/
theorem hello_halts :
    let prog : List Nat := [91, 104, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 93, 112]
    let out : List Nat := [104, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `1 2+p 5 3-p 6 7*p 7 2/p _7 2/p 2k 7 3/p 2k _7 3%p 10 3~f` prints
```
3
2
42
3
-3
2.33
-.01
.01
3.33
-.01
2.33
-3
3
42
2
3
```
-/
theorem arith_halts :
    let prog : List Nat := [49, 32, 50, 43, 112, 32, 53, 32, 51, 45, 112, 32, 54, 32, 55, 42, 112, 32, 55, 32, 50, 47, 112, 32, 95, 55, 32, 50, 47, 112, 32, 50, 107, 32, 55, 32, 51, 47, 112, 32, 50, 107, 32, 95, 55, 32, 51, 37, 112, 32, 49, 48, 32, 51, 126, 102]
    let out : List Nat := [51, 10, 50, 10, 52, 50, 10, 51, 10, 45, 51, 10, 50, 46, 51, 51, 10, 45, 46, 48, 49, 10, 46, 48, 49, 10, 51, 46, 51, 51, 10, 45, 46, 48, 49, 10, 50, 46, 51, 51, 10, 45, 51, 10, 51, 10, 52, 50, 10, 50, 10, 51, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `1.5 2.25+p 1.50 2.2-p 0.1 0.2*p 2k 0.1 0.2*p 1.234 5.6789*p` prints
```
3.75
-.70
0
.02
7.0077
```
-/
theorem scale_halts :
    let prog : List Nat := [49, 46, 53, 32, 50, 46, 50, 53, 43, 112, 32, 49, 46, 53, 48, 32, 50, 46, 50, 45, 112, 32, 48, 46, 49, 32, 48, 46, 50, 42, 112, 32, 50, 107, 32, 48, 46, 49, 32, 48, 46, 50, 42, 112, 32, 49, 46, 50, 51, 52, 32, 53, 46, 54, 55, 56, 57, 42, 112]
    let out : List Nat := [51, 46, 55, 53, 10, 45, 46, 55, 48, 10, 48, 10, 46, 48, 50, 10, 55, 46, 48, 48, 55, 55, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `2 10^p 2 _1^p 2k 3 _2^p 1.5 3^p _.1 3^p 3 5 7|p 4 13 497|p` prints
```
1024
0
.11
3.37
-0
0
1.59
```
-/
theorem power_halts :
    let prog : List Nat := [50, 32, 49, 48, 94, 112, 32, 50, 32, 95, 49, 94, 112, 32, 50, 107, 32, 51, 32, 95, 50, 94, 112, 32, 49, 46, 53, 32, 51, 94, 112, 32, 95, 46, 49, 32, 51, 94, 112, 32, 51, 32, 53, 32, 55, 124, 112, 32, 52, 32, 49, 51, 32, 52, 57, 55, 124, 112]
    let out : List Nat := [49, 48, 50, 52, 10, 48, 10, 46, 49, 49, 10, 51, 46, 51, 55, 10, 45, 48, 10, 48, 10, 49, 46, 53, 57, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `2v p 2k 2v p 0.0001v p 10k 1000000v p 0.25v p 144v p` prints
```
1
1.41
.0100
1000.0000000000
.5000000000
12.0000000000
```
-/
theorem sqrt_halts :
    let prog : List Nat := [50, 118, 32, 112, 32, 50, 107, 32, 50, 118, 32, 112, 32, 48, 46, 48, 48, 48, 49, 118, 32, 112, 32, 49, 48, 107, 32, 49, 48, 48, 48, 48, 48, 48, 118, 32, 112, 32, 48, 46, 50, 53, 118, 32, 112, 32, 49, 52, 52, 118, 32, 112]
    let out : List Nat := [49, 10, 49, 46, 52, 49, 10, 46, 48, 49, 48, 48, 10, 49, 48, 48, 48, 46, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 10, 46, 53, 48, 48, 48, 48, 48, 48, 48, 48, 48, 10, 49, 50, 46, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `1.p .5p 0.00p _0p _ 5p 007p 0.10p [abc]p [a[b]c]p [a]n [b]n 10P` prints
```
1
.5
0
0
-5
7
.10
abc
a[b]c
ab
```
-/
theorem printing_halts :
    let prog : List Nat := [49, 46, 112, 32, 46, 53, 112, 32, 48, 46, 48, 48, 112, 32, 95, 48, 112, 32, 95, 32, 53, 112, 32, 48, 48, 55, 112, 32, 48, 46, 49, 48, 112, 32, 91, 97, 98, 99, 93, 112, 32, 91, 97, 91, 98, 93, 99, 93, 112, 32, 91, 97, 93, 110, 32, 91, 98, 93, 110, 32, 49, 48, 80]
    let out : List Nat := [49, 10, 46, 53, 10, 48, 10, 48, 10, 45, 53, 10, 55, 10, 46, 49, 48, 10, 97, 98, 99, 10, 97, 91, 98, 93, 99, 10, 97, 98, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `12345Zp .00012Zp 1.20Xp [abc]Zp [abc]Xp 0Zp 100Xp` prints
```
5
2
2
3
0
1
0
```
-/
theorem length_halts :
    let prog : List Nat := [49, 50, 51, 52, 53, 90, 112, 32, 46, 48, 48, 48, 49, 50, 90, 112, 32, 49, 46, 50, 48, 88, 112, 32, 91, 97, 98, 99, 93, 90, 112, 32, 91, 97, 98, 99, 93, 88, 112, 32, 48, 90, 112, 32, 49, 48, 48, 88, 112]
    let out : List Nat := [53, 10, 50, 10, 50, 10, 51, 10, 48, 10, 49, 10, 48, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `1 2 3 3R f c 1 2 3 _3R f c 1dp d+p z p c 1 2 r f` prints
```
1
3
2
2
1
3
1
2
2
1
2
```
-/
theorem stack_halts :
    let prog : List Nat := [49, 32, 50, 32, 51, 32, 51, 82, 32, 102, 32, 99, 32, 49, 32, 50, 32, 51, 32, 95, 51, 82, 32, 102, 32, 99, 32, 49, 100, 112, 32, 100, 43, 112, 32, 122, 32, 112, 32, 99, 32, 49, 32, 50, 32, 114, 32, 102]
    let out : List Nat := [49, 10, 51, 10, 50, 10, 50, 10, 49, 10, 51, 10, 49, 10, 50, 10, 50, 10, 49, 10, 50, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `97a P 3a P 256 1+P [xyz]a P 65P 16706P` prints
```
a\x03\x01\x01xAAB
```
-/
theorem ascii_halts :
    let prog : List Nat := [57, 55, 97, 32, 80, 32, 51, 97, 32, 80, 32, 50, 53, 54, 32, 49, 43, 80, 32, 91, 120, 121, 122, 93, 97, 32, 80, 32, 54, 53, 80, 32, 49, 54, 55, 48, 54, 80]
    let out : List Nat := [97, 3, 1, 1, 120, 65, 65, 66]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `2o 10p 0.5p 5.25p _6p 16o 255p 3.75p 20o 399p 1.5p 100o 12345.678p` prints
```
1010
.1000
101.0100000
-110
FF
3.C0
 19 19
 01.10
 01 23 45.67 80
```
-/
theorem obase_halts :
    let prog : List Nat := [50, 111, 32, 49, 48, 112, 32, 48, 46, 53, 112, 32, 53, 46, 50, 53, 112, 32, 95, 54, 112, 32, 49, 54, 111, 32, 50, 53, 53, 112, 32, 51, 46, 55, 53, 112, 32, 50, 48, 111, 32, 51, 57, 57, 112, 32, 49, 46, 53, 112, 32, 49, 48, 48, 111, 32, 49, 50, 51, 52, 53, 46, 54, 55, 56, 112]
    let out : List Nat := [49, 48, 49, 48, 10, 46, 49, 48, 48, 48, 10, 49, 48, 49, 46, 48, 49, 48, 48, 48, 48, 48, 10, 45, 49, 49, 48, 10, 70, 70, 10, 51, 46, 67, 48, 10, 32, 49, 57, 32, 49, 57, 10, 32, 48, 49, 46, 49, 48, 10, 32, 48, 49, 32, 50, 51, 32, 52, 53, 46, 54, 55, 32, 56, 48, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `2i 101p 1.1p 16i FFp A.8p` prints
```
5
1.5
135
11.0
```
-/
theorem ibase_halts :
    let prog : List Nat := [50, 105, 32, 49, 48, 49, 112, 32, 49, 46, 49, 112, 32, 49, 54, 105, 32, 70, 70, 112, 32, 65, 46, 56, 112]
    let out : List Nat := [53, 10, 49, 46, 53, 10, 49, 51, 53, 10, 49, 49, 46, 48, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `2k Kp 0k Kp Ip Op 1o Op 4294967297k Kp 2147483649k Kp` prints
```
2
0
10
10
10
0
0
```
-/
theorem params_halts :
    let prog : List Nat := [50, 107, 32, 75, 112, 32, 48, 107, 32, 75, 112, 32, 73, 112, 32, 79, 112, 32, 49, 111, 32, 79, 112, 32, 52, 50, 57, 52, 57, 54, 55, 50, 57, 55, 107, 32, 75, 112, 32, 50, 49, 52, 55, 52, 56, 51, 54, 52, 57, 107, 32, 75, 112]
    let out : List Nat := [50, 10, 48, 10, 49, 48, 10, 49, 48, 10, 49, 48, 10, 48, 10, 48, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `[2p]sa 1 2<a 2 1<a 1 2>a 2 1>a 1 1!=a 1 2!=a 1 2!<a 2 1!<a` prints
```
2
2
2
2
```
-/
theorem compare_halts :
    let prog : List Nat := [91, 50, 112, 93, 115, 97, 32, 49, 32, 50, 60, 97, 32, 50, 32, 49, 60, 97, 32, 49, 32, 50, 62, 97, 32, 50, 32, 49, 62, 97, 32, 49, 32, 49, 33, 61, 97, 32, 49, 32, 50, 33, 61, 97, 32, 49, 32, 50, 33, 60, 97, 32, 50, 32, 49, 33, 60, 97]
    let out : List Nat := [50, 10, 50, 10, 50, 10, 50, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `5Sa 6Sa lap Lap Lap Lap f 7 3:b 3;bp 4;bp` prints
```
6
6
5
5
5
6
6
7
0
```
-/
theorem registers_halts :
    let prog : List Nat := [53, 83, 97, 32, 54, 83, 97, 32, 108, 97, 112, 32, 76, 97, 112, 32, 76, 97, 112, 32, 76, 97, 112, 32, 102, 32, 55, 32, 51, 58, 98, 32, 51, 59, 98, 112, 32, 52, 59, 98, 112]
    let out : List Nat := [54, 10, 54, 10, 53, 10, 53, 10, 53, 10, 54, 10, 54, 10, 55, 10, 48, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `[1p q 2p]x 3p` prints
```
1
```
-/
theorem quit_halts :
    let prog : List Nat := [91, 49, 112, 32, 113, 32, 50, 112, 93, 120, 32, 51, 112]
    let out : List Nat := [49, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `[[1p 2Q 5p]x 2p]x 3p [4p 1Q 5p]x 6p` prints
```
1
3
4
5
6
```
-/
theorem q2_halts :
    let prog : List Nat := [91, 91, 49, 112, 32, 50, 81, 32, 53, 112, 93, 120, 32, 50, 112, 93, 120, 32, 51, 112, 32, 91, 52, 112, 32, 49, 81, 32, 53, 112, 93, 120, 32, 54, 112]
    let out : List Nat := [49, 10, 51, 10, 52, 10, 53, 10, 54, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `y 1 2 f` prints
```
'y' (0171) unimplemented
2
1
```
-/
theorem unimplemented_halts :
    let prog : List Nat := [121, 32, 49, 32, 50, 32, 102]
    let out : List Nat := [39, 121, 39, 32, 40, 48, 49, 55, 49, 41, 32, 117, 110, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 10, 50, 10, 49, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `[d p 1- d 0<a]sa 5 lax` prints
```
5
4
3
2
1
```
-/
theorem loop_halts :
    let prog : List Nat := [91, 100, 32, 112, 32, 49, 45, 32, 100, 32, 48, 60, 97, 93, 115, 97, 32, 53, 32, 108, 97, 120]
    let out : List Nat := [53, 10, 52, 10, 51, 10, 50, 10, 49, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `[d 1- d 1<f *]sf 10 lfx p 30 lfx p` prints
```
3628800
265252859812191058636308480000000
```
-/
theorem factorial_halts :
    let prog : List Nat := [91, 100, 32, 49, 45, 32, 100, 32, 49, 60, 102, 32, 42, 93, 115, 102, 32, 49, 48, 32, 108, 102, 120, 32, 112, 32, 51, 48, 32, 108, 102, 120, 32, 112]
    let out : List Nat := [51, 54, 50, 56, 56, 48, 48, 10, 50, 54, 53, 50, 53, 50, 56, 53, 57, 56, 49, 50, 49, 57, 49, 48, 53, 56, 54, 51, 54, 51, 48, 56, 52, 56, 48, 48, 48, 48, 48, 48, 48, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `0sa 1sb [la lb d sa + d sb p lc 1+ d sc 15>f]sf 0sc lfx` prints
```
1
2
3
5
8
13
21
34
55
89
144
233
377
610
987
```
-/
theorem fibonacci_halts :
    let prog : List Nat := [48, 115, 97, 32, 49, 115, 98, 32, 91, 108, 97, 32, 108, 98, 32, 100, 32, 115, 97, 32, 43, 32, 100, 32, 115, 98, 32, 112, 32, 108, 99, 32, 49, 43, 32, 100, 32, 115, 99, 32, 49, 53, 62, 102, 93, 115, 102, 32, 48, 115, 99, 32, 108, 102, 120]
    let out : List Nat := [49, 10, 50, 10, 51, 10, 53, 10, 56, 10, 49, 51, 10, 50, 49, 10, 51, 52, 10, 53, 53, 10, 56, 57, 10, 49, 52, 52, 10, 50, 51, 51, 10, 51, 55, 55, 10, 54, 49, 48, 10, 57, 56, 55, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `[d Sa % La r d 0<g]sg 1071 462 lgx r p 12345678 87654321 lgx r p` prints
```
21
9
```
-/
theorem gcd_halts :
    let prog : List Nat := [91, 100, 32, 83, 97, 32, 37, 32, 76, 97, 32, 114, 32, 100, 32, 48, 60, 103, 93, 115, 103, 32, 49, 48, 55, 49, 32, 52, 54, 50, 32, 108, 103, 120, 32, 114, 32, 112, 32, 49, 50, 51, 52, 53, 54, 55, 56, 32, 56, 55, 54, 53, 52, 51, 50, 49, 32, 108, 103, 120, 32, 114, 32, 112]
    let out : List Nat := [50, 49, 10, 57, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `50k 2v p` prints
```
1.41421356237309504880168872420969807856967187537694
```
-/
theorem sqrt2_halts :
    let prog : List Nat := [53, 48, 107, 32, 50, 118, 32, 112]
    let out : List Nat := [49, 46, 52, 49, 52, 50, 49, 51, 53, 54, 50, 51, 55, 51, 48, 57, 53, 48, 52, 56, 56, 48, 49, 54, 56, 56, 55, 50, 52, 50, 48, 57, 54, 57, 56, 48, 55, 56, 53, 54, 57, 54, 55, 49, 56, 55, 53, 51, 55, 54, 57, 52, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `1234567890123456789012345678901234567890 987654321098765432109876543210*p` prints
```
121932631137021795226185032733744855963362292333223746380111126352690\
0
```
-/
theorem bigmul_halts :
    let prog : List Nat := [49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 32, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 42, 112]
    let out : List Nat := [49, 50, 49, 57, 51, 50, 54, 51, 49, 49, 51, 55, 48, 50, 49, 55, 57, 53, 50, 50, 54, 49, 56, 53, 48, 51, 50, 55, 51, 51, 55, 52, 52, 56, 53, 53, 57, 54, 51, 51, 54, 50, 50, 57, 50, 51, 51, 51, 50, 50, 51, 55, 52, 54, 51, 56, 48, 49, 49, 49, 49, 50, 54, 51, 53, 50, 54, 57, 48, 92, 10, 48, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)

/-- `2 300^p` prints
```
203703597633448608626844568840937816105146839366593625063614044935438\
1299763336706183397376
```
-/
theorem wrap_halts :
    let prog : List Nat := [50, 32, 51, 48, 48, 94, 112]
    let out : List Nat := [50, 48, 51, 55, 48, 51, 53, 57, 55, 54, 51, 51, 52, 52, 56, 54, 48, 56, 54, 50, 54, 56, 52, 52, 53, 54, 56, 56, 52, 48, 57, 51, 55, 56, 49, 54, 49, 48, 53, 49, 52, 54, 56, 51, 57, 51, 54, 54, 53, 57, 51, 54, 50, 53, 48, 54, 51, 54, 49, 52, 48, 52, 52, 57, 51, 53, 52, 51, 56, 92, 10, 49, 50, 57, 57, 55, 54, 51, 51, 51, 54, 55, 48, 54, 49, 56, 51, 51, 57, 55, 51, 55, 54, 10]
    (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out :=
  capstone (N := 1000000) (by decide +kernel) (by decide +kernel)
end Dc.Capstones
