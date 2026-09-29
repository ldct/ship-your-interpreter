# GNU dc: plan to a verified binary

The goal is the dc analogue of `endToEnd_refinement` (the WHILE result): a
kernel-checked theorem, with axioms `propext`, `Classical.choice` and
`Quot.sound` only, relating the semantics `Dc.Runs` to the behaviour of
`dc-port/dc-riscv-htif.elf` under the Sail RV64 model (`Vsa.Machine`), for
every program the binary can hold.

## The final theorem

```lean
theorem Dc.endToEnd (prog : List Nat) (hp : DcAdmissible prog) :
    (∀ out, Runs 70 prog out →
       Halts (dcBoot prog) (outStr out) 0 ∨ Halts (dcBoot prog) (outStr []) 1 ∨ …) ∧
    (∀ s, Halts (dcBoot prog) s 0 → ∃ out, Runs 70 prog out ∧ s = outStr out) ∧
    (Diverges (dcBoot prog) → ¬ ∃ out, Runs 70 prog out)
```

- `dcBoot prog`: the configuration after the loader (`initializeMemory`) and
  `setupElf` for the ELF with `prog` written into `dc_script.text`, stated at
  its zero-filled view (`Vsa.Densify.fillZero`, as WHILE's theorem is).
- `DcAdmissible prog`: `prog.length < 8192`, no NUL byte in `prog`, and the
  stack bound of M11.
- The exact form of the first conjunct is decided in M0.

Trust base, as for WHILE: the Lean kernel, the Sail RV64 model, and two
natively checked links (the ELF parse yields the loader image; the boot
image equals the kernel's `dcBoot` term), re-checked by a replay script.

## Fixed design decisions

- **Binary.** GNU dc 1.4.1 (GNU bc 1.07.1 sources, unmodified: `dc/eval.c`,
  `misc.c`, `numeric.c`, `stack.c`, `string.c`, `array.c`,
  `lib/number.c`), `dc-port/htif_main.c` (`dc -e` on the embedded program),
  the C library `dc-port/libc/`, libgcc, built by `dc-port/Makefile` with the
  WHILE binary's compiler (xPack GCC 15.2.0, `-O2 -march=rv64i`).
- **Layout.** `dc-port/link.ld` pins `.tohost` at `0x8001ad00` and `gp` at
  `0x8001b510`, the constants the step layer inherits from the WHILE binary
  (`Vsa.Sim.tohostAddr` in `GoodState` and `LdOK`/`StOK`; `roR`). `.text`
  and `.rodata` lie below `.tohost`; `.data`, `.bss`, the heap
  (`_end`…`0x87800000`) and the 8 MiB stack lie above.
- **Environment.** No shell (`system` fails), empty standard input, no
  environment (`DC_LINE_LENGTH` unset: line length 70), standard error
  discarded. The semantics models exactly this (`Dc.dcFunc`, `Dc.skipSys`).
- **Proof technique.** The Iris-route symbolic layer without Iris: `SWP`
  over `LocalRun`/`LocalRunO` (`VsaIris/Vsa/SymRun.lean`, `SymRunO.lean`),
  specialised to dc as `DW` (`Dc/Mach/Run.lean`), driven by generated
  per-instruction step lemmas and `dx_run` (`Dc/Mach/Tac.lean`). Function
  specs are in continuation-passing style over `DW`/`SWPO`, like
  `VsaIris/Vsa/SnpStrlen.lean`. Recursion (macro evaluation) is by
  induction on `Dc.Loop` derivations; non-termination by the fuel-indexed
  interpreter `Dc.run`.
- **Discipline.** `CLAUDE.md` applies to `Dc/`: no `sorry`, `axiom`,
  `native_decide` or `bv_decide`; no raised `maxHeartbeats`; named-field
  structures for pre/postconditions; generated code over hand repetition.

## Milestones

Each milestone ends with its modules compiled, `#print axioms` on its
headline theorems, and a commit. Instruction counts are from
`experiments/dc/disasm.txt`.

### M0. Statement and resources (Refinement.lean)

Decide how resource exhaustion appears in the theorem and restate
`Dc.DcSim`/`Dc.refinement` accordingly.

- *Heap.* `malloc` returns `NULL` when the bump pointer reaches
  `__heap_end`; dc then exits with status 1 (`dc_memfail`, `out_of_memory`).
  Either (a) weaken `term_sim` to "halts with `out` and status 0, or halts
  with status 1", or (b) add a capacity hypothesis over an allocation-cost
  instrumentation of the semantics (WHILE's `capacity`). Recommendation:
  (a); (b) needs a cost model of every `malloc` in the bc library
  (including Karatsuba temporaries) and can be added later without
  changing the proof structure.
- *Stack.* Nested macro evaluation recurses in C (`evalstr` →
  `dc_eval_and_free_str` → `evalstr`); overflow corrupts the heap, so a
  hypothesis is unavoidable. Define `Dc.Depth prog d` (some evaluation of
  `prog`, terminating or not, reaches non-tail nesting depth `d`) as an
  inductive relation beside `Loop`, and require `∀ d, Depth prog d →
  d * F + B ≤ 8 MiB` with `F` the per-level frame bytes and `B` the deepest
  library call chain, both read off the binary (M11).
- Deliverable: the final statement in `Dc/Refinement.lean`, with the
  admissibility structure and a control witness showing it is satisfiable
  (a concrete program).

### M1. Machine layer (Dc/Mach)

- Compile the generated decode lemmas (`Dc/Mach/DecodeTable/*`, 2,762
  words) and the step table (`Dc/Mach/Steps/*`, 7,794 instructions). Fix the
  generators until every file compiles; add `--check` of both generators to
  a dc stage of `scripts/check_all.sh`.
- Hand-written step lemmas for the six instructions without one: `lb`
  (`0x80004120`, `0x800041c8`, in `_bc_shift_addsub`) as an observed load
  step (`stepObs_alu` pattern with `execute_load_signed_char`); the two
  `_start` instructions that set `gp` (a boot segment outside `DW`); the two
  `ebreak`s are unreachable and need none.
- HTIF: `swp_putc` instances for the `tohost` stores of `fputc`/`putchar`
  (`TohostSite` certificates), and the exit store of `_exit`
  (`exit_haltFact`), giving a `Halts` from a symbolic run.
- `dx_run` validated on straight-line code, a loop and a call.
- Exit: `strlen` specified and proved (the first end-to-end use).

### M2. The C library (`dc-port/libc/libc.c`, ~700 instructions)

Specs, in the style of `SnpStrlen.lean` (register keep-sets, named
preconditions, CPS continuations):

- Byte functions: `memcpy`, `memset`, `memchr`, `strchr`, `strlen`,
  `strncpy` (loops, owned or read-only bytes).
- Output: `fputc`/`putchar` on `stdout` print one byte (`SWPO`), on
  `stderr` print nothing; `fwrite` prints `size*n` bytes.
- Formatting: `emit_unsigned`, `format.constprop.0`, `vfprintf`,
  `fprintf`, `snprintf`, for the conversions dc uses (`%s %c %#o %ld`,
  literals). Spec: the byte string produced equals a Lean function of the
  format and arguments (`Dc.Mach.fmt`); to `stderr` the run only terminates
  and preserves memory outside the call's frame.
- Allocator: `malloc`, `free`, `realloc` with the heap invariant
  `HeapInv` (a walk of headers from the aligned `_end` to the bump
  pointer; the free list is a duplicate-free list of free blocks) and the
  ownership split: a returned block is fresh, disjoint from every live
  block and from the allocator's own bytes; `free` returns it. Heap
  exhaustion returns `NULL`.
- Stubs: `getenv` (`NULL`), `system` (`-1`), `getc` (`EOF`), `fflush`,
  `fclose`, `ferror`, `signal`, `isatty`, `abort`, `__assert_fail`, `exit`,
  `_exit`.
- libgcc: `__muldi3`, `__divdi3`, `__moddi3`, `__udivdi3`/`__umoddi3`,
  `__divsi3`/`__modsi3`/`__udivsi3`/`__umodsi3` (the WHILE proofs of the
  64-bit routines, `divdi3_wrap_spec` and friends, are the model; the code
  bytes are the same at different addresses).

### M3. Number representation (lib/number.c data)

- `bc_struct` layout (read off `bc_new_num`): `n_sign` @0, `n_len` @4,
  `n_scale` @8, `n_refs` @12, `n_next` @16, `n_ptr` @24, `n_value` @32; 40
  bytes. Digits are `n_len + n_scale` bytes `0..9` at `n_value`.
- `NumAt Mt p x`: the struct at `p` and its digit array represent
  `x : Dc.Num` (sign flag, magnitude, scale; `n_len` is the digit count of
  the integer part without leading zeros, at least 1).
- Sharing: numbers are immutable once shared and reference counted
  (`bc_copy_num`, `dc_dup_num`). Abstract heap of number objects
  `NumHeap := List (Addr × Num × refcount)` with `refcount` = number of
  references from the machine state (dc stack, registers, arrays,
  `_zero_`/`_one_`/`_two_`, live temporaries). The `_bc_Free_list` holds
  dead structs (digits freed).
- Lemmas: frame (a number's bytes are untouched by writes outside its
  footprint), footprints disjoint across objects, transfer of ownership on
  `bc_free_num` reaching zero.

### M4. bc: allocation, comparison, small functions (~450 instructions)

`bc_new_num`, `bc_free_num`, `bc_copy_num`, `bc_init_num`,
`bc_init_numbers`, `_bc_rm_leading_zeros` (inlined where used),
`_bc_do_compare`, `bc_compare`, `bc_is_zero`, `bc_is_near_zero`,
`bc_is_neg`, `bc_num2long`, `bc_int2num`, `bc_out_long` — each against the
corresponding `Dc.Num` function (`Num.cmp`, `Num.isNearZero`, `Num.toLong`,
`Num.ofInt`, `Num.outLong`).

### M5. bc: addition and subtraction (~520 instructions)

`_bc_do_add`, `_bc_do_sub` (digit loops with carry/borrow over aligned
scales), `bc_add`, `bc_sub` against `Num.add`/`Num.sub`, including the
equal-magnitude zero, the `scale_min` padding, and leading-zero removal.
Needs digit-array arithmetic lemmas: the value of a digit array, carry
propagation, alignment by scale (`Dc/Mach/Bc/Digits.lean`).

### M6. bc: multiplication (~950 instructions)

`_bc_simp_mul` (schoolbook, inlined in `_bc_rec_mul`), `_bc_shift_addsub`
(with the two `lb` steps), `new_sub_num`, the Karatsuba recursion
`_bc_rec_mul` (threshold `MUL_BASE_DIGITS = 80`), and `bc_multiply`
(truncation to `min (s1+s2) (max k (max s1 s2))`, zero sign) against
`Num.mul`. Karatsuba correctness is proved on digit-array values by
strong induction on length.

### M7. bc: division (~650 instructions)

`_one_mult`, `bc_divide` (normalisation, `qguess` with the Knuth
correction, the divide-by-one early branch whose result is overwritten)
against `Num.div`; `bc_divmod`, `bc_modulo` against `Num.divmod`/
`Num.modulo`. The key lemma is that `bc_divide`'s quotient equals
`⌊a·10^(sb+k) / (b·10^sa)⌋` digit by digit.

### M8. bc: powers, roots, output (~1,160 instructions)

- `bc_raise` against `Num.raise` (exact intermediate scales, truncation by
  `n_scale`, negative exponents via `bc_divide`, the `LONG_MAX` exponent
  bound).
- `bc_raisemod` against `Num.raisemod`.
- `bc_sqrt` against `Dc.SqrtLoop` (the machine's Newton loop matches the
  relation step for step; termination is not needed because `SqrtLoop` is
  the relation's own recursion).
- `bc_out_num` (base 10 and other bases, `bc_out_long` digits for bases
  above 16) with `out_char` line wrapping against `Num.out`.

### M9. dc data and helpers (~1,300 instructions)

- Representation of `Dc.St`: the evaluation stack (`dc_list` nodes with
  `dc_data`), 256 register stacks with per-level arrays (`dc_array` lists),
  `dc_string` objects (reference counted, `s_ptr`/`s_len`), the globals
  `dc_ibase`, `dc_obase`, `dc_scale`, `unwind_depth`, `unwind_noexit`, and
  the out column of `out_char`.
- Specs of `stack.c` (`dc_push`, `dc_pop`, `dc_top_of_stack`,
  `dc_clear_stack`, `dc_binop`, `dc_binop2`, `dc_triop`, `dc_cmpop`,
  register get/set/push/pop, `dc_stack_rotate`, `dc_tell_*`,
  `dc_printall`), `array.c`, `string.c` (`dc_makestring`, `dc_dup_str`,
  `dc_free_str`, `dc_out_str`, `dc_readstring` on empty stdin),
  `numeric.c` wrappers (`dc_add` … `dc_sqrt`, `dc_num2int`,
  `dc_int2data`, `dc_getnum`, `dc_out_num`, `dc_dump_num`, `dc_numlen`,
  `dc_tell_scale`), `misc.c` (`dc_print`, `dc_show_id`, `dc_system`,
  `dc_malloc`, `dc_memfail`, `dc_dup`) — each against the matching
  `Dc.Machine` function.

### M10. The evaluator (~870 instructions)

- `dc_func` (the command `switch`, jump table in `.rodata`): for each
  command character, the machine run from `dc_func`'s entry refines
  `Dc.dcFunc` (state and returned status); one lemma per `switch` arm,
  generated where arms share a shape.
- `evalstr`: its loop state (`s`, `end`, `tail_depth`, `next_negcmp`)
  represents a `Dc.Frame`; by induction on `Dc.Loop`/`Dc.Tos` derivations,
  a derivation `Loop lm st f st' r` yields a machine run from `evalstr`'s
  loop head to its return with the represented `st'` and `r` (term
  direction).
- Stuck direction: by induction on fuel, `Dc.run lm n st f = none` implies
  no clean halt of the machine within the corresponding number of steps.
- `dc_evalstr` (top-level status).

### M11. Boot, exit and the stack bound

- `_start` (`gp`, `sp`, `.bss` clearing loop), `main` (`dc_math_init`,
  `dc_string_init`, `dc_register_init`, `dc_array_init`, `strlen`,
  `dc_makestring`), `flush_okay`, `exit`/`_exit`.
- The stack: per-level frame size of the `evalstr` recursion and the
  deepest library chain below it, read off the prologues; `Dc.Depth` and
  the admissibility bound of M0 discharge every stack store's side
  condition.
- Boot image: the loader memory of the ELF with `prog` patched in, as a
  kernel term (`dcBoot`), with the native `ElfLoads`-style check and a
  replay script (the WHILE `experiments/review-v2/Replay.lean` pattern).

### M12. Assembly and audit

- `DcSim` for the layout from M10 and M11; `Dc.endToEnd`.
- Capstones: `Dc.Validation` theorems restated as machine `Halts` facts for
  the validation programs.
- Gates: generator `--check`s, the axiom audit of every headline theorem,
  `scripts/dc/difftest.py` and `scripts/dc/elf_difftest.py` on the corpus,
  the boot replay. README section updated.

## Validation (continuous)

- `scripts/dc/difftest.py`: the Lean interpreter against host GNU dc
  (programs using `!` or `?` excluded; they differ by environment).
- `scripts/dc/elf_difftest.py`: the ELF on the proof's machine model
  (`Vsa.runElf`) against the Lean interpreter, all programs.
- `scripts/dc/gen_validation.py`: kernel-checked `Runs` theorems for
  outputs the ELF produced (`Dc/Validation.lean`).

Rerun both difftests after any change to the semantics, the port or the
libc; regenerate the decode and step tables after any change to the ELF.

## Known risks

- **Proof size.** The bc library is ~3,500 instructions of digit-array
  arithmetic; Karatsuba and long division are the largest single proofs.
  Mitigation: prove the digit algorithms once over a Lean functional model
  of each C function, then relate machine runs to the model by symbolic
  execution (two-step refinement), and generate the per-arm `dc_func`
  lemmas.
- **Build time.** The step table is 33 MB of generated Lean; keep modules
  under ~120 instructions and build serially into the private tree.
- **Semantics mismatches** found during the proof (as `bc_num2long`'s
  `LONG_MAX` was found by testing) are fixed in `Dc/Num.lean`/
  `Dc/Machine.lean` first, re-validated by both difftests, then the proof
  continues.
- **Unreachable code** (`dc_evalfile`, `input_fil`, `bc_str2num`,
  `bc_num2str`, `dc_trap_interrupt`, `strtol`, `ungetc`, `perror`,
  `fopen`, the `ebreak`s) needs no spec; the symbolic runs never reach it.

## Status

| Milestone | Status |
| --- | --- |
| Semantics, interpreter, adequacy, validation tooling | done |
| Port, libc, layout | done |
| M0 statement and resources | open |
| M1 machine layer | generators done; tables compiling |
| M2–M12 | open |
