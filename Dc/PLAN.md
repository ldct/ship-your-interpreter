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
       Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
    (∀ s, Halts (dcBoot prog) s 0 → ∃ out, Runs 70 prog out ∧ s = outStr out) ∧
    (Diverges (dcBoot prog) → ¬ ∃ out, Runs 70 prog out)
```

- `dcBoot prog`: the configuration after the loader (`initializeMemory`) and
  `setupElf` for the ELF with `prog` written into `dc_script.text`, stated at
  its zero-filled view (`Vsa.Densify.fillZero`, as WHILE's theorem is).
- `DcAdmissible prog`: `prog.length < 8192`, no NUL byte in `prog`, and
  `NestBound 70 prog D` (`Dc/Depth.lean`) for the nesting bound `D` of M11.
- Heap exhaustion is allowed as an outcome: status 1 (decision M0 (a)).

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

### M0. Statement and resources (done)

- *Heap* (decision (a)): `malloc` returns `NULL` when the bump pointer
  reaches `__heap_end` and dc exits with status 1 (`dc_memfail`,
  `out_of_memory`). `DcSim.term_sim` allows that exit
  (`Dc/Refinement.lean`); `refinement` still gives that every clean halt is
  a terminating run with the same output, and that divergence excludes
  termination. A capacity hypothesis (WHILE's `capacity`) can later remove
  the status-1 disjunct without changing the proof structure.
- *Stack*: `Dc.nestDepth lm n st f` (`Dc/Depth.lean`) is the deepest
  non-tail macro nesting within `n` steps, defined for every fuel, so it
  bounds non-terminating evaluations too; `NestBound lm prog D` is
  `∀ n, nestDepth lm n St.init ⟨prog, 1, false⟩ ≤ D`. M11 fixes `D` from
  the binary's frame sizes (`D * F + B ≤ 8 MiB`).
- Remaining for M12: the concrete `DcAdmissible` and a control witness.

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
- The two `_start` instructions that set `gp` (`0x80000000`/`0x80000004`)
  run before `DW` holds (`gp` is read-only there): a boot segment from the
  loader state to `DW` at `0x80000008`.
- `Halts` from a printing run: the `DWO` run from the boot state to
  `_exit`'s store (`dcExit_haltFact`, `Dc/Mach/Htif.lean`) through
  `wp_lroW`, `wp_exitW` and `vsa_adequacy_exit`, with the boot ownership
  split (the VSA pattern: `VsaIris/Interp/EndToEnd.lean`).
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

Last run (current ELF): ELF difftest 1,660 agree, 0 differ, 2 over the
2,000,000-step limit, of 1,662 programs; host dc differences 0.

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
| M0 statement and resources | done |
| M1 machine layer | done: decode and step tables compile (`gen_dc_decode.py`, `gen_dc_steps.py`, `--check` in `check_all.sh`); observed `lb` steps `stL_80004120`/`stL_800041c8` (`Dc/Mach/LoadObs.lean`); HTIF `tohost_<pc>` sites, `stP_<pc>` print steps (`Dc/Mach/Tohost.lean`), `DWO`, `dcExit_haltFact` (`Dc/Mach/Htif.lean`); `dx_run` on straight-line code, a loop and a call (`strlen_loop`, `main_scriptLen`); `strlen_spec` (`Dc/Mach/Strlen.lean`). The `gp` boot pair and `Halts` from a run are M11 items |
| M2 C library | done: byte functions `memset_spec`, `memcpy_spec`, `memchr_spec`, `strchr_spec`, `strncpy_spec` (`Bytes.lean`); `fputc_spec`, `putchar_spec`, `fwrite_*` over `DWO` (`Stdio.lean`); stubs and exits (`Stubs.lean`); `__muldi3`, `__udivdi3`, `__umoddi3`, `__divdi3`, `__moddi3` (`Libgcc.lean`; dc never calls the 32-bit `__divsi3`/`__udivsi3`/`__umodsi3`, so they have no spec); `HeapInv`, `malloc`/`free`, `realloc` (`HeapInv.lean`, `Malloc.lean`, `Realloc.lean`); the formatter against `Dc.Mach.fmt` (`FmtModel.lean`): `emit_unsigned_spec`, `fmt_loop`, `format_spec`, `vfprintf_spec`, `fprintf_spec` (to any stream; the console gains `fdOut fd (bytesStr (fmt ps args))`, so `stdout` prints and `stderr` only terminates and preserves memory outside the frame), `snprintf_spec` (`EmitSites.lean` … `Printf.lean`). Scope premises, checked against every call site: `%s` arguments are `.rodata` strings (`RoStr`); `fprintf`/`snprintf` take at most six/five register arguments (dc's formats take at most three) |
| M3 number representation | representation and heap closure checked: `NumAt.frame`, digit/normalization model, `BcHeap.foot_disjoint`, `.foot_not_alloc`, `.transport`, and `NewNumPost.insert`. Exact reference accounting depends on M9; zero-reference machine release is the M4 `bc_free_num` obligation. See the [closure ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#dc-number-heap-and-reference-release-obligations) for scope and suppliers |
| M4 allocation, comparison, small functions | done: `bc_new_num`, `bc_copy_num`, `bc_init_num`, `bc_compare` (and internal comparison), `bc_is_zero`, `bc_is_near_zero`, `bc_is_neg`, `bc_num2long`, `bc_free_num` (both reference arms and the `NULL` slot), `bc_init_numbers`, `bc_int2num`, `bc_out_long` (over the `CharCb` contract of its `out_char` argument). `_bc_rm_leading_zeros` has no out-of-line copy in the binary; each inlined copy is proved with its caller in M5–M7 |
| M5–M8 value models | done (`Dc/BcModel/`, no machine imports): digit-list values and the carry/borrow loops of `_bc_do_add`/`_bc_do_sub` tied to `Num.add`/`Num.sub` (`Digits.lean`, `Add.lean`); schoolbook columns and carry propagation of `_bc_simp_mul` (`Mul.lean`); `_one_mult`, the ripple loops of `_bc_shift_addsub`, the Karatsuba identity and the bound that the accumulator of `_bc_rec_mul` never overflows its `ulen + vlen + 1` digits (`Karatsuba.lean`); the Knuth quotient-digit guess (`guess ∈ {q, q+1}`) and long division (`Div.lean`); the truncated reads of `bc_multiply`/`bc_divide` tied to `Num.mul`/`Num.div` (`Result.lean`); `bc_raise`'s exact repeated squaring (`Raise.lean`); the base-10 bytes of `bc_out_num` and its integer-digit stack (`Out.lean`) |
| M5 addition and subtraction | `_bc_do_add` done (`bc_do_add_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m5-_bc_do_add-checked)); `_bc_do_sub` done (`bc_do_sub_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m5-_bc_do_sub-checked)); `bc_add`, `bc_sub` done (`bc_add_spec`, `bc_sub_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m5-bc_add-and-bc_sub-checked)) |
| M6 multiplication | heap prerequisite done: the number heap admits `new_sub_num` views and `bc_free_num`'s view arm is proved ([ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m6-prerequisite-number-views-in-the-heap-checked)); `_bc_shift_addsub` proved ([ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m6-_bc_shift_addsub-checked)); `_bc_rec_mul` proved at every size (`rm_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m6-_bc_rec_mul-checked)); `bc_multiply` proved against `Num.mul` (`bc_multiply_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m6-bc_multiply-checked)) |
| M7 division | done: `bc_divide` against `Num.div` (`bc_divide_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m7-bc_divide-checked)); `bc_divmod` against `Num.divmod` and `Num.modulo` (`bc_divmod_spec`, `bc_divmod_rem_spec`), `bc_modulo` against `Num.modulo` (`bc_modulo_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m7-bc_divmod-bc_modulo-checked)) |
| M8 powers, roots, output | `bc_raise` done (`bc_raise_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m8-bc_raise-checked)); `bc_raisemod` done (`bc_raisemod_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m8-bc_raisemod-checked)); `bc_sqrt` done (`bc_sqrt_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m8-bc_sqrt-checked)); `bc_out_num` done (`bc_out_num_spec`, [ledger](../experiments/smt/PROOF_CLOSURE_PLAN.md#m8-bc_out_num-checked)) |
| M9–M12 machine proofs | open |
