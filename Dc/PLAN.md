# GNU dc: refinement proof plan

Target: `Dc.refinement` (`Dc/Refinement.lean`) at the layout of
`dc-port/dc-riscv-htif.elf`, i.e. a proof of `DcSim L` where `L.boot prog`
is the ELF's initial configuration (after the loader and `setupElf`) with
`prog` in the script buffer. Unlike WHILE, parsing is part of the dc
semantics (`Dc.Runs` reads program text), so the boundary is the ELF entry
and no boot-trace witness is needed.

## Statement decisions

- **Line length 70.** The ELF has no environment; `getenv` returns `NULL`.
- **Resources.** dc has no recursion budget: a program whose macro nesting
  exceeds the 8 MiB stack overwrites the heap. `L.admissible prog` carries a
  stack bound on every evaluation of `prog` (the analogue of WHILE's
  `stack_admissible`), stated over the semantics. Heap exhaustion makes
  `malloc` return `NULL` and dc exit with status 1 (`dc_memfail`); the
  statement either carries a capacity bound (WHILE's `capacity`) or weakens
  `term_sim` to "halts with `out` and status 0, or with status 1". Decide
  when the allocator spec is written.
- **The C library** is `dc-port/libc/` (written for verification), not
  newlib: 7,891 instructions in the ELF instead of 28,857.

## Layers

| Layer | Content | Status |
| --- | --- | --- |
| Semantics | `Dc/Num`, `Dc/Machine`, `Dc/Semantics`; interpreter sound, complete, deterministic (`Dc/Interp`, `Dc/Adequacy`); `Dc/Refinement` | done |
| Validation | `scripts/dc/difftest.py` (host dc), `scripts/dc/elf_difftest.py` (the ELF on `Vsa.runElf`), `Dc/Validation.lean` (generated, kernel-checked) | running |
| A. Decode | `Dc/Mach/DecodeTable/*` for the 2,749 words the WHILE table lacks (`scripts/dc/gen_dc_decode.py`) | generated, compiling |
| A. Steps | per-instruction step lemmas over `SWP` for the dc text (generator modelled on `scripts/gen_interp_steps.py`): ALU, loads (owned / read-only image), stores, branches, `j`, `ret`, `jal`, `jalr` calls, `jr` table jumps, `sltu`/`sltiu` (`swp_alu`), `lb` (new observed load step), HTIF putchar and exit | next |
| B. Program logic | CPS function specs over `SWPO` (continuation quantified), recursion by induction on `Dc.Loop` derivations; stuck direction by the fuel-indexed interpreter (`run n = none` ⇒ no clean halt within the corresponding machine steps) | |
| C. libc | `malloc`/`free`/`realloc` (first-fit list, bump pointer) with a heap invariant; `memcpy`, `memset`, `memchr`, `strchr`, `strlen`, `strncpy`; `fputc`/`putchar`/`fwrite`; `format`/`fprintf`/`snprintf` (`%s %c %#o %ld`) | |
| D. bc numbers | `NumRepr` (a `bc_struct` and its digit array) and specs of `bc_new_num`, `bc_free_num` (the `_bc_Free_list`), `_bc_rm_leading_zeros`, `_bc_do_compare`, `_bc_do_add`, `_bc_do_sub`, `bc_add`, `bc_sub`, `bc_multiply` (`_bc_rec_mul`, `_bc_simp_mul`, `_bc_shift_addsub`), `bc_divide` (`_one_mult`), `bc_divmod`, `bc_raise`, `bc_raisemod`, `bc_sqrt`, `bc_out_num`, `bc_num2long`, `bc_int2num`, against `Dc.Num` | |
| E. dc | representation of `Dc.St` (stack, 256 register stacks with arrays, strings); `stack.c`, `array.c`, `string.c`, `numeric.c`, `misc.c`; `dc_func` per command against `Dc.dcFunc`; `evalstr` against `Loop`/`Tos` | |
| F. Top | `_start` (`.bss` clear), `main` (`bc_init_numbers`, `dc_register_init`, `dc_makestring`), `flush_okay`, `exit`; `DcSim` for the layout; `Dc.refinement` instantiated | |
