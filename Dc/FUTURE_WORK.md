# Future work: splitting `Dc.endToEnd` into a terminating and a diverging theorem

Status: proposal, not started. Written 2026-10-23 from the review thread on
`DcAdmissible` (review notes in the project thread). Nothing in the
repository has been changed for it. Branch `gnu-dc-semantics`, commit 43f7af6
at the time of the review.

## Motivation

`DcAdmissible` (`Dc/EndToEnd.lean`) has seven fields. Four of them
(`nest`, `leak`, `size`, `tail`) are `∀ n` bounds over fuel-indexed measures,
each backed by its own copy of `run`'s dispatch (`nestDepth`, `leakCount`,
`tailMax`, `AllCalls`) with its own monotonicity and stabilization lemmas.
The `∀ n` form exists only so the stuck direction can bound every finite
prefix of a diverging run. For terminating programs a far smaller premise
suffices, and the terminating theorem is a corollary of the existing one.

The plan is two headline theorems instead of one.

## Theorem 1: terminating programs, small premise

```lean
/-- A program that terminates within `dcK` commands, every `dc_func` call
meeting the SizeBound. -/
structure TermAdmissible (prog : List Nat) : Prop where
  prog : DcProg prog
  term : ∃ N ≤ dcK, ∃ x, run 70 N St.init ⟨prog, 1, false⟩ = some x
  size : AllCalls 70 (fun st c _ => CallP st c) dcK St.init ⟨prog, 1, false⟩

theorem endToEnd_term (prog : List Nat) (h : TermAdmissible prog) :
    ∃ out, Runs 70 prog out ∧
      (Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
      ∀ s, Halts (dcBoot prog) s 0 → s = outStr out
```

Proof sketch (one new file, nothing existing changes):

1. Three lemmas by mutual induction over `run`'s cases, same shape as
   `nestDepth_mono` (`Dc/Mach/EvalDivBudget.lean`):
   - `nestDepth lm n st f ≤ n`
   - `leakCount lm n st f ≤ n` (a literal step adds `numLeak ≤ 1` and
     `leakCmd` is `0` for digits, so at most one per fuel step)
   - `tailMax lm n st f ≤ f.td + n`
2. `TermAdmissible.toAdmissible : TermAdmissible prog → DcAdmissible prog`
   from those three and the existing `nestBound_of_run`, `leakBound_of_run`,
   `tailBound_of_run`, `allCalls_of_run` (`Dc/Mach/EvalStable.lean`), using
   `N ≤ dcK ≤ dcD` and `dcK + 1 < 2^31`.
3. `endToEnd_term` from `endToEnd`, `runOut_spec`/`run_iff` for the output
   and `Runs.det` (`Dc/Adequacy.lean`) for the last conjunct.

This is `Dc.capstone` (`Dc/Capstones.lean`) with a `Prop` premise instead
of `admCheck`, and `admCheck` becomes its decision procedure.

Why `size` stays: operand widths can grow doubly exponentially in few steps
(repeated squaring), so no step bound subsumes the SizeBound.

## Theorem 2: possibly diverging programs

The current `Dc.endToEnd` with the current `DcAdmissible`, unchanged. Its
content for a program with no terminating run is best stated directly:

```lean
theorem endToEnd_div (prog : List Nat) (h : DcAdmissible prog)
    (hno : ¬ ∃ out, Runs 70 prog out) :
    Diverges (dcBoot prog) ∨ ∃ s, Halts (dcBoot prog) s 1
```

This is `dc_stuck_sim` with the error status narrowed to 1. To check: that
`dc_stuck_loaded` yields `e = 1` rather than `e ≠ 0` (the only error exit
is `dc_memfail`). If it only gives `e ≠ 0`, keep that form.

What theorem 2 does and does not say for a diverging program: the binary
either runs forever or exits 1, and never exits 0; it says nothing about the
output printed while looping, because `Vsa.Machine.Diverges` carries no
output.

## Related improvements (independent of the split)

- Count leaks only on the routes where the binary loses a reference
  (`/ % ~` on a zero divisor, the register commands' error routes), not on
  every occurrence. Today any infinite loop containing a division or a
  fractional literal is inadmissible for theorem 2. Needs `leakAllow` and
  `FnPost.lk` to become route-sensitive.
- Raise the `2^20` handle slack in `EvAt.budget`/`FnPre.hsLen`.
  `DcAt.numRefs_lt` needs only `hs.length ≤ 2^30` and `G.lk.length ≤ 2^29`,
  so `dcK` could grow from `250000` to about `2^27`. `State.lean` changes
  rebuild about 50 modules.
- `Dc/PLAN.md` "The final theorem" still describes the old `LeakBound` and
  omits `size`, `tail` and the register commands in `leakAllow`; update it
  to present both theorems.
- Longer term: one instrumented `run` with a ghost `{depth, lost}`
  accumulator and a single `Safe` predicate over visited configurations
  would replace the four measure functions and their lemma families
  (the review in the project thread, alternative A).
