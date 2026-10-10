#!/usr/bin/env bash
# check_dc_axioms.sh — the axiom audit of dc's headline theorems (Dc/PLAN.md
# M12): every function spec of the bc library (M3-M8), of dc's data and
# helpers (M9), the evaluator's cores (M10), boot/exit/out-of-memory (M11)
# and the end-to-end theorem (M12) depends on {propext, Classical.choice,
# Quot.sound} only.
#
# Usage: scripts/dc/check_dc_axioms.sh          (needs `lake build Dc`)
#
# Prints each `#print axioms` report and fails if any theorem depends on an
# axiom outside the allowed set, or is unknown. check_all.sh runs it as
# stage c4 when a Dc build is present.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2
THEOREMS=(
  Dc.endToEnd                                     # THE dc theorem (Dc/EndToEnd.lean), unconditional
  Dc.endToEnd_of_evalstr                          # the same from evalstr's two specifications
  Dc.refinement                                   # the generic composition (Dc/Refinement.lean)
  Dc.dc_term_sim
  Dc.dc_stuck_sim
  Dc.DcAdmissible.of_check                        # admissibility decided for a terminating program (Dc/Capstones.lean)
  Dc.capstone
  Dc.Mach.stable_succ                             # the budgets stabilize once run returns (EvalStable)
  Dc.Mach.size_of_run                             # the per-call premise computed (EvalCheck)
  Dc.Capstones.hello_halts
  Dc.Capstones.arith_halts
  Dc.Capstones.scale_halts
  Dc.Capstones.power_halts
  Dc.Capstones.sqrt_halts
  Dc.Capstones.printing_halts
  Dc.Capstones.length_halts
  Dc.Capstones.stack_halts
  Dc.Capstones.ascii_halts
  Dc.Capstones.obase_halts
  Dc.Capstones.ibase_halts
  Dc.Capstones.compare_halts
  Dc.Capstones.registers_halts
  Dc.Capstones.quit_halts
  Dc.Capstones.q2_halts
  Dc.Capstones.unimplemented_halts
  Dc.Capstones.loop_halts
  Dc.Capstones.fibonacci_halts
  Dc.Capstones.sqrt2_halts
  Dc.Capstones.bigmul_halts
  Dc.Capstones.wrap_halts
  Dc.sqrt_total                                   # bc_sqrt's Newton loop terminates (Dc/SqrtTotal.lean)
  Dc.Mach.sqOut_total
  Dc.evOomBoot                                    # evalstr's out-of-memory at the boot call
  Dc.Mach.bc_add_spec
  Dc.Mach.bc_compare_spec
  Dc.Mach.bc_copy_num_spec
  Dc.Mach.bc_divide_null_spec
  Dc.Mach.bc_divide_spec
  Dc.Mach.bc_divmod_rem_spec
  Dc.Mach.bc_divmod_spec
  Dc.Mach.bc_do_add_spec
  Dc.Mach.bc_do_sub_spec
  Dc.Mach.bc_free_num_spec
  Dc.Mach.bc_init_num_spec
  Dc.Mach.bc_init_numbers_spec
  Dc.Mach.bc_int2num_spec
  Dc.Mach.bc_is_near_zero_spec
  Dc.Mach.bc_is_neg_spec
  Dc.Mach.bc_is_zero_spec
  Dc.Mach.bc_modulo_spec
  Dc.Mach.bc_multiply_spec
  Dc.Mach.bc_new_num_spec
  Dc.Mach.bc_num2long_spec
  Dc.Mach.bc_out_long_spec
  Dc.Mach.bc_out_num_spec
  Dc.Mach.bc_raise_spec
  Dc.Mach.bc_raisemod_spec
  Dc.Mach.bc_shift_addsub_spec
  Dc.Mach.bc_sqrt_spec
  Dc.Mach.bc_sub_spec
  Dc.Mach.dc_add_spec
  Dc.Mach.dc_array_free_spec
  Dc.Mach.dc_array_get_spec
  Dc.Mach.dc_array_init_spec
  Dc.Mach.dc_array_set_spec
  Dc.Mach.dc_binop2_spec
  Dc.Mach.dc_binop_spec
  Dc.Mach.dc_clear_stack_spec
  Dc.Mach.dc_cmpop_spec
  Dc.Mach.dc_copy_spec
  Dc.Mach.dc_div_spec
  Dc.Mach.dc_divrem_spec
  Dc.Mach.dc_dump_num_spec
  Dc.Mach.dc_dup_num_spec
  Dc.Mach.dc_dup_spec
  Dc.Mach.dc_dup_str_spec
  Dc.Mach.dc_exp_spec
  Dc.Mach.dc_free_num_spec
  Dc.Mach.dc_free_str_spec
  Dc.Mach.dc_func_spec
  Dc.Mach.dc_getnum_spec
  Dc.Mach.dc_init_num_spec
  Dc.Mach.dc_int2data_spec
  Dc.Mach.dc_int2num_null_spec
  Dc.Mach.dc_int2num_spec
  Dc.Mach.dc_makestring_spec
  Dc.Mach.dc_malloc_spec
  Dc.Mach.dc_math_init_spec
  Dc.Mach.dc_memfail_spec
  Dc.Mach.dc_modexp_spec
  Dc.Mach.dc_mul_spec
  Dc.Mach.dc_num2int_spec
  Dc.Mach.dc_numlen_spec
  Dc.Mach.dc_out_num_spec
  Dc.Mach.dc_out_str_spec
  Dc.Mach.dc_pop_spec
  Dc.Mach.dc_print_spec
  Dc.Mach.dc_printall_spec
  Dc.Mach.dc_push_spec
  Dc.Mach.dc_readstring_spec
  Dc.Mach.dc_register_get_spec
  Dc.Mach.dc_register_init_spec
  Dc.Mach.dc_register_pop_spec
  Dc.Mach.dc_register_push_spec
  Dc.Mach.dc_register_set_spec
  Dc.Mach.dc_rem_spec
  Dc.Mach.dc_show_id_spec
  Dc.Mach.dc_sqrt_spec
  Dc.Mach.dc_stack_rotate_spec
  Dc.Mach.dc_string_init_spec
  Dc.Mach.dc_sub_spec
  Dc.Mach.dc_system_spec
  Dc.Mach.dc_tell_length_spec
  Dc.Mach.dc_tell_scale_spec
  Dc.Mach.dc_tell_stackdepth_spec
  Dc.Mach.dc_top_spec
  Dc.Mach.dc_triop_spec
  Dc.Mach.fprintf_prog_spec
  Dc.Mach.fprintf_spec
  Dc.Mach.one_mult_spec
  Dc.Mach.rm_spec
  Dc.Mach.rt_error_spec
  Dc.Mach.rt_warn_spec
  Dc.Mach.oom_memfail
  Dc.Mach.fnOom_memfail
  Dc.Mach.dc_halts
  Dc.Mach.dc_halts_wp
  Dc.Mach.dc_halts_loaded
  Dc.Mach.dc_halts_wp_loaded
  Dc.Mach.dc_stuck
  Dc.Mach.dc_stuck_loaded
  Dc.Mach.dcBoot_loaded
  Dc.Mach.evalstr_spec
  Dc.Mach.evalstrDiv_of_term
  Dc.Mach.ev_entry_k
  Dc.Mach.evs_int_k
  Dc.Mach.evs_str_k
)
AXFILE="$(mktemp /tmp/dc_axioms.XXXXXX)".lean
mv "${AXFILE%.lean}" "$AXFILE"
{
  echo "import Dc"
  for t in "${THEOREMS[@]}"; do echo "#print axioms $t"; done
} > "$AXFILE"
OUT="$(lake env lean "$AXFILE" 2>&1)"; STATUS=$?
rm -f "$AXFILE"
[ "$STATUS" -eq 0 ] || { echo "$OUT"; echo "check_dc_axioms: lean failed" >&2; exit 1; }
AX_OUT="$OUT" AX_NAMES="$(printf '%s\n' "${THEOREMS[@]}")" python3 - <<'PYEOF'
import os, re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
out = re.sub(r"\n[ \t]+", " ", os.environ["AX_OUT"])
names = set(os.environ["AX_NAMES"].split()); seen = set(); bad = []
for line in out.splitlines():
    m = re.search(r"'(.*)' depends on axioms: \[([^\]]*)\]", line)
    if m:
        seen.add(m.group(1))
        extra = {a.strip() for a in m.group(2).split(",") if a.strip()} - allowed
        if extra: bad.append(f"{m.group(1)}: disallowed axioms {sorted(extra)}")
        continue
    m = re.search(r"'(.*)' does not depend on any axioms", line)
    if m:
        seen.add(m.group(1)); continue
    if re.search(r"\berror\b", line, re.I):
        bad.append(f"lean error: {line.strip()}")
if seen != names: bad.append(f"missing reports for {sorted(names - seen)}")
print(f"check_dc_axioms: {len(seen)}/{len(names)} theorems audited, allowed = {sorted(allowed)}")
if bad:
    print("\n".join(bad), file=sys.stderr); sys.exit(1)
PYEOF
