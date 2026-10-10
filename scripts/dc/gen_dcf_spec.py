#!/usr/bin/env python3
"""Generate `dc_func`'s per-character contract lemmas and their case split.

For each character `c` in `9..126` whose arm is proved, `dcf_<c>` joins the
dispatch `dcf_disp_<c>` (`DcFuncDisp.lean`) with the arm `fa_*` at the table
target of `c` through `fn_arm` (`DcFuncSpecBase.lean`), under the bundled
premises `FnPre`/`FnRegs`. `DcFuncSpec.lean` collects them: `fnDone` lists the
characters covered, `dc_func_spec_done` is the contract for each of them and
for every character outside the table (`dcf_out`); once every arm is in,
`dc_func_spec` is the contract for every character.

An arm is used when its theorem is on `HEAD` in the module named in `ARMS`
and `Dc.lean` imports that module (agent B's `DcFuncArmR*` arms plug in as
they are integrated); rerun the generator after an arm lands.

Output (do not hand-edit): `Dc/Mach/DcFuncSpec{1,2,3,B}.lean`, `Dc/Mach/DcFuncSpec.lean`
(`DcFuncSpecB` holds the characters whose arms are in `DcFuncArmR*`).

    python3 scripts/dc/gen_dcf_spec.py [--check]
"""
import pathlib
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import gen_dcf_disp  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[2]

# Argument abbreviations.
W = "(by have := hp.stk; have := hp.stkPr; have := hp.stkDn; omega)"
HS = "(by have := hp.hsLen; omega)"
OP = f"hlive h hc {W} ho hp.mb"

# Table target -> (module, theorem, arguments after the theorem name).
ARMS = {
    0x80000C10: ("Dc.Mach.DcFuncArm0", "fa_ws", "hlive (c := {c}) (by decide) h hc hk"),
    0x80000C20: ("Dc.Mach.DcFuncArm0", "fa_int", "hlive (c := {c}) rfl h hc hk"),
    0x80000C30: ("Dc.Mach.DcFuncArmV4", "fa_default", f"hlive rfl (by decide) h hc {W} e13 hk"),
    0x80000C6C: ("Dc.Mach.DcFuncArm2", "fa_rem", f"{OP} hp.size.rem {HS} hp.lkLen (by decide) hk"),
    0x80000C84: ("Dc.Mach.DcFuncArm0", "fa_hash", "hlive h hc hk"),
    0x80000C8C: ("Dc.Mach.DcFuncArm0", "fa_bang", "hlive h hc e11 hp.pk hk"),
    0x80000CA4: ("Dc.Mach.DcFuncArm1", "fa_K", f"hlive h hc {W} ho {HS} hk"),
    0x80000CB8: ("Dc.Mach.DcFuncArm1", "fa_I", f"hlive h hc {W} ho {HS} hk"),
    0x80000CCC: ("Dc.Mach.DcFuncArmV3", "fa_query", f"hlive h hc {W} ho hp.laOwn (hp.laArm _) hk"),
    0x80000D30: ("Dc.Mach.DcFuncArm0", "fa_x", "hlive h hc hk"),
    0x80000D38: ("Dc.Mach.DcFuncArmR2", "fa_gt", f"hlive h hc {W} e11 e12 hp.pk hk"),
    0x80000D64: ("Dc.Mach.DcFuncArmR2", "fa_eq", f"hlive h hc {W} e11 e12 hp.pk hk"),
    0x80000D90: ("Dc.Mach.DcFuncArmR2", "fa_lt", f"hlive h hc {W} e11 e12 hp.pk hk"),
    0x80000DC0: ("Dc.Mach.DcFuncArmR4", "fa_semi", f"hlive h hc {W} ho {HS} (by decide) e11 hp.pk hp.srt hk"),
    0x80000E08: ("Dc.Mach.DcFuncArmR4", "fa_colon", f"hlive h hc {W} ho (by decide) e11 hp.pk hk"),
    0x80000E40: ("Dc.Mach.DcFuncArmR1", "fa_k", f"hlive h hc {W} (by decide) hk"),
    0x80000E78: ("Dc.Mach.DcFuncArmR1", "fa_i", f"hlive h hc {W} (by decide) hk"),
    0x80000EB4: ("Dc.Mach.DcFuncArmV6", "fa_f", f"{OP} {HS} hp.size.all hp.err hk"),
    0x80000EC4: ("Dc.Mach.DcFuncArmR3", "fa_s", f"hlive h hc {W} ho e11 hp.pk hk"),
    0x80000EF4: ("Dc.Mach.DcFuncArmV1", "fa_r", "hlive h hc hk"),
    0x80000F00: ("Dc.Mach.DcFuncArm0", "fa_q", "hlive h hc hk"),
    0x80000F1C: ("Dc.Mach.DcFuncArm1", "fa_O", f"hlive h hc {W} ho {HS} hk"),
    0x80000F30: ("Dc.Mach.DcFuncArmR3", "fa_L", f"hlive h hc {W} ho e11 hp.pk hk"),
    0x80000F5C: ("Dc.Mach.DcFuncArmV8", "fa_a", f"hlive h hc {W} ho hk"),
    0x80000FA0: ("Dc.Mach.DcFuncArm2", "fa_exp", f"{OP} hp.size.exp {HS} hp.lkLen hk"),
    0x80000FB8: ("Dc.Mach.DcFuncArmV7", "fa_Z", f"hlive h hc {W} ho {HS} hk"),
    0x80000FE0: ("Dc.Mach.DcFuncArmV1", "fa_X", f"hlive h hc {W} ho {HS} (by decide) hk"),
    0x80001008: ("Dc.Mach.DcFuncArmR3", "fa_S", f"hlive h hc {W} ho e11 hp.pk hk"),
    0x80001038: ("Dc.Mach.DcFuncArmR2", "fa_R", f"hlive h hc {W} (by decide) hk"),
    0x80001058: ("Dc.Mach.DcFuncArmR1", "fa_Q", f"hlive h hc {W} (by decide) hk"),
    0x800010A8: ("Dc.Mach.DcFuncArm2", "fa_add", f"{OP} {HS} hp.lkLen hk"),
    0x800010C0: ("Dc.Mach.DcFuncArm2", "fa_div", f"{OP} hp.size.div {HS} hp.lkLen (by decide) hk"),
    0x800010D8: ("Dc.Mach.DcFuncArm2", "fa_sub", f"{OP} {HS} hp.lkLen hk"),
    0x800010F0: ("Dc.Mach.DcFuncArmR1", "fa_o", f"hlive h hc {W} (by decide) hk"),
    0x80001128: ("Dc.Mach.DcFuncArmV6", "fa_n", f"{OP} {HS} hp.size.top hp.err hk"),
    0x80001154: ("Dc.Mach.DcFuncArmV5", "fa_c", f"hlive h hc {W} hk"),
    0x8000115C: ("Dc.Mach.DcFuncArmV6", "fa_p", f"{OP} {HS} hp.size.top hp.err hk"),
    0x80001188: ("Dc.Mach.DcFuncArmV5", "fa_d", f"hlive h hc {W} ho {HS} hk"),
    0x800011A8: ("Dc.Mach.DcFuncArm2", "fa_modexp", f"{OP} hp.size.modexp {HS} hp.lkLen (by decide) hk"),
    0x800011C0: ("Dc.Mach.DcFuncArm1", "fa_z", f"hlive h hc {W} ho {HS} hk"),
    0x800011D0: ("Dc.Mach.DcFuncArm2", "fa_mul", f"{OP} {HS} hp.lkLen hk"),
    0x800011E8: ("Dc.Mach.DcFuncArmV2", "fa_v", f"{OP} {HS} hp.lkLen (by decide) hp.size.sqOut hp.size.sqrt hk"),
    0x80000BD4: ("Dc.Mach.DcFuncArmV7", "fa_P", f"{OP} {HS} hp.size.top hk"),
    0x80001220: ("Dc.Mach.DcFuncArmR3", "fa_l", f"hlive h hc {W} ho {HS} e11 hp.pk hk"),
    0x80001240: ("Dc.Mach.DcFuncArm2", "fa_divrem", f"{OP} hp.size.rem {HS} hp.lkLen (by decide) hk"),
    0x80001258: ("Dc.Mach.DcFuncArm0", "fa_lbrack", "hlive h hc hk"),
}

# The characters per generated module.
PARTS = [range(9, 48), range(48, 91), range(91, 127)]


def head(path):
    r = subprocess.run(["git", "show", f"HEAD:{path}"], cwd=ROOT, capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""


DC_IMPORTS = head("Dc.lean")


def landed(module, thm):
    """The theorem is on `HEAD` in the module, and `Dc.lean` imports the module
    (the integrator's mark that it compiles)."""
    path = module.replace(".", "/") + ".lean"
    return f"import {module}\n" in DC_IMPORTS and f"theorem {thm} " in head(path)


def arm(c):
    _, _, tgt = gen_dcf_disp.entry(c)
    module, thm, args = ARMS[tgt]
    if args is None or not landed(module, thm):
        return None
    return tgt, module, thm, args.format(c=c)


HEAD = """{imports}

/-!
# `dc_func`'s contract per character, part {n} (generated by `scripts/dc/gen_dcf_spec.py`; do not edit)

`dcf_<c>`: from `dc_func`'s entry with `a0 = c` under `FnPre`/`FnRegs`, the
dispatch `dcf_disp_<c>` joined with the arm of `c` (`fn_arm`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

"""

LEMMA = """theorem dcf_{c} {{live S : Nat → Prop}} {{Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}}
    (hlive : ∀ p ∈ dcText, live p.1) {{t0 : String}} {{sp W : Nat}} {{M : Mem}} {{H : Heap}}
    {{F : List Blk}} {{L : List NumObj}} {{C : BcConsts}} {{G : DcG}} {{hs : List GV}} {{st : St}}
    {{peek : Option Nat}} {{neg : Bool}} {{R : Nat → BitVec 64}}
    (hp : FnPre S sp W M H F L C G hs st {c} peek) (hr : FnRegs R sp {c} peek neg)
    (ho : FnOom live S Q sp W M)
    (hk : FnK live S Q (leakAllow {c}) t0 st (dcFunc 70 st {c} peek neg) G hs sp W M R) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000b9c#64 R M :=
  fn_arm hp hr (dcf_disp_{c} hlive hp.heapOwn (hp.frame.mono {W})
    (by have := hp.room; have := hp.stk; omega) R hr.r2 hr.r10)
    fun R' hc h e11 e12 e13 => {thm} {args}

"""


def render_part(n, cs):
    mods = sorted({"Dc.Mach.DcFuncSpecBase"} | {a[1][1] for a in cs})
    parts = [HEAD.format(imports="\n".join(f"import {m}" for m in mods), n=n)]
    for c, (tgt, module, thm, args) in cs:
        parts.append(LEMMA.format(c=c, thm=thm, args=args, W=W))
    parts.append("end Dc.Mach\n")
    return "".join(parts)


FINAL = """{imports}

/-!
# `dc_func`'s contract (generated by `scripts/dc/gen_dcf_spec.py`; do not edit)

`fnDone`: the characters of `9..126` whose arms are proved. `dc_func_spec_done`:
for each of them, and for every character outside the table, `dc_func` run
from its entry under `FnPre`/`FnRegs` continues as the caller's `FnK` for
`dcFunc 70 st c peek neg` (or reaches `dc_memfail`, `FnOom`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The characters of `9..126` whose `dc_func` arm is proved. -/
def fnDone : List Nat := {done}

/-- **`dc_func (c, peekc, negcmp)`** at `0x80000b9c` for `c` in `fnDone` or
outside the table. -/
theorem dc_func_spec_done {{live S : Nat → Prop}}
    {{Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}}
    (hlive : ∀ p ∈ dcText, live p.1) {{t0 : String}} {{sp W : Nat}} {{M : Mem}} {{H : Heap}}
    {{F : List Blk}} {{L : List NumObj}} {{C : BcConsts}} {{G : DcG}} {{hs : List GV}} {{st : St}}
    {{c : Nat}} {{peek : Option Nat}} {{neg : Bool}} {{R : Nat → BitVec 64}}
    (hc : c ∈ fnDone ∨ c < 9 ∨ 126 < c)
    (hp : FnPre S sp W M H F L C G hs st c peek) (hr : FnRegs R sp c peek neg)
    (ho : FnOom live S Q sp W M)
    (hk : FnK live S Q (leakAllow c) t0 st (dcFunc 70 st c peek neg) G hs sp W M R) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000b9c#64 R M := by
  rcases hc with hc | hout
  · simp only [fnDone, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with {pat}
    {cases}
  · exact dcf_out hlive hp hr hout hk
{full}
end Dc.Mach
"""

FULL = """
/-- **`dc_func (c, peekc, negcmp)`** at `0x80000b9c`, every character. -/
theorem dc_func_spec {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {sp W : Nat} {M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {c : Nat} {peek : Option Nat} {neg : Bool} {R : Nat → BitVec 64}
    (hp : FnPre S sp W M H F L C G hs st c peek) (hr : FnRegs R sp c peek neg)
    (ho : FnOom live S Q sp W M)
    (hk : FnK live S Q (leakAllow c) t0 st (dcFunc 70 st c peek neg) G hs sp W M R) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000b9c#64 R M :=
  dc_func_spec_done hlive (by
    by_cases h : 9 ≤ c ∧ c ≤ 126
    · have hall : ∀ c, c < 127 → 9 ≤ c → c ∈ fnDone := by decide +kernel
      exact .inl (hall c (by omega) h.1)
    · exact .inr (by omega)) hp hr ho hk
"""


def render():
    done = {c: arm(c) for c in range(9, 127)}
    done = {c: a for c, a in done.items() if a is not None}
    out = {}
    names = []
    def own(a):
        return not a[1].startswith("Dc.Mach.DcFuncArmR")
    for i, rng in enumerate(PARTS, 1):
        cs = [(c, done[c]) for c in rng if c in done and own(done[c])]
        name = f"DcFuncSpec{i}"
        names.append(name)
        out[ROOT / f"Dc/Mach/{name}.lean"] = render_part(i, cs)
    cs = [(c, done[c]) for c in sorted(done) if not own(done[c])]
    names.append("DcFuncSpecB")
    out[ROOT / "Dc/Mach/DcFuncSpecB.lean"] = render_part("B (the arms of `DcFuncArmR*`)", cs)
    keys = sorted(done)
    pat = " | ".join("rfl" for _ in keys)
    cases = "\n    ".join(f"· exact dcf_{c} hlive hp hr ho hk" for c in keys)
    full = FULL if len(keys) == 126 - 9 + 1 else ""
    out[ROOT / "Dc/Mach/DcFuncSpec.lean"] = FINAL.format(
        imports="\n".join(f"import Dc.Mach.{n}" for n in names),
        done="[" + ", ".join(map(str, keys)) + "]", pat=pat, cases=cases, full=full)
    return out


def main():
    out = render()
    if "--check" in sys.argv:
        stale = [p for p, t in out.items() if not p.exists() or p.read_text() != t]
        if stale:
            sys.exit("stale: " + ", ".join(map(str, stale)) + f"; rerun {__file__}")
        return
    for p, t in out.items():
        p.write_text(t)


if __name__ == "__main__":
    main()
