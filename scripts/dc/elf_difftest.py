#!/usr/bin/env python3
"""Compare the RISC-V dc binary on the proof's machine model with the Lean
semantics of dc.

For every program of the corpus (the hand-written cases and random programs
of difftest.py), runs

* `dc-port/dc-riscv-htif.elf` on the Sail RV64 model through `Vsa.runElf`
  (scripts/dc/DcElfRun.lean), with the program patched into the ELF's
  script buffer, and
* the Lean interpreter `Dc.runOut` at line length 70 (the ELF has no
  environment, so `DC_LINE_LENGTH` is unset and dc uses 70),
* optionally host GNU dc (`--host-dc`),

and reports every difference in console output, and any nonzero exit code.

    python3 scripts/dc/elf_difftest.py --vsa-olean DIR --dc-olean DIR \
        [--random N] [--seed S] [--jobs J] [--fuel STEPS]
"""

import argparse
import concurrent.futures
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import difftest  # noqa: E402

REPO = Path(__file__).resolve().parents[2]
ELF = "dc-port/dc-riscv-htif.elf"


def run_elf_shard(progs, olean, fuel):
    data = b"".join(p.encode("latin-1") + b"\0" for p in progs)
    cmd = ["lake", "env", "sh", "-c",
           f'LEAN_PATH="{olean}:$LEAN_PATH" lean --run scripts/dc/DcElfRun.lean {ELF} {fuel}']
    p = subprocess.run(cmd, cwd=REPO, input=data, capture_output=True, check=True)
    lines = [l for l in p.stdout.decode().splitlines() if l != "TODO: cancel_reservation"]
    assert len(lines) == len(progs), (len(lines), len(progs), p.stderr.decode()[-2000:])
    out = []
    for l in lines:
        f = l.split(" ")
        if f[0] in ("FUEL", "ERROR"):
            out.append((f[0], None, None))
        else:
            out.append((int(f[0]), int(f[1]), bytes.fromhex(f[2]) if len(f) > 2 else b""))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--vsa-olean", required=True)
    ap.add_argument("--dc-olean", required=True)
    ap.add_argument("--random", type=int, default=0)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--fuel", type=int, default=2_000_000)
    ap.add_argument("--host-dc", action="store_true")
    args = ap.parse_args()

    rng = difftest.random.Random(args.seed)
    progs = difftest.CASES + [difftest.gen_program(rng) for _ in range(args.random)]
    progs = [p for p in progs
             if "?" not in p and not difftest.re.search(r"!(?![<=>])", p)]
    progs = list(dict.fromkeys(progs))

    lean = difftest.run_lean(progs, 70, args.dc_olean)
    shards = [progs[i::args.jobs] for i in range(args.jobs)]
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
        results = list(ex.map(lambda s: run_elf_shard(s, args.vsa_olean, args.fuel), shards))
    elf = {}
    for shard, res in zip(shards, results):
        elf.update(zip(shard, res))

    agree = fuel = model = host_diff = 0
    failures = 0
    steps = []
    for p, want in zip(progs, lean):
        code, n, got = elf[p]
        if code == "FUEL":
            fuel += 1
            continue
        if code == "ERROR":
            failures += 1
            print(f"ERROR {p!r}")
            continue
        if want is None:
            model += 1
            print(f"outside the model or out of Lean fuel: {p!r} (elf: {got!r})")
            continue
        steps.append(n)
        if code != 0 or got != want:
            failures += 1
            print(f"DIFF {p!r}\n   elf:  exit {code} {got!r}\n   lean: {want!r}")
            continue
        agree += 1
        if args.host_dc:
            host = difftest.run_dc(p, 70, 5.0)
            if host is not None and host != got:
                host_diff += 1
                print(f"HOST DIFF {p!r}\n   host: {host!r}\n   elf:  {got!r}")
    print(f"{agree} agree, {failures} differ, {fuel} over {args.fuel} steps, "
          f"{model} outside the Lean model, of {len(progs)} programs")
    if steps:
        steps.sort()
        print(f"machine steps: min {steps[0]}, median {steps[len(steps)//2]}, max {steps[-1]}")
    if args.host_dc:
        print(f"host dc differences: {host_diff}")
    return 1 if failures or host_diff else 0


if __name__ == "__main__":
    sys.exit(main())
