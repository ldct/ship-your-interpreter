#!/usr/bin/env python3
"""Differential test of the Lean dc interpreter (`Dc.runOut`) against GNU dc.

Runs each program with `dc -e PROGRAM` (stdout only) and with the Lean
interpreter (`scripts/dc/DcRun.lean`), for several `DC_LINE_LENGTH` values,
and reports every byte-level difference. Programs on which GNU dc times out,
or the Lean interpreter runs out of fuel, are counted separately.

    python3 scripts/dc/difftest.py --olean DIR [--random N] [--seed S]

`--olean` is the directory holding the compiled `Dc` modules.
"""

import argparse
import os
import re
import random
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

# Hand-written cases: one feature or quirk each.
CASES = [
    "1 2+p", "5 3-p", "3 5-p", "_3 _5-p", "6 7*p", "7 2/p", "_7 2/p",
    "2k 7 3/p", "2k _7 3%p", "10 3~f", "10 _3~f", "5k 1 3/p 3*p",
    "1.5 2.25+p", "1.50 2.2-p", "1.5 1.5-p", "0.1 0.2*p", "2k 0.1 0.2*p",
    "1.234 5.6789*p", "3k 1.234 5.6789*p", "_1.5 2*p", "_.001 .001*p",
    "2 10^p", "2 _1^p", "0 _1^p", "2k 3 _2^p", "1.5 3^p", "_.1 3^p",
    "_1.5 3^p", "2 0^p", "2 0.5^p", "_2 3^p", "_2 4^p", "10k 1.1 20^p",
    "_.1 3^1^p", "_.1 3^2^p", "_.1 3^_1^p",
    "3 5 7|p", "2 10 1000|p", "4 13 497|p", "3 _1 7|f", "3 5 0|f",
    "2v p", "2k 2v p", "0.0001v p", "10k 1000000v p", "_4v f", "0v p",
    "1v p", "144v p", "20k 2v p", "0.25v p", "3k 0.5v p", "123456789v p",
    "5k 99.99v p", "1.00v p", "[s]v f",
    "1.p .5p 0.00p _0p _ 5p _.5p 1.50p", "007p 0.10p",
    "12345Zp .00012Zp 1.20Xp [abc]Zp [abc]Xp 0Zp 0.000Zp 100Xp",
    "1 2 3 3R f", "1 2 3 _3R f", "1 2 3 4 5 2R f", "1 2 r f", "1 r f",
    "1 2 3 10R f", "1 2 3 1R f", "1 2 3 0R f", "c f", "1 2 3 c f",
    "1dp d+p", "z p 1 2 z f", "[abc]p [a[b]c]p [a]n [b]n 10P",
    "97a P 3a P 256 1+P [xyz]a P []a P", "0P", "65P 16706P", "1.9P _66P",
    "300a P", "_1a P", "0.5a P",
    "2o 10p 0.5p 5.25p _6p", "16o 255p 3.75p 4095.5p", "20o 399p 1.5p",
    "100o 12345.678p", "3o 0.1p", "8o 64p", "1000o 123456789.5p",
    "2i 101p 1.1p 16i FFp A.8p", "16i 1F.Fp", "10i Ap Bp", "17i Ip 1i Ip",
    "2k Kp 0k Kp _1k Kp [x]k Kp", "Ip Op 1o Op [a]o Op", "0.5k Kp 2.9k Kp",
    "[9p]sa =a 1p", "=a 1p", "3 3=a", "[2p]sa 1 2<a 2 1<a 1 2>a 2 1>a",
    "[2p]sa 1 1!=a 1 2!=a 1 2!<a 2 1!<a 1 2!>a", "[y]sa 1 2 <a", "1 2<",
    "[1p]sa lax lax", "5sa lap lap", "la p", "5Sa 6Sa lap Lap Lap Lap f",
    "1 0:a 0;ap 5;ap 1;bp", "5:a lap", "[x]0:a lap Lap f", "7 3:a 3;ap 3;bp",
    "7 3:a 8 3:a 3;ap 9 1:a 1;ap 3;ap", "7 _1:a f", "7 [q]:a f", "1 2 3 4Sa 5 0:a 0;a p",
    "5 0:a 6Sa 0;ap La 0;ap", "4 1:r lr 0 1;r f",
    "[1p q 2p]x 3p", "[1p 1Q 2p]x 3p", "[1p 2Q 2p]x 3p",
    "[[1p 2Q 5p]x 2p]x 3p", "[[[1p 3Q]x 2p]x 3p]x 4p", "[1p 0Q 2p]x 3p",
    "[1p [z]Q 2p]x 3p", "q 1p", "1Q 2p", "2Q 3p",
    "[lax]sa 0 0Sb [ 1+ d 5>b]", "[d1+ d10>a]sa 0lax f",
    "[d p 1- d 0<a]sa 5 lax", "[1+d 100>a]sa 0 lax p",
    "[d 2% 0=e d1- d0<a]sa [d p]se 6 lax",
    "[lbx 1p]sa [2p q]sb lax 3p", "[lbx]sa [2Q]sb lax 3p",
    "[[3Q]x 1p]x 2p", "[[3Q]x]x 2p", "[3Q]x 2p",
    "# comment\n1p", "1 # c\n2 f", "[1p]x # c", "1p#", "[p]x",
    "y", "1 y 2 f", " ", "\t1\t2\tf", "\n1\n", "\r1p",
    "[x", "[ab", "[a]]p", "[[]]p", "l", "s", "S", ":", ";", "L", "<",
    "1 2 \\ f", "!echo hi\n1p", "1 2 !x", "? 1p", "[?]x 2p", "!<", "@ ` { } $ & ' ( ) , \" \x7f",
    "99999999999999999999999k Kp", "2 64^ 1-k Kp", "4294967297k Kp",
    "9223372036854775807k Kp", "9223372036854775808a P",
    "1 99999999999999999999^p",
    "20k 1 7/p 1 7/ 7*p", "1 3/ 3*p", "123.456 1000*p 123.456 _1000/p",
    "1234567890123456789012345678901234567890 987654321098765432109876543210*p",
    "2 200^p", "2 300^ 3 100^/p", "7 0/f", "7 0%f", "7 0~f", "7.00 0.0/f",
    "_0 _0+p", "_0 1*p", "0 _1*p", "_1 3/p", "3k _1 3/p",
]


def gen_number(rng: random.Random) -> str:
    kind = rng.random()
    if kind < 0.35:
        s = str(rng.randint(0, 20))
    elif kind < 0.55:
        s = str(rng.randint(0, 10**rng.randint(1, 30)))
    elif kind < 0.8:
        s = "%s.%s" % (rng.choice(["", "0", str(rng.randint(0, 999))]),
                       "".join(rng.choice("0123456789") for _ in range(rng.randint(0, 6))))
    else:
        s = "".join(rng.choice("0123456789ABCDEF") for _ in range(rng.randint(1, 4)))
    if rng.random() < 0.3:
        s = "_" + s
    return s


REGS = "abcxy"
SIMPLE = list("+-*/%~^|pnfcdrzIKOXZPa") + ["R", "v", "x"]


def gen_program(rng: random.Random, depth: int = 0) -> str:
    parts = []
    for _ in range(rng.randint(1, 14 if depth == 0 else 6)):
        r = rng.random()
        if r < 0.3:
            parts.append(gen_number(rng))
        elif r < 0.55:
            parts.append(rng.choice(SIMPLE))
        elif r < 0.62:
            parts.append(rng.choice(["k", "o", "i"]) if rng.random() < 0.5 else
                         rng.choice(["2k", "5k", "0k", "16o", "2o", "3o", "20o", "10o", "16i", "10i", "2i"]))
        elif r < 0.75:
            parts.append(rng.choice("slSL:;") + rng.choice(REGS))
        elif r < 0.85 and depth < 2:
            parts.append("[" + gen_program(rng, depth + 1) + "]")
        elif r < 0.92:
            parts.append(rng.choice(["", "!"]) + rng.choice("<=>") + rng.choice(REGS))
        elif r < 0.96:
            parts.append(rng.choice(["q", "Q", "1Q", "2Q", "3Q"]))
        else:
            parts.append(rng.choice(["#c\n", "\n", "\t", "y", "3 5 7|", "2v", "!ls\n", "?"]))
    return rng.choice([" ", "", " "]).join(parts)


def outside_host(prog: str) -> bool:
    """`!` runs a shell and `?` reads stdin on the host, unlike the model."""
    return "?" in prog or re.search(r"!(?![<=>])", prog) is not None


def run_dc(prog: str, lm: int, timeout: float):
    env = dict(os.environ, DC_LINE_LENGTH=str(lm))
    try:
        p = subprocess.run(["dc", "-e", prog], capture_output=True, env=env,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    return p.stdout


def run_lean(progs, lm: int, olean: str):
    data = b"".join(p.encode("latin-1") + b"\0" for p in progs)
    cmd = ["lake", "env", "sh", "-c",
           f'LEAN_PATH="{olean}:$LEAN_PATH" lean --run scripts/dc/DcRun.lean {lm}']
    p = subprocess.run(cmd, cwd=REPO, input=data, capture_output=True, check=True)
    lines = p.stdout.decode().splitlines()
    assert len(lines) == len(progs), (len(lines), len(progs), p.stderr.decode()[-2000:])
    return [None if l == "NONE" else bytes.fromhex(l) for l in lines]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--olean", required=True)
    ap.add_argument("--random", type=int, default=0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--timeout", type=float, default=2.0)
    ap.add_argument("--line-lengths", default="0,70,7")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    progs = CASES + [gen_program(rng) for _ in range(args.random)]
    # `!` (shell escape) and `?` (read stdin) are outside the model.
    progs = [p for p in progs if not outside_host(p)]
    failures = 0
    for lm in [int(x) for x in args.line_lengths.split(",")]:
        expected = [run_dc(p, lm, args.timeout) for p in progs]
        live = [p for p, e in zip(progs, expected) if e is not None]
        got = dict(zip(live, run_lean(live, lm, args.olean)))
        agree = timeouts = fuel = 0
        for p, e in zip(progs, expected):
            if e is None:
                timeouts += 1
                continue
            g = got[p]
            if g is None:
                fuel += 1
                print(f"[lm={lm}] NONE for {p!r} (dc: {e!r})")
                failures += 1
            elif g != e:
                failures += 1
                print(f"[lm={lm}] DIFF {p!r}\n   dc:   {e!r}\n   lean: {g!r}")
            else:
                agree += 1
        print(f"line length {lm}: {agree} agree, {failures} failing so far, "
              f"{timeouts} dc timeouts, {fuel} out of fuel/model, of {len(progs)}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
