#!/usr/bin/env python3
"""Relocate a Gforth 1.0 image (.fi) offline, as engine/main.c's loader
(`gforth_loader` + `gforth_relocate`) does at start-up, for the
indirect-threaded engine without dynamic code (gforth-port/).

The loader's inputs other than the image are read from the linked ELF:
the primitive table `symbols.<n>` that `gforth_engine(NULL)` returns
(`vm_prims`), and the group table `groups`. The output is the image as the
loader leaves it in memory at address BASE: what `gforth_header` points to
when `gforth_boot` runs. gforth-port/Makefile links it at `gf_dict`.

    gen_gf_image.py ELF IMAGE.fi OUT.bin       relocate for ELF's `gf_dict`
    gen_gf_image.py ELF IMAGE.fi OUT.bin --check-elf
                                   also check that ELF's .gf_dict holds exactly that
    gen_gf_image.py ELF IMAGE.fi OUT.bin --base ADDR --check DUMP
                                   relocate for ADDR and compare with a memory
                                   dump of the real loader's image (from gdb at
                                   gforth_boot, in a build that runs gforth_loader)
    gen_gf_image.py --size IMAGE.fi            bytes of the relocated image
    gen_gf_image.py --free IMAGE.fi            dictionary bytes after it
"""
import argparse
import struct
import subprocess
import sys

CELL = 8
MASK = (1 << 64) - 1
SECTION_BITS = 8
PRIMSECTION = (1 << SECTION_BITS) - 1
DOCOL, DOER_MAX = 0, 9
CF_NIL = -1
PRIM_VERSION = 1          # engine/main.c
CFA_BYTE_OFFSET = 2 * CELL  # NEW_CFA (forth.h)


def s64(x):
    x &= MASK
    return x - (1 << 64) if x >> 63 else x


def section(x):
    return (x & MASK) >> (64 - SECTION_BITS)


def insection(x):
    return (x & MASK) & (MASK >> SECTION_BITS)


def cf(c):
    return -c - 2


class Elf:
    def __init__(self, path):
        self.data = open(path, "rb").read()
        out = subprocess.run(["riscv64-unknown-elf-readelf", "-SW", path],
                             capture_output=True, text=True, check=True).stdout
        self.sections = []
        for line in out.splitlines():
            f = line.replace("[ ", "[").split()
            if len(f) > 6 and f[0].startswith("[") and f[2] in ("PROGBITS", "NOBITS"):
                self.sections.append((f[1], f[2], int(f[3], 16), int(f[4], 16), int(f[5], 16)))
        out = subprocess.run(["riscv64-unknown-elf-nm", "-S", path],
                             capture_output=True, text=True, check=True).stdout
        self.syms = {}
        for line in out.splitlines():
            f = line.split()
            if len(f) == 4:
                self.syms[f[3]] = (int(f[0], 16), int(f[1], 16))
            elif len(f) == 3:     # no size (assembler labels)
                self.syms[f[2]] = (int(f[0], 16), 0)

    def sym(self, prefix):
        hits = [k for k in self.syms if k == prefix or k.startswith(prefix + ".")]
        assert len(hits) == 1, (prefix, hits)
        return self.syms[hits[0]]

    def read(self, addr, n):
        for name, kind, a, off, size in self.sections:
            if a <= addr and addr + n <= a + size:
                assert kind == "PROGBITS", name
                return self.data[off + addr - a: off + addr - a + n]
        raise KeyError(hex(addr))

    def cells(self, addr, n):
        return list(struct.unpack_from("<%dQ" % n, self.read(addr, 8 * n)))


def load_fi(path):
    """The image as gforth_loader reads it: the dictionary after the
    preamble, and its relocation bitmap."""
    d = open(path, "rb").read()
    pre = 0
    while d[pre:pre + 7] != b"Gforth6":
        pre += 8
    pre += 8
    hdr = struct.unpack_from("<4Q", d, pre)
    base, dp = hdr[0], hdr[2]
    size = dp - base
    image = list(struct.unpack_from("<%dQ" % (size // CELL), d, pre))
    rbytes = ((size - 1) // CELL) // 8 + 1
    bits = d[pre + size: pre + size + rbytes]
    assert d[pre + size + rbytes: pre + size + rbytes + 8] != b"Section.", \
        "images with extra sections are not supported"
    return base, size, image, bits


def relocate(elf, fi, at):
    base, size, image, bits = fi
    sym_addr, sym_size = elf.sym("symbols")
    vm_prims = elf.cells(sym_addr, sym_size // CELL)
    npriminfos = vm_prims.index(0)
    gaddr, gsize = elf.sym("groups")
    groups = elf.cells(gaddr, gsize // CELL)
    acc = 0
    for i in range(32):           # gforth_relocate: cumulative group table
        acc += groups[i]
        groups[i] = acc

    def cfa(n):                  # CFA(n), indirect threaded
        return sym_addr + CELL * (n & ~0x4000) + CFA_BYTE_OFFSET

    out = list(image)
    for k in range(len(bits)):
        for b in range(8):
            i = 8 * k + b
            if not (bits[k] >> (7 - b)) & 1:
                continue
            token = s64(image[i])
            if section(token) == PRIMSECTION:
                group = ((-token) & 0x3E00) >> 9
                if group == 0:
                    t = s64(token | 0x4000)
                    if t == CF_NIL:
                        out[i] = 0
                    elif cf(DOER_MAX) <= t <= cf(DOCOL):
                        out[i] = vm_prims[cf(token)]
                    elif cf(t) < npriminfos:
                        out[i] = cfa(cf(token)) & MASK
                    else:
                        raise ValueError("primitive %d not in this engine" % cf(token))
                else:
                    tok = (-token) & 0x1FF
                    assert tok < groups[group + 1] - groups[group], (i, token)
                    n = groups[group] + tok
                    out[i] = cfa(n)
                    if (token & 0x8000) == 0:      # special CFA
                        out[i] = vm_prims[n]
            elif token >= base:
                assert section(token) == 0, "extra sections not supported"
                out[i] = (at - base + insection(token)) & MASK
            elif token != 0:
                raise ValueError("unrelocated tagged item at cell %d" % i)
    out[0] = at                   # image[0] = (Cell)image
    if out[18] == 0:              # header.checksum: gforth_loader sets it
        out[18] = checksum(sym_addr, vm_prims)
    return out, sym_addr, vm_prims


def checksum(sym_addr, vm_prims):
    """engine/main.c checksum(), indirect threaded."""
    r = PRIM_VERSION
    for i in range(DOCOL, DOER_MAX + 1):
        r ^= vm_prims[i]
        r = ((r << 5) | (r >> 59)) & MASK
    return r ^ sym_addr


def main():
    if len(sys.argv) == 3 and sys.argv[1] in ("--size", "--free"):
        base, size, image, _ = load_fi(sys.argv[2])
        dict_size = image[1]
        print(size if sys.argv[1] == "--size" else dict_size - size)
        return 0
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("elf")
    ap.add_argument("image")
    ap.add_argument("out")
    ap.add_argument("--base", type=lambda s: int(s, 0))
    ap.add_argument("--check", metavar="DUMP")
    ap.add_argument("--check-elf", action="store_true")
    a = ap.parse_args()
    elf = Elf(a.elf)
    fi = load_fi(a.image)
    at = a.base if a.base is not None else elf.sym("gf_dict")[0]
    out, sym_addr, vm_prims = relocate(elf, fi, at)
    blob = struct.pack("<%dQ" % len(out), *out)
    open(a.out, "wb").write(blob)
    print("relocated %d cells at %#x" % (len(out), at))
    real = None
    if a.check:
        real = open(a.check, "rb").read()
    elif a.check_elf:
        real = elf.read(at, len(blob))
    if real is not None:
        assert len(real) >= len(blob), (len(real), len(blob))
        diffs = [i for i in range(len(out))
                 if blob[8 * i: 8 * i + 8] != real[8 * i: 8 * i + 8]]
        for i in diffs[:20]:
            print("cell %d (+%#x): ours %#x there %#x" % (
                i, 8 * i, out[i], struct.unpack_from("<Q", real, 8 * i)[0]))
        print("%d cells differ" % len(diffs))
        return 1 if diffs else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
