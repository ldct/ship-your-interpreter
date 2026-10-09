import Dc.Mach.Bc.KaraFree

/-!
# Inlined `bc_free_num` on a register, `_bc_Free_list` by `auipc`

Outside `_bc_rec_mul`, an inlined `bc_free_num (&n)` on a register `r`
reads `_bc_Free_list` through `auipc` instead of a saved base register:

    [beqz r, Nn]                     -- optional null test
    lw a5,12(r); addiw a5,a5,-1; sw a5,12(r); bnez a5, Nd
    ld a0,24(r); beqz a0, Uv         -- (or bnez a0, J)
    J: jal free
    U: auipc a5; ld a5,_bc_Free_list; auipc a4; sd r,_bc_Free_list; sd a5,16(r)

- `FreeK cl`: the continuation, `KFreeK` with the clobbered registers `cl`
  (the site may interleave a register write, e.g. `li s4,0` in `bc_divmod`).

The per-site lemmas are generated (`scripts/dc/gen_bc_free.py` →
`FreeSites.lean`): `ffree_<P0>` takes one continuation per route (the
decrement at `Nd`, a view at `Nv`, an owner at `No`); `fnull_<P0>` is the
null route.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The continuation at `pc` after an inlined free of `x` that may clobber
the registers `cl`: the heap freed, every byte off the heap and outside `fr`
unchanged. -/
def FreeK (cl : List Nat) (live S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (pc : BitVec 64) (R0 : Nat → BitVec 64) (M0 : Mem) (fr : Nat → Prop) (H : Heap)
    (F : List Blk) (L1 L2 : List NumObj) (x : NumObj) : Prop :=
  ∀ R' M' H' F' L', Keeps cl R' R0 → KFreed H F L1 L2 x H' F' L' →
    BcHeap S M' H' F' L' → OutFrame fr M' M0 → DW live S Q pc R' M'

/-- A continuation accepting more clobbered registers serves fewer. -/
theorem FreeK.mono {cl cl' : List Nat} {live S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64}
    {R0 : Nat → BitVec 64} {M0 : Mem} {fr : Nat → Prop} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (hk : FreeK cl' live S Q pc R0 M0 fr H F L1 L2 x)
    (hs : ∀ z ∈ cl, z ∈ cl') : FreeK cl live S Q pc R0 M0 fr H F L1 L2 x :=
  fun R' M' H' F' L' hkp => hk R' M' H' F' L' (hkp.mono hs)

end Dc.Mach
