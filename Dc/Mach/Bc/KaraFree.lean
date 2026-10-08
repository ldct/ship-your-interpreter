import Dc.Mach.Bc.KaraHeap

/-!
# `_bc_rec_mul`'s inlined `bc_free_num` calls

The cleanup of the Karatsuba step frees `u1`, `u0`, `v1`, `m1`, `v0`, `m2`,
`m3`, `d1`, `d2`, each by an inlined `bc_free_num`: `n_refs` lowered; on the
last reference the buffer freed (owners) and the struct pushed on
`_bc_Free_list`.

- `KFreed`: the two outcomes on the number heap.
- `KFreeK`: the continuation at the next site.

The per-site lemmas are generated (`scripts/dc/gen_kara_free.py` →
`KaraFreeSites.lean`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- An inlined free of `x` (`L = L1 ++ x :: L2`): one reference fewer, or
the object released (its struct heads the dead chain). -/
inductive KFreed (H : Heap) (F : List Blk) (L1 L2 : List NumObj) (x : NumObj) :
    Heap → List Blk → List NumObj → Prop
  | dec : 2 ≤ x.rep.refs → KFreed H F L1 L2 x H F (L1 ++ x.decRef :: L2)
  | rel {H' : Heap} : x.rep.refs = 1 → KFreed H F L1 L2 x H' (x.sb :: F) (L1 ++ L2)

/-- The continuation after an inlined free at `pc`: the heap freed, every
byte off the heap and outside `fr` (the cleared pointer slot, if any)
unchanged. -/
def KFreeK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (pc : BitVec 64) (R0 : Nat → BitVec 64) (M0 : Mem) (fr : Nat → Prop) (H : Heap)
    (F : List Blk) (L1 L2 : List NumObj) (x : NumObj) : Prop :=
  ∀ R' M' H' F' L', Keeps [1, 10, 14, 15] R' R0 → KFreed H F L1 L2 x H' F' L' →
    BcHeap S M' H' F' L' → OutFrame fr M' M0 → DW live S Q pc R' M'

/-- A cleared pointer slot at `sa` (`bc_free_num (&m)` stores `NULL`): owned,
off the heap, inside the continuation's frame `fr`. -/
structure KSlot (S fr : Nat → Prop) (sa : Nat) : Prop where
  own : ∀ b ∈ accAddrs sa 8, S b
  out : ∀ a, sa ≤ a → a < sa + 8 → OutHeap a
  fr : ∀ a, sa ≤ a → a < sa + 8 → fr a
  al : sa % 8 = 0
  lo : 0x8001ad10 ≤ sa
  hi : sa + 8 ≤ 0x100000000

end Dc.Mach
