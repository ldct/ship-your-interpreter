import Dc.Mach.EvalEntry

/-!
# `evalstr`'s loop: continuation-generic case statements (M10)

The status cases after `dc_func` returned (`EvCall`), stated over their
continuations instead of the fuel and the caller's `EvK`: `EvHeadK` (the
loop head with the invariant over the next frame) and `EvEndK` (the loop's
exit `0x8000156c` with the invariant). The term direction instantiates them
with `LoopIH` and `ev_exit`; the stuck direction with its own end
conditions. `EvIntCore`/`EvStrCore`: `DC_INT` and `DC_STR` in this shape.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **The loop head with the invariant** over the next state `st'` and a
frame `f'` (nonempty) with the budget `k'`: any ghost `G2` and lost strings `xs2`
whose leaks fit the activation's (`G`, `xs`, `k` before the command), the
caller's strings pinned. -/
def EvHeadK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W d k k' q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (G : DcG)
    (hs xs : List GV) (st' : St) (f' : Frame) : Prop :=
  ∀ (R2 : Nat → BitVec 64) (M2 : Mem) (H2 : Heap) (F2 : List Blk) (L2 : List NumObj)
    (C2 : BcConsts) (G2 : DcG) (xs2 : List GV) (o' : StrObj),
    EvAt S sp W d k' q M0 R0 R2 M2 H2 F2 L2 C2 G2 hs xs2 st' f' o' → R2 12 = boolWord f'.neg →
    f'.s ≠ [] → G2.lk.length + xs2.length + 4 * k' ≤ G.lk.length + xs.length + 4 * k →
    StrPin G.strs G2.strs hs.tail →
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x800014f8#64 R2 M2

/-- **The loop's exit** (`0x8000156c`, `DC_OKAY` with the state `st'`) when
the next frame `f'` is empty, from the invariant over any frame. -/
def EvEndK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (G : DcG)
    (hs xs : List GV) (st' : St) (f' : Frame) : Prop :=
  f'.s = [] →
  ∀ k' (R2 : Nat → BitVec 64) (M2 : Mem) (H2 : Heap) (F2 : List Blk) (L2 : List NumObj)
    (C2 : BcConsts) (G2 : DcG) (xs2 : List GV) (f'' : Frame) (o' : StrObj),
    EvAt S sp W d k' q M0 R0 R2 M2 H2 F2 L2 C2 G2 hs xs2 st' f'' o' →
    G2.lk.length + xs2.length + 4 * k' ≤ G.lk.length + xs.length + 4 * k →
    StrPin G.strs G2.strs hs.tail →
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x8000156c#64 R2 M2

/-- **`DC_INT`** (status `5`): the number read pushed, on to the rest after it. -/
def EvIntCore (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St) (c : Nat)
    (rest : List Nat) (td : Nat) (neg : Bool) (o : StrObj) (Rc R' : Nat → BitVec 64) (Mc M' : Mem)
    (H' : Heap) (F' : List Blk) (L' : List NumObj) (C' : BcConsts) (G' : DcG) (ex : List GV),
    EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C' G'
      st ex →
    dcFunc 70 st c rest.head? neg = .int → R' 10 = BitVec.ofNat 64 5 → leakOne c ≤ k →
    EvOom live S Q sp W q M0 →
    EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs
      (st.push (.num (readNum st.ibase (c :: rest)).1)) ⟨(readNum st.ibase (c :: rest)).2, td, false⟩ →
    EvEndK live S Q t0 sp W d k q M0 R0 G hs xs (st.push (.num (readNum st.ibase (c :: rest)).1))
      ⟨(readNum st.ibase (c :: rest)).2, td, false⟩ →
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M'

/-- **`DC_STR`** (status `6`): the bracketed string pushed, on to the rest
after it. -/
def EvStrCore (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St) (c : Nat)
    (rest : List Nat) (td : Nat) (neg : Bool) (o : StrObj) (Rc R' : Nat → BitVec 64) (Mc M' : Mem)
    (H' : Heap) (F' : List Blk) (L' : List NumObj) (C' : BcConsts) (G' : DcG) (ex : List GV),
    EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C' G'
      st ex →
    dcFunc 70 st c rest.head? neg = .str → R' 10 = BitVec.ofNat 64 6 → leakOne c ≤ k →
    EvOom live S Q sp W q M0 →
    EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs
      (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩ →
    EvEndK live S Q t0 sp W d k q M0 R0 G hs xs (st.push (.str (scanStr 1 rest).1))
      ⟨(scanStr 1 rest).2, td, false⟩ →
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M'

end Dc.Mach
