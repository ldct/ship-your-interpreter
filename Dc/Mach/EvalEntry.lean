import Dc.Mach.EvalLoop

/-!
# `evalstr`'s entry (M10)

`evalstr (string)` at `0x80001448`: the type check of `*string` (a string),
the prologue (`ra`, `s0`, `s1`, `s6`, `s8` saved, `interrupt_seen = 0`, the
text and its end from `dc_str2charp`/`dc_strlen`), then for an empty text the
return `DC_OKAY` (`0x800018f8`), else the rest of the prologue and the loop
head with `EvAt`: `EvEntrySpec n` from `LoopIH n` (`ev_entry`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **The entry's premises** (`EvalstrSpec`'s, at an evaluation of fuel `n`). -/
structure EvEntry (S : Nat → Prop) (sp W d k q : Nat) (M : Mem) (R : Nat → BitVec 64) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St)
    (o : StrObj) : Prop where
  len : o.s.length < 2 ^ 24
  sb : StrBound (2 ^ 24) st
  srt : ArrSorted st
  dc : DcAt S M H F L C G (xs ++ hs) st
  strIn : o ∈ G.strs
  held : hs.head? = some (.str o.hb.pay)
  slot : DatAt M q (.str o.hb.pay)
  slotPlace : DatSlot S sp q
  r2 : R 2 = BitVec.ofNat 64 sp
  r10 : R 10 = BitVec.ofNat 64 q
  al : (R 1).toNat % 4 = 0
  frame : StackFrame S sp W
  room : heapEnd + W ≤ sp
  stk : 176 * (d + 1) + 1216 + rmStack (2 ^ 30) ≤ W
  stkPr : 176 * (d + 1) + 192 + 336 + prN ≤ W
  stkDn : 176 * (d + 1) + 192 + 336 + dnN ≤ W
  budget : G.lk.length + xs.length + hs.length + 4 * k + d + 8 ≤ 2 ^ 20
  mb : MulBase S M
  err : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a
  globs : EvGlobs S M

/-- **`evalstr` at an evaluation completing at fuel `n`**, from the loop
at fuel `n` (`LoopIH`): the statement `ev_entry` proves. -/
def EvEntrySpec (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (n : Nat) : Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M : Mem) (R : Nat → BitVec 64) (H : Heap) (F : List Blk)
    (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st st' : St) (o : StrObj)
    (r : Status),
    EvFuel 70 n d k st ⟨o.s, 1, false⟩ st' r → EvEntry S sp W d k q M R H F L C G hs xs st o →
    EvOom live S Q sp W q M → EvK live S Q t0 sp W k q M R G hs xs st' r →
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001448#64 R M

end Dc.Mach
