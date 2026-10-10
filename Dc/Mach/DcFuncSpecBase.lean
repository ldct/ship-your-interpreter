import Dc.Mach.DcFuncArmV8
import Dc.Mach.DcFuncDisp
import Dc.Mach.EvalLeak

/-!
# `dc_func`'s contract: premises and the per-arm join (M10)

`FnPre`: what `dc_func (c, peekc, negcmp)` needs at its entry, the union of
its arms' premises: the state, the stack frame (`stk` covers the deepest arm),
the handle and lost-reference counts, `mul_base_digits` (`MulBase`), `errno`'s
and `stdin_lookahead`'s bytes (`out_char`'s first call clears `errno`; `?`
reads `stdin_lookahead`, which holds `EOF`), and the operand sizes of the
arithmetic, square-root and printing commands (`FnSize`, the SizeBound
premises). `FnRegs`: the argument registers.

`fn_arm` joins a generated dispatch `dcf_disp_<c>` with an arm: the arm runs
from the frame `FnAt.of_disp` and the state `DcAt.of_disp`. The per-character
lemmas `dcf_<c>` are generated (`scripts/dc/gen_dcf_spec.py`); `dcf_out`
covers the characters outside the table.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- **SizeBound for one command**: the operand sizes the bc callees bound
(the printing commands' widths, `/ % ~ ^ |`, `v`), and that the square root
of the top number exists (`SqOut`, the Newton relation's result). -/
structure FnSize (st : St) : Prop where
  all : ∀ v ∈ st.stack, ∀ n, v = .num n → n.wid < 2 ^ 20
  div : ∀ b a rest, st.stack = .num b :: .num a :: rest → a.wid + st.scale + b.wid < 2 ^ 27
  rem : ∀ b a rest, st.stack = .num b :: .num a :: rest → a.wid + st.scale + b.wid < 2 ^ 24
  exp : ∀ b a rest, st.stack = .num b :: .num a :: rest →
    (b.toLong.natAbs + 1) * (a.wid + 1) + st.scale < 2 ^ 24
  modexp : ∀ c b a rest, st.stack = .num c :: .num b :: .num a :: rest →
    8 * (a.wid + c.wid + st.scale + 1) + b.wid < 2 ^ 24
  sqrt : ∀ n rest, st.stack = .num n :: rest → n.wid + st.scale < 2 ^ 20
  sqOut : ∀ n rest, st.stack = .num n :: rest → ∃ o, SqOut n st.scale o

theorem FnSize.top {st : St} (h : FnSize st) : ∀ n rest, st.stack = .num n :: rest → n.wid < 2 ^ 20 :=
  fun n rest e => h.all (.num n) (by rw [e]; exact List.mem_cons_self) n rfl

/-- **`dc_func`'s premises** at its entry (memory `M`, frame `W` bytes below `sp`). -/
structure FnPre (S : Nat → Prop) (sp W : Nat) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G : DcG) (hs : List GV) (st : St) (c : Nat) (peek : Option Nat) : Prop where
  dc : DcAt S M H F L C G hs st
  frame : StackFrame S sp W
  room : heapEnd + W ≤ sp
  stk : 1216 + rmStack (2 ^ 30) ≤ W
  stkPr : 192 + 336 + prN ≤ W
  stkDn : 192 + 336 + dnN ≤ W
  hsLen : hs.length + 4 ≤ 2 ^ 20
  lkLen : G.lk.length + 2 ≤ 2 ^ 29
  mb : MulBase S M
  err : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a
  laOwn : ∀ a, 0x8001cd30 ≤ a → a < 0x8001cd34 → S a
  la : ldv .lw M 0x8001cd30 = 0xFFFFFFFFFFFFFFFF#64
  size : FnSize st
  c256 : c < 256
  pk : ∀ r, peek = some r → r < 256

/-- `dc_func`'s argument registers: `sp`, `c`, `peekc`, `negcmp`, an aligned `ra`. -/
structure FnRegs (R : Nat → BitVec 64) (sp c : Nat) (peek : Option Nat) (neg : Bool) : Prop where
  r2 : R 2 = BitVec.ofNat 64 sp
  r10 : R 10 = BitVec.ofNat 64 c
  r11 : R 11 = chW peek
  r12 : R 12 = boolWord neg
  al : (R 1).toNat % 4 = 0

theorem FnPre.heapOwn {S : Nat → Prop} {sp W : Nat} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {c : Nat} {peek : Option Nat}
    (hp : FnPre S sp W M H F L C G hs st c peek) : HeapOwn S :=
  fun a e1 e2 => hp.dc.heap.heap.own a e1 e2

/-- The `stdin_lookahead` word after the dispatch's store of `ra`. -/
theorem FnPre.laArm {S : Nat → Prop} {sp W : Nat} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {c : Nat} {peek : Option Nat}
    (hp : FnPre S sp W M H F L C G hs st c peek) (ra : BitVec 64) :
    ldv .lw (writeLog M [(sp - 192 + 184, 8, ra)]) 0x8001cd30 = 0xFFFFFFFFFFFFFFFF#64 := by
  have := hp.room; simp only [heapEnd] at this
  rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega)]; exact hp.la

/-- **An arm joined to its dispatch**: the arm at `tgt` runs from the frame
and the state after the dispatch (`a1`, `a2` kept, `a3 = c`). -/
theorem fn_arm {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} {sp W : Nat} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
    {G : DcG} {hs : List GV} {st : St} {c tgt : Nat} {peek : Option Nat} {neg : Bool}
    {R : Nat → BitVec 64} (hp : FnPre S sp W M H F L C G hs st c peek) (hr : FnRegs R sp c peek neg)
    (hdisp : (∀ R', Keeps [2, 13, 14, 15] R' R → R' 2 = BitVec.ofNat 64 (sp - 192) → R' 13 = R 10 →
      DWO live S Q t (BitVec.ofNat 64 tgt) R' (writeLog M [(sp - 192 + 184, 8, R 1)])) →
      DWO live S Q t 0x80000b9c#64 R M)
    (harm : ∀ R', FnAt S sp W M R R' (writeLog M [(sp - 192 + 184, 8, R 1)]) →
      DcAt S (writeLog M [(sp - 192 + 184, 8, R 1)]) H F L C G hs st →
      R' 11 = chW peek → R' 12 = boolWord neg → R' 13 = BitVec.ofNat 64 c →
      DWO live S Q t (BitVec.ofNat 64 tgt) R' (writeLog M [(sp - 192 + 184, 8, R 1)])) :
    DWO live S Q t 0x80000b9c#64 R M :=
  hdisp fun R' k e2 e13 =>
    harm R' (FnAt.of_disp hp.frame hp.room (by have := hp.stk; omega) hr.r2 hr.al k e2)
      (hp.dc.of_disp (by have := hp.room; have := hp.stk; omega))
      ((k.get 11 (by decide)).trans hr.r11) ((k.get 12 (by decide)).trans hr.r12)
      (e13.trans hr.r10)

/-- A character outside the table falls to `dcFunc`'s last case. -/
theorem dcFunc_out {lm c : Nat} (st : St) (peek : Option Nat) (neg : Bool) (hc : c < 9 ∨ 126 < c) :
    dcFunc lm st c peek neg = .ok (st.emit (unimplemented c)) := by
  unfold dcFunc
  dsimp only
  split <;> first | rfl | (exfalso; omega)

/-- **A character outside `9..126`**: the default arm. -/
theorem dcf_out {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {sp W : Nat} {M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {c : Nat}
    {peek : Option Nat} {neg : Bool} {R : Nat → BitVec 64}
    (hp : FnPre S sp W M H F L C G hs st c peek) (hr : FnRegs R sp c peek neg)
    (hout : c < 9 ∨ 126 < c)
    (hk : FnK live S Q (leakAllow c) t0 st (dcFunc 70 st c peek neg) G hs sp W M R) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000b9c#64 R M := by
  refine dcf_disp_out hlive (hp.frame.mono (by have := hp.stk; omega)) (by have := hp.room; have := hp.stk; omega)
    hp.c256 hout R hr.r2 hr.r10 fun R' k e2 e13 => ?_
  exact fa_default hlive (dcFunc_out st peek neg hout) hp.c256 (hp.dc.of_disp (by have := hp.room; have := hp.stk; omega))
    (FnAt.of_disp hp.frame hp.room (by have := hp.stk; omega) hr.r2 hr.al k e2) (by have := hp.stk; omega)
    (e13.trans hr.r10) hk

end Dc.Mach
