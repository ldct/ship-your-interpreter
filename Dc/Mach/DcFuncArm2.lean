import Dc.Mach.DcFuncArm1
import Dc.Mach.DcArith
import Dc.Mach.DcDiv
import Dc.Mach.DcRaise
import Dc.Mach.DcDivrem
import Dc.Mach.DcModexp

/-!
# `dc_func`'s arithmetic arms (M10)

`+ - * / % ^` call `dc_binop`, `~` `dc_binop2` and `|` `dc_triop` with the
operation's function pointer and `dc_scale`, then return `DC_OKAY`. The
callee's return is `fn_opRet`, its out-of-memory exit `fn_opOom`; the arms
instantiate `fn_binop`, `fn_binop2`, `fn_triop` with the operations of
`DcArith`, `DcDiv`, `DcRaise`, `DcDivrem` and `DcModexp`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {st : St} {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {G : DcG} {hs : List GV} {sp W : Nat} {R0 R : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- `mul_base_digits` through the arm's stores. -/
theorem FnAt.mulBase (hc : FnAt S sp W M0 R0 R M) (hmb : MulBase S M0) : MulBase S M :=
  hmb.transport fun a e1 e2 => by
    have ho := mulBase_off e1 e2
    have hab := hc.room
    refine hc.out a ho.1 ho.2.1 (fun hg => ?_) (fun hf => ?_)
    · simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr, mulBaseAddr] at hg e1 e2; omega
    · have := ho.2.2; simp only [frameIn, heapStart] at hf this; simp only [heapEnd] at hab; omega

theorem binop_out (st : St) (f : Num → Num → Option Num) : (binop st f).out = st.out := by
  unfold binop; split <;> (try split) <;> rfl

theorem binop2_out (st : St) (f : Num → Num → Option (Num × Num)) :
    (binop2 st f).out = st.out := by
  unfold binop2; split <;> (try split) <;> rfl

theorem triop_out (st : St) (f : Num → Num → Num → Option Num) : (triop st f).out = st.out := by
  unfold triop; split <;> (try split) <;> rfl

/-- **An operation callee's return** at `p + 4` (`j DC_OKAY`). -/
theorem fn_opRet {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {Wc lk p : Nat} {R' : Nat → BitVec 64} {M' : Mem}
    {H' : Heap} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG} {st' : St}
    (hc : FnAt S sp W M0 R0 R M) (hW : 192 + Wc ≤ W) (hj : JAt live S Q (p + 4) 0x80000c10)
    (h1 : R 1 = BitVec.ofNat 64 (p + 4)) (k : Keeps (1 :: 2 :: opClob) R' R) (e2 : R' 2 = R 2)
    (hlk : G'.lk.length ≤ G.lk.length + lk) (hlk2 : lk ≤ al) (hstr : G'.strs = G.strs)
    (h' : DcAt S M' H' F' L' C' G' hs st') (hout : StkOut (sp - 192) Wc M' M)
    (hk : FnK live S Q al t0 st (.ok st') G hs sp W M0 R0) (hso : st'.out = st.out) :
    DWO live S Q (t0 ++ Dc.outStr st.out) (R 1) R' M' := by
  rw [h1, ← hso]
  exact hj _ R' M' (fa_ok hlive (ex := []) h' (hc.callS hW (k.mono (by decide)) e2 hout) hk (.ok _)
    (by simp) (by simp; omega) (StrPin.of_eq hstr _))

/-- **An operation callee out of memory.** -/
theorem fn_opOom {Wc sp' : Nat} {R' : Nat → BitVec 64} {M' : Mem} {t' : String}
    (hc : FnAt S sp W M0 R0 R M) (ho : FnOom live S Q sp W M0) (hW : 192 + Wc ≤ W)
    (o : OomAt S (sp - 192) Wc M (fun _ => False) sp' R' M') :
    DWO live S Q t' 0x80001e74#64 R' M' :=
  hc.oom ho hW o.lo o.hi o.r2 fun a e1 e2 _ e4 => o.out a e1 e2 e4 id

/-- **`dc_binop (op, dc_scale)`** from its call (return address `p + 4`). -/
theorem fn_binop {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {fa N lk p : Nat}
    {f : Nat → Num → Num → Option Num} {ok : Nat → Num → Num → Prop}
    (hop : DcOp live S fa N lk ok f) (hfa : fa % 4 = 0 ∧ fa < 2 ^ 64) (hlk2 : lk ≤ al)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 448 ≤ W)
    (hN : 192 + 112 + N ≤ W) (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hok : ∀ b a rest, st.stack = .num b :: .num a :: rest → ok st.scale a b)
    (hhs : hs.length + 3 ≤ 2 ^ 20) (hlk : G.lk.length + lk ≤ 2 ^ 29)
    (h10 : R 10 = BitVec.ofNat 64 fa) (h11 : R 11 = BitVec.ofNat 64 st.scale)
    (h1 : R 1 = BitVec.ofNat 64 (p + 4)) (hp : (p + 4) % 4 = 0 ∧ p + 4 < 2 ^ 64)
    (hj : JAt live S Q (p + 4) 0x80000c10)
    (hk : FnK live S Q al t0 st (.ok (binop st (f st.scale))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800031c8#64 R M :=
  dc_binop_spec hlive hop hfa.1 hfa.2 h hok hhs (hc.mulBase hmb) hlk (hc.cf (Wc := W - 192) (by omega))
    (hc.cab (by omega)) (by omega) (by omega) R h10 h11 hc.r2
    (by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp.2]; exact hp.1)
    (fun R' M' H' F' L' C' G' k e2 hl hstr h' hout =>
      fn_opRet hlive hc (Wc := W - 192) (by omega) hj h1 k e2 hl hlk2 hstr h' hout hk (binop_out _ _))
    fun R' M' sp' o => fn_opOom hc ho (Wc := W - 192) (by omega) o

/-- **`dc_binop2 (op, dc_scale)`** from its call. -/
theorem fn_binop2 {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {fa N lk p : Nat}
    {f : Nat → Num → Num → Option (Num × Num)} {ok : Nat → Num → Num → Prop}
    (hop : DcOp2 live S fa N lk ok f) (hfa : fa % 4 = 0 ∧ fa < 2 ^ 64) (hlk2 : lk ≤ al)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 464 ≤ W)
    (hN : 192 + 128 + N ≤ W) (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hok : ∀ b a rest, st.stack = .num b :: .num a :: rest → ok st.scale a b)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + lk ≤ 2 ^ 29)
    (h10 : R 10 = BitVec.ofNat 64 fa) (h11 : R 11 = BitVec.ofNat 64 st.scale)
    (h1 : R 1 = BitVec.ofNat 64 (p + 4)) (hp : (p + 4) % 4 = 0 ∧ p + 4 < 2 ^ 64)
    (hj : JAt live S Q (p + 4) 0x80000c10)
    (hk : FnK live S Q al t0 st (.ok (binop2 st (f st.scale))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800032e8#64 R M :=
  dc_binop2_spec hlive hop hfa.1 hfa.2 h hok hhs (hc.mulBase hmb) hlk (hc.cf (Wc := W - 192) (by omega))
    (hc.cab (by omega)) (by omega) (by omega) R h10 h11 hc.r2
    (by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp.2]; exact hp.1)
    (fun R' M' H' F' L' C' G' k e2 hl hstr h' hout =>
      fn_opRet hlive hc (Wc := W - 192) (by omega) hj h1 k e2 hl hlk2 hstr h' hout hk (binop2_out _ _))
    fun R' M' sp' o => fn_opOom hc ho (Wc := W - 192) (by omega) o

/-- **`dc_triop (op, dc_scale)`** from its call. -/
theorem fn_triop {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {fa N lk p : Nat}
    {f : Nat → Num → Num → Num → Option Num} {ok : Nat → Num → Num → Num → Prop}
    (hop : DcOp3 live S fa N lk ok f) (hfa : fa % 4 = 0 ∧ fa < 2 ^ 64) (hlk2 : lk ≤ al)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 464 ≤ W)
    (hN : 192 + 128 + N ≤ W) (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hok : ∀ c b a rest, st.stack = .num c :: .num b :: .num a :: rest → ok st.scale a b c)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + lk ≤ 2 ^ 29)
    (h10 : R 10 = BitVec.ofNat 64 fa) (h11 : R 11 = BitVec.ofNat 64 st.scale)
    (h1 : R 1 = BitVec.ofNat 64 (p + 4)) (hp : (p + 4) % 4 = 0 ∧ p + 4 < 2 ^ 64)
    (hj : JAt live S Q (p + 4) 0x80000c10)
    (hk : FnK live S Q al t0 st (.ok (triop st (f st.scale))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80003520#64 R M :=
  dc_triop_spec hlive hop hfa.1 hfa.2 h hok hhs (hc.mulBase hmb) hlk (hc.cf (Wc := W - 192) (by omega))
    (hc.cab (by omega)) (by omega) (by omega) R h10 h11 hc.r2
    (by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp.2]; exact hp.1)
    (fun R' M' H' F' L' C' G' k e2 hl hstr h' hout =>
      fn_opRet hlive hc (Wc := W - 192) (by omega) hj h1 k e2 hl hlk2 hstr h' hout hk (triop_out _ _))
    fun R' M' sp' o => fn_opOom hc ho (Wc := W - 192) (by omega) o

set_option hygiene false in
/-- An operation arm's start: `dc_scale` loaded (`a1`) for the call. -/
macro "fn_op_pre" : tactic =>
  `(tactic| (
    have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
    have htx : tohostAddr = 0x8001ad00 := rfl
    have hg := h.glob
    have hv : ldv .lw M 0x8001cd8c = BitVec.ofNat 64 st.scale := h.view.scale))

set_option hygiene false in
/-- An operation arm's `j DC_OKAY` after the call. -/
macro "fn_op_j" : tactic =>
  `(tactic| (
    intro t R M k
    simp only [Nat.reduceAdd]
    have htx : tohostAddr = 0x8001ad00 := rfl
    bc_run hlive hlive [] at 0x80000c10
    exact k))

/-- `+` (`0x800010a8`): `dc_binop` with `Num.add`. -/
theorem fa_add {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + 2 ≤ 2 ^ 29)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 43 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800010a8#64 R M := by
  fn_op_pre
  bc_run hlive hS [hv] at 0x800031c8
  refine fn_binop (p := 0x800010b8) hlive (dc_add_spec hlive) (by decide) (by omega) h
    (hc.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by omega) ho hmb
    (fun _ _ _ _ => trivial) (by omega) (by omega) (by bsimp []) (by bsimp []) (by bsimp []) (by decide) ?_ hk
  fn_op_j

/-- `-` (`0x800010d8`): `dc_binop` with `Num.sub`. -/
theorem fa_sub {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + 2 ≤ 2 ^ 29)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 45 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800010d8#64 R M := by
  fn_op_pre
  bc_run hlive hS [hv] at 0x800031c8
  refine fn_binop (p := 0x800010e8) hlive (dc_sub_spec hlive) (by decide) (by omega) h
    (hc.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by omega) ho hmb
    (fun _ _ _ _ => trivial) (by omega) (by omega) (by bsimp []) (by bsimp []) (by bsimp []) (by decide) ?_ hk
  fn_op_j

/-- `*` (`0x800011d0`): `dc_binop` with `Num.mul`. -/
theorem fa_mul {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + 2 ≤ 2 ^ 29)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 42 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800011d0#64 R M := by
  fn_op_pre
  bc_run hlive hS [hv] at 0x800031c8
  refine fn_binop (p := 0x800011e0) hlive (dc_mul_spec hlive) (by decide) (by omega) h
    (hc.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by omega) ho hmb
    (fun _ _ _ _ => trivial) (by omega) (by omega) (by bsimp []) (by bsimp []) (by bsimp []) (by decide) ?_ hk
  fn_op_j

/-- `/` (`0x800010c0`): `dc_binop` with `Num.div`. -/
theorem fa_div {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hok : ∀ b a rest, st.stack = .num b :: .num a :: rest → a.wid + st.scale + b.wid < 2 ^ 27)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + 2 ≤ 2 ^ 29)
    (hal : 1 ≤ al) (hk : FnK live S Q al t0 st (dcFunc 70 st 47 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800010c0#64 R M := by
  fn_op_pre
  bc_run hlive hS [hv] at 0x800031c8
  refine fn_binop (p := 0x800010d0) hlive (dc_div_spec hlive) (by decide) (by omega) h
    (hc.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by omega) ho hmb
    hok (by omega) (by omega) (by bsimp []) (by bsimp []) (by bsimp []) (by decide) ?_ hk
  fn_op_j

/-- `%` (`0x80000c6c`): `dc_binop` with `Num.modulo`. -/
theorem fa_rem {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hok : ∀ b a rest, st.stack = .num b :: .num a :: rest → a.wid + st.scale + b.wid < 2 ^ 24)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + 2 ≤ 2 ^ 29)
    (hal : 1 ≤ al) (hk : FnK live S Q al t0 st (dcFunc 70 st 37 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000c6c#64 R M := by
  fn_op_pre
  bc_run hlive hS [hv] at 0x800031c8
  refine fn_binop (p := 0x80000c7c) hlive (dc_rem_spec hlive) (by decide) (by omega) h
    (hc.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by omega) ho hmb
    hok (by omega) (by omega) (by bsimp []) (by bsimp []) (by bsimp []) (by decide) ?_ hk
  fn_op_j

/-- `^` (`0x80000fa0`): `dc_binop` with `Num.raise`. -/
theorem fa_exp {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hok : ∀ b a rest, st.stack = .num b :: .num a :: rest →
      (b.toLong.natAbs + 1) * (a.wid + 1) + st.scale < 2 ^ 24)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + 2 ≤ 2 ^ 29)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 94 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000fa0#64 R M := by
  fn_op_pre
  bc_run hlive hS [hv] at 0x800031c8
  refine fn_binop (p := 0x80000fb0) hlive (dc_exp_spec hlive) (by decide) (by omega) h
    (hc.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by omega) ho hmb
    hok (by omega) (by omega) (by bsimp []) (by bsimp []) (by bsimp []) (by decide) ?_ hk
  fn_op_j

/-- `~` (`0x80001240`): `dc_binop2` with `Num.divmod`. -/
theorem fa_divrem {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hok : ∀ b a rest, st.stack = .num b :: .num a :: rest → a.wid + st.scale + b.wid < 2 ^ 24)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + 2 ≤ 2 ^ 29)
    (hal : 2 ≤ al) (hk : FnK live S Q al t0 st (dcFunc 70 st 126 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001240#64 R M := by
  fn_op_pre
  bc_run hlive hS [hv] at 0x800032e8
  refine fn_binop2 (p := 0x80001250) hlive (dc_divrem_spec hlive) (by decide) (by omega) h
    (hc.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by omega) ho hmb
    hok (by omega) (by omega) (by bsimp []) (by bsimp []) (by bsimp []) (by decide) ?_ hk
  fn_op_j

/-- `|` (`0x800011a8`): `dc_triop` with `Num.raisemod`. -/
theorem fa_modexp {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hok : ∀ c b a rest, st.stack = .num c :: .num b :: .num a :: rest →
      8 * (a.wid + c.wid + st.scale + 1) + b.wid < 2 ^ 24)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + 2 ≤ 2 ^ 29)
    (hal : 1 ≤ al) (hk : FnK live S Q al t0 st (dcFunc 70 st 124 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800011a8#64 R M := by
  fn_op_pre
  bc_run hlive hS [hv] at 0x80003520
  refine fn_triop (p := 0x800011b8) hlive (dc_modexp_spec hlive) (by decide) (by omega) h
    (hc.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by omega) ho hmb
    hok (by omega) (by omega) (by bsimp []) (by bsimp []) (by bsimp []) (by decide) ?_ hk
  fn_op_j

end

end Dc.Mach
