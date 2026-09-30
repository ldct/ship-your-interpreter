import Dc.Mach.EmitUnsigned
import VsaIris.Interp.Arm

/-!
# `format.constprop.0` (`0x80000168`)

`format(k, fmt, ap)` (`libc.c`) walks the format in `.rodata`, emitting
literal bytes and conversions into the sink `k` (`SinkAt`), taking arguments
from the `va_list` words at `ap`.

The loop head is `0x800001d0` (the byte at `s0` in `a5`, not NUL). Its
state (`FmtState`): the constant registers (`s1 = k`, the two jump tables in
`s7`/`s2`, the bytes `%`, `l`, `#` in `s4`/`s5`/`s6`, `1` in `s3`, `18` in
`s8`), the argument pointer `s9`, the sink after the output so far, the
frame (only the 192 bytes below `sp`, for `format`'s and `emit_unsigned`'s
frames, and the sink's count word and buffer change), and the saved
registers. Each piece ends at one of six "next" sites (`fmt_next_<pc>`),
which load the following byte and return to the loop head or leave to
`0x80000298`.
-/

namespace Dc.Mach

open Lean Elab Tactic Meta
open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `dx_ro h`: the `.rodata` load step `stR_<pc> h` at the goal's PC, leaving
its address, table-membership and continuation goals. -/
elab "dx_ro " h:term : tactic => do
  let g ← getMainGoal
  let some pc ← g.withContext (do swpPC? (← g.getType)) | throwError "dx_ro: no literal PC"
  let s := String.ofList (Nat.toDigits 16 pc)
  let s := String.ofList (List.replicate (8 - s.length) (Char.ofNat 48)) ++ s
  let nm := Name.mkStr (Name.mkStr (Name.mkStr .anonymous "Dc") "Mach") s!"stR_{s}"
  evalTactic (← `(tactic| refine $(mkIdent nm) $h ?_ ?_ ?_))

/-- `keeps_tac` stopping as soon as `h` closes the goal (for a base that is
itself a chain of writes). -/
macro "keeps_to " h:term : tactic =>
  `(tactic| repeat (first | exact $h | refine Keeps.upd _ (by decide) ?_))

/-- The registers the loop may change (all but the callee-saved `s10`, `s11`
and the temporaries `format` does not touch). -/
abbrev fmtK : List Nat := [1, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
  24, 25]

/-- The saved registers in `format`'s frame at `fr`. -/
structure FmtSaved (M : Mem) (fr : Nat) (R0 : Nat → BitVec 64) : Prop where
  ra : ldv .ld M (fr + 88) = R0 1
  s0 : ldv .ld M (fr + 80) = R0 8
  s1 : ldv .ld M (fr + 72) = R0 9
  s2 : ldv .ld M (fr + 64) = R0 18
  s3 : ldv .ld M (fr + 56) = R0 19
  s4 : ldv .ld M (fr + 48) = R0 20
  s5 : ldv .ld M (fr + 40) = R0 21
  s6 : ldv .ld M (fr + 32) = R0 22
  s7 : ldv .ld M (fr + 24) = R0 23
  s8 : ldv .ld M (fr + 16) = R0 24
  s9 : ldv .ld M (fr + 8) = R0 25

theorem FmtSaved.transport {M M' : Mem} {fr : Nat} {R0 : Nat → BitVec 64} (h : FmtSaved M fr R0)
    (hag : ∀ a, fr + 8 ≤ a → a < fr + 96 → imgM M' a = imgM M a) : FmtSaved M' fr R0 := by
  have t : ∀ o, 8 ≤ o → o + 8 ≤ 96 → ldv .ld M' (fr + o) = ldv .ld M (fr + o) := fun o h1 h2 =>
    ldv_ld_congr fun j hj => hag _ (by omega) (by omega)
  exact ⟨(t 88 (by omega) (by omega)).trans h.ra, (t 80 (by omega) (by omega)).trans h.s0,
    (t 72 (by omega) (by omega)).trans h.s1, (t 64 (by omega) (by omega)).trans h.s2,
    (t 56 (by omega) (by omega)).trans h.s3, (t 48 (by omega) (by omega)).trans h.s4,
    (t 40 (by omega) (by omega)).trans h.s5, (t 32 (by omega) (by omega)).trans h.s6,
    (t 24 (by omega) (by omega)).trans h.s7, (t 16 (by omega) (by omega)).trans h.s8,
    (t 8 (by omega) (by omega)).trans h.s9⟩

/-- **The loop state** of `format`: registers, sink, frame and saved words,
with the arguments at `ap` and the output `out` so far; `M0` is the memory
at `format`'s entry, `sp` its stack pointer, `R0` its registers. -/
structure FmtState (S : Nat → Prop) (M0 : Mem) (sp k : Nat) (dst : SinkDst)
    (R0 : Nat → BitVec 64) (ap : Nat) (out : List (BitVec 8)) (R : Nat → BitVec 64) (M : Mem) :
    Prop where
  rk : (R 9).toNat = k
  t2 : R 18 = 0x80007f10#64
  one : (R 19).toNat = 1
  pct : (R 20).toNat = 37
  ell : (R 21).toNat = 108
  hash : (R 22).toNat = 35
  t1 : R 23 = 0x80007ec4#64
  n18 : (R 24).toNat = 18
  rap : (R 25).toNat = ap
  rsp : (R 2).toNat = sp - 96
  rsp' : R 2 + 96#64 = R0 2
  keep : Keeps fmtK R R0
  sink : SinkAt S M k dst out
  frame : ∀ a, (a < sp - 192 ∨ sp ≤ a) → ¬ dst.Byte k a → imgM M a = imgM M0 a
  saved : FmtSaved M (sp - 96) R0
  off : ∀ a, dst.Read k a → a < sp - 192 ∨ sp ≤ a
  fr : StackFrame S sp 192

/-- The state through register writes outside the constants: the listed
registers, and `s9` (the argument pointer, now at `ap'`). -/
theorem FmtState.regs {S : Nat → Prop} {M0 : Mem} {sp k : Nat} {dst : SinkDst}
    {R0 : Nat → BitVec 64} {ap ap' : Nat} {out : List (BitVec 8)} {R R' : Nat → BitVec 64}
    {M : Mem} (h : FmtState S M0 sp k dst R0 ap out R M)
    (hr : Keeps [1, 5, 8, 10, 11, 12, 13, 14, 15, 16, 17, 25] R' R) (h25 : (R' 25).toNat = ap') :
    FmtState S M0 sp k dst R0 ap' out R' M where
  rk := by rw [hr.get 9]; exact h.rk
  t2 := by rw [hr.get 18]; exact h.t2
  one := by rw [hr.get 19]; exact h.one
  pct := by rw [hr.get 20]; exact h.pct
  ell := by rw [hr.get 21]; exact h.ell
  hash := by rw [hr.get 22]; exact h.hash
  t1 := by rw [hr.get 23]; exact h.t1
  n18 := by rw [hr.get 24]; exact h.n18
  rap := h25
  rsp := by rw [hr.get 2]; exact h.rsp
  rsp' := by rw [hr.get 2]; exact h.rsp'
  keep := (hr.mono (by decide)).trans h.keep
  sink := h.sink
  frame := h.frame
  saved := h.saved
  off := h.off
  fr := h.fr

/-! ## The "next" sites

```
X   lbu a5,1(s0) ; X+4 addi s0,s0,1 ; X+8 bnez a5,800001d0 ; X+12 j 80000298
```
at `X ∈ {0x8000028c, 0x80000320, 0x800003ac, 0x80000418, 0x80000470}`, and at
`0x800002f0` with `mv s9,a1` after the load.
-/

set_option hygiene false in
/-- The next-site run from `X` (the proof of `fmt_next_<X>`). -/
macro "next_tac" : tactic =>
  `(tactic| (
    have htx : tohostAddr = 0x8001ad00 := rfl
    obtain ⟨hb1, hb2, hb3, hb4, -⟩ := hro
    have ea : (R 8 + 1#64).toNat = q + 1 := by rw [BitVec.toNat_add, hq]; gnorm; omega
    dx_ro hlive
    · gnorm; rw [ea]; simp only [LdOK]; omega
    · gnorm; rw [ea]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx
      rw [hb1]; exact hb2
    gnorm
    rw [ea, ldvf_lbu, hb1]
    dx_run hlive at 0x800001d0 0x80000298
    · intro hnz
      refine hloop (fun e => hnz (by rw [e]; rfl)) _ ?_ ?_ ?_
      · exact hst.regs (by keeps_tac (Keeps.refl _ _)) (by gnorm; first | exact hap | exact hst.rap)
      · gnorm; rw [BitVec.toNat_add, hq]; gnorm; omega
      · gnorm; rw [toNat_zext8]
    · intro hz
      simp only [ne_eq, Classical.not_not] at hz
      have hb0 : b = 0#8 := by
        have := congrArg BitVec.toNat hz; gnorm_at this; rw [toNat_zext8] at this
        exact BitVec.eq_of_toNat_eq this
      first
        | exact hexit hb0 _ (hst.regs (by keeps_tac (Keeps.refl _ _))
            (by gnorm; first | exact hap | exact hst.rap))
        | (dx_run hlive at 0x80000298
           exact hexit hb0 _ (hst.regs (by keeps_tac (Keeps.refl _ _))
             (by gnorm; first | exact hap | exact hst.rap)))))

/-- The next site at `0x8000028c`. -/
theorem fmt_next_8000028c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hloop : b ≠ 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap out R' M → (R' 8).toNat = q + 1 →
      (R' 15).toNat = b.toNat → DW live S Q 0x800001d0#64 R' M)
    (hexit : b = 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap out R' M →
      DW live S Q 0x80000298#64 R' M) :
    DW live S Q 0x8000028c#64 R M := by
  next_tac

/-- The next site at `0x80000320`. -/
theorem fmt_next_80000320 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hloop : b ≠ 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap out R' M → (R' 8).toNat = q + 1 →
      (R' 15).toNat = b.toNat → DW live S Q 0x800001d0#64 R' M)
    (hexit : b = 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap out R' M →
      DW live S Q 0x80000298#64 R' M) :
    DW live S Q 0x80000320#64 R M := by
  next_tac

/-- The next site at `0x800003ac`. -/
theorem fmt_next_800003ac {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hloop : b ≠ 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap out R' M → (R' 8).toNat = q + 1 →
      (R' 15).toNat = b.toNat → DW live S Q 0x800001d0#64 R' M)
    (hexit : b = 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap out R' M →
      DW live S Q 0x80000298#64 R' M) :
    DW live S Q 0x800003ac#64 R M := by
  next_tac

/-- The next site at `0x80000418`. -/
theorem fmt_next_80000418 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hloop : b ≠ 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap out R' M → (R' 8).toNat = q + 1 →
      (R' 15).toNat = b.toNat → DW live S Q 0x800001d0#64 R' M)
    (hexit : b = 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap out R' M →
      DW live S Q 0x80000298#64 R' M) :
    DW live S Q 0x80000418#64 R M := by
  next_tac

/-- The next site at `0x80000470`. -/
theorem fmt_next_80000470 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hloop : b ≠ 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap out R' M → (R' 8).toNat = q + 1 →
      (R' 15).toNat = b.toNat → DW live S Q 0x800001d0#64 R' M)
    (hexit : b = 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap out R' M →
      DW live S Q 0x80000298#64 R' M) :
    DW live S Q 0x80000470#64 R M := by
  next_tac

/-- The next site at `0x800002f0`. -/
theorem fmt_next_800002f0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap ap' : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (hap : (R 11).toNat = ap') {q : Nat} (hq : (R 8).toNat = q)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hloop : b ≠ 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap' out R' M → (R' 8).toNat = q + 1 →
      (R' 15).toNat = b.toNat → DW live S Q 0x800001d0#64 R' M)
    (hexit : b = 0#8 → ∀ R', FmtState S M0 sp k dst R0 ap' out R' M →
      DW live S Q 0x80000298#64 R' M) :
    DW live S Q 0x800002f0#64 R M := by
  next_tac

/-! ## Pieces -/

/-- What follows a piece whose last byte is at `q`: the byte `b` at `q + 1`
starts the next piece (loop head) or is the NUL (exit), with the arguments at
`ap` and the output `out`. -/
def FmtK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (M0 : Mem) (sp k : Nat) (dst : SinkDst) (R0 : Nat → BitVec 64) (ap : Nat)
    (out : List (BitVec 8)) (q : Nat) (b : BitVec 8) : Prop :=
  (b ≠ 0#8 → ∀ R M, FmtState S M0 sp k dst R0 ap out R M → (R 8).toNat = q + 1 →
    (R 15).toNat = b.toNat → DWS live S Q t0 dst out 0x800001d0#64 R M) ∧
  (b = 0#8 → ∀ R M, FmtState S M0 sp k dst R0 ap out R M →
    DWS live S Q t0 dst out 0x80000298#64 R M)

/-- The state after emits (`Emitted`) and register writes outside the
constants. -/
theorem FmtState.emitted {S : Nat → Prop} {M0 : Mem} {sp k : Nat} {dst : SinkDst}
    {R0 : Nat → BitVec 64} {ap ap' : Nat} {out out' : List (BitVec 8)} {R R' : Nat → BitVec 64}
    {M M' : Mem} (h : FmtState S M0 sp k dst R0 ap out R M) (hE : Emitted S M M' k dst out')
    (hr : Keeps [1, 5, 8, 10, 11, 12, 13, 14, 15, 16, 17, 25] R' R) (h25 : (R' 25).toNat = ap') :
    FmtState S M0 sp k dst R0 ap' out' R' M' :=
  { h.regs hr h25 with
    sink := hE.sink
    frame := fun a ha hb => (hE.frame a hb).trans (h.frame a ha hb)
    saved := h.saved.transport fun a h1 h2 =>
      hE.frame a fun hb => by
        have := h.off a (SinkDst.read_of_byte hb); have := h.fr.lo; omega }

theorem SinkAt.fw_nat {S : Nat → Prop} {M : Mem} {k : Nat} {dst : SinkDst}
    {out : List (BitVec 8)} (h : SinkAt S M k dst out) {a : Nat} (ha : a = k) :
    (ldv .ld M a).toNat = dst.fw := by
  subst ha; rw [h.fw, ofNat_toNat_lt]
  cases dst with
  | stream f fd => have := h.streamFd.1.hi; simp only [SinkDst.fw]; omega
  | buffer => simp only [SinkDst.fw]; omega

theorem SinkAt.len_nat {S : Nat → Prop} {M : Mem} {k : Nat} {dst : SinkDst}
    {out : List (BitVec 8)} (h : SinkAt S M k dst out) {a : Nat} (ha : a = k + 24) :
    (ldv .ld M a).toNat = out.length := by
  subst ha; rw [h.len, ofNat_toNat_lt]; have := h.short; omega

/-- **A literal byte** `c` at the loop head (`0x800001d0`, `c ≠ %`): emitted
(`emit_80000310`), then the next site `0x80000320`. -/
theorem fmt_lit {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {c b : BitVec 8}
    (hc : R 15 = zero_extend (m := 64) c) (hc37 : c ≠ 37#8) (hro : RoBytes (q + 1) [b])
    (hsh : out.length + 1 < 2 ^ 62) (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ [c]) q b) :
    DWS live S Q t0 dst out 0x800001d0#64 R M := by
  have hs := hst.sink
  have hkal := hs.al
  have hklo := hs.lo
  have hkhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hk9 := hst.rk
  have h20 := hst.pct
  have hcn : (R 15).toNat ≠ 37 := by
    rw [hc, toNat_zext8]; intro e; exact hc37 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  dx_run hlive at 0x80000310
  rotate_left
  · intro hc'; exfalso; simp only [ne_eq, Classical.not_not] at hc'
    have := congrArg BitVec.toNat hc'; omega
  intro _
  dx_run hlive at 0x80000310
  all_goals (try own_by hs)
  refine emit_80000310 hlive hs c hsh _ ?kr ?fr ?lr ?l1 ?c ?one fun R' M' hk' hr14 hE' => ?_
  case kr => gnorm; exact hk9
  case fr => gnorm; exact hs.fw_nat hk9
  case lr => gnorm; exact hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)
  case l1 =>
    gnorm; rw [BitVec.toNat_add, hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)]
    gnorm; omega
  case c => gnorm; exact hc
  case one => gnorm; exact hst.one
  have hst' := hst.emitted (R' := R') (ap' := ap) hE'
    ((hk'.mono (by decide)).trans (by keeps_tac (Keeps.refl _ _)))
    (by rw [hk'.get 25]; gnorm; try exact hst.rap)
  refine fmt_next_80000320 hlive hst' (by rw [hk'.get 8]; gnorm; exact hq) hro
    (fun hb R'' hs'' => hK.1 hb R'' M' hs'') (fun hb R'' hs'' => hK.2 hb R'' M' hs'')

/-! ## Arguments -/

/-- An argument word at `ap`: eight owned bytes in RAM holding `w`. -/
structure ArgW (S : Nat → Prop) (M : Mem) (ap : Nat) (w : BitVec 64) : Prop where
  own : ∀ i, i < 8 → S (ap + i)
  lo : tohostAddr + 16 ≤ ap
  hi : ap + 8 ≤ 0x88000000
  val : ldv .ld M ap = w

theorem ArgW.own' {S : Nat → Prop} {M : Mem} {ap : Nat} {w : BitVec 64} (h : ArgW S M ap w)
    {x : Nat} (h1 : ap ≤ x) (h2 : x < ap + 8) : S x := by
  have := h.own (x - ap) (by omega); rwa [Nat.add_sub_cancel' h1] at this

/-- A `ld`'s low word, sign-extended, is the `lw` at the same address. -/
theorem lwOfLd (M : Mem) (a : Nat) : ldv .lw M a = sx32 (ldv .ld M a) := by
  have h8 := toNat_append8 (imgM M) a
  have h4 := toNat_append4 (imgM M) a
  have hs := imgLE_split (imgM M) a 4 4
  have hl := imgLE_lt (imgM M) (a + 4) 4
  simp only [ldv, bytesVal, bytesAt, widthOfM, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, sx32,
    Nat.add_zero]
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, h8, h4, show (8 : Nat) = 4 + 4 from rfl, hs]
  have hl4 := imgLE_lt (imgM M) a 4
  simp only [show (256 : Nat) ^ 4 = 2 ^ 32 by decide] at hl4 ⊢
  omega

/-- A `ld`'s low word, zero-extended, is the `lwu` at the same address. -/
theorem lwuOfLd (M : Mem) (a : Nat) :
    ldv .lwu M a = BitVec.ofNat 64 ((ldv .ld M a).toNat % 2 ^ 32) := by
  have h8 := toNat_append8 (imgM M) a
  have h4 := toNat_append4 (imgM M) a
  have hs := imgLE_split (imgM M) a 4 4
  have hl := imgLE_lt (imgM M) (a + 4) 4
  have hl4 := imgLE_lt (imgM M) a 4
  simp only [ldv, bytesVal, bytesAt, widthOfM, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.getD_cons_zero, List.getD_cons_succ,
    Nat.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.toNat_ofNat]
  rw [h4, BitVec.signExtend_eq, h8, show (8 : Nat) = 4 + 4 from rfl, hs]
  simp only [show (256 : Nat) ^ 4 = 2 ^ 32 by decide] at hl hl4 ⊢
  omega

theorem lo8_sx32 (w : BitVec 64) : lo8 (sx32 w) = w.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo8, sx32, BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth]
  rw [BitVec.toNat_signExtend]
  simp only [BitVec.toNat_setWidth]
  split <;> omega

/-! ## `%c` (`0x800002b0`) and `%%` (`0x8000038c`)

```
800002b0 ld a2,24(s1) ; 800002b4 ld a4,0(s1) ; 800002b8 lw a3,0(s9)
800002bc addi a1,s9,8 ; 800002c0 addi a5,a2,1 ; 800002c4 … (emit_800002c4) → 800002f0
8000038c ld a3,24(s1) ; 80000390 ld a4,0(s1) ; 80000394 addi a5,a3,1
80000398 … (emit_80000398) → 800003ac
```
The conversion character is at `q` (`s0`).
-/

/-- **`%c`** with the argument word `w` at `ap`. -/
theorem fmt_c {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {w : BitVec 64}
    (harg : ArgW S M ap w) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : out.length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ [w.setWidth 8]) q b) :
    DWS live S Q t0 dst out 0x800002b0#64 R M := by
  have hs := hst.sink
  have hkal := hs.al
  have hklo := hs.lo
  have hkhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hk9 := hst.rk
  have h25 := hst.rap
  have halo := harg.lo
  have hahi := harg.hi
  dx_run hlive at 0x800002c4
  all_goals (try own_by hs)
  all_goals (try own_by harg)
  refine emit_800002c4 hlive hs (w.setWidth 8) hsh _ ?kr ?fr ?lr ?l1 ?c fun R' M' hk' hr15 hE' => ?_
  case kr => gnorm; exact hk9
  case fr => gnorm; exact hs.fw_nat hk9
  case lr => gnorm; exact hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)
  case l1 =>
    gnorm; rw [BitVec.toNat_add, hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)]
    gnorm; omega
  case c => gnorm; rw [h25, lwOfLd, harg.val, lo8_sx32]
  have hst' := hst.emitted (R' := R') (ap' := ap) hE'
    ((hk'.mono (by decide)).trans (by keeps_tac (Keeps.refl _ _)))
    (by rw [hk'.get 25]; gnorm; try exact h25)
  refine fmt_next_800002f0 hlive hst' (ap' := ap + 8) ?_ (by rw [hk'.get 8]; gnorm; exact hq) hro
    (fun hb R'' hs'' => hK.1 hb R'' M' hs'') (fun hb R'' hs'' => hK.2 hb R'' M' hs'')
  rw [hk'.get 11]; gnorm; rw [BitVec.toNat_add, h25]; gnorm; omega

/-- **`%%`**. -/
theorem fmt_pct {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b]) (hsh : out.length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ [37#8]) q b) :
    DWS live S Q t0 dst out 0x8000038c#64 R M := by
  have hs := hst.sink
  have hkal := hs.al
  have hklo := hs.lo
  have hkhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hk9 := hst.rk
  dx_run hlive at 0x80000398
  all_goals (try own_by hs)
  refine emit_80000398 hlive hs hsh _ ?kr ?fr ?lr ?l1 fun R' M' hk' hr15 hE' => ?_
  case kr => gnorm; exact hk9
  case fr => gnorm; exact hs.fw_nat hk9
  case lr => gnorm; exact hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)
  case l1 =>
    gnorm; rw [BitVec.toNat_add, hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)]
    gnorm; omega
  have hst' := hst.emitted (R' := R') (ap' := ap) hE'
    ((hk'.mono (by decide)).trans (by keeps_tac (Keeps.refl _ _)))
    (by rw [hk'.get 25]; gnorm; try exact hst.rap)
  exact fmt_next_800003ac hlive hst' (by rw [hk'.get 8]; gnorm; exact hq) hro
    (fun hb R'' hs'' => hK.1 hb R'' M' hs'') (fun hb R'' hs'' => hK.2 hb R'' M' hs'')

/-! ## `%s` (`0x80000244`)

```
80000244 ld a5,0(s9) ; 80000248 addi s9,s9,8 ; 8000024c lbu a4,0(a5)
80000250 beqz a4,8000028c ; 80000254 ld a3,24(s1) ; 80000258 li a6,257
8000025c slli a6,a6,0x30 ; 80000260 li a0,1
80000264 ld a1,0(s1) ; 80000268 addi a5,a5,1 ; 8000026c addi a2,a3,1
80000270 … (emit_80000270) → 80000284 lbu a4,0(a5) ; 80000288 bnez a4,80000264
```
-/

/-- The `i`-th byte of `.rodata` bytes. -/
theorem RoBytes.get {p : Nat} : ∀ {l : List (BitVec 8)} (i : Nat) (hi : i < l.length),
    RoBytes p l → dcROImg (p + i) = l[i] ∧ (p + i, dcROImg (p + i)) ∈ dcRO ∧
      0x80000000 ≤ p + i ∧ p + i + 1 ≤ tohostAddr
  | [], i, hi, _ => absurd hi (by simp)
  | b :: l, 0, _, ⟨h1, h2, h3, h4, _⟩ => by simp only [Nat.add_zero]; rw [h1]; exact ⟨rfl, h2, h3, h4⟩
  | b :: l, i + 1, hi, ⟨_, _, _, _, h5⟩ => by
    have := RoBytes.get (p := p + 1) (l := l) i (by simpa using hi) h5
    rw [show p + (i + 1) = p + 1 + i by omega]; simpa using this

/-- The string loop of `%s` at `0x80000264`: `a5` at the byte `i` of the
string `str` at `w` (in `a4`), `a3` the count, `a0 = 1`. -/
theorem fmt_str {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {q w : Nat} {str : List (BitVec 8)} (hstr : RoStr w str)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b]) (hsh : out.length + str.length < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ str) q b) :
    ∀ m i (R : Nat → BitVec 64) (M : Mem), str.length - i = m → i < str.length →
      FmtState S M0 sp k dst R0 ap (out ++ str.take i) R M → (R 8).toNat = q →
      (R 15).toNat = w + i → R 14 = zero_extend (m := 64) (dcROImg (w + i)) →
      (R 13).toNat = out.length + i → (R 10).toNat = 1 → R 16 = 72339069014638592#64 →
      DWS live S Q t0 dst (out ++ str.take i) 0x80000264#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro m
  induction m with
  | zero => intro i R M hm hi; omega
  | succ m ih =>
  intro i R M hm hi hst hq h15 h14 h13 h10 h16
  have hs := hst.sink
  have hkal := hs.al
  have hklo := hs.lo
  have hkhi := hs.hi
  have hk9 := hst.rk
  have hlen : (out ++ str.take i).length = out.length + i := by simp; omega
  have hbi := (RoBytes.get i (by simp; omega) hstr.bytes)
  rw [List.getElem_append_left hi] at hbi
  dx_run hlive at 0x80000270
  all_goals (try own_by hs)
  refine emit_80000270 hlive hs (str[i]) (by rw [hlen]; omega) _ ?kr ?fr ?lr ?l1 ?c ?one ?pw
    fun R' M' hk' hr13 hE' => ?_
  case kr => gnorm; exact hk9
  case fr => gnorm; exact hs.fw_nat hk9
  case lr => gnorm; rw [h13, hlen]
  case l1 => gnorm; rw [BitVec.toNat_add, h13, hlen]; gnorm; omega
  case c => gnorm; rw [h14, hbi.1]
  case one => gnorm; exact h10
  case pw => gnorm; exact h16
  have htake : out ++ str.take i ++ [str[i]] = out ++ str.take (i + 1) := by
    rw [List.append_assoc, List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  rw [htake] at hE' ⊢
  rw [hlen] at hr13
  have hst' := hst.emitted (R' := R') (ap' := ap) hE'
    ((hk'.mono (by decide)).trans (by keeps_tac (Keeps.refl _ _)))
    (by rw [hk'.get 25]; gnorm; try exact hst.rap)
  have e15 : (R' 15).toNat = w + i + 1 := by
    rw [hk'.get 15]; gnorm; rw [BitVec.toNat_add, h15]; gnorm; omega
  have hbj := RoBytes.get (i + 1) (by simp; omega) hstr.bytes
  rw [← Nat.add_assoc] at hbj
  dx_ro hlive
  · gnorm; rw [e15]; simp only [LdOK]; omega
  · gnorm; rw [e15]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx; exact hbj.2.1
  gnorm
  rw [e15, ldvf_lbu]
  dx_run hlive at 0x80000264 0x8000028c
  · -- another byte
    intro hnz
    have hi1 : i + 1 < str.length := by
      refine Classical.byContradiction fun hge => hnz ?_
      have : i + 1 = str.length := by omega
      rw [hbj.1, List.getElem_append_right (by omega)]; simp [this]; rfl
    refine ih (i + 1) _ M' (by omega) hi1 (hst'.regs (by keeps_tac (Keeps.refl _ _))
      (by gnorm; exact hst'.rap)) ?_ ?_ ?_ ?_ ?_ ?_
    · gnorm; rw [hk'.get 8]; gnorm; exact hq
    · gnorm; exact e15
    · gnorm; rfl
    · gnorm; rw [hr13]; try omega
    · gnorm; rw [hk'.get 10]; gnorm; exact h10
    · gnorm; rw [hk'.get 16]; gnorm; exact h16
  · -- the NUL
    intro hz
    simp only [ne_eq, Classical.not_not] at hz
    have hi1 : ¬ i + 1 < str.length := by
      intro hlt
      have hne := hstr.nz (str[i + 1]) (List.getElem_mem _)
      apply hne
      have := congrArg BitVec.toNat hz
      gnorm_at this
      rw [toNat_zext8, hbj.1, List.getElem_append_left hlt] at this
      exact BitVec.eq_of_toNat_eq this
    have htk : str.take (i + 1) = str := List.take_of_length_le (by omega)
    rw [htk] at hst' ⊢
    exact fmt_next_8000028c hlive (hst'.regs (by keeps_tac (Keeps.refl _ _)) (by gnorm; exact hst'.rap))
      (by gnorm; rw [hk'.get 8]; gnorm; exact hq) hro
      (fun hb R'' hs'' => hK.1 hb R'' M' hs'') (fun hb R'' hs'' => hK.2 hb R'' M' hs'')

/-- **`%s`** with the argument word `wv` at `ap`, a `.rodata` string `str`. -/
theorem fmt_s {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {wv : BitVec 64}
    (harg : ArgW S M ap wv) {str : List (BitVec 8)} (hstr : RoStr wv.toNat str)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b]) (hsh : out.length + str.length < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ str) q b) :
    DWS live S Q t0 dst out 0x80000244#64 R M := by
  have hs := hst.sink
  have hkal := hs.al
  have hklo := hs.lo
  have hkhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hk9 := hst.rk
  have h25 := hst.rap
  have halo := harg.lo
  have hahi := harg.hi
  have hb0 := RoBytes.get 0 (by simp) hstr.bytes
  simp only [Nat.add_zero] at hb0
  have ew : (ldv .ld M (R 25).toNat).toNat = wv.toNat := by rw [h25, harg.val]
  dx_run hlive at 0x8000024c
  all_goals (try own_by harg)
  dx_ro hlive
  · gnorm; rw [ew]; simp only [LdOK]; omega
  · gnorm; rw [ew]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx; exact hb0.2.1
  gnorm
  rw [ew, ldvf_lbu]
  have hst8 : FmtState S M0 sp k dst R0 (ap + 8) out
      (upd (upd (upd R 15 (ldv .ld M (R 25).toNat)) 25 (R 25 + 8#64)) 14
        (zero_extend (m := 64) (dcROImg wv.toNat))) M :=
    hst.regs (by keeps_tac (Keeps.refl _ _)) (by gnorm; rw [BitVec.toNat_add, h25]; gnorm; omega)
  dx_run hlive at 0x8000028c 0x80000264
  · -- the empty string
    intro hz
    have hnil : str = [] := by
      cases str with
      | nil => rfl
      | cons c l =>
        exfalso
        have hne := hstr.nz c List.mem_cons_self
        apply hne
        have := congrArg BitVec.toNat hz
        gnorm_at this
        rw [toNat_zext8, hb0.1] at this
        exact BitVec.eq_of_toNat_eq this
    subst hnil
    rw [List.append_nil] at hK
    exact fmt_next_8000028c hlive hst8 (by gnorm; exact hq) hro
      (fun hb R'' hs'' => hK.1 hb R'' M hs'') (fun hb R'' hs'' => hK.2 hb R'' M hs'')
  · intro hnz
    have hlen : 0 < str.length := by
      refine Nat.pos_of_ne_zero fun h0 => hnz ?_
      rw [hb0.1, List.getElem_append_right (by omega)]; simp [h0]; rfl
    dx_run hlive at 0x80000264
    all_goals (try own_by hs)
    rw [show out = out ++ str.take 0 by simp]
    refine fmt_str hlive hstr hro hsh hK (str.length - 0) 0 _ M rfl hlen ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [List.take_zero, List.append_nil]
      exact hst8.regs (by keeps_to (Keeps.refl _ _)) (by gnorm; exact hst8.rap)
    · gnorm; exact hq
    · gnorm; rw [ew]; try rfl
    · gnorm; rw [Nat.add_zero]
    · gnorm; exact hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)
    · gnorm
    · gnorm

/-! ## The calls of `emit_unsigned` (`0x8000040c`, `0x80000464`)

```
8000040c li a2,10 ; 80000410 mv a0,s1 ; 80000414 jal emit_unsigned   → 80000418
80000464 li a2,8  ; 80000468 mv a0,s1 ; 8000046c jal emit_unsigned   → 80000470
```
-/

/-- The state after a call that changes only the callee's frame below
`format`'s and the sink. -/
theorem FmtState.called {S : Nat → Prop} {M0 : Mem} {sp k : Nat} {dst : SinkDst}
    {R0 : Nat → BitVec 64} {ap : Nat} {out out' : List (BitVec 8)} {R R' : Nat → BitVec 64}
    {M M' : Mem} (h : FmtState S M0 sp k dst R0 ap out R M) (hs : SinkAt S M' k dst out')
    (hfrm : ∀ a, (a < sp - 96 - 96 ∨ sp - 96 ≤ a) → ¬ dst.Byte k a → imgM M' a = imgM M a)
    (hr : Keeps [1, 5, 8, 10, 11, 12, 13, 14, 15, 16, 17, 25] R' R) (h25 : (R' 25).toNat = ap) :
    FmtState S M0 sp k dst R0 ap out' R' M' :=
  have hlo := h.fr.lo
  { h.regs hr h25 with
    sink := hs
    frame := fun a ha hb => (hfrm a (by omega) hb).trans (h.frame a ha hb)
    saved := h.saved.transport fun a h1 h2 =>
      hfrm a (by omega) fun hb => by have := h.off a (SinkDst.read_of_byte hb); omega }

/-- `emit_unsigned`'s frame below `format`'s. -/
theorem FmtState.euFrame {S : Nat → Prop} {M0 : Mem} {sp k : Nat} {dst : SinkDst}
    {R0 : Nat → BitVec 64} {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (h : FmtState S M0 sp k dst R0 ap out R M) : StackFrame S (sp - 96) 96 :=
  have hf := h.fr
  have := hf.lo
  have := hf.al
  ⟨fun a h1 h2 => hf.own a (by omega) (by omega), by omega, by have := hf.hi; omega, by omega⟩

set_option hygiene false in
/-- The call of `emit_unsigned` in base `$b` and the next site. -/
macro "eu_call_tac " b:num : tactic =>
  `(tactic| (
    have hs := hst.sink
    have hlo := hst.fr.lo
    have htx : tohostAddr = 0x8001ad00 := rfl
    dx_run hlive at 0x80000040
    refine emit_unsigned_spec hlive hst.euFrame hs
      (fun a ha => by have := hst.off a ha; omega) (b := $b) (by omega) _ ?_ ?_ ?_ ?_ ?_
      fun R' M' hk' hs' hfrm => ?_
    · gnorm; exact hst.rsp
    · gnorm; exact hst.rk
    · gnorm
    · gnorm; rw [hu]; exact hsh
    · gnorm <;> decide
    have hst' := hst.called (R' := R') hs' hfrm
      ((hk'.mono (by decide)).trans (by keeps_to (Keeps.refl _ _)))
      (by rw [hk'.get 25]; gnorm; exact hst.rap)
    gnorm
    rw [hu]
    refine next_lem hlive hst' (by rw [hk'.get 8]; gnorm; exact hq) hro ?_ ?_
    · intro hb R'' hs''; gnorm_at hs''; rw [hu] at hs''; exact hK.1 hb R'' M' hs''
    · intro hb R'' hs''; gnorm_at hs''; rw [hu] at hs''; exact hK.2 hb R'' M' hs''))

/-- **`emit_unsigned(k, u, 10)`** from `0x8000040c`, then the next site. -/
theorem fmt_dec {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {u : Nat}
    (hu : (R 11).toNat = u) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : out.length + ndig 10 u < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ udigits 10 u) q b) :
    DWS live S Q t0 dst out 0x8000040c#64 R M := by
  have next_lem := @fmt_next_80000418
  eu_call_tac 10

/-- **`emit_unsigned(k, u, 8)`** from `0x80000464`, then the next site. -/
theorem fmt_oct {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {u : Nat}
    (hu : (R 11).toNat = u) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : out.length + ndig 8 u < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ udigits 8 u) q b) :
    DWS live S Q t0 dst out 0x80000464#64 R M := by
  have next_lem := @fmt_next_80000470
  eu_call_tac 8

/-! ## `%d` (`0x800003fc`, `0x8000048c`), `%u` (`0x80000428`, `0x800004d8`)

```
800003fc lw a5,0(s9) ; 80000400 addi s9,s9,8 ; 80000404 mv a1,a5 ; 80000408 bltz a5,8000049c
8000048c ld a5,0(s9) ; 80000490 addi s9,s9,8 ; 80000494 mv a1,a5 ; 80000498 bgez a5,8000040c
8000049c ld a2,24(s1) ; 800004a0 ld a3,0(s1) ; 800004a4 addi a4,a2,1
800004a8 … (emit_800004a8) → 800004d0 neg a1,a5 ; 800004d4 j 8000040c
80000428 lwu a1,0(s9) ; 8000042c addi s9,s9,8 ; 80000430 j 8000040c
800004d8 ld a1,0(s9) ; 800004dc addi s9,s9,8 ; 800004e0 j 8000040c
```
-/

/-- A negative `%d` value `v` in `a5` at `0x8000049c`: `-`, then its magnitude. -/
theorem fmt_neg {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : out.length + 1 + ndig 10 (-(R 15)).toNat < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ 45#8 :: udigits 10 (-(R 15)).toNat) q b) :
    DWS live S Q t0 dst out 0x8000049c#64 R M := by
  have hs := hst.sink
  have hkal := hs.al
  have hklo := hs.lo
  have hkhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hk9 := hst.rk
  dx_run hlive at 0x800004a8
  all_goals (try own_by hs)
  refine emit_800004a8 hlive hs (by omega) _ ?kr ?fr ?lr ?l1 fun R' M' hk' hr14 hE' => ?_
  case kr => gnorm; exact hk9
  case fr => gnorm; exact hs.fw_nat hk9
  case lr => gnorm; exact hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)
  case l1 =>
    gnorm; rw [BitVec.toNat_add, hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)]
    gnorm; omega
  have hst' := hst.emitted (R' := R') (ap' := ap) hE'
    ((hk'.mono (by decide)).trans (by keeps_to (Keeps.refl _ _)))
    (by rw [hk'.get 25]; gnorm; try exact hst.rap)
  have e15 : R' 15 = R 15 := by rw [hk'.get 15]; gnorm
  dx_run hlive at 0x8000040c
  refine fmt_dec hlive (hst'.regs (by keeps_to (Keeps.refl _ _)) (by gnorm; exact hst'.rap))
    (by gnorm; rw [hk'.get 8]; gnorm; exact hq) (u := (-(R 15)).toNat) (by gnorm; rw [e15]; simp)
    hro (by simp only [List.length_append, List.length_singleton]; omega) ?_
  simpa using hK

/-- A `%d` value `v` in `a5` and `a1` at `0x80000408` (after the load):
negative to `fmt_neg`, else `emit_unsigned`. -/
theorem fmt_dval {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {v : BitVec 64}
    (h15 : R 15 = v) (h11 : R 11 = v) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : out.length + 1 + ndig 10 (if v.msb then (-v).toNat else v.toNat) < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ (if v.msb then 45#8 :: udigits 10 (-v).toNat
      else udigits 10 v.toNat)) q b) (pc : BitVec 64)
    (hpc : pc = 0x80000408#64 ∨ pc = 0x80000498#64) :
    DWS live S Q t0 dst out pc R M := by
  have hneg : v.msb = true → DWS live S Q t0 dst out 0x8000049c#64 R M := fun hn =>
    fmt_neg hlive hst hq hro (by rw [h15]; simpa [hn] using hsh) (by rw [h15]; simpa [hn] using hK)
  have hpos : v.msb = false → DWS live S Q t0 dst out 0x8000040c#64 R M := fun hn =>
    fmt_dec hlive hst hq (u := v.toNat) (by rw [h11]) hro (by simp [hn] at hsh; omega)
      (by simpa [hn] using hK)
  rcases hpc with rfl | rfl
  · dx_run hlive at 0x8000049c 0x8000040c
    · intro hn; rw [toInt_lt0_msb, h15] at hn; exact hneg hn
    · intro hn; rw [toInt_lt0_msb, h15] at hn; exact hpos (by simpa using hn)
  · dx_run hlive at 0x8000049c 0x8000040c
    · intro hn; rw [toInt_ge0_msb, h15] at hn; exact hpos hn
    · intro hn; rw [toInt_ge0_msb, h15] at hn; exact hneg (by simpa using hn)

theorem udigits_length (b v : Nat) : (udigits b v).length = ndig b v := by
  simp [udigits]

theorem sx32_dval (w : BitVec 64) : sx32 w = dval false w := by
  simp [sx32, dval, BitVec.truncate_eq_setWidth]

/-- The `%d` output as `fmt_dval` states it. -/
theorem convOut_d (alt lng : Bool) (a : FArg) :
    convOut alt lng .d a = (if (dval lng a.w).msb then 45#8 :: udigits 10 (-(dval lng a.w)).toNat
      else udigits 10 (dval lng a.w).toNat) := rfl

/-- The length bound `fmt_dval` needs from the output's. -/
theorem dval_sh {out : List (BitVec 8)} {v : BitVec 64}
    (h : (out ++ (if v.msb then 45#8 :: udigits 10 (-v).toNat else udigits 10 v.toNat)).length + 1
      < 2 ^ 62) :
    out.length + 1 + ndig 10 (if v.msb then (-v).toNat else v.toNat) < 2 ^ 62 := by
  by_cases hm : v.msb = true
  · simp only [hm, ite_true, List.length_append, List.length_cons, udigits_length] at h ⊢; omega
  · simp only [hm, Bool.false_eq_true, ite_false, List.length_append, udigits_length] at h ⊢; omega

set_option hygiene false in
/-- A numeric argument load, then `$tac` at the value. -/
macro "num_load_tac " j:num : tactic =>
  `(tactic| (
    have hlo := harg.lo
    have hhi := harg.hi
    have htx : tohostAddr = 0x8001ad00 := rfl
    have h25 := hst.rap
    dx_run hlive at $j
    all_goals (try own_by harg)))

/-- **`%d`** (no `l`) with the argument word at `ap`. -/
theorem fmt_d0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {alt : Bool}
    {a : FArg} (harg : ArgW S M ap a.w) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : (out ++ convOut alt false .d a).length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ convOut alt false .d a) q b) :
    DWS live S Q t0 dst out 0x800003fc#64 R M := by
  num_load_tac 0x80000408
  rw [convOut_d] at hsh hK
  refine fmt_dval hlive (hst.regs (by keeps_to (Keeps.refl _ _))
      (by gnorm; rw [BitVec.toNat_add, h25]; gnorm; omega)) (by gnorm; exact hq)
    (v := dval false a.w) ?_ ?_ hro (dval_sh hsh) hK _ (.inl rfl)
  · gnorm; rw [h25, lwOfLd, harg.val, sx32_dval]
  · gnorm; rw [h25, lwOfLd, harg.val, sx32_dval]

/-- **`%ld`** with the argument word at `ap`. -/
theorem fmt_d1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {alt : Bool}
    {a : FArg} (harg : ArgW S M ap a.w) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : (out ++ convOut alt true .d a).length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ convOut alt true .d a) q b) :
    DWS live S Q t0 dst out 0x8000048c#64 R M := by
  num_load_tac 0x80000498
  rw [convOut_d] at hsh hK
  refine fmt_dval hlive (hst.regs (by keeps_to (Keeps.refl _ _))
      (by gnorm; rw [BitVec.toNat_add, h25]; gnorm; omega)) (by gnorm; exact hq)
    (v := dval true a.w) ?_ ?_ hro (dval_sh hsh) hK _ (.inr rfl)
  · gnorm; rw [h25, harg.val]; rfl
  · gnorm; rw [h25, harg.val]; rfl

/-- **`%u`** (no `l`) with the argument word at `ap`. -/
theorem fmt_u0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {alt : Bool}
    {a : FArg} (harg : ArgW S M ap a.w) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : (out ++ convOut alt false .u a).length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ convOut alt false .u a) q b) :
    DWS live S Q t0 dst out 0x80000428#64 R M := by
  num_load_tac 0x8000040c
  simp only [convOut, List.length_append, udigits_length] at hsh hK
  refine fmt_dec hlive (hst.regs (by keeps_to (Keeps.refl _ _))
      (by gnorm; rw [BitVec.toNat_add, h25]; gnorm; omega)) (by gnorm; exact hq)
    (u := uval false a.w) ?_ hro (by omega) hK
  gnorm; rw [h25, lwuOfLd, harg.val, BitVec.toNat_ofNat]; simp [uval]; try omega

/-- **`%lu`** with the argument word at `ap`. -/
theorem fmt_u1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {alt : Bool}
    {a : FArg} (harg : ArgW S M ap a.w) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : (out ++ convOut alt true .u a).length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ convOut alt true .u a) q b) :
    DWS live S Q t0 dst out 0x800004d8#64 R M := by
  num_load_tac 0x8000040c
  simp only [convOut, List.length_append, udigits_length] at hsh hK
  refine fmt_dec hlive (hst.regs (by keeps_to (Keeps.refl _ _))
      (by gnorm; rw [BitVec.toNat_add, h25]; gnorm; omega)) (by gnorm; exact hq)
    (u := uval true a.w) ?_ hro (by omega) hK
  gnorm; rw [h25, harg.val]; rfl

/-! ## `%o`, `%#o` (`0x80000434`, `0x80000480`)

```
80000434 lwu a1,0(s9) ; 80000438 addi s9,s9,8
8000043c beqz a1,80000464 ; 80000440 beqz a4,80000464
80000444 ld a3,24(s1) ; 80000448 ld a4,0(s1) ; 8000044c addi a5,a3,1
80000450 … (emit_80000450) → 80000464
80000480 ld a1,0(s9) ; 80000484 addi s9,s9,8 ; 80000488 j 8000043c
```
`a4` holds the `#` flag.
-/

/-- The `%o` value `u` in `a1`, the `#` flag in `a4`, at `0x8000043c`. -/
theorem fmt_oalt {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {u : Nat}
    (hu : (R 11).toNat = u) {alt : Bool} (h14 : R 14 = if alt then 1#64 else 0#64)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : out.length + 1 + ndig 8 u < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap
      (out ++ ((if alt && u ≠ 0 then [48#8] else []) ++ udigits 8 u)) q b) :
    DWS live S Q t0 dst out 0x8000043c#64 R M := by
  have hs := hst.sink
  have hkal := hs.al
  have hklo := hs.lo
  have hkhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hk9 := hst.rk
  have hplain : (alt && u ≠ 0) = false → DWS live S Q t0 dst out 0x80000464#64 R M := fun h =>
    fmt_oct hlive hst hq hu hro (by omega) (by rw [h] at hK; simpa using hK)
  dx_run hlive at 0x80000464 0x80000440
  · intro hz
    have : u = 0 := by rw [← hu, hz]; rfl
    exact hplain (by simp [this])
  · intro hnz
    have hu0 : u ≠ 0 := fun e => hnz (BitVec.eq_of_toNat_eq (by rw [hu, e]; rfl))
    dx_run hlive at 0x80000464 0x80000444
    · intro ha
      cases alt with
      | false => exact hplain rfl
      | true => rw [h14] at ha; exact absurd ha (by decide)
    · intro ha
      cases alt with
      | false => rw [h14] at ha; exact absurd rfl ha
      | true =>
      dx_run hlive at 0x80000450
      all_goals (try own_by hs)
      refine emit_80000450 hlive hs (by omega) _ ?kr ?fr ?lr ?l1 fun R' M' hk' hr15 hE' => ?_
      case kr => gnorm; exact hk9
      case fr => gnorm; exact hs.fw_nat hk9
      case lr => gnorm; exact hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)
      case l1 =>
        gnorm; rw [BitVec.toNat_add, hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)]
        gnorm; omega
      have hst' := hst.emitted (R' := R') (ap' := ap) hE'
        ((hk'.mono (by decide)).trans (by keeps_to (Keeps.refl _ _)))
        (by rw [hk'.get 25]; gnorm; try exact hst.rap)
      refine fmt_oct hlive hst' (by rw [hk'.get 8]; gnorm; exact hq) (u := u)
        (by rw [hk'.get 11]; gnorm; exact hu) hro (by simp; omega) ?_
      simpa [hu0] using hK

/-- **`%o`**/**`%#o`** (no `l`) with the argument word at `ap`. -/
theorem fmt_o0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {alt : Bool}
    (h14 : R 14 = if alt then 1#64 else 0#64)
    {a : FArg} (harg : ArgW S M ap a.w) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : out.length + 1 + ndig 8 (uval false a.w) < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ convOut alt false .o a) q b) :
    DWS live S Q t0 dst out 0x80000434#64 R M := by
  num_load_tac 0x8000043c
  refine fmt_oalt hlive (hst.regs (by keeps_to (Keeps.refl _ _))
      (by gnorm; rw [BitVec.toNat_add, h25]; gnorm; omega)) (by gnorm; exact hq)
    (u := uval false a.w) ?_ (by gnorm; exact h14) hro hsh hK
  gnorm; rw [h25, lwuOfLd, harg.val, BitVec.toNat_ofNat]; simp [uval]; try omega

/-- **`%lo`**/**`%#lo`** with the argument word at `ap`. -/
theorem fmt_o1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {alt : Bool}
    (h14 : R 14 = if alt then 1#64 else 0#64)
    {a : FArg} (harg : ArgW S M ap a.w) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : out.length + 1 + ndig 8 (uval true a.w) < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ convOut alt true .o a) q b) :
    DWS live S Q t0 dst out 0x80000480#64 R M := by
  num_load_tac 0x8000043c
  refine fmt_oalt hlive (hst.regs (by keeps_to (Keeps.refl _ _))
      (by gnorm; rw [BitVec.toNat_add, h25]; gnorm; omega)) (by gnorm; exact hq)
    (u := uval true a.w) ?_ (by gnorm; exact h14) hro hsh hK
  gnorm; rw [h25, harg.val]; rfl

/-! ## Dispatch (`0x800001e8`, `0x80000368`)

```
800001e8 beq a5,s4,8000038c ; 800001ec addiw a5,a5,-99 ; 800001f0 zext.b a5,a5
800001f4 bltu s8,a5,8000020c ; 800001f8 slli a5,a5,0x2 ; 800001fc add a5,a5,s7
80000200 lw a5,0(a5) ; 80000204 add a5,a5,s7 ; 80000208 jr a5
80000368 … the same with the table `s2` (after `l`) … 80000388 jr a5
```
-/

/-- The handler of a conversion (after `l` when `lng`). -/
def hpc (lng : Bool) : Conv → Nat
  | .pct => 0x8000038c
  | .c => 0x800002b0
  | .s => 0x80000244
  | .d => if lng then 0x8000048c else 0x800003fc
  | .u => if lng then 0x800004d8 else 0x80000428
  | .o => if lng then 0x80000480 else 0x80000434

theorem DW_pc_eq {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {pc pc' : BitVec 64} {R : Nat → BitVec 64} {M : Mem} (h : pc = pc')
    (hk : DW live S Q pc' R M) : DW live S Q pc R M := h ▸ hk

set_option hygiene false in
/-- The table dispatch from the `beq a5,s4` at `0x800001e8`/`0x80000368` to the
handler `$tgt` (the table in `$t`: `hst.t1` or `hst.t2`). -/
macro "tab_tac " st:num ld:num t:term:max tgt:num : tactic =>
  `(tactic| (
    dx_run hlive at $st
    dx_run [2] hlive
    rw [h15]; sx_norm; try simp only [BitVec.reduceAnd]
    dx_run hlive at $ld
    rw [$t:term]; gnorm
    dx_ro hlive
    · gnorm; decide
    · gnorm; decide +kernel
    gnorm
    dx_run hlive
    · gnorm; rw [$t:term]; decide +kernel
    · rw [$t:term]
      refine DW_pc_eq (pc' := BitVec.ofNat 64 $tgt) (by decide +kernel) (hk _ ?_)
      keeps_tac (Keeps.refl _ _)))

theorem fmt_tab_false_s {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (h15 : R 15 = 115#64)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q 0x80000244#64 R' M) :
    DW live S Q 0x800001e8#64 R M := by
  have h20 := hst.pct
  have h24 := hst.n18
  have h15n := congrArg BitVec.toNat h15
  gnorm_at h15n
  tab_tac 0x800001ec 0x80000200 hst.t1 0x80000244

theorem fmt_tab_false_c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (h15 : R 15 = 99#64)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q 0x800002b0#64 R' M) :
    DW live S Q 0x800001e8#64 R M := by
  have h20 := hst.pct
  have h24 := hst.n18
  have h15n := congrArg BitVec.toNat h15
  gnorm_at h15n
  tab_tac 0x800001ec 0x80000200 hst.t1 0x800002b0

theorem fmt_tab_false_d {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (h15 : R 15 = 100#64)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q 0x800003fc#64 R' M) :
    DW live S Q 0x800001e8#64 R M := by
  have h20 := hst.pct
  have h24 := hst.n18
  have h15n := congrArg BitVec.toNat h15
  gnorm_at h15n
  tab_tac 0x800001ec 0x80000200 hst.t1 0x800003fc

theorem fmt_tab_false_u {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (h15 : R 15 = 117#64)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q 0x80000428#64 R' M) :
    DW live S Q 0x800001e8#64 R M := by
  have h20 := hst.pct
  have h24 := hst.n18
  have h15n := congrArg BitVec.toNat h15
  gnorm_at h15n
  tab_tac 0x800001ec 0x80000200 hst.t1 0x80000428

theorem fmt_tab_false_o {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (h15 : R 15 = 111#64)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q 0x80000434#64 R' M) :
    DW live S Q 0x800001e8#64 R M := by
  have h20 := hst.pct
  have h24 := hst.n18
  have h15n := congrArg BitVec.toNat h15
  gnorm_at h15n
  tab_tac 0x800001ec 0x80000200 hst.t1 0x80000434

theorem fmt_tab_true_s {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (h15 : R 15 = 115#64)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q 0x80000244#64 R' M) :
    DW live S Q 0x80000368#64 R M := by
  have h20 := hst.pct
  have h24 := hst.n18
  have h15n := congrArg BitVec.toNat h15
  gnorm_at h15n
  tab_tac 0x8000036c 0x80000380 hst.t2 0x80000244

theorem fmt_tab_true_c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (h15 : R 15 = 99#64)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q 0x800002b0#64 R' M) :
    DW live S Q 0x80000368#64 R M := by
  have h20 := hst.pct
  have h24 := hst.n18
  have h15n := congrArg BitVec.toNat h15
  gnorm_at h15n
  tab_tac 0x8000036c 0x80000380 hst.t2 0x800002b0

theorem fmt_tab_true_d {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (h15 : R 15 = 100#64)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q 0x8000048c#64 R' M) :
    DW live S Q 0x80000368#64 R M := by
  have h20 := hst.pct
  have h24 := hst.n18
  have h15n := congrArg BitVec.toNat h15
  gnorm_at h15n
  tab_tac 0x8000036c 0x80000380 hst.t2 0x8000048c

theorem fmt_tab_true_u {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (h15 : R 15 = 117#64)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q 0x800004d8#64 R' M) :
    DW live S Q 0x80000368#64 R M := by
  have h20 := hst.pct
  have h24 := hst.n18
  have h15n := congrArg BitVec.toNat h15
  gnorm_at h15n
  tab_tac 0x8000036c 0x80000380 hst.t2 0x800004d8

theorem fmt_tab_true_o {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (h15 : R 15 = 111#64)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q 0x80000480#64 R' M) :
    DW live S Q 0x80000368#64 R M := by
  have h20 := hst.pct
  have h24 := hst.n18
  have h15n := congrArg BitVec.toNat h15
  gnorm_at h15n
  tab_tac 0x8000036c 0x80000380 hst.t2 0x80000480

/-- **Dispatch** on the conversion character `kk` (in `a5`) from the table
of the `l` flag `lng`, to its handler. -/
theorem fmt_tab {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (lng : Bool) (kk : Conv)
    (h15 : R 15 = BitVec.ofNat 64 kk.char.toNat)
    (hk : ∀ R', Keeps [15] R' R → DW live S Q (BitVec.ofNat 64 (hpc lng kk)) R' M) :
    DW live S Q (if lng then 0x80000368#64 else 0x800001e8#64) R M := by
  have h20 := hst.pct
  cases lng <;> cases kk <;>
    simp only [Conv.char, hpc, Bool.false_eq_true, ite_true, ite_false, BitVec.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow] at h15 hk ⊢
  case false.pct =>
    have h15n := congrArg BitVec.toNat h15; gnorm_at h15n
    dx_run hlive at 0x8000038c; exact hk _ (Keeps.refl _ _)
  case true.pct =>
    have h15n := congrArg BitVec.toNat h15; gnorm_at h15n
    dx_run hlive at 0x8000038c; exact hk _ (Keeps.refl _ _)
  case false.s => exact fmt_tab_false_s hlive hst h15 hk
  case false.c => exact fmt_tab_false_c hlive hst h15 hk
  case false.d => exact fmt_tab_false_d hlive hst h15 hk
  case false.u => exact fmt_tab_false_u hlive hst h15 hk
  case false.o => exact fmt_tab_false_o hlive hst h15 hk
  case true.s => exact fmt_tab_true_s hlive hst h15 hk
  case true.c => exact fmt_tab_true_c hlive hst h15 hk
  case true.d => exact fmt_tab_true_d hlive hst h15 hk
  case true.u => exact fmt_tab_true_u hlive hst h15 hk
  case true.o => exact fmt_tab_true_o hlive hst h15 hk

/-! ## Flags (`0x800001d0`)

```
800001d0 bne a5,s4,80000304 ; 800001d4 lbu a5,1(s0) ; 800001d8 beq a5,s6,80000350
800001dc addi s0,s0,1 ; 800001e0 li a4,0 ; 800001e4 beq a5,s5,80000360   → 800001e8
80000350 lbu a5,2(s0) ; 80000354 li a4,1 ; 80000358 addi s0,s0,2
8000035c bne a5,s5,800001e8 ; 80000360 lbu a5,1(s0) ; 80000364 addi s0,s0,1  → 80000368
```
From `%` at `p` to the dispatch with `s0` at the conversion character, `a4`
the `#` flag, `a5` the character.
-/

theorem zext_ofNat (b : BitVec 8) : zero_extend (m := 64) b = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq; rw [toNat_zext8, BitVec.toNat_ofNat]; have := b.isLt; omega

/-- The `#` flag in `a4`. -/
abbrev altW (alt : Bool) : BitVec 64 := if alt then 1#64 else 0#64

/-- The dispatch's entry for the flags. -/
abbrev tabPC (lng : Bool) : BitVec 64 := if lng then 0x80000368#64 else 0x800001e8#64

/-- The loop head at a conversion without flags: `%` at `p`, the character
`kc` at `p + 1`. -/
theorem fmt_flags_ff {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) {kc : BitVec 8} (hkc : kc.toNat ≠ 35 ∧ kc.toNat ≠ 108)
    (hro : RoBytes (p + 1) [kc])
    (hk : ∀ R', FmtState S M0 sp k dst R0 ap out R' M → (R' 8).toNat = p + 1 → R' 14 = altW false →
      R' 15 = BitVec.ofNat 64 kc.toNat → DW live S Q (tabPC false) R' M) :
    DW live S Q 0x800001d0#64 R M := by
  have h20 := hst.pct
  have h21 := hst.ell
  have h22 := hst.hash
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨hb1, hb2, hb3, hb4, -⟩ := hro
  have hlt := kc.isLt
  have ea : (R 8 + 1#64).toNat = p + 1 := by rw [BitVec.toNat_add, hp]; gnorm; omega
  dx_run hlive at 0x800001d4
  dx_ro hlive
  · gnorm; rw [ea]; simp only [LdOK]; omega
  · gnorm; rw [ea]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx; rw [hb1]; exact hb2
  gnorm
  rw [ea, ldvf_lbu, hb1, zext_ofNat]
  dx_run hlive at 0x800001e8
  refine hk _ (hst.regs (by keeps_tac (Keeps.refl _ _)) (by gnorm; exact hst.rap)) ?_ ?_ ?_
  · gnorm; rw [BitVec.toNat_add, hp]; gnorm; omega
  · gnorm; rfl
  · gnorm

/-- `%#` then the character `kc` at `p + 2`. -/
theorem fmt_flags_tf {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) {kc : BitVec 8} (hkc : kc.toNat ≠ 35 ∧ kc.toNat ≠ 108)
    (hro : RoBytes (p + 1) [35#8, kc])
    (hk : ∀ R', FmtState S M0 sp k dst R0 ap out R' M → (R' 8).toNat = p + 2 → R' 14 = altW true →
      R' 15 = BitVec.ofNat 64 kc.toNat → DW live S Q (tabPC false) R' M) :
    DW live S Q 0x800001d0#64 R M := by
  have h20 := hst.pct
  have h21 := hst.ell
  have h22 := hst.hash
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨hb1, hb2, hb3, hb4, hc1, hc2, hc3, hc4, -⟩ := hro
  have hlt := kc.isLt
  have ea : (R 8 + 1#64).toNat = p + 1 := by rw [BitVec.toNat_add, hp]; gnorm; omega
  have ea2 : (R 8 + 2#64).toNat = p + 2 := by rw [BitVec.toNat_add, hp]; gnorm; omega
  dx_run hlive at 0x800001d4
  dx_ro hlive
  · gnorm; rw [ea]; simp only [LdOK]; omega
  · gnorm; rw [ea]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx; rw [hb1]; exact hb2
  gnorm
  rw [ea, ldvf_lbu, hb1, zext_ofNat]
  dx_run hlive at 0x80000350
  dx_ro hlive
  · gnorm; rw [ea2]; simp only [LdOK]; omega
  · gnorm; rw [ea2]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx; rw [hc1]; exact hc2
  gnorm
  rw [ea2, ldvf_lbu, hc1, zext_ofNat]
  dx_run hlive at 0x800001e8
  rotate_left
  · intro hc; exfalso; simp only [ne_eq, Classical.not_not] at hc; gnorm_at hc
    have := congrArg BitVec.toNat hc; gnorm_at this; rw [BitVec.toNat_ofNat] at this; omega
  intro _
  refine hk _ (hst.regs (by keeps_tac (Keeps.refl _ _)) (by gnorm; exact hst.rap)) ?_ ?_ ?_
  · gnorm; exact ea2
  · gnorm; rfl
  · gnorm

/-- `%l` then the character `kc` at `p + 2`. -/
theorem fmt_flags_ft {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) {kc : BitVec 8}
    (hro : RoBytes (p + 1) [108#8, kc])
    (hk : ∀ R', FmtState S M0 sp k dst R0 ap out R' M → (R' 8).toNat = p + 2 → R' 14 = altW false →
      R' 15 = BitVec.ofNat 64 kc.toNat → DW live S Q (tabPC true) R' M) :
    DW live S Q 0x800001d0#64 R M := by
  have h20 := hst.pct
  have h21 := hst.ell
  have h22 := hst.hash
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨hb1, hb2, hb3, hb4, hc1, hc2, hc3, hc4, -⟩ := hro
  have hlt := kc.isLt
  have ea : (R 8 + 1#64).toNat = p + 1 := by rw [BitVec.toNat_add, hp]; gnorm; omega
  have ea2 : (R 8 + 1#64 + 1#64).toNat = p + 2 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hp]; gnorm; omega
  dx_run hlive at 0x800001d4
  dx_ro hlive
  · gnorm; rw [ea]; simp only [LdOK]; omega
  · gnorm; rw [ea]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx; rw [hb1]; exact hb2
  gnorm
  rw [ea, ldvf_lbu, hb1, zext_ofNat]
  dx_run hlive at 0x80000360
  dx_ro hlive
  · gnorm; rw [ea2]; simp only [LdOK]; omega
  · gnorm; rw [ea2]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx; rw [hc1]; exact hc2
  gnorm
  rw [ea2, ldvf_lbu, hc1, zext_ofNat]
  dx_run hlive at 0x80000368
  refine hk _ (hst.regs (by keeps_tac (Keeps.refl _ _)) (by gnorm; exact hst.rap)) ?_ ?_ ?_
  · gnorm; rw [BitVec.toNat_add, ea]; gnorm; omega
  · gnorm; rfl
  · gnorm

/-- `%#l` then the character `kc` at `p + 3`. -/
theorem fmt_flags_tt {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) {kc : BitVec 8}
    (hro : RoBytes (p + 1) [35#8, 108#8, kc])
    (hk : ∀ R', FmtState S M0 sp k dst R0 ap out R' M → (R' 8).toNat = p + 3 → R' 14 = altW true →
      R' 15 = BitVec.ofNat 64 kc.toNat → DW live S Q (tabPC true) R' M) :
    DW live S Q 0x800001d0#64 R M := by
  have h20 := hst.pct
  have h21 := hst.ell
  have h22 := hst.hash
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨hb1, hb2, hb3, hb4, hc1, hc2, hc3, hc4, hd1, hd2, hd3, hd4, -⟩ := hro
  have hlt := kc.isLt
  have ea : (R 8 + 1#64).toNat = p + 1 := by rw [BitVec.toNat_add, hp]; gnorm; omega
  have ea2 : (R 8 + 2#64).toNat = p + 2 := by rw [BitVec.toNat_add, hp]; gnorm; omega
  have ea3 : (R 8 + 2#64 + 1#64).toNat = p + 3 := by
    rw [BitVec.toNat_add, ea2]; gnorm; omega
  dx_run hlive at 0x800001d4
  dx_ro hlive
  · gnorm; rw [ea]; simp only [LdOK]; omega
  · gnorm; rw [ea]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx; rw [hb1]; exact hb2
  gnorm
  rw [ea, ldvf_lbu, hb1, zext_ofNat]
  dx_run hlive at 0x80000350
  dx_ro hlive
  · gnorm; rw [ea2]; simp only [LdOK]; omega
  · gnorm; rw [ea2]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx; rw [hc1]; exact hc2
  gnorm
  rw [ea2, ldvf_lbu, hc1, zext_ofNat]
  dx_run hlive at 0x80000360
  dx_ro hlive
  · gnorm; rw [ea3]; simp only [LdOK]; omega
  · gnorm; rw [ea3]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx; rw [hd1]; exact hd2
  gnorm
  rw [ea3, ldvf_lbu, hd1, zext_ofNat]
  dx_run hlive at 0x80000368
  refine hk _ (hst.regs (by keeps_tac (Keeps.refl _ _)) (by gnorm; exact hst.rap)) ?_ ?_ ?_
  · gnorm; rw [BitVec.toNat_add, ea2]; gnorm; omega
  · gnorm; rfl
  · gnorm

/-! ## A conversion from the loop head -/

theorem Conv.char_ne (kk : Conv) : kk.char.toNat ≠ 35 ∧ kk.char.toNat ≠ 108 := by
  cases kk <;> decide

/-- The facts a conversion needs of its argument: the word at `ap`, and for
`%s` the `.rodata` string. -/
structure ArgOK (S : Nat → Prop) (M : Mem) (ap : Nat) (kk : Conv) (a : FArg) : Prop where
  word : ArgW S M ap a.w
  str : kk = .s → RoStr a.w.toNat a.s

theorem sh_s {out : List (BitVec 8)} {alt lng : Bool} {a : FArg}
    (h : (out ++ convOut alt lng .s a).length + 1 < 2 ^ 62) : out.length + a.s.length < 2 ^ 62 := by
  simp only [convOut, List.length_append] at h; omega

theorem sh_c {out : List (BitVec 8)} {alt lng : Bool} {a : FArg}
    (h : (out ++ convOut alt lng .c a).length + 1 < 2 ^ 62) : out.length + 1 < 2 ^ 62 := by
  simp only [convOut, List.length_append, List.length_singleton] at h; omega

theorem sh_o {out : List (BitVec 8)} {alt lng : Bool} {a : FArg}
    (h : (out ++ convOut alt lng .o a).length + 1 < 2 ^ 62) :
    out.length + 1 + ndig 8 (uval lng a.w) < 2 ^ 62 := by
  simp only [convOut, List.length_append, udigits_length] at h
  split at h <;> simp only [List.length_singleton, List.length_nil] at h <;> omega

/-- A conversion `%k` (`k` not `%`) from the loop head. -/
theorem fmt_conv_ff {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) (kk : Conv) (hkk : kk ≠ .pct) {b : BitVec 8}
    (hro : RoBytes (p + 1) ([kk.char] ++ [b])) {a : FArg} (harg : ArgOK S M ap kk a)
    (hsh : (out ++ convOut false false kk a).length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ convOut false false kk a) (p + 1) b) :
    DWS live S Q t0 dst out 0x800001d0#64 R M := by
  rw [RoBytes.append] at hro
  obtain ⟨hro1, hro2⟩ := hro
  simp only [List.length_append, List.length_cons, List.length_nil] at hro2
  refine fmt_flags_ff hlive hst hp h15 (kc := kk.char) kk.char_ne hro1 fun R' hst' h8 h14 h15' => ?_
  refine fmt_tab hlive hst' false kk h15' fun R'' hkp => ?_
  have hst'' := hst'.regs (R' := R'') (ap' := ap) (by keeps_tac (hkp.mono (by decide)))
    (by rw [hkp.get 25]; exact hst'.rap)
  have hq : (R'' 8).toNat = p + 1 := by rw [hkp.get 8]; exact h8
  have hnx : RoBytes (p + 1 + 1) [b] := by rw [show p + 1 + 1 = p + 1 + 1 by omega]; exact hro2
  cases kk with
  | pct => exact absurd rfl hkk
  | s => exact fmt_s hlive hst'' hq harg.word (harg.str rfl) hnx (sh_s hsh) hK
  | c => exact fmt_c hlive hst'' hq harg.word hnx (sh_c hsh) hK
  | d => exact fmt_d0 hlive hst'' hq harg.word hnx hsh hK
  | u => exact fmt_u0 hlive hst'' hq harg.word hnx hsh hK
  | o => exact fmt_o0 hlive hst'' hq (by rw [hkp.get 14]; exact h14) harg.word hnx (sh_o hsh) hK

/-- A conversion `%#k` (`k` not `%`) from the loop head. -/
theorem fmt_conv_tf {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) (kk : Conv) (hkk : kk ≠ .pct) {b : BitVec 8}
    (hro : RoBytes (p + 1) ([35#8] ++ [kk.char] ++ [b])) {a : FArg} (harg : ArgOK S M ap kk a)
    (hsh : (out ++ convOut true false kk a).length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ convOut true false kk a) (p + 2) b) :
    DWS live S Q t0 dst out 0x800001d0#64 R M := by
  rw [RoBytes.append] at hro
  obtain ⟨hro1, hro2⟩ := hro
  simp only [List.length_append, List.length_cons, List.length_nil] at hro2
  refine fmt_flags_tf hlive hst hp h15 (kc := kk.char) kk.char_ne hro1 fun R' hst' h8 h14 h15' => ?_
  refine fmt_tab hlive hst' false kk h15' fun R'' hkp => ?_
  have hst'' := hst'.regs (R' := R'') (ap' := ap) (by keeps_tac (hkp.mono (by decide)))
    (by rw [hkp.get 25]; exact hst'.rap)
  have hq : (R'' 8).toNat = p + 2 := by rw [hkp.get 8]; exact h8
  have hnx : RoBytes (p + 2 + 1) [b] := by rw [show p + 2 + 1 = p + 1 + 2 by omega]; exact hro2
  cases kk with
  | pct => exact absurd rfl hkk
  | s => exact fmt_s hlive hst'' hq harg.word (harg.str rfl) hnx (sh_s hsh) hK
  | c => exact fmt_c hlive hst'' hq harg.word hnx (sh_c hsh) hK
  | d => exact fmt_d0 hlive hst'' hq harg.word hnx hsh hK
  | u => exact fmt_u0 hlive hst'' hq harg.word hnx hsh hK
  | o => exact fmt_o0 hlive hst'' hq (by rw [hkp.get 14]; exact h14) harg.word hnx (sh_o hsh) hK

/-- A conversion `%lk` (`k` not `%`) from the loop head. -/
theorem fmt_conv_ft {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) (kk : Conv) (hkk : kk ≠ .pct) {b : BitVec 8}
    (hro : RoBytes (p + 1) ([108#8] ++ [kk.char] ++ [b])) {a : FArg} (harg : ArgOK S M ap kk a)
    (hsh : (out ++ convOut false true kk a).length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ convOut false true kk a) (p + 2) b) :
    DWS live S Q t0 dst out 0x800001d0#64 R M := by
  rw [RoBytes.append] at hro
  obtain ⟨hro1, hro2⟩ := hro
  simp only [List.length_append, List.length_cons, List.length_nil] at hro2
  refine fmt_flags_ft hlive hst hp h15 (kc := kk.char) hro1 fun R' hst' h8 h14 h15' => ?_
  refine fmt_tab hlive hst' true kk h15' fun R'' hkp => ?_
  have hst'' := hst'.regs (R' := R'') (ap' := ap) (by keeps_tac (hkp.mono (by decide)))
    (by rw [hkp.get 25]; exact hst'.rap)
  have hq : (R'' 8).toNat = p + 2 := by rw [hkp.get 8]; exact h8
  have hnx : RoBytes (p + 2 + 1) [b] := by rw [show p + 2 + 1 = p + 1 + 2 by omega]; exact hro2
  cases kk with
  | pct => exact absurd rfl hkk
  | s => exact fmt_s hlive hst'' hq harg.word (harg.str rfl) hnx (sh_s hsh) hK
  | c => exact fmt_c hlive hst'' hq harg.word hnx (sh_c hsh) hK
  | d => exact fmt_d1 hlive hst'' hq harg.word hnx hsh hK
  | u => exact fmt_u1 hlive hst'' hq harg.word hnx hsh hK
  | o => exact fmt_o1 hlive hst'' hq (by rw [hkp.get 14]; exact h14) harg.word hnx (sh_o hsh) hK

/-- A conversion `%#lk` (`k` not `%`) from the loop head. -/
theorem fmt_conv_tt {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) (kk : Conv) (hkk : kk ≠ .pct) {b : BitVec 8}
    (hro : RoBytes (p + 1) ([35#8, 108#8] ++ [kk.char] ++ [b])) {a : FArg} (harg : ArgOK S M ap kk a)
    (hsh : (out ++ convOut true true kk a).length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 (ap + 8) (out ++ convOut true true kk a) (p + 3) b) :
    DWS live S Q t0 dst out 0x800001d0#64 R M := by
  rw [RoBytes.append] at hro
  obtain ⟨hro1, hro2⟩ := hro
  simp only [List.length_append, List.length_cons, List.length_nil] at hro2
  refine fmt_flags_tt hlive hst hp h15 (kc := kk.char) hro1 fun R' hst' h8 h14 h15' => ?_
  refine fmt_tab hlive hst' true kk h15' fun R'' hkp => ?_
  have hst'' := hst'.regs (R' := R'') (ap' := ap) (by keeps_tac (hkp.mono (by decide)))
    (by rw [hkp.get 25]; exact hst'.rap)
  have hq : (R'' 8).toNat = p + 3 := by rw [hkp.get 8]; exact h8
  have hnx : RoBytes (p + 3 + 1) [b] := by rw [show p + 3 + 1 = p + 1 + 3 by omega]; exact hro2
  cases kk with
  | pct => exact absurd rfl hkk
  | s => exact fmt_s hlive hst'' hq harg.word (harg.str rfl) hnx (sh_s hsh) hK
  | c => exact fmt_c hlive hst'' hq harg.word hnx (sh_c hsh) hK
  | d => exact fmt_d1 hlive hst'' hq harg.word hnx hsh hK
  | u => exact fmt_u1 hlive hst'' hq harg.word hnx hsh hK
  | o => exact fmt_o1 hlive hst'' hq (by rw [hkp.get 14]; exact h14) harg.word hnx (sh_o hsh) hK

/-- `%%` from the loop head. -/
theorem fmt_pct_ff {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) {b : BitVec 8}
    (hro : RoBytes (p + 1) ([37#8] ++ [b])) (hsh : out.length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ [37#8]) (p + 1) b) :
    DWS live S Q t0 dst out 0x800001d0#64 R M := by
  rw [RoBytes.append] at hro
  obtain ⟨hro1, hro2⟩ := hro
  simp only [List.length_append, List.length_cons, List.length_nil] at hro2
  refine fmt_flags_ff hlive hst hp h15 (kc := Conv.pct.char) Conv.pct.char_ne hro1 fun R' hst' h8 h14 h15' => ?_
  refine fmt_tab hlive hst' false .pct h15' fun R'' hkp => ?_
  have hst'' := hst'.regs (R' := R'') (ap' := ap) (by keeps_tac (hkp.mono (by decide)))
    (by rw [hkp.get 25]; exact hst'.rap)
  have hq : (R'' 8).toNat = p + 1 := by rw [hkp.get 8]; exact h8
  have hnx : RoBytes (p + 1 + 1) [b] := by rw [show p + 1 + 1 = p + 1 + 1 by omega]; exact hro2
  exact fmt_pct hlive hst'' hq hnx hsh hK

/-- `%#%` from the loop head. -/
theorem fmt_pct_tf {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) {b : BitVec 8}
    (hro : RoBytes (p + 1) ([35#8] ++ [37#8] ++ [b])) (hsh : out.length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ [37#8]) (p + 2) b) :
    DWS live S Q t0 dst out 0x800001d0#64 R M := by
  rw [RoBytes.append] at hro
  obtain ⟨hro1, hro2⟩ := hro
  simp only [List.length_append, List.length_cons, List.length_nil] at hro2
  refine fmt_flags_tf hlive hst hp h15 (kc := Conv.pct.char) Conv.pct.char_ne hro1 fun R' hst' h8 h14 h15' => ?_
  refine fmt_tab hlive hst' false .pct h15' fun R'' hkp => ?_
  have hst'' := hst'.regs (R' := R'') (ap' := ap) (by keeps_tac (hkp.mono (by decide)))
    (by rw [hkp.get 25]; exact hst'.rap)
  have hq : (R'' 8).toNat = p + 2 := by rw [hkp.get 8]; exact h8
  have hnx : RoBytes (p + 2 + 1) [b] := by rw [show p + 2 + 1 = p + 1 + 2 by omega]; exact hro2
  exact fmt_pct hlive hst'' hq hnx hsh hK

/-- `%l%` from the loop head. -/
theorem fmt_pct_ft {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) {b : BitVec 8}
    (hro : RoBytes (p + 1) ([108#8] ++ [37#8] ++ [b])) (hsh : out.length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ [37#8]) (p + 2) b) :
    DWS live S Q t0 dst out 0x800001d0#64 R M := by
  rw [RoBytes.append] at hro
  obtain ⟨hro1, hro2⟩ := hro
  simp only [List.length_append, List.length_cons, List.length_nil] at hro2
  refine fmt_flags_ft hlive hst hp h15 (kc := Conv.pct.char) hro1 fun R' hst' h8 h14 h15' => ?_
  refine fmt_tab hlive hst' true .pct h15' fun R'' hkp => ?_
  have hst'' := hst'.regs (R' := R'') (ap' := ap) (by keeps_tac (hkp.mono (by decide)))
    (by rw [hkp.get 25]; exact hst'.rap)
  have hq : (R'' 8).toNat = p + 2 := by rw [hkp.get 8]; exact h8
  have hnx : RoBytes (p + 2 + 1) [b] := by rw [show p + 2 + 1 = p + 1 + 2 by omega]; exact hro2
  exact fmt_pct hlive hst'' hq hnx hsh hK

/-- `%#l%` from the loop head. -/
theorem fmt_pct_tt {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {p : Nat} (hp : (R 8).toNat = p)
    (h15 : (R 15).toNat = 37) {b : BitVec 8}
    (hro : RoBytes (p + 1) ([35#8, 108#8] ++ [37#8] ++ [b])) (hsh : out.length + 1 < 2 ^ 62)
    (hK : FmtK live S Q t0 M0 sp k dst R0 ap (out ++ [37#8]) (p + 3) b) :
    DWS live S Q t0 dst out 0x800001d0#64 R M := by
  rw [RoBytes.append] at hro
  obtain ⟨hro1, hro2⟩ := hro
  simp only [List.length_append, List.length_cons, List.length_nil] at hro2
  refine fmt_flags_tt hlive hst hp h15 (kc := Conv.pct.char) hro1 fun R' hst' h8 h14 h15' => ?_
  refine fmt_tab hlive hst' true .pct h15' fun R'' hkp => ?_
  have hst'' := hst'.regs (R' := R'') (ap' := ap) (by keeps_tac (hkp.mono (by decide)))
    (by rw [hkp.get 25]; exact hst'.rap)
  have hq : (R'' 8).toNat = p + 3 := by rw [hkp.get 8]; exact h8
  have hnx : RoBytes (p + 3 + 1) [b] := by rw [show p + 3 + 1 = p + 1 + 3 by omega]; exact hro2
  exact fmt_pct hlive hst'' hq hnx hsh hK

/-! ## The loop (`0x800001d0`) -/

/-- The arguments the pieces take, at `ap`, over `format`'s entry memory
`M0`, outside the frames and the sink's bytes. -/
def ArgsAt (S : Nat → Prop) (M0 : Mem) (sp k : Nat) (dst : SinkDst) :
    Nat → List Piece → List FArg → Prop
  | _, [], _ => True
  | ap, .lit _ :: ps, args => ArgsAt S M0 sp k dst ap ps args
  | ap, .conv _ _ .pct :: ps, args => ArgsAt S M0 sp k dst ap ps args
  | ap, .conv _ _ kk :: ps, a :: args => (ArgOK S M0 ap kk a ∧
      ∀ j, j < 8 → (ap + j < sp - 192 ∨ sp ≤ ap + j) ∧ ¬ dst.Byte k (ap + j)) ∧
      ArgsAt S M0 sp k dst (ap + 8) ps args
  | _, .conv _ _ _ :: _, [] => False

/-- An argument of `format`'s entry memory in the loop's memory. -/
theorem ArgOK.transport {S : Nat → Prop} {M0 M : Mem} {ap : Nat} {kk : Conv} {a : FArg}
    (h : ArgOK S M0 ap kk a) (hag : ∀ j, j < 8 → imgM M (ap + j) = imgM M0 (ap + j)) :
    ArgOK S M ap kk a :=
  ⟨⟨h.word.own, h.word.lo, h.word.hi, (ldv_ld_congr hag).trans h.word.val⟩, h.str⟩

/-- The first byte of the format from the pieces `ps` (the NUL at the end). -/
def fbyte : List Piece → BitVec 8
  | [] => 0#8
  | .lit c :: _ => c
  | .conv .. :: _ => 37#8

theorem fbyte_ne {ps : List Piece} (hok : ∀ pc ∈ ps, pc.ok) (hne : ps ≠ []) : fbyte ps ≠ 0#8 := by
  cases ps with
  | nil => exact absurd rfl hne
  | cons pc ps =>
    cases pc with
    | lit c => exact (hok _ List.mem_cons_self).1
    | conv => simp [fbyte]

theorem fmtBytes_cons (pc : Piece) (ps : List Piece) :
    fmtBytes (pc :: ps) = pc.bytes ++ fmtBytes ps := by
  simp [fmtBytes]

theorem fmtBytes_head (ps : List Piece) : ∃ l, fmtBytes ps ++ [0#8] = fbyte ps :: l := by
  cases ps with
  | nil => exact ⟨[], rfl⟩
  | cons pc ps =>
    cases pc with
    | lit c => exact ⟨fmtBytes ps ++ [0#8], by simp [fmtBytes, Piece.bytes, fbyte]⟩
    | conv alt lng kk =>
      exact ⟨_, by simp only [fmtBytes_cons, Piece.bytes, List.cons_append, List.append_assoc]; rfl⟩

/-- **The loop** of `format` from the head at `0x800001d0`: the pieces `ps`
at `p` (then the NUL) with the arguments `args` at `ap` produce the rest of
`outF`, then the exit at `0x80000298`. -/
theorem fmt_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {outF : List (BitVec 8)} (hshF : outF.length + 1 < 2 ^ 62)
    (hexit : ∀ ap R M, FmtState S M0 sp k dst R0 ap outF R M →
      DWS live S Q t0 dst outF 0x80000298#64 R M) :
    ∀ (ps : List Piece) (p ap : Nat) (args : List FArg) (out : List (BitVec 8))
      (R : Nat → BitVec 64) (M : Mem), ps ≠ [] → (∀ pc ∈ ps, pc.ok) →
      FmtState S M0 sp k dst R0 ap out R M → (R 8).toNat = p → (R 15).toNat = (fbyte ps).toNat →
      RoBytes p (fmtBytes ps ++ [0#8]) → ArgsAt S M0 sp k dst ap ps args →
      out ++ fmt ps args = outF → DWS live S Q t0 dst out 0x800001d0#64 R M := by
  intro ps
  induction ps with
  | nil => intro p ap args out R M hne; exact absurd rfl hne
  | cons pc ps ih =>
  intro p ap args out R M _ hok hst hp h15 hro hargs hout
  have hokt : ∀ pc ∈ ps, pc.ok := fun x hx => hok x (List.mem_cons_of_mem _ hx)
  obtain ⟨l, hl⟩ := fmtBytes_head ps
  rw [fmtBytes_cons, List.append_assoc, hl, RoBytes.append] at hro
  obtain ⟨hro1, hro2⟩ := hro
  have hpos : 1 ≤ pc.bytes.length := by cases pc <;> simp [Piece.bytes]
  -- what follows the piece
  have hK : ∀ ap' args' out', out' ++ fmt ps args' = outF → ArgsAt S M0 sp k dst ap' ps args' →
      FmtK live S Q t0 M0 sp k dst R0 ap' out' (p + pc.bytes.length - 1) (fbyte ps) := by
    intro ap' args' out' hout' hargs'
    constructor
    · intro hb R' M' hst' hq h15'
      have hne : ps ≠ [] := by rintro rfl; exact hb rfl
      refine ih (p + pc.bytes.length) ap' args' out' R' M' hne hokt hst' (by rw [hq]; omega) h15'
        (by rw [hl]; exact hro2) hargs' hout'
    · intro hb R' M' hst'
      have hnil : ps = [] := by
        refine Classical.byContradiction fun hne => fbyte_ne hokt hne hb
      subst hnil
      simp only [fmt, List.append_nil] at hout'
      subst hout'
      exact hexit ap' R' M' hst'
  -- the next byte alone
  have hnx : RoBytes (p + pc.bytes.length) [fbyte ps] := by
    have := hro2; rw [show fbyte ps :: l = [fbyte ps] ++ l from rfl, RoBytes.append] at this
    exact this.1
  have hshl : ∀ o, o ++ fmt ps args = outF → o.length + 1 < 2 ^ 62 := fun o h => by
    have := congrArg List.length h; simp at this; omega
  cases pc with
  | lit c =>
    obtain ⟨hc0, hc37⟩ := hok _ List.mem_cons_self
    simp only [fmt] at hout
    have hout2 : (out ++ [c]) ++ fmt ps args = outF := by simpa using hout
    obtain ⟨hb1, -, -, -, -⟩ := hro1
    refine fmt_lit hlive hst hp (c := c) ?_ hc37 hnx
      (by have := hshl _ hout2; simp at this; omega) (hK ap args (out ++ [c]) hout2 hargs)
    apply BitVec.eq_of_toNat_eq; rw [h15, toNat_zext8]; rfl
  | conv alt lng kk =>
    have h37 : (R 15).toNat = 37 := h15
    obtain ⟨-, -, -, -, hrt⟩ := hro1
    -- the bytes after `%`, then the next byte
    have hro' : RoBytes (p + 1) ((if alt then [35#8] else []) ++ (if lng then [108#8] else []) ++
        [kk.char] ++ [fbyte ps]) := by
      rw [RoBytes.append]
      refine ⟨by simpa [Piece.bytes] using hrt, ?_⟩
      have e : p + 1 + ((if alt then [35#8] else []) ++ (if lng then [108#8] else []) ++
          [kk.char]).length = p + (Piece.conv alt lng kk).bytes.length := by
        cases alt <;> cases lng <;> simp [Piece.bytes] <;> omega
      rw [e]; exact hnx
    have hlen : p + (Piece.conv alt lng kk).bytes.length - 1 =
        p + (1 + (if alt then 1 else 0) + (if lng then 1 else 0)) := by
      cases alt <;> cases lng <;> simp [Piece.bytes] <;> omega
    by_cases hkk : kk = .pct
    · subst hkk
      simp only [fmt] at hout
      have hout2 : (out ++ [37#8]) ++ fmt ps args = outF := by simpa using hout
      have hK' := hK ap args (out ++ [37#8]) hout2 hargs
      rw [hlen] at hK'
      have hsh := hshl _ hout2
      simp only [List.length_append, List.length_singleton] at hsh
      cases alt <;> cases lng <;> simp at hro' hK'
      · exact fmt_pct_ff hlive hst hp h37 hro' (by omega) hK'
      · exact fmt_pct_ft hlive hst hp h37 hro' (by omega) hK'
      · exact fmt_pct_tf hlive hst hp h37 hro' (by omega) hK'
      · exact fmt_pct_tt hlive hst hp h37 hro' (by omega) hK'
    · cases args with
      | nil => cases kk <;> simp [ArgsAt] at hargs; exact (hkk rfl).elim
      | cons a args =>
      have hA : (ArgOK S M0 ap kk a ∧ ∀ j, j < 8 → (ap + j < sp - 192 ∨ sp ≤ ap + j) ∧
          ¬ dst.Byte k (ap + j)) ∧ ArgsAt S M0 sp k dst (ap + 8) ps args := by
        cases kk <;> first | exact absurd rfl hkk | exact hargs
      obtain ⟨⟨harg0, hoffa⟩, hargs'⟩ := hA
      have harg := harg0.transport fun j hj => hst.frame _ (hoffa j hj).1 (hoffa j hj).2
      have hfmt : fmt (.conv alt lng kk :: ps) (a :: args) = convOut alt lng kk a ++ fmt ps args := by
        cases kk <;> first | exact absurd rfl hkk | rfl
      rw [hfmt] at hout
      have hout2 : (out ++ convOut alt lng kk a) ++ fmt ps args = outF := by simpa using hout
      have hK' := hK (ap + 8) args (out ++ convOut alt lng kk a) hout2 hargs'
      rw [hlen] at hK'
      have hsh : (out ++ convOut alt lng kk a).length + 1 < 2 ^ 62 := by
        have := congrArg List.length hout2; simp only [List.length_append] at this ⊢; omega
      cases alt <;> cases lng <;> simp at hro' hK'
      · exact fmt_conv_ff hlive hst hp h37 kk hkk hro' harg hsh hK'
      · exact fmt_conv_ft hlive hst hp h37 kk hkk hro' harg hsh hK'
      · exact fmt_conv_tf hlive hst hp h37 kk hkk hro' harg hsh hK'
      · exact fmt_conv_tt hlive hst hp h37 kk hkk hro' harg hsh hK'

end Dc.Mach
