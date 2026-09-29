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
def FmtK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (M0 : Mem)
    (sp k : Nat) (dst : SinkDst) (R0 : Nat → BitVec 64) (ap : Nat) (out : List (BitVec 8))
    (q : Nat) (b : BitVec 8) : Prop :=
  (b ≠ 0#8 → ∀ R M, FmtState S M0 sp k dst R0 ap out R M → (R 8).toNat = q + 1 →
    (R 15).toNat = b.toNat → DW live S Q 0x800001d0#64 R M) ∧
  (b = 0#8 → ∀ R M, FmtState S M0 sp k dst R0 ap out R M → DW live S Q 0x80000298#64 R M)

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
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {c b : BitVec 8}
    (hc : R 15 = zero_extend (m := 64) c) (hc37 : c ≠ 37#8) (hro : RoBytes (q + 1) [b])
    (hsh : out.length + 1 < 2 ^ 62) (hK : FmtK live S Q M0 sp k dst R0 ap (out ++ [c]) q b) :
    DW live S Q 0x800001d0#64 R M := by
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
  case c => gnorm; rw [hc, lo8_zext]
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
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {w : BitVec 64}
    (harg : ArgW S M ap w) {b : BitVec 8} (hro : RoBytes (q + 1) [b])
    (hsh : out.length + 1 < 2 ^ 62)
    (hK : FmtK live S Q M0 sp k dst R0 (ap + 8) (out ++ [w.setWidth 8]) q b) :
    DW live S Q 0x800002b0#64 R M := by
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
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b]) (hsh : out.length + 1 < 2 ^ 62)
    (hK : FmtK live S Q M0 sp k dst R0 ap (out ++ [37#8]) q b) :
    DW live S Q 0x8000038c#64 R M := by
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
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {q w : Nat} {str : List (BitVec 8)} (hstr : RoStr w str)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b]) (hsh : out.length + str.length < 2 ^ 62)
    (hK : FmtK live S Q M0 sp k dst R0 ap (out ++ str) q b) :
    ∀ m i (R : Nat → BitVec 64) (M : Mem), str.length - i = m → i < str.length →
      FmtState S M0 sp k dst R0 ap (out ++ str.take i) R M → (R 8).toNat = q →
      (R 15).toNat = w + i → R 14 = zero_extend (m := 64) (dcROImg (w + i)) →
      (R 13).toNat = out.length + i → (R 10).toNat = 1 → DW live S Q 0x80000264#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro m
  induction m with
  | zero => intro i R M hm hi; omega
  | succ m ih =>
  intro i R M hm hi hst hq h15 h14 h13 h10
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
  refine emit_80000270 hlive hs (str[i]) (by rw [hlen]; omega) _ ?kr ?fr ?lr ?l1 ?c ?one
    fun R' M' hk' hr13 hE' => ?_
  case kr => gnorm; exact hk9
  case fr => gnorm; exact hs.fw_nat hk9
  case lr => gnorm; rw [h13, hlen]
  case l1 => gnorm; rw [BitVec.toNat_add, h13, hlen]; gnorm; omega
  case c => gnorm; rw [h14, lo8_zext, hbi.1]
  case one => gnorm; exact h10
  have htake : out ++ str.take i ++ [str[i]] = out ++ str.take (i + 1) := by
    rw [List.append_assoc, List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  rw [htake] at hE'
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
      (by gnorm; exact hst'.rap)) ?_ ?_ ?_ ?_ ?_
    · gnorm; rw [hk'.get 8]; gnorm; exact hq
    · gnorm; exact e15
    · gnorm; rfl
    · gnorm; rw [hr13]; try omega
    · gnorm; rw [hk'.get 10]; gnorm; exact h10
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
    rw [htk] at hst'
    exact fmt_next_8000028c hlive (hst'.regs (by keeps_tac (Keeps.refl _ _)) (by gnorm; exact hst'.rap))
      (by gnorm; rw [hk'.get 8]; gnorm; exact hq) hro
      (fun hb R'' hs'' => hK.1 hb R'' M' hs'') (fun hb R'' hs'' => hK.2 hb R'' M' hs'')

/-- **`%s`** with the argument word `wv` at `ap`, a `.rodata` string `str`. -/
theorem fmt_s {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) {q : Nat} (hq : (R 8).toNat = q) {wv : BitVec 64}
    (harg : ArgW S M ap wv) {str : List (BitVec 8)} (hstr : RoStr wv.toNat str)
    {b : BitVec 8} (hro : RoBytes (q + 1) [b]) (hsh : out.length + str.length < 2 ^ 62)
    (hK : FmtK live S Q M0 sp k dst R0 (ap + 8) (out ++ str) q b) :
    DW live S Q 0x80000244#64 R M := by
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
    refine fmt_str hlive hstr hro hsh hK (str.length - 0) 0 _ M rfl hlen ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [List.take_zero, List.append_nil]
      exact hst8.regs (by keeps_to (Keeps.refl _ _)) (by gnorm; exact hst8.rap)
    · gnorm; exact hq
    · gnorm; rw [ew]; try rfl
    · gnorm; rw [Nat.add_zero]
    · gnorm; exact hs.len_nat (by rw [BitVec.toNat_add, hk9]; gnorm; omega)
    · gnorm

end Dc.Mach
