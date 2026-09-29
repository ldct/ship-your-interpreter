import Dc.Mach.EmitUnsigned

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
open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
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

end Dc.Mach
