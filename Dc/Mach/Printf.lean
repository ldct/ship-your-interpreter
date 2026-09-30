import Dc.Mach.Format

/-!
# `format.constprop.0`, `vfprintf`, `fprintf`, `snprintf`

The entry points of the formatter (`libc.c`), over the loop `fmt_loop`
(`Format.lean`):

- `format_spec` (`0x80000168`): `format(k, fmt, ap)` from an empty sink at
  `k`; the sink receives `fmt ps args` (`Dc.Mach.fmt`) and `a0` is its length
  (as the C `int`); only `format`'s 192-byte stack area (its frame and
  `emit_unsigned`'s) and the sink's count word and buffer change.
- `vfprintf_spec`, `fprintf_spec`: to a stream that is not `stdout` (every
  call in dc passes `stderr`): the run returns with the length, printing
  nothing, and only its stack area changes.
- `snprintf_spec`: into an owned buffer of `n > 0` bytes: its first
  `min (len, n - 1)` bytes are the output, then the NUL.

`fprintf` and `snprintf` take their variable arguments in registers
(`a2`–`a7` and `a3`–`a7`), which the callee spills below the caller's `sp`;
dc passes at most five.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## `format`'s exit and entry -/

/-- `format`'s exit at `0x80000298`: `a0` the count (`lw`), the saved
registers restored, back at the entry's `ra`. -/
theorem fmt_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M0 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {R0 : Nat → BitVec 64}
    {ap : Nat} {out : List (BitVec 8)} {R : Nat → BitVec 64} {M : Mem}
    (hst : FmtState S M0 sp k dst R0 ap out R M) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps euClob R' R0 → R' 10 = sx32 (BitVec.ofNat 64 out.length) →
      DW live S Q (R0 1) R' M) :
    DW live S Q 0x80000298#64 R M := by
  have hs := hst.sink
  have hfr := hst.fr
  have hsv := hst.saved
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have hkal := hs.al
  have hklo := hs.lo
  have hkhi := hs.hi
  have hk9 := hst.rk
  have h2 := hst.rsp
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive at 0x80000210
  all_goals (try own_by hs)
  have ha0 : ldv .lw M (R 9 + 24#64).toNat = sx32 (BitVec.ofNat 64 out.length) := by
    rw [lwOfLd, BitVec.toNat_add, hk9]; gnorm
    rw [show (k + 24) % 2 ^ 64 = k + 24 by omega, hs.len]
  rw [ha0]
  generalize sx32 (BitVec.ofNat 64 out.length) = v at hk
  have e : ∀ o, o < 96 → (R 2 + BitVec.ofNat 64 o).toNat = sp - 96 + o := fun o ho => by
    rw [BitVec.toNat_add, h2, BitVec.toNat_ofNat]; omega
  dx_run hlive
  all_goals (try dc_frame hfr)
  all_goals simp only [e 88 (by omega), e 80 (by omega), e 72 (by omega), e 64 (by omega),
    e 56 (by omega), e 48 (by omega), e 40 (by omega), e 32 (by omega), e 24 (by omega),
    e 16 (by omega), e 8 (by omega), hsv.ra, hsv.s0, hsv.s1, hsv.s2, hsv.s3, hsv.s4, hsv.s5,
    hsv.s6, hsv.s7, hsv.s8, hsv.s9]
  · gnorm; exact hal
  refine hk _ ?_ (by gnorm)
  refine Keeps.restore hst.rsp' ?_
  iterate 11 refine Keeps.restore rfl ?_
  exact Keeps.upd _ (by decide) (hst.keep.mono (by decide))

/-- **`format(k, fmt, ap)`** at `0x80000168`, from an empty sink at `k`:
the pieces `ps` at `p` (then the NUL) with the arguments `args` at `ap`; the
sink receives `fmt ps args`, `a0` is its length as an `int`; only the 192
bytes below `sp` and the sink's count word and buffer change; clobbers `t0`,
`a0`–`a7`. -/
theorem format_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k p ap : Nat} {dst : SinkDst} {ps : List Piece}
    {args : List FArg} (hfr : StackFrame S sp 192) (hs : SinkAt S M k dst [])
    (hoff : ∀ a, dst.Read k a → a < sp - 192 ∨ sp ≤ a) (hok : ∀ pc ∈ ps, pc.ok)
    (hro : RoBytes p (fmtBytes ps ++ [0#8])) (hargs : ArgsAt S M sp k dst ap ps args)
    (hsh : (fmt ps args).length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hsp : (R 2).toNat = sp) (h10 : (R 10).toNat = k)
    (h11 : (R 11).toNat = p) (h12 : (R 12).toNat = ap) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps euClob R' R → R' 10 = sx32 (BitVec.ofNat 64 (fmt ps args).length) →
      SinkAt S M' k dst (fmt ps args) →
      (∀ a, (a < sp - 192 ∨ sp ≤ a) → ¬ dst.Byte k a → imgM M' a = imgM M a) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80000168#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨l, hl⟩ := fmtBytes_head ps
  have hb := hro
  rw [hl] at hb
  obtain ⟨hb1, hb2, hb3, hb4, -⟩ := hb
  have ea : (R 11 + sign_extend (m := 64) (0x000#12)).toNat = p := by gnorm; exact h11
  dx_ro hlive
  · rw [ea]; simp only [LdOK]; omega
  · rw [ea]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx
    rw [hb1]; exact hb2
  rw [ea, ldvf_lbu, hb1]
  by_cases hne : ps = []
  · subst hne
    simp only [fbyte, fmt] at hk ⊢
    dx_run hlive
    refine hk _ M ?_ (by gnorm; rfl) hs fun _ _ _ => rfl
    keeps_tac (Keeps.refl _ _)
  have hb0 := fbyte_ne hok hne
  have hz : ¬ (zero_extend (m := 64) (fbyte ps)) = 0#64 := by
    intro e; apply hb0; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e; rw [toNat_zext8] at this; rw [this]; rfl
  dx_run hlive at 0x800001d0
  all_goals (try dc_frame hfr)
  have e : ∀ o, o < 96 → (R 2 + 18446744073709551520#64 + BitVec.ofNat 64 o).toNat = sp - 96 + o :=
    fun o ho => by rw [BitVec.toNat_add, BitVec.toNat_add, hsp]; simp only [BitVec.toNat_ofNat]; omega
  simp only [e 88 (by omega), e 80 (by omega), e 72 (by omega), e 64 (by omega),
    e 56 (by omega), e 48 (by omega), e 40 (by omega), e 32 (by omega), e 24 (by omega),
    e 16 (by omega), e 8 (by omega)]
  refine fmt_loop hlive hsh (fun ap' R' M' hst' => fmt_exit hlive hst' hal fun R'' hkp h10' =>
      hk R'' M' hkp h10' hst'.sink hst'.frame)
    ps p ap args [] _ _ hne hok ?_ (by gnorm; exact h11) (by gnorm; exact toNat_zext8 _) hro hargs
    (by simp)
  exact {
    rk := by gnorm; exact h10
    t2 := by gnorm
    one := by gnorm
    pct := by gnorm
    ell := by gnorm
    hash := by gnorm
    t1 := by gnorm
    n18 := by gnorm
    rap := by gnorm; exact h12
    rsp := by gnorm; rw [BitVec.toNat_add, hsp]; gnorm; omega
    rsp' := by gnorm; exact add_lits_cancel _ _ _ (by decide)
    keep := by keeps_tac (Keeps.refl _ _)
    sink := hs.transport fun a ha => by
      have := hoff a ha
      simp (disch := omega) only [imgM_store_miss]
    frame := fun a ha _ => by simp (disch := omega) only [imgM_store_miss]
    saved := by constructor <;> simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss]
    off := hoff
    fr := hfr }

end Dc.Mach
