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

/-! ## Arguments and frames of the callers -/

/-- The strings of the `%s` arguments, in `.rodata`. -/
def ArgStrs : List Piece → List FArg → Prop
  | [], _ => True
  | .lit _ :: ps, args => ArgStrs ps args
  | .conv _ _ .pct :: ps, args => ArgStrs ps args
  | .conv _ _ .s :: ps, a :: args => RoStr a.w.toNat a.s ∧ ArgStrs ps args
  | .conv _ _ _ :: ps, _ :: args => ArgStrs ps args
  | .conv _ _ _ :: _, [] => False

/-- The argument words at `ap`, `ap + 8`, …. -/
def ArgWords (S : Nat → Prop) (M : Mem) (ap : Nat) (args : List FArg) : Prop :=
  ∀ i (h : i < args.length), ArgW S M (ap + 8 * i) args[i].w

theorem ArgWords.tail {S : Nat → Prop} {M : Mem} {ap : Nat} {a : FArg} {args : List FArg}
    (h : ArgWords S M ap (a :: args)) : ArgWords S M (ap + 8) args := fun i hi => by
  rw [show ap + 8 + 8 * i = ap + 8 * (i + 1) by omega]
  exact h (i + 1) (by simp only [List.length_cons]; omega)

/-- The arguments as `format` takes them (`ArgsAt`): the words and strings,
outside `format`'s area and the sink's bytes. -/
theorem argsAt_of {S : Nat → Prop} {M : Mem} {sp k : Nat} {dst : SinkDst} :
    ∀ (ps : List Piece) (ap : Nat) (args : List FArg), ArgWords S M ap args → ArgStrs ps args →
      (∀ j, ap ≤ j → j < ap + 8 * args.length → (j < sp - 192 ∨ sp ≤ j) ∧ ¬ dst.Byte k j) →
      ArgsAt S M sp k dst ap ps args := by
  intro ps
  induction ps with
  | nil => intro _ _ _ _ _; trivial
  | cons pc ps ih =>
  intro ap args hw hs hr
  have hone : ∀ a args', args = a :: args' → ∀ kk : Conv, (kk = .s → RoStr a.w.toNat a.s) →
      ArgStrs ps args' →
      (ArgOK S M ap kk a ∧ ∀ j, j < 8 → (ap + j < sp - 192 ∨ sp ≤ ap + j) ∧ ¬ dst.Byte k (ap + j)) ∧
        ArgsAt S M sp k dst (ap + 8) ps args' := by
    intro a args' e kk hstr hs'
    subst e
    refine ⟨⟨⟨by
      have h0 := hw 0 (by simp)
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at h0; exact h0, hstr⟩, fun j hj => hr _ (by omega) ?_⟩,
      ih (ap + 8) args' hw.tail hs' fun j h1 h2 => hr j (by omega) ?_⟩
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
  cases pc with
  | lit c => exact ih ap args hw hs hr
  | conv alt lng kk =>
    cases kk with
    | pct => exact ih ap args hw hs hr
    | s => cases args with
      | nil => exact hs.elim
      | cons a args' => exact hone a args' rfl .s (fun _ => hs.1) hs.2
    | c => cases args with
      | nil => exact hs.elim
      | cons a args' => exact hone a args' rfl .c (fun e => nomatch e) hs
    | d => cases args with
      | nil => exact hs.elim
      | cons a args' => exact hone a args' rfl .d (fun e => nomatch e) hs
    | u => cases args with
      | nil => exact hs.elim
      | cons a args' => exact hone a args' rfl .u (fun e => nomatch e) hs
    | o => cases args with
      | nil => exact hs.elim
      | cons a args' => exact hone a args' rfl .o (fun e => nomatch e) hs

/-- Argument words survive a memory that agrees on them. -/
theorem ArgWords.transport {S : Nat → Prop} {M M' : Mem} {ap : Nat} {args : List FArg}
    (h : ArgWords S M ap args)
    (hag : ∀ j, ap ≤ j → j < ap + 8 * args.length → imgM M' j = imgM M j) :
    ArgWords S M' ap args := fun i hi =>
  ⟨(h i hi).own, (h i hi).lo, (h i hi).hi,
    (ldv_ld_congr fun j hj => hag _ (by omega) (by omega)).trans (h i hi).val⟩

/-- A callee's frame inside the caller's. -/
theorem StackFrame.sub {S : Nat → Prop} {sp n m : Nat} (h : StackFrame S sp (m + n))
    (hm : m % 16 = 0) : StackFrame S (sp - m) n where
  own a h1 h2 := h.own a (by omega) (by omega)
  lo := by have := h.lo; omega
  hi := by have := h.hi; omega
  al := by have := h.al; omega

/-- A stream survives a memory that agrees on its word. -/
theorem FdAt.transport {S : Nat → Prop} {M M' : Mem} {f fd : Nat} (h : FdAt S M f fd)
    (hag : ∀ j, j < 4 → imgM M' (f + j) = imgM M (f + j)) : FdAt S M' f fd :=
  ⟨h.own, (ldv_congr .lw fun j hj => hag j hj).trans h.val, h.lo, h.hi, h.small⟩

/-! ## `vfprintf` (`0x80000748`) -/

/-- **`vfprintf(f, fmt, ap)`** at `0x80000748` to the stream `f` (descriptor
`fd ≠ 1`, not `stdout`): prints nothing, returns the length of
`fmt ps args` as an `int`; only the 240 bytes below `sp` change; clobbers
`t0`, `a0`–`a7`. -/
theorem vfprintf_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp f fd p ap : Nat} {ps : List Piece} {args : List FArg}
    (hfr : StackFrame S sp 240) (hfd : FdAt S M f fd) (hne : fd ≠ 1)
    (hfoff : f + 4 ≤ sp - 240 ∨ sp ≤ f) (hok : ∀ pc ∈ ps, pc.ok)
    (hro : RoBytes p (fmtBytes ps ++ [0#8])) (hw : ArgWords S M ap args) (hstr : ArgStrs ps args)
    (hap : ∀ j, ap ≤ j → j < ap + 8 * args.length → j < sp - 240 ∨ sp ≤ j)
    (hsh : (fmt ps args).length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hsp : (R 2).toNat = sp) (h10 : (R 10).toNat = f)
    (h11 : (R 11).toNat = p) (h12 : (R 12).toNat = ap) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps euClob R' R → R' 10 = sx32 (BitVec.ofNat 64 (fmt ps args).length) →
      (∀ a, (a < sp - 240 ∨ sp ≤ a) → imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x80000748#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive at 0x80000168
  all_goals (try dc_frame hfr)
  have e0 : (R 2 + 18446744073709551568#64).toNat = sp - 48 := by
    rw [BitVec.toNat_add, hsp]; simp only [BitVec.toNat_ofNat]; omega
  have e : ∀ o, o < 48 → (R 2 + 18446744073709551568#64 + BitVec.ofNat 64 o).toNat = sp - 48 + o :=
    fun o ho => by rw [BitVec.toNat_add, e0]; simp only [BitVec.toNat_ofNat]; omega
  simp only [e 40 (by omega), e 8 (by omega), e 16 (by omega), e 24 (by omega), e0]
  have hfd' := hfd.transport (M' := writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48, 8, R 10)]) [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 8, 8, 0#64)])
      [(sp - 48 + 16, 8, 0#64)]) [(sp - 48 + 24, 8, 0#64)]) fun j hj => by
    simp (disch := omega) only [imgM_store_miss]
  refine format_spec hlive (sp := sp - 48) (k := sp - 48) (ap := ap) (dst := .stream f fd)
    (hfr.sub (m := 48) (n := 192) (by omega)) ?hs ?hoff hok hro ?hargs hsh _ ?hsp ?h10 ?h11 ?h12
    (by gnorm) fun R' M' hkp h10' hs' hfr' => ?_
  case hs =>
    exact {
      own := fun i hi => hfr.own _ (by omega) (by omega)
      al := by omega
      lo := by omega
      hi := by omega
      fw := by
        simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss, SinkDst.fw]
        rw [← h10]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (R 10).isLt]
      len := by simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss, List.length_nil]
      short := by simp
      dstAt := .stream hfd' hne (by omega) }
  case hoff =>
    intro a ha
    rcases ha with ha | ha <;> omega
  case hargs =>
    refine argsAt_of ps ap args (hw.transport fun j h1 h2 => ?_) hstr fun j h1 h2 => ?_
    · have := hap j h1 h2
      simp (disch := omega) only [imgM_store_miss]
    · have := hap j h1 h2
      exact ⟨by omega, fun hb => by have := hb.1; have := hb.2; omega⟩
  case hsp => gnorm; exact e0
  case h10 => gnorm; exact e0
  case h11 => gnorm; exact h11
  case h12 => gnorm; exact h12
  gnorm
  have hsp' : (R' 2).toNat = sp - 48 := by rw [hkp.get 2]; gnorm; exact e0
  have hra : ldv .ld M' (sp - 48 + 40) = R 1 := by
    rw [ldv_ld_congr (Mt' := M') (Mt := writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48, 8, R 10)]) [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 8, 8, 0#64)])
      [(sp - 48 + 16, 8, 0#64)]) [(sp - 48 + 24, 8, 0#64)]) fun j hj =>
        hfr' _ (.inr (by omega)) fun hb => by have := hb.2; omega]
    simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss]
  have e40 : (R' 2 + 40#64).toNat = sp - 48 + 40 := by rw [BitVec.toNat_add, hsp']; gnorm; omega
  dx_run hlive
  all_goals (try dc_frame hfr)
  all_goals simp only [e40, hra]
  · gnorm; exact hal
  refine hk _ M' ?_ (by gnorm; exact h10') fun a ha => ?_
  · refine Keeps.restore (by rw [hkp.get 2]; gnorm; exact add_lits_cancel _ _ _ (by decide)) ?_
    refine Keeps.restore rfl ?_
    exact (hkp.mono (by decide)).trans (by keeps_tac (Keeps.refl _ _))
  · rw [hfr' a (by omega) fun hb => by have := hb.1; have := hb.2; omega]
    simp (disch := omega) only [imgM_store_miss]

end Dc.Mach
