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

/-- Name the memory of a `DW` goal (`hMb : Mb = …`), to state facts about it
without spelling it. -/
theorem DW.memEq {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {pc : BitVec 64} {R : Nat → BitVec 64} {M : Mem} (h : ∀ Mb, Mb = M → DW live S Q pc R Mb) :
    DW live S Q pc R M := h M rfl

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

/-! ## `fprintf` (`0x80000774`) -/

/-- The registers `fprintf` may change: `emit_unsigned`'s, `t1` and `t3`. -/
abbrev fprintfClob : List Nat := [5, 6, 10, 11, 12, 13, 14, 15, 16, 17, 28]

/-- **`fprintf(f, fmt, …)`** at `0x80000774` to the stream `f` (descriptor
`fd ≠ 1`, not `stdout`), with at most six variable arguments, the words in
`a2`–`a7`: prints nothing, returns the length of `fmt ps args` as an `int`;
only the 304 bytes below `sp` change. -/
theorem fprintf_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp f fd p : Nat} {ps : List Piece} {args : List FArg}
    (hfr : StackFrame S sp 304) (hfd : FdAt S M f fd) (hne : fd ≠ 1)
    (hfoff : f + 4 ≤ sp - 304 ∨ sp ≤ f) (hok : ∀ pc ∈ ps, pc.ok)
    (hro : RoBytes p (fmtBytes ps ++ [0#8])) (hstr : ArgStrs ps args)
    (hsh : (fmt ps args).length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hn : args.length ≤ 6)
    (hargs : ∀ i (h : i < args.length), args[i].w = R (12 + i))
    (hsp : (R 2).toNat = sp) (h10 : (R 10).toNat = f) (h11 : (R 11).toNat = p)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps fprintfClob R' R →
      R' 10 = sx32 (BitVec.ofNat 64 (fmt ps args).length) →
      (∀ a, (a < sp - 304 ∨ sp ≤ a) → imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x80000774#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive at 0x80000168
  all_goals (try dc_frame hfr)
  have e0 : (R 2 + 18446744073709551504#64).toNat = sp - 112 := by
    rw [BitVec.toNat_add, hsp]; simp only [BitVec.toNat_ofNat]; omega
  have e : ∀ o, o < 112 → (R 2 + 18446744073709551504#64 + BitVec.ofNat 64 o).toNat =
      sp - 112 + o :=
    fun o ho => by rw [BitVec.toNat_add, e0]; simp only [BitVec.toNat_ofNat]; omega
  simp only [e 64 (by omega), e 56 (by omega), e 16 (by omega), e 72 (by omega), e 80 (by omega),
    e 88 (by omega), e 96 (by omega), e 104 (by omega), e 24 (by omega), e 32 (by omega),
    e 40 (by omega), e 8 (by omega)]
  refine DW.memEq fun Mb hMb => ?_
  have hag : ∀ a, (a < sp - 112 ∨ sp ≤ a) → imgM Mb a = imgM M a := fun a ha => by
    rw [hMb]; simp (disch := omega) only [imgM_store_miss]
  have hra : ldv .ld Mb (sp - 112 + 56) = R 1 := by
    rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss]
  have hv : ∀ i, i < 6 → ldv .ld Mb (sp - 112 + 64 + 8 * i) = R (12 + i) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    (rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss, Nat.mul_zero, Nat.add_zero])
  refine format_spec hlive (sp := sp - 112) (k := sp - 112 + 16) (ap := sp - 112 + 64)
    (dst := .stream f fd) (hfr.sub (m := 112) (n := 192) (by omega)) ?hs ?hoff hok hro ?hargs hsh
    _ ?hsp ?h10 ?h11 ?h12 (by gnorm) fun R' M' hkp h10' hs' hfr' => ?_
  case hs =>
    have hown : ∀ i, i < 32 → S (sp - 112 + 16 + i) := fun i hi => hfr.own _ (by omega) (by omega)
    have hal' : (sp - 112 + 16) % 8 = 0 := by omega
    have hlo' : tohostAddr + 16 ≤ sp - 112 + 16 := by rw [htx]; omega
    have hhi' : sp - 112 + 16 + 32 ≤ 0x88000000 := by omega
    have hfd' : FdAt S Mb f fd := hfd.transport fun j hj => hag _ (by omega)
    exact {
      own := hown
      al := hal'
      lo := hlo'
      hi := hhi'
      fw := by
        rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss, SinkDst.fw]
        rw [← h10]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (R 10).isLt]
      len := by
        rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss, List.length_nil]
      short := by simp
      dstAt := .stream hfd' hne (by omega) }
  case hoff =>
    intro a ha
    rcases ha with ha | ha <;> omega
  case hargs =>
    have hw : ArgWords S Mb (sp - 112 + 64) args := fun i hi => by
      have hi6 : i < 6 := by omega
      exact ⟨fun j hj => hfr.own _ (by omega) (by omega), by rw [htx]; omega, by omega,
        (hv i hi6).trans (hargs i hi).symm⟩
    refine argsAt_of ps _ args hw hstr fun j h1 h2 => ?_
    exact ⟨by omega, fun hb => by have := hb.1; have := hb.2; omega⟩
  case hsp => gnorm; exact e0
  case h10 => gnorm; exact e 16 (by omega)
  case h11 => gnorm; exact h11
  case h12 => gnorm; exact e 64 (by omega)
  gnorm
  have hsp' : (R' 2).toNat = sp - 112 := by rw [hkp.get 2]; gnorm; exact e0
  have hra' : ldv .ld M' (sp - 112 + 56) = R 1 := by
    rw [ldv_ld_congr (Mt' := M') (Mt := Mb) fun j hj =>
        hfr' _ (.inr (by omega)) fun hb => by have := hb.2; omega]
    exact hra
  have e56 : (R' 2 + 56#64).toNat = sp - 112 + 56 := by rw [BitVec.toNat_add, hsp']; gnorm; omega
  dx_run hlive
  all_goals (try dc_frame hfr)
  all_goals simp only [e56, hra']
  · gnorm; exact hal
  refine hk _ M' ?_ (by gnorm; exact h10') fun a ha => ?_
  · refine Keeps.restore (by rw [hkp.get 2]; gnorm; exact add_lits_cancel _ _ _ (by decide)) ?_
    refine Keeps.restore rfl ?_
    exact (hkp.mono (by decide)).trans (by keeps_tac (Keeps.refl _ _))
  · rw [hfr' a (by omega) fun hb => by have := hb.1; have := hb.2; omega]
    exact hag a (by omega)

/-! ## `snprintf` (`0x800007c8`) -/

/-- The registers `snprintf` may change: `emit_unsigned`'s and `t1`. -/
abbrev snprintfClob : List Nat := [5, 6, 10, 11, 12, 13, 14, 15, 16, 17]

/-- `snprintf`'s epilogue at `0x80000830`: `ra`, `s0`, `s1` and `sp`
restored from the 128-byte frame at `sp - 128`. -/
theorem snprintf_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp : Nat} (hfr : StackFrame S sp 320) {ks : List Nat}
    (R0 R : Nat → BitVec 64) (h2 : (R 2).toNat = sp - 128) (h2' : R 2 + 128#64 = R0 2)
    (hra : ldv .ld M (sp - 128 + 72) = R0 1) (hs0 : ldv .ld M (sp - 128 + 64) = R0 8)
    (hs1 : ldv .ld M (sp - 128 + 56) = R0 9) (hal : (R0 1).toNat % 4 = 0)
    (hkeep : Keeps (1 :: 8 :: 9 :: 2 :: ks) R R0)
    (hk : ∀ R', Keeps ks R' R0 → R' 10 = R 10 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x80000830#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e : ∀ o, o < 128 → (R 2 + BitVec.ofNat 64 o).toNat = sp - 128 + o := fun o ho => by
    rw [BitVec.toNat_add, h2]; simp only [BitVec.toNat_ofNat]; omega
  dx_run hlive
  all_goals (try dc_frame hfr)
  all_goals simp only [e 72 (by omega), e 64 (by omega), e 56 (by omega), hra, hs0, hs1]
  · gnorm; exact hal
  refine hk _ ?_ (by gnorm)
  refine Keeps.restore (by gnorm; exact h2') ?_
  refine Keeps.restore rfl ?_
  refine Keeps.restore rfl ?_
  refine Keeps.restore rfl ?_
  exact hkeep

/-- `snprintf`'s NUL store at `0x80000828` (`buf[m] = 0`, `m < n`), then the
epilogue. -/
theorem snprintf_nul {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp buf n m : Nat} (hfr : StackFrame S sp 320)
    (hb : OwnedBytes S buf n) (hboff : buf + n ≤ sp - 320 ∨ sp ≤ buf) (hm : m < n)
    {ks : List Nat} (R0 R : Nat → BitVec 64) (h2 : (R 2).toNat = sp - 128)
    (h2' : R 2 + 128#64 = R0 2)
    (hra : ldv .ld M (sp - 128 + 72) = R0 1) (hs0 : ldv .ld M (sp - 128 + 64) = R0 8)
    (hs1 : ldv .ld M (sp - 128 + 56) = R0 9) (hal : (R0 1).toNat % 4 = 0)
    (hkeep : Keeps (1 :: 8 :: 9 :: 2 :: ks) R R0) (h9 : (R 9).toNat = buf)
    (h15 : R 15 = BitVec.ofNat 64 m)
    (hk : ∀ R' M', Keeps ks R' R0 → R' 10 = R 10 → imgM M' (buf + m) = 0#8 →
      (∀ a, a ≠ buf + m → imgM M' a = imgM M a) → DW live S Q (R0 1) R' M') :
    DW live S Q 0x80000828#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hblo := hb.lo
  have hbhi := hb.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  have ea : (R 9 + R 15).toNat = buf + m := by
    rw [BitVec.toNat_add, h9, h15, BitVec.toNat_ofNat]; omega
  dx_run hlive at 0x80000830
  all_goals (try (first
    | exact hb.own' (by omega) (by omega)
    | (gnorm; rw [ea]; intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx;
       exact hb.own' (by omega) (by omega))))
  gnorm
  rw [ea]
  have hfr1 : ∀ a, a ≠ buf + m → imgM (writeLog M [(buf + m, 1, 0#64)]) a = imgM M a :=
    fun a ha => imgM_store_miss _ _ (by omega)
  have t : ∀ o, o < 128 → o + 8 ≤ 128 → ldv .ld (writeLog M [(buf + m, 1, 0#64)]) (sp - 128 + o) =
      ldv .ld M (sp - 128 + o) := fun o h1 h2 => ldv_ld_miss _ _ (by omega)
  refine snprintf_epi hlive hfr R0 _ (by gnorm; exact h2) (by gnorm; exact h2')
    ((t 72 (by omega) (by omega)).trans hra) ((t 64 (by omega) (by omega)).trans hs0)
    ((t 56 (by omega) (by omega)).trans hs1) hal (Keeps.upd _ (by simp) hkeep)
    fun R' hk' h10' => hk R' _ hk' (by rw [h10']; gnorm) ?_ hfr1
  rw [imgM_sb]; rfl

/-- `snprintf` after `format` returns (`0x8000081c`): the count `L` at
`sp - 128 + 40`, `s0 = n`, `s1 = buf`; for `n > 0` the NUL at
`buf[min L (n - 1)]`. -/
theorem snprintf_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp buf n L : Nat} (hfr : StackFrame S sp 320)
    (hb : OwnedBytes S buf n) (hboff : buf + n ≤ sp - 320 ∨ sp ≤ buf) (hbn : n < 2 ^ 62)
    (hL : L < 2 ^ 62)
    {ks : List Nat} (R0 R : Nat → BitVec 64) (h2 : (R 2).toNat = sp - 128)
    (h2' : R 2 + 128#64 = R0 2)
    (hra : ldv .ld M (sp - 128 + 72) = R0 1) (hs0 : ldv .ld M (sp - 128 + 64) = R0 8)
    (hs1 : ldv .ld M (sp - 128 + 56) = R0 9) (hal : (R0 1).toNat % 4 = 0)
    (hlen : ldv .ld M (sp - 128 + 40) = BitVec.ofNat 64 L)
    (hkeep : Keeps (1 :: 8 :: 9 :: 2 :: ks) R R0) (h15in : 15 ∈ ks)
    (h8 : (R 8).toNat = n) (h9 : (R 9).toNat = buf)
    (hk : ∀ R' M', Keeps ks R' R0 → R' 10 = R 10 → (0 < n → imgM M' (buf + min L (n - 1)) = 0#8) →
      (∀ a, (0 < n → a ≠ buf + min L (n - 1)) → imgM M' a = imgM M a) →
      DW live S Q (R0 1) R' M') :
    DW live S Q 0x8000081c#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e40 : (R 2 + 40#64).toNat = sp - 128 + 40 := by
    rw [BitVec.toNat_add, h2]; simp only [BitVec.toNat_ofNat]; omega
  have hk15 : Keeps (1 :: 8 :: 9 :: 2 :: ks) (upd R 15 (BitVec.ofNat 64 L)) R0 :=
    Keeps.upd _ (by simp [h15in]) hkeep
  dx_run hlive at 0x80000828 0x80000830
  all_goals (try dc_frame hfr)
  all_goals simp only [e40, hlen]
  · intro hz
    gnorm_at hz
    have hn0 : n = 0 := by rw [← h8, hz]; rfl
    exact snprintf_epi hlive hfr R0 _ (by gnorm; exact h2) (by gnorm; exact h2') hra hs0 hs1 hal hk15
      fun R' hk' h10' => hk R' M hk' (by rw [h10']; gnorm) (fun h => absurd h (by omega))
        fun _ _ => rfl
  intro hnz
  have hn0 : n ≠ 0 := fun e => hnz (by gnorm; apply BitVec.eq_of_toNat_eq; rw [h8, e]; rfl)
  dx_run hlive at 0x80000828
  · intro hge
    gnorm_at hge
    rw [h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hge
    have hmin : min L (n - 1) = n - 1 := by omega
    dx_run hlive at 0x80000828
    refine snprintf_nul hlive hfr hb hboff (m := n - 1) (by omega) R0 _ (by gnorm; exact h2)
      (by gnorm; exact h2') hra hs0 hs1 hal (Keeps.upd _ (by simp [h15in]) hk15)
      (by gnorm; exact h9) ?_ fun R' M' hk' h10' hnul hfr' => hk R' M' hk' (by rw [h10']; gnorm)
        (fun _ => by rw [hmin]; exact hnul) fun a ha => hfr' a (by rw [← hmin]; exact ha (by omega))
    gnorm; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, h8, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  · intro hlt
    gnorm_at hlt
    rw [h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt
    have hmin : min L (n - 1) = L := by omega
    refine snprintf_nul hlive hfr hb hboff (m := L) (by omega) R0 _ (by gnorm; exact h2)
      (by gnorm; exact h2') hra hs0 hs1 hal hk15 (by gnorm; exact h9) (by gnorm)
      fun R' M' hk' h10' hnul hfr' => hk R' M' hk' (by rw [h10']; gnorm)
        (fun _ => by rw [hmin]; exact hnul) fun a ha => hfr' a (by rw [← hmin]; exact ha (by omega))

/-- **`snprintf(buf, n, fmt, …)`** at `0x800007c8` into the owned buffer of
`n` bytes at `buf`, with at most five variable arguments, the words in
`a3`–`a7`: returns the length `L` of `fmt ps args` as an `int`; the buffer's
first `min L (n - 1)` bytes are the output and the next is NUL (for
`n > 0`); only the buffer and the 320 bytes below `sp` change. -/
theorem snprintf_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp buf n p : Nat} {ps : List Piece} {args : List FArg}
    (hfr : StackFrame S sp 320) (hb : OwnedBytes S buf n) (hbn : n < 2 ^ 62)
    (hboff : buf + n ≤ sp - 320 ∨ sp ≤ buf) (hok : ∀ pc ∈ ps, pc.ok)
    (hro : RoBytes p (fmtBytes ps ++ [0#8])) (hstr : ArgStrs ps args)
    (hsh : (fmt ps args).length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hn : args.length ≤ 5)
    (hargs : ∀ i (h : i < args.length), args[i].w = R (13 + i))
    (hsp : (R 2).toNat = sp) (h10 : (R 10).toNat = buf) (h11 : (R 11).toNat = n)
    (h12 : (R 12).toNat = p) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps snprintfClob R' R →
      R' 10 = sx32 (BitVec.ofNat 64 (fmt ps args).length) →
      (∀ j (h : j < (fmt ps args).length), j + 1 < n → imgM M' (buf + j) = (fmt ps args)[j]) →
      (0 < n → imgM M' (buf + min (fmt ps args).length (n - 1)) = 0#8) →
      (∀ a, (a < sp - 320 ∨ sp ≤ a) → ¬ (buf ≤ a ∧ a < buf + n) → imgM M' a = imgM M a) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x800007c8#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have hblo := hb.lo
  have hbhi := hb.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive at 0x80000168
  all_goals (try dc_frame hfr)
  have e0 : (R 2 + 18446744073709551488#64).toNat = sp - 128 := by
    rw [BitVec.toNat_add, hsp]; simp only [BitVec.toNat_ofNat]; omega
  have e : ∀ o, o < 128 → (R 2 + 18446744073709551488#64 + BitVec.ofNat 64 o).toNat =
      sp - 128 + o :=
    fun o ho => by rw [BitVec.toNat_add, e0]; simp only [BitVec.toNat_ofNat]; omega
  simp only [e 64 (by omega), e 56 (by omega), e 16 (by omega), e 72 (by omega), e 88 (by omega),
    e 96 (by omega), e 104 (by omega), e 112 (by omega), e 120 (by omega), e 24 (by omega),
    e 32 (by omega), e 40 (by omega), e 8 (by omega)]
  refine DW.memEq fun Mb hMb => ?_
  have hag : ∀ a, (a < sp - 128 ∨ sp ≤ a) → imgM Mb a = imgM M a := fun a ha => by
    rw [hMb]; simp (disch := omega) only [imgM_store_miss]
  have hra : ldv .ld Mb (sp - 128 + 72) = R 1 := by
    rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss]
  have hs0 : ldv .ld Mb (sp - 128 + 64) = R 8 := by
    rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss]
  have hs1 : ldv .ld Mb (sp - 128 + 56) = R 9 := by
    rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss]
  have hv : ∀ i, i < 5 → ldv .ld Mb (sp - 128 + 88 + 8 * i) = R (13 + i) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with
      rfl | rfl | rfl | rfl | rfl <;>
    (rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss, Nat.mul_zero, Nat.add_zero])
  have ofn : ∀ x : BitVec 64, BitVec.ofNat 64 x.toNat = x := fun x => by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]
  refine format_spec hlive (sp := sp - 128) (k := sp - 128 + 16) (ap := sp - 128 + 88)
    (dst := .buffer buf n) (hfr.sub (m := 128) (n := 192) (by omega)) ?hs ?hoff hok hro ?hargs hsh
    _ ?hsp ?h10 ?h11 ?h12 (by gnorm) fun R' M' hkp h10' hs' hfr' => ?_
  case hs =>
    have hown : ∀ i, i < 32 → S (sp - 128 + 16 + i) := fun i hi => hfr.own _ (by omega) (by omega)
    have hal' : (sp - 128 + 16) % 8 = 0 := by omega
    have hlo' : tohostAddr + 16 ≤ sp - 128 + 16 := by rw [htx]; omega
    have hhi' : sp - 128 + 16 + 32 ≤ 0x88000000 := by omega
    have h8 : ldv .ld Mb (sp - 128 + 16 + 8) = BitVec.ofNat 64 buf := by
      rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss]; rw [← h10, ofn]
    have h16 : ldv .ld Mb (sp - 128 + 16 + 16) = BitVec.ofNat 64 n := by
      rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss]; rw [← h11, ofn]
    exact {
      own := hown
      al := hal'
      lo := hlo'
      hi := hhi'
      fw := by rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss, SinkDst.fw]
      len := by
        rw [hMb]; simp (disch := omega) only [ldv_ld_hit_eq, ldv_ld_miss, List.length_nil]
      short := by simp
      dstAt := .buffer hb (by omega) hbn h8 h16 fun j hj => absurd hj (by simp) }
  case hoff =>
    intro a ha
    rcases ha with ha | ha <;> omega
  case hargs =>
    have hw : ArgWords S Mb (sp - 128 + 88) args := fun i hi => by
      have hi5 : i < 5 := by omega
      exact ⟨fun j hj => hfr.own _ (by omega) (by omega), by rw [htx]; omega, by omega,
        (hv i hi5).trans (hargs i hi).symm⟩
    refine argsAt_of ps _ args hw hstr fun j h1 h2 => ?_
    refine ⟨by omega, fun hb' => ?_⟩
    rcases hb' with hb' | hb' <;> omega
  case hsp => gnorm; exact e0
  case h10 => gnorm; exact e 16 (by omega)
  case h11 => gnorm; exact h12
  case h12 => gnorm; exact e 88 (by omega)
  gnorm
  have hsp' : (R' 2).toNat = sp - 128 := by rw [hkp.get 2]; gnorm; exact e0
  have hkeep : ∀ a, sp - 128 ≤ a → a < sp → ¬ (sp - 128 + 16 + 24 ≤ a ∧ a < sp - 128 + 16 + 32) →
      imgM M' a = imgM Mb a := fun a h1 h2 h3 =>
    hfr' a (.inr h1) fun hb' => by rcases hb' with hb' | hb' <;> omega
  have hra' : ldv .ld M' (sp - 128 + 72) = R 1 :=
    (ldv_ld_congr fun j hj => hkeep _ (by omega) (by omega) (by omega)).trans hra
  have hs0' : ldv .ld M' (sp - 128 + 64) = R 8 :=
    (ldv_ld_congr fun j hj => hkeep _ (by omega) (by omega) (by omega)).trans hs0
  have hs1' : ldv .ld M' (sp - 128 + 56) = R 9 :=
    (ldv_ld_congr fun j hj => hkeep _ (by omega) (by omega) (by omega)).trans hs1
  have hlen : ldv .ld M' (sp - 128 + 40) = BitVec.ofNat 64 (fmt ps args).length := hs'.len
  have e' : ∀ o, o < 128 → (R' 2 + BitVec.ofNat 64 o).toNat = sp - 128 + o := fun o ho => by
    rw [BitVec.toNat_add, hsp']; simp only [BitVec.toNat_ofNat]; omega
  have h8' : R' 8 = R 11 := by rw [hkp.get 8]; gnorm
  have h9' : R' 9 = R 10 := by rw [hkp.get 9]; gnorm
  have hL := hs'.short
  have hbufc : ∀ j (h : j < (fmt ps args).length), j + 1 < n →
      imgM M' (buf + j) = (fmt ps args)[j] := by
    cases hd : hs'.dstAt with
    | buffer _ _ _ _ _ hc => exact hc
  have hlen' : ldv .ld M' (sp - 128 + 40) = BitVec.ofNat 64 (fmt ps args).length := by
    have := hs'.len; rwa [show sp - 128 + 16 + 24 = sp - 128 + 40 by omega] at this
  refine snprintf_ret hlive hfr hb hboff hbn hL (ks := snprintfClob) R R' hsp'
    (by rw [hkp.get 2]; gnorm; exact add_lits_cancel _ _ _ (by decide)) hra' hs0' hs1' hal hlen'
    ((hkp.mono (by decide)).trans (by keeps_tac (Keeps.refl _ _))) (by decide)
    (by rw [h8']; exact h11) (by rw [h9']; exact h10)
    fun R2 M2 hk2 h10'' hnul hfr2 => hk R2 M2 hk2 (by rw [h10'', h10']) ?_ hnul ?_
  · intro j hj hjn
    rw [hfr2 _ fun _ => by omega]
    exact hbufc j hj hjn
  · intro a ha hab
    rw [hfr2 a fun _ e => hab ⟨by omega, by omega⟩]
    rw [hfr' a (by omega) fun hb' => by rcases hb' with hb' | hb' <;> omega]
    exact hag a (by omega)

end Dc.Mach
