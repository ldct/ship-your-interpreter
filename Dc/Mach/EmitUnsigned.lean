import Dc.Mach.EmitSites

/-!
# `emit_unsigned` (`0x80000040`)

```c
static void emit_unsigned(struct sink *k, unsigned long v, unsigned base)
{
	char d[24]; int n = 0;
	do { d[n++] = "0123456789abcdef"[v % base]; v /= base; } while (v);
	while (n) emit(k, d[--n]);
}
```

The digit loop (`0x80000084`, `eu_digits`) stores the `ndig b v` digits
`dg b v j` at `sp + 8 + j` of the 96-byte frame, calling `__umoddi3` and
`__hidden___udivdi3`; the emit loop (`0x800000e8`, `eu_emit`) emits them
from the last to the first through the inlined `emit` (`emit_800000f4`).
`emit_unsigned_spec`: the sink receives `udigits b v`; only the frame and
the sink's count word and buffer change.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The registers `emit_unsigned` may change. -/
abbrev euClob : List Nat := [5, 10, 11, 12, 13, 14, 15, 16, 17]

/-- The saved registers in `emit_unsigned`'s frame at `fr` (the callee's
`sp`). -/
structure EUSaved (M : Mem) (fr : Nat) (R0 : Nat → BitVec 64) : Prop where
  ra : ldv .ld M (fr + 88) = R0 1
  s0 : ldv .ld M (fr + 80) = R0 8
  s1 : ldv .ld M (fr + 72) = R0 9
  s2 : ldv .ld M (fr + 64) = R0 18
  s3 : ldv .ld M (fr + 56) = R0 19
  s4 : ldv .ld M (fr + 48) = R0 20
  s5 : ldv .ld M (fr + 40) = R0 21
  s6 : ldv .ld M (fr + 32) = R0 22

theorem EUSaved.transport {M M' : Mem} {fr : Nat} {R0 : Nat → BitVec 64} (h : EUSaved M fr R0)
    (hag : ∀ a, fr + 32 ≤ a → a < fr + 96 → imgM M' a = imgM M a) : EUSaved M' fr R0 := by
  have t : ∀ o, 32 ≤ o → o + 8 ≤ 96 → ldv .ld M' (fr + o) = ldv .ld M (fr + o) := fun o h1 h2 =>
    ldv_ld_congr fun j hj => hag _ (by omega) (by omega)
  exact ⟨(t 88 (by omega) (by omega)).trans h.ra, (t 80 (by omega) (by omega)).trans h.s0,
    (t 72 (by omega) (by omega)).trans h.s1, (t 64 (by omega) (by omega)).trans h.s2,
    (t 56 (by omega) (by omega)).trans h.s3, (t 48 (by omega) (by omega)).trans h.s4,
    (t 40 (by omega) (by omega)).trans h.s5, (t 32 (by omega) (by omega)).trans h.s6⟩

/-- `emit_unsigned`'s epilogue at `0x80000110`. -/
theorem eu_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp : Nat} (hfr : StackFrame S sp 96)
    (R0 R : Nat → BitVec 64) (h2 : (R 2).toNat = sp - 96) (h2' : R 2 + 96#64 = R0 2)
    (hsv : EUSaved M (sp - 96) R0)
    (hkeep : Keeps [1, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] R R0)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps euClob R' R0 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x80000110#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive
  all_goals (try dc_frame hfr)
  all_goals simp (disch := sx_addr) only [ldv_eq_at hsv.ra, ldv_eq_at hsv.s0, ldv_eq_at hsv.s1,
    ldv_eq_at hsv.s2, ldv_eq_at hsv.s3, ldv_eq_at hsv.s4, ldv_eq_at hsv.s5, ldv_eq_at hsv.s6]
  all_goals (try (dc_simp [hal]; done))
  refine hk _ ?_
  refine Keeps.restore (by dc_simp [h2']) ?_
  iterate 8 refine Keeps.restore rfl ?_
  exact hkeep.mono (by decide)

/-! ## The emit loop (`0x800000e8`)

```
800000e8 ld a3,0(s4) ; 800000ec lbu a2,0(a5) ; 800000f0 addi a1,a4,1
800000f4 … (emit_800000f4) … 80000108 addi a5,a5,-1 ; 8000010c bne a5,a0,800000e8
```
-/

/-- The digits `g (N-1), …, g j`, emitted most significant first. -/
def emitted (N : Nat) (g : Nat → BitVec 8) (j : Nat) : List (BitVec 8) :=
  (((List.range N).drop j).map g).reverse

theorem emitted_length (N : Nat) (g : Nat → BitVec 8) (j : Nat) :
    (emitted N g j).length = N - j := by
  simp [emitted]

theorem emitted_step {N j : Nat} (g : Nat → BitVec 8) (h : j < N) :
    emitted N g j = emitted N g (j + 1) ++ [g j] := by
  unfold emitted
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp [List.getElem_range]

theorem emitted_zero (N : Nat) (g : Nat → BitVec 8) :
    emitted N g 0 = ((List.range N).map g).reverse := by
  simp [emitted]

theorem emitted_all (N : Nat) (g : Nat → BitVec 8) : emitted N g N = [] := by
  simp [emitted]

theorem Emitted.refl {S : Nat → Prop} {M : Mem} {k : Nat} {dst : SinkDst}
    {out : List (BitVec 8)} (h : SinkAt S M k dst out) : Emitted S M M k dst out :=
  ⟨h, fun _ _ => rfl⟩

theorem Emitted.trans {S : Nat → Prop} {M0 M1 M2 : Mem} {k : Nat} {dst : SinkDst}
    {o1 o2 : List (BitVec 8)} (h1 : Emitted S M0 M1 k dst o1) (h2 : Emitted S M1 M2 k dst o2) :
    Emitted S M0 M2 k dst o2 :=
  ⟨h2.sink, fun a ha => (h2.frame a ha).trans (h1.frame a ha)⟩

theorem SinkDst.read_of_byte {k : Nat} {dst : SinkDst} {a : Nat} (h : dst.Byte k a) :
    dst.Read k a := by
  cases dst with
  | stream => exact .inl ⟨by have := h.1; omega, h.2⟩
  | buffer =>
    rcases h with h | h
    · exact .inl ⟨by have := h.1; omega, h.2⟩
    · exact .inr h

theorem lo8_zext (b : BitVec 8) : lo8 (zero_extend (m := 64) b) = b := by
  rw [← sbData_eq]; exact sbData_zext b

/-- The emit loop at `0x800000e8`: `a5` at the digit `j` (at `sp - 88 + j`),
`a0` one below the first digit, `a4` the count, the digits `g (N-1), …,
g (j+1)` already emitted. -/
theorem eu_emit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k : Nat} {dst : SinkDst} {out : List (BitVec 8)}
    {M0 : Mem} (hfr : StackFrame S sp 96) (hoff : ∀ a, dst.Read k a → a < sp - 96 ∨ sp ≤ a)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0) {N : Nat} (hN : N ≤ 24)
    (g : Nat → BitVec 8) (hsh : out.length + N < 2 ^ 62)
    (hk : ∀ R' M', Keeps euClob R' R0 → Emitted S M0 M' k dst (out ++ emitted N g 0) →
      DW live S Q (R0 1) R' M') :
    ∀ j (R : Nat → BitVec 64) (M : Mem), j < N → (R 15).toNat = sp - 88 + j →
      (R 10).toNat = sp - 89 → (R 14).toNat = out.length + (N - (j + 1)) → (R 16).toNat = 1 →
      (R 20).toNat = k → (R 2).toNat = sp - 96 → R 2 + 96#64 = R0 2 →
      Keeps [1, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] R R0 →
      EUSaved M (sp - 96) R0 → (∀ i, i < N → imgM M (sp - 88 + i) = g i) →
      Emitted S M0 M k dst (out ++ emitted N g (j + 1)) → DW live S Q 0x800000e8#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro R M hj h15 h10 h14 h16 h20 h2 h2' hkeep hsv hdig hE
  have hs := hE.sink
  have hkal := hs.al
  have hklo := hs.lo
  have hkhi := hs.hi
  have hfw : dst.fw < 2 ^ 64 := by
    cases dst with
    | stream f fd => have := hs.streamFd.1.hi; simp only [SinkDst.fw]; omega
    | buffer => simp only [SinkDst.fw]; omega
  dx_run hlive at 0x800000f4
  all_goals (try own_by hs)
  all_goals (try dc_frame hfr)
  refine emit_800000f4 hlive hs (g j) (by simp [emitted_length]; omega) _ ?kr ?fr ?lr ?l1 ?c ?one
    fun R' M' hk' hr14 hE' => ?_
  case kr => gnorm; exact h20
  case fr =>
    gnorm
    rw [h20, hs.fw, ofNat_toNat_lt hfw]
  case lr => gnorm; simp [emitted_length, h14]
  case l1 =>
    gnorm; rw [BitVec.toNat_add, h14]; simp [emitted_length]; omega
  case c =>
    gnorm
    rw [ldv_lbu, lo8_zext, h15]
    exact hdig j hj
  case one => gnorm; exact h16
  -- after the emit (`0x80000108`)
  have hfm : ∀ a, (sp - 96 ≤ a ∧ a < sp) → imgM M' a = imgM M a := fun a ha =>
    hE'.frame a fun hb => by have := hoff a (SinkDst.read_of_byte hb); omega
  have hsv' : EUSaved M' (sp - 96) R0 := hsv.transport fun a h1 h2 => hfm a ⟨by omega, by omega⟩
  have hdig' : ∀ i, i < N → imgM M' (sp - 88 + i) = g i := fun i hi =>
    (hfm _ ⟨by omega, by omega⟩).trans (hdig i hi)
  have hE2 : Emitted S M0 M' k dst (out ++ emitted N g j) := by
    have := hE.trans hE'
    rwa [List.append_assoc, ← emitted_step g hj] at this
  have e15 : (R' 15).toNat = sp - 88 + j := by rw [hk'.get 15]; gnorm; exact h15
  have e10 : (R' 10).toNat = sp - 89 := by rw [hk'.get 10]; gnorm; exact h10
  have e2 : R' 2 = R 2 := by rw [hk'.get 2]; gnorm
  have hkeep' : Keeps [1, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] R' R0 :=
    (hk'.mono (by decide)).trans (by keeps_tac hkeep)
  cases j with
  | zero =>
    dx_run hlive at 0x80000110
    refine eu_exit hlive hfr R0 _ (by gnorm; rw [e2]; exact h2) (by gnorm; rw [e2]; exact h2') hsv'
      (by keeps_tac hkeep') hal fun R'' hk'' => hk R'' M' hk'' hE2
  | succ j =>
    dx_run hlive at 0x800000e8
    rotate_left
    · intro hc; exfalso; simp only [ne_eq, Classical.not_not] at hc; gnorm_at hc
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_add, e15, e10] at this; gnorm_at this; omega
    intro _
    refine ih j (by omega) _ M' (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by keeps_tac hkeep') hsv' hdig' hE2
    · gnorm; rw [BitVec.toNat_add, e15]; gnorm; omega
    · gnorm; exact e10
    · gnorm; rw [hr14]; simp [emitted_length]; omega
    · gnorm; rw [hk'.get 16]; gnorm; exact h16
    · gnorm; rw [hk'.get 20]; gnorm; exact h20
    · gnorm; rw [e2]; exact h2
    · gnorm; rw [e2]; exact h2'

end Dc.Mach
