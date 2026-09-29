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

/-! ## The digit loop (`0x80000084`)

```
80000084 mv a1,s3 ; 80000088 mv a0,s0 ; 8000008c jal __umoddi3
80000090 add a0,s6,a0 ; 80000094 lbu a5,0(a0) ; 80000098 mv a1,s3 ; 8000009c mv a0,s0
800000a0 sb a5,0(s2) ; 800000a4 jal __hidden___udivdi3 ; 800000a8 mv s5,s0 ; 800000ac mv a5,s2
800000b0 mv s0,a0 ; 800000b4 addi s2,s2,1 ; 800000b8 bgeu s5,s3,80000084
```
-/

/-- `subw` of two words `n` apart, `n < 2^31`. -/
theorem subw_eq {x y : BitVec 64} {n : Nat} (h : x.toNat = y.toNat + n) (hn : n < 2 ^ 31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0 - Sail.BitVec.extractLsb y 31 0) =
      BitVec.ofNat 64 n := by
  have hz : (Sail.BitVec.extractLsb x 31 0 - Sail.BitVec.extractLsb y 31 0 : BitVec 32) =
      BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_ofNat]
    have := x.isLt
    omega
  rw [hz]
  simp only [sign_extend, Sail.BitVec.signExtend]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by simp [BitVec.msb_eq_decide]; omega)]
  simp; omega

/-- `udivV` by a nonzero divisor. -/
theorem udivV_toNat {x y : BitVec 64} (hy : y.toNat ≠ 0) : (udivV x y).toNat = x.toNat / y.toNat := by
  have : y ≠ 0#64 := fun e => hy (by rw [e]; rfl)
  rw [udivV, ite_eq_right_of_eq_false _ _ (eq_false this), BitVec.toNat_udiv]

/-- `"0123456789abcdef"` at `0x800079c8` in `.rodata`. -/
theorem digit_ro : ∀ i, i < 16 →
    dcROImg (0x800079c8 + i) = digitChar i ∧ (0x800079c8 + i, dcROImg (0x800079c8 + i)) ∈ dcRO := by
  decide

theorem ldvf_lbu (f : Nat → BitVec 8) (a : Nat) : ldvf .lbu f a = zero_extend (m := 64) (f a) := by
  simp [ldvf, bytesAt, bytesVal, widthOfM]

/-- At most `m` digits below `b ^ m`. -/
theorem ndig_le {b : Nat} (hb : 2 ≤ b) : ∀ m v, 1 ≤ m → v < b ^ m → ndig b v ≤ m := by
  intro m
  induction m with
  | zero => intro v h; omega
  | succ m ih =>
    intro v _ hv
    by_cases h : b ≤ v
    · rw [ndig_of_ge hb h]
      have : v / b < b ^ m := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; rwa [← Nat.pow_succ]
      have h1 : 1 ≤ m := by
        refine Classical.byContradiction fun h0 => ?_
        have : m = 0 := by omega
        subst this; simp at hv; omega
      have := ih (v / b) h1 this; omega
    · rw [ndig_of_lt (by omega)]; omega

/-- At most 22 octal or decimal digits of a 64-bit value. -/
theorem ndig_le22 {b v : Nat} (hb : 8 ≤ b) (hv : v < 2 ^ 64) : ndig b v ≤ 22 := by
  refine ndig_le (by omega) 22 v (by omega) (Nat.lt_of_lt_of_le hv ?_)
  calc 2 ^ 64 ≤ 8 ^ 22 := by decide
    _ ≤ b ^ 22 := Nat.pow_le_pow_left hb 22

/-- The digit loop at `0x80000084`, iteration `n`: `s0 = v / b ^ n`, `s2`
at the digit `n` (at `sp - 88 + n`), the digits `0 … n-1` stored. -/
theorem eu_digits {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k b v : Nat} {dst : SinkDst} {out : List (BitVec 8)}
    {Me : Mem} (hfr : StackFrame S sp 96) (hoff : ∀ a, dst.Read k a → a < sp - 96 ∨ sp ≤ a)
    (hb : 8 ≤ b ∧ b ≤ 10) (hv : v < 2 ^ 64) (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hsh : out.length + ndig b v < 2 ^ 62)
    (hk : ∀ R' M', Keeps euClob R' R0 → SinkAt S M' k dst (out ++ udigits b v) →
      (∀ a, (a < sp - 96 ∨ sp ≤ a) → ¬ dst.Byte k a → imgM M' a = imgM Me a) →
      DW live S Q (R0 1) R' M') :
    ∀ m n (R : Nat → BitVec 64) (M : Mem), ndig b v - n = m → n < ndig b v →
      (R 8).toNat = v / b ^ n →
      (R 18).toNat = sp - 88 + n → (R 9).toNat = sp - 88 → (R 19).toNat = b → (R 20).toNat = k →
      R 22 = 0x800079c8#64 → (R 2).toNat = sp - 96 → R 2 + 96#64 = R0 2 →
      Keeps [1, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] R R0 →
      EUSaved M (sp - 96) R0 → (∀ j, j < n → imgM M (sp - 88 + j) = dg b v j) →
      SinkAt S M k dst out → (∀ a, (a < sp - 96 ∨ sp ≤ a) → imgM M a = imgM Me a) →
      DW live S Q 0x80000084#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hN := ndig_le22 hb.1 hv
  intro m
  induction m with
  | zero => intro n R M hm hn; omega
  | succ m ih =>
  intro n R M hm hn h8 h18 h9 h19 h20 h22 h2 h2' hkeep hsv hdig hs hfrm
  have hklo := hs.lo
  have hkhi := hs.hi
  have hkal := hs.al
  obtain ⟨vn, hvn⟩ : ∃ vn, vn = v / b ^ n := ⟨_, rfl⟩
  rw [← hvn] at h8
  have hvn64 : vn < 2 ^ 64 := by rw [hvn]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
  dx_run hlive at 0x80007958
  refine umoddi3_spec hlive _ (by gnorm <;> decide) fun R1 hk1 hr1 => ?_
  gnorm
  have hd : vn % b < 10 := by have := Nat.mod_lt vn (show b > 0 by omega); omega
  have e10 : (R1 10).toNat = vn % b := by
    rw [hr1]; gnorm; rw [BitVec.toNat_umod, h8, h19]
  have e22 : R1 22 = 0x800079c8#64 := by rw [hk1.get 22]; gnorm; exact h22
  dx_run hlive at 0x80000094
  refine stR_80000094 hlive ?_ ?_ ?_
  · gnorm; rw [e22, BitVec.toNat_add, e10]; simp only [LdOK]; gnorm; omega
  · gnorm; rw [e22, BitVec.toNat_add, e10]; gnorm
    rw [show (2147514824 + vn % b) % 18446744073709551616 = 0x800079c8 + vn % b by omega]
    intro x hx; rw [accAddrs_one, List.mem_singleton] at hx; subst hx
    exact (digit_ro _ (by omega)).2
  have ea : (R1 22 + R1 10).toNat = 0x800079c8 + vn % b := by
    rw [e22, BitVec.toNat_add, e10]; gnorm; omega
  gnorm
  rw [ea, ldvf_lbu, (digit_ro _ (by omega)).1]
  have e18 : (R1 18).toNat = sp - 88 + n := by rw [hk1.get 18]; gnorm; exact h18
  have e8 : (R1 8).toNat = vn := by rw [hk1.get 8]; gnorm; exact h8
  have e19 : (R1 19).toNat = b := by rw [hk1.get 19]; gnorm; exact h19
  dx_run hlive at 0x80007910
  all_goals (try dc_frame hfr)
  refine udivdi3_spec hlive _ (by gnorm <;> decide) fun R2 hk2 hq _ => ?_
  gnorm
  gnorm_at hq
  have hb0 : b ≠ 0 := by omega
  have f10 : (R2 10).toNat = vn / b := by rw [hq, udivV_toNat (by rw [e19]; exact hb0), e8, e19]
  have f8 : (R2 8).toNat = vn := by rw [hk2.get 8]; gnorm; exact e8
  have f19 : (R2 19).toNat = b := by rw [hk2.get 19]; gnorm; exact e19
  have f18 : (R2 18).toNat = sp - 88 + n := by rw [hk2.get 18]; gnorm; exact e18
  have f9 : (R2 9).toNat = sp - 88 := by rw [hk2.get 9]; gnorm; rw [hk1.get 9]; gnorm; exact h9
  have f20 : (R2 20).toNat = k := by rw [hk2.get 20]; gnorm; rw [hk1.get 20]; gnorm; exact h20
  have f22 : R2 22 = 0x800079c8#64 := by rw [hk2.get 22]; gnorm; exact e22
  have f2 : R2 2 = R 2 := by rw [hk2.get 2]; gnorm; rw [hk1.get 2]; gnorm
  have fkeep : Keeps [1, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] R2 R0 :=
    (hk2.mono (by decide)).trans (by
      keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac hkeep)))
  rw [e18]
  -- the memory after the digit store
  have hn24 : n < 22 := by omega
  have hin : ∀ a, (a < sp - 96 ∨ sp ≤ a) → imgM (writeLog M [(sp - 88 + n, 1,
      zero_extend (m := 64) (digitChar (vn % b)))]) a = imgM M a :=
    fun a ha => imgM_store_miss _ _ (by omega)
  have hsv1 := hsv.transport (M' := writeLog M [(sp - 88 + n, 1,
      zero_extend (m := 64) (digitChar (vn % b)))]) fun a h1 h2 => imgM_store_miss _ _ (by omega)
  have hs1 := hs.transport (Mt' := writeLog M [(sp - 88 + n, 1,
      zero_extend (m := 64) (digitChar (vn % b)))]) fun a ha => hin a (hoff a ha)
  have hdig1 : ∀ j, j < n + 1 → imgM (writeLog M [(sp - 88 + n, 1,
      zero_extend (m := 64) (digitChar (vn % b)))]) (sp - 88 + j) = dg b v j := by
    intro j hj
    by_cases e : j = n
    · subst e; rw [imgM_sb, sbData_zext, dg, ← hvn]
    · rw [imgM_store_miss _ _ (by omega)]; exact hdig j (by omega)
  have hfrm1 : ∀ a, (a < sp - 96 ∨ sp ≤ a) → imgM (writeLog M [(sp - 88 + n, 1,
      zero_extend (m := 64) (digitChar (vn % b)))]) a = imgM Me a :=
    fun a ha => (hin a ha).trans (hfrm a ha)
  by_cases hlast : n + 1 < ndig b v
  · have hge : b ≤ vn := hvn ▸ ndig_ge (by omega) v n hlast
    dx_run hlive at 0x80000084
    refine ih (n + 1) _ _ ?_ hlast ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by keeps_tac fkeep) hsv1 hdig1
      hs1 hfrm1
    · omega
    · gnorm; rw [f10, hvn, div_pow_succ]
    · gnorm; rw [BitVec.toNat_add, f18]; gnorm; try omega
    · gnorm; exact f9
    · gnorm; exact f19
    · gnorm; exact f20
    · gnorm; exact f22
    · gnorm; rw [f2]; exact h2
    · gnorm; rw [f2]; exact h2'
  · have hN1 : ndig b v = n + 1 := by omega
    have hlt : vn < b := by
      have := ndig_lt (b := b) (by omega) v; rw [hN1, Nat.add_sub_cancel] at this; rw [hvn]; exact this
    dx_run hlive at 0x800000bc
    apply st_800000bc hlive
    rw [subw_eq (n := n) (by gnorm; rw [f18, f9]; try omega) (by omega)]
    dx_run hlive at 0x800000e8
    all_goals (try own_by hs1)
    have hsh32 : BitVec.ofNat 64 n <<< 32 >>> 32 = BitVec.ofNat 64 n := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      omega
    have hN24 : ndig b v ≤ 24 := by omega
    refine eu_emit (M0 := writeLog M [(sp - 88 + n, 1, zero_extend (m := 64) (digitChar (vn % b)))])
      hlive hfr hoff R0 hal hN24 (dg b v) hsh (fun R' M' hk' hE => ?_) n _ _ (by omega)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by keeps_tac fkeep) hsv1 (by rw [hN1]; exact hdig1) ?_
    · refine hk R' M' hk' ?_ fun a ha hb => (hE.frame a hb).trans (hfrm1 a ha)
      rw [udigits, ← emitted_zero]; exact hE.sink
    · gnorm; rw [BitVec.toNat_add, f9, BitVec.toNat_ofNat]; omega
    · gnorm; rw [hsh32, BitVec.add_sub_cancel, BitVec.toNat_add, f9]; gnorm; omega
    · gnorm
      rw [show (R2 20 + 24#64).toNat = k + 24 by rw [BitVec.toNat_add, f20]; gnorm; omega, hs1.len,
        ofNat_toNat_lt (by omega)]
      omega
    · gnorm
    · gnorm; exact f20
    · gnorm; rw [f2]; exact h2
    · gnorm; rw [f2]; exact h2'
    · rw [hN1, emitted_all, List.append_nil]; exact Emitted.refl hs1

/-! ## The entry (`0x80000040`)

```
80000040 addi sp,sp,-96 ; 80000044 sd s1,72(sp) ; 80000048 sd s3,56(sp)
8000004c addi s1,sp,8 ; 80000050 slli s3,a2,0x20 ; 80000054 sd s0,80(sp)
80000058 sd s2,64(sp) ; 8000005c sd s4,48(sp) ; 80000060 sd s6,32(sp)
80000064 sd ra,88(sp) ; 80000068 sd s5,40(sp) ; 8000006c srli s3,s3,0x20
80000070 mv s0,a1 ; 80000074 mv s4,a0 ; 80000078 mv s2,s1
8000007c auipc s6,0x8 ; 80000080 addi s6,s6,-1716
```
-/

/-- **`emit_unsigned(k, v, b)`** at `0x80000040`, `b ∈ [8, 10]`, with a
96-byte frame below `sp` apart from the sink: the sink receives
`udigits b v`; only the frame and the sink's count word and buffer change;
clobbers `t0`, `a0`–`a7`. -/
theorem emit_unsigned_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp k b : Nat} {dst : SinkDst} {out : List (BitVec 8)}
    (hfr : StackFrame S sp 96) (hs : SinkAt S M k dst out)
    (hoff : ∀ a, dst.Read k a → a < sp - 96 ∨ sp ≤ a) (hb : 8 ≤ b ∧ b ≤ 10)
    (R : Nat → BitVec 64) (hsp : (R 2).toNat = sp) (h10 : (R 10).toNat = k)
    (h12 : R 12 = BitVec.ofNat 64 b) (hsh : out.length + ndig b (R 11).toNat < 2 ^ 62)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps euClob R' R → SinkAt S M' k dst (out ++ udigits b (R 11).toNat) →
      (∀ a, (a < sp - 96 ∨ sp ≤ a) → ¬ dst.Byte k a → imgM M' a = imgM M a) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80000040#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive at 0x80000084
  all_goals (try dc_frame hfr)
  refine eu_digits hlive hfr hoff hb (R 11).isLt R hal hsh hk (ndig b (R 11).toNat - 0) 0 _ _ rfl
    (ndig_pos _ _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by keeps_tac (Keeps.refl _ _)) ?_ (fun j hj => absurd hj (by omega))
    (hs.transport fun a ha => ?_) ?_
  · gnorm; simp
  · gnorm; rw [BitVec.toNat_add, BitVec.toNat_add, hsp]; gnorm; omega
  · gnorm; rw [BitVec.toNat_add, BitVec.toNat_add, hsp]; gnorm; omega
  · gnorm; rw [h12]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega
  · gnorm; exact h10
  · gnorm
  · gnorm; rw [BitVec.toNat_add, hsp]; gnorm; omega
  · gnorm; exact add_lits_cancel _ _ _ (by decide)
  · constructor <;> (simp (disch := sx_addr) only [ldv_ld_hit_eq, ldv_ld_miss]; gnorm)
  · have := hoff a ha
    simp (disch := sx_addr) only [imgM_store_miss]
  · intro a ha
    simp (disch := sx_addr) only [imgM_store_miss]

end Dc.Mach
