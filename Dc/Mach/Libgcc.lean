import Dc.Mach.Bytes
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.DivLoops

/-!
# libgcc arithmetic (`__muldi3`, `__udivdi3` and the wrappers)

The libgcc routines of the dc binary, over `DW` (`Run.lean`):

- `__muldi3` (`0x800078a4`): shift-and-add, `a0 = x * y` (wrapping).
- `__hidden___udivdi3` (`0x80007910`): normalize-then-subtract, `a0 = n / d`
  (`-1` for `d = 0`, `udivV`), `a1 = n % d`.
- `__umoddi3`, `__divdi3`, `__moddi3`, `__udivsi3`, `__umodsi3`, `__divsi3`:
  wrappers that call `__hidden___udivdi3` with `t0` as the link register.

The arithmetic cores reuse the WHILE proofs' identities (`Vsa.Sim.invmul_bv`,
`Vsa.Sim.or_two_pow_eq_add`); the loop invariants are the named structures
`DivNorm` and `DivInv`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## `__muldi3` (`0x800078a4`)

```
800078a4 mv a2,a0 ; 800078a8 li a0,0
800078ac andi a3,a1,1 ; 800078b0 beqz a3,800078b8 ; 800078b4 add a0,a0,a2
800078b8 srli a1,a1,0x1 ; 800078bc slli a2,a2,0x1 ; 800078c0 bnez a1,800078ac
800078c4 ret
```
-/

theorem and1_toNat (a : BitVec 64) : (a &&& 1#64).toNat = a.toNat % 2 := by
  rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 1

theorem shr1_toNat (a : BitVec 64) : (a >>> 1).toNat = a.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

/-- One shift-and-add step keeps `a0 + a2 * a1`, bit clear. -/
theorem mul_step_even (a0 a1 a2 : BitVec 64) (h : a1 &&& 1#64 = 0#64) :
    a0 + (a2 <<< 1) * (a1 >>> 1) = a0 + a2 * a1 := by
  rw [invmul_bv a2 a1, h, BitVec.zero_mul, BitVec.add_zero]

/-- One shift-and-add step keeps `a0 + a2 * a1`, bit set. -/
theorem mul_step_odd (a0 a1 a2 : BitVec 64) (h : ¬ a1 &&& 1#64 = 0#64) :
    a0 + a2 + (a2 <<< 1) * (a1 >>> 1) = a0 + a2 * a1 := by
  have h1 : a1 &&& 1#64 = 1#64 := by
    apply BitVec.eq_of_toNat_eq
    have hne : (a1 &&& 1#64).toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    rw [and1_toNat] at hne ⊢; show a1.toNat % 2 = 1; omega
  rw [invmul_bv a2 a1, h1, BitVec.one_mul, BitVec.add_assoc, BitVec.add_comm a2]

theorem muldi3_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (x y : BitVec 64)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 12, 13] R' R0 → R' 10 = x * y → DW live S Q (R0 1) R' Mt) :
    ∀ m (R : Nat → BitVec 64), (R 11).toNat = m → R 10 + R 12 * R 11 = x * y →
      Keeps [10, 11, 12, 13] R R0 → DW live S Q 0x800078ac#64 R Mt := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro R hm hinv hkeep
    dx_run hlive
    · -- bit clear
      intro hb
      dc_simp [] at hb
      dx_run hlive
      · intro hnz
        dc_simp [] at hnz
        refine ih _ ?_ _ rfl ?_ (by keeps_tac hkeep)
        · dc_simp []
          rw [shr1_toNat, ← hm]
          have : (R 11).toNat ≠ 0 := fun e => hnz (BitVec.eq_of_toNat_eq (by rw [shr1_toNat, e]; rfl))
          omega
        · dc_simp []; rw [mul_step_even _ _ _ hb, hinv]
      · intro hz
        dx_run hlive
        · dc_simp [hkeep.get 1, hal]
        · rw [hkeep.get 1]
          refine hk _ (by keeps_tac hkeep) ?_
          dc_simp []
          have hz' : R 11 >>> 1 = 0#64 := Classical.byContradiction hz
          rw [← hinv, ← mul_step_even _ _ _ hb, hz', BitVec.mul_zero, BitVec.add_zero]
    · -- bit set
      intro hb
      dc_simp [] at hb
      dx_run hlive
      · intro hnz
        dc_simp [] at hnz
        refine ih _ ?_ _ rfl ?_ (by keeps_tac hkeep)
        · dc_simp []
          rw [shr1_toNat, ← hm]
          have : (R 11).toNat ≠ 0 := fun e => hnz (BitVec.eq_of_toNat_eq (by rw [shr1_toNat, e]; rfl))
          omega
        · dc_simp []; rw [mul_step_odd _ _ _ hb, hinv]
      · intro hz
        dx_run hlive
        · dc_simp [hkeep.get 1, hal]
        · rw [hkeep.get 1]
          refine hk _ (by keeps_tac hkeep) ?_
          dc_simp []
          have hz' : R 11 >>> 1 = 0#64 := Classical.byContradiction hz
          rw [← hinv, ← mul_step_odd _ _ _ hb, hz', BitVec.mul_zero, BitVec.add_zero]

/-- **`__muldi3(x, y)`** at `0x800078a4`: `a0 = x * y` (mod `2^64`);
clobbers `a1`–`a3`. -/
theorem muldi3_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 12, 13] R' R → R' 10 = R 10 * R 11 → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x800078a4#64 R Mt := by
  dx_run hlive at 0x800078ac
  refine muldi3_loop hlive (R 10) (R 11) R hal hk _ _ rfl ?_ (by keeps_tac Keeps.refl _ _)
  dc_simp []
  rw [BitVec.zero_add]


/-! ## `__hidden___udivdi3` (`0x80007910`)

```
80007910 mv a2,a1 ; 80007914 mv a1,a0 ; 80007918 li a0,-1 ; 8000791c beqz a2,80007954
80007920 li a3,1 ; 80007924 bgeu a2,a1,80007938
80007928 blez a2,80007938 ; 8000792c slli a2,a2,0x1 ; 80007930 slli a3,a3,0x1
80007934 bltu a2,a1,80007928
80007938 li a0,0
8000793c bltu a1,a2,80007948 ; 80007940 sub a1,a1,a2 ; 80007944 or a0,a0,a3
80007948 srli a3,a3,0x1 ; 8000794c srli a2,a2,0x1 ; 80007950 bnez a3,8000793c
80007954 ret
```
-/

/-- The quotient `__udivdi3` returns: `n / d`, and all ones for `d = 0`
(RISC-V `divu`). The remainder is `n % d` (`BitVec.umod`, `n` for `d = 0`). -/
def udivV (n d : BitVec 64) : BitVec 64 := if d = 0#64 then BitVec.allOnes 64 else n / d

/-- The divide loop's invariant at bit `j`: the quotient bits above `j` are in
`a0`, the remainder `a1` is below `D·2^(j+1)`. -/
structure DivInv (N D j a0 a1 : Nat) : Prop where
  low : a0 % 2 ^ (j + 1) = 0
  eq : a0 * D + a1 = N
  lt : a1 < D * 2 ^ (j + 1)

theorem two_pow_succ_mul (D j : Nat) : D * 2 ^ (j + 1) = D * 2 ^ j * 2 := by
  rw [Nat.pow_succ, Nat.mul_assoc]

theorem DivInv.skip {N D j a0 a1 : Nat} (h : DivInv N D (j + 1) a0 a1)
    (hlt : a1 < D * 2 ^ (j + 1)) : DivInv N D j a0 a1 :=
  ⟨mod_drop_pow _ _ h.low, h.eq, hlt⟩

theorem DivInv.sub {N D j a0 a1 : Nat} (h : DivInv N D j a0 a1) (hge : D * 2 ^ j ≤ a1) :
    a1 - D * 2 ^ j < D * 2 ^ j ∧ (a0 + 2 ^ j) * D + (a1 - D * 2 ^ j) = N := by
  have hl := h.lt
  have he := h.eq
  rw [two_pow_succ_mul] at hl
  refine ⟨by omega, ?_⟩
  rw [Nat.add_mul, Nat.mul_comm (2 ^ j) D]; omega

theorem DivInv.sub_succ {N D j a0 a1 : Nat} (h : DivInv N D (j + 1) a0 a1)
    (hge : D * 2 ^ (j + 1) ≤ a1) : DivInv N D j (a0 + 2 ^ (j + 1)) (a1 - D * 2 ^ (j + 1)) :=
  ⟨mod_add_pow a0 (j + 1) h.low, (h.sub hge).2, (h.sub hge).1⟩

theorem DivInv.fin {N D a0 a1 : Nat} (h : DivInv N D 0 a0 a1) (hlt : a1 < D) :
    N / D = a0 ∧ N % D = a1 :=
  (Nat.div_mod_unique (by omega)).2 ⟨by have := h.eq; rw [Nat.mul_comm D a0]; omega, hlt⟩

theorem DivInv.fin_sub {N D a0 a1 : Nat} (h : DivInv N D 0 a0 a1) (hge : D ≤ a1) :
    N / D = a0 + 1 ∧ N % D = a1 - D := by
  have := h.sub (by simpa using hge)
  simp only [Nat.pow_zero, Nat.mul_one] at this
  exact (Nat.div_mod_unique (by omega)).2 ⟨by rw [Nat.mul_comm D]; omega, this.1⟩

theorem sub_toNat {x y : BitVec 64} (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.2 h)

theorem or_pow_toNat {x y : BitVec 64} {j : Nat} (hy : y.toNat = 2 ^ j) (hx : x.toNat % 2 ^ (j + 1) = 0) :
    (x ||| y).toNat = x.toNat + 2 ^ j := by
  rw [BitVec.toNat_or, hy, or_two_pow_eq_add _ _ hx]

theorem udiv_result {n d q r : BitVec 64} (hd : d.toNat ≠ 0)
    (h : n.toNat / d.toNat = q.toNat ∧ n.toNat % d.toNat = r.toNat) :
    q = udivV n d ∧ r = n % d := by
  have hd' : d ≠ 0#64 := fun e => hd (by rw [e]; rfl)
  refine ⟨?_, ?_⟩
  · rw [udivV, ite_eq_right_iff.2 (fun h => absurd h hd')]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_udiv, h.1]
  · apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod, h.2]

theorem mul_pow_half (D j : Nat) : D * 2 ^ (j + 1) / 2 = D * 2 ^ j := by
  rw [two_pow_succ_mul]; exact Nat.mul_div_cancel _ (by decide)

theorem pow_half (j : Nat) : 2 ^ (j + 1) / 2 = 2 ^ j := by
  simpa using mul_pow_half 1 j

/-- The divide loop of `__udivdi3` at `0x8000793c`, bit `j`: `a3 = 2^j`,
`a2 = D·2^j`, `DivInv` on `a0`, `a1`. -/
theorem udiv_divide {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (n d : BitVec 64) (hd : d.toNat ≠ 0)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 12, 13] R' R0 → R' 10 = udivV n d → R' 11 = n % d →
      DW live S Q (R0 1) R' Mt) :
    ∀ j (R : Nat → BitVec 64), (R 13).toNat = 2 ^ j → (R 12).toNat = d.toNat * 2 ^ j →
      DivInv n.toNat d.toNat j (R 10).toNat (R 11).toNat → Keeps [10, 11, 12, 13] R R0 →
      DW live S Q 0x8000793c#64 R Mt := by
  have hD := hd
  intro j
  induction j with
  | zero =>
    intro R h13 h12 hinv hkeep
    simp only [Nat.pow_zero, Nat.mul_one] at h13 h12
    have h13' : (R 13 >>> 1) = 0#64 := BitVec.eq_of_toNat_eq (by rw [shr1_toNat, h13]; rfl)
    dx_run hlive
    · -- skip
      intro hlt
      dx_run hlive
      · dc_simp [hkeep.get 1, hal]
      · rw [hkeep.get 1]
        have := udiv_result (n := n) (q := R 10) (r := R 11) hd (hinv.fin (by omega))
        refine hk _ (by keeps_tac hkeep) ?_ ?_
        · dc_simp []; exact this.1
        · dc_simp []; exact this.2
    · -- subtract
      intro hge
      dx_run hlive
      · dc_simp [hkeep.get 1, hal]
      · rw [hkeep.get 1]
        have hf := hinv.fin_sub (by omega)
        have e0 : (R 10 ||| R 13).toNat = (R 10).toNat + 1 := by
          simpa using or_pow_toNat (j := 0) (by simpa using h13) hinv.low
        have e1 : (R 11 - R 12).toNat = (R 11).toNat - d.toNat := by
          rw [sub_toNat (by omega), h12]
        have := udiv_result (n := n) (q := R 10 ||| R 13) (r := R 11 - R 12) hd (by rw [e0, e1]; exact hf)
        refine hk _ (by keeps_tac hkeep) ?_ ?_
        · dc_simp []; exact this.1
        · dc_simp []; exact this.2
  | succ j ih =>
    intro R h13 h12 hinv hkeep
    have e3 : (R 13 >>> 1).toNat = 2 ^ j := by rw [shr1_toNat, h13, pow_half]
    have e2 : (R 12 >>> 1).toNat = d.toNat * 2 ^ j := by rw [shr1_toNat, h12, mul_pow_half]
    have hne3 : R 13 >>> 1 ≠ 0#64 := fun e => by
      have := congrArg BitVec.toNat e; rw [e3] at this; exact absurd this (Nat.ne_of_gt (Nat.two_pow_pos j))
    dx_run hlive
    · -- skip
      intro hlt
      dx_run hlive
      · intro _
        refine ih _ ?_ ?_ ?_ (by keeps_tac hkeep)
        · dc_simp []; exact e3
        · dc_simp []; exact e2
        · dc_simp []; exact hinv.skip (by omega)
      · intro hz; dc_simp [] at hz; exact absurd hne3 hz
    · -- subtract
      intro hge
      dx_run hlive
      · intro _
        refine ih _ ?_ ?_ ?_ (by keeps_tac hkeep)
        · dc_simp []; exact e3
        · dc_simp []; exact e2
        · dc_simp []
          rw [or_pow_toNat h13 hinv.low, sub_toNat (by omega), h12]
          exact hinv.sub_succ (by omega)
      · intro hz; dc_simp [] at hz; exact absurd hne3 hz


theorem shl1_toNat {x : BitVec 64} (h : x.toNat < 2 ^ 63) : (x <<< 1).toNat = x.toNat * 2 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]; omega

theorem toInt_le0_iff {x : BitVec 64} (h : x.toNat ≠ 0) :
    x.toInt ≤ (0#64).toInt ↔ 2 ^ 63 ≤ x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond, show (0#64).toInt = 0 from rfl]
  split <;> omega

/-- The normalize loop of `__udivdi3` at `0x80007928`: `a2 = D·2^j < n`,
`a3 = 2^j`. -/
theorem udiv_norm {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (n d : BitVec 64) (hd : d.toNat ≠ 0)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 12, 13] R' R0 → R' 10 = udivV n d → R' 11 = n % d →
      DW live S Q (R0 1) R' Mt) :
    ∀ k j (R : Nat → BitVec 64), 64 - j = k → R 11 = n → (R 13).toNat = 2 ^ j →
      (R 12).toNat = d.toNat * 2 ^ j → (R 12).toNat < n.toNat → Keeps [10, 11, 12, 13] R R0 →
      DW live S Q 0x80007928#64 R Mt := by
  have hn := n.isLt
  intro k
  induction k with
  | zero =>
    intro j R hk0 h11 h13 h12 hlt hkeep
    have : 2 ^ 64 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    have : 2 ^ j ≤ d.toNat * 2 ^ j := Nat.le_mul_of_pos_left _ (by omega)
    omega
  | succ k ih =>
    intro j R hk0 h11 h13 h12 hlt hkeep
    have hpos : 2 ^ j ≤ d.toNat * 2 ^ j := Nat.le_mul_of_pos_left _ (by omega)
    have hjp := Nat.two_pow_pos j
    have hz : (R 12).toNat ≠ 0 := by omega
    dx_run hlive
    · -- the top bit of `a2` is set: divide from bit `j`
      intro hle
      rw [toInt_le0_iff hz] at hle
      dx_run hlive at 0x8000793c
      refine udiv_divide hlive n d hd R0 hal hk j _ ?_ ?_ ?_ (by keeps_tac hkeep)
      · dc_simp []; exact h13
      · dc_simp []; exact h12
      · dc_simp []
        refine ⟨Nat.zero_mod _, by rw [h11]; omega, ?_⟩
        rw [two_pow_succ_mul, h11]; omega
    · intro hgt
      rw [toInt_le0_iff hz] at hgt
      have e12 : (R 12 <<< 1).toNat = d.toNat * 2 ^ (j + 1) := by
        rw [shl1_toNat (by omega), h12, two_pow_succ_mul]
      have e13 : (R 13 <<< 1).toNat = 2 ^ (j + 1) := by
        rw [shl1_toNat (by omega), h13, Nat.pow_succ]
      dx_run hlive
      · -- still below `n`: shift again
        intro hlt'
        dc_simp [] at hlt'
        refine ih (j + 1) _ (by omega) ?_ ?_ ?_ ?_ (by keeps_tac hkeep)
        · dc_simp [h11]
        · dc_simp []; exact e13
        · dc_simp []; exact e12
        · dc_simp []; rw [e12, ← h11]; rw [e12] at hlt'; exact hlt'
      · intro hge
        dc_simp [] at hge
        dx_run hlive at 0x8000793c
        refine udiv_divide hlive n d hd R0 hal hk (j + 1) _ ?_ ?_ ?_ (by keeps_tac hkeep)
        · dc_simp []; exact e13
        · dc_simp []; exact e12
        · dc_simp [h11]
          rw [h11] at hge
          refine ⟨Nat.zero_mod _, by omega, ?_⟩
          rw [two_pow_succ_mul, ← e12]; omega

/-- **`__hidden___udivdi3(n, d)`** at `0x80007910`: `a0 = udivV n d`
(`n / d`, all ones for `d = 0`), `a1 = n % d`; clobbers `a2`, `a3`. -/
theorem udivdi3_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 12, 13] R' R → R' 10 = udivV (R 10) (R 11) →
      R' 11 = R 10 % R 11 → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x80007910#64 R Mt := by
  dx_run hlive
  · -- `d = 0`
    intro hz
    dc_simp [] at hz
    dx_run hlive
    refine hk _ (by keeps_tac Keeps.refl _ _) ?_ ?_
    · dc_simp []; rw [udivV, ite_eq_left_iff.2 (fun h => absurd hz h)]; rfl
    · dc_simp []; rw [hz, BitVec.umod_zero]
  · intro hnz
    dc_simp [] at hnz
    have hd : (R 11).toNat ≠ 0 := fun e => hnz (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    dx_run hlive
    · -- `d ≥ n`: one quotient bit
      intro hge
      dc_simp [] at hge
      dx_run hlive at 0x8000793c
      refine udiv_divide hlive (R 10) (R 11) hd R hal hk 0 _ ?_ ?_ ?_ (by keeps_tac Keeps.refl _ _)
      · dc_simp []; try rfl
      · dc_simp []; try simp
      · dc_simp []
        exact ⟨Nat.zero_mod _, by omega, by simp; omega⟩
    · intro hlt
      dc_simp [] at hlt
      refine udiv_norm hlive (R 10) (R 11) hd R hal hk (64 - 0) 0 _ rfl ?_ ?_ ?_ ?_
        (by keeps_tac Keeps.refl _ _)
      · dc_simp []
      · dc_simp []; try rfl
      · dc_simp []; try simp
      · dc_simp []; omega


/-! ## The signed and remainder wrappers

They call `__hidden___udivdi3` with the return address in `t0` and clobber
`ra`, `t0`, `a0`–`a3` (`Keeps [1, 5, 10, 11, 12, 13]`).

```
80007908 bltz a0,80007968 ; 8000790c bltz a1,80007978      (__divdi3)
80007958 mv t0,ra ; 8000795c jal __hidden___udivdi3 ; 80007960 mv a0,a1 ; 80007964 jr t0
80007968 neg a0,a0 ; 8000796c bgtz a1,8000797c ; 80007970 neg a1,a1 ; 80007974 j 80007910
80007978 neg a1,a1 ; 8000797c mv t0,ra ; 80007980 jal … ; 80007984 neg a0,a0 ; 80007988 jr t0
8000798c mv t0,ra ; 80007990 bltz a1,800079a4 ; 80007994 bltz a0,800079ac     (__moddi3)
80007998 jal … ; 8000799c mv a0,a1 ; 800079a0 jr t0
800079a4 neg a1,a1 ; 800079a8 bgez a0,80007998
800079ac neg a0,a0 ; 800079b0 jal … ; 800079b4 neg a0,a1 ; 800079b8 jr t0
```
-/

/-- The quotient `__divdi3` returns: `BitVec.sdiv`, all ones for `d = 0`. -/
def sdivV (n d : BitVec 64) : BitVec 64 := if d = 0#64 then BitVec.allOnes 64 else n.sdiv d

theorem toInt_lt0_msb (x : BitVec 64) : x.toInt < (0#64).toInt ↔ x.msb = true := by
  rw [show (0#64).toInt = 0 from rfl, BitVec.toInt_neg_iff, BitVec.msb_eq_decide]; simp; omega

theorem toInt_ge0_msb (x : BitVec 64) : (0#64).toInt ≤ x.toInt ↔ x.msb = false := by
  have := toInt_lt0_msb x
  constructor
  · intro h; cases hm : x.msb
    · rfl
    · exact absurd (this.2 hm) (by omega)
  · intro h; exact Int.not_lt.1 fun h' => by rw [this.1 h'] at h; exact absurd h (by decide)

theorem toInt_gt0 (x : BitVec 64) : (0#64).toInt < x.toInt ↔ x.msb = false ∧ x ≠ 0#64 := by
  rw [show (0#64).toInt = 0 from rfl, BitVec.toInt_eq_toNat_cond x, BitVec.msb_eq_decide]
  constructor
  · intro h
    refine ⟨?_, fun e => by rw [e] at h; simp at h⟩
    split at h <;> simp <;> omega
  · rintro ⟨h1, h2⟩
    have : x.toNat ≠ 0 := fun e => h2 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    simp at h1
    split <;> omega

theorem neg_msb_false {x : BitVec 64} (h : x.msb = true) : x ≠ 0#64 := by
  rintro rfl; simp at h

theorem neg_ne_zero {x : BitVec 64} (h : x ≠ 0#64) : -x ≠ 0#64 := by
  intro e; apply h; rw [← BitVec.neg_neg (x := x), e]; rfl

theorem sdivV_pp {n d : BitVec 64} (hn : n.msb = false) (hd : d.msb = false) :
    sdivV n d = udivV n d := by
  unfold sdivV udivV
  split
  · rfl
  · simp [BitVec.sdiv, hn, hd, BitVec.udiv_eq]

theorem sdivV_pn {n d : BitVec 64} (hn : n.msb = false) (hd : d.msb = true) :
    sdivV n d = -(udivV n (-d)) := by
  unfold sdivV udivV
  simp [neg_msb_false hd, neg_ne_zero (neg_msb_false hd), BitVec.sdiv, hn, hd, BitVec.udiv_eq,
    BitVec.neg_eq]

theorem sdivV_np {n d : BitVec 64} (hn : n.msb = true) (hd : d.msb = false) (hd0 : d ≠ 0#64) :
    sdivV n d = -(udivV (-n) d) := by
  unfold sdivV udivV
  simp [hd0, BitVec.sdiv, hn, hd, BitVec.udiv_eq, BitVec.neg_eq]

theorem sdivV_n0 {n : BitVec 64} : sdivV n 0#64 = udivV (-n) (-0#64) := by
  unfold sdivV udivV; simp

theorem sdivV_nn {n d : BitVec 64} (hn : n.msb = true) (hd : d.msb = true) :
    sdivV n d = udivV (-n) (-d) := by
  unfold sdivV udivV
  simp [neg_msb_false hd, neg_ne_zero (neg_msb_false hd), BitVec.sdiv, hn, hd, BitVec.udiv_eq,
    BitVec.neg_eq]

theorem srem_pp {n d : BitVec 64} (hn : n.msb = false) (hd : d.msb = false) :
    n.srem d = n % d := by simp [BitVec.srem, hn, hd, BitVec.umod_eq]

theorem srem_pn {n d : BitVec 64} (hn : n.msb = false) (hd : d.msb = true) :
    n.srem d = n % (-d) := by simp [BitVec.srem, hn, hd, BitVec.umod_eq, BitVec.neg_eq]

theorem srem_np {n d : BitVec 64} (hn : n.msb = true) (hd : d.msb = false) :
    n.srem d = -((-n) % d) := by simp [BitVec.srem, hn, hd, BitVec.umod_eq, BitVec.neg_eq]

theorem srem_nn {n d : BitVec 64} (hn : n.msb = true) (hd : d.msb = true) :
    n.srem d = -((-n) % (-d)) := by simp [BitVec.srem, hn, hd, BitVec.umod_eq, BitVec.neg_eq]

/-- The registers a `__hidden___udivdi3` wrapper may change. -/
abbrev divClob : List Nat := [1, 5, 10, 11, 12, 13]

theorem keeps_div {R' R1 R : Nat → BitVec 64} (h : Keeps [10, 11, 12, 13] R' R1)
    (h1 : Keeps divClob R1 R) : Keeps divClob R' R :=
  (h.mono (by decide)).trans h1

/-- **`__umoddi3(n, d)`** at `0x80007958`: `a0 = n % d`. -/
theorem umoddi3_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps divClob R' R → R' 10 = R 10 % R 11 → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x80007958#64 R Mt := by
  dx_run hlive at 0x80007910
  refine udivdi3_spec hlive _ (by dc_simp []; try decide) fun R' hkeep _ hr => ?_
  have h5 : R' 5 = R 1 := by rw [hkeep.get 5]; dc_simp []
  show DW live S Q 0x80007960#64 R' Mt
  dx_run hlive
  · dc_simp [h5, hal]
  · rw [h5]
    refine hk _ (by keeps_tac (keeps_div hkeep (by keeps_tac Keeps.refl _ _))) ?_
    dc_simp [hr]


/-- `__divdi3`'s negated call at `0x8000797c`: `a0 = -(udivV a0 a1)`, back at `ra`. -/
theorem divdi3_negCall {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps divClob R' R → R' 10 = -(udivV (R 10) (R 11)) → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x8000797c#64 R Mt := by
  dx_run hlive at 0x80007910
  refine udivdi3_spec hlive _ (by dc_simp []; try decide) fun R' hkeep hq _ => ?_
  have h5 : R' 5 = R 1 := by rw [hkeep.get 5]; dc_simp []
  show DW live S Q 0x80007984#64 R' Mt
  dx_run hlive
  · dc_simp [h5, hal]
  · rw [h5]
    refine hk _ (by keeps_tac (keeps_div hkeep (by keeps_tac Keeps.refl _ _))) ?_
    dc_simp [hq, BitVec.zero_sub]

/-- **`__divdi3(n, d)`** at `0x80007908`: `a0 = sdivV n d` (`BitVec.sdiv`,
all ones for `d = 0`). -/
theorem divdi3_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps divClob R' R → R' 10 = sdivV (R 10) (R 11) → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x80007908#64 R Mt := by
  dx_run hlive
  · -- `n < 0`
    intro hn
    rw [toInt_lt0_msb] at hn
    dx_run hlive
    · -- `d > 0`
      intro hd
      rw [toInt_gt0] at hd
      dc_simp [] at hd
      refine divdi3_negCall hlive _ hal fun R' hkeep hq => hk R' ?_ ?_
      · exact hkeep.trans (by keeps_tac Keeps.refl _ _)
      · rw [hq, sdivV_np hn hd.1 hd.2]; dc_simp [BitVec.zero_sub]
    · intro hd
      dc_simp [] at hd
      dx_run hlive at 0x80007910
      refine udivdi3_spec hlive _ hal fun R' hkeep hq _ => hk R' ?_ ?_
      · exact keeps_div hkeep (by keeps_tac Keeps.refl _ _)
      · rw [hq]; dc_simp [BitVec.zero_sub]
        by_cases hd0 : R 11 = 0#64
        · rw [hd0, sdivV_n0]
        · have hm : (R 11).msb = true := by
            cases hm : (R 11).msb
            · exact absurd ((toInt_gt0 _).2 ⟨hm, hd0⟩) hd
            · rfl
          rw [sdivV_nn hn hm]
  · intro hn
    rw [toInt_lt0_msb] at hn
    have hn' : (R 10).msb = false := by simpa using hn
    dx_run hlive
    · -- `d < 0`
      intro hd
      rw [toInt_lt0_msb] at hd
      dx_run hlive at 0x8000797c
      refine divdi3_negCall hlive _ hal fun R' hkeep hq => hk R' ?_ ?_
      · exact hkeep.trans (by keeps_tac Keeps.refl _ _)
      · rw [hq, sdivV_pn hn' hd]; dc_simp [BitVec.zero_sub]
    · intro hd
      rw [toInt_lt0_msb] at hd
      have hd' : (R 11).msb = false := by simpa using hd
      refine udivdi3_spec hlive _ hal fun R' hkeep hq _ => hk R' ?_ ?_
      · exact keeps_div hkeep (Keeps.refl _ _)
      · rw [hq, sdivV_pp hn' hd']


/-- `__moddi3`'s call at `0x80007998` (`t0` the return address): `a0 = a0 % a1`. -/
theorem moddi3_posCall {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (hal : (R 5).toNat % 4 = 0)
    (hk : ∀ R', Keeps divClob R' R → R' 10 = R 10 % R 11 → DW live S Q (R 5) R' Mt) :
    DW live S Q 0x80007998#64 R Mt := by
  dx_run hlive at 0x80007910
  refine udivdi3_spec hlive _ (by dc_simp []; try decide) fun R' hkeep _ hr => ?_
  have h5 : R' 5 = R 5 := by rw [hkeep.get 5]; dc_simp []
  show DW live S Q 0x8000799c#64 R' Mt
  dx_run hlive
  · dc_simp [h5, hal]
  · rw [h5]
    refine hk _ (by keeps_tac (keeps_div hkeep (by keeps_tac Keeps.refl _ _))) ?_
    dc_simp [hr]

/-- `__moddi3`'s negated call at `0x800079ac`: `a0 = -((-a0) % a1)`. -/
theorem moddi3_negCall {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (hal : (R 5).toNat % 4 = 0)
    (hk : ∀ R', Keeps divClob R' R → R' 10 = -((-R 10) % R 11) → DW live S Q (R 5) R' Mt) :
    DW live S Q 0x800079ac#64 R Mt := by
  dx_run hlive at 0x80007910
  refine udivdi3_spec hlive _ (by dc_simp []; try decide) fun R' hkeep _ hr => ?_
  have h5 : R' 5 = R 5 := by rw [hkeep.get 5]; dc_simp []
  show DW live S Q 0x800079b4#64 R' Mt
  dx_run hlive
  · dc_simp [h5, hal]
  · rw [h5]
    refine hk _ (by keeps_tac (keeps_div hkeep (by keeps_tac Keeps.refl _ _))) ?_
    dc_simp [hr, BitVec.zero_sub]

/-- **`__moddi3(n, d)`** at `0x8000798c`: `a0 = n.srem d` (the C `%`, sign
of the dividend; `n` for `d = 0`). -/
theorem moddi3_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps divClob R' R → R' 10 = (R 10).srem (R 11) → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x8000798c#64 R Mt := by
  dx_run hlive
  · -- `d < 0`
    intro hd
    rw [toInt_lt0_msb] at hd
    dc_simp [] at hd
    dx_run hlive at 0x80007998 0x800079ac
    · intro hn
      rw [toInt_ge0_msb] at hn
      dc_simp [] at hn
      refine moddi3_posCall hlive _ (by dc_simp [hal]) fun R' hkeep hr => ?_
      dc_simp []
      refine hk R' (hkeep.trans (by keeps_tac Keeps.refl _ _)) ?_
      rw [hr, srem_pn hn hd]; dc_simp [BitVec.zero_sub]
    · intro hn
      rw [toInt_ge0_msb] at hn
      dc_simp [] at hn
      have hn' : (R 10).msb = true := by simpa using hn
      refine moddi3_negCall hlive _ (by dc_simp [hal]) fun R' hkeep hr => ?_
      dc_simp []
      refine hk R' (hkeep.trans (by keeps_tac Keeps.refl _ _)) ?_
      rw [hr, srem_nn hn' hd]; dc_simp [BitVec.zero_sub]
  · intro hd
    rw [toInt_lt0_msb] at hd
    dc_simp [] at hd
    have hd' : (R 11).msb = false := by simpa using hd
    dx_run hlive at 0x80007998 0x800079ac
    · intro hn
      rw [toInt_lt0_msb] at hn
      dc_simp [] at hn
      refine moddi3_negCall hlive _ (by dc_simp [hal]) fun R' hkeep hr => ?_
      dc_simp []
      refine hk R' (hkeep.trans (by keeps_tac Keeps.refl _ _)) ?_
      rw [hr, srem_np hn hd']; dc_simp []
    · intro hn
      rw [toInt_lt0_msb] at hn
      dc_simp [] at hn
      have hn' : (R 10).msb = false := by simpa using hn
      refine moddi3_posCall hlive _ (by dc_simp [hal]) fun R' hkeep hr => ?_
      dc_simp []
      refine hk R' (hkeep.trans (by keeps_tac Keeps.refl _ _)) ?_
      rw [hr, srem_pp hn' hd']; dc_simp []

end Dc.Mach
