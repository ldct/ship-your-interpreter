import Dc.Mach.Bc.Small

/-!
# `bc_is_zero`, `bc_is_near_zero`, `bc_num2long` (`lib/number.c`)

Read-only scans of the digits of one number:

- `bc_is_zero_spec`: `a0 = 1` iff the number is zero (`Num.isZero`); the
  quick check `num == _zero_` needs `_zero_`'s object to be zero.
- `bc_is_near_zero_spec`: `a0 = 1` iff `Num.isNearZero n s`.
- `bc_num2long_spec`: `a0 = Num.toLong n` (the loop stops once the value
  exceeds `LONG_MAX / 10` with digits left, and then returns `0`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

theorem NumAt.getD_lt {Mt : Mem} {o : NumRep} (h : NumAt Mt o) (i : Nat) : o.ds.getD i 0 < 10 :=
  getD_digit h.shape.dig i

/-- The `lbu` of a digit. -/
theorem NumAt.lbu {Mt : Mem} {o : NumRep} (h : NumAt Mt o) {i : Nat} (hi : i < o.len + o.scale) :
    ldv .lbu Mt (o.val + i) = BitVec.ofNat 64 (o.ds.getD i 0) := by
  rw [ldv_lbu, h.digit i hi]
  have := h.getD_lt i
  apply BitVec.eq_of_toNat_eq
  rw [toNat_zext8, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- `addiw r, r, -1` on a small positive word. -/
theorem sxw_pred {k : Nat} (h1 : 1 ≤ k) (h2 : k < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (k + 18446744073709551615))) =
      BitVec.ofNat 64 (k - 1) := by
  rw [show BitVec.ofNat 64 (k + 18446744073709551615) = BitVec.ofNat 64 (k - 1) by
    apply BitVec.eq_of_toNat_eq; simp; omega]
  exact sxw_ofNat (by omega)


/-! ## `bc_is_zero` (`0x80004a10`)

```
80004a10 auipc a5,0x18 ; 80004a14 ld a5,952(a5) (_zero_) ; 80004a18 beq a5,a0,80004a50
80004a1c lw a4,4(a0) ; 80004a20 lw a5,8(a0) ; 80004a24 addw a5,a5,a4
80004a28 blez a5,80004a58 ; 80004a2c ld a4,32(a0) ; 80004a30 j 80004a38
80004a34 beqz a5,80004a50 ; 80004a38 lbu a3,0(a4) ; 80004a3c addiw a5,a5,-1
80004a40 addi a4,a4,1 ; 80004a44 beqz a3,80004a34 ; 80004a48 li a0,0 ; 80004a4c ret
80004a50 li a0,1 ; 80004a54 ret ; 80004a58 seqz a0,a5 ; 80004a5c ret
```
-/

/-- The scan at `0x80004a38`: `a4 = n_value + i`, `a5 = n_len + n_scale - i`,
the first `i` digits zero. -/
theorem is_zero_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 13, 14, 15] R' R0 → R' 10 = boolWord o.num.isZero →
      DW live S Q (R0 1) R' Mt) :
    ∀ k i (R : Nat → BitVec 64), o.len + o.scale - i = k → i < o.len + o.scale →
      R 14 = BitVec.ofNat 64 (o.val + i) → R 15 = BitVec.ofNat 64 (o.len + o.scale - i) →
      (∀ j, j < i → o.ds.getD j 0 = 0) → Keeps [10, 13, 14, 15] R R0 →
      DW live S Q 0x80004a38#64 R Mt := by
  num_facts h
  intro k
  induction k with
  | zero => intro i R h1 h2; omega
  | succ k ih =>
    intro i R hn hi h14 h15 hz hkeep
    have hd := h.getD_lt i
    dx_run hlive
    all_goals bsimp [h14, h15, h.lbu hi, sxw_pred]
    all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
    · intro h0
      bsimp [ofNat_eq_zero_iff] at h0
      dx_run hlive
      · intro hc
        bsimp [ofNat_eq_zero_iff] at hc
        dx_run hlive
        · bsimp [hkeep.get 1, hal]
        · rw [hkeep.get 1]
          refine hk _ (by keeps_tac hkeep) ?_
          have : dval o.ds = 0 := (dval_eq_zero_iff _).2 fun j hj => by
            rcases Nat.lt_or_ge j i with h1 | h1
            · exact hz j h1
            · rw [show j = i by omega]; exact h0
          have e : o.num.isZero = true := by simp [Dc.Num.isZero, NumRep.num, this]
          rw [e]; rfl
      · intro hc
        bsimp [ofNat_eq_zero_iff] at hc
        refine ih (i + 1) _ (by omega) (by omega) ?_ ?_ ?_ (by keeps_tac hkeep)
        · bsimp [Nat.add_assoc]
        · bsimp [Nat.sub_sub]
        · intro j hj
          rcases Nat.lt_or_ge j i with h1 | h1
          · exact hz j h1
          · rw [show j = i by omega]; exact h0
    · intro h0
      bsimp [ofNat_eq_zero_iff] at h0
      dx_run hlive
      · bsimp [hkeep.get 1, hal]
      · rw [hkeep.get 1]
        refine hk _ (by keeps_tac hkeep) ?_
        have : dval o.ds ≠ 0 := fun e => h0 ((dval_eq_zero_iff _).1 e i (by omega))
        have e : o.num.isZero = false := by simp [Dc.Num.isZero, NumRep.num, this]
        rw [e]; rfl

/-- **`bc_is_zero(num)`** at `0x80004a10`: `a0` is `1` if the number is
zero, else `0`; clobbers `a3`–`a5`. `hz`: if `num` is `_zero_`'s object, the
number is zero. -/
theorem bc_is_zero_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o)
    (hzg : ∀ b, 0x8001cdc8 ≤ b → b < 0x8001cdd0 → S b)
    (hz : ldv .ld Mt zeroAddr = BitVec.ofNat 64 o.p → o.num.isZero = true)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 o.p) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 13, 14, 15] R' R → R' 10 = boolWord o.num.isZero →
      DW live S Q (R 1) R' Mt) :
    DW live S Q 0x80004a10#64 R Mt := by
  num_facts h
  have hl := h.len; have hsc := h.scale; have hv := h.value
  have hz' : ldv .ld Mt 2147601864 = BitVec.ofNat 64 o.p → o.num.isZero = true := hz
  dx_run hlive at 0x80004a14
  apply st_80004a14 hlive
  · bsimp []; bc_addr
  · bsimp []; intro b hb; have := of_mem_accAddrs hb; exact hzg b (by omega) (by omega)
  dx_run hlive
  all_goals bsimp [h10, hl, hsc, hv, sxw_ofNat]
  all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
  · intro he
    dx_run hlive
    refine hk _ (by keeps_tac Keeps.refl _ _) ?_
    rw [hz' he]; rfl
  · intro _
    dx_run hlive
    all_goals bsimp [h10, hl, hsc, hv, sxw_ofNat, addw_ofNat]
    all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
    · intro hc; exact absurd hc (not_blez (by omega) (by omega))
    · intro _
      dx_run hlive at 0x80004a38
      all_goals bsimp [h10, hl, hsc, hv, sxw_ofNat, addw_ofNat]
      all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
      refine is_zero_loop hlive hS h R hal hk _ 0 _ rfl (by omega)
        ?_ ?_ (fun j hj => absurd hj (Nat.not_lt_zero _)) (by keeps_tac Keeps.refl _ _)
      · bsimp []
      · bsimp [Nat.add_comm]

end Dc.Mach
