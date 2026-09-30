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

/-! ## `bc_is_near_zero` (`0x80004a60`)

```
80004a60 lw a4,8(a0) ; 80004a64 mv a5,a4 ; 80004a68 bge a1,a4,80004a70 ; 80004a6c mv a5,a1
80004a70 lw a4,4(a0) ; 80004a74 addw a5,a5,a4 ; 80004a78 blez a5,80004abc
80004a7c ld a4,32(a0) ; 80004a80 j 80004a8c
80004a84 addiw a5,a5,-1 ; 80004a88 beqz a5,80004ab4
80004a8c lbu a3,0(a4) ; 80004a90 addi a4,a4,1 ; 80004a94 beqz a3,80004a84
80004a98 li a4,1 ; 80004a9c li a0,0 ; 80004aa0 bne a5,a4,80004ab0
80004aa4 addi a3,a3,-1 ; 80004aa8 seqz a0,a3 ; 80004aac ret
80004ab0 ret ; 80004ab4 li a0,1 ; 80004ab8 ret ; 80004abc seqz a0,a5 ; 80004ac0 ret
```
-/

theorem getD_take {ds : List Nat} {m j : Nat} (h : j < m) : (ds.take m).getD j 0 = ds.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ite_true]

/-- `Num.isNearZero` on an object: the first `n_len + min s n_scale` digits
are at most one. -/
theorem NumRep.isNearZero_eq {o : NumRep} (hs : NumShape o) (s : Nat) :
    o.num.isNearZero s = decide (dval (o.ds.take (o.len + min s o.scale)) ≤ 1) := by
  have e := dval_div_take o.ds hs.dig (o.len + min s o.scale)
  rw [hs.dsLen, show o.len + o.scale - (o.len + min s o.scale) = o.scale - min s o.scale by omega] at e
  simp only [Dc.Num.isNearZero, NumRep.num, e]

/-- The scan at `0x80004a8c`: `a4 = n_value + i`, `a5 = c - i` for
`c = n_len + min s n_scale`, the first `i` digits zero. -/
theorem is_near_zero_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o) {c : Nat}
    (hc : c ≤ o.len + o.scale) (hc1 : 1 ≤ c) (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 13, 14, 15] R' R0 → R' 10 = boolWord (decide (dval (o.ds.take c) ≤ 1)) →
      DW live S Q (R0 1) R' Mt) :
    ∀ k i (R : Nat → BitVec 64), c - i = k → i < c →
      R 14 = BitVec.ofNat 64 (o.val + i) → R 15 = BitVec.ofNat 64 (c - i) →
      (∀ j, j < i → o.ds.getD j 0 = 0) → Keeps [10, 13, 14, 15] R R0 →
      DW live S Q 0x80004a8c#64 R Mt := by
  num_facts h
  have hlen : (o.ds.take c).length = c := List.length_take_of_le (by omega)
  have hne : o.ds.take c ≠ [] := by
    intro e; rw [e] at hlen; simp at hlen; omega
  have hiff := dval_le_one_iff _ hne
  rw [hlen] at hiff
  intro k
  induction k with
  | zero => intro i R h1 h2; omega
  | succ k ih =>
    intro i R hn hi h14 h15 hz hkeep
    have hd := h.getD_lt i
    dx_run hlive
    all_goals bsimp [h14, h15, h.lbu (show i < o.len + o.scale by omega), sxw_pred]
    all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
    · intro h0
      bsimp [ofNat_eq_zero_iff] at h0
      dx_run hlive
      all_goals bsimp [h14, h15, sxw_pred]
      · intro he
        bsimp [ofNat_eq_zero_iff] at he
        dx_run hlive
        · bsimp [hkeep.get 1, hal]
        rw [hkeep.get 1]
        refine hk _ (by keeps_tac hkeep) ?_
        have : dval (o.ds.take c) ≤ 1 := hiff.2 ⟨fun j hj => by
          rw [getD_take (by omega)]
          rcases Nat.lt_or_ge j i with h1 | h1
          · exact hz j h1
          · rw [show j = i by omega]; exact h0, by
          rw [getD_take (by omega), show c - 1 = i by omega, h0]; omega⟩
        rw [decide_eq_true this]; rfl
      · intro he
        bsimp [ofNat_eq_zero_iff] at he
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
      all_goals bsimp [h14, h15]
      · intro hne1
        bv_nat at hne1
        dx_run hlive
        · bsimp [hkeep.get 1, hal]
        rw [hkeep.get 1]
        refine hk _ (by keeps_tac hkeep) ?_
        have : ¬ dval (o.ds.take c) ≤ 1 := fun hle => h0 (by
          have := (hiff.1 hle).1 i (by omega); rwa [getD_take (by omega)] at this)
        simp only [this, decide_false]; rfl
      · intro he1
        bv_nat at he1
        dx_run hlive
        · bsimp [hkeep.get 1, hal]
        rw [hkeep.get 1]
        refine hk _ (by keeps_tac hkeep) ?_
        have hi1 : i = c - 1 := by omega
        have e2 : (dval (o.ds.take c) ≤ 1) ↔ o.ds.getD i 0 = 1 := by
          rw [hiff]
          constructor
          · rintro ⟨_, h2⟩; rw [getD_take (by omega), ← hi1] at h2; omega
          · intro h1
            refine ⟨fun j hj => ?_, ?_⟩
            · rw [getD_take (by omega)]; exact hz j (by omega)
            · rw [getD_take (by omega), ← hi1, h1]; exact Nat.le_refl _
        simp only [e2]; bsimp [sltiu1, ze_bb]
        simp only [show (BitVec.ofNat 64 (o.ds.getD i 0 + 18446744073709551615)).toNat = 0 ↔ o.ds.getD i 0 = 1 by rw [BitVec.toNat_ofNat]; omega]

/-- **`bc_is_near_zero(num, s)`** at `0x80004a60`, `0 ≤ s < 2^31`: `a0` is
`1` if `Num.isNearZero n s`, else `0`; clobbers `a3`–`a5`. -/
theorem bc_is_near_zero_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o)
    {s : Nat} (hs : s < 2 ^ 31)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 o.p) (h11 : R 11 = BitVec.ofNat 64 s)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 13, 14, 15] R' R → R' 10 = boolWord (o.num.isNearZero s) →
      DW live S Q (R 1) R' Mt) :
    DW live S Q 0x80004a60#64 R Mt := by
  num_facts h
  have hl := h.len; have hsc := h.scale; have hv := h.value
  have hk' : ∀ R', Keeps [10, 13, 14, 15] R' R →
      R' 10 = boolWord (decide (dval (o.ds.take (o.len + min s o.scale)) ≤ 1)) →
      DW live S Q (R 1) R' Mt := fun R' h1 h2 => hk R' h1 (by rw [NumRep.isNearZero_eq h.shape]; exact h2)
  -- from `0x80004a70` with `a5 = min s n_scale`
  have tail : ∀ R', R' 15 = BitVec.ofNat 64 (min s o.scale) → R' 10 = BitVec.ofNat 64 o.p →
      Keeps [10, 13, 14, 15] R' R → DW live S Q 0x80004a70#64 R' Mt := by
    intro R' h15 h10' hkp
    have hmin : min s o.scale ≤ o.scale := Nat.min_le_right _ _
    dx_run hlive at 0x80004a8c
    all_goals bsimp [h10', h15, hl, hsc, hv, sxw_ofNat, addw_ofNat]
    all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
    · intro hc; exact absurd hc (not_blez (by omega) (by omega))
    · intro _
      dx_run hlive at 0x80004a8c
      all_goals bsimp [h10', hl, hsc, hv]
      all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
      refine is_near_zero_loop hlive hS h (c := o.len + min s o.scale) (by omega) (by omega) R hal
        hk' _ 0 _ rfl (by omega) ?_ ?_ (fun j hj => absurd hj (Nat.not_lt_zero _))
        (by keeps_tac hkp)
      · bsimp []
      · bsimp [Nat.add_comm]
  dx_run hlive at 0x80004a70
  all_goals bsimp [h10, h11, hl, hsc, hv]
  all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
  · intro hge
    rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hge
    refine tail _ ?_ (by bsimp [h10]) (by keeps_tac Keeps.refl _ _)
    bsimp [Nat.min_eq_right (show o.scale ≤ s by omega)]
  · intro hlt
    rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hlt
    dx_run hlive at 0x80004a70
    refine tail _ ?_ (by bsimp [h10]) (by keeps_tac Keeps.refl _ _)
    bsimp [h11, Nat.min_eq_left (show s ≤ o.scale by omega)]

end Dc.Mach
