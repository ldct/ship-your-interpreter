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

/-! ## `bc_num2long` (`0x800065a0`)

```
800065a0 lw a3,4(a0) ; 800065a4 blez a3,80006604 ; 800065a8 ld a2,32(a0)
800065ac lui a6,0xcccd ; 800065b0 addi a6,a6,-819 (LONG_MAX/10 + 1) ; 800065b4 li a4,0
800065b8 slli a5,a4,0x2 ; 800065bc lbu a1,0(a2) ; 800065c0 add a5,a5,a4 ; 800065c4 slli a5,a5,0x1
800065c8 addiw a3,a3,-1 ; 800065cc addi a2,a2,1 ; 800065d0 add a4,a1,a5
800065d4 beqz a3,800065dc ; 800065d8 blt a4,a6,800065b8
800065dc li a5,0 ; 800065e0 bnez a3,800065f0
800065e4 not a5,a4 ; 800065e8 srai a5,a5,0x3f ; 800065ec and a5,a4,a5 (val < 0 → 0)
800065f0 lw a4,0(a0) ; 800065f4 beqz a4,800065fc ; 800065f8 neg a5,a5
800065fc mv a0,a5 ; 80006600 ret ; 80006604 li a5,0 ; 80006608 j 800065f0
```
-/

/-- The unsigned value `bc_num2long` computes: the integer part, or `0` when
the loop stops early. -/
def num2longVal (o : NumRep) : Nat :=
  if dval (o.ds.take (o.len - 1)) ≤ 214748364 then dval (o.ds.take o.len) else 0

/-- The digit loop at `0x800065b8`: `a4 = dval (take i)`, `a3 = n_len - i`,
`a2 = n_value + i`, `a6 = LONG_MAX/10 + 1`. -/
theorem num2long_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o)
    (R0 : Nat → BitVec 64)
    (hk : ∀ R', Keeps [11, 12, 13, 14, 15, 16] R' R0 → R' 15 = BitVec.ofNat 64 (num2longVal o) →
      DW live S Q 0x800065f0#64 R' Mt) :
    ∀ k i (R : Nat → BitVec 64), o.len - i = k → i < o.len →
      R 14 = BitVec.ofNat 64 (dval (o.ds.take i)) → dval (o.ds.take i) ≤ 214748364 →
      R 13 = BitVec.ofNat 64 (o.len - i) → R 12 = BitVec.ofNat 64 (o.val + i) →
      R 16 = BitVec.ofNat 64 214748365 → Keeps [11, 12, 13, 14, 15, 16] R R0 →
      DW live S Q 0x800065b8#64 R Mt := by
  num_facts h
  intro k
  induction k with
  | zero => intro i R h1 h2; omega
  | succ k ih =>
    intro i R hn hi h14 hv h13 h12 h16 hkeep
    have hd := h.getD_lt i
    have hsucc := dval_take_succ o.ds (m := i) (by omega)
    have hnx : o.ds.getD i 0 + (dval (o.ds.take i) * 2 ^ 2 + dval (o.ds.take i)) * 2 ^ 1 =
        dval (o.ds.take (i + 1)) := by rw [hsucc]; omega
    dx_run hlive
    all_goals bsimp [h14, h13, h12, h16, h.lbu (show i < o.len + o.scale by omega), sxw_pred,
      shl_ofNat, hnx]
    all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
    · intro h0
      bv_nat at h0
      have hl : i + 1 = o.len := by omega
      dx_run hlive at 0x800065f0
      refine hk _ (by keeps_tac hkeep) ?_
      have hv1 : dval (o.ds.take (i + 1)) < 2 ^ 63 := by omega
      bsimp [max0_ofNat hv1]
      unfold num2longVal
      rw [ite_eq_left (by rw [show o.len - 1 = i by omega]; exact hv), hl]
    · intro h0
      bv_nat at h0
      dx_run hlive at 0x800065f0
      all_goals bsimp [h16, toInt_ofNat_small]
      · intro hlt
        refine ih (i + 1) _ (by omega) (by omega) ?_ (by omega) ?_ ?_ ?_ (by keeps_tac hkeep)
        · bsimp []
        · bsimp [Nat.sub_sub]
        · bsimp [Nat.add_assoc]
        · bsimp [h16]
      · intro hge
        dx_run hlive at 0x800065f0
        rotate_left
        · intro hc; bsimp [] at hc; bv_nat at hc; omega
        intro _
        refine hk _ (by keeps_tac hkeep) ?_
        bsimp []
        unfold num2longVal
        have := dval_take_mono o.ds (show i + 1 ≤ o.len - 1 by omega)
        simp only [show ¬ dval (o.ds.take (o.len - 1)) ≤ 214748364 by omega, ite_false]

/-- `Num.toLong` of an object: `num2longVal` with the sign. -/
theorem NumRep.toLong_eq {o : NumRep} (hs : NumShape o) :
    o.num.toLong = if o.neg then -(num2longVal o : Int) else (num2longVal o : Int) := by
  have hip : o.num.intPart = dval (o.ds.take o.len) := by
    have := dval_div_take o.ds hs.dig o.len
    rw [hs.dsLen, Nat.add_sub_cancel_left] at this
    exact this
  have hlen := hs.lenPos
  have h10 : dval (o.ds.take o.len) / 10 = dval (o.ds.take (o.len - 1)) := by
    have e := dval_take_succ o.ds (m := o.len - 1) (by rw [hs.dsLen]; omega)
    rw [Nat.sub_add_cancel hlen] at e
    have := getD_digit hs.dig (o.len - 1)
    omega
  simp only [Dc.Num.toLong, hip, h10, num2longVal, NumRep.num_neg, Dc.Num.longMax]
  by_cases hc : dval (o.ds.take (o.len - 1)) ≤ 214748364
  · simp [hc]
  · simp [hc]

/-- **`bc_num2long(num)`** at `0x800065a0`: `a0 = Num.toLong n` (as a 64-bit
`long`); clobbers `a1`–`a6`. -/
theorem bc_num2long_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 o.p) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 12, 13, 14, 15, 16] R' R → R' 10 = BitVec.ofInt 64 o.num.toLong →
      DW live S Q (R 1) R' Mt) :
    DW live S Q 0x800065a0#64 R Mt := by
  num_facts h
  have hl := h.len; have hv := h.value; have hsg := h.sign
  have hV : num2longVal o ≤ 2147483649 := by
    unfold num2longVal
    split
    · rename_i hc
      have e := dval_take_succ o.ds (m := o.len - 1) (by omega)
      rw [Nat.sub_add_cancel h.shape.lenPos] at e
      have := getD_digit h.shape.dig (o.len - 1)
      omega
    · omega
  dx_run hlive at 0x800065b8
  all_goals bsimp [h10, hl, hv]
  all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
  · intro hc; exact absurd hc (not_blez (by omega) (by omega))
  intro _
  dx_run hlive at 0x800065b8
  all_goals bsimp [h10, hl, hv]
  all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
  refine num2long_loop hlive hS h R (fun R' hkp h15 => ?_) _ 0 _ rfl (by omega) ?_ (by simp) ?_ ?_ ?_
    (by keeps_tac Keeps.refl _ _)
  · have h10' : R' 10 = BitVec.ofNat 64 o.p := (hkp.get 10).trans h10
    have hkR : R' 1 = R 1 := hkp.get 1
    have hlong := NumRep.toLong_eq h.shape
    cases hneg : o.neg
    · rw [hneg, signWord_false] at hsg
      rw [hneg] at hlong
      dx_run hlive
      all_goals bsimp [h10', hsg, h15, hkR, hal]
      all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
      · intro _
        dx_run hlive
        all_goals bsimp [h10', hsg, h15, hkR, hal]
        refine hk _ (by keeps_tac (hkp.mono (by decide))) ?_
        bsimp [hlong]
        simp only [Bool.false_eq_true, ite_false, BitVec.ofInt_natCast]
      · intro hc; exact absurd trivial hc
    · rw [hneg, signWord_true] at hsg
      rw [hneg] at hlong
      dx_run hlive
      all_goals bsimp [h10', hsg, h15, hkR, hal]
      all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
      · intro hc; exact absurd hc (by decide)
      · intro _
        dx_run hlive
        all_goals bsimp [h10', hsg, h15, hkR, hal]
        refine hk _ (by keeps_tac (hkp.mono (by decide))) ?_
        bsimp [hlong]
        rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]
        exact BitVec.zero_sub _
  all_goals bsimp [List.take_zero, dval_nil]

end Dc.Mach
