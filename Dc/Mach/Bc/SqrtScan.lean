import Dc.Mach.Bc.SqrtBase

/-!
# `bc_sqrt`'s inlined `bc_is_near_zero (diff, cscale)` (`0x80006c04`)

```
80006c04 lw a4,8(s10) ; 80006c08 mv a5,a4 ; 80006c0c bge s11,a4,80006c14 ; 80006c10 mv a5,s11
80006c14 lw a4,4(s10) ; 80006c18 addw a5,a5,a4 ; 80006c1c blez a5,80006d40
80006c20 ld a4,32(s10) ; 80006c24 j 80006c30
80006c28 addiw a5,a5,-1 ; 80006c2c beqz a5,80006d44
80006c30 lbu a3,0(a4) ; 80006c34 addi a4,a4,1 ; 80006c38 beqz a3,80006c28
80006c3c bne a5,s5,80006c44 ; 80006c40 beq a3,s5,80006d44
80006d40 bnez a5,80006c44
```

`diff` in `s10`, `cscale` in `s11`, `1` in `s5`: near zero on to `0x80006d44`,
otherwise to `0x80006c44` (`sq_scan`), as `bc_is_near_zero_spec`
(`Scan.lean`) with the branches inlined.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The scan at `0x80006c30`: `a4 = n_value + i`, `a5 = c - i` for
`c = n_len + min s n_scale`, the first `i` digits zero. -/
theorem sq_scan_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o) {c : Nat}
    (hc : c ≤ o.len + o.scale) (hc1 : 1 ≤ c) (R0 : Nat → BitVec 64) (h21 : R0 21 = 1#64)
    (hnear : ∀ R', Keeps [13, 14, 15] R' R0 → dval (o.ds.take c) ≤ 1 →
      DW live S Q 0x80006d44#64 R' Mt)
    (hfar : ∀ R', Keeps [13, 14, 15] R' R0 → ¬ dval (o.ds.take c) ≤ 1 →
      DW live S Q 0x80006c44#64 R' Mt) :
    ∀ k i (R : Nat → BitVec 64), c - i = k → i < c →
      R 14 = BitVec.ofNat 64 (o.val + i) → R 15 = BitVec.ofNat 64 (c - i) →
      (∀ j, j < i → o.ds.getD j 0 = 0) → Keeps [13, 14, 15] R R0 →
      DW live S Q 0x80006c30#64 R Mt := by
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
    have h21' : R 21 = 1#64 := by rw [hkeep.get 21 (by decide)]; exact h21
    dx_run hlive at 0x80006d44 0x80006c44 0x80006c30
    all_goals bsimp [h14, h15, h21', h.lbu (show i < o.len + o.scale by omega), sxw_ofNat]
    all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
    · intro h0
      bsimp [ofNat_eq_zero_iff] at h0
      dx_run hlive at 0x80006d44 0x80006c44 0x80006c30
      all_goals bsimp [h14, h15, sxw_ofNat]
      · intro he
        bsimp [ofNat_eq_zero_iff] at he
        refine hnear _ (by keeps_tac hkeep) (hiff.2 ⟨fun j hj => ?_, ?_⟩)
        · rw [getD_take (by omega)]
          rcases Nat.lt_or_ge j i with h1 | h1
          · exact hz j h1
          · rw [show j = i by omega]; exact h0
        · rw [getD_take (by omega), show c - 1 = i by omega, h0]; omega
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
      dx_run hlive at 0x80006d44 0x80006c44 0x80006c30
      all_goals bsimp [h14, h15, h21']
      · intro hne1
        bv_nat at hne1
        refine hfar _ (by keeps_tac hkeep) fun hle => h0 ?_
        have := (hiff.1 hle).1 i (by omega); rwa [getD_take (by omega)] at this
      · intro he1
        bv_nat at he1
        have hi1 : i = c - 1 := by omega
        dx_run hlive at 0x80006d44 0x80006c44 0x80006c30
        all_goals bsimp [h21']
        · intro hd1
          bv_nat at hd1
          refine hnear _ (by keeps_tac hkeep) (hiff.2 ⟨fun j hj => ?_, ?_⟩)
          · rw [getD_take (by omega)]; exact hz j (by omega)
          · rw [getD_take (by omega), ← hi1]; omega
        · intro hd1
          bv_nat at hd1
          refine hfar _ (by keeps_tac hkeep) fun hle => ?_
          have := (hiff.1 hle).2
          rw [getD_take (by omega), ← hi1] at this
          omega

/-- **`bc_is_near_zero (diff, cscale)` inlined** at `0x80006c04`: `diff`
(`s10`, an integer digit) near zero at `cscale` (`s11`) goes on to
`0x80006d44`, otherwise to `0x80006c44`; clobbers `a3`–`a5`. -/
theorem sq_scan {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o)
    (hlp : 1 ≤ o.len) {s : Nat} (hs : s < 2 ^ 31)
    (R : Nat → BitVec 64) (h26 : R 26 = BitVec.ofNat 64 o.p) (h27 : R 27 = BitVec.ofNat 64 s)
    (h21 : R 21 = 1#64)
    (hnear : ∀ R', Keeps [13, 14, 15] R' R → o.num.isNearZero s = true →
      DW live S Q 0x80006d44#64 R' Mt)
    (hfar : ∀ R', Keeps [13, 14, 15] R' R → o.num.isNearZero s = false →
      DW live S Q 0x80006c44#64 R' Mt) :
    DW live S Q 0x80006c04#64 R Mt := by
  num_facts h
  have hl := h.len; have hsc := h.scale; have hv := h.value
  have hn' : ∀ R', Keeps [13, 14, 15] R' R →
      dval (o.ds.take (o.len + min s o.scale)) ≤ 1 → DW live S Q 0x80006d44#64 R' Mt :=
    fun R' h1 h2 => hnear R' h1 (by rw [NumRep.isNearZero_eq h.shape]; exact decide_eq_true h2)
  have hf' : ∀ R', Keeps [13, 14, 15] R' R →
      ¬ dval (o.ds.take (o.len + min s o.scale)) ≤ 1 → DW live S Q 0x80006c44#64 R' Mt :=
    fun R' h1 h2 => hfar R' h1 (by rw [NumRep.isNearZero_eq h.shape]; exact decide_eq_false h2)
  -- from `0x80006c14` with `a5 = min s n_scale`
  have tail : ∀ R', R' 15 = BitVec.ofNat 64 (min s o.scale) → R' 26 = BitVec.ofNat 64 o.p →
      Keeps [13, 14, 15] R' R → DW live S Q 0x80006c14#64 R' Mt := by
    intro R' h15 h26' hkp
    have hmin : min s o.scale ≤ o.scale := Nat.min_le_right _ _
    dx_run hlive at 0x80006c30 0x80006d40
    all_goals bsimp [h26', h15, hl, hsc, hv, sxw_ofNat, addw_ofNat]
    all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
    · intro hc; exact absurd hc (not_blez (by omega) (by omega))
    · intro _
      dx_run hlive at 0x80006c30
      all_goals bsimp [h26', hl, hsc, hv]
      all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
      refine sq_scan_loop hlive hS h (c := o.len + min s o.scale) (by omega) (by omega) R'
        (by rw [hkp.get 21 (by decide)]; exact h21)
        (fun R'' h1 h2 => hn' R'' (h1.trans hkp) h2) (fun R'' h1 h2 => hf' R'' (h1.trans hkp) h2)
        _ 0 _ rfl (by omega) ?_ ?_ (fun j hj => absurd hj (Nat.not_lt_zero _))
        (by keeps_tac Keeps.refl _ _)
      · bsimp []
      · bsimp [Nat.add_comm]
  dx_run hlive at 0x80006c14
  all_goals bsimp [h26, h27, hl, hsc, hv]
  all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
  · intro hge
    rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hge
    refine tail _ ?_ (by bsimp [h26]) (by keeps_tac Keeps.refl _ _)
    bsimp [Nat.min_eq_right (show o.scale ≤ s by omega)]
  · intro hlt
    rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hlt
    dx_run hlive at 0x80006c14
    refine tail _ ?_ (by bsimp [h26]) (by keeps_tac Keeps.refl _ _)
    bsimp [h27, Nat.min_eq_left (show s ≤ o.scale by omega)]

end Dc.Mach
