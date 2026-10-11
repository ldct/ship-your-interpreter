import Dc.Mach.Bc.Init
import Dc.Mach.Stubs
import Dc.Mach.State

/-!
# `main`'s initialisation callees (M11)

```
80002a48 dc_math_init:     j bc_init_numbers
80003c74 dc_string_init:   ret
80003c78 dc_array_init:    ret
80002cd0 dc_register_init: auipc a5 ; addi a5 = dc_register ; auipc a4 ; addi a4 = __bss_end
80002ce0                   sd zero,0(a5) ; addi a5,a5,8 ; bne a5,a4,80002ce0 ; ret
```

`dc_math_init_spec` is `bc_init_numbers_spec` behind the tail jump; the two
empty initialisers are leaves (`dc_leaf`); `dc_register_init_spec` zeroes the
2048 bytes of `dc_register` (`Filled` with zero bytes, one doubleword per
pass of `reg_init_loop`, `Filled.snocW`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The doubleword of zero bytes. -/
theorem imgW_zero (a : Nat) : VsaIris.Interp.imgW (fun _ => 0#8) a = 0#64 := by
  simp [VsaIris.Interp.imgW, VsaIris.Interp.imgLE]

/-- One more zero doubleword stored at the end of a zero fill. -/
theorem Filled.snocW {Mt Mt0 : Mem} {d i : Nat} (h : Filled Mt Mt0 d i (fun _ => 0#8)) {A : Nat}
    (hA : A = d + i) : Filled (writeLog Mt [(A, 8, 0#64)]) Mt0 d (i + 8) (fun _ => 0#8) where
  fill j hj := by
    by_cases hji : i ≤ j
    · subst hA
      have := VsaIris.Interp.imgM_store_img (Mt := Mt) (a := d + i) (img := fun _ => 0#8)
        (j := j - i) (by omega)
      rw [imgW_zero, show d + i + (j - i) = d + j by omega] at this
      exact this
    · rw [imgM_store_miss _ _ (by omega)]; exact h.fill j (by omega)
  rest a ha := by rw [imgM_store_miss _ _ (by omega)]; exact h.rest a (by omega)

/-- **`dc_math_init ()`** at `0x80002a48`: the tail jump to `bc_init_numbers`. -/
theorem dc_math_init_spec {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} {F : List Blk} {L : List NumObj}
    (hb : BcHeap S X Mt H F L) {sp : Nat} {R : Nat → BitVec 64} (cx : InitCtx S R sp)
    (hk : InitK live S X Q R Mt L sp) :
    DW live S Q 0x80002a48#64 R Mt := by
  dx_run hlive at 0x80004948
  exact bc_init_numbers_spec hlive hb cx hk

section Leaves

variable {live : Nat → Prop} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
  (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)

include hlive hal

/-- **`dc_string_init ()`** at `0x80003c74`: nothing. -/
theorem dc_string_init_spec (hk : LeafRet live S Q R Mt [] fun _ => True) :
    DW live S Q 0x80003c74#64 R Mt := by dc_leaf hlive hk

/-- **`dc_array_init ()`** at `0x80003c78`: nothing. -/
theorem dc_array_init_spec (hk : LeafRet live S Q R Mt [] fun _ => True) :
    DW live S Q 0x80003c78#64 R Mt := by dc_leaf hlive hk

end Leaves

/-- `__bss_end` (`heapStart`), the end of `dc_register`. -/
theorem dcReg_end : dcRegAddr + 2048 = heapStart := rfl

/-- `dc_register_init`'s loop at `0x80002ce0` with `a5 = dc_register + i`
(`i` a multiple of 8 below 2048). -/
theorem reg_init_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hown : ∀ a, dcRegAddr ≤ a → a < dcRegAddr + 2048 → S a)
    (Mt0 : Mem) (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [14, 15] R' R0 → Filled Mt' Mt0 dcRegAddr 2048 (fun _ => 0#8) →
      DW live S Q (R0 1) R' Mt') :
    ∀ k i (R : Nat → BitVec 64) (Mt : Mem), 2048 - i = 8 * k → i < 2048 →
      R 15 = BitVec.ofNat 64 (dcRegAddr + i) → R 14 = BitVec.ofNat 64 heapStart →
      Keeps [14, 15] R R0 → Filled Mt Mt0 dcRegAddr i (fun _ => 0#8) →
      DW live S Q 0x80002ce0#64 R Mt := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k with
  | zero => intro i R Mt h1 h2; omega
  | succ k ih =>
    intro i R Mt hn hi h15 h14 hkeep hf
    have hi8 : i % 8 = 0 := by omega
    dx_run hlive
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, se12_zero,
      BitVec.add_zero, h15, h14, ofNat_add_ofNat]
    · simp only [BitVec.toNat_ofNat, StOK, dc_addrs]; omega
    · intro b hb
      have hb' := of_mem_accAddrs hb
      simp only [BitVec.toNat_ofNat] at hb'
      exact hown b (by simp only [dc_addrs] at hb' ⊢; omega) (by simp only [dc_addrs] at hb' ⊢; omega)
    · intro hne
      refine ih (i + 8) _ _ (by omega) ?_ ?_ ?_ ?_ ?_
      · refine Classical.byContradiction fun hge => hne ?_
        have : i + 8 = 2048 := by omega
        rw [Nat.add_assoc, this]
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15, ofNat_add_ofNat,
          Nat.add_assoc]
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h14]
      · keeps_tac hkeep
      · exact hf.snocW (by simp only [BitVec.toNat_ofNat, dc_addrs]; omega)
    · intro heq
      have hn' : i + 8 = 2048 := by
        refine Classical.byContradiction fun hne => heq ?_
        rw [ofNat_ne_iff (by simp only [dc_addrs]; omega) (by simp only [heapStart]; omega)]
        simp only [dc_addrs, heapStart]; omega
      dx_run hlive
      · simp only [upd_apply, Nat.reduceEqDiff, ite_false, hkeep.get 1, hal]
      · rw [hkeep.get 1]
        refine hk _ _ (by keeps_tac hkeep) ?_
        have e : (2048 : Nat) = i + 8 := by omega
        rw [e]
        exact hf.snocW (by simp only [BitVec.toNat_ofNat, dc_addrs]; omega)

/-- **`dc_register_init ()`** at `0x80002cd0`: the 256 register words zeroed;
`a4`/`a5` clobbered. -/
theorem dc_register_init_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hown : ∀ a, dcRegAddr ≤ a → a < dcRegAddr + 2048 → S a)
    (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [14, 15] R' R → Filled Mt' Mt dcRegAddr 2048 (fun _ => 0#8) →
      DW live S Q (R 1) R' Mt') :
    DW live S Q 0x80002cd0#64 R Mt := by
  dx_run hlive at 0x80002ce0
  refine reg_init_loop hlive hown Mt R hal hk 256 0 _ _ rfl (by omega) ?_ ?_
    (by keeps_tac Keeps.refl _ _) (Filled.zero Mt _ _)
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]

end Dc.Mach
