import Dc.Mach.Bc.Scratch
import Dc.Mach.Bc.SimpMul
import Dc.BcModel.DivLoop

/-!
# `_one_mult` (`lib/number.c`, `0x80003ebc`)

```
80003ebc beqz a2,80003f8c ; 80003ec0 li a5,1 ; 80003ec4 beq a2,a5,80003fa0
80003ec8 blez a1,80003f9c ; 80003ecc addi sp,sp,-64 ; 80003ed0 addiw a5,a1,-1
80003ed4 sd s5,8(sp) ; 80003ed8 slli s5,a5,0x20 ; 80003edc addi a1,a1,-1
80003ee0 srli s5,s5,0x20 ; 80003ee4 sd s1,40(sp) ; 80003ee8 sd s4,16(sp)
80003eec sd s6,0(sp) ; 80003ef0 add s1,a0,a1 ; 80003ef4 add s6,a3,a1
80003ef8 not s4,s5 ; 80003efc sd s0,48(sp) ; 80003f00 sd s2,32(sp)
80003f04 sd s3,24(sp) ; 80003f08 sd ra,56(sp) ; 80003f0c mv s3,a2
80003f10 add s4,s1,s4 ; 80003f14 mv s2,s6 ; 80003f18 li s0,0
80003f1c lbu a1,0(s1) ; 80003f20 mv a0,s3 ; 80003f24 addi s2,s2,-1
80003f28 jal __muldi3 ; 80003f2c addw s0,a0,s0 ; 80003f30 mv a0,s0
80003f34 li a1,10 ; 80003f38 jal __moddi3 ; 80003f3c sb a0,1(s2)
80003f40 li a1,10 ; 80003f44 mv a0,s0 ; 80003f48 addi s1,s1,-1
80003f4c jal __divdi3 ; 80003f50 sext.w s0,a0 ; 80003f54 bne s1,s4,80003f1c
80003f58 beqz s0,80003f64 ; 80003f5c sub a3,s6,s5 ; 80003f60 sb s0,-1(a3)
80003f64 ld ra,56(sp) … 80003f80 ld s6,0(sp) ; 80003f84 addi sp,sp,64 ; 80003f88 ret
80003f8c mv a2,a1 ; 80003f90 mv a0,a3 ; 80003f94 li a1,0 ; 80003f98 j memset
80003f9c ret
80003fa0 mv a2,a1 ; 80003fa4 mv a1,a0 ; 80003fa8 mv a0,a3 ; 80003fac j memcpy
```

`_one_mult(num, size, digit, result)` stores the `size` low digits of
`num · digit` at `result` (from the last digit, so `result = num` works in
place) and a nonzero carry at `result - 1`; `digit = 0` is a `memset`,
`digit = 1` a `memcpy`.

- `OmArgs`: the `n` digits `xs` at `p`, the result at `r`, both in the heap.
- `OmPost`: digit `i` of `P = dvalBE xs · d` at `r + i`; the carry.
- `one_mult_spec`: the contract.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- `_one_mult`'s fixed context: the 64-byte frame above the heap. -/
structure OmCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp : Nat) : Prop where
  frame : StackFrame S sp 64
  above : heapEnd + 64 ≤ sp
  heap : HeapOwn S
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0

/-- The operands: the digits `xs` at `p`, the digit `d`, the result at
`r` (the carry at `r - 1`), in place (`r = p`, then `d ≠ 1`) or apart. -/
structure OmArgs (M : Mem) (p n d r : Nat) (xs : List Nat) : Prop where
  len : xs.length = n
  dig : IsDigits xs
  bytes : ∀ i, i < n → imgM M (p + i) = BitVec.ofNat 8 (xs.getD i 0)
  d10 : d < 10
  n31 : n < 2 ^ 31
  plo : heapStart ≤ p
  phi : p + n ≤ heapEnd
  rlo : heapStart + 1 ≤ r
  rhi : r + n ≤ heapEnd
  ov : r = p ∨ p + n + 1 ≤ r ∨ r + n ≤ p
  cp : d = 1 → r ≠ p

/-- The result for the product `P`: its `n` low digits at `r`, a nonzero
carry at `r - 1`, nothing else changed off the stack frame. -/
structure OmPost (M' M : Mem) (sp r n P : Nat) : Prop where
  digits : ∀ i, i < n → imgM M' (r + i) = BitVec.ofNat 8 (P / 10 ^ (n - 1 - i) % 10)
  carry : P / 10 ^ n ≠ 0 → imgM M' (r - 1) = BitVec.ofNat 8 (P / 10 ^ n)
  keep : P / 10 ^ n = 0 → imgM M' (r - 1) = imgM M (r - 1)
  rest : ∀ a, (a + 1 < r ∨ r + n ≤ a) → ¬ frameIn sp 64 a → imgM M' a = imgM M a

/-- The continuation. -/
abbrev OmK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (M0 : Mem) (sp r n P : Nat) : Prop :=
  ∀ R' M', Keeps binClob R' R0 → OmPost M' M0 sp r n P → DW live S Q (R0 1) R' M'

/-- The prologue's saved registers. -/
abbrev omSlots : List (Nat × Nat) :=
  [(1, 56), (19, 24), (18, 32), (8, 48), (22, 0), (20, 16), (9, 40), (21, 8)]

/-- The registers `_one_mult` changes before its epilogue. -/
abbrev omAll : List Nat :=
  [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 28, 29, 30, 31]

/-- The loop's state at `0x80003f1c` after the last `k` digits: carry `c`. -/
structure OmAt (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp p r n d k c P : Nat)
    (xs : List Nat) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 64)
  r8 : R 8 = BitVec.ofNat 64 c
  r9 : R 9 = BitVec.ofNat 64 (p + n - 1 - k)
  r18 : R 18 = BitVec.ofNat 64 (r + n - 1 - k)
  r19 : R 19 = BitVec.ofNat 64 d
  r20 : R 20 = BitVec.ofNat 64 (p - 1)
  r21 : R 21 = BitVec.ofNat 64 (n - 1)
  r22 : R 22 = BitVec.ofNat 64 (r + n - 1)
  regs : Keeps omAll R R0
  saved : SavedWords M (sp - 64) omSlots R0
  kn : k ≤ n
  n1 : 1 ≤ n
  digits : ∀ i, n - k ≤ i → i < n → imgM M (r + i) = BitVec.ofNat 8 (P / 10 ^ (n - 1 - i) % 10)
  rest : ∀ a, (a < r + n - k ∨ r + n ≤ a) → ¬ frameIn sp 64 a → imgM M a = imgM M0 a
  carry : c = dvalBE (xs.drop (n - k)) * d / 10 ^ k

/-- The epilogue at `0x80003f64`. -/
theorem om_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp r n P : Nat}
    (cx : OmCtx S R0 sp) (hk : OmK live S Q R0 M0 sp r n P)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 64)) (sv : SavedWords M (sp - 64) omSlots R0)
    (hkp : Keeps omAll R R0) (hp : OmPost M M0 sp r n P) :
    DW live S Q 0x80003f64#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS := cx.heap
  have e1 := sv.get 1 56; have e8 := sv.get 8 48; have e9 := sv.get 9 40
  have e18 := sv.get 18 32; have e19 := sv.get 19 24; have e20 := sv.get 20 16
  have e21 := sv.get 21 8; have e22 := sv.get 22 0
  have hal := cx.al
  bc_run hlive hS [h2, e1, e8, e9, e18, e19, e20, e21, e22]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ _ (Keeps.unwind (saved := [1, 2, 8, 9, 18, 19, 20, 21, 22])
    ?_ (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp)) hp
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, e1, e8, e9, e18, e19, e20, e21, e22]
  all_goals (congr 1 <;> omega)

/-- After the loop, at `0x80003f58`: a nonzero carry stored at `r - 1`. -/
theorem om_fin {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp p r n d c : Nat} {xs : List Nat}
    (cx : OmCtx S R0 sp) (ha : OmArgs M0 p n d r xs)
    (hk : OmK live S Q R0 M0 sp r n (dvalBE xs * d))
    (st : OmAt M0 M R0 R sp p r n d n c (dvalBE xs * d) xs) :
    DW live S Q 0x80003f58#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS := cx.heap
  have hrl := ha.rlo; have hrh := ha.rhi; have hn := ha.n31; have hn1 := st.n1
  simp only [heapStart, heapEnd] at hab hrl hrh
  have hc : c = dvalBE xs * d / 10 ^ n := by
    have := st.carry; rwa [Nat.sub_self, List.drop_zero] at this
  have hc10 : c < 10 := by
    rw [hc]
    have hx := dvalBE_lt ha.dig
    rw [ha.len] at hx
    refine (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr ?_
    calc dvalBE xs * d < 10 ^ n * 10 := by
          rcases Nat.eq_zero_or_pos d with h | h
          · rw [h, Nat.mul_zero]; exact Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)
          · exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hx h)
              (Nat.mul_le_mul_left _ (by have := ha.d10; omega))
      _ = 10 * 10 ^ n := Nat.mul_comm _ _
  have hdig : ∀ i, i < n → imgM M (r + i) = BitVec.ofNat 8 (dvalBE xs * d / 10 ^ (n - 1 - i) % 10) :=
    fun i hi => st.digits i (by omega) hi
  have hfr : ∀ a, ¬ frameIn sp 64 a ↔ ¬ (sp - 64 ≤ a ∧ a < sp) := fun a => Iff.rfl
  bc_run hlive hS [st.r8, st.r22, st.r21] at 0x80003f64
  · intro h0
    have hc0 : c = 0 := ofNat64_eq (by omega) (by omega) (by rw [h0])
    exact om_epi hlive cx hk st.r2 st.saved st.regs
      ⟨hdig, fun h => absurd (hc ▸ hc0) h, fun _ => st.rest _ (.inl (by omega))
        (by simp only [frameIn]; omega),
       fun a ha' hf => st.rest a (by omega) hf⟩
  · intro h0
    have hc0 : c ≠ 0 := fun e => h0 (by rw [e])
    have hsub : BitVec.ofNat 64 (r + n - 1) - BitVec.ofNat 64 (n - 1) = BitVec.ofNat 64 r := by
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]; congr 1; omega
    bc_run hlive hS [st.r8, st.r22, st.r21, hsub, word_pred (show 1 ≤ r by omega)] at 0x80003f64
    all_goals first | exact acc_heap hS (by omega) (by omega) | skip
    have hm : ∀ a, a ≠ r - 1 → imgM (writeLog M [(r - 1, 1, BitVec.ofNat 64 c)]) a = imgM M a :=
      fun a ha => imgM_store_miss _ _ (by omega)
    refine om_epi hlive cx hk (by bsimp [st.r2])
      (st.saved.transport (lo := 0) (top := 64) (hag := fun a h1 h2 => hm a (by omega)))
      (by keeps_tac st.regs)
      ⟨fun i hi => (hm _ (by omega)).trans (hdig i hi), fun _ => ?_, fun h => absurd (hc ▸ h) hc0,
        fun a ha' hf => (hm a (by omega)).trans (st.rest a (by omega) hf)⟩
    rw [imgM_sb, sbData_ofNat, ← hc]

/-- One digit stored: the state after `k + 1` digits. -/
theorem OmAt.step {M0 M : Mem} {R0 Rk R' : Nat → BitVec 64} {sp p r n d k c A : Nat}
    {xs : List Nat} (st : OmAt M0 M R0 Rk sp p r n d k c (dvalBE xs * d) xs)
    (ha : OmArgs M0 p n d r xs) (hkn : k < n) (hA : A = r + n - 1 - k)
    (hkk : Keeps omAll R' Rk) (h2 : R' 2 = BitVec.ofNat 64 (sp - 64))
    (h8 : R' 8 = BitVec.ofNat 64 ((xs.getD (n - 1 - k) 0 * d + c) / 10))
    (h9 : R' 9 = BitVec.ofNat 64 (p + n - 1 - (k + 1)))
    (h18 : R' 18 = BitVec.ofNat 64 (r + n - 1 - (k + 1)))
    (h19 : R' 19 = BitVec.ofNat 64 d) (h20 : R' 20 = BitVec.ofNat 64 (p - 1))
    (h21 : R' 21 = BitVec.ofNat 64 (n - 1)) (h22 : R' 22 = BitVec.ofNat 64 (r + n - 1))
    (hsp : heapEnd + 64 ≤ sp) :
    OmAt M0 (writeLog M [(A, 1, BitVec.ofNat 64 ((xs.getD (n - 1 - k) 0 * d + c) % 10))]) R0 R'
      sp p r n d (k + 1) ((xs.getD (n - 1 - k) 0 * d + c) / 10) (dvalBE xs * d) xs := by
  obtain ⟨hdig, hcar⟩ := oneMult_step (d := d) ha.len hkn
  have hc := st.carry
  have hrh := ha.rhi
  simp only [heapEnd] at hsp hrh
  have hm : ∀ a, a ≠ A → imgM (writeLog M [(A, 1, BitVec.ofNat 64
      ((xs.getD (n - 1 - k) 0 * d + c) % 10))]) a = imgM M a :=
    fun a ha' => imgM_store_miss _ _ (by omega)
  refine ⟨h2, h8, h9, h18, h19, h20, h21, h22, hkk.trans st.regs, ?_, by omega, st.n1, ?_, ?_, ?_⟩
  · exact st.saved.transport (lo := 0) (top := 64) (hag := fun a h1 h2 => hm a (by omega))
  · intro i hi1 hi2
    by_cases hi : i = n - 1 - k
    · subst hi
      rw [show r + (n - 1 - k) = A by omega, imgM_sb, sbData_ofNat,
        show n - 1 - (n - 1 - k) = k by omega, hdig, ← hc]
    · rw [hm _ (by omega)]
      exact st.digits i (by omega) hi2
  · intro a ha' hf
    rw [hm a (by omega)]
    exact st.rest a (by omega) hf
  · rw [hcar, ← hc]

/-- The digit store and carry from `0x80003f2c` (`a0 = x · d` for the next
digit `x`), on to the next digit or the carry store. -/
theorem om_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 Rk R : Nat → BitVec 64} {sp p r n d k c : Nat} {xs : List Nat}
    (cx : OmCtx S R0 sp) (ha : OmArgs M0 p n d r xs)
    (hk : OmK live S Q R0 M0 sp r n (dvalBE xs * d))
    (st : OmAt M0 M R0 Rk sp p r n d k c (dvalBE xs * d) xs) (hkn : k < n)
    (hkk : Keeps [1, 10, 11, 12, 13, 18] R Rk)
    (h18 : R 18 = BitVec.ofNat 64 (r + n - 1 - k - 1))
    (h10 : R 10 = BitVec.ofNat 64 (xs.getD (n - 1 - k) 0 * d))
    (hnext : ∀ R' M' c', k + 1 < n →
      OmAt M0 M' R0 R' sp p r n d (k + 1) c' (dvalBE xs * d) xs → DW live S Q 0x80003f1c#64 R' M') :
    DW live S Q 0x80003f2c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS := cx.heap
  have hrl := ha.rlo; have hrh := ha.rhi; have hn := ha.n31; have hd := ha.d10
  have hpl := ha.plo; have hph := ha.phi
  simp only [heapStart, heapEnd] at hab hrl hrh hpl hph
  obtain ⟨hdig, hcar⟩ := oneMult_step (d := d) ha.len hkn
  have hx : xs.getD (n - 1 - k) 0 < 10 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [ha.len]; omega),
      Option.getD_some]
    exact ha.dig _ (List.getElem_mem _)
  have hc10 : c < 10 := by
    have e := st.carry
    have hsl' := dvalBE_lt (ds := xs.drop (n - k)) (fun e he => ha.dig e (List.mem_of_mem_drop he))
    rw [List.length_drop, ha.len, show n - (n - k) = k by omega] at hsl'
    rw [e]
    refine (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr ?_
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.mul_zero]; exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    · calc dvalBE (xs.drop (n - k)) * d < 10 ^ k * d := Nat.mul_lt_mul_of_pos_right hsl' h
        _ ≤ 10 ^ k * 10 := Nat.mul_le_mul_left _ (by omega)
        _ = 10 * 10 ^ k := Nat.mul_comm _ _
  have hxd : xs.getD (n - 1 - k) 0 * d ≤ 9 * 9 :=
    Nat.mul_le_mul (show _ ≤ 9 by omega) (show d ≤ 9 by omega)
  have e8 : R 8 = BitVec.ofNat 64 c := by rw [hkk.get 8]; exact st.r8
  have e9 : R 9 = BitVec.ofNat 64 (p + n - 1 - k) := by rw [hkk.get 9]; exact st.r9
  bc_run hlive hS [h10, e8, addw_ofNat (show xs.getD (n - 1 - k) 0 * d + c < 2 ^ 31 by omega)]
    at 0x80003f38
  apply st_80003f38 hlive
  refine moddi3_spec hlive _ (by bsimp []) fun R1 hk1 hr1 => ?_
  bsimp [] at hr1 ⊢
  rw [srem10_small (by omega)] at hr1
  have q8 : R1 8 = BitVec.ofNat 64 (xs.getD (n - 1 - k) 0 * d + c) := by
    rw [hk1.get 8]; bsimp []
  have q18 : R1 18 = BitVec.ofNat 64 (r + n - 1 - k - 1) := by rw [hk1.get 18]; bsimp [h18]
  have q9 : R1 9 = BitVec.ofNat 64 (p + n - 1 - k) := by rw [hk1.get 9]; bsimp [e9]
  bc_run hlive hS [hr1, q8, q18, q9] at 0x80003f4c
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  apply st_80003f4c hlive
  refine divdi3_spec hlive _ (by bsimp []) fun R2 hk2 hr2 => ?_
  bsimp [] at hr2 ⊢
  rw [sdiv10_small (by omega)] at hr2
  have K : Keeps [1, 5, 8, 9, 10, 11, 12, 13, 18] R2 Rk :=
    ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _)))).trans (hkk.mono (by decide))
  have r9 : R2 9 = BitVec.ofNat 64 (p + n - 1 - (k + 1)) := by
    rw [hk2.get 9]; bsimp [q9, word_pred (show 1 ≤ p + n - 1 - k by omega)]
    congr 1 <;> omega
  have r18 : R2 18 = BitVec.ofNat 64 (r + n - 1 - (k + 1)) := by
    rw [hk2.get 18]; bsimp [q18]
    congr 1 <;> omega
  have e20 : R2 20 = BitVec.ofNat 64 (p - 1) := (K.get 20).trans st.r20
  bc_run hlive hS [hr2, r9, e20] at 0x80003f1c 0x80003f58
  · intro hne
    have hk2' : k + 1 < n := by
      refine Classical.byContradiction fun hc => hne ?_
      congr 1; omega
    exact hnext _ _ _ hk2' (st.step ha hkn (by omega) (by keeps_tac (K.mono (by decide)))
      (by bsimp [K.get 2, st.r2]) (by bsimp []) (by bsimp [r9]) (by bsimp [r18])
      (by bsimp [K.get 19, st.r19]) (by bsimp [e20]) (by bsimp [K.get 21, st.r21])
      (by bsimp [K.get 22, st.r22]) cx.above)
  · intro heq
    have hkn' : k + 1 = n := by
      have := ofNat64_eq (by omega) (by omega) (Classical.not_not.mp heq)
      omega
    subst hkn'
    exact om_fin hlive cx ha hk (st.step ha hkn (by omega) (by keeps_tac (K.mono (by decide)))
      (by bsimp [K.get 2, st.r2]) (by bsimp []) (by bsimp [r9]) (by bsimp [r18])
      (by bsimp [K.get 19, st.r19]) (by bsimp [e20]) (by bsimp [K.get 21, st.r21])
      (by bsimp [K.get 22, st.r22]) cx.above)

/-- A digit byte loaded with `lbu`. -/
theorem lbu_digit {M : Mem} {a x : Nat} (hx : x < 10) (h : imgM M a = BitVec.ofNat 8 x) :
    ldv .lbu M a = BitVec.ofNat 64 x := by
  rw [ldv_lbu, h]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_zext8, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- **The digit loop** from `0x80003f1c`, by the number of digits left. -/
theorem om_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 : Mem} {R0 : Nat → BitVec 64} {sp p r n d : Nat} {xs : List Nat}
    (cx : OmCtx S R0 sp) (ha : OmArgs M0 p n d r xs)
    (hk : OmK live S Q R0 M0 sp r n (dvalBE xs * d)) :
    ∀ m k c (R : Nat → BitVec 64) (M : Mem), n - k = m → k < n →
      OmAt M0 M R0 R sp p r n d k c (dvalBE xs * d) xs → DW live S Q 0x80003f1c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS := cx.heap
  have hrl := ha.rlo; have hrh := ha.rhi; have hn := ha.n31; have hd := ha.d10
  have hpl := ha.plo; have hph := ha.phi; have hov := ha.ov
  simp only [heapStart, heapEnd] at hab hrl hrh hpl hph
  intro m
  induction m with
  | zero => intro k c R M h1 h2; omega
  | succ m ih =>
    intro k c R M hm hkn st
    have hx : xs.getD (n - 1 - k) 0 < 10 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [ha.len]; omega),
        Option.getD_some]
      exact ha.dig _ (List.getElem_mem _)
    have hb : imgM M (p + (n - 1 - k)) = BitVec.ofNat 8 (xs.getD (n - 1 - k) 0) := by
      rw [st.rest _ (by omega) (by simp only [frameIn]; omega)]
      exact ha.bytes _ (by omega)
    have hl := lbu_digit hx hb
    rw [show p + (n - 1 - k) = p + n - 1 - k by omega] at hl
    have h9 := st.r9; have h19 := st.r19; have h18 := st.r18
    bc_run hlive hS [h9, hl, h19, h18] at 0x80003f28
    all_goals first | exact acc_heap hS (by omega) (by omega) | skip
    apply st_80003f28 hlive
    refine muldi3_spec hlive _ (by bsimp []) fun R1 hk1 hr1 => ?_
    bsimp [] at hr1 ⊢
    rw [mul_ofNat, Nat.mul_comm] at hr1
    exact om_tail hlive cx ha hk st hkn
      (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (by rw [hk1.get 18]; bsimp [h18]) hr1
      fun R' M' c' h st' => ih (k + 1) c' R' M' (by omega) h st'

/-- The prologue from `0x80003ecc` (`n ≥ 1`, `d ≥ 2`) into the loop. -/
theorem om_pro {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 : Mem} {R0 : Nat → BitVec 64} {sp p r n d : Nat} {xs : List Nat}
    (cx : OmCtx S R0 sp) (ha : OmArgs M0 p n d r xs)
    (hk : OmK live S Q R0 M0 sp r n (dvalBE xs * d)) (hn1 : 1 ≤ n) {R : Nat → BitVec 64}
    (hkR : Keeps [15] R R0)
    (h10 : R 10 = BitVec.ofNat 64 p) (h11 : R 11 = BitVec.ofNat 64 n)
    (h12 : R 12 = BitVec.ofNat 64 d) (h13 : R 13 = BitVec.ofNat 64 r) :
    DW live S Q 0x80003ecc#64 R M0 := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS := cx.heap
  have hrl := ha.rlo; have hrh := ha.rhi; have hn := ha.n31; have hd := ha.d10
  have hpl := ha.plo; have hph := ha.phi
  simp only [heapStart, heapEnd] at hab hrl hrh hpl hph
  have h2 : R 2 = BitVec.ofNat 64 sp := (hkR.get 2).trans cx.sp0
  have k1 := hkR.get 1; have k8 := hkR.get 8; have k9 := hkR.get 9; have k18 := hkR.get 18
  have k19 := hkR.get 19; have k20 := hkR.get 20; have k21 := hkR.get 21; have k22 := hkR.get 22
  have sv := (((((((SavedWords.nil M0 (sp - 64) R0).store 21 8).store 9 40).store 20 16).store 22 0
    ).store 8 48).store 18 32).store 19 24 |>.store 1 56
  have hnot := add_not_ofNat (A := p + (n - 1)) (B := n - 1) (by omega) (by omega)
  bc_run hlive hS [h2, h10, h11, h12, h13, k1, k8, k9, k18, k19, k20, k21, k22, word_sub64 (show 64 ≤ sp by omega), word_pred hn1,
    sxw_ofNat (show n - 1 < 2 ^ 31 by omega), shl_shr32 (show n - 1 < 2 ^ 32 by omega),
    ofNat_add_ofNat, hnot] at 0x80003f1c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine om_loop hlive cx ha hk n 0 0 _ _ (by omega) (by omega)
    ⟨by bsimp [], by bsimp [], by bsimp []; congr 1; omega, by bsimp []; congr 1; omega,
      by bsimp [], by bsimp [hnot]; congr 1; omega, by bsimp [], by bsimp []; congr 1; omega,
      by keeps_tac (hkR.mono (by decide)), sv, by omega, hn1, fun i h1 h2 => by omega, ?_, ?_⟩
  · intro a _ hf
    simp only [frameIn] at hf
    repeat rw [imgM_store_miss _ _ (by omega)]
  · rw [Nat.sub_zero, List.drop_of_length_le (by rw [ha.len]; exact Nat.le_refl _), dvalBE_nil,
      Nat.zero_mul, Nat.zero_div]

/-- **`_one_mult(num, size, digit, result)`** at `0x80003ebc`: the `n` low
digits of `dvalBE xs · d` at `r` and a nonzero carry at `r - 1` (`OmPost`),
`a0`–`a7` and the temporaries clobbered. -/
theorem one_mult_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 : Mem} {R0 : Nat → BitVec 64} {sp p r n d : Nat} {xs : List Nat}
    (cx : OmCtx S R0 sp) (ha : OmArgs M0 p n d r xs)
    (h10 : R0 10 = BitVec.ofNat 64 p) (h11 : R0 11 = BitVec.ofNat 64 n)
    (h12 : R0 12 = BitVec.ofNat 64 d) (h13 : R0 13 = BitVec.ofNat 64 r)
    (hk : OmK live S Q R0 M0 sp r n (dvalBE xs * d)) :
    DW live S Q 0x80003ebc#64 R0 M0 := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS := cx.heap
  have hal := cx.al
  have hrl := ha.rlo; have hrh := ha.rhi; have hn := ha.n31; have hd := ha.d10
  have hpl := ha.plo; have hph := ha.phi
  simp only [heapStart, heapEnd] at hrl hrh hpl hph
  have hX := dvalBE_lt ha.dig
  rw [ha.len] at hX
  have hown : ∀ a w, 2147603920 ≤ a → a + w ≤ 2273312768 → OwnedBytes S a w :=
    fun a w h1 h2 => ⟨fun i hi => hS _ (by simp only [heapStart]; omega)
      (by simp only [heapEnd]; omega), by omega, by omega⟩
  bc_run hlive hS [h12] at 0x80003ec4 0x80003f8c
  · -- `digit = 0`: `memset(result, 0, size)`
    intro h0
    have hd0 : d = 0 := ofNat64_eq (by omega) (by omega) (by rw [h0])
    subst hd0
    bc_run hlive hS [h11, h13] at 0x80000890
    refine memset_spec hlive (hown r n (by omega) (by omega)) _ (by bsimp []) (by bsimp [])
      (by bsimp [hal]) fun R' M' hk1 hf => ?_
    bsimp [] at hf ⊢
    refine hk R' M' (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      ⟨fun i hi => ?_, fun h => absurd (by rw [Nat.mul_zero, Nat.zero_div]) h,
        fun _ => hf.rest _ (.inl (by omega)), fun a ha' _ => hf.rest a (by omega)⟩
    rw [hf.fill i hi, Nat.mul_zero, Nat.zero_div, Nat.zero_mod]; rfl
  · intro hne
    have hd0 : d ≠ 0 := fun e => hne (by rw [e])
    bc_run hlive hS [h12] at 0x80003fa0 0x80003ec8
    · -- `digit = 1`: `memcpy(result, num, size)`
      intro h1
      have hd1 : d = 1 := ofNat64_eq (by omega) (by omega) (by rw [h1])
      subst hd1
      have hrp := ha.cp rfl
      have hdis : p + n ≤ r ∨ r + n ≤ p := by have := ha.ov; omega
      bc_run hlive hS [h10, h11, h13] at 0x8000086c
      refine memcpy_spec hlive ⟨hown r n (by omega) (by omega), hown p n (by omega) (by omega), hdis⟩
        _ (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [hal]) fun R' M' hk1 hf => ?_
      bsimp [] at hf ⊢
      rw [Nat.mul_one] at hk
      have hc : dvalBE xs / 10 ^ n = 0 := Nat.div_eq_of_lt hX
      refine hk R' M' (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
        ⟨fun i hi => ?_, fun h => absurd hc h, fun _ => hf.rest _ (.inl (by omega)),
          fun a ha' _ => hf.rest a (by omega)⟩
      rw [hf.fill i hi, ha.bytes i hi, ← ha.len, dvalBE_digit ha.dig (by rw [ha.len]; exact hi)]
    · intro hne1
      have hd1 : d ≠ 1 := fun e => hne1 (by rw [e])
      bc_run hlive hS [h11] at 0x80003ecc
      · intro hle
        have hn0 : n = 0 := by
          (try simp (disch := omega) only [toInt_ofNat_small] at hle); omega
        subst hn0
        have hx0 : xs = [] := List.eq_nil_of_length_eq_zero ha.len
        subst hx0
        bc_run hlive hS []
        exact hk _ _ (by keeps_tac Keeps.refl _ _) ⟨fun i hi => absurd hi (Nat.not_lt_zero _),
          fun h => absurd (by rw [dvalBE_nil, Nat.zero_mul, Nat.zero_div]) h, fun _ => rfl,
          fun _ _ _ => rfl⟩
      · intro hgt
        have hn1 : 1 ≤ n := by
          (try simp (disch := omega) only [toInt_ofNat_small] at hgt); omega
        exact om_pro hlive cx ha hk hn1 (by keeps_tac Keeps.refl _ _) (by bsimp [h10])
          (by bsimp [h11]) (by bsimp [h12]) (by bsimp [h13])

end Dc.Mach
