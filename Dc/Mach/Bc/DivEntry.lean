import Dc.Mach.Bc.DivBufs

/-!
# `bc_divide`'s entry checks (`0x8000589c` to `0x80005954`)

- `dvt_neg`: the `-1` return from `0x80005b3c` (division by zero).
- `dvz_scan`: `bc_is_zero (n2)` inlined at `0x80005914`.
- `dvz_trim`: the trailing-zero trim of `n2`'s scale at `0x80005948`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- The `-1` return's second half from `0x80005b5c`: `s7`–`s11` back, `ret`. -/
theorem dvt_neg2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr : NumObj} {n : Option Num}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = none)
    (sv : SavedWords M (sp - 208) divSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 208))
    (h1 : R 1 = R0 1) (h8 : R 8 = R0 8) (h9 : R 9 = R0 9) (h18 : R 18 = R0 18)
    (h19 : R 19 = R0 19) (h20 : R 20 = R0 20) (h21 : R 21 = R0 21) (h22 : R 22 = R0 22)
    (h10 : R 10 = 0xffffffffffffffff#64) (hkp : Keeps divAll R R0) (hS : HeapOwn S)
    (hfr : ∀ a, ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    DW live S Q 0x80005b5c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hal := cx.al
  have g23 := sv.get 23 136; have g24 := sv.get 24 128; have g25 := sv.get 25 120
  have g26 := sv.get 26 112; have g27 := sv.get 27 104
  bc_run hlive hS [h1, h2, g23, g24, g25, g26, g27]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk.zero hn _ _ (Keeps.unwind
    (saved := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp)) (by bsimp [h10]) hfr
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, h1, h8, h9, h18, h19, h20, h21, h22, g23, g24, g25, g26, g27]
  all_goals (try (congr 1; omega))

/-- **Division by zero** from `0x80005b3c` (`a0 = -1`): the epilogue and
`ret`, only the frame changed. -/
theorem dvt_neg {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr : NumObj} {n : Option Num}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = none)
    (sv : SavedWords M (sp - 208) divSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 208))
    (h10 : R 10 = 0xffffffffffffffff#64) (hkp : Keeps divAll R R0) (hS : HeapOwn S)
    (hfr : ∀ a, ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    DW live S Q 0x80005b3c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have g1 := sv.get 1 200; have g8 := sv.get 8 192; have g9 := sv.get 9 184
  have g18 := sv.get 18 176; have g19 := sv.get 19 168; have g20 := sv.get 20 160
  have g21 := sv.get 21 152; have g22 := sv.get 22 144
  bc_run hlive hS [h2, g1, g8, g9, g18, g19, g20, g21, g22] at 0x80005b5c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact dvt_neg2 hlive cx hk hn sv (by bsimp [h2]) (by bsimp [g1]) (by bsimp [g8])
    (by bsimp [g9]) (by bsimp [g18]) (by bsimp [g19]) (by bsimp [g20]) (by bsimp [g21])
    (by bsimp [g22]) (by bsimp [h10]) (by keeps_tac hkp) hS hfr

/-- **`n2`'s zero test** at `0x80005914` (`bc_is_zero` inlined): digits
`0 … i - 1` zero, `a3 = n - i`, `a4` at digit `i`; the first nonzero digit
`i0` ends it at `0x80005924`, all `n` zero at `0x80005e44`. -/
theorem dvz_scan {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {Rb : Nat → BitVec 64} (hS : HeapOwn S) {ds : List Nat} (hd : IsDigits ds)
    {v n : Nat} (hb : ∀ i, i < n → imgM M (v + i) = BitVec.ofNat 8 (ds.getD i 0)) (hn : n < 2 ^ 30)
    (hlo : 2147603920 ≤ v) (hhi : v + n ≤ 2273312768)
    (hfound : ∀ R' i0, i0 < n → ds.getD i0 0 ≠ 0 → (∀ j, j < i0 → ds.getD j 0 = 0) →
      Keeps [12, 13, 14] R' Rb → DW live S Q 0x80005924#64 R' M)
    (hnone : ∀ R', (∀ j, j < n → ds.getD j 0 = 0) → Keeps [12, 13, 14] R' Rb →
      DW live S Q 0x80005e44#64 R' M) :
    ∀ k i R, i + 1 + k = n → (∀ j, j < i → ds.getD j 0 = 0) → Keeps [12, 13, 14] R Rb →
      R 13 = BitVec.ofNat 64 (n - i) → R 14 = BitVec.ofNat 64 (v + i) →
      DW live S Q 0x80005914#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  refine count_rec fun k i R ih hi hz kk h13 h14 => ?_
  have hl := lbu_digit (hd.getD i) (hb i (by omega))
  have hdl := hd.getD i
  have e1 : BitVec.ofNat 64 (v + i) + 1#64 = BitVec.ofNat 64 (v + (i + 1)) := by
    rw [show (1#64) = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat]; congr 1
  have e2 := subw_ofNat_le (a := n - i) (b := 1) (by omega) (by omega)
  have hq := ofNat_eq_zero_iff (show ds.getD i 0 < 2 ^ 64 by omega)
  bc_run hlive hS [h13, h14, hl, e1, e2] at 0x80005924 0x80005910
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro h0
    replace h0 : ds.getD i 0 = 0 := hq.mp h0
    have hz' : ∀ j, j < i + 1 → ds.getD j 0 = 0 := fun j hj => by
      rcases Nat.lt_or_ge j i with h | h
      · exact hz j h
      · rw [show j = i by omega]; exact h0
    have e3 := ofNat_eq_zero_iff (show n - i - 1 < 2 ^ 64 by omega)
    bc_run hlive hS [e3] at 0x80005e44 0x80005914
    · intro h1
      exact hnone _ (fun j hj => hz' j (by omega)) (by keeps_tac kk)
    · intro h1
      rcases k with _ | k
      · omega
      exact ih k rfl _ (by omega) hz' (by keeps_tac kk) (by bsimp []; exact congrArg _ (by omega))
        (by bsimp [])
  · intro h0
    replace h0 : ds.getD i 0 ≠ 0 := fun e => h0 (hq.mpr e)
    exact hfound _ i (by omega) h0 hz (by keeps_tac kk)

/-- **`n2`'s trailing-zero trim** at `0x80005948` (`while (scale2 > 0 &&
*n2ptr-- == 0) scale2--`): `s3 = c = sc - i ≥ 1`, `a5` at digit `ln + c - 1`,
digits `ln + c … ln + sc - 1` zero; ends at `0x80005954` with `s3 = s2`, the
digits from `ln + s2` zero. -/
theorem dvz_trim {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {Rb : Nat → BitVec 64} (hS : HeapOwn S) {ds : List Nat} (hd : IsDigits ds)
    {v ln sc : Nat} (hb : ∀ j, j < ln + sc → imgM M (v + j) = BitVec.ofNat 8 (ds.getD j 0))
    (hn : ln + sc < 2 ^ 30) (hlo : 2147603920 ≤ v) (hhi : v + ln + sc ≤ 2273312768)
    (hdone : ∀ R' s2, s2 ≤ sc → (∀ j, s2 ≤ j → j < sc → ds.getD (ln + j) 0 = 0) →
      Keeps [14, 15, 19] R' Rb → R' 19 = BitVec.ofNat 64 s2 → DW live S Q 0x80005954#64 R' M) :
    ∀ k i R, i + 1 + k = sc → (∀ j, sc - i ≤ j → j < sc → ds.getD (ln + j) 0 = 0) →
      Keeps [14, 15, 19] R Rb → R 19 = BitVec.ofNat 64 (sc - i) →
      R 15 = BitVec.ofNat 64 (v + (ln + (sc - i) - 1)) → DW live S Q 0x80005948#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  refine count_rec fun k i R ih hi hz kk h19 h15 => ?_
  have hl := lbu_digit (hd.getD (ln + (sc - i) - 1)) (hb _ (by omega))
  have hdl := hd.getD (ln + (sc - i) - 1)
  have hq := ofNat_eq_zero_iff (show ds.getD (ln + (sc - i) - 1) 0 < 2 ^ 64 by omega)
  have e2 := sxw_ofNat (k := sc - i - 1) (by omega)
  bc_run hlive hS [h19, h15, hl] at 0x80005954 0x80005940
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro h0
    replace h0 : ds.getD (ln + (sc - i) - 1) 0 = 0 := hq.mp h0
    have hz' : ∀ j, sc - (i + 1) ≤ j → j < sc → ds.getD (ln + j) 0 = 0 := fun j hj1 hj2 => by
      rcases Nat.lt_or_ge j (sc - i) with h | h
      · rw [show ln + j = ln + (sc - i) - 1 by omega]; exact h0
      · exact hz j h hj2
    have e3 := ofNat_eq_zero_iff (show sc - i - 1 < 2 ^ 64 by omega)
    bc_run hlive hS [h19, e2, e3] at 0x80005954 0x80005948
    · intro h1
      bc_run hlive hS [] at 0x80005954
      exact hdone _ 0 (by omega) (fun j hj1 hj2 => hz' j (by omega) hj2) (by keeps_tac kk) (by bsimp [])
    · intro h1
      rcases k with _ | k
      · omega
      exact ih k rfl _ (by omega) hz' (by keeps_tac kk) (by bsimp []; exact congrArg _ (by omega))
        (by bsimp []; exact congrArg _ (by omega))
  · intro h0
    exact hdone _ (sc - i) (by omega) hz (by keeps_tac kk) (by bsimp [h19])

end

end Dc.Mach
