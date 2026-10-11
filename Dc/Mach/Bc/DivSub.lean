import Dc.Mach.Bc.OneMult
import Dc.Mach.Bc.DoSub
import Dc.BcModel.DivStep

/-!
# `bc_divide`'s subtract and add-back loops

```
80005de8 lbu a5,0(a1) ; 80005dec lbu a4,0(a3) ; 80005df0 addi a3,a3,-1
80005df4 addi a1,a1,-1 ; 80005df8 subw a5,a5,a4 ; 80005dfc subw a5,a5,a0
80005e00 li a0,0 ; 80005e04 bgez a5,80005e10 ; 80005e08 addiw a5,a5,10
80005e0c li a0,1 ; 80005e10 sb a5,1(a1) ; 80005e14 bne a7,a3,80005de8

80005f14 lbu a4,0(a2) ; 80005f18 lbu a5,0(a3) ; 80005f1c addi a3,a3,-1
80005f20 addi a2,a2,-1 ; 80005f24 addw a5,a5,a4 ; 80005f28 addw a5,a5,a1
80005f2c li a1,0 ; 80005f30 bgeu a7,a5,80005f3c ; 80005f34 addiw a5,a5,-10
80005f38 mv a1,a0 ; 80005f3c sb a5,1(a2) ; 80005f40 bne a3,t1,80005f14
```

The window of `L + 1` digits at `A` (big-endian; position `j` from the
bottom at `A + L - j`):

- `dsub_loop`: minus the product's `L + 1` digits at `B`, with borrow
  (`subLE`), the final borrow in `a0`;
- `dadd_loop`: plus the divisor's `L` digits at `N`, with carry (`addLE`)
  over the low `L` positions, the final carry in `a1`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

theorem borrowAt_full : ∀ (xs ys : List Nat) (b : Nat), xs.length = ys.length →
    borrowAt xs ys b xs.length = subBorrow xs ys b
  | [], [], b, _ => by simp [borrowAt, subBorrow]
  | x :: xs, y :: ys, b, h => by
    simp only [List.length_cons, borrowAt, subBorrow]
    split <;> exact borrowAt_full xs ys _ (by simpa using h)
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-! ## The subtract loop -/

/-- The window `w` at `A` and the product `m` at `B` (little-endian, `L + 1`
digits each, position `j` at `A + L - j`, `B + L - j`), apart, in the heap. -/
structure DsArgs (M : Mem) (A B L : Nat) (w m : List Nat) : Prop where
  wl : w.length = L + 1
  ml : m.length = L + 1
  wd : IsDigits w
  md : IsDigits m
  wb : ∀ j, j ≤ L → imgM M (A + L - j) = BitVec.ofNat 8 (w.getD j 0)
  mb : ∀ j, j ≤ L → imgM M (B + L - j) = BitVec.ofNat 8 (m.getD j 0)
  alo : 2147603920 ≤ A
  ahi : A + L < 2273312768
  blo : 2147603920 ≤ B
  bhi : B + L < 2273312768
  apart : A + L < B ∨ B + L < A

/-- The subtract loop at `0x80005de8` after `j` positions. -/
structure DsAt (M0 M : Mem) (R0 R : Nat → BitVec 64) (A B L j : Nat) (w m : List Nat) : Prop where
  r11 : R 11 = BitVec.ofNat 64 (A + L - j)
  r13 : R 13 = BitVec.ofNat 64 (B + L - j)
  r10 : R 10 = BitVec.ofNat 64 (borrowAt w m 0 j)
  r17 : R 17 = BitVec.ofNat 64 (B - 1)
  regs : Keeps [10, 11, 13, 14, 15] R R0
  jl : j ≤ L
  done : ∀ i, i < j → imgM M (A + L - i) = BitVec.ofNat 8 ((subLE w m 0).getD i 0)
  only : MemOnly (fun a => A + L - j < a ∧ a ≤ A + L) M M0

/-- The subtraction's result at `0x80005e18`. -/
structure DsPost (M0 M : Mem) (R0 R : Nat → BitVec 64) (A L : Nat) (w m : List Nat) : Prop where
  r10 : R 10 = BitVec.ofNat 64 (subBorrow w m 0)
  regs : Keeps [10, 11, 13, 14, 15] R R0
  done : ∀ i, i ≤ L → imgM M (A + L - i) = BitVec.ofNat 8 ((subLE w m 0).getD i 0)
  only : MemOnly (fun a => A ≤ a ∧ a ≤ A + L) M M0

/-- The store at `0x80005e10` of position `j` (the word `v` in `a5`). -/
theorem dsub_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M0 M : Mem} {R0 R : Nat → BitVec 64} {A B L j : Nat} {w m : List Nat}
    {v : BitVec 64}
    (ha : DsArgs M0 A B L w m) (hj : j ≤ L)
    (hdone : ∀ i, i < j → imgM M (A + L - i) = BitVec.ofNat 8 ((subLE w m 0).getD i 0))
    (honly : MemOnly (fun a => A + L - j < a ∧ a ≤ A + L) M M0)
    (hk : Keeps [10, 11, 13, 14, 15] R R0) (h15 : R 15 = v)
    (hv : sbData v = BitVec.ofNat 8 ((subLE w m 0).getD j 0))
    (h11 : R 11 = BitVec.ofNat 64 (A + L - j - 1)) (h13 : R 13 = BitVec.ofNat 64 (B + L - j - 1))
    (h10 : R 10 = BitVec.ofNat 64 (borrowAt w m 0 (j + 1))) (h17 : R 17 = BitVec.ofNat 64 (B - 1))
    (hnext : j + 1 ≤ L → ∀ R' M', DsAt M0 M' R0 R' A B L (j + 1) w m →
      DW live S Q 0x80005de8#64 R' M')
    (hexit : ∀ R' M', DsPost M0 M' R0 R' A L w m → DW live S Q 0x80005e18#64 R' M') :
    DW live S Q 0x80005e10#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have a1 := ha.alo; have a2 := ha.ahi; have b1 := ha.blo; have b2 := ha.bhi
  have hw := ha.wl
  have hM : ∀ a, a ≠ A + L - j → imgM (writeLog M [(A + L - j, 1, v)]) a = imgM M a :=
    fun a h => imgM_store_miss _ _ (by omega)
  have done' : ∀ i, i < j + 1 → imgM (writeLog M [(A + L - j, 1, v)]) (A + L - i) =
      BitVec.ofNat 8 ((subLE w m 0).getD i 0) := by
    intro i hi
    by_cases e : i = j
    · subst e; rw [imgM_sb, hv]
    · rw [hM _ (by omega)]; exact hdone i (by omega)
  have only' : MemOnly (fun a => A + L - (j + 1) < a ∧ a ≤ A + L)
      (writeLog M [(A + L - j, 1, v)]) M0 := fun a h =>
    (hM a (fun e => h ⟨by omega, by omega⟩)).trans (honly a fun h' => h ⟨by omega, h'.2⟩)
  bc_run hlive hS [h15, h11, h13, h17] at 0x80005de8 0x80005e18
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  all_goals rw [show A + L - j - 1 + 1 = A + L - j by omega]
  · intro hne
    have hj' : j + 1 ≤ L := by
      refine Nat.lt_of_le_of_ne hj fun e => hne ?_
      congr 1; omega
    exact hnext hj' _ _ ⟨by rw [h11, Nat.sub_sub], by rw [h13, Nat.sub_sub], h10, h17, hk,
      hj', done', only'⟩
  · intro he
    have hjL : j = L := by
      have := ofNat64_eq (by omega) (by omega) (Classical.not_not.mp he)
      omega
    subst hjL
    refine hexit _ _ ⟨?_, hk, fun i hi => done' i (by omega), fun a h => only' a fun h' => h ⟨by omega, h'.2⟩⟩
    rw [h10, ← hw, borrowAt_full w m 0 (by rw [hw, ha.ml])]

/-- One position of the subtract loop. -/
theorem dsub_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M0 M : Mem} {R0 R : Nat → BitVec 64} {A B L j : Nat} {w m : List Nat}
    (ha : DsArgs M0 A B L w m) (st : DsAt M0 M R0 R A B L j w m)
    (hnext : j + 1 ≤ L → ∀ R' M', DsAt M0 M' R0 R' A B L (j + 1) w m →
      DW live S Q 0x80005de8#64 R' M')
    (hexit : ∀ R' M', DsPost M0 M' R0 R' A L w m → DW live S Q 0x80005e18#64 R' M') :
    DW live S Q 0x80005de8#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have a1 := ha.alo; have a2 := ha.ahi; have b1 := ha.blo; have b2 := ha.bhi
  have hap := ha.apart; have hj := st.jl
  have hx : w.getD j 0 < 10 := ha.wd.getD j
  have hy : m.getD j 0 < 10 := ha.md.getD j
  have hb := borrowAt_le w m 0 j (by decide)
  have l1 : ldv .lbu M (A + L - j) = BitVec.ofNat 64 (w.getD j 0) :=
    lbu_digit hx ((st.only _ (by omega)).trans (ha.wb j hj))
  have l2 : ldv .lbu M (B + L - j) = BitVec.ofNat 64 (m.getD j 0) :=
    lbu_digit hy ((st.only _ (by omega)).trans (ha.mb j hj))
  have hr := subLE_getD w m 0 j (by rw [ha.wl, ha.ml]) (by rw [ha.wl]; omega)
  have hbs := borrowAt_succ w m 0 j (by rw [ha.wl, ha.ml]) (by rw [ha.wl]; omega)
  have h11 := st.r11; have h13 := st.r13; have h10 := st.r10; have h17 := st.r17
  have e11 : BitVec.ofNat 64 (A + L - j) + 18446744073709551615#64 =
      BitVec.ofNat 64 (A + L - j - 1) := word_pred (by omega)
  have e13 : BitVec.ofNat 64 (B + L - j) + 18446744073709551615#64 =
      BitVec.ofNat 64 (B + L - j - 1) := word_pred (by omega)
  by_cases hlt : w.getD j 0 < m.getD j 0 + borrowAt w m 0 j
  · rw [if_pos hlt] at hr hbs
    bc_run hlive hS [h11, h13, h10, h17, l1, l2, e11, e13, subw_nat, subw_int_nat, toInt_ofInt64,
      BitVec.toInt_zero] at 0x80005e10
    · intro hneg; omega
    · intro hneg
      bc_run hlive hS [addiw10_int] at 0x80005e10
      exact dsub_tail hlive hS ha hj st.done st.only (by keeps_tac st.regs)
        (v := BitVec.ofNat 64 ((↑(w.getD j 0) - ↑(m.getD j 0) - ↑(borrowAt w m 0 j) + 10 : Int).toNat))
        (by bsimp []) (by rw [sbData_ofNat, hr]; congr 1; omega) (by bsimp []) (by bsimp [])
        (by bsimp [hbs]) (by bsimp [h17]) hnext hexit
  · rw [if_neg hlt] at hr hbs
    bc_run hlive hS [h11, h13, h10, h17, l1, l2, e11, e13, subw_ofNat, toInt_ofNat_small,
      BitVec.toInt_zero] at 0x80005e10
    · intro _
      exact dsub_tail hlive hS ha hj st.done st.only (by keeps_tac st.regs)
        (v := BitVec.ofNat 64 (w.getD j 0 - m.getD j 0 - borrowAt w m 0 j))
        (by bsimp []) (by rw [sbData_ofNat, hr]) (by bsimp []) (by bsimp [])
        (by bsimp [hbs]) (by bsimp [h17]) hnext hexit
    · intro hneg; omega

/-- **The subtract loop** from position `j`. -/
theorem dsub_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M0 : Mem} {R0 : Nat → BitVec 64} {A B L : Nat} {w m : List Nat}
    (ha : DsArgs M0 A B L w m)
    (hexit : ∀ R' M', DsPost M0 M' R0 R' A L w m → DW live S Q 0x80005e18#64 R' M') :
    ∀ n j R M, L - j = n → DsAt M0 M R0 R A B L j w m → DW live S Q 0x80005de8#64 R M := by
  intro n
  induction n with
  | zero =>
    intro j R M hn st
    exact dsub_body hlive hS ha st (fun h => absurd h (by omega)) hexit
  | succ n ih =>
    intro j R M hn st
    exact dsub_body hlive hS ha st (fun _ R' M' st' => ih (j + 1) R' M' (by omega) st') hexit


/-! ## The add-back loop -/

/-- The window `s` at `A` (little-endian, `L + 1` digits) and the divisor
`v` (little-endian, `L` digits, position `j` at `N + L - 1 - j`), apart, in
the heap. -/
structure DaArgs (M : Mem) (A N L : Nat) (s v : List Nat) : Prop where
  sl : s.length = L + 1
  vl : v.length = L
  sd : IsDigits s
  vd : IsDigits v
  sb : ∀ j, j ≤ L → imgM M (A + L - j) = BitVec.ofNat 8 (s.getD j 0)
  vb : ∀ j, j < L → imgM M (N + L - 1 - j) = BitVec.ofNat 8 (v.getD j 0)
  alo : 2147603920 ≤ A
  ahi : A + L < 2273312768
  nlo : 2147603920 ≤ N
  nhi : N + L < 2273312768
  apart : A + L < N ∨ N + L ≤ A
  l1 : 1 ≤ L

/-- The add-back loop at `0x80005f14` after `j` positions. -/
structure DaAt (M0 M : Mem) (R0 R : Nat → BitVec 64) (A N L j : Nat) (s v : List Nat) : Prop where
  r12 : R 12 = BitVec.ofNat 64 (A + L - j)
  r13 : R 13 = BitVec.ofNat 64 (N + L - 1 - j)
  r11 : R 11 = BitVec.ofNat 64 (carryAt (s.take L) v 0 j)
  r17 : R 17 = BitVec.ofNat 64 9
  r6 : R 6 = BitVec.ofNat 64 (N - 1)
  r10 : R 10 = BitVec.ofNat 64 1
  regs : Keeps [11, 12, 13, 14, 15] R R0
  jl : j < L
  done : ∀ i, i < j → imgM M (A + L - i) = BitVec.ofNat 8 ((addLE (s.take L) v 0).getD i 0)
  only : MemOnly (fun a => A + L - j < a ∧ a ≤ A + L) M M0

/-- The add-back's result at `0x80005f44`. -/
structure DaPost (M0 M : Mem) (R0 R : Nat → BitVec 64) (A L : Nat) (s v : List Nat) : Prop where
  r11 : R 11 = BitVec.ofNat 64 ((addLE (s.take L) v 0).getD L 0)
  regs : Keeps [11, 12, 13, 14, 15] R R0
  done : ∀ i, i < L → imgM M (A + L - i) = BitVec.ofNat 8 ((addLE (s.take L) v 0).getD i 0)
  only : MemOnly (fun a => A < a ∧ a ≤ A + L) M M0

/-- The store at `0x80005f3c` of position `j` (the word `u` in `a5`). -/
theorem dadd_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M0 M : Mem} {R0 R : Nat → BitVec 64} {A N L j : Nat} {s v : List Nat}
    {u : BitVec 64}
    (ha : DaArgs M0 A N L s v) (hj : j < L)
    (hdone : ∀ i, i < j → imgM M (A + L - i) = BitVec.ofNat 8 ((addLE (s.take L) v 0).getD i 0))
    (honly : MemOnly (fun a => A + L - j < a ∧ a ≤ A + L) M M0)
    (hk : Keeps [11, 12, 13, 14, 15] R R0) (h15 : R 15 = u)
    (hu : sbData u = BitVec.ofNat 8 ((addLE (s.take L) v 0).getD j 0))
    (h12 : R 12 = BitVec.ofNat 64 (A + L - j - 1)) (h13 : R 13 = BitVec.ofNat 64 (N + L - 1 - j - 1))
    (h11 : R 11 = BitVec.ofNat 64 (carryAt (s.take L) v 0 (j + 1)))
    (h17 : R 17 = BitVec.ofNat 64 9) (h6 : R 6 = BitVec.ofNat 64 (N - 1))
    (h10 : R 10 = BitVec.ofNat 64 1)
    (hnext : j + 1 < L → ∀ R' M', DaAt M0 M' R0 R' A N L (j + 1) s v →
      DW live S Q 0x80005f14#64 R' M')
    (hexit : ∀ R' M', DaPost M0 M' R0 R' A L s v → DW live S Q 0x80005f44#64 R' M') :
    DW live S Q 0x80005f3c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have a1 := ha.alo; have a2 := ha.ahi; have b1 := ha.nlo; have b2 := ha.nhi
  have hM : ∀ a, a ≠ A + L - j → imgM (writeLog M [(A + L - j, 1, u)]) a = imgM M a :=
    fun a h => imgM_store_miss _ _ (by omega)
  have done' : ∀ i, i < j + 1 → imgM (writeLog M [(A + L - j, 1, u)]) (A + L - i) =
      BitVec.ofNat 8 ((addLE (s.take L) v 0).getD i 0) := by
    intro i hi
    by_cases e : i = j
    · subst e; rw [imgM_sb, hu]
    · rw [hM _ (by omega)]; exact hdone i (by omega)
  have only' : MemOnly (fun a => A + L - (j + 1) < a ∧ a ≤ A + L)
      (writeLog M [(A + L - j, 1, u)]) M0 := fun a h =>
    (hM a (fun e => h ⟨by omega, by omega⟩)).trans (honly a fun h' => h ⟨by omega, h'.2⟩)
  bc_run hlive hS [h15, h12, h13, h6] at 0x80005f14 0x80005f44
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  all_goals rw [show A + L - j - 1 + 1 = A + L - j by omega]
  · intro hne
    have hj' : j + 1 < L := by
      refine Nat.lt_of_le_of_ne hj fun e => hne ?_
      congr 1; omega
    exact hnext hj' _ _ ⟨by rw [h12, Nat.sub_sub], by rw [h13, Nat.sub_sub], h11, h17, h6, h10,
      hk, hj', done', only'⟩
  · intro he
    have hjL : j + 1 = L := by
      have := ofNat64_eq (by omega) (by omega) (Classical.not_not.mp he)
      omega
    refine hexit _ _ ⟨?_, hk, fun i hi => done' i (by omega),
      fun a h => only' a fun h' => h ⟨by omega, h'.2⟩⟩
    have htl : (s.take L).length = L := by rw [List.length_take, ha.sl]; omega
    have e := addLE_getD_last (s.take L) v 0 (by rw [htl, ha.vl])
    rw [htl] at e
    rw [h11, hjL, e]

/-- One position of the add-back loop. -/
theorem dadd_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M0 M : Mem} {R0 R : Nat → BitVec 64} {A N L j : Nat} {s v : List Nat}
    (ha : DaArgs M0 A N L s v) (st : DaAt M0 M R0 R A N L j s v)
    (hnext : j + 1 < L → ∀ R' M', DaAt M0 M' R0 R' A N L (j + 1) s v →
      DW live S Q 0x80005f14#64 R' M')
    (hexit : ∀ R' M', DaPost M0 M' R0 R' A L s v → DW live S Q 0x80005f44#64 R' M') :
    DW live S Q 0x80005f14#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have a1 := ha.alo; have a2 := ha.ahi; have b1 := ha.nlo; have b2 := ha.nhi
  have hap := ha.apart; have hj := st.jl
  have htl : (s.take L).length = L := by rw [List.length_take, ha.sl]; omega
  have hsd : IsDigits (s.take L) := ha.sd.take L
  have hx : (s.take L).getD j 0 < 10 := hsd.getD j
  have hxs : (s.take L).getD j 0 = s.getD j 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
  have hy : v.getD j 0 < 10 := ha.vd.getD j
  have hc := carryAt_le (s.take L) v 0 j hsd ha.vd (by decide)
  have l1 : ldv .lbu M (A + L - j) = BitVec.ofNat 64 ((s.take L).getD j 0) := by
    rw [hxs]; exact lbu_digit (ha.sd.getD j) ((st.only _ (by omega)).trans (ha.sb j (by omega)))
  have l2 : ldv .lbu M (N + L - 1 - j) = BitVec.ofNat 64 (v.getD j 0) :=
    lbu_digit hy ((st.only _ (by omega)).trans (ha.vb j hj))
  have hr := addLE_getD (s.take L) v 0 j (by rw [htl, ha.vl]) (by rw [htl]; exact hj)
  have hcs := carryAt_succ (s.take L) v 0 j (by rw [htl, ha.vl]) (by rw [htl]; exact hj)
  have h12 := st.r12; have h13 := st.r13; have h11 := st.r11; have h17 := st.r17
  have h6 := st.r6; have h10 := st.r10
  have e12 : BitVec.ofNat 64 (A + L - j) + 18446744073709551615#64 =
      BitVec.ofNat 64 (A + L - j - 1) := word_pred (by omega)
  have e13 : BitVec.ofNat 64 (N + L - 1 - j) + 18446744073709551615#64 =
      BitVec.ofNat 64 (N + L - 1 - j - 1) := word_pred (by omega)
  bc_run hlive hS [h12, h13, h11, h17, l1, l2, e12, e13, addw_ofNat] at 0x80005f3c
  · intro hle
    exact dadd_tail hlive hS ha hj st.done st.only (by keeps_tac st.regs)
      (u := BitVec.ofNat 64 (v.getD j 0 + (s.take L).getD j 0 + carryAt (s.take L) v 0 j)) (by bsimp [])
      (by rw [sbData_ofNat, hr]; congr 1; omega) (by bsimp []) (by bsimp [])
      (by bsimp [hcs]; congr 1; omega) (by bsimp [h17]) (by bsimp [h6]) (by bsimp [h10])
      hnext hexit
  · intro hgt
    bc_run hlive hS [se12_ff6, word_sub10, h10] at 0x80005f3c
    exact dadd_tail hlive hS ha hj st.done st.only (by keeps_tac st.regs)
      (u := BitVec.ofNat 64 (v.getD j 0 + (s.take L).getD j 0 + carryAt (s.take L) v 0 j - 10))
      (by bsimp [])
      (by rw [sbData_ofNat, hr]; congr 1; omega) (by bsimp []) (by bsimp [])
      (by bsimp [hcs, h10]; congr 1; omega) (by bsimp [h17]) (by bsimp [h6]) (by bsimp [h10])
      hnext hexit

/-- **The add-back loop** from position `j`. -/
theorem dadd_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M0 : Mem} {R0 : Nat → BitVec 64} {A N L : Nat} {s v : List Nat}
    (ha : DaArgs M0 A N L s v)
    (hexit : ∀ R' M', DaPost M0 M' R0 R' A L s v → DW live S Q 0x80005f44#64 R' M') :
    ∀ n j R M, L - j = n → DaAt M0 M R0 R A N L j s v → DW live S Q 0x80005f14#64 R M := by
  intro n
  induction n with
  | zero =>
    intro j R M hn st
    have := st.jl; omega
  | succ n ih =>
    intro j R M hn st
    exact dadd_body hlive hS ha st (fun _ R' M' st' => ih (j + 1) R' M' (by omega) st') hexit

end Dc.Mach
