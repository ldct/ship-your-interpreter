import Dc.Mach.Bc.ShiftAddSub
import Dc.Mach.Bc.Int2Num

/-!
# `_bc_simp_mul` inside `_bc_rec_mul` (`lib/number.c`)

`_bc_rec_mul` (`0x80004bd0`) takes its base case when `ulen + vlen` is below
`mul_base_digits` or either length is below a quarter of it; the base case
is `_bc_simp_mul`, inlined:

```
80004c30 bc_new_num (ulen + vlen + 1, 0) ; *prod = it
80004c58 save s3, s7-s11 ; s8 = u's digits, s9 = v's, s3 = pvptr
80004cb4 column k (s2): n1ptr (s7), n2ptr (s11) at their starting digits
80004ce8 inner loop: sum (s10) += *n1ptr-- * *n2ptr++ (__muldi3)
80004d0c *pvptr-- = sum % 10 (__modsi3) ; sum /= 10 (__divdi3)
80004d44 *pvptr = sum ; restore, ret
```

The columns are `conv a b k` of the little-endian digit functions
(`Dc/BcModel/Mul.lean`); the machine runs `ulen + vlen` columns, one more
than `simpMulLE`, whose extra column is zero.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-! ## The model -/

/-- The little-endian digit function of the first `n` digits of `ds`. -/
def digLE (ds : List Nat) (n : Nat) : Nat → Nat := fun i => if i < n then ds.getD (n - 1 - i) 0 else 0

/-- What the inner loop adds from `n1ptr` at little-endian index `i` with
`r` digits of `n2` left. -/
def dotR (a : Nat → Nat) (la : Nat) (b : Nat → Nat) (i r : Nat) : Nat :=
  if r = 0 then 0 else dotLoop a la b i (r - 1)

theorem dotR_step (a : Nat → Nat) (la : Nat) (b : Nat → Nat) {i r : Nat} (hi : i < la)
    (hr : 1 ≤ r) : dotR a la b i r = a i * b (r - 1) + dotR a la b (i + 1) (r - 1) := by
  unfold dotR
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  cases j with
  | zero => simp [dotLoop, hi]
  | succ j => simp [dotLoop, hi]

theorem dotR_out (a : Nat → Nat) (la : Nat) (b : Nat → Nat) {i r : Nat} (hi : la ≤ i) :
    dotR a la b i r = 0 := by
  unfold dotR
  split
  · rfl
  · obtain ⟨j, hj⟩ : ∃ j, r - 1 = j := ⟨_, rfl⟩
    rw [hj]; cases j <;> simp [dotLoop, show ¬ i < la by omega]

/-! ## The inner loop -/

theorem mul_ofNat (a b : Nat) :
    BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_mod]

/-- Registers the inner loop changes. -/
abbrev smInClob : List Nat := [1, 10, 11, 12, 13, 23, 26, 27]

/-- The inner loop at `0x80004cec`: `n1ptr` (`s7`) at `u`'s little-endian
index `i < ulen`, `n2ptr` (`s11`) with `r` of `v`'s digits left, `s1` at
`v`'s last read digit, `s0` at `u`'s first, `sum` in `s10`. -/
theorem sm_inner {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {u v : NumRep} (hS : HeapOwn S) (hu : NumAt M u) (hv : NumAt M v)
    {la lb : Nat} (hla : la ≤ u.len + u.scale) (hlb : lb ≤ v.len + v.scale) (hlb1 : 1 ≤ lb) :
    ∀ (r i sum : Nat) (R : Nat → BitVec 64), i < la → r ≤ lb →
      R 23 = BitVec.ofNat 64 (u.val + (la - 1 - i)) → R 8 = BitVec.ofNat 64 u.val →
      R 27 = BitVec.ofNat 64 (v.val + lb - r) → R 9 = BitVec.ofNat 64 (v.val + lb - 1) →
      R 26 = BitVec.ofNat 64 sum → sum + 81 * min r (la - i) < 2 ^ 30 →
      (∀ R', Keeps smInClob R' R →
        R' 26 = BitVec.ofNat 64 (sum + dotR (digLE u.ds la) la (digLE v.ds lb) i r) →
        DW live S Q 0x80004d0c#64 R' M) →
      DW live S Q 0x80004cec#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have u1 := hu.shape.vLo; have u2 := hu.shape.vHi
  have v1 := hv.shape.vLo; have v2 := hv.shape.vHi
  simp only [heapStart, heapEnd] at u1 u2 v1 v2
  intro r
  induction r with
  | zero =>
    intro i sum R hi _ h23 h8 h27 h9 h26 _ hk
    bc_run hlive hS [h9, h27] at 0x80004d0c
    · intro _
      exact hk R (Keeps.refl _ _) (by rw [h26]; simp [dotR])
    · intro hc; (try bv_nat at hc); omega
  | succ r ih =>
    intro i sum R hi hr h23 h8 h27 h9 h26 hsum hk
    have l1 := hv.lbu (i := lb - (r + 1)) (by omega)
    have l0 := hu.lbu (i := la - 1 - i) (by omega)
    rw [show v.val + (lb - (r + 1)) = v.val + lb - (r + 1) by omega] at l1
    have d1 := hv.getD_lt (lb - (r + 1))
    have d0 := hu.getD_lt (la - 1 - i)
    bc_run hlive hS [h9, h27, h23, l0, l1] at 0x80004d00
    · intro hc; omega
    intro _
    bc_run hlive hS [h9, h27, h23, l0, l1] at 0x80004d00
    apply st_80004d00 hlive
    refine muldi3_spec hlive _ (by bsimp []) fun R1 hk1 hr1 => ?_
    bsimp [] at hr1 ⊢
    rw [mul_ofNat] at hr1
    have r23 : R1 23 = BitVec.ofNat 64 (u.val + (la - 1 - i) - 1) := by
      rw [hk1.get 23]; bsimp [h23]
    have r8 : R1 8 = BitVec.ofNat 64 u.val := by rw [hk1.get 8]; bsimp [h8]
    have r9 : R1 9 = BitVec.ofNat 64 (v.val + lb - 1) := by rw [hk1.get 9]; bsimp [h9]
    have r26 : R1 26 = BitVec.ofNat 64 sum := by rw [hk1.get 26]; bsimp [h26]
    have r27 : R1 27 = BitVec.ofNat 64 (v.val + lb - (r + 1) + 1) := by
      rw [hk1.get 27]; bsimp [h27]
    have hp : u.ds.getD (la - 1 - i) 0 * v.ds.getD (lb - (r + 1)) 0 ≤ 81 :=
      Nat.mul_le_mul (by omega : _ ≤ 9) (by omega : _ ≤ 9)
    have hval : sum + dotR (digLE u.ds la) la (digLE v.ds lb) i (r + 1) =
        u.ds.getD (la - 1 - i) 0 * v.ds.getD (lb - (r + 1)) 0 + sum +
          dotR (digLE u.ds la) la (digLE v.ds lb) (i + 1) r := by
      rw [dotR_step _ _ _ hi (by omega)]
      simp only [Nat.add_sub_cancel, digLE, if_pos hi, if_pos (show r < lb by omega)]
      rw [show lb - 1 - r = lb - (r + 1) by omega]
      ac_rfl
    have hkk : Keeps smInClob (upd R1 26 (BitVec.ofNat 64
        (u.ds.getD (la - 1 - i) 0 * v.ds.getD (lb - (r + 1)) 0 + sum))) R :=
      by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
    bc_run hlive hS [hr1, r23, r8, r9, r26, r27, addw_ofNat (by omega :
      u.ds.getD (la - 1 - i) 0 * v.ds.getD (lb - (r + 1)) 0 + sum < 2 ^ 31)] at 0x80004cec 0x80004d0c
    · intro hc
      refine ih (i + 1) (u.ds.getD (la - 1 - i) 0 * v.ds.getD (lb - (r + 1)) 0 + sum) _ (by omega) (by omega) ?_ (by bsimp [r8]) ?_ (by bsimp [r9])
        (by bsimp []) (by omega) fun R' hk' h' => hk R' (hk'.trans hkk) (by rw [h', hval])
      · rw [show u.val + (la - 1 - (i + 1)) = u.val + (la - 1 - i) - 1 by omega]; bsimp [r23]
      · rw [show v.val + lb - r = v.val + lb - (r + 1) + 1 by omega]; bsimp [r27]
    · intro hc
      refine hk _ hkk ?_
      rw [hval, dotR_out _ _ _ (by omega : la ≤ i + 1)]
      bsimp []

/-! ## The columns -/

/-- Column `k`'s sum as the inner loop adds it: from `u`'s index
`k - min k (lb - 1)` with `min k (lb - 1) + 1` of `v`'s digits. -/
def colv (a : Nat → Nat) (la : Nat) (b : Nat → Nat) (lb k : Nat) : Nat :=
  dotR a la b (k - min k (lb - 1)) (min k (lb - 1) + 1)

/-- The digits (newest first) and the carry after `k` columns. -/
def colSt (a : Nat → Nat) (la : Nat) (b : Nat → Nat) (lb : Nat) : Nat → List Nat × Nat
  | 0 => ([], 0)
  | k + 1 =>
    (((colSt a la b lb k).2 + colv a la b lb k) % 10 :: (colSt a la b lb k).1,
      ((colSt a la b lb k).2 + colv a la b lb k) / 10)

/-- The column loop's registers at `0x80004cb4` for column `k`, carry `c`;
the product's digits end at `P`. -/
structure ColRegs (R : Nat → BitVec 64) (u v : NumRep) (la lb P sp k c : Nat) : Prop where
  r18 : R 18 = BitVec.ofNat 64 k
  r26 : R 26 = BitVec.ofNat 64 c
  r19 : R 19 = BitVec.ofNat 64 (P - k)
  r20 : R 20 = BitVec.ofNat 64 (la - 1)
  r21 : R 21 = BitVec.ofNat 64 lb
  r22 : R 22 = BitVec.ofNat 64 (la + lb)
  r24 : R 24 = BitVec.ofNat 64 u.val
  r25 : R 25 = BitVec.ofNat 64 v.val
  r9 : R 9 = BitVec.ofNat 64 (v.val + lb - 1)
  r8 : R 8 = BitVec.ofNat 64 u.val
  r2 : R 2 = BitVec.ofNat 64 sp

/-- A `subw` of two words. -/
abbrev subw (x y : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.extractLsb 31 0 x - BitVec.extractLsb 31 0 y)

theorem ex_sx (y : BitVec 32) : BitVec.extractLsb 31 0 (BitVec.signExtend 64 y) = y := by
  ext i hi
  simp [show i < 64 by omega, BitVec.getElem_signExtend, show i < 32 by omega]

theorem e_ofNat (P : Nat) : BitVec.extractLsb 31 0 (BitVec.ofNat 64 P) = BitVec.ofNat 32 P := by
  apply BitVec.eq_of_toNat_eq; simp

theorem subw_toInt {k V : Nat} (hk : k < 2 ^ 31) (hV : V < 2 ^ 31) :
    (subw (BitVec.ofNat 64 k) (BitVec.ofNat 64 V)).toInt = (k : Int) - V := by
  rw [BitVec.toInt_signExtend_of_le (by decide), e_ofNat, e_ofNat, BitVec.toInt_eq_toNat_cond]
  simp [BitVec.toNat_sub]
  split <;> omega

/-- The column loop's `subw` of a stored pointer difference and `pvptr`. -/
theorem subw_ptr {P V k : Nat} (hk : k ≤ P) :
    subw (subw (BitVec.ofNat 64 P) (BitVec.ofNat 64 V)) (BitVec.ofNat 64 (P - k)) =
      subw (BitVec.ofNat 64 k) (BitVec.ofNat 64 V) := by
  simp only [subw, ex_sx, e_ofNat]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

theorem ptr_sub {x m d : Nat} (h : d ≤ x + m) (hx : x + m < 2 ^ 64) (hm : m < 2 ^ 64) (hd : d < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 m - BitVec.ofNat 64 d) = BitVec.ofNat 64 (x + m - d) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub, BitVec.toNat_add]
  omega

/-- The inner loop's first test at `0x80004ce8`: `n1ptr` at index `i ≤ la`
(below `u`'s digits when `i = la`). -/
theorem sm_ce8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {u v : NumRep} (hS : HeapOwn S) (hu : NumAt M u) (hv : NumAt M v)
    {la lb : Nat} (hla : la ≤ u.len + u.scale) (hlb : lb ≤ v.len + v.scale) (hla1 : 1 ≤ la)
    (hlb1 : 1 ≤ lb) {i r sum : Nat} {R : Nat → BitVec 64} (hi : i ≤ la) (hr : r ≤ lb)
    (h23 : R 23 = BitVec.ofNat 64 (u.val + (la - 1) - i)) (h8 : R 8 = BitVec.ofNat 64 u.val)
    (h27 : R 27 = BitVec.ofNat 64 (v.val + lb - r)) (h9 : R 9 = BitVec.ofNat 64 (v.val + lb - 1))
    (h26 : R 26 = BitVec.ofNat 64 sum) (hsum : sum + 81 * min r (la - i) < 2 ^ 30)
    (hk : ∀ R', Keeps smInClob R' R →
      R' 26 = BitVec.ofNat 64 (sum + dotR (digLE u.ds la) la (digLE v.ds lb) i r) →
      DW live S Q 0x80004d0c#64 R' M) :
    DW live S Q 0x80004ce8#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have u1 := hu.shape.vLo; have u2 := hu.shape.vHi
  simp only [heapStart, heapEnd] at u1 u2
  bc_run hlive hS [h23, h8] at 0x80004cec 0x80004d0c
  · intro hc
    (try bv_nat at hc)
    exact hk R (Keeps.refl _ _) (by rw [h26, dotR_out _ _ _ (by omega : la ≤ i), Nat.add_zero])
  · intro hc
    (try bv_nat at hc)
    exact sm_inner hlive hS hu hv hla hlb hlb1 r i sum R (by omega) hr
      (by rw [h23]; congr 1; omega) h8 h27 h9 h26 hsum hk

/-- Registers the column head and the inner loop change. -/
abbrev smHeadClob : List Nat := [1, 10, 11, 12, 13, 14, 15, 23, 26, 27]

/-- Column `k` from `0x80004cd4`, with `a5 = (la - 1) - MAX (0, k - lb + 1)`. -/
theorem sm_col_mid {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {u v : NumRep} (hS : HeapOwn S) (hu : NumAt M u) (hv : NumAt M v)
    {la lb P sp k c : Nat} (hla : la ≤ u.len + u.scale) (hlb : lb ≤ v.len + v.scale)
    (hla1 : 1 ≤ la) (hlb1 : 1 ≤ lb) (hk : k < la + lb) (hN : la + lb < 2 ^ 31)
    (hc : c + 81 * min la lb < 2 ^ 30) {R : Nat → BitVec 64}
    (hr : ColRegs R u v la lb P sp k c)
    (h15 : R 15 = BitVec.ofNat 64 (la - 1) - BitVec.ofNat 64 (k + 1 - lb))
    (hkk : ∀ R', Keeps smHeadClob R' R →
      R' 26 = BitVec.ofNat 64 (c + colv (digLE u.ds la) la (digLE v.ds lb) lb k) →
      DW live S Q 0x80004d0c#64 R' M) :
    DW live S Q 0x80004cd4#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have u1 := hu.shape.vLo; have u2 := hu.shape.vHi
  have v1 := hv.shape.vLo; have v2 := hv.shape.vHi
  simp only [heapStart, heapEnd] at u1 u2 v1 v2
  have e7 : BitVec.ofNat 64 u.val + (BitVec.ofNat 64 (la - 1) - BitVec.ofNat 64 (k + 1 - lb)) =
      BitVec.ofNat 64 (u.val + (la - 1) - (k + 1 - lb)) := ptr_sub (by omega) (by omega) (by omega) (by omega)
  bc_run hlive hS [hr.r18, hr.r24, hr.r25, hr.r9, hr.r21, h15, e7, sxw_ofNat, toInt_ofNat_small] at 0x80004ce8
  · intro hc'
    (try simp (disch := omega) only [toInt_ofNat_small] at hc')
    refine sm_ce8 hlive hS hu hv hla hlb hla1 hlb1 (i := k + 1 - lb) (r := lb) (sum := c) (by omega) (by omega)
      (by bsimp []) (by bsimp [hr.r8]) (by bsimp [hr.r25]; congr 1; omega) (by bsimp [hr.r9])
      (by bsimp [hr.r26]) (by omega) fun R' hk' h' => hkk R' ((hk'.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)) ?_
    rw [h']; unfold colv
    rw [show min k (lb - 1) = lb - 1 by omega, show k - (lb - 1) = k + 1 - lb by omega,
      show lb - 1 + 1 = lb by omega]
  · intro hc'
    bc_run hlive hS [hr.r9] at 0x80004ce8
    refine sm_ce8 hlive hS hu hv hla hlb hla1 hlb1 (i := k + 1 - lb) (r := k + 1) (sum := c) (by omega) (by omega)
      (by bsimp []) (by bsimp [hr.r8]) (by bsimp [hr.r18]; rw [sub_ofNat (by omega) (by omega)]; congr 1; omega) (by bsimp [hr.r9])
      (by bsimp [hr.r26]) (by omega) fun R' hk' h' => hkk R' ((hk'.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)) ?_
    rw [h']; unfold colv
    rw [show min k (lb - 1) = k by omega, show k - k = k + 1 - lb by omega]

/-- Scratch registers of the column head. -/
abbrev colScratch : List Nat := [1, 5, 10, 11, 12, 13, 14, 15, 23, 27]

theorem ColRegs.keep {R R' : Nat → BitVec 64} {u v : NumRep} {la lb P sp k c : Nat}
    (hr : ColRegs R u v la lb P sp k c) (hk : Keeps colScratch R' R) :
    ColRegs R' u v la lb P sp k c where
  r18 := by rw [hk.get 18]; exact hr.r18
  r26 := by rw [hk.get 26]; exact hr.r26
  r19 := by rw [hk.get 19]; exact hr.r19
  r20 := by rw [hk.get 20]; exact hr.r20
  r21 := by rw [hk.get 21]; exact hr.r21
  r22 := by rw [hk.get 22]; exact hr.r22
  r24 := by rw [hk.get 24]; exact hr.r24
  r25 := by rw [hk.get 25]; exact hr.r25
  r9 := by rw [hk.get 9]; exact hr.r9
  r8 := by rw [hk.get 8]; exact hr.r8
  r2 := by rw [hk.get 2]; exact hr.r2

theorem m1_toInt : (18446744073709551615#64).toInt = -1 := by decide

/-- Column `k` from `0x80004cb4` to the digit store at `0x80004d0c`. -/
theorem sm_col_head {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {u v : NumRep} (hS : HeapOwn S) (hu : NumAt M u) (hv : NumAt M v)
    {la lb P sp k c : Nat} (hla : la ≤ u.len + u.scale) (hlb : lb ≤ v.len + v.scale)
    (hla1 : 1 ≤ la) (hlb1 : 1 ≤ lb) (hk : k < la + lb) (hN : la + lb < 2 ^ 31) (hkP : k ≤ P)
    (hc : c + 81 * min la lb < 2 ^ 30) {R : Nat → BitVec 64} {A8 A10 : BitVec 64}
    (hsf : StackFrame S (sp + 192) 192)
    (h8 : ldv .ld M (sp + 8) = A8) (h10 : ldv .ld M (sp + 16) = A10)
    (hA8 : subw A8 (BitVec.ofNat 64 (P - k)) = subw (BitVec.ofNat 64 k) (BitVec.ofNat 64 lb))
    (hA10 : subw A10 (BitVec.ofNat 64 (P - k)) = subw (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 lb))
    (hr : ColRegs R u v la lb P sp k c)
    (hkk : ∀ R', Keeps smHeadClob R' R →
      R' 26 = BitVec.ofNat 64 (c + colv (digLE u.ds la) la (digLE v.ds lb) lb k) →
      DW live S Q 0x80004d0c#64 R' M) :
    DW live S Q 0x80004cb4#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hsl := hsf.lo; have hsh := hsf.hi
  bc_run hlive hS [hr.r19, hr.r20, hr.r2, h8, hA8] at 0x80004cd4 0x80004cc8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · intro hc'
    rw [subw_toInt (by omega) (by omega), m1_toInt] at hc'
    refine sm_col_mid hlive hS hu hv hla hlb hla1 hlb1 hk hN hc
      (hr.keep (by keeps_tac Keeps.refl _ _)) (by bsimp []; rw [show k + 1 - lb = 0 by omega]; exact (BitVec.sub_zero _).symm)
      fun R' hk' h' => hkk R' ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) h'
  · intro hc'
    rw [subw_toInt (by omega) (by omega), m1_toInt] at hc'
    bc_run hlive hS [hr.r19, hr.r20, hr.r2, h10, hA10, subw_ofNat (show lb ≤ k + 1 by omega) (by omega)]
      at 0x80004cd4
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine sm_col_mid hlive hS hu hv hla hlb hla1 hlb1 hk hN hc
      (hr.keep (by keeps_tac Keeps.refl _ _)) (by bsimp [])
      fun R' hk' h' => hkk R' ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) h'

/-- Registers a column changes. -/
abbrev colClob : List Nat := [1, 5, 8, 10, 11, 12, 13, 14, 15, 18, 19, 23, 26, 27]

theorem ColRegs.set26 {R R' : Nat → BitVec 64} {u v : NumRep} {la lb P sp k c s : Nat}
    (hr : ColRegs R u v la lb P sp k c) (hk : Keeps smHeadClob R' R)
    (h26 : R' 26 = BitVec.ofNat 64 s) : ColRegs R' u v la lb P sp k s where
  r18 := by rw [hk.get 18]; exact hr.r18
  r26 := h26
  r19 := by rw [hk.get 19]; exact hr.r19
  r20 := by rw [hk.get 20]; exact hr.r20
  r21 := by rw [hk.get 21]; exact hr.r21
  r22 := by rw [hk.get 22]; exact hr.r22
  r24 := by rw [hk.get 24]; exact hr.r24
  r25 := by rw [hk.get 25]; exact hr.r25
  r9 := by rw [hk.get 9]; exact hr.r9
  r8 := by rw [hk.get 8]; exact hr.r8
  r2 := by rw [hk.get 2]; exact hr.r2

theorem ofNat64_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- The column registers after the counters advance. -/
theorem ColRegs.next {R : Nat → BitVec 64} {u v : NumRep} {la lb P sp k s c : Nat}
    (hr : ColRegs R u v la lb P sp k s) :
    ColRegs (upd (upd (upd R 18 (BitVec.ofNat 64 (k + 1))) 19 (BitVec.ofNat 64 (P - k - 1))) 26
      (BitVec.ofNat 64 c)) u v la lb P sp (k + 1) c where
  r18 := by bsimp []
  r26 := by bsimp []
  r19 := by bsimp []; congr 1
  r20 := by bsimp [hr.r20]
  r21 := by bsimp [hr.r21]
  r22 := by bsimp [hr.r22]
  r24 := by bsimp [hr.r24]
  r25 := by bsimp [hr.r25]
  r9 := by bsimp [hr.r9]
  r8 := by bsimp [hr.r8]
  r2 := by bsimp [hr.r2]

/-- The column registers after `s0` is reloaded through `a5`. -/
theorem ColRegs.reload {R : Nat → BitVec 64} {u v : NumRep} {la lb P sp k c : Nat}
    (hr : ColRegs R u v la lb P sp k c) (x : BitVec 64) :
    ColRegs (upd (upd R 15 x) 8 (BitVec.ofNat 64 u.val)) u v la lb P sp k c where
  r18 := by bsimp [hr.r18]
  r26 := by bsimp [hr.r26]
  r19 := by bsimp [hr.r19]
  r20 := by bsimp [hr.r20]
  r21 := by bsimp [hr.r21]
  r22 := by bsimp [hr.r22]
  r24 := by bsimp [hr.r24]
  r25 := by bsimp [hr.r25]
  r9 := by bsimp [hr.r9]
  r8 := by bsimp []
  r2 := by bsimp [hr.r2]

/-- The digit store and carry of column `k` from `0x80004d0c` (sum `s` in
`s10`), on to the next column or the final carry. -/
theorem sm_col_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {u v : NumRep} (hS : HeapOwn S) (hus : NumShape u) {la lb P sp k s : Nat}
    (hk : k < la + lb) (hN : la + lb < 2 ^ 31) (hkP : k < P) (hs : s < 2 ^ 30)
    (hPlo : 2147603920 ≤ P - k) (hPhi : P + 1 ≤ 2273312768)
    {R : Nat → BitVec 64} (hsf : StackFrame S (sp + 192) 192) (hr : ColRegs R u v la lb P sp k s)
    (hs0 : ldv .ld (writeLog M [(P - k, 1, BitVec.ofNat 64 (s % 10))]) sp = BitVec.ofNat 64 u.p)
    (hval : ldv .ld (writeLog M [(P - k, 1, BitVec.ofNat 64 (s % 10))]) (u.p + 32) =
      BitVec.ofNat 64 u.val)
    (hnext : k + 1 < la + lb → ∀ R', Keeps colClob R' R → ColRegs R' u v la lb P sp (k + 1) (s / 10) →
      DW live S Q 0x80004cb4#64 R' (writeLog M [(P - k, 1, BitVec.ofNat 64 (s % 10))]))
    (hexit : k + 1 = la + lb → ∀ R', Keeps colClob R' R → ColRegs R' u v la lb P sp (k + 1) (s / 10) →
      DW live S Q 0x80004d44#64 R' (writeLog M [(P - k, 1, BitVec.ofNat 64 (s % 10))])) :
    DW live S Q 0x80004d0c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hsl := hsf.lo; have hsh := hsf.hi
  bc_run hlive hS [hr.r26] at 0x80004d14
  apply st_80004d14 hlive
  refine moddi3_spec hlive _ (by bsimp []) fun R1 hk1 hr1 => ?_
  bsimp [] at hr1 ⊢
  rw [srem10_small (by omega)] at hr1
  have q1 := hr.keep (R' := R1) (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  bc_run hlive hS [hr1, q1.r19, q1.r26] at 0x80004d24
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  apply st_80004d24 hlive
  refine divdi3_spec hlive _ (by bsimp []) fun R2 hk2 hr2 => ?_
  bsimp [] at hr2 ⊢
  rw [sdiv10_small (by omega)] at hr2
  have q2 := q1.keep (R' := R2) (by keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  have hkk : Keeps colClob R2 R :=
    (hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  bc_run hlive hS [hr2, q2.r18, q2.r19, q2.r22, q2.r2, hs0, hval, word_pred (show 1 ≤ P - k by omega),
    sxw_ofNat (show s / 10 < 2 ^ 31 by omega)] at 0x80004cb4 0x80004d44
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · intro hc
    exact hexit (ofNat64_eq (by omega) (by omega) hc) _ (by keeps_tac hkk) q2.next
  · intro hc
    have hc' : k + 1 ≠ la + lb := fun e => hc (by rw [e])
    have up1 := hus.pLo; have up2 := hus.pHi
    simp only [heapStart, heapEnd] at up1 up2
    bc_run hlive hS [hs0, hval, q2.r2] at 0x80004cb4
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact hnext (by omega) _ (by keeps_tac hkk) (q2.next.reload _)

/-! ## The column loop -/

theorem dotR_le {a b : Nat → Nat} (ha : ∀ i, a i ≤ 9) (hb : ∀ j, b j ≤ 9) (la : Nat) :
    ∀ r i, dotR a la b i r ≤ 81 * min r (la - i)
  | 0, i => by simp [dotR]
  | r + 1, i => by
    rcases Nat.lt_or_ge i la with hi | hi
    · rw [dotR_step a la b hi (by omega), Nat.add_sub_cancel]
      have h1 : a i * b r ≤ 81 := Nat.mul_le_mul (ha i) (hb r)
      have h2 := dotR_le ha hb la r (i + 1)
      omega
    · rw [dotR_out a la b hi]; omega

theorem digLE_le {ds : List Nat} (hd : ∀ i, ds.getD i 0 < 10) (n i : Nat) : digLE ds n i ≤ 9 := by
  unfold digLE; split
  · have := hd (n - 1 - i); omega
  · omega

theorem colv_le {a b : Nat → Nat} (ha : ∀ i, a i ≤ 9) (hb : ∀ j, b j ≤ 9) (la lb k : Nat)
    (hlb : 1 ≤ lb) : colv a la b lb k ≤ 81 * min la lb := by
  have := dotR_le ha hb la (min k (lb - 1) + 1) (k - min k (lb - 1))
  unfold colv; omega

/-- The carry stays below `9 * min la lb`. -/
theorem colSt_le {a b : Nat → Nat} (ha : ∀ i, a i ≤ 9) (hb : ∀ j, b j ≤ 9) (la lb : Nat)
    (hlb : 1 ≤ lb) : ∀ k, (colSt a la b lb k).2 ≤ 9 * min la lb
  | 0 => by simp [colSt]
  | k + 1 => by
    have h1 := colSt_le ha hb la lb hlb k
    have h2 := colv_le ha hb la lb k hlb
    simp only [colSt]
    omega

/-- The product's digits through column `k` (big-endian, unwritten zeros first). -/
abbrev colDs (u v : NumRep) (la lb k : Nat) : List Nat :=
  List.replicate (la + lb + 1 - k) 0 ++ (colSt (digLE u.ds la) la (digLE v.ds lb) lb k).1

/-- **The column loop** at `0x80004cb4` with `j` columns left: each column
adds its products to the carry, stores `sum % 10` at `pvptr` and keeps
`sum / 10`. -/
theorem sm_cols {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {H : Heap} {F : List Blk} {L : List NumObj} {y uo vo : NumObj}
    (hyo : y.Owns) (huL : uo ∈ L) (hvL : vo ∈ L) {la lb P sp : Nat} {A8 A10 : BitVec 64}
    (hla : la ≤ uo.rep.len + uo.rep.scale) (hlb : lb ≤ vo.rep.len + vo.rep.scale)
    (hla1 : 1 ≤ la) (hlb1 : 1 ≤ lb) (hN : la + lb < 2 ^ 31) (hm : 90 * min la lb < 2 ^ 30)
    (hyl : y.rep.len + y.rep.scale = la + lb + 1) (hP : P = y.rep.val + (la + lb))
    (hsf : StackFrame S (sp + 192) 192) (hsp : heapEnd ≤ sp)
    (hA8 : ∀ k, k ≤ P →
      subw A8 (BitVec.ofNat 64 (P - k)) = subw (BitVec.ofNat 64 k) (BitVec.ofNat 64 lb))
    (hA10 : ∀ k, k ≤ P →
      subw A10 (BitVec.ofNat 64 (P - k)) = subw (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 lb))
    {M0 : Mem} {R0 : Nat → BitVec 64}
    (hk : ∀ R' M', Keeps colClob R' R0 →
      ColRegs R' uo.rep vo.rep la lb P sp (la + lb)
        (colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb (la + lb)).2 →
      BcHeap S M' H F (withDs y (colDs uo.rep vo.rep la lb (la + lb)) :: L) →
      MemOnly (accBytes y.rep) M' M0 → DW live S Q 0x80004d44#64 R' M') :
    ∀ j k R M, j + k = la + lb → 1 ≤ j → Keeps colClob R R0 →
      ColRegs R uo.rep vo.rep la lb P sp k
        (colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k).2 →
      BcHeap S M H F (withDs y (colDs uo.rep vo.rep la lb k) :: L) →
      MemOnly (accBytes y.rep) M M0 → ldv .ld M sp = BitVec.ofNat 64 uo.rep.p →
      ldv .ld M (sp + 8) = A8 → ldv .ld M (sp + 16) = A10 →
      DW live S Q 0x80004cb4#64 R M := by
  intro j
  induction j with
  | zero => intro k R M _ h; omega
  | succ j ih =>
    intro k R M hjk _ hkR hr hb hmo h0 h8 h10
    have hu := hb.nums uo (List.mem_cons_of_mem _ huL)
    have hv := hb.nums vo (List.mem_cons_of_mem _ hvL)
    have hys := (hb.nums _ List.mem_cons_self).shape
    have y1 := hys.vLo; have y2 := hys.vHi
    simp only [withDs, heapStart, heapEnd] at y1 y2
    have hsp' := hsp
    simp only [heapEnd] at hsp'
    have ha9 : ∀ i, digLE uo.rep.ds la i ≤ 9 := digLE_le hu.getD_lt la
    have hb9 : ∀ i, digLE vo.rep.ds lb i ≤ 9 := digLE_le hv.getD_lt lb
    have hc := colSt_le ha9 hb9 la lb hlb1 k
    have hcv := colv_le ha9 hb9 la lb k hlb1
    refine sm_col_head hlive hS hu hv hla hlb hla1 hlb1 (by omega) hN (by omega) (by omega) hsf h8 h10
      (hA8 k (by omega)) (hA10 k (by omega)) hr fun R1 hk1 h1 => ?_
    have hrev : (0 :: List.replicate (la + lb - k) 0).reverse ++
        (colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k).1 = colDs uo.rep vo.rep la lb k := by
      unfold colDs
      rw [← List.replicate_succ, List.reverse_replicate, show la + lb - k + 1 = la + lb + 1 - k by omega]
    have hb' := BcHeap.storeRev hyo (xs := List.replicate (la + lb - k) 0)
      (D := (colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k).1) (a := 0)
      (d := ((colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k).2 +
        colv (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k) % 10)
      (by rw [hrev]; exact hb) (by simp only [withDs, List.length_replicate]; omega)
      (Nat.mod_lt _ (by decide)) (sbData_ofNat _)
    rw [List.length_replicate, show y.rep.val + (la + lb - k) = P - k by omega] at hb'
    have hcd : (List.replicate (la + lb - k) 0).reverse ++
        (((colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k).2 +
          colv (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k) % 10 ::
          (colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k).1) =
        colDs uo.rep vo.rep la lb (k + 1) := by
      unfold colDs
      rw [List.reverse_replicate, show la + lb + 1 - (k + 1) = la + lb - k by omega]
      rfl
    rw [hcd] at hb'
    have hmo' : MemOnly (accBytes y.rep) (writeLog M [(P - k, 1, BitVec.ofNat 64
        (((colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k).2 +
          colv (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k) % 10))]) M0 :=
      ((MemOnly.store M _ 1 _).mono fun a ha => by simp only [accBytes]; omega).trans hmo
    refine sm_col_tail hlive hS hu.shape (by omega) hN (by omega) (by omega) (by omega) (by omega) hsf
      (hr.set26 hk1 h1) (by rw [ldv_ld_miss _ _ (by omega)]; exact h0)
      (hb'.nums uo (List.mem_cons_of_mem _ huL)).value
      (fun hlt R2 hk2 hr2 => ih (k + 1) R2 _ (by omega) (by omega) (hk2.trans ((hk1.mono (by decide)).trans hkR)) hr2 hb' hmo'
        (by rw [ldv_ld_miss _ _ (by omega)]; exact h0) (by rw [ldv_ld_miss _ _ (by omega)]; exact h8)
        (by rw [ldv_ld_miss _ _ (by omega)]; exact h10))
      fun heq R2 hk2 hr2 => ?_
    have hfin := hk R2 (writeLog M [(P - k, 1, BitVec.ofNat 64
        (((colSt (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k).2 +
          colv (digLE uo.rep.ds la) la (digLE vo.rep.ds lb) lb k) % 10))]) (hk2.trans ((hk1.mono (by decide)).trans hkR))
    rw [← heq] at hfin
    exact hfin hr2 hb' hmo'

end Dc.Mach
