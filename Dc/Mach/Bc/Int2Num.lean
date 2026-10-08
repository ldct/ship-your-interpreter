import Dc.Mach.Bc.NumStore
import Dc.Mach.Libgcc
import Dc.BcModel.Out

/-!
# `bc_int2num` (`lib/number.c`)

```
8000690c addi sp,sp,-96 ; save s0,s4,s5,ra,s1,s2,s3 ; s0 = a1 ; s4 = a0 ; s5 = 0
80006938 bgez a1 ; negw s0,a1 ; li s5,1
80006944 buf[0] = s0 % 10 (__moddi3) ; s1 = sext (s0 / 10) (__divdi3)
80006964 beqz s1 -> 80006a0c (s2 = 1, s3 = 0, s0 = sp + 1)
80006968 s2 = 1 ; s0 = sp + 1
80006970 loop: *s0 = s1 % 10 ; s1 = sext (s1 / 10) ; s0++ ; s3 = s2 ; s2++ ; bnez s1
800069a4 bc_free_num (num) ; bc_new_num (s2, 0) ; *num = a0 ; if s5: n_sign = MINUS
800069c8 copy: s3 = s0 - s3 - 1 ; do *a5++ = *--s0 while s0 != s3
800069e8 restore, ret
```

The digits go least significant first into the 10-byte stack buffer at
`sp`, then most significant first into the new number.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## Small-operand arithmetic of the libgcc calls -/

theorem msb_ofNat_small {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).msb = false := by
  rw [BitVec.msb_eq_decide]; simp; omega

theorem srem10_small {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).srem (BitVec.ofNat 64 10) = BitVec.ofNat 64 (n % 10) := by
  rw [srem_pp (msb_ofNat_small h) (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod]
  omega

theorem sdiv10_small {n : Nat} (h : n < 2 ^ 63) :
    sdivV (BitVec.ofNat 64 n) (BitVec.ofNat 64 10) = BitVec.ofNat 64 (n / 10) := by
  rw [sdivV_pp (msb_ofNat_small h) (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp [udivV, BitVec.toNat_udiv]
  omega

/-! ## The digit buffer -/

/-- A number below `10 ^ k` has at most `k` decimal digits. -/
theorem digits_len_le : ∀ (k n : Nat), n < 10 ^ k → (Num.digits 10 n).length ≤ k
  | 0, n, h => by
    have : n = 0 := by simp at h; omega
    subst this; decide
  | k + 1, n, h => by
    by_cases hn : n = 0
    · subst hn; exact Nat.le_trans (by decide) (Nat.zero_le _)
    rw [BcModel.digits_step 10 (by decide) n hn, List.length_append]
    have := digits_len_le k (n / 10) (by rw [Nat.pow_succ] at h; omega)
    simp; omega

/-- The least significant digits first, as the stack buffer holds them. -/
def i2nBuf (n : Nat) : List Nat := if n = 0 then [0] else (Num.digits 10 n).reverse

/-- The bytes at `base` hold the digit list `buf`. -/
def BufAt (M : Mem) (base : Nat) (buf : List Nat) : Prop :=
  ∀ j, j < buf.length → imgM M (base + j) = BitVec.ofNat 8 (buf.getD j 0)

theorem BufAt.snoc {M : Mem} {base : Nat} {buf : List Nat} (h : BufAt M base buf) (d : Nat) :
    BufAt (writeLog M [(base + buf.length, 1, BitVec.ofNat 64 d)]) base (buf ++ [d]) := by
  intro j hj
  simp only [List.length_append, List.length_cons, List.length_nil] at hj
  by_cases hji : j = buf.length
  · subst hji
    rw [imgM_sb, sbData_eq]
    apply BitVec.eq_of_toNat_eq
    simp [lo8, toNat_setWidth8]
  · rw [imgM_store_miss _ _ (by omega), h j (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < buf.length by omega)]

/-! ## Decimal digits of a natural number -/

/-- The digits of `n` are decimal digits, denote `n`, and (for `n ≠ 0`)
start with a nonzero digit. -/
structure DigitsOf (n : Nat) : Prop where
  dig : Digits (Num.digits 10 n)
  val : dval (Num.digits 10 n) = n
  ne : n ≠ 0 → Num.digits 10 n ≠ []
  head : n ≠ 0 → (Num.digits 10 n).getD 0 0 ≠ 0

theorem digitsOf : ∀ n, DigitsOf n
  | n => by
    by_cases hn : n = 0
    · subst hn; exact ⟨by decide, rfl, fun h => absurd rfl h, fun h => absurd rfl h⟩
    have hst := BcModel.digits_step 10 (by decide) n hn
    have ih := digitsOf (n / 10)
    have hd : n % 10 < 10 := Nat.mod_lt _ (by decide)
    refine ⟨?_, ?_, fun _ => by rw [hst]; simp, fun _ => ?_⟩
    · rw [hst]; intro d hd'
      rcases List.mem_append.mp hd' with h | h
      · exact ih.dig d h
      · simp at h; omega
    · rw [hst]
      show BcModel.dvalBE _ = n
      rw [BcModel.dvalBE_append]
      have := ih.val
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.pow_one]
      show dval _ * 10 + dval [n % 10] = n
      rw [this]; simp [dval]; omega
    · rw [hst]
      by_cases hq : n / 10 = 0
      · rw [hq]; simp [show Num.digits 10 0 = [] from rfl]; omega
      · have h1 := ih.ne hq
        have h2 := ih.head hq
        obtain ⟨d, ds, he⟩ := List.exists_cons_of_ne_nil h1
        rw [he] at h2 ⊢
        simpa using h2
  decreasing_by omega

/-! ## The digit loop (`0x80006970`) -/

/-- The registers the digit loop may change. -/
abbrev i2nLoopClob : List Nat := [1, 5, 8, 9, 10, 11, 12, 13, 15, 18, 19]

/-- The digit loop: `s1 = cur ≠ 0` still to convert, `buf` (least significant
first) at `sp' = sp - 96`, `s0 = sp' + |buf|`, `s2 = |buf|`. It ends at
`0x800069a4` with the whole buffer, `s3 = |buf| - 1`. -/
theorem i2n_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {sp n0 : Nat} (hsf : StackFrame S sp 128) {M0 : Mem}
    {R0 : Nat → BitVec 64}
    (hk : ∀ R M buf, Num.digits 10 n0 = buf.reverse → 1 ≤ buf.length → buf.length ≤ 10 →
      R 18 = BitVec.ofNat 64 buf.length → R 19 = BitVec.ofNat 64 (buf.length - 1) →
      R 8 = BitVec.ofNat 64 (sp - 96 + buf.length) → BufAt M (sp - 96) buf →
      MemOnly (fun a => sp - 96 ≤ a ∧ a < sp - 86) M M0 → Keeps i2nLoopClob R R0 →
      DW live S Q 0x800069a4#64 R M) :
    ∀ k cur buf (R : Nat → BitVec 64) (M : Mem), (Num.digits 10 cur).length = k → cur ≠ 0 →
      Num.digits 10 n0 = Num.digits 10 cur ++ buf.reverse → 1 ≤ buf.length →
      buf.length + k ≤ 10 → cur < 2 ^ 31 →
      R 9 = BitVec.ofNat 64 cur → R 18 = BitVec.ofNat 64 buf.length →
      R 8 = BitVec.ofNat 64 (sp - 96 + buf.length) → R 2 = BitVec.ofNat 64 (sp - 96) →
      BufAt M (sp - 96) buf → MemOnly (fun a => sp - 96 ≤ a ∧ a < sp - 86) M M0 →
      Keeps i2nLoopClob R R0 →
      DW live S Q 0x80006970#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k with
  | zero =>
    intro cur buf R M hl hc
    rw [BcModel.digits_step 10 (by decide) cur hc] at hl
    simp at hl
  | succ k ih =>
    intro cur buf R M hl hc hd hb1 hb10 hcl h9 h18 h8 h2 hbuf hmo hkp
    bc_run hlive hS [h9, h18, h8, h2] at 0x80006978
    apply st_80006978 hlive
    refine moddi3_spec hlive _ (by bsimp []) fun R1 hk1 hr1 => ?_
    bsimp [] at hr1 ⊢
    rw [srem10_small (by omega)] at hr1
    have r9 : R1 9 = BitVec.ofNat 64 cur := by rw [hk1.get 9]; bsimp [h9]
    have r8 : R1 8 = BitVec.ofNat 64 (sp - 96 + buf.length) := by rw [hk1.get 8]; bsimp [h8]
    have r18 : R1 18 = BitVec.ofNat 64 buf.length := by rw [hk1.get 18]; bsimp [h18]
    have r2 : R1 2 = BitVec.ofNat 64 (sp - 96) := by rw [hk1.get 2]; bsimp [h2]
    bc_run hlive hS [hr1, r9, r8, r18, r2] at 0x8000698c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    apply st_8000698c hlive
    refine divdi3_spec hlive _ (by bsimp []) fun R2 hk2 hr2 => ?_
    bsimp [] at hr2 ⊢
    rw [sdiv10_small (by omega)] at hr2
    have q8 : R2 8 = BitVec.ofNat 64 (sp - 96 + buf.length) := by rw [hk2.get 8]; bsimp [r8]
    have q18 : R2 18 = BitVec.ofNat 64 buf.length := by rw [hk2.get 18]; bsimp [r18]
    have q2 : R2 2 = BitVec.ofNat 64 (sp - 96) := by rw [hk2.get 2]; bsimp [r2]
    have hst := BcModel.digits_step 10 (by decide) cur hc
    have hl' : (Num.digits 10 (cur / 10)).length = k := by
      rw [hst, List.length_append] at hl; simp at hl; omega
    have hmo' : MemOnly (fun a => sp - 96 ≤ a ∧ a < sp - 86)
        (writeLog M [(sp - 96 + buf.length, 1, BitVec.ofNat 64 (cur % 10))]) M0 :=
      ((MemOnly.store M _ 1 _).mono fun a ha => by omega).trans hmo
    have hkk : Keeps i2nLoopClob R2 R :=
      (hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    bc_run hlive hS [hr2, q8, q18, q2] at 0x80006970 0x800069a4
    · intro hne
      have hq : cur / 10 ≠ 0 := fun e => hne (by rw [e])
      refine ih (cur / 10) (buf ++ [cur % 10]) _ _ hl' hq ?_ (by simp) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by omega) (by bsimp []) ?_ ?_ (by bsimp [q2]) (hbuf.snoc _) hmo' ?_
      · rw [hd, hst]; simp
      · bsimp []; rw [sxw_ofNat (by omega)]; simp
      · bsimp []; simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_assoc]
      · keeps_tac (hkk.trans hkp)
    · intro heq
      have hq : cur / 10 = 0 := by
        rcases Nat.eq_zero_or_pos (cur / 10) with h | h
        · exact h
        · exact absurd (by intro e; have := (ofNat_eq_iff (x := cur / 10) (y := 0) (by omega) (by omega)).mp e; omega) heq
      refine hk _ _ (buf ++ [cur % 10]) ?_ (by simp) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        ?_ ?_ ?_ (hbuf.snoc _) hmo' ?_
      · rw [hd, hst, hq]; simp; rfl
      · bsimp []; rw [sxw_ofNat (by omega)]; simp
      · bsimp []; simp
      · bsimp []; simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_assoc]
      · keeps_tac (hkk.trans hkp)

/-! ## The copy loop (`0x800069d4`) -/

theorem rev_getD (buf : List Nat) {j : Nat} (hj : j < buf.length) :
    buf.reverse.getD j 0 = buf.getD (buf.length - 1 - j) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_reverse hj]

/-- One more digit of `ds` in place, the rest still zero. -/
theorem fill_step (ds : List Nat) {j : Nat} (hj : j < ds.length) :
    (ds.take j ++ List.replicate (ds.length - j) 0).set j (ds.getD j 0) =
      ds.take (j + 1) ++ List.replicate (ds.length - (j + 1)) 0 := by
  have hl : (ds.take j).length = j := by simp; omega
  rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self,
    show ds.length - j = (ds.length - (j + 1)) + 1 by omega, List.replicate_succ, List.set_cons_zero,
    List.take_add_one, List.append_assoc]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
    Option.toList_some, List.singleton_append]

/-- A buffer off the heap survives heap-only writes. -/
theorem BufAt.transport {M M' : Mem} {base : Nat} {buf : List Nat} (h : BufAt M base buf)
    (hfr : MemOnly (fun a => ¬ OutHeap a) M' M) (hout : ∀ j, j < buf.length → OutHeap (base + j)) :
    BufAt M' base buf := fun j hj => by
  rw [hfr _ fun h' => h' (hout j hj)]; exact h j hj

/-- The object `y` with digit list `ds`. -/
abbrev withDs (y : NumObj) (ds : List Nat) : NumObj := { y with rep := { y.rep with ds := ds } }

/-- One copy step on the heap: digit `j` of `ds` stored. -/
theorem copy_step_heap {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {ds : List Nat} {j : Nat} (hyl : y.rep.len + y.rep.scale = ds.length)
    (hb : BcHeap S M H F (withDs y (ds.take j ++ List.replicate (ds.length - j) 0) :: L))
    (hj : j < ds.length) (hd : ds.getD j 0 < 10) :
    BcHeap S (writeLog M [(y.rep.val + j, 1, zero_extend (m := 64) (BitVec.ofNat 8 (ds.getD j 0)))])
      H F (withDs y (ds.take (j + 1) ++ List.replicate (ds.length - (j + 1)) 0) :: L) := by
  have h := BcHeap.setDigit (L1 := []) hb (i := j) (d := ds.getD j 0) (by simp only [withDs]; omega)
    hd (v := zero_extend (m := 64) (BitVec.ofNat 8 (ds.getD j 0))) (sbData_zext _)
  simp only [withDs, List.nil_append] at h ⊢
  rw [fill_step ds hj] at h
  exact h

/-- The copy loop: the reversed buffer into `y`'s digits, `j` done; `s0` at
the buffer byte after the next one to copy, `a5 = n_value + j`. -/
theorem i2n_copy {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {sp : Nat} (hsf : StackFrame S sp 128) (hab : heapEnd + 128 ≤ sp)
    {buf : List Nat} (hbd : Digits buf) (hl10 : buf.length ≤ 10)
    {H : Heap} {F : List Blk} {L : List NumObj} {y : NumObj} {M0 : Mem} {R0 : Nat → BitVec 64}
    (hyl : y.rep.len + y.rep.scale = buf.length)
    (hk : ∀ R M, BcHeap S M H F (withDs y buf.reverse :: L) → BufAt M (sp - 96) buf →
      MemOnly (fun a => ¬ OutHeap a) M M0 → Keeps [8, 14, 15] R R0 →
      DW live S Q 0x800069e8#64 R M) :
    ∀ k j (R : Nat → BitVec 64) (M : Mem), buf.length - j = k → j < buf.length →
      R 8 = BitVec.ofNat 64 (sp - 96 + buf.length - j) → R 19 = BitVec.ofNat 64 (sp - 96) →
      R 15 = BitVec.ofNat 64 (y.rep.val + j) →
      BcHeap S M H F (withDs y (buf.reverse.take j ++ List.replicate (buf.length - j) 0) :: L) →
      BufAt M (sp - 96) buf → MemOnly (fun a => ¬ OutHeap a) M M0 → Keeps [8, 14, 15] R R0 →
      DW live S Q 0x800069d4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapEnd] at hab
  intro k
  induction k with
  | zero => intro j R M h1 h2; omega
  | succ k ih =>
    intro j R M hkj hj h8 h19 h15 hb hbuf hmo hkp
    have hn := hb.nums _ List.mem_cons_self
    num_facts hn
    have hrd := hbuf (buf.length - 1 - j) (by omega)
    rw [show sp - 96 + (buf.length - 1 - j) = sp - 96 + buf.length - j - 1 by omega] at hrd
    have p8 : BitVec.ofNat 64 (sp - 96 + buf.length - j) + 18446744073709551615#64 =
        BitVec.ofNat 64 (sp - 96 + buf.length - j - 1) := word_pred (by omega)
    have p15 : BitVec.ofNat 64 (y.rep.val + j + 1) + 18446744073709551615#64 =
        BitVec.ofNat 64 (y.rep.val + j) := word_pred (by omega)
    apply st_800069d4 hlive
    all_goals bsimp [h8, p8]
    all_goals first | bc_addr | exact frame_acc hsf (by omega) (by omega) | skip
    have hvb : y.rep.val + y.rep.len + y.rep.scale ≤ 2273312768 := hn.shape.vHi
    have hvl : 2147603920 ≤ y.rep.ptr := hn.shape.vLo
    have hpl : y.rep.ptr ≤ y.rep.val := hn.shape.ptrLe
    have hrl : buf.reverse.length = buf.length := List.length_reverse
    have hdj : buf.reverse.getD j 0 = buf.getD (buf.length - 1 - j) 0 := rev_getD buf hj
    have hd10 : buf.reverse.getD j 0 < 10 := by
      rw [hdj]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show buf.length - 1 - j < buf.length by omega),
        Option.getD_some]
      exact hbd _ (List.getElem_mem _)
    have hb' := copy_step_heap (hyl.trans hrl.symm) (hrl ▸ hb) (by omega) hd10
    rw [hdj, hrl] at hb'
    have hst : MemOnly (fun a => ¬ OutHeap a) (writeLog M [(y.rep.val + j, 1,
        zero_extend (m := 64) (BitVec.ofNat 8 (buf.getD (buf.length - 1 - j) 0)))]) M :=
      (MemOnly.store M _ 1 _).mono fun a ha h' => by
        simp only [OutHeap, heapStart, heapEnd] at h'; omega
    have hbuf' := hbuf.transport hst fun i hi => by
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
    bc_run hlive hS [h8, h19, h15, ldv_lbu, hrd, p8, p15] at 0x800069d4 0x800069e8
    all_goals first | exact acc_heap hS (by omega) (by omega) | skip
    · intro hne
      refine ih (j + 1) _ _ (by omega) ?_ (by bsimp []; congr 1) (by bsimp [h19])
        (by bsimp [Nat.add_assoc]) hb' hbuf' (hst.trans hmo) (by keeps_tac hkp)
      rcases Nat.lt_or_ge (j + 1) buf.length with h | h
      · exact h
      · exact absurd (by congr 1; omega) hne
    · intro heq
      have hj1 : j + 1 = buf.length := by
        have := (ofNat_eq_iff (x := sp - 96) (y := sp - 96 + buf.length - j - 1) (by omega)
          (by omega)).mp (Classical.not_not.mp heq)
        omega
      have htk : List.take buf.length buf.reverse = buf.reverse := by
        rw [← hrl, List.take_length]
      rw [hj1, Nat.sub_self, List.replicate_zero, List.append_nil, htk] at hb'
      exact hk _ _ hb' hbuf' (hst.trans hmo) (by keeps_tac hkp)

end Dc.Mach
