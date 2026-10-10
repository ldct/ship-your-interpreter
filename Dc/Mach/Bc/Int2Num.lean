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

/-! ## The buffer's digits -/

/-- What `i2nBuf n` holds: at most ten decimal digits, least significant
first, denoting `n` without a leading zero when read backwards. -/
structure BufModel (n : Nat) : Prop where
  dig : Digits (i2nBuf n)
  pos : 1 ≤ (i2nBuf n).length
  le10 : (i2nBuf n).length ≤ 10
  val : dval (i2nBuf n).reverse = n
  norm : (i2nBuf n).length = 1 ∨ (i2nBuf n).reverse.getD 0 0 ≠ 0

theorem bufModel {n : Nat} (hn : n < 2 ^ 31) : BufModel n := by
  by_cases h0 : n = 0
  · subst h0; exact ⟨by decide, by decide, by decide, rfl, .inl rfl⟩
  have d := digitsOf n
  have hl := digits_len_le 10 n (by omega)
  have hne := d.ne h0
  have hpos : 1 ≤ (Num.digits 10 n).length := by
    rcases List.exists_cons_of_ne_nil hne with ⟨a, t, e⟩; rw [e]; simp
  have e : i2nBuf n = (Num.digits 10 n).reverse := by simp [i2nBuf, h0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [e] <;> try simp only [List.reverse_reverse, List.length_reverse]
  · exact fun e he => d.dig e (List.mem_reverse.mp he)
  · exact hpos
  · exact hl
  · exact d.val
  · exact .inr (d.head h0)

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

/-- One copy step on the heap: digit `j` of `ds` stored. -/
theorem copy_step_heap {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {ds : List Nat} {j : Nat} (hyl : y.rep.len + y.rep.scale = ds.length)
    (hyo : y.Owns) (hb : BcHeap S X M H F (withDs y (ds.take j ++ List.replicate (ds.length - j) 0) :: L))
    (hj : j < ds.length) (hd : ds.getD j 0 < 10) :
    BcHeap S X (writeLog M [(y.rep.val + j, 1, zero_extend (m := 64) (BitVec.ofNat 8 (ds.getD j 0)))])
      H F (withDs y (ds.take (j + 1) ++ List.replicate (ds.length - (j + 1)) 0) :: L) := by
  have h := BcHeap.setDigit (L1 := []) hb (hb.head_noView hyo) (i := j) (d := ds.getD j 0) (by simp only [withDs]; omega)
    hd (v := zero_extend (m := 64) (BitVec.ofNat 8 (ds.getD j 0))) (sbData_zext _)
  simp only [withDs, List.nil_append] at h ⊢
  rw [fill_step ds hj] at h
  exact h

/-- The copy loop: the reversed buffer into `y`'s digits, `j` done; `s0` at
the buffer byte after the next one to copy, `a5 = n_value + j`. -/
theorem i2n_copy {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {sp : Nat} (hsf : StackFrame S sp 128) (hab : heapEnd + 128 ≤ sp)
    {buf : List Nat} (hbd : Digits buf) (hl10 : buf.length ≤ 10)
    {H : Heap} {F : List Blk} {L : List NumObj} {y : NumObj} {M0 : Mem} {R0 : Nat → BitVec 64}
    (hyl : y.rep.len + y.rep.scale = buf.length) (hyo : y.Owns)
    (hk : ∀ R M, BcHeap S X M H F (withDs y buf.reverse :: L) → BufAt M (sp - 96) buf →
      MemOnly (fun a => ¬ OutHeap a) M M0 → Keeps [8, 14, 15] R R0 →
      DW live S Q 0x800069e8#64 R M) :
    ∀ k j (R : Nat → BitVec 64) (M : Mem), buf.length - j = k → j < buf.length →
      R 8 = BitVec.ofNat 64 (sp - 96 + buf.length - j) → R 19 = BitVec.ofNat 64 (sp - 96) →
      R 15 = BitVec.ofNat 64 (y.rep.val + j) →
      BcHeap S X M H F (withDs y (buf.reverse.take j ++ List.replicate (buf.length - j) 0) :: L) →
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
    have hvl : 2147603920 ≤ y.rep.val := hn.shape.vLo
    have hpl : y.rep.ptr ≤ y.rep.val := hn.shape.ptrLe
    have hrl : buf.reverse.length = buf.length := List.length_reverse
    have hdj : buf.reverse.getD j 0 = buf.getD (buf.length - 1 - j) 0 := rev_getD buf hj
    have hd10 : buf.reverse.getD j 0 < 10 := by
      rw [hdj]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show buf.length - 1 - j < buf.length by omega),
        Option.getD_some]
      exact hbd _ (List.getElem_mem _)
    have hb' := copy_step_heap (hyl.trans hrl.symm) hyo (hrl ▸ hb) (by omega) hd10
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

/-! ## Frame, context, and result -/

/-- The registers `bc_int2num` may change. -/
abbrev i2nClob : List Nat := [5, 10, 11, 12, 13, 14, 15]

/-- The registers changed inside `bc_int2num` before its epilogue. -/
abbrev i2nAll : List Nat := [1, 2, 5, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20, 21]

/-- The saved `ra`, `s0`–`s5` in the 96-byte frame below `sp`. -/
structure I2NSaved (M : Mem) (sp : Nat) (R0 : Nat → BitVec 64) : Prop where
  ra : ldv .ld M (sp - 8) = R0 1
  s0 : ldv .ld M (sp - 16) = R0 8
  s1 : ldv .ld M (sp - 24) = R0 9
  s2 : ldv .ld M (sp - 32) = R0 18
  s3 : ldv .ld M (sp - 40) = R0 19
  s4 : ldv .ld M (sp - 48) = R0 20
  s5 : ldv .ld M (sp - 56) = R0 21

theorem I2NSaved.transport {M M' : Mem} {sp : Nat} {R0 : Nat → BitVec 64} (h : I2NSaved M sp R0)
    (hsp : 56 ≤ sp) (hag : ∀ a, sp - 56 ≤ a → a < sp → imgM M' a = imgM M a) :
    I2NSaved M' sp R0 := by
  have t : ∀ o, 8 ≤ o → o ≤ 56 → ldv .ld M' (sp - o) = ldv .ld M (sp - o) := fun o h1 h2 =>
    ldv_congr .ld fun j hj => hag _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)
  exact ⟨(t 8 (by omega) (by omega)).trans h.ra, (t 16 (by omega) (by omega)).trans h.s0,
    (t 24 (by omega) (by omega)).trans h.s1, (t 32 (by omega) (by omega)).trans h.s2,
    (t 40 (by omega) (by omega)).trans h.s3, (t 48 (by omega) (by omega)).trans h.s4,
    (t 56 (by omega) (by omega)).trans h.s5⟩

/-- `bc_int2num`'s fixed context: the 128-byte stack window (its frame and
its callees'), the result slot `q` off the heap and the window, the entry's
`sp` and return address, and `v` a C `int` other than `INT_MIN`. -/
structure I2NCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp q : Nat) (v : Int) : Prop where
  frame : StackFrame S sp 128
  above : heapEnd + 128 ≤ sp
  slot : PtrSlot S q
  slotOut : ∀ a, slotBytes q a → OutHeap a
  slotApart : q + 8 ≤ sp - 128 ∨ sp ≤ q
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0
  vlo : -2 ^ 31 < v
  vhi : v < 2 ^ 31

/-- `bc_int2num`'s result: the new number `y` for `v` (normalized, one
reference) heads the heap left by freeing `x`, its struct is in the slot, and
off the heap only the slot and the stack window changed. -/
structure I2NPostF (S : Nat → Prop) (X : Raws) (Mt0 Mt : Mem) (H : Heap) (F : List Blk)
    (Fr : List NumObj → Prop) (q sp : Nat) (v : Int) (L : List NumObj) (y : NumObj) :
    Prop where
  heap : BcHeap S X Mt H F (y :: L)
  rest : Fr L
  num : y.rep.num = Num.ofInt v
  norm : y.rep.Norm
  refs : y.rep.refs = 1
  pos : 1 ≤ y.rep.len
  owns : y.Owns
  slot : ldv .ld Mt q = BitVec.ofNat 64 y.sb.pay
  out : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 128 a → imgM Mt a = imgM Mt0 a

/-- `bc_int2num`'s continuations: the result, or `out_of_memory`. -/
structure I2NKF (live S : Nat → Prop) (X : Raws) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (Fr : List NumObj → Prop) (q sp : Nat) (v : Int) :
    Prop where
  ret : ∀ R' Mt' H F L y, Keeps i2nClob R' R0 → I2NPostF S X Mt0 Mt' H F Fr q sp v L y →
    DW live S Q (R0 1) R' Mt'
  oom : ∀ R' Mt', R' 2 = BitVec.ofNat 64 (sp - 128) →
    (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 128 a → imgM Mt' a = imgM Mt0 a) →
    DW live S Q 0x80002bcc#64 R' Mt'

/-- `I2NPostF` for a slot that held `x` (freed once). -/
abbrev I2NPost (S : Nat → Prop) (X : Raws) (Mt0 Mt : Mem) (H : Heap) (F : List Blk)
    (L1 L2 : List NumObj) (x : NumObj) (q sp : Nat) (v : Int) (L : List NumObj) (y : NumObj) : Prop :=
  I2NPostF S X Mt0 Mt H F (FreedRest L1 L2 x) q sp v L y

/-- `I2NKF` for a slot that held `x` (freed once). -/
abbrev I2NK (live S : Nat → Prop) (X : Raws) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (L1 L2 : List NumObj) (x : NumObj) (q sp : Nat) (v : Int) :
    Prop :=
  I2NKF live S X Q R0 Mt0 (FreedRest L1 L2 x) q sp v

/-- Leaving `bc_int2num`: `ra`, `sp` and `s0`–`s5` restored, the rest kept. -/
theorem keeps_restore {R' R R0 : Nat → BitVec 64} (h1 : R' 1 = R0 1) (h2 : R' 2 = R0 2)
    (h8 : R' 8 = R0 8) (h9 : R' 9 = R0 9) (h18 : R' 18 = R0 18) (h19 : R' 19 = R0 19)
    (h20 : R' 20 = R0 20) (h21 : R' 21 = R0 21) (hk : Keeps i2nAll R' R)
    (hkp : Keeps i2nAll R R0) : Keeps i2nClob R' R0 := fun z hz => by
  by_cases e1 : z = 1; · subst e1; exact h1
  by_cases e2 : z = 2; · subst e2; exact h2
  by_cases e8 : z = 8; · subst e8; exact h8
  by_cases e9 : z = 9; · subst e9; exact h9
  by_cases e18 : z = 18; · subst e18; exact h18
  by_cases e19 : z = 19; · subst e19; exact h19
  by_cases e20 : z = 20; · subst e20; exact h20
  by_cases e21 : z = 21; · subst e21; exact h21
  have hz' : z ∉ i2nAll := by
    simp only [i2nClob, i2nAll, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz ⊢; omega
  exact (hk z hz').trans (hkp z hz')

/-- The epilogue at `0x800069e8`: the saved registers back, `sp` up. -/
theorem i2n_epi {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {v : Int} {Fr : List NumObj → Prop} {H : Heap} {F : List Blk} {L : List NumObj} {y : NumObj}
    (cx : I2NCtx S R0 sp q v) (hk : I2NKF live S X Q R0 Mt0 Fr q sp v)
    (hsv : I2NSaved M sp R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (hkp : Keeps i2nAll R R0)
    (hp : I2NPostF S X Mt0 M H F Fr q sp v L y) :
    DW live S Q 0x800069e8#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hp.heap.heap.own a h1 h2
  have e1 : ldv .ld M (sp - 96 + 88) = R0 1 := by rw [show sp - 96 + 88 = sp - 8 by omega]; exact hsv.ra
  have e8 : ldv .ld M (sp - 96 + 80) = R0 8 := by rw [show sp - 96 + 80 = sp - 16 by omega]; exact hsv.s0
  have e9 : ldv .ld M (sp - 96 + 72) = R0 9 := by rw [show sp - 96 + 72 = sp - 24 by omega]; exact hsv.s1
  have e18 : ldv .ld M (sp - 96 + 64) = R0 18 := by rw [show sp - 96 + 64 = sp - 32 by omega]; exact hsv.s2
  have e19 : ldv .ld M (sp - 96 + 56) = R0 19 := by rw [show sp - 96 + 56 = sp - 40 by omega]; exact hsv.s3
  have e20 : ldv .ld M (sp - 96 + 48) = R0 20 := by rw [show sp - 96 + 48 = sp - 48 by omega]; exact hsv.s4
  have e21 : ldv .ld M (sp - 96 + 40) = R0 21 := by rw [show sp - 96 + 40 = sp - 56 by omega]; exact hsv.s5
  have hal := cx.al
  bc_run hlive hS [h2, e1, e8, e9, e18, e19, e20, e21]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  exact hk.ret _ _ H F L y (keeps_restore (by bsimp []) (by bsimp [cx.sp0]; congr 1; omega)
    (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
    (by keeps_tac Keeps.refl _ _) hkp) hp

/-- Inside `bc_int2num` once its buffer holds `v`'s digits: `sp` lowered by
96, the saved registers in the frame, `s4 = q`, `s5` the sign flag, `s2`
the digit count, `s3` one less, `s0` past the buffer's last digit, and off
the heap only the slot and the stack window changed. -/
structure I2NAt (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp q : Nat) (v : Int) :
    Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 96)
  saved : I2NSaved M sp R0
  rq : R 20 = BitVec.ofNat 64 q
  rneg : R 21 = BitVec.ofNat 64 (if v < 0 then 1 else 0)
  rlen : R 18 = BitVec.ofNat 64 (i2nBuf v.natAbs).length
  rlast : R 19 = BitVec.ofNat 64 ((i2nBuf v.natAbs).length - 1)
  rcur : R 8 = BitVec.ofNat 64 (sp - 96 + (i2nBuf v.natAbs).length)
  buf : BufAt M (sp - 96) (i2nBuf v.natAbs)
  regs : Keeps i2nAll R R0
  out : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 128 a → imgM M a = imgM Mt0 a

/-- `I2NAt` through memory writes confined to the heap, the slot and the
callees' 32-byte frame below the buffer. -/
theorem I2NAt.mem {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat}
    {v : Int} (st : I2NAt S Mt0 M R0 R sp q v) (cx : I2NCtx S R0 sp q v)
    (hag : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn (sp - 96) 32 a → imgM M' a = imgM M a) :
    I2NAt S Mt0 M' R0 R sp q v := by
  have hab := cx.above
  have hap := cx.slotApart
  simp only [heapEnd] at hab
  have hw : ∀ a, sp - 96 ≤ a → a < sp → imgM M' a = imgM M a := fun a h1 h2 =>
    hag a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)
  have bm := bufModel (n := v.natAbs) (by have := cx.vlo; have := cx.vhi; omega)
  have hl10 := bm.le10
  exact
    { st with
      saved := st.saved.transport (by omega) fun a h1 h2 => hw a (by omega) h2
      buf := fun j hj => by rw [hw _ (by omega) (by omega)]; exact st.buf j hj
      out := fun a ha h1 h2 => by
        by_cases hs : slotBytes q a
        · exact absurd hs h1
        · rw [hag a ha hs fun h => h2 (by simp only [frameIn] at *; omega)]
          exact st.out a ha h1 h2 }

/-- The registers a call from `bc_int2num` may change. -/
abbrev i2nCallClob : List Nat := [1, 5, 10, 11, 12, 13, 14, 15]

/-- `I2NAt` through a call: only `ra` and `a0`–`a5` changed. -/
theorem I2NAt.calls {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp q : Nat}
    {v : Int} (st : I2NAt S Mt0 M R0 R sp q v) (hk : Keeps i2nCallClob R' R) :
    I2NAt S Mt0 M R0 R' sp q v :=
  { st with
    r2 := by rw [hk.get 2]; exact st.r2
    rq := by rw [hk.get 20]; exact st.rq
    rneg := by rw [hk.get 21]; exact st.rneg
    rlen := by rw [hk.get 18]; exact st.rlen
    rlast := by rw [hk.get 19]; exact st.rlast
    rcur := by rw [hk.get 8]; exact st.rcur
    regs := (hk.mono (by decide)).trans st.regs }

/-- `I2NAt` through a change of `a5`. -/
theorem I2NAt.a5 {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat}
    {v : Int} (st : I2NAt S Mt0 M R0 R sp q v) (w : BitVec 64) :
    I2NAt S Mt0 M R0 (upd R 15 w) sp q v :=
  { st with
    r2 := by rw [upd_other _ _ (by decide)]; exact st.r2
    rq := by rw [upd_other _ _ (by decide)]; exact st.rq
    rneg := by rw [upd_other _ _ (by decide)]; exact st.rneg
    rlen := by rw [upd_other _ _ (by decide)]; exact st.rlen
    rlast := by rw [upd_other _ _ (by decide)]; exact st.rlast
    rcur := by rw [upd_other _ _ (by decide)]; exact st.rcur
    regs := by keeps_tac st.regs }

/-- The new number's digits from the buffer, from `0x800069c8`, then the
epilogue. -/
theorem i2n_fill {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {v : Int} {Fr : List NumObj → Prop} {H : Heap} {F : List Blk} {L : List NumObj} {y : NumObj}
    (cx : I2NCtx S R0 sp q v) (hk : I2NKF live S X Q R0 Mt0 Fr q sp v)
    (st : I2NAt S Mt0 M R0 R sp q v) (hb : BcHeap S X M H F (y :: L))
    (hy : y.rep = { zeroRep y.sb.pay y.db.pay (i2nBuf v.natAbs).length 0 with neg := decide (v < 0) })
    (hr10 : R 10 = BitVec.ofNat 64 y.sb.pay) (hslot : ldv .ld M q = BitVec.ofNat 64 y.sb.pay)
    (hrest : Fr L) :
    DW live S Q 0x800069c8#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hn := hb.nums y List.mem_cons_self
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hp : y.rep.p = y.sb.pay := by rw [hy]; rfl
  have hval := hn.value
  rw [hp] at hval
  have hs := hn.shape
  have h1 := hs.pLo; have h2 := hs.pHi; have h3 := hs.pAl
  simp only [heapStart, heapEnd] at h1 h2 hab
  have bm := bufModel (n := v.natAbs) (by have := cx.vlo; have := cx.vhi; omega)
  have hr19 := st.rlast; have hr8 := st.rcur
  have hlen := bm.pos; have hl10 := bm.le10
  have hnot := add_not_ofNat (A := sp - 96 + (i2nBuf v.natAbs).length)
    (B := (i2nBuf v.natAbs).length - 1) (by omega) (by omega)
  have hyl : y.rep.len + y.rep.scale = (i2nBuf v.natAbs).length := by rw [hy]; rfl
  have hyo : y.Owns := by show y.rep.ptr ≠ 0; rw [hy]; show y.db.h + 16 ≠ 0; omega
  have hds : List.take 0 (i2nBuf v.natAbs).reverse ++
      List.replicate ((i2nBuf v.natAbs).length - 0) 0 = y.rep.ds := by rw [hy]; simp [zeroRep]
  have hsv := st.saved
  have hr2 := st.r2
  have hkp := st.regs
  bc_run hlive hS [hr10, hval, hr19, hr8, hnot] at 0x800069d4
  refine i2n_copy hlive hS hsf cx.above bm.dig bm.le10 hyl hyo (fun R' M' hb' hbuf' hmo hkp' => ?_)
    _ 0 _ _ rfl hlen (by bsimp [hr8]) (by bsimp []; congr 1; omega) (by bsimp []) (by rw [hds]; exact hb)
    st.buf (MemOnly.refl _ _) (Keeps.refl _ _)
  have hout : ∀ a, OutHeap a → imgM M' a = imgM M a := fun a ha => hmo a fun h => h ha
  refine i2n_epi (H := H) (F := F) (L := L) (y := withDs y (i2nBuf v.natAbs).reverse) hlive cx hk (hsv.transport (by omega) fun a h1 h2 => hout a (by
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega))
    (by rw [hkp'.get 2]; bsimp [hr2]) ((hkp'.mono (by decide)).trans (by keeps_tac hkp)) ?_
  have hq := cx.slotOut
  exact
    { heap := hb'
      rest := hrest
      num := by
        simp only [NumRep.num, withDs]
        rw [bm.val]
        have e1 : y.rep.neg = decide (v < 0) := by rw [hy]
        have e2 : y.rep.scale = 0 := by rw [hy]; rfl
        rw [e1, e2]; rfl
      norm := by
        have e1 : y.rep.len = (i2nBuf v.natAbs).length := by rw [hy]; rfl
        rcases bm.norm with h | h
        · exact .inl (by simp only [withDs]; rw [e1, h]; try omega)
        · exact .inr h
      refs := by simp only [withDs]; rw [hy]; rfl
      pos := by
        have e1 : y.rep.len = (i2nBuf v.natAbs).length := by rw [hy]; rfl
        simp only [withDs]; rw [e1]; exact hlen
      owns := hyo
      slot := by
        rw [ldv_congr .ld fun j hj => hout _ (hq _ (by simp only [widthOfM] at hj; omega))]
        exact hslot
      out := fun a ha h1 h2 => (hout a ha).trans (st.out a ha h1 h2) }

/-- After `bc_new_num`, from `0x800069b8`: the result's struct stored in the
slot and its sign set when `v < 0`, then the digits and the epilogue. -/
theorem i2n_tail {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {v : Int} {Fr : List NumObj → Prop} {H : Heap} {F : List Blk} {L : List NumObj} {y : NumObj}
    (cx : I2NCtx S R0 sp q v) (hk : I2NKF live S X Q R0 Mt0 Fr q sp v)
    (st : I2NAt S Mt0 M R0 R sp q v) (hb : BcHeap S X M H F (y :: L))
    (hy : y.rep = zeroRep y.sb.pay y.db.pay (i2nBuf v.natAbs).length 0)
    (hr10 : R 10 = BitVec.ofNat 64 y.sb.pay) (hrest : Fr L) :
    DW live S Q 0x800069b8#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hn := hb.nums y List.mem_cons_self
  have hs := hn.shape
  have hp : y.rep.p = y.sb.pay := by rw [hy]; rfl
  have h1 := hs.pLo; have h2 := hs.pHi; have h3 := hs.pAl
  rw [hp] at h1 h2 h3
  simp only [heapStart, heapEnd] at h1 h2 hab
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hr20 := st.rq; have hr21 := st.rneg
  have hb1 := hb.out_frame (MemOnly.store M q 8 (BitVec.ofNat 64 y.sb.pay)) cx.slotOut
  have st1 := st.mem cx (M' := writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)])
    fun a _ hs _ => imgM_store_miss _ _ (by simp only [slotBytes] at hs; omega)
  by_cases hv : v < 0
  · have e21 : R 21 = BitVec.ofNat 64 1 := by rw [hr21, if_pos hv]
    bc_run hlive hS [hr10, hr20, e21] at 0x800069c8
    all_goals first | exact hq.acc | skip
    bc_run hlive hS [hr10, hr20, e21] at 0x800069c8
    have hq0 := cx.slotOut q ⟨Nat.le_refl _, by omega⟩
    have hq7 := cx.slotOut (q + 7) ⟨by omega, by omega⟩
    simp only [OutHeap, heapStart, heapEnd] at hq0 hq7
    have hb2 := BcHeap.setSign (L1 := []) hb1 true (v := 1#64) (by decide)
    rw [hp] at hb2
    refine i2n_fill hlive cx hk ((st1.mem cx fun a ha _ _ => imgM_store_miss _ _ ?_).a5 _) hb2
      ?_ (by bsimp [hr10]) ?_ hrest
    · simp only [OutHeap, heapStart, heapEnd] at ha; omega
    · show { y.rep with neg := true } = _
      rw [hy, decide_eq_true hv]
    · rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _
  · have e21 : R 21 = BitVec.ofNat 64 0 := by rw [hr21, if_neg hv]
    bc_run hlive hS [hr10, hr20, e21] at 0x800069c8
    all_goals first | exact hq.acc | skip
    refine i2n_fill hlive cx hk st1 hb1 ?_ hr10 (ldv_store_hit _ _ _) hrest
    rw [hy, decide_eq_false hv]; rfl

/-- The `bc_new_num(|buf|, 0)` call from `0x800069ac`, then the tail; out
of memory reaches `I2NK.oom`. -/
theorem i2n_new {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {v : Int} {Fr : List NumObj → Prop} {H : Heap} {F : List Blk} {L : List NumObj}
    (cx : I2NCtx S R0 sp q v) (hk : I2NKF live S X Q R0 Mt0 Fr q sp v)
    (st : I2NAt S Mt0 M R0 R sp q v) (hb : BcHeap S X M H F L) (hrest : Fr L) :
    DW live S Q 0x800069ac#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have bm := bufModel (n := v.natAbs) (by have := cx.vlo; have := cx.vhi; omega)
  have hl1 := bm.pos; have hl10 := bm.le10
  have hr18 := st.rlen; have hr2 := st.r2
  bc_run hlive hS [hr18, hr2] at 0x80004250
  have hsf' : StackFrame S (sp - 96) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine bc_new_num_spec hlive hb.newHeap hsf' (len := (i2nBuf v.natAbs).length) (scale := 0)
    (by simp only [heapEnd]; omega) (by omega) hl1 _ (by bsimp [hr18]) (by bsimp []) (by bsimp [hr2]) (by bsimp [])
    ⟨fun R1 Mt1 H1 F1 y hk1 hp1 hr1 => ?_, fun R' Mt' hr2' hout => ?_⟩
  · bsimp []
    exact i2n_tail hlive cx hk
      ((st.calls ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))).mem cx
        fun a ha _ hf => hp1.out a ha hf)
      (NewNumPost.insert hb hp1) hp1.rep hr1 hrest
  · refine hk.oom R' Mt' (by rw [hr2', show sp - 96 - 32 = sp - 128 by omega]) fun a ha h1 h2 => ?_
    rw [hout a ha fun h => h2 (by simp only [frameIn] at *; omega)]
    exact st.out a ha h1 h2

/-- The `bc_free_num(num)` call from `0x800069a4`, then `bc_new_num`. -/
theorem i2n_free {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {v : Int} {L1 L2 : List NumObj}
    {x : NumObj} {H : Heap} {F : List Blk}
    (cx : I2NCtx S R0 sp q v) (hk : I2NK live S X Q R0 Mt0 L1 L2 x q sp v)
    (st : I2NAt S Mt0 M R0 R sp q v) (e : FreeEntry S X M H F L1 L2 x q (sp - 96)) :
    DW live S Q 0x800069a4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h := e.heap
  have hS : HeapOwn S := fun a h1 h2 => h.heap.own a h1 h2
  have hn := h.nums x e.mem
  have hxb := h.blocks x e.mem
  have hs := hn.shape
  have hp1 := hs.pLo; have hp2 := hs.pHi
  have hr20 := st.rq; have hr2 := st.r2
  bc_run hlive hS [hr20, hr2] at 0x800048c0
  refine bc_free_num_spec hlive e _ (by bsimp [hr20]) (by bsimp [hr2]) (by bsimp [])
    ⟨fun hx2 R' Mt' hk1 hb' _ hmo => ?_, fun hx1 R' Mt' H' hk1 hrp => ?_⟩
  · bsimp []
    refine i2n_new hlive cx hk ((st.calls ((hk1.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))).mem cx fun a ha hsl _ => hmo a fun hc => ?_) hb' (.dec hx2)
    rcases hc with hc | hc
    · simp only [refsBytes, OutHeap, heapStart, heapEnd] at hc ha hp1 hp2; omega
    · exact hsl hc
  · bsimp []
    refine i2n_new hlive cx hk ((st.calls ((hk1.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))).mem cx fun a ha hsl hf => hrp.frame a fun hc => ?_)
      hrp.heap (.rel hx1)
    rcases hc with hc | hc | hc | hc | hc
    · exact OutHeap.not_alloc h.heap ha hc
    · exact ha.1 (live_in_heap h.heap hxb.sLive hc)
    · exact hsl hc
    · exact hf hc
    · exact ha.2.2 hc

/-! ## The entry and the first digit -/

theorem i2nBuf_small {n : Nat} (h : n < 10) : i2nBuf n = [n % 10] := by
  by_cases h0 : n = 0
  · subst h0; rfl
  · simp only [i2nBuf, h0, if_false]
    rw [BcModel.digits_step 10 (by decide) n h0, Nat.div_eq_of_lt h]
    rfl

/-- `bc_free_num`'s entry facts through writes confined to `bc_int2num`'s
stack window. -/
theorem FreeEntry.window {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} {R0 : Nat → BitVec 64} {sp q : Nat} {v : Int}
    (e : FreeEntry S X Mt H F L1 L2 x q (sp - 96)) (cx : I2NCtx S R0 sp q v)
    (hmo : MemOnly (frameIn sp 128) Mt' Mt) : FreeEntry S X Mt' H F L1 L2 x q (sp - 96) := by
  have hab := cx.above
  have hap := cx.slotApart
  simp only [heapEnd] at hab
  exact
    { e with
      heap := e.heap.out_frame hmo fun a ha => by
        simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at *; omega
      word := by
        rw [ldv_congr .ld fun j hj => hmo _ (by simp only [frameIn, widthOfM] at *; omega)]
        exact e.word }

/-- **`bc_int2num`'s slot at entry**: a number of the heap, freed once
(`FreedRest`), or `NULL` (`bc_free_num` returns at once, the heap kept). -/
inductive I2NSlot (S : Nat → Prop) (X : Raws) (Mt : Mem) (H : Heap) (F : List Blk) (q sp : Nat) :
    List NumObj → (List NumObj → Prop) → Prop
  | num {L1 L2 : List NumObj} {x : NumObj} :
      FreeEntry S X Mt H F L1 L2 x q sp → I2NSlot S X Mt H F q sp (L1 ++ x :: L2) (FreedRest L1 L2 x)
  | null {L : List NumObj} : BcHeap S X Mt H F L → ldv .ld Mt q = 0#64 →
      I2NSlot S X Mt H F q sp L (· = L)

theorem I2NSlot.heap {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk} {q sp : Nat}
    {L0 : List NumObj} {Fr : List NumObj → Prop} (e : I2NSlot S X Mt H F q sp L0 Fr) :
    BcHeap S X Mt H F L0 := by
  cases e with
  | num e => exact e.heap
  | null hb _ => exact hb

/-- The slot's entry facts through writes confined to `bc_int2num`'s stack
window. -/
theorem I2NSlot.window {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H : Heap} {F : List Blk}
    {L0 : List NumObj} {Fr : List NumObj → Prop} {R0 : Nat → BitVec 64} {sp q : Nat} {v : Int}
    (e : I2NSlot S X Mt H F q (sp - 96) L0 Fr) (cx : I2NCtx S R0 sp q v)
    (hmo : MemOnly (frameIn sp 128) Mt' Mt) : I2NSlot S X Mt' H F q (sp - 96) L0 Fr := by
  cases e with
  | num e => exact .num (e.window cx hmo)
  | null hb h0 =>
    have hab := cx.above
    have hap := cx.slotApart
    simp only [heapEnd] at hab
    refine .null (hb.out_frame hmo fun a ha => by
      simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at *; omega) ?_
    rw [ldv_congr .ld fun j hj => hmo _ (by simp only [frameIn, widthOfM] at *; omega)]
    exact h0

/-- The `bc_free_num(num)` call from `0x800069a4` on either slot, then
`bc_new_num`. -/
theorem i2n_freeS {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {v : Int} {L0 : List NumObj}
    {Fr : List NumObj → Prop} {H : Heap} {F : List Blk}
    (cx : I2NCtx S R0 sp q v) (hk : I2NKF live S X Q R0 Mt0 Fr q sp v)
    (st : I2NAt S Mt0 M R0 R sp q v) (e : I2NSlot S X M H F q (sp - 96) L0 Fr) :
    DW live S Q 0x800069a4#64 R M := by
  cases e with
  | num e => exact i2n_free hlive cx hk st e
  | null hb h0 =>
    have hsf := cx.frame
    have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
    have htx : tohostAddr = 0x8001ad00 := rfl
    have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
    have hr20 := st.rq; have hr2 := st.r2
    bc_run hlive hS [hr20, hr2] at 0x800048c0
    refine bc_free_num_null hlive cx.slot h0 _ (by bsimp [hr20]) (by bsimp []) fun R' hk1 => ?_
    bsimp []
    exact i2n_new hlive cx hk (st.calls ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      hb rfl

/-- Inside `bc_int2num` after its prologue and sign test: `sp` lowered by
96, the saved registers in the frame, `s4 = q`, `s5` the sign flag,
`s0 = |v|`, and only the stack window changed. -/
structure I2NHead (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp q : Nat) (v : Int) :
    Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 96)
  saved : I2NSaved M sp R0
  rq : R 20 = BitVec.ofNat 64 q
  rneg : R 21 = BitVec.ofNat 64 (if v < 0 then 1 else 0)
  rabs : R 8 = BitVec.ofNat 64 v.natAbs
  regs : Keeps i2nAll R R0
  win : MemOnly (frameIn sp 128) M Mt0

/-- The buffer filled: `I2NHead` becomes `I2NAt`. -/
theorem I2NHead.toAt {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp q : Nat}
    {v : Int} (hd : I2NHead S Mt0 M R0 R sp q v) (cx : I2NCtx S R0 sp q v)
    (hmo : MemOnly (fun a => sp - 96 ≤ a ∧ a < sp - 86) M' M)
    (hbuf : BufAt M' (sp - 96) (i2nBuf v.natAbs))
    (h18 : R' 18 = BitVec.ofNat 64 (i2nBuf v.natAbs).length)
    (h19 : R' 19 = BitVec.ofNat 64 ((i2nBuf v.natAbs).length - 1))
    (h8 : R' 8 = BitVec.ofNat 64 (sp - 96 + (i2nBuf v.natAbs).length))
    (hkp : Keeps i2nLoopClob R' R) : I2NAt S Mt0 M' R0 R' sp q v := by
  have hsf := cx.frame
  have hsl := hsf.lo
  exact
    { r2 := by rw [hkp.get 2]; exact hd.r2
      saved := hd.saved.transport (by omega) fun a h1 _ => hmo a (by omega)
      rq := by rw [hkp.get 20]; exact hd.rq
      rneg := by rw [hkp.get 21]; exact hd.rneg
      rlen := h18
      rlast := h19
      rcur := h8
      buf := hbuf
      regs := (hkp.mono (by decide)).trans hd.regs
      out := fun a _ _ h2 => (hmo a (by simp only [frameIn] at h2; omega)).trans (hd.win a h2) }

/-- From `0x80006944`: the first digit `|v| % 10`, then the digit loop or
(for `|v| < 10`) straight to `bc_free_num`. -/
theorem i2n_head {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat} {v : Int} {L0 : List NumObj}
    {Fr : List NumObj → Prop} {H : Heap} {F : List Blk}
    (cx : I2NCtx S R0 sp q v) (hk : I2NKF live S X Q R0 Mt0 Fr q sp v)
    (hd : I2NHead S Mt0 M R0 R sp q v) (e : I2NSlot S X Mt0 H F q (sp - 96) L0 Fr) :
    DW live S Q 0x80006944#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => e.heap.heap.own a h1 h2
  have hn : v.natAbs < 2 ^ 31 := by have := cx.vlo; have := cx.vhi; omega
  have h8 := hd.rabs; have h2 := hd.r2
  bc_run hlive hS [h8, h2] at 0x8000694c
  apply st_8000694c hlive
  refine moddi3_spec hlive _ (by bsimp []) fun R1 hk1 hr1 => ?_
  bsimp [] at hr1 ⊢
  rw [srem10_small (by omega)] at hr1
  have r8 : R1 8 = BitVec.ofNat 64 v.natAbs := by rw [hk1.get 8]; bsimp [h8]
  have r2 : R1 2 = BitVec.ofNat 64 (sp - 96) := by rw [hk1.get 2]; bsimp [h2]
  bc_run hlive hS [hr1, r8, r2] at 0x8000695c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  apply st_8000695c hlive
  refine divdi3_spec hlive _ (by bsimp []) fun R2 hk2 hr2 => ?_
  bsimp [] at hr2 ⊢
  rw [sdiv10_small (by omega)] at hr2
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 96) := by rw [hk2.get 2]; bsimp [r2]
  have hsx : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (v.natAbs / 10))) =
      BitVec.ofNat 64 (v.natAbs / 10) := sxw_ofNat (by omega)
  have hkk : Keeps i2nLoopClob R2 R :=
    (hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  have hmo1 : MemOnly (fun a => sp - 96 ≤ a ∧ a < sp - 86)
      (writeLog M [(sp - 96, 1, BitVec.ofNat 64 (v.natAbs % 10))]) M :=
    (MemOnly.store M _ 1 _).mono fun a ha => by omega
  have hwin : ∀ {M'}, MemOnly (fun a => sp - 96 ≤ a ∧ a < sp - 86) M' M →
      MemOnly (frameIn sp 128) M' Mt0 := fun h =>
    (h.mono fun a ha => by simp only [frameIn]; omega).trans hd.win
  have hbuf1 : BufAt (writeLog M [(sp - 96, 1, BitVec.ofNat 64 (v.natAbs % 10))]) (sp - 96)
      [v.natAbs % 10] := by
    have h0 := BufAt.snoc (M := M) (base := sp - 96) (buf := []) (fun j hj => absurd hj (by simp))
      (v.natAbs % 10)
    simp only [List.length_nil, Nat.add_zero, List.nil_append] at h0
    exact h0
  bc_run hlive hS [hr2, q2, hsx] at 0x80006970 0x800069a4
  · -- `|v| < 10`
    intro hz
    have hq : v.natAbs / 10 = 0 := (ofNat_eq_iff (x := v.natAbs / 10) (y := 0) (by omega) (by omega)).mp hz
    have hb1 : i2nBuf v.natAbs = [v.natAbs % 10] := i2nBuf_small (by omega)
    bc_run hlive hS [hr2, q2, hsx] at 0x800069a4
    refine i2n_freeS hlive cx hk (hd.toAt cx hmo1 (by rw [hb1]; exact hbuf1) (by rw [hb1]; bsimp [List.length_cons, List.length_nil])
      (by rw [hb1]; bsimp [List.length_cons, List.length_nil])
      (by rw [hb1]; bsimp [q2, List.length_cons, List.length_nil]) (by keeps_tac hkk)) (e.window cx (hwin hmo1))
  · -- the digit loop
    intro hz
    have hq : v.natAbs / 10 ≠ 0 := fun h => hz (by rw [h])
    have hv0 : v.natAbs ≠ 0 := fun h => hq (by rw [h])
    have hst := BcModel.digits_step 10 (by decide) v.natAbs hv0
    have hlen := digits_len_le 10 v.natAbs (by omega)
    rw [hst, List.length_append] at hlen
    bc_run hlive hS [hr2, q2, hsx] at 0x80006970
    refine i2n_loop hlive hS hsf (n0 := v.natAbs) (fun R' M' buf hd' hl1 hl10 h18 h19 h8 hbuf hmo hkp => ?_)
      _ (v.natAbs / 10) [v.natAbs % 10] _ _ rfl hq (by rw [hst]; rfl) (by simp)
      (by simp only [List.length_cons, List.length_nil] at hlen ⊢; omega) (by omega) (by bsimp [])
      (by bsimp [List.length_cons, List.length_nil])
      (by bsimp [q2, List.length_cons, List.length_nil]) (by bsimp [q2]) hbuf1 (MemOnly.refl _ _)
      (Keeps.refl _ _)
    have hbe : buf = i2nBuf v.natAbs := by
      simp only [i2nBuf, hv0, if_false]; rw [hd', List.reverse_reverse]
    subst hbe
    exact i2n_freeS hlive cx hk (hd.toAt cx (hmo.trans hmo1) hbuf h18 h19 h8
      (hkp.trans (by keeps_tac hkk))) (e.window cx (hwin (hmo.trans hmo1)))

/-- The memory after `bc_int2num`'s prologue: seven saved registers. -/
def i2nPro (Mt : Mem) (R : Nat → BitVec 64) (sp : Nat) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [(sp - 96 + 80, 8, R 8)]) [(sp - 96 + 48, 8, R 20)]) [(sp - 96 + 40, 8, R 21)])
    [(sp - 96 + 88, 8, R 1)]) [(sp - 96 + 72, 8, R 9)]) [(sp - 96 + 64, 8, R 18)])
    [(sp - 96 + 56, 8, R 19)]

theorem i2nPro_saved (Mt : Mem) (R : Nat → BitVec 64) {sp : Nat} (hsp : 128 ≤ sp) :
    I2NSaved (i2nPro Mt R sp) sp R := by
  unfold i2nPro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show sp - 8 = sp - 96 + 88 by omega]
    repeat (first | rw [ldv_ld_miss _ _ (by omega)] | exact ldv_store_hit _ _ _)
  · rw [show sp - 16 = sp - 96 + 80 by omega]
    repeat (first | rw [ldv_ld_miss _ _ (by omega)] | exact ldv_store_hit _ _ _)
  · rw [show sp - 24 = sp - 96 + 72 by omega]
    repeat (first | rw [ldv_ld_miss _ _ (by omega)] | exact ldv_store_hit _ _ _)
  · rw [show sp - 32 = sp - 96 + 64 by omega]
    repeat (first | rw [ldv_ld_miss _ _ (by omega)] | exact ldv_store_hit _ _ _)
  · rw [show sp - 40 = sp - 96 + 56 by omega]
    repeat (first | rw [ldv_ld_miss _ _ (by omega)] | exact ldv_store_hit _ _ _)
  · rw [show sp - 48 = sp - 96 + 48 by omega]
    repeat (first | rw [ldv_ld_miss _ _ (by omega)] | exact ldv_store_hit _ _ _)
  · rw [show sp - 56 = sp - 96 + 40 by omega]
    repeat (first | rw [ldv_ld_miss _ _ (by omega)] | exact ldv_store_hit _ _ _)

theorem i2nPro_win (Mt : Mem) (R : Nat → BitVec 64) {sp : Nat} (hsp : 128 ≤ sp) :
    MemOnly (frameIn sp 128) (i2nPro Mt R sp) Mt := fun a ha => by
  unfold i2nPro
  simp only [frameIn] at ha
  repeat rw [imgM_store_miss _ _ (by omega)]

theorem toInt_neg_small {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 63) :
    (- BitVec.ofNat 64 n).toInt = - (n : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]
  split <;> omega

/-- `negw` of a negated small word. -/
theorem negw_neg {n : Nat} (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (0#32 - BitVec.extractLsb 31 0 (- BitVec.ofNat 64 n)) =
      BitVec.ofNat 64 n := by
  have e : 0#32 - BitVec.extractLsb 31 0 (- BitVec.ofNat 64 n) =
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_neg, BitVec.toNat_ofNat]
    omega
  rw [e]; exact sxw_ofNat (by omega)

/-- **`bc_int2num(num, val)`** at `0x8000690c`, `-2^31 < val < 2^31`, with
the object `x` in the slot `num` (`L = L1 ++ x :: L2`): frees `x`
(`bc_free_num`), then stores in the slot a fresh normalized number for `val`
with one reference (`I2NK.ret`, `I2NPost`), or reaches `out_of_memory`;
clobbers `a0`–`a5`. -/
theorem bc_int2num_specS {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt : Mem} {R : Nat → BitVec 64} {sp q : Nat} {v : Int} {L0 : List NumObj}
    {Fr : List NumObj → Prop} {H : Heap} {F : List Blk}
    (cx : I2NCtx S R sp q v) (e : I2NSlot S X Mt H F q (sp - 96) L0 Fr)
    (h10 : R 10 = BitVec.ofNat 64 q) (h11 : R 11 = BitVec.ofInt 64 v)
    (hk : I2NKF live S X Q R Mt Fr q sp v) :
    DW live S Q 0x8000690c#64 R Mt := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => e.heap.heap.own a h1 h2
  have h2 := cx.sp0
  have hvl := cx.vlo; have hvh := cx.vhi
  by_cases hv : v < 0
  · have e11 : R 11 = - BitVec.ofNat 64 v.natAbs := by
      rw [h11, show v = - (v.natAbs : Int) by omega, BitVec.ofInt_neg, BitVec.ofInt_natCast,
        Int.natAbs_neg, Int.natAbs_natCast]
    have hti := toInt_neg_small (n := v.natAbs) (by omega) (by omega)
    have hng := negw_neg (n := v.natAbs) (by omega)
    bc_run hlive hS [h10, e11, h2] at 0x80006944
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    · intro hc; rw [hti] at hc; simp only [BitVec.toInt_zero] at hc; omega
    · intro _
      bc_run hlive hS [h10, e11, h2, hng] at 0x80006944
      refine i2n_head hlive cx hk (M := i2nPro Mt R sp)
        ⟨?_, i2nPro_saved Mt R (by omega), ?_, ?_, ?_, ?_, i2nPro_win Mt R (by omega)⟩ e
      · bsimp []
      · bsimp []
      · bsimp [if_pos hv]
      · bsimp []
      · keeps_tac Keeps.refl _ _
  · have e11 : R 11 = BitVec.ofNat 64 v.natAbs := by
      rw [h11, show v = (v.natAbs : Int) by omega, BitVec.ofInt_natCast, Int.natAbs_natCast]
    have hti := toInt_ofNat_small (k := v.natAbs) (by omega)
    bc_run hlive hS [h10, e11, h2] at 0x80006944
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    · intro _
      refine i2n_head hlive cx hk (M := i2nPro Mt R sp)
        ⟨?_, i2nPro_saved Mt R (by omega), ?_, ?_, ?_, ?_, i2nPro_win Mt R (by omega)⟩ e
      · bsimp []
      · bsimp []
      · bsimp [if_neg hv]
      · bsimp []
      · keeps_tac Keeps.refl _ _
    · intro hc; rw [hti] at hc; simp only [BitVec.toInt_zero] at hc; omega

/-- **`bc_int2num(num, val)`** at `0x8000690c` with the object `x` in the
slot: `bc_int2num_specS` at a slot holding a number. -/
theorem bc_int2num_spec {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt : Mem} {R : Nat → BitVec 64} {sp q : Nat} {v : Int} {L1 L2 : List NumObj}
    {x : NumObj} {H : Heap} {F : List Blk}
    (cx : I2NCtx S R sp q v) (e : FreeEntry S X Mt H F L1 L2 x q (sp - 96))
    (h10 : R 10 = BitVec.ofNat 64 q) (h11 : R 11 = BitVec.ofInt 64 v)
    (hk : I2NK live S X Q R Mt L1 L2 x q sp v) :
    DW live S Q 0x8000690c#64 R Mt :=
  bc_int2num_specS hlive cx (.num e) h10 h11 hk

end Dc.Mach
