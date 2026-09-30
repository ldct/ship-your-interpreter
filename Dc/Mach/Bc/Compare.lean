import Dc.Mach.Bc.Scan

/-!
# `_bc_do_compare` and `bc_compare` (`lib/number.c`)

GCC splits `_bc_do_compare` (`ignore_last` constant-propagated to `FALSE`):
the sign test stays in the callers (`bc_compare`), the rest is
`_bc_do_compare.part.0.constprop.0` at `0x80003fb0` with `a2 = use_sign`.
On normalised numbers (`NumRep.Norm`) it compares magnitudes:
`n_len` first, then the digits of the common length, then the extra fraction
digits of the longer scale against zero.

- `cmpMag_of_*`: `Num.cmpMag` of two objects from that walk (the first
  differing digit of the zero-padded digit lists decides).
- `do_compare_spec`: `a0 = ordWord (cmpRes u neg₁ (Num.cmpMag n₁ n₂))`.
- `bc_compare_spec`: `a0 = ordWord (Num.cmp n₁ n₂)`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## Magnitude comparison on representations -/

/-- The digits of `o` padded with zeros to scale `s`. -/
def NumRep.padded (o : NumRep) (s : Nat) : List Nat := o.ds ++ List.replicate (s - o.scale) 0

theorem NumRep.padded_len {o : NumRep} (hs : NumShape o) {s : Nat} (h : o.scale ≤ s) :
    (o.padded s).length = o.len + s := by
  simp only [NumRep.padded, List.length_append, List.length_replicate, hs.dsLen]; omega

theorem NumRep.padded_getD (o : NumRep) (s j : Nat) : (o.padded s).getD j 0 = o.ds.getD j 0 :=
  getD_pad _ _ _

theorem NumRep.padded_digits {o : NumRep} (hs : NumShape o) (s : Nat) : Digits (o.padded s) :=
  digits_pad hs.dig _

theorem NumRep.padded_val (o : NumRep) (s : Nat) :
    dval (o.padded s) = dval o.ds * 10 ^ (s - o.scale) := by
  simp only [NumRep.padded, dval_append, dval_replicate_zero, List.length_replicate, Nat.add_zero]

theorem NumRep.cmpMag_eq (a b : NumRep) :
    Dc.Num.cmpMag a.num b.num =
      compare (dval (a.padded (max a.scale b.scale))) (dval (b.padded (max a.scale b.scale))) := by
  simp only [Dc.Num.cmpMag, NumRep.align_eq, NumRep.num_scale, NumRep.padded]

/-- Equal integer lengths: the first differing digit decides. -/
theorem cmpMag_of_first_diff {a b : NumRep} (ha : NumShape a) (hb : NumShape b)
    (hl : a.len = b.len) {j : Nat} (hj : j < a.len + max a.scale b.scale)
    (heq : ∀ i, i < j → a.ds.getD i 0 = b.ds.getD i 0) (hne : a.ds.getD j 0 ≠ b.ds.getD j 0) :
    Dc.Num.cmpMag a.num b.num = compare (a.ds.getD j 0) (b.ds.getD j 0) := by
  rw [NumRep.cmpMag_eq]
  have h1 := NumRep.padded_len ha (Nat.le_max_left a.scale b.scale)
  have h2 := NumRep.padded_len hb (Nat.le_max_right a.scale b.scale)
  rw [compare_dval_first_diff j (NumRep.padded_digits ha _) (NumRep.padded_digits hb _)
    (by rw [h1, h2, hl]) (by rw [h1]; exact hj)
    (fun i hi => by rw [NumRep.padded_getD, NumRep.padded_getD]; exact heq i hi)
    (by rw [NumRep.padded_getD, NumRep.padded_getD]; exact hne),
    NumRep.padded_getD, NumRep.padded_getD]

/-- Equal integer lengths and no differing digit: equal. -/
theorem cmpMag_of_all_eq {a b : NumRep} (ha : NumShape a) (hb : NumShape b)
    (hl : a.len = b.len)
    (heq : ∀ i, i < a.len + max a.scale b.scale → a.ds.getD i 0 = b.ds.getD i 0) :
    Dc.Num.cmpMag a.num b.num = .eq := by
  rw [NumRep.cmpMag_eq]
  have h1 := NumRep.padded_len ha (Nat.le_max_left a.scale b.scale)
  have h2 := NumRep.padded_len hb (Nat.le_max_right a.scale b.scale)
  have : a.padded (max a.scale b.scale) = b.padded (max a.scale b.scale) :=
    list_ext_getD (by rw [h1, h2, hl]) fun i hi => by
      rw [NumRep.padded_getD, NumRep.padded_getD]; exact heq i (by rw [h1] at hi; exact hi)
  rw [this]; exact Nat.compare_eq_eq.2 rfl

/-- A shorter integer part (normalised): smaller. -/
theorem cmpMag_of_len_lt {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hnb : b.Norm)
    (hl : a.len < b.len) : Dc.Num.cmpMag a.num b.num = .lt := by
  rw [NumRep.cmpMag_eq]
  apply Nat.compare_eq_lt.2
  have la := dval_lt (NumRep.padded_digits ha (max a.scale b.scale))
  rw [NumRep.padded_len ha (Nat.le_max_left a.scale b.scale)] at la
  have := ha.lenPos
  have lb := NumRep.mag_ge hb hnb (by omega)
  rw [NumRep.padded_val b]
  have hmono : 10 ^ (a.len + max a.scale b.scale) ≤
      10 ^ (b.len - 1 + b.scale) * 10 ^ (max a.scale b.scale - b.scale) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have := Nat.mul_le_mul_right (10 ^ (max a.scale b.scale - b.scale)) lb
  omega

theorem cmpMag_swap (a b : Dc.Num) : Dc.Num.cmpMag b a = (Dc.Num.cmpMag a b).swap := by
  simp only [Dc.Num.cmpMag, Nat.max_comm b.scale a.scale]
  exact (Nat.compare_swap _ _).symm

/-- A longer integer part (normalised): larger. -/
theorem cmpMag_of_len_gt {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hna : a.Norm)
    (hl : b.len < a.len) : Dc.Num.cmpMag a.num b.num = .gt := by
  rw [cmpMag_swap, cmpMag_of_len_lt hb ha hna hl]; rfl

/-! ## `_bc_do_compare.part.0.constprop.0` (`0x80003fb0`)

```
80003fb0 lw a5,4(a0) ; 80003fb4 lw a4,4(a1) ; 80003fb8 beq a5,a4,80003fdc
80003fbc bge a4,a5,80004030
80003fc0 li a3,1 ; 80003fc4 beqz a2,80003fd4 ; 80003fc8 lw a5,0(a0) ; 80003fcc li a3,1
80003fd0 bnez a5,80004050 ; 80003fd4 mv a0,a3 ; 80003fd8 ret
80003fdc lw a7,8(a0) ; 80003fe0 lw t1,8(a1) ; 80003fe4 mv a6,a7 ; 80003fe8 bge t1,a7,80003ff0
80003fec mv a6,t1 ; 80003ff0 addw a6,a6,a5 ; 80003ff4 ld a4,32(a0) ; 80003ff8 ld a5,32(a1)
80003ffc mv a3,a6 ; 80004000 bgtz a6,80004014 ; 80004004 j 8000405c
80004008 addi a4,a4,1 ; 8000400c addi a5,a5,1 ; 80004010 beqz a3,80004060
80004014 lbu a6,0(a4) ; 80004018 lbu a1,0(a5) ; 8000401c addiw a3,a3,-1
80004020 beq a6,a1,80004008 ; 80004024 lbu a4,0(a4) ; 80004028 lbu a5,0(a5)
8000402c bltu a5,a4,80003fc0
80004030 li a3,-1 ; 80004034 beqz a2,80003fd4 ; 80004038 lw a5,0(a0) ; 8000403c li a3,-1
80004040 beqz a5,80003fd4 ; 80004044 li a3,1 ; 80004048 mv a0,a3 ; 8000404c ret
80004050 li a3,-1 ; 80004054 mv a0,a3 ; 80004058 ret ; 8000405c bnez a6,80004024
80004060 li a3,0 ; 80004064 beq a7,t1,80003fd4 ; 80004068 bge t1,a7,80004094
8000406c subw a5,a7,t1 ; 80004070 slli a5,a5,0x20 ; 80004074 srli a5,a5,0x20
80004078 add a5,a4,a5 ; 8000407c j 80004084 ; 80004080 beq a5,a4,80003fd4
80004084 lbu a3,0(a4) ; 80004088 addi a4,a4,1 ; 8000408c beqz a3,80004080 ; 80004090 j 80003fc0
80004094 subw a4,t1,a7 ; 80004098 slli a4,a4,0x20 ; 8000409c srli a4,a4,0x20
800040a0 add a4,a5,a4 ; 800040a4 j 800040ac ; 800040a8 beq a5,a4,80003fd4
800040ac lbu a3,0(a5) ; 800040b0 addi a5,a5,1 ; 800040b4 beqz a3,800040a8 ; 800040b8 j 80004030
```
-/

/-- `use_sign` and `n1`'s sign applied to a magnitude comparison. -/
def cmpRes (u neg : Bool) (c : Ordering) : Ordering := if u && neg then c.swap else c

/-- The registers `_bc_do_compare.part.0` may change. -/
abbrev cmpClob : List Nat := [6, 10, 11, 13, 14, 15, 16, 17]

/-- The return of `_bc_do_compare.part.0` entered with `R0`, result `res`. -/
abbrev CmpK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt : Mem) (res : Ordering) : Prop :=
  ∀ R', Keeps cmpClob R' R0 → R' 10 = ordWord res → DW live S Q (R0 1) R' Mt

/-- What the paths need: `a0 = n1`, `a2 = use_sign`, the return address. -/
structure CmpRegs (R R0 : Nat → BitVec 64) (o : NumRep) (u : Bool) : Prop where
  keep : Keeps cmpClob R R0
  a0 : R 10 = BitVec.ofNat 64 o.p
  a2 : R 12 = boolWord u
  ra : (R0 1).toNat % 4 = 0

/-- The "greater" exit at `0x80003fc0`. -/
theorem cmp_gt_path {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o) {u : Bool}
    {R R0 : Nat → BitVec 64} (hr : CmpRegs R R0 o u) (hk : CmpK live S Q R0 Mt (cmpRes u o.neg .gt)) :
    DW live S Q 0x80003fc0#64 R Mt := by
  num_facts h
  have h10 := hr.a0; have h12 := hr.a2; have hkeep := hr.keep; have hal := hr.ra
  have hsg := h.sign
  have h1 : R 1 = R0 1 := hkeep.get 1
  cases u <;> cases hneg : o.neg <;> rw [hneg] at hsg <;>
    simp only [signWord_false, signWord_true] at hsg
  iterate 3 all_goals bc_run hlive hS [h10, h12, hsg, h1, hal]
  all_goals refine hk _ (by keeps_tac hkeep) ?_
  all_goals first | rfl | (simp [cmpRes, ordWord, hneg])
  all_goals done

/-- The "less" exit at `0x80004030`. -/
theorem cmp_lt_path {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o) {u : Bool}
    {R R0 : Nat → BitVec 64} (hr : CmpRegs R R0 o u) (hk : CmpK live S Q R0 Mt (cmpRes u o.neg .lt)) :
    DW live S Q 0x80004030#64 R Mt := by
  num_facts h
  have h10 := hr.a0; have h12 := hr.a2; have hkeep := hr.keep; have hal := hr.ra
  have hsg := h.sign
  have h1 : R 1 = R0 1 := hkeep.get 1
  cases u <;> cases hneg : o.neg <;> rw [hneg] at hsg <;>
    simp only [signWord_false, signWord_true] at hsg
  iterate 3 all_goals bc_run hlive hS [h10, h12, hsg, h1, hal]
  all_goals refine hk _ (by keeps_tac hkeep) ?_
  all_goals first | rfl | (simp [cmpRes, ordWord, hneg])

/-- The "equal" exit at `0x80003fd4` (`a3 = 0`). -/
theorem cmp_eq_path {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {R R0 : Nat → BitVec 64} (hkeep : Keeps cmpClob R R0)
    (h13 : R 13 = 0#64) (hal : (R0 1).toNat % 4 = 0) {res : Ordering} (hres : res = .eq)
    (hk : CmpK live S Q R0 Mt res) :
    DW live S Q 0x80003fd4#64 R Mt := by
  have h1 : R 1 = R0 1 := hkeep.get 1
  dx_run hlive
  · bsimp [h1, hal]
  · rw [h1]; refine hk _ (by keeps_tac hkeep) ?_
    bsimp [h13, hres]; rfl

theorem getD_ge {ds : List Nat} {j : Nat} (h : ds.length ≤ j) : ds.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem cmpRes_eq (u neg : Bool) : cmpRes u neg .eq = .eq := by cases u <;> cases neg <;> rfl

/-- The operands of the digit walk: `a`, `b` with equal `n_len`. -/
structure CmpPair (Mt : Mem) (a b : NumRep) : Prop where
  ha : NumAt Mt a
  hb : NumAt Mt b
  len : a.len = b.len

/-- The scan of `n1`'s extra fraction digits at `0x80004084` (`n1` has the
longer scale): `a4 = n1.n_value + j`, `a5` its end; the first `j` digits
agree. -/
theorem cmp_tail1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {a b : NumRep} (hp : CmpPair Mt a b)
    (hsc : b.scale < a.scale) {u : Bool} {R0 : Nat → BitVec 64}
    (hk : CmpK live S Q R0 Mt (cmpRes u a.neg (Dc.Num.cmpMag a.num b.num))) :
    ∀ k j (R : Nat → BitVec 64), a.len + a.scale - j = k → b.len + b.scale ≤ j →
      j < a.len + a.scale → CmpRegs R R0 a u →
      R 14 = BitVec.ofNat 64 (a.val + j) → R 15 = BitVec.ofNat 64 (a.val + a.len + a.scale) →
      (∀ i, i < j → a.ds.getD i 0 = b.ds.getD i 0) →
      DW live S Q 0x80004084#64 R Mt := by
  have h := hp.ha
  num_facts h
  have hbl := hp.hb.shape.dsLen
  have hmax : max a.scale b.scale = a.scale := Nat.max_eq_left (by omega)
  intro k
  induction k with
  | zero => intro j R h1 h2 h3; omega
  | succ k ih =>
    intro j R hn hj1 hj2 hr h14 h15 heq
    have hd := h.getD_lt j
    have hb0 : b.ds.getD j 0 = 0 := getD_ge (by omega)
    have hkeep := hr.keep
    bc_run hlive hS [h14, h15, h.lbu hj2] at 0x80004080
    · intro h0
      bv_nat at h0
      rw [Nat.mod_eq_of_lt (by omega)] at h0
      bc_run hlive hS [h14, h15] at 0x80003fd4
      · intro he
        bv_nat at he
        have hj : j + 1 = a.len + a.scale := by omega
        refine cmp_eq_path hlive (by keeps_tac hkeep) (by bsimp [h0]) hr.ra ?_ hk
        rw [cmpMag_of_all_eq h.shape hp.hb.shape hp.len fun i hi => ?_, cmpRes_eq]
        rcases Nat.lt_or_ge i j with h1 | h1
        · exact heq i h1
        · rw [show i = j by omega, hb0]; exact h0
      · intro hne
        bv_nat at hne
        refine ih (j + 1) _ (by omega) (by omega) (by omega)
          ⟨by keeps_tac hkeep, by bsimp [hr.a0], by bsimp [hr.a2], hr.ra⟩ (by bsimp [Nat.add_assoc])
          (by bsimp [h15]) fun i hi => ?_
        rcases Nat.lt_or_ge i j with h1 | h1
        · exact heq i h1
        · rw [show i = j by omega, hb0]; exact h0
    · intro h0
      bv_nat at h0
      rw [Nat.mod_eq_of_lt (by omega)] at h0
      bc_run hlive hS [h14, h15] at 0x80003fc0
      refine cmp_gt_path hlive hS h (u := u) ⟨by keeps_tac hkeep, by bsimp [hr.a0], by bsimp [hr.a2], hr.ra⟩ ?_
      have e : Dc.Num.cmpMag a.num b.num = .gt := by
        rw [cmpMag_of_first_diff h.shape hp.hb.shape hp.len (j := j) (by omega) heq
          (by rw [hb0]; omega), hb0]
        exact Nat.compare_eq_gt.2 (by omega)
      rw [e] at hk; exact hk

/-- The scan of `n2`'s extra fraction digits at `0x800040ac` (`n2` has the
longer scale): `a5 = n2.n_value + j`, `a4` its end. -/
theorem cmp_tail2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {a b : NumRep} (hp : CmpPair Mt a b)
    (hsc : a.scale < b.scale) {u : Bool} {R0 : Nat → BitVec 64}
    (hk : CmpK live S Q R0 Mt (cmpRes u a.neg (Dc.Num.cmpMag a.num b.num))) :
    ∀ k j (R : Nat → BitVec 64), b.len + b.scale - j = k → a.len + a.scale ≤ j →
      j < b.len + b.scale → CmpRegs R R0 a u →
      R 15 = BitVec.ofNat 64 (b.val + j) → R 14 = BitVec.ofNat 64 (b.val + b.len + b.scale) →
      (∀ i, i < j → a.ds.getD i 0 = b.ds.getD i 0) →
      DW live S Q 0x800040ac#64 R Mt := by
  have h := hp.hb
  num_facts h
  have hal' := hp.ha.shape.dsLen
  have hlen := hp.len
  have hmax : max a.scale b.scale = b.scale := Nat.max_eq_right (by omega)
  intro k
  induction k with
  | zero => intro j R h1 h2 h3; omega
  | succ k ih =>
    intro j R hn hj1 hj2 hr h15 h14 heq
    have hd := h.getD_lt j
    have ha0 : a.ds.getD j 0 = 0 := getD_ge (by omega)
    have hkeep := hr.keep
    bc_run hlive hS [h14, h15, h.lbu hj2] at 0x800040a8
    · intro h0
      bv_nat at h0
      rw [Nat.mod_eq_of_lt (by omega)] at h0
      bc_run hlive hS [h14, h15] at 0x80003fd4
      · intro he
        bv_nat at he
        refine cmp_eq_path hlive (by keeps_tac hkeep) (by bsimp [h0]) hr.ra ?_ hk
        rw [cmpMag_of_all_eq hp.ha.shape h.shape hp.len fun i hi => ?_, cmpRes_eq]
        rcases Nat.lt_or_ge i j with h1 | h1
        · exact heq i h1
        · rw [show i = j by omega, ha0]; exact h0.symm
      · intro hne
        bv_nat at hne
        refine ih (j + 1) _ (by omega) (by omega) (by omega)
          ⟨by keeps_tac hkeep, by bsimp [hr.a0], by bsimp [hr.a2], hr.ra⟩ (by bsimp [Nat.add_assoc])
          (by bsimp [h14]) fun i hi => ?_
        rcases Nat.lt_or_ge i j with h1 | h1
        · exact heq i h1
        · rw [show i = j by omega, ha0]; exact h0.symm
    · intro h0
      bv_nat at h0
      rw [Nat.mod_eq_of_lt (by omega)] at h0
      bc_run hlive hS [h14, h15] at 0x80004030
      refine cmp_lt_path hlive hS hp.ha (u := u)
        ⟨by keeps_tac hkeep, by bsimp [hr.a0], by bsimp [hr.a2], hr.ra⟩ ?_
      have e : Dc.Num.cmpMag a.num b.num = .lt := by
        rw [cmpMag_of_first_diff hp.ha.shape h.shape hp.len (j := j) (by omega) heq
          (by rw [ha0]; omega), ha0]
        exact Nat.compare_eq_lt.2 (by omega)
      rw [e] at hk; exact hk

/-- The end of the common digits at `0x80004060`: `a4`/`a5` past the first
`c = n_len + min s₁ s₂` digits of each (all equal), `a7 = s₁`, `t1 = s₂`. -/
theorem cmp_junction {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {a b : NumRep} (hp : CmpPair Mt a b)
    {u : Bool} {R0 R : Nat → BitVec 64}
    (hk : CmpK live S Q R0 Mt (cmpRes u a.neg (Dc.Num.cmpMag a.num b.num))) (hr : CmpRegs R R0 a u)
    (h14 : R 14 = BitVec.ofNat 64 (a.val + (a.len + min a.scale b.scale)))
    (h15 : R 15 = BitVec.ofNat 64 (b.val + (a.len + min a.scale b.scale)))
    (h17 : R 17 = BitVec.ofNat 64 a.scale) (h6 : R 6 = BitVec.ofNat 64 b.scale)
    (heq : ∀ i, i < a.len + min a.scale b.scale → a.ds.getD i 0 = b.ds.getD i 0) :
    DW live S Q 0x80004060#64 R Mt := by
  have h := hp.ha
  num_facts h
  have hb := hp.hb
  have := hb.shape.pLo; have := hb.shape.vHi; have := hb.shape.size
  have hlen := hp.len
  have hkeep := hr.keep
  have hbv := hb.shape.vHi
  simp only [heapEnd] at hbv
  bc_run hlive hS [h14, h15, h17, h6] at 0x80003fd4 0x80004084 0x800040ac
  · intro he
    bv_nat at he
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
    refine cmp_eq_path hlive (by keeps_tac hkeep) (by bsimp []) hr.ra ?_ hk
    rw [cmpMag_of_all_eq h.shape hb.shape hlen fun i hi => heq i (by omega), cmpRes_eq]
  · intro hne
    bv_nat at hne
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hne
    bc_run hlive hS [h14, h15, h17, h6, toInt_ofNat_small] at 0x80003fd4 0x80004084 0x800040ac
    · intro hle
      have hlt : a.scale < b.scale := by omega
      bc_run hlive hS [h14, h15, h17, h6, subw_ofNat, shl_ofNat, shr_ofNat] at 0x80003fd4 0x80004084 0x800040ac
      refine cmp_tail2 hlive hS hp hlt hk _ (a.len + min a.scale b.scale) _ rfl (by omega) (by omega)
        ⟨by keeps_tac hkeep, by bsimp [hr.a0], by bsimp [hr.a2], hr.ra⟩ (by bsimp [h15])
        ?_ heq
      bsimp []
      exact ofNat_congr (by omega)
    · intro hgt
      have hlt : b.scale < a.scale := by omega
      bc_run hlive hS [h14, h15, h17, h6, subw_ofNat, shl_ofNat, shr_ofNat] at 0x80003fd4 0x80004084 0x800040ac
      refine cmp_tail1 hlive hS hp hlt hk _ (a.len + min a.scale b.scale) _ rfl (by omega) (by omega)
        ⟨by keeps_tac hkeep, by bsimp [hr.a0], by bsimp [hr.a2], hr.ra⟩ (by bsimp [h14])
        ?_ heq
      bsimp []
      exact ofNat_congr (by omega)

/-- The common-digit loop at `0x80004014`: `a4`/`a5` at digit `i` of each,
`a3 = c - i` for `c = n_len + min s₁ s₂`, the first `i` digits equal. -/
theorem cmp_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {a b : NumRep} (hp : CmpPair Mt a b)
    {u : Bool} {R0 : Nat → BitVec 64}
    (hk : CmpK live S Q R0 Mt (cmpRes u a.neg (Dc.Num.cmpMag a.num b.num))) :
    ∀ k i (R : Nat → BitVec 64), a.len + min a.scale b.scale - i = k →
      i < a.len + min a.scale b.scale → CmpRegs R R0 a u →
      R 14 = BitVec.ofNat 64 (a.val + i) → R 15 = BitVec.ofNat 64 (b.val + i) →
      R 13 = BitVec.ofNat 64 (a.len + min a.scale b.scale - i) →
      R 17 = BitVec.ofNat 64 a.scale → R 6 = BitVec.ofNat 64 b.scale →
      (∀ j, j < i → a.ds.getD j 0 = b.ds.getD j 0) →
      DW live S Q 0x80004014#64 R Mt := by
  have h := hp.ha
  num_facts h
  have hb := hp.hb
  have := hb.shape.pLo; have := hb.shape.vHi; have := hb.shape.size; have := hb.shape.vLo
  have := hb.shape.ptrLe
  have hbv := hb.shape.vHi
  simp only [heapEnd] at hbv
  have hbl := hb.shape.vLo
  simp only [heapStart] at hbl
  have hlen := hp.len
  have hmin : min a.scale b.scale ≤ a.scale := Nat.min_le_left _ _
  have hmin2 : min a.scale b.scale ≤ b.scale := Nat.min_le_right _ _
  intro k
  induction k with
  | zero => intro i R h1 h2; omega
  | succ k ih =>
    intro i R hn hi hr h14 h15 h13 h17 h6 heq
    have hkeep := hr.keep
    have hda := h.getD_lt i
    have hdb := hb.getD_lt i
    have la := h.lbu (show i < a.len + a.scale by omega)
    have lb := hb.lbu (show i < b.len + b.scale by omega)
    bc_run hlive hS [h14, h15, h13, la, lb, sxw_pred] at 0x80004060 0x80003fc0 0x80004030
    · intro he
      bv_nat at he
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
      bc_run hlive hS [h14, h15, h13, sxw_pred] at 0x80004060 0x80003fc0 0x80004030 0x80004014
      · intro hz
        bv_nat at hz
        refine cmp_junction hlive hS hp hk ⟨by keeps_tac hkeep, by bsimp [hr.a0], by bsimp [hr.a2], hr.ra⟩
          ?_ ?_ (by bsimp [h17]) (by bsimp [h6]) fun j hj => ?_
        · bsimp []; exact ofNat_congr (by omega)
        · bsimp []; exact ofNat_congr (by omega)
        · rcases Nat.lt_or_ge j i with h1 | h1
          · exact heq j h1
          · rw [show j = i by omega]; exact he
      · intro hz
        bv_nat at hz
        refine ih (i + 1) _ (by omega) (by omega)
          ⟨by keeps_tac hkeep, by bsimp [hr.a0], by bsimp [hr.a2], hr.ra⟩ (by bsimp [Nat.add_assoc])
          (by bsimp [Nat.add_assoc]) (by bsimp [Nat.sub_sub]) (by bsimp [h17]) (by bsimp [h6])
          fun j hj => ?_
        rcases Nat.lt_or_ge j i with h1 | h1
        · exact heq j h1
        · rw [show j = i by omega]; exact he
    · intro hne
      bv_nat at hne
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hne
      have hc := cmpMag_of_first_diff h.shape hb.shape hlen (j := i) (by omega) heq hne
      bc_run hlive hS [h14, h15, la, lb] at 0x80004060 0x80003fc0 0x80004030
      · intro hlt
        refine cmp_gt_path hlive hS h (u := u)
          ⟨by keeps_tac hkeep, by bsimp [hr.a0], by bsimp [hr.a2], hr.ra⟩ ?_
        rw [hc, Nat.compare_eq_gt.2 hlt] at hk; exact hk
      · intro hge
        refine cmp_lt_path hlive hS h (u := u)
          ⟨by keeps_tac hkeep, by bsimp [hr.a0], by bsimp [hr.a2], hr.ra⟩ ?_
        rw [hc, Nat.compare_eq_lt.2 (by omega)] at hk; exact hk

/-- **`_bc_do_compare(n1, n2, use_sign, FALSE)`** past the sign test, at
`0x80003fb0`, on normalised numbers: `a0 = ordWord (cmpRes u neg₁ (Num.cmpMag
n₁ n₂))`; clobbers `a0`, `a1`, `a3`–`a7`, `t1`. -/
theorem do_compare_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {a b : NumRep} (ha : NumAt Mt a)
    (hb : NumAt Mt b) (hna : a.Norm) (hnb : b.Norm) {u : Bool}
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 a.p) (h11 : R 11 = BitVec.ofNat 64 b.p)
    (h12 : R 12 = boolWord u) (hal : (R 1).toNat % 4 = 0)
    (hk : CmpK live S Q R Mt (cmpRes u a.neg (Dc.Num.cmpMag a.num b.num))) :
    DW live S Q 0x80003fb0#64 R Mt := by
  have h := ha
  num_facts h
  have := hb.shape.pLo; have := hb.shape.pHi; have := hb.shape.vHi; have := hb.shape.size
  have := hb.shape.pAl; have := hb.shape.lenPos
  have hbp := hb.shape.pHi; have hbp2 := hb.shape.pLo
  simp only [heapEnd, heapStart] at hbp hbp2
  have la := ha.len; have lb := hb.len; have sa := ha.scale; have sb := hb.scale
  have va := ha.value; have vb := hb.value
  have hr0 : CmpRegs R R a u := ⟨Keeps.refl _ _, h10, h12, hal⟩
  bc_run hlive hS [h10, h11, la, lb] at 0x80003fc0 0x80004030 0x80003fdc
  · intro he
    bv_nat at he
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
    have hp : CmpPair Mt a b := ⟨ha, hb, he⟩
    -- from `0x80003ff0` with `a6 = min s₁ s₂`
    have mid : ∀ R', R' 16 = BitVec.ofNat 64 (min a.scale b.scale) → R' 15 = BitVec.ofNat 64 a.len →
        R' 10 = BitVec.ofNat 64 a.p → R' 11 = BitVec.ofNat 64 b.p → R' 12 = boolWord u →
        R' 17 = BitVec.ofNat 64 a.scale → R' 6 = BitVec.ofNat 64 b.scale → Keeps cmpClob R' R →
        DW live S Q 0x80003ff0#64 R' Mt := by
      intro R' h16 h15 h10' h11' h12' h17 h6 hkp
      have hmin : min a.scale b.scale ≤ a.scale := Nat.min_le_left _ _
      bc_run hlive hS [h16, h15, h10', h11', va, vb, addw_ofNat] at 0x80004014
      · intro _
        refine cmp_loop hlive hS hp hk _ 0 _ rfl (by omega)
          ⟨by keeps_tac hkp, by bsimp [h10'], by bsimp [h12'], hal⟩ (by bsimp []) (by bsimp [])
          (by bsimp [Nat.add_comm]) (by bsimp [h17]) (by bsimp [h6])
          fun j hj => absurd hj (Nat.not_lt_zero _)
      · intro hc
        simp (disch := omega) only [toInt_ofNat_small] at hc
        simp at hc; omega
    bc_run hlive hS [h10, h11, la, lb, sa, sb, toInt_ofNat_small] at 0x80004014 0x80003ff0
    · intro hle
      refine mid _ (by bsimp [Nat.min_eq_left (show a.scale ≤ b.scale by omega)]) (by bsimp []) (by bsimp [h10]) (by bsimp [h11])
        (by bsimp [h12]) (by bsimp []) (by bsimp []) (by keeps_tac Keeps.refl _ _)
    · intro hgt
      bc_run hlive hS [h10, h11, la, lb, sa, sb] at 0x80003ff0
      refine mid _ (by bsimp [Nat.min_eq_right (show b.scale ≤ a.scale by omega)]) (by bsimp [])
        (by bsimp [h10]) (by bsimp [h11]) (by bsimp [h12]) (by bsimp []) (by bsimp [])
        (by keeps_tac Keeps.refl _ _)
  · intro hne
    bv_nat at hne
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hne
    bc_run hlive hS [h10, h11, la, lb, toInt_ofNat_small] at 0x80003fc0 0x80004030 0x80003fdc
    · intro hle
      refine cmp_lt_path hlive hS ha (u := u) ⟨by keeps_tac Keeps.refl _ _, by bsimp [h10], by bsimp [h12], hal⟩ ?_
      rw [cmpMag_of_len_lt ha.shape hb.shape hnb (by omega)] at hk; exact hk
    · intro hgt
      refine cmp_gt_path hlive hS ha (u := u) ⟨by keeps_tac Keeps.refl _ _, by bsimp [h10], by bsimp [h12], hal⟩ ?_
      rw [cmpMag_of_len_gt ha.shape hb.shape hna (by omega)] at hk; exact hk

/-! ## `bc_compare` (`0x800049d8`)

```
800049d8 lw a5,0(a0) ; 800049dc lw a4,0(a1) ; 800049e0 beq a4,a5,800049f8
800049e4 li a0,-1 ; 800049e8 bnez a5,800049f4 ; 800049ec li a0,1 ; 800049f0 ret ; 800049f4 ret
800049f8 li a2,1 ; 800049fc j 80003fb0
```
-/

/-- **`bc_compare(n1, n2)`** at `0x800049d8` on normalised numbers:
`a0 = ordWord (Num.cmp n₁ n₂)`; clobbers `a0`–`a7`, `t1`. -/
theorem bc_compare_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {a b : NumRep} (ha : NumAt Mt a)
    (hb : NumAt Mt b) (hna : a.Norm) (hnb : b.Norm)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 a.p) (h11 : R 11 = BitVec.ofNat 64 b.p)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [6, 10, 11, 12, 13, 14, 15, 16, 17] R' R →
      R' 10 = ordWord (Dc.Num.cmp a.num b.num) → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x800049d8#64 R Mt := by
  have h := ha
  num_facts h
  have := hb.shape.pLo; have := hb.shape.pHi; have := hb.shape.pAl
  have hbp := hb.shape.pHi; have hbp2 := hb.shape.pLo
  simp only [heapEnd, heapStart] at hbp hbp2
  have sga := ha.sign; have sgb := hb.sign
  cases hna' : a.neg <;> cases hnb' : b.neg <;> rw [hna'] at sga <;> rw [hnb'] at sgb <;>
    simp only [signWord_false, signWord_true] at sga sgb
  iterate 3 all_goals (try bc_run hlive hS [h10, h11, sga, sgb, hal] at 0x80003fb0)
  -- different signs
  all_goals try (refine hk _ (by keeps_tac Keeps.refl _ _) ?_; bsimp []; simp [Dc.Num.cmp, NumRep.num, ordWord, hna', hnb']; done)
  -- equal signs
  all_goals
    refine do_compare_spec hlive hS ha hb hna hnb (u := true) _ (by bsimp [h10])
      (by bsimp [h11]) (by bsimp []) (by bsimp [hal]) fun R' hkp h10' => ?_
  all_goals bsimp []
  all_goals refine hk R' ((Keeps.mono hkp (by decide)).trans (by keeps_tac Keeps.refl _ _)) ?_
  all_goals rw [h10']
  all_goals simp [Dc.Num.cmp, cmpRes, NumRep.num, hna', hnb']

end Dc.Mach
