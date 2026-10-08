import Dc.Mach.Bc.DoSub
import Dc.BcModel.Karatsuba

/-!
# `_bc_shift_addsub` (`lib/number.c`, `isra` clone at `0x800040bc`)

```
800040bc count = val_len (a7), one less when val's first digit is 0
800040cc assert (accum len + scale >= shift + count) (80004244: __assert_fail)
800040e0 accp = accum value + len + scale - shift - 1 (a3), valp = val + len - 1 (a2)
800040fc sub == 0: 800041a4 add loop (800041c8), carry ripple (80004204)
80004100 sub != 0: subtract loop (80004120), borrow ripple (8000415c)
```

Arguments: `a0` the accumulator object, `a1` `val->n_len`, `a2`
`val->n_value`, `a3` the shift, `a4` the `sub` flag. The accumulator's digits
from the shifted position down are the little-endian list `accLE`; the
loops replace them with `addRip`/`subRip` of `val`'s little-endian digits
(`Dc/BcModel/Karatsuba.lean`). The ripple stores without a bound: the
caller supplies that no carry (borrow) leaves the accumulator
(`ShiftArgs.noCarry`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-! ## The model -/

/-- The add or subtract loops. -/
def ripOp (sub : Bool) : List Nat → List Nat → Nat → List Nat := if sub then subRip else addRip

/-- The carry (borrow) left past the accumulator. -/
def ripOut (sub : Bool) : List Nat → List Nat → Nat → Nat := if sub then subRipB else addRipC

/-- How many digits of `val` the loops read: `n_len`, one less when the
first digit is `0`. -/
def valCount (w : NumRep) : Nat := if w.ds.getD 0 0 = 0 then w.len - 1 else w.len

/-- `val`'s digits the loops read, little-endian. -/
def valLE (w : NumRep) : List Nat := ((w.ds.take w.len).reverse).take (valCount w)

/-- The accumulator's digits from the shifted position down, little-endian. -/
def accLE (y : NumRep) (shift : Nat) : List Nat := (y.ds.take (y.len + y.scale - shift)).reverse

/-- The accumulator's digits after `_bc_shift_addsub`. -/
def shiftDs (y w : NumRep) (shift : Nat) (sub : Bool) : List Nat :=
  (ripOp sub (accLE y shift) (valLE w) 0).reverse ++ y.ds.drop (y.len + y.scale - shift)

/-- `_bc_shift_addsub`'s precondition: `val` is a number of the heap, the
assertion holds, and no carry (borrow) leaves the accumulator. -/
structure ShiftArgs (L : List NumObj) (y w : NumObj) (shift : Nat) (sub : Bool) : Prop where
  mw : w ∈ L
  fit : shift + valCount w.rep ≤ y.rep.len + y.rep.scale
  noCarry : ripOut sub (accLE y.rep shift) (valLE w.rep) 0 = 0

/-! ## List bookkeeping -/

theorem valCount_le (w : NumRep) : valCount w ≤ w.len := by
  unfold valCount; split <;> omega

theorem valLE_length {w : NumRep} (hl : w.len ≤ w.ds.length) : (valLE w).length = valCount w := by
  have := valCount_le w
  simp only [valLE, List.length_take, List.length_reverse]; omega

/-- The digit the loops read after `j` steps. -/
theorem valLE_drop {w : NumRep} (hl : w.len ≤ w.ds.length) {j v : Nat} {vs : List Nat}
    (h : (valLE w).drop j = v :: vs) :
    j < valCount w ∧ v = w.ds.getD (w.len - 1 - j) 0 := by
  have hc := valCount_le w
  have hlen := valLE_length hl
  have hj : j < (valLE w).length := by
    rcases Nat.lt_or_ge j (valLE w).length with h' | h'
    · exact h'
    · rw [List.drop_eq_nil_of_le h'] at h; exact absurd h (by simp)
  refine ⟨by omega, ?_⟩
  rw [List.drop_eq_getElem_cons hj] at h
  obtain ⟨rfl, -⟩ := List.cons.inj h
  simp only [valLE, List.getElem_take, List.getElem_reverse, List.length_take]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  congr 1 <;> omega

/-- The accumulator before the loops. -/
theorem accLE_split (y : NumRep) (shift : Nat) :
    y.ds = (accLE y shift).reverse ++ y.ds.drop (y.len + y.scale - shift) := by
  rw [accLE, List.reverse_reverse, List.take_append_drop]

/-- One position stored. -/
theorem set_rev (xs D : List Nat) (a d : Nat) :
    (xs.reverse ++ a :: D).set xs.length d = xs.reverse ++ d :: D := by
  rw [List.set_append_right _ _ (by simp)]; simp

/-- The digit at the stored position. -/
theorem getD_rev (xs D : List Nat) (a : Nat) : (xs.reverse ++ a :: D).getD xs.length 0 = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp

theorem rev_cons_append (a : Nat) (xs D : List Nat) :
    (a :: xs).reverse ++ D = xs.reverse ++ a :: D := by simp

theorem length_rev_append (A D : List Nat) : (A.reverse ++ D).length = A.length + D.length := by
  simp

/-! ## Reading `val`'s digits with `lb` -/

theorem sext8_digit {d : Nat} (hd : d < 10) :
    sign_extend (m := 64) (BitVec.ofNat 8 d) = BitVec.ofNat 64 d := by
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨
    d = 9) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- The `lb` of a digit. -/
theorem NumAt.lb {Mt : Mem} {o : NumRep} (h : NumAt Mt o) {i : Nat} (hi : i < o.len + o.scale) :
    sign_extend (m := 64) (imgM Mt (o.val + i)) = BitVec.ofNat 64 (o.ds.getD i 0) := by
  rw [h.digit i hi]; exact sext8_digit (h.getD_lt i)

/-! ## Byte arithmetic -/

/-- `slliw r, r, 24; sraiw r, r, 24` on a word holding a small integer. -/
abbrev sext8w (x : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (shift_bits_right_arith
    (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.extractLsb 31 0 x <<< 24))) 24#5)

theorem sext8w_table : ∀ k : Fin 30,
    sext8w (BitVec.ofInt 64 ((k : Int) - 10)) = BitVec.ofInt 64 ((k : Int) - 10) := by decide

theorem sext8w_ofInt {u : Int} (h1 : -10 ≤ u) (h2 : u < 20) :
    BitVec.signExtend 64 (shift_bits_right_arith
      (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofInt 64 u) <<< 24)))
        24#5) = BitVec.ofInt 64 u := by
  have := sext8w_table ⟨(u + 10).toNat, by omega⟩
  simp only [Fin.val_mk] at this
  rwa [show ((u + 10).toNat : Int) - 10 = u by omega] at this

theorem sext8w_ofNat {k : Nat} (h : k < 20) :
    BitVec.signExtend 64 (shift_bits_right_arith
      (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 k) <<< 24)))
        24#5) = BitVec.ofNat 64 k := by
  rw [← ofInt_natCast64]; exact sext8w_ofInt (by omega) (by omega)

/-- `addiw r, r, -1` on a word holding a digit. -/
theorem addiwm1_nat {a : Nat} (h : a < 10) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (a + 18446744073709551615))) =
      BitVec.ofInt 64 ((a : Int) - 1) := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨
    a = 9) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-! ## The subtract loop -/

/-- The registers `_bc_shift_addsub` may change. -/
abbrev shClob : List Nat := [5, 6, 10, 11, 12, 13, 14, 15, 16, 17, 28]

/-- The accumulator's digit bytes. -/
abbrev accBytes (y : NumRep) (a : Nat) : Prop := y.val ≤ a ∧ a < y.val + y.len + y.scale

/-- The state through `_bc_shift_addsub`: registers off `shClob` and bytes
off the accumulator's digits unchanged. -/
structure ShSt (y : NumObj) (R0 : Nat → BitVec 64) (M0 : Mem) (R : Nat → BitVec 64) (M : Mem) :
    Prop where
  keeps : Keeps shClob R R0
  mem : MemOnly (accBytes y.rep) M M0

/-- The subtract loop's registers at `0x80004120`: `a2` at `val`'s digit,
`a1` at the accumulator's, `t1` where `a2` stops, `a6` the borrow, `a4 = 1`,
`a3`, `a7` as set before the loop. -/
structure SubRegs' (R : Nat → BitVec 64) (Pv Pa E c A3 A7 : Nat) : Prop where
  r12 : R 12 = BitVec.ofNat 64 Pv
  r11 : R 11 = BitVec.ofNat 64 Pa
  r6 : R 6 = BitVec.ofNat 64 E
  r16 : R 16 = BitVec.ofNat 64 c
  r14 : R 14 = 1#64
  r13 : R 13 = BitVec.ofNat 64 A3
  r17 : R 17 = BitVec.ofNat 64 A7

/-- One digit stored into the accumulator at the head of the heap. -/
theorem BcHeap.storeRev {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} (hyo : y.Owns) {xs D : List Nat} {a d : Nat}
    (hb : BcHeap S M H F (withDs y ((a :: xs).reverse ++ D) :: L))
    (hN : xs.length < y.rep.len + y.rep.scale) (hd : d < 10) {v : BitVec 64}
    (hv : sbData v = BitVec.ofNat 8 d) :
    BcHeap S (writeLog M [(y.rep.val + xs.length, 1, v)]) H F
      (withDs y (xs.reverse ++ d :: D) :: L) := by
  have hst := BcHeap.setDigit (L1 := []) hb (hb.head_noView hyo) (i := xs.length) (d := d)
    (by simpa only [withDs] using hN) hd hv
  simp only [withDs, List.nil_append] at hst ⊢
  rw [rev_cons_append, set_rev] at hst
  exact hst

/-- `ShSt` through one accumulator store. -/
theorem ShSt.store {y : NumObj} {R0 R R' : Nat → BitVec 64} {M0 M : Mem} (st : ShSt y R0 M0 R M)
    (hk : Keeps shClob R' R) {i : Nat} (hi : i < y.rep.len + y.rep.scale) (v : BitVec 64) :
    ShSt y R0 M0 R' (writeLog M [(y.rep.val + i, 1, v)]) :=
  ⟨hk.trans st.keeps, fun a ha => by
    rw [imgM_store_miss _ _ (by simp only [accBytes] at ha; omega)]; exact st.mem a ha⟩

/-- `ShSt` through register changes in `shClob`. -/
theorem ShSt.regs {y : NumObj} {R0 R R' : Nat → BitVec 64} {M0 M : Mem} (st : ShSt y R0 M0 R M)
    (hk : Keeps shClob R' R) : ShSt y R0 M0 R' M :=
  ⟨hk.trans st.keeps, st.mem⟩

/-- One position of the subtract loop at `0x80004120`: accumulator digit `a`
at `Pa`, `val`'s digit `v` at `Pv`, borrow `c` in. -/
theorem sub_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {xs D : List Nat} {a v c Pv Pa E A3 A7 : Nat}
    (hyo : y.Owns) (st : ShSt y R0 M0 R M)
    (hb : BcHeap S M H F (withDs y ((a :: xs).reverse ++ D) :: L))
    (sr : SubRegs' R Pv Pa E c A3 A7) (hPa : Pa = y.rep.val + xs.length)
    (hN : xs.length < y.rep.len + y.rep.scale)
    (lv : sign_extend (m := 64) (imgM M Pv) = BitVec.ofNat 64 v)
    (hv : v < 10) (ha : a < 10) (hc : c ≤ 1)
    (p1 : 2147603920 ≤ Pv) (p2 : Pv < 2273312768) (hE : E ≤ Pv)
    (hnext : Pv - 1 ≠ E → ∀ (R' : Nat → BitVec 64) (M' : Mem), ShSt y R0 M0 R' M' →
      BcHeap S M' H F (withDs y (xs.reverse ++
        (if a < v + c then a + 10 - v - c else a - v - c) :: D) :: L) →
      SubRegs' R' (Pv - 1) (Pa - 1) E (if a < v + c then 1 else 0) A3 A7 →
      DW live S Q 0x80004120#64 R' M')
    (hexit : Pv - 1 = E → ∀ (R' : Nat → BitVec 64) (M' : Mem), ShSt y R0 M0 R' M' →
      BcHeap S M' H F (withDs y (xs.reverse ++
        (if a < v + c then a + 10 - v - c else a - v - c) :: D) :: L) →
      SubRegs' R' (Pv - 1) (Pa - 1) E (if a < v + c then 1 else 0) A3 A7 →
      DW live S Q 0x80004158#64 R' M') :
    DW live S Q 0x80004120#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hn := hb.nums _ List.mem_cons_self
  have v1 := hn.shape.vLo; have v2 := hn.shape.vHi
  simp only [heapStart, heapEnd, withDs] at v1 v2
  have la := hn.lbu (i := xs.length) (by simpa only [withDs] using hN)
  simp only [withDs] at la
  rw [rev_cons_append, getD_rev, ← hPa] at la
  have h12 := sr.r12; have h11 := sr.r11; have h16 := sr.r16; have h14 := sr.r14
  have h6 := sr.r6; have h13 := sr.r13; have h17 := sr.r17
  by_cases hlt : a < v + c
  · simp only [if_pos hlt] at hnext hexit
    bc_run hlive hS [h12, h11, h16, h14, lv, la, addw_ofNat, subw_nat, sext8w_ofInt,
      toInt_ofInt64, BitVec.toInt_zero] at 0x80004150
    · intro hneg; omega
    · intro _
      bc_run hlive hS [h12, h11, h16, h14, addiw10_int] at 0x80004150
      have hb' := BcHeap.storeRev hyo hb hN (d := a + 10 - v - c) (by omega)
        (v := BitVec.ofNat 64 ((↑a - ↑(v + c) + 10 : Int).toNat)) (by rw [sbData_ofNat]; congr 1; omega)
      bc_run hlive hS [h12, h11, h6] at 0x80004120 0x80004158
      all_goals intro hc
      all_goals rw [show Pa - 1 + 1 = y.rep.val + xs.length by omega]
      · exact hnext (fun e => hc (by rw [e])) _ _ (st.store (by keeps_tac Keeps.refl _ _) hN _) hb'
          ⟨by bsimp [], by bsimp [], by bsimp [h6], by bsimp [], by bsimp [h14], by bsimp [h13],
            by bsimp [h17]⟩
      · bv_nat at hc
        exact hexit (by omega) _ _ (st.store (by keeps_tac Keeps.refl _ _) hN _) hb'
          ⟨by bsimp [], by bsimp [], by bsimp [h6], by bsimp [], by bsimp [h14], by bsimp [h13],
            by bsimp [h17]⟩
  · simp only [if_neg hlt] at hnext hexit
    bc_run hlive hS [h12, h11, h16, h14, lv, la, addw_ofNat, subw_nat, sext8w_ofInt,
      toInt_ofInt64, BitVec.toInt_zero] at 0x80004150
    · intro _
      have hb' := BcHeap.storeRev hyo hb hN (d := a - v - c) (by omega)
        (v := BitVec.ofInt 64 (↑a - ↑(v + c))) (by rw [ofInt_nonneg (by omega), sbData_ofNat]; congr 1; omega)
      bc_run hlive hS [h12, h11, h6] at 0x80004120 0x80004158
      all_goals intro hc
      all_goals rw [show Pa - 1 + 1 = y.rep.val + xs.length by omega]
      · exact hnext (fun e => hc (by rw [e])) _ _ (st.store (by keeps_tac Keeps.refl _ _) hN _) hb'
          ⟨by bsimp [], by bsimp [], by bsimp [h6], by bsimp [], by bsimp [h14], by bsimp [h13],
            by bsimp [h17]⟩
      · bv_nat at hc
        exact hexit (by omega) _ _ (st.store (by keeps_tac Keeps.refl _ _) hN _) hb'
          ⟨by bsimp [], by bsimp [], by bsimp [h6], by bsimp [], by bsimp [h14], by bsimp [h13],
            by bsimp [h17]⟩
    · intro hneg; omega

/-- A heap is a property of the memory image. -/
theorem BcHeap.congr {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    (h : BcHeap S M H F L) (he : ∀ a, imgM M' a = imgM M a) : BcHeap S M' H F L :=
  h.transport (fun a _ => he a) (fun _ _ a _ => he a) (fun j _ => he _)

theorem se9 : BitVec.signExtend 64 (BitVec.extractLsb 31 0 9#64) = 9#64 := by decide

/-- `_bc_shift_addsub`'s return: the accumulator's digits now `ds`. -/
def ShRet (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (H : Heap) (F : List Blk) (L : List NumObj) (y : NumObj) (R0 : Nat → BitVec 64) (M0 : Mem)
    (ds : List Nat) : Prop :=
  ∀ R' M', ShSt y R0 M0 R' M' → BcHeap S M' H F (withDs y ds :: L) → DW live S Q (R0 1) R' M'

/-- The borrow ripple's loop at `0x8000417c`: digit `0` at `P` already
stored as `-1` over the heap's image `M1`; `a4 = 0`, `a5 = P`. -/
theorem sub_rip_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 : Mem} {R0 : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} (hyo : y.Owns) (hal : (R0 1).toNat % 4 = 0) :
    ∀ (rest D : List Nat) (R : Nat → BitVec 64) (M M1 : Mem), ShSt y R0 M0 R M →
      BcHeap S M1 H F (withDs y ((0 :: rest).reverse ++ D) :: L) →
      (∀ a, a ≠ y.rep.val + rest.length → imgM M a = imgM M1 a) →
      rest.length < y.rep.len + y.rep.scale →
      R 14 = BitVec.ofNat 64 0 → R 15 = BitVec.ofNat 64 (y.rep.val + rest.length) →
      subRipB rest [] 1 = 0 →
      ShRet live S Q H F L y R0 M0 ((subRip (0 :: rest) [] 1).reverse ++ D) →
      DW live S Q 0x8000417c#64 R M := by
  intro rest
  induction rest with
  | nil => intro D R M M1 _ _ _ _ _ _ hnc; simp [subRipB] at hnc
  | cons b rest ih =>
  intro D R M M1 st hb hag hN h14 h15 hnc hk
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hn := hb.nums _ List.mem_cons_self
  have v1 := hn.shape.vLo; have v2 := hn.shape.vHi
  simp only [heapStart, heapEnd, withDs] at v1 v2
  simp only [List.length_cons] at hN h15 hag
  have hb9a := BcHeap.storeRev hyo hb (xs := b :: rest) (by simpa using hN) (d := 9) (by omega)
    (v := 9#64) (by decide)
  simp only [List.length_cons] at hb9a
  have hb9 := hb9a.congr (M' := writeLog M [(y.rep.val + (rest.length + 1), 1, 9#64)])
    fun a => by
      by_cases e : a = y.rep.val + (rest.length + 1)
      · subst e; rw [imgM_sb, imgM_sb]
      · rw [imgM_store_miss _ _ (by simp only [widthOfM] at *; omega),
          imgM_store_miss _ _ (by simp only [widthOfM] at *; omega)]
        exact hag a e
  have hn9 := hb9.nums _ List.mem_cons_self
  have lb := hn9.lbu (i := rest.length) (by simp only [withDs]; omega)
  simp only [withDs, List.length_cons] at lb
  rw [rev_cons_append, getD_rev] at lb
  have hbl : b < 10 := by
    have := hn9.getD_lt rest.length
    simp only [withDs, List.length_cons] at this
    rwa [rev_cons_append, getD_rev] at this
  have hPm : y.rep.val + (rest.length + 1) - 1 = y.rep.val + rest.length := by omega
  have hb' := hn9.shape.vLo
  bc_run hlive hS [h14, h15, se9] at 0x80004184
  bc_run hlive hS [h15, word_pred (k := y.rep.val + (rest.length + 1)) (by omega), hPm, lb,
    addiwm1_nat hbl, sext8w_ofInt, toInt_ofInt64, BitVec.toInt_zero]
  · intro hc
    have hb0 : b = 0 := by omega
    subst hb0
    refine ih (9 :: D) _ _ _ ((st.store (by keeps_tac Keeps.refl _ _) hN _).store
      (by keeps_tac Keeps.refl _ _) (i := rest.length) (by omega) _) hb9
      (fun a ha => imgM_store_miss _ _ (by omega)) (by omega)
      (by bsimp []) (by bsimp []) (by simpa [subRipB] using hnc) ?_
    have e : subRip (0 :: 0 :: rest) [] 1 = 9 :: subRip (0 :: rest) [] 1 := by simp [subRip]
    rw [e, rev_cons_append] at hk
    exact hk
  · intro hc
    have hb1 : ¬ b < 1 := by omega
    have hbs := BcHeap.storeRev hyo hb9 (xs := rest) (by omega) (d := b - 1)
      (by omega) (v := BitVec.ofInt 64 ((b : Int) - 1))
      (by rw [ofInt_nonneg (by omega), sbData_ofNat]; congr 1; omega)
    have h1 : R 1 = R0 1 := st.keeps.get 1
    bc_run hlive hS [h1, hal]
    have e : subRip (0 :: b :: rest) [] 1 = 9 :: (b - 1) :: rest := by simp [subRip, hb1]
    rw [e, rev_cons_append, rev_cons_append] at hk
    exact hk _ _ ((st.store (by keeps_tac Keeps.refl _ _) hN _).store
      (by keeps_tac Keeps.refl _ _) (i := rest.length) (by omega) _) hbs

theorem subRip_nil_zero (xs : List Nat) : subRip xs [] 0 = xs := by
  cases xs <;> simp [subRip]

/-- After the subtract loop at `0x80004158`: borrow `c` in `a6`, the
accumulator's unprocessed digits `xs` (little-endian) below position
`A3 - A7`. -/
theorem sub_rip {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {xs D : List Nat} {c A3 A7 : Nat} (hyo : y.Owns) (hal : (R0 1).toNat % 4 = 0)
    (st : ShSt y R0 M0 R M) (hb : BcHeap S M H F (withDs y (xs.reverse ++ D) :: L))
    (hN : xs.length ≤ y.rep.len + y.rep.scale) (hc : c ≤ 1)
    (h16 : R 16 = BitVec.ofNat 64 c) (h13 : R 13 = BitVec.ofNat 64 A3)
    (h17 : R 17 = BitVec.ofNat 64 A7) (hP : A3 = y.rep.val + xs.length + A7)
    (hA3 : A3 < 2 ^ 63) (hnc : subRipB xs [] c = 0)
    (hk : ShRet live S Q H F L y R0 M0 ((subRip xs [] c).reverse ++ D)) :
    DW live S Q 0x80004158#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h1 : R 1 = R0 1 := st.keeps.get 1
  have hn := hb.nums _ List.mem_cons_self
  have v1 := hn.shape.vLo; have v2 := hn.shape.vHi
  simp only [heapStart, heapEnd, withDs] at v1 v2
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · bc_run hlive hS [h16]
    bc_run hlive hS [h1, hal]
    rw [subRip_nil_zero] at hk
    exact hk _ _ st hb
  rcases xs with _ | ⟨b, rest⟩
  · simp [subRipB] at hnc
  simp only [List.length_cons] at hN hP
  have lb := hn.lbu (i := rest.length) (by simp only [withDs]; omega)
  simp only [withDs] at lb
  rw [rev_cons_append, getD_rev] at lb
  have hbl : b < 10 := by
    have := hn.getD_lt rest.length
    simp only [withDs] at this
    rwa [rev_cons_append, getD_rev] at this
  have hPm : A3 - 1 - A7 = y.rep.val + rest.length := by omega
  bc_run hlive hS [h16, h13, h17] at 0x80004164
  bc_run hlive hS [h16, h13, h17, sub_ofNat, hPm, lb, addiwm1_nat hbl, sext8w_ofInt,
    toInt_ofInt64, BitVec.toInt_zero] at 0x80004178
  bc_run hlive hS [toInt_ofInt64, BitVec.toInt_zero] at 0x8000417c 0x8000423c
  · intro hc
    have hb1 : ¬ b < 1 := by omega
    have hbs := BcHeap.storeRev hyo hb (xs := rest) (by omega) (d := b - 1)
      (by omega) (v := BitVec.ofInt 64 ((b : Int) - 1))
      (by rw [ofInt_nonneg (by omega), sbData_ofNat]; congr 1; omega)
    bc_run hlive hS [h1, hal]
    have e : subRip (b :: rest) [] 1 = (b - 1) :: rest := by simp [subRip, hb1]
    rw [e, rev_cons_append] at hk
    exact hk _ _ (st.store (by keeps_tac Keeps.refl _ _) (i := rest.length) (by omega) _) hbs
  · intro hc
    have hb0 : b = 0 := by omega
    subst hb0
    exact sub_rip_loop hlive hyo hal rest D _ _ M
      (st.store (by keeps_tac Keeps.refl _ _) (i := rest.length) (by omega) _) hb
      (fun a ha => imgM_store_miss _ _ (by omega)) (by omega) (by bsimp []) (by bsimp [])
      (by simpa [subRipB] using hnc) hk

/-- The subtract loop from `0x80004120`: `val`'s digits `V` from step `j`
on, the accumulator's unprocessed digits `a :: xs`, borrow `c`. -/
theorem sub_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 : Mem} {R0 : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y w : NumObj} {E A3 A7 : Nat} (hyo : y.Owns) (hal : (R0 1).toNat % 4 = 0) (hw : w ∈ L)
    (hA3 : A3 < 2 ^ 63) :
    ∀ (V : List Nat) (j a : Nat) (xs D : List Nat) (c : Nat) (R : Nat → BitVec 64) (M : Mem),
      (valLE w.rep).drop j = V → 0 < V.length → V.length ≤ xs.length + 1 →
      ShSt y R0 M0 R M → BcHeap S M H F (withDs y ((a :: xs).reverse ++ D) :: L) →
      SubRegs' R (w.rep.val + (w.rep.len - 1 - j)) (y.rep.val + xs.length) E c A3 A7 →
      E + V.length = w.rep.val + (w.rep.len - 1 - j) →
      A3 = y.rep.val + (xs.length + 1 - V.length) + A7 →
      xs.length < y.rep.len + y.rep.scale → c ≤ 1 →
      subRipB (a :: xs) V c = 0 →
      ShRet live S Q H F L y R0 M0 ((subRip (a :: xs) V c).reverse ++ D) →
      DW live S Q 0x80004120#64 R M := by
  intro V
  induction V with
  | nil => intro _ _ _ _ _ _ _ _ hV; simp at hV
  | cons v vs ih =>
  intro j a xs D c R M hV _ hVx st hb sr hE hP hN hc hnc hk
  have hwm : w ∈ withDs y ((a :: xs).reverse ++ D) :: L := List.mem_cons_of_mem _ hw
  have hnw := hb.nums w hwm
  have hdl := hnw.shape.dsLen
  have ⟨hjc, hvj⟩ := valLE_drop (by omega) hV
  have hcl := valCount_le w.rep
  have lv := hnw.lb (i := w.rep.len - 1 - j) (by omega)
  rw [← hvj] at lv
  have hvl : v < 10 := by have := hnw.getD_lt (w.rep.len - 1 - j); rw [← hvj] at this; exact this
  have hn := hb.nums _ List.mem_cons_self
  have hal0 : (y.rep.val + xs.length) = y.rep.val + xs.length := rfl
  have hal1 : a < 10 := by
    have := hn.getD_lt xs.length
    simp only [withDs] at this
    rwa [rev_cons_append, getD_rev] at this
  have w1 := hnw.shape.vLo; have w2 := hnw.shape.vHi
  simp only [heapStart, heapEnd] at w1 w2
  simp only [List.length_cons] at hVx hE hP
  have hlen : (valLE w.rep).length - j = vs.length + 1 := by
    rw [← List.length_drop, hV]; rfl
  have hvc := valLE_length (w := w.rep) (by omega)
  refine sub_body hlive hyo st hb sr rfl hN lv hvl hal1 hc (by omega) (by omega) (by omega)
    ?_ ?_
  · intro hpe R' M' st' hb' sr'
    rcases xs with _ | ⟨a', xs'⟩
    · simp only [List.length_nil] at hVx; omega
    simp only [List.length_cons] at hVx hE hP hN sr' ⊢
    rw [show w.rep.val + (w.rep.len - 1 - j) - 1 = w.rep.val + (w.rep.len - 1 - (j + 1)) by omega,
      show y.rep.val + (xs'.length + 1) - 1 = y.rep.val + xs'.length by omega] at sr'
    have hV' : (valLE w.rep).drop (j + 1) = vs := by
      rw [← List.drop_drop, hV]; rfl
    by_cases hlt : a < v + c
    all_goals simp only [subRip, subRipB, hlt, if_true, if_false] at hnc hk hb' sr'
    all_goals rw [rev_cons_append] at hk
    all_goals
      exact ih (j + 1) a' xs' _ _ R' M' hV' (by omega) (by omega) st' hb' sr' (by omega)
        (by omega) (by omega) (by decide) hnc hk
  · intro hpe R' M' st' hb' sr'
    have hvs : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hvs
    simp only [List.length_nil] at hP
    by_cases hlt : a < v + c
    all_goals simp only [subRip, subRipB, hlt, if_true, if_false] at hnc hk hb' sr'
    all_goals rw [rev_cons_append] at hk
    all_goals
      exact sub_rip hlive hyo hal st' hb' (by omega) (by decide) sr'.r16 sr'.r13 sr'.r17
        (by omega) hA3 hnc hk

/-! ## The add loop -/

/-- The add loop's registers at `0x800041c8`: `a2` at `val`'s digit, `a4`
at the accumulator's, `a6` where `a2` stops, `a0` the carry, `t1 = 9`,
`a3`, `a7` as set before the loop. -/
structure AddRegs' (R : Nat → BitVec 64) (Pv Pa E c A3 A7 : Nat) : Prop where
  r12 : R 12 = BitVec.ofNat 64 Pv
  r14 : R 14 = BitVec.ofNat 64 Pa
  r16 : R 16 = BitVec.ofNat 64 E
  r10 : R 10 = BitVec.ofNat 64 c
  r6 : R 6 = BitVec.ofNat 64 9
  r13 : R 13 = BitVec.ofNat 64 A3
  r17 : R 17 = BitVec.ofNat 64 A7

/-- One position of the add loop at `0x800041c8`: accumulator digit `a` at
`Pa`, `val`'s digit `v` at `Pv`, carry `c` in. -/
theorem add_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {xs D : List Nat} {a v c Pv Pa E A3 A7 : Nat}
    (hyo : y.Owns) (st : ShSt y R0 M0 R M)
    (hb : BcHeap S M H F (withDs y ((a :: xs).reverse ++ D) :: L))
    (sr : AddRegs' R Pv Pa E c A3 A7) (hPa : Pa = y.rep.val + xs.length)
    (hN : xs.length < y.rep.len + y.rep.scale)
    (lv : sign_extend (m := 64) (imgM M Pv) = BitVec.ofNat 64 v)
    (hv : v < 10) (ha : a < 10) (hc : c ≤ 1)
    (p1 : 2147603920 ≤ Pv) (p2 : Pv < 2273312768) (hE : E ≤ Pv)
    (hnext : Pv - 1 ≠ E → ∀ (R' : Nat → BitVec 64) (M' : Mem), ShSt y R0 M0 R' M' →
      BcHeap S M' H F (withDs y (xs.reverse ++
        (if 9 < a + v + c then a + v + c - 10 else a + v + c) :: D) :: L) →
      AddRegs' R' (Pv - 1) (Pa - 1) E (if 9 < a + v + c then 1 else 0) A3 A7 →
      DW live S Q 0x800041c8#64 R' M')
    (hexit : Pv - 1 = E → ∀ (R' : Nat → BitVec 64) (M' : Mem), ShSt y R0 M0 R' M' →
      BcHeap S M' H F (withDs y (xs.reverse ++
        (if 9 < a + v + c then a + v + c - 10 else a + v + c) :: D) :: L) →
      AddRegs' R' (Pv - 1) (Pa - 1) E (if 9 < a + v + c then 1 else 0) A3 A7 →
      DW live S Q 0x80004200#64 R' M') :
    DW live S Q 0x800041c8#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hn := hb.nums _ List.mem_cons_self
  have v1 := hn.shape.vLo; have v2 := hn.shape.vHi
  simp only [heapStart, heapEnd, withDs] at v1 v2
  have la := hn.lbu (i := xs.length) (by simpa only [withDs] using hN)
  simp only [withDs] at la
  rw [rev_cons_append, getD_rev, ← hPa] at la
  have h12 := sr.r12; have h14 := sr.r14; have h16 := sr.r16; have h10 := sr.r10
  have h6 := sr.r6; have h13 := sr.r13; have h17 := sr.r17
  have hPa1 : Pa - 1 + 1 = y.rep.val + xs.length := by omega
  bc_run hlive hS [h12, h14, h10, h6, lv, la, addw_ofNat, sext8w_ofNat, toInt_ofNat_small] at 0x800041f8
  · intro hc'
    have hle : ¬ 9 < a + v + c := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hc'); omega
    simp only [if_neg hle] at hnext hexit
    have hb' := BcHeap.storeRev hyo hb hN (d := a + v + c) (by omega)
      (v := BitVec.ofNat 64 (v + c + a)) (by rw [sbData_ofNat]; congr 1; omega)
    bc_run hlive hS [h12, h14, h16] at 0x800041c8 0x80004200
    all_goals intro hc
    all_goals rw [hPa1]
    · exact hnext (fun e => hc (by rw [e])) _ _ (st.store (by keeps_tac Keeps.refl _ _) hN _) hb'
        ⟨by bsimp [], by bsimp [], by bsimp [h16], by bsimp [], by bsimp [h6], by bsimp [h13],
          by bsimp [h17]⟩
    · bv_nat at hc
      exact hexit (by omega) _ _ (st.store (by keeps_tac Keeps.refl _ _) hN _) hb'
        ⟨by bsimp [], by bsimp [], by bsimp [h16], by bsimp [], by bsimp [h6], by bsimp [h13],
          by bsimp [h17]⟩
  · intro hc'
    have hgt : 9 < a + v + c := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hc'); omega
    simp only [if_pos hgt] at hnext hexit
    have e10 : v + c + a - 10 = a + v + c - 10 := by omega
    have hb' := BcHeap.storeRev hyo hb hN (d := a + v + c - 10) (by omega)
      (v := BitVec.ofNat 64 (a + v + c - 10)) (by rw [sbData_ofNat])
    bc_run hlive hS [h12, h14, h6, se12_ff6, word_sub10 (k := v + c + a) (by omega), e10,
      sxw_ofNat] at 0x800041f8
    bc_run hlive hS [h12, h14, h16] at 0x800041c8 0x80004200
    all_goals intro hc
    all_goals rw [hPa1]
    · exact hnext (fun e => hc (by rw [e])) _ _ (st.store (by keeps_tac Keeps.refl _ _) hN _) hb'
        ⟨by bsimp [], by bsimp [], by bsimp [h16], by bsimp [], by bsimp [h6], by bsimp [h13],
          by bsimp [h17]⟩
    · bv_nat at hc
      exact hexit (by omega) _ _ (st.store (by keeps_tac Keeps.refl _ _) hN _) hb'
        ⟨by bsimp [], by bsimp [], by bsimp [h16], by bsimp [], by bsimp [h6], by bsimp [h13],
          by bsimp [h17]⟩

theorem se12_ff7 : sign_extend (m := 64) (0xff7#12) = 18446744073709551607#64 := by decide

/-- `addiw r, r, -9` on a word of at least 9. -/
theorem word_sub9 {k : Nat} (h : 9 ≤ k) :
    BitVec.ofNat 64 k + 18446744073709551607#64 = BitVec.ofNat 64 (k - 9) := by
  change BitVec.ofNat 64 k + -(9#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le k 9 (by decide) h

/-- The carry ripple's head at `0x80004228` when the digit `b` absorbs the
carry. -/
theorem add_rip_done {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {rest D : List Nat} {b : Nat} (hyo : y.Owns) (hal : (R0 1).toNat % 4 = 0)
    (st : ShSt y R0 M0 R M) (hb : BcHeap S M H F (withDs y ((b :: rest).reverse ++ D) :: L))
    (hN : rest.length < y.rep.len + y.rep.scale) (hb8 : b + 1 ≤ 9)
    (h14 : R 14 = BitVec.ofNat 64 b) (h15 : R 15 = BitVec.ofNat 64 (y.rep.val + rest.length))
    (h12 : R 12 = BitVec.ofNat 64 9)
    (hk : ShRet live S Q H F L y R0 M0 ((addRip (b :: rest) [] 1).reverse ++ D)) :
    DW live S Q 0x80004228#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h1 : R 1 = R0 1 := st.keeps.get 1
  have hn := hb.nums _ List.mem_cons_self
  have v1 := hn.shape.vLo; have v2 := hn.shape.vHi
  simp only [heapStart, heapEnd, withDs] at v1 v2
  bc_run hlive hS [h14, h15, h12, sxw_ofNat, sext8w_ofNat, toInt_ofNat_small] at 0x8000423c
  · intro hc; exfalso; (try simp (disch := omega) only [toInt_ofNat_small] at hc); omega
  · intro _
    have hbs := BcHeap.storeRev hyo hb (xs := rest) hN (d := b + 1) (by omega)
      (v := BitVec.ofNat 64 (b + 1)) (sbData_ofNat _)
    bc_run hlive hS [h1, hal]
    have e : addRip (b :: rest) [] 1 = (b + 1) :: rest := by
      simp [addRip, show ¬ 9 < b + 1 by omega]
    rw [e, rev_cons_append] at hk
    exact hk _ _ (st.store (by keeps_tac Keeps.refl _ _) hN _) hbs

/-- The carry ripple from `0x80004228`: digit `b` at `a5` loaded into `a4`,
carry `1`. -/
theorem add_rip_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 : Mem} {R0 : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} (hyo : y.Owns) (hal : (R0 1).toNat % 4 = 0) :
    ∀ (rest : List Nat) (b : Nat) (D : List Nat) (R : Nat → BitVec 64) (M : Mem),
      ShSt y R0 M0 R M → BcHeap S M H F (withDs y ((b :: rest).reverse ++ D) :: L) →
      rest.length < y.rep.len + y.rep.scale →
      R 14 = BitVec.ofNat 64 b → R 15 = BitVec.ofNat 64 (y.rep.val + rest.length) →
      R 12 = BitVec.ofNat 64 9 → addRipC (b :: rest) [] 1 = 0 →
      ShRet live S Q H F L y R0 M0 ((addRip (b :: rest) [] 1).reverse ++ D) →
      DW live S Q 0x80004228#64 R M := by
  intro rest
  induction rest with
  | nil =>
    intro b D R M st hb hN h14 h15 h12 hnc hk
    have hb8 : b + 1 ≤ 9 := by
      rcases Nat.lt_or_ge 9 (b + 1) with h | h
      · simp [addRipC, h] at hnc
      · exact h
    exact add_rip_done hlive hyo hal st hb hN hb8 h14 h15 h12 hk
  | cons b' rest ih =>
  intro b D R M st hb hN h14 h15 h12 hnc hk
  by_cases hb8 : b + 1 ≤ 9
  · exact add_rip_done hlive hyo hal st hb hN hb8 h14 h15 h12 hk
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hn := hb.nums _ List.mem_cons_self
  have v1 := hn.shape.vLo; have v2 := hn.shape.vHi
  simp only [heapStart, heapEnd, withDs] at v1 v2
  have hbl : b < 10 := by
    have := hn.getD_lt (b' :: rest).length
    simp only [withDs] at this
    rwa [rev_cons_append, getD_rev] at this
  have hb9 : b - 9 = 0 := by omega
  simp only [List.length_cons] at hN h15
  bc_run hlive hS [h14, h15, h12, sxw_ofNat, sext8w_ofNat, toInt_ofNat_small] at 0x80004218
    0x8000423c
  rotate_left
  · intro hc; exfalso; (try simp (disch := omega) only [toInt_ofNat_small] at hc); omega
  intro _
  have hb0a := BcHeap.storeRev hyo hb (xs := b' :: rest) (by simpa using hN) (d := 0) (by omega)
    (v := 0#64) (by decide)
  simp only [List.length_cons] at hb0a
  have hb0 := hb0a.congr (M' := writeLog (writeLog M [(y.rep.val + (rest.length + 1), 1,
      BitVec.ofNat 64 (b + 1))]) [(y.rep.val + (rest.length + 1), 1, 0#64)])
    fun a => by
      by_cases e : a = y.rep.val + (rest.length + 1)
      · subst e; rw [imgM_sb, imgM_sb]
      · rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
          imgM_store_miss _ _ (by omega)]
  have hn0 := hb0.nums _ List.mem_cons_self
  have lb := hn0.lbu (i := rest.length) (by simp only [withDs]; omega)
  simp only [withDs] at lb
  rw [rev_cons_append, getD_rev] at lb
  have hPm : y.rep.val + (rest.length + 1) - 1 = y.rep.val + rest.length := by omega
  bc_run hlive hS [h14, h15, h12, se12_ff7, word_sub9 (k := b) (by omega), hb9,
    word_pred (k := y.rep.val + (rest.length + 1)) (by omega), hPm, lb] at 0x80004228
  have hgt : 9 < b + 1 := by omega
  simp only [addRip, addRipC, hgt, if_true, show b + 1 - 10 = 0 by omega,
    show ((1 : Nat) = 0) = False by decide, if_false] at hnc hk
  rw [rev_cons_append] at hk
  exact ih b' (0 :: D) _ _ ((st.store (by keeps_tac Keeps.refl _ _) hN _).store
    (by keeps_tac Keeps.refl _ _) hN _) hb0 (by omega) (by bsimp []) (by bsimp [])
    (by bsimp [h12]) hnc hk

theorem addRip_nil_zero (xs : List Nat) : addRip xs [] 0 = xs := by
  cases xs <;> simp [addRip]

/-- After the add loop at `0x80004200`: carry `c` in `a0`, the
accumulator's unprocessed digits `xs` (little-endian) below position
`A3 - A7`. -/
theorem add_rip {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {xs D : List Nat} {c A3 A7 : Nat} (hyo : y.Owns) (hal : (R0 1).toNat % 4 = 0)
    (st : ShSt y R0 M0 R M) (hb : BcHeap S M H F (withDs y (xs.reverse ++ D) :: L))
    (hN : xs.length ≤ y.rep.len + y.rep.scale) (hc : c ≤ 1)
    (h10 : R 10 = BitVec.ofNat 64 c) (h13 : R 13 = BitVec.ofNat 64 A3)
    (h17 : R 17 = BitVec.ofNat 64 A7) (hP : A3 = y.rep.val + xs.length + A7)
    (hA3 : A3 < 2 ^ 63) (hnc : addRipC xs [] c = 0)
    (hk : ShRet live S Q H F L y R0 M0 ((addRip xs [] c).reverse ++ D)) :
    DW live S Q 0x80004200#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h1 : R 1 = R0 1 := st.keeps.get 1
  have hn := hb.nums _ List.mem_cons_self
  have v1 := hn.shape.vLo; have v2 := hn.shape.vHi
  simp only [heapStart, heapEnd, withDs] at v1 v2
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · bc_run hlive hS [h10]
    bc_run hlive hS [h1, hal]
    rw [addRip_nil_zero] at hk
    exact hk _ _ st hb
  rcases xs with _ | ⟨b, rest⟩
  · simp [addRipC] at hnc
  simp only [List.length_cons] at hN hP
  have lb := hn.lbu (i := rest.length) (by simp only [withDs]; omega)
  simp only [withDs] at lb
  rw [rev_cons_append, getD_rev] at lb
  have hPm : A3 - 1 - A7 = y.rep.val + rest.length := by omega
  bc_run hlive hS [h10, h13, h17] at 0x80004208
  bc_run hlive hS [h13, h17, sub_ofNat, hPm, lb] at 0x80004228
  exact add_rip_loop hlive hyo hal rest b D _ _ (st.regs (by keeps_tac Keeps.refl _ _)) hb (by omega) (by bsimp []) (by bsimp [])
    (by bsimp []) hnc hk

/-- The add loop from `0x800041c8`: `val`'s digits `V` from step `j` on, the
accumulator's unprocessed digits `a :: xs`, carry `c`. -/
theorem add_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 : Mem} {R0 : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y w : NumObj} {E A3 A7 : Nat} (hyo : y.Owns) (hal : (R0 1).toNat % 4 = 0) (hw : w ∈ L)
    (hA3 : A3 < 2 ^ 63) :
    ∀ (V : List Nat) (j a : Nat) (xs D : List Nat) (c : Nat) (R : Nat → BitVec 64) (M : Mem),
      (valLE w.rep).drop j = V → 0 < V.length → V.length ≤ xs.length + 1 →
      ShSt y R0 M0 R M → BcHeap S M H F (withDs y ((a :: xs).reverse ++ D) :: L) →
      AddRegs' R (w.rep.val + (w.rep.len - 1 - j)) (y.rep.val + xs.length) E c A3 A7 →
      E + V.length = w.rep.val + (w.rep.len - 1 - j) →
      A3 = y.rep.val + (xs.length + 1 - V.length) + A7 →
      xs.length < y.rep.len + y.rep.scale → c ≤ 1 →
      addRipC (a :: xs) V c = 0 →
      ShRet live S Q H F L y R0 M0 ((addRip (a :: xs) V c).reverse ++ D) →
      DW live S Q 0x800041c8#64 R M := by
  intro V
  induction V with
  | nil => intro _ _ _ _ _ _ _ _ hV; simp at hV
  | cons v vs ih =>
  intro j a xs D c R M hV _ hVx st hb sr hE hP hN hc hnc hk
  have hwm : w ∈ withDs y ((a :: xs).reverse ++ D) :: L := List.mem_cons_of_mem _ hw
  have hnw := hb.nums w hwm
  have hdl := hnw.shape.dsLen
  have ⟨hjc, hvj⟩ := valLE_drop (by omega) hV
  have hcl := valCount_le w.rep
  have lv := hnw.lb (i := w.rep.len - 1 - j) (by omega)
  rw [← hvj] at lv
  have hvl : v < 10 := by have := hnw.getD_lt (w.rep.len - 1 - j); rw [← hvj] at this; exact this
  have hn := hb.nums _ List.mem_cons_self
  have hal1 : a < 10 := by
    have := hn.getD_lt xs.length
    simp only [withDs] at this
    rwa [rev_cons_append, getD_rev] at this
  have w1 := hnw.shape.vLo; have w2 := hnw.shape.vHi
  simp only [heapStart, heapEnd] at w1 w2
  simp only [List.length_cons] at hVx hE hP
  have hlen : (valLE w.rep).length - j = vs.length + 1 := by
    rw [← List.length_drop, hV]; rfl
  have hvc := valLE_length (w := w.rep) (by omega)
  refine add_body hlive hyo st hb sr rfl hN lv hvl hal1 hc (by omega) (by omega) (by omega)
    ?_ ?_
  · intro hpe R' M' st' hb' sr'
    rcases xs with _ | ⟨a', xs'⟩
    · simp only [List.length_nil] at hVx; omega
    simp only [List.length_cons] at hVx hE hP hN sr' ⊢
    rw [show w.rep.val + (w.rep.len - 1 - j) - 1 = w.rep.val + (w.rep.len - 1 - (j + 1)) by omega,
      show y.rep.val + (xs'.length + 1) - 1 = y.rep.val + xs'.length by omega] at sr'
    have hV' : (valLE w.rep).drop (j + 1) = vs := by
      rw [← List.drop_drop, hV]; rfl
    by_cases hlt : 9 < a + v + c
    all_goals simp only [addRip, addRipC, hlt, if_true, if_false] at hnc hk hb' sr'
    all_goals rw [rev_cons_append] at hk
    all_goals
      exact ih (j + 1) a' xs' _ _ R' M' hV' (by omega) (by omega) st' hb' sr' (by omega)
        (by omega) (by omega) (by decide) hnc hk
  · intro hpe R' M' st' hb' sr'
    have hvs : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hvs
    simp only [List.length_nil] at hP
    by_cases hlt : 9 < a + v + c
    all_goals simp only [addRip, addRipC, hlt, if_true, if_false] at hnc hk hb' sr'
    all_goals rw [rev_cons_append] at hk
    all_goals
      exact add_rip hlive hyo hal st' hb' (by omega) (by decide) sr'.r10 sr'.r13 sr'.r17
        (by omega) hA3 hnc hk

/-! ## `_bc_shift_addsub` -/

theorem bv_acc {n : Nat} (x y z o : BitVec n) : x - y + -o + z = (x + z) - (y + o) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.sub_eq_add_neg]; ac_rfl

/-- The accumulator's last position `a3`. -/
theorem acc_ptr {v a b c : Nat} (h : b + 1 ≤ a + c) (hb : b < 2 ^ 63) :
    BitVec.ofNat 64 v + (BitVec.ofNat 64 a - BitVec.ofNat 64 b + 18446744073709551615#64 +
      BitVec.ofNat 64 c) = BitVec.ofNat 64 (v + (a + c - b - 1)) := by
  change BitVec.ofNat 64 v + (BitVec.ofNat 64 a - BitVec.ofNat 64 b + -(1#64) +
      BitVec.ofNat 64 c) = _
  rw [bv_acc, BitVec.ofNat_add_ofNat, show (1#64) = BitVec.ofNat 64 1 from rfl,
    BitVec.ofNat_add_ofNat, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) h,
    BitVec.ofNat_add_ofNat]
  congr 1 <;> omega

/-- `slli r, r, 32; srli r, r, 32` on a 32-bit count. -/
theorem zext32_ofNat {k : Nat} (h : k < 2 ^ 32) :
    BitVec.ofNat 64 k <<< 32 >>> 32 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : k * 2 ^ 32 < 2 ^ 64), Nat.shiftRight_eq_div_pow,
    Nat.mul_div_cancel _ (by decide)]

/-- The loops' dispatch at `0x800040fc` with `val`'s count `cnt ≥ 1` in
`a7`, the accumulator's shifted last position in `a3`, `val`'s last integer
digit in `a2`, the operation in `a4`. -/
theorem sh_dispatch {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y w : NumObj} {shift : Nat} {sub : Bool} (hyo : y.Owns) (hal : (R0 1).toNat % 4 = 0)
    (ha : ShiftArgs L y w shift sub) (st : ShSt y R0 M0 R M) (hb : BcHeap S M H F (y :: L))
    (hc : 1 ≤ valCount w.rep)
    (h17 : R 17 = BitVec.ofNat 64 (valCount w.rep))
    (h13 : R 13 = BitVec.ofNat 64 (y.rep.val + (y.rep.len + y.rep.scale - shift - 1)))
    (h12 : R 12 = BitVec.ofNat 64 (w.rep.val + (w.rep.len - 1)))
    (h14 : R 14 = BitVec.ofNat 64 (if sub then 1 else 0))
    (hk : ShRet live S Q H F L y R0 M0 (shiftDs y.rep w.rep shift sub)) :
    DW live S Q 0x800040fc#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hn := hb.nums _ List.mem_cons_self
  have hnw := hb.nums _ (List.mem_cons_of_mem _ ha.mw)
  num_facts hn
  num_facts hnw
  have hfit := ha.fit
  have hcl := valCount_le w.rep
  have hvl := valLE_length (w := w.rep) (by omega)
  have hnc := ha.noCarry
  have hal' := accLE_split y.rep shift
  have hacl : (accLE y.rep shift).length = y.rep.len + y.rep.scale - shift := by
    simp only [accLE, List.length_reverse, List.length_take]; omega
  unfold shiftDs at hk
  generalize accLE y.rep shift = A at hal' hacl hnc hk
  rcases A with _ | ⟨a, xs⟩
  · simp only [List.length_nil] at hacl; omega
  simp only [List.length_cons] at hacl
  generalize y.rep.ds.drop (y.rep.len + y.rep.scale - shift) = D at hal' hk
  have hb' : BcHeap S M H F (withDs y ((a :: xs).reverse ++ D) :: L) := by
    rw [← hal']; exact hb
  have hP : y.rep.val + (y.rep.len + y.rep.scale - shift - 1) = y.rep.val + xs.length := by
    omega
  rw [hP] at h13
  cases sub
  · simp only [ripOp, ripOut, Bool.false_eq_true, if_false] at hk hnc h14
    bc_run hlive hS [h17, h13, h12, h14] at 0x800041a4
    bc_run hlive hS [h17, h13, h12, h14] at 0x800041a8 0x80004240
    · intro hz; bv_nat at hz; omega
    intro _
    bc_run hlive hS [h17, h13, h12, h14, word_pred (k := valCount w.rep) hc, sxw_ofNat,
      zext32_ofNat (k := valCount w.rep - 1) (by omega),
      add_not_ofNat (A := w.rep.val + (w.rep.len - 1)) (B := valCount w.rep - 1) (by omega)
        (by omega)] at 0x800041c8
    exact add_loop (E := w.rep.val + (w.rep.len - 1) - (valCount w.rep - 1) - 1)
      (A3 := y.rep.val + xs.length) (A7 := valCount w.rep - 1) hlive hyo hal ha.mw (by omega)
      (valLE w.rep) 0 a xs D 0 _ M rfl (by omega)
      (by omega) (st.regs (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [h12, h13, h14], by bsimp [h12, h13, h14], by bsimp [h12, h13, h14],
        by bsimp [h12, h13, h14], by bsimp [h12, h13, h14], by bsimp [h12, h13, h14],
        by bsimp [h12, h13, h14]⟩ (by omega) (by omega) (by omega) (by decide) hnc hk
  · simp only [ripOp, ripOut, if_true] at hk hnc h14
    bc_run hlive hS [h17, h13, h12, h14] at 0x80004100
    bc_run hlive hS [h17, h13, h12, h14] at 0x80004104 0x8000423c
    · intro hz; bv_nat at hz; omega
    intro _
    bc_run hlive hS [h17, h13, h12, h14, word_pred (k := valCount w.rep) hc, sxw_ofNat,
      zext32_ofNat (k := valCount w.rep - 1) (by omega),
      add_not_ofNat (A := w.rep.val + (w.rep.len - 1)) (B := valCount w.rep - 1) (by omega)
        (by omega)] at 0x80004120
    exact sub_loop (E := w.rep.val + (w.rep.len - 1) - (valCount w.rep - 1) - 1)
      (A3 := y.rep.val + xs.length) (A7 := valCount w.rep - 1) hlive hyo hal ha.mw (by omega)
      (valLE w.rep) 0 a xs D 0 _ M rfl (by omega)
      (by omega) (st.regs (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [h12, h13, h14], by bsimp [h12, h13, h14], by bsimp [h12, h13, h14],
        by bsimp [h12, h13, h14], by bsimp [h12, h13, h14], by bsimp [h12, h13, h14],
        by bsimp [h12, h13, h14]⟩ (by omega) (by omega) (by omega) (by decide) hnc hk

/-- `withDs` with the object's own digits. -/
theorem withDs_self (y : NumObj) : withDs y y.rep.ds = y := rfl

/-- The dispatch at `0x800040fc` as the entry leaves it: `val`'s count in
`a7`, `a3` computed from the accumulator's fields. -/
theorem sh_mid {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y w : NumObj} {shift : Nat} {sub : Bool} (hyo : y.Owns) (hal : (R0 1).toNat % 4 = 0)
    (ha : ShiftArgs L y w shift sub) (st : ShSt y R0 M R M) (hb : BcHeap S M H F (y :: L))
    (h17 : R 17 = BitVec.ofNat 64 (valCount w.rep))
    (h13 : R 13 = BitVec.ofNat 64 y.rep.val + (BitVec.ofNat 64 y.rep.len -
      BitVec.ofNat 64 shift + 18446744073709551615#64 + BitVec.ofNat 64 y.rep.scale))
    (h12 : R 12 = BitVec.ofNat 64 (w.rep.val + (w.rep.len - 1)))
    (h14 : R 14 = BitVec.ofNat 64 (if sub then 1 else 0))
    (hk : ShRet live S Q H F L y R0 M (shiftDs y.rep w.rep shift sub)) :
    DW live S Q 0x800040fc#64 R M := by
  have hfit := ha.fit
  have hn := hb.nums _ List.mem_cons_self
  num_facts hn
  rcases Nat.eq_zero_or_pos (valCount w.rep) with hc | hc
  · have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
    have htx : tohostAddr = 0x8001ad00 := rfl
    have h1 : R 1 = R0 1 := st.keeps.get 1
    have hv : valLE w.rep = [] := by simp [valLE, hc]
    have hds : shiftDs y.rep w.rep shift sub = y.rep.ds := by
      rw [shiftDs, hv]
      cases sub <;> simp only [ripOp, subRip_nil_zero, addRip_nil_zero, Bool.false_eq_true,
        if_true, if_false] <;> exact (accLE_split y.rep shift).symm
    rw [hds] at hk
    rw [hc] at h17
    cases sub
    · bc_run hlive hS [h17, h14] at 0x800041a4
      bc_run hlive hS [h17, h14] at 0x80004240
      bc_run hlive hS [h1, hal]
      exact hk _ _ st hb
    · bc_run hlive hS [h17, h14] at 0x80004100
      bc_run hlive hS [h17, h14] at 0x8000423c
      bc_run hlive hS [h1, hal]
      exact hk _ _ st hb
  · rw [acc_ptr (by omega) (by omega)] at h13
    exact sh_dispatch hlive hyo hal ha st hb hc h17 h13 h12 h14 hk

/-- `_bc_shift_addsub` at `0x800040cc`, `val`'s count in `a7`. -/
theorem sh_head {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y w : NumObj} {shift : Nat} {sub : Bool} (hyo : y.Owns) (hal : (R0 1).toNat % 4 = 0)
    (ha : ShiftArgs L y w shift sub) (st : ShSt y R0 M R M) (hb : BcHeap S M H F (y :: L))
    (h10 : R 10 = BitVec.ofNat 64 y.rep.p) (h11 : R 11 = BitVec.ofNat 64 w.rep.len)
    (h12 : R 12 = BitVec.ofNat 64 w.rep.val) (h13 : R 13 = BitVec.ofNat 64 shift)
    (h14 : R 14 = BitVec.ofNat 64 (if sub then 1 else 0))
    (h17 : R 17 = BitVec.ofNat 64 (valCount w.rep))
    (hk : ShRet live S Q H F L y R0 M (shiftDs y.rep w.rep shift sub)) :
    DW live S Q 0x800040cc#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hn := hb.nums _ List.mem_cons_self
  have hnw := hb.nums _ (List.mem_cons_of_mem _ ha.mw)
  num_facts hn
  num_facts hnw
  have hfit := ha.fit
  have hcl := valCount_le w.rep
  bc_run hlive hS [h10, h11, h12, h13, h14, h17, hn.len, hn.scale, addw_ofNat,
    toInt_ofNat_small] at 0x800040e0
  · intro hc; exfalso; (try simp (disch := omega) only [toInt_ofNat_small] at hc); omega
  intro _
  bc_run hlive hS [h10, h11, h12, h13, h14, h17, hn.value] at 0x800040fc
  exact sh_mid hlive hyo hal ha (st.regs (by keeps_tac Keeps.refl _ _)) hb
    (by bsimp [h17]) (by bsimp [h13]) (by bsimp []) (by bsimp [h14]) hk

/-- **`_bc_shift_addsub`** (`0x800040bc`): `a0` the accumulator `y` heading
the heap, `a1`/`a2` `val`'s `n_len`/`n_value`, `a3` the shift, `a4` the
operation. It adds (subtracts) `val`'s integer digits into `y`'s digits
from `shift` positions below its last, rippling the carry (borrow), and
returns with `y`'s digits `shiftDs`. -/
theorem bc_shift_addsub_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    {y w : NumObj} {shift : Nat} {sub : Bool} (hyo : y.Owns) (hal : (R 1).toNat % 4 = 0)
    (ha : ShiftArgs L y w shift sub) (hb : BcHeap S M H F (y :: L))
    (h10 : R 10 = BitVec.ofNat 64 y.rep.p) (h11 : R 11 = BitVec.ofNat 64 w.rep.len)
    (h12 : R 12 = BitVec.ofNat 64 w.rep.val) (h13 : R 13 = BitVec.ofNat 64 shift)
    (h14 : R 14 = BitVec.ofNat 64 (if sub then 1 else 0))
    (hk : ShRet live S Q H F L y R M (shiftDs y.rep w.rep shift sub)) :
    DW live S Q 0x800040bc#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hnw := hb.nums _ (List.mem_cons_of_mem _ ha.mw)
  num_facts hnw
  have l0 := hnw.lbu (i := 0) (by omega)
  simp only [Nat.add_zero] at l0
  have st0 : ShSt y R M R M := ⟨Keeps.refl _ _, MemOnly.refl _ _⟩
  by_cases hz : w.rep.ds.getD 0 0 = 0
  · have hcnt : valCount w.rep = w.rep.len - 1 := by unfold valCount; rw [if_pos hz]
    rw [hz] at l0
    bc_run hlive hS [h10, h11, h12, h13, h14, l0] at 0x800040cc
    bc_run hlive hS [h11, sxw_ofNat, word_pred (k := w.rep.len) (by omega)] at 0x800040cc
    exact sh_head hlive hyo hal ha (st0.regs (by keeps_tac Keeps.refl _ _)) hb
      (by bsimp [h10]) (by bsimp [h11]) (by bsimp [h12]) (by bsimp [h13]) (by bsimp [h14])
      (by bsimp [hcnt]) hk
  · have hcnt : valCount w.rep = w.rep.len := by unfold valCount; rw [if_neg hz]
    have hd := hnw.getD_lt 0
    bc_run hlive hS [h10, h11, h12, h13, h14, l0] at 0x800040cc
    rotate_left
    · intro e; bv_nat at e; omega
    intro _
    exact sh_head hlive hyo hal ha (st0.regs (by keeps_tac Keeps.refl _ _)) hb
      (by bsimp [h10]) (by bsimp [h11]) (by bsimp [h12]) (by bsimp [h13]) (by bsimp [h14])
      (by bsimp [hcnt, h11]) hk

end Dc.Mach
