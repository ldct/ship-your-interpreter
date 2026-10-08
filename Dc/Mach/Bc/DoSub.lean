import Dc.Mach.Bc.DoAdd

/-!
# `_bc_do_sub` (`lib/number.c`)

```
800045e8 save s0-s7, ra in a 96-byte frame ; s6 = n1, s7 = n2
         D = max l1 l2 (s1), l2 (s2), l1 (s3), min l1 l2 (s4),
         S = max s1 s2 (s5), min s1 s2 (s0) ; smin at sp+8
80004664 bc_new_num (D, max S smin)
80004674 smin > S: zero the scale_min tail (already zero)
800046a0 n1ptr (a6), n2ptr (a1), diffptr (a3) at their last digits
800046dc s1 > s2: copy n1's extra fraction digits (80004704)
80004850 s2 >= s1: subtract n2's extra fraction digits from zero (80004878)
8000472c c = l2 + min s (s0), borrow (a4)
80004740 subtract loop over c positions
80004790 l1 > l2: propagate the borrow (800047b8), then copy n1 (80004838)
800047d8 _bc_rm_leading_zeros (inlined) ; 8000480c restore, ret
```

The result's digits from the last one down are the little-endian difference
`subLE xs ys 0` of the aligned operands (`Dc/BcModel/Steps.lean`): after
`k` positions the result object holds `sumDs N k r Z`, and the borrow
register holds `borrowAt xs ys 0 k`. The subtrahend is not longer than the
minuend (`SubArgs.le`), as for the normalized operands `bc_add` and
`bc_sub` pass after comparing magnitudes.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-! ## Words holding small integers -/

theorem toInt_ofInt64 {u : Int} (h1 : -2 ^ 63 ≤ u) (h2 : u < 2 ^ 63) :
    (BitVec.ofInt 64 u).toInt = u := by
  rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- `subw` of two small integers. -/
theorem subw_int {u v : Int} (hu1 : -2 ^ 31 ≤ u) (hu2 : u < 2 ^ 31) (hv1 : -2 ^ 31 ≤ v)
    (hv2 : v < 2 ^ 31) (h1 : -2 ^ 31 ≤ u - v) (h2 : u - v < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofInt 64 u) -
      BitVec.extractLsb 31 0 (BitVec.ofInt 64 v)) = BitVec.ofInt 64 (u - v) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), toInt_ofInt64 (by omega) (by omega)]
  have e : BitVec.extractLsb 31 0 (BitVec.ofInt 64 u) - BitVec.extractLsb 31 0 (BitVec.ofInt 64 v) =
      BitVec.ofInt 32 (u - v) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_ofInt]
    omega
  rw [e, BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)

theorem ofInt_natCast64 (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by simp

/-- `subw` of two small naturals, as an integer word. -/
theorem subw_nat {a b : Nat} (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) -
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 b)) = BitVec.ofInt 64 ((a : Int) - b) := by
  rw [← ofInt_natCast64 a, ← ofInt_natCast64 b]
  exact subw_int (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- `subw` of a small integer and a small natural. -/
theorem subw_int_nat {u : Int} {b : Nat} (hu1 : -2 ^ 30 ≤ u) (hu2 : u < 2 ^ 30) (hb : b < 2 ^ 30) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofInt 64 u) -
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 b)) = BitVec.ofInt 64 (u - b) := by
  rw [← ofInt_natCast64 b]
  exact subw_int (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- A nonnegative integer word is a natural one. -/
theorem ofInt_nonneg {u : Int} (h : 0 ≤ u) : BitVec.ofInt 64 u = BitVec.ofNat 64 u.toNat := by
  rw [← ofInt_natCast64, Int.toNat_of_nonneg h]

/-! ## Storing one position of a result -/

/-- Position `N - 1 - k` of a result `sumDs N k r Z` written with digit `k`
of `r`. -/
theorem BcHeap.storeSum {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {N k : Nat} {r Z : List Nat} (hyl : y.rep.len + y.rep.scale = N + Z.length)
    (hk : k < N) (hr : k < r.length) (hd : r.getD k 0 < 10)
    (hb : BcHeap S M H F (withDs y (sumDs N k r Z) :: L))
    {v : BitVec 64} (hv : sbData v = BitVec.ofNat 8 (r.getD k 0)) :
    BcHeap S (writeLog M [(y.rep.val + (N - 1 - k), 1, v)]) H F
      (withDs y (sumDs N (k + 1) r Z) :: L) := by
  have hst := BcHeap.setDigit (L1 := []) hb (i := N - 1 - k) (d := r.getD k 0)
    (by simp only [withDs] at hyl ⊢; omega) hd hv
  simp only [withDs, List.nil_append] at hst ⊢
  rw [sumDs_step hk hr] at hst
  exact hst

/-! ## The model -/

/-- The little-endian difference. -/
abbrev subR (a b : NumRep) : List Nat := subLE (addXs a b) (addYs a b) 0
/-- The result's digits after `k` positions. -/
abbrev subDs (a b : NumRep) (smin k : Nat) : List Nat := sumDs (addN a b) k (subR a b) (addZ a b smin)
/-- The borrow into position `k`. -/
abbrev subB (a b : NumRep) (k : Nat) : Nat := borrowAt (addXs a b) (addYs a b) 0 k

/-- The lengths and digits of the operands and the difference. -/
structure SubModel (a b : NumRep) : Prop where
  xl : (addXs a b).length = addN a b
  yl : (addYs a b).length = addN a b
  rl : (subR a b).length = addN a b
  xd : IsDigits (addXs a b)
  yd : IsDigits (addYs a b)
  rd : IsDigits (subR a b)

theorem subModel {a b : NumRep} (ha : NumShape a) (hb : NumShape b) : SubModel a b := by
  have xl := opLE_length ha.dsLen a.len a.scale b.len b.scale (by omega) (by omega)
  have yl := opLE_length hb.dsLen a.len a.scale b.len b.scale (by omega) (by omega)
  have xd := padLE_digits ha.dig a.scale (loopScale a.scale b.scale) (addN a b)
  have yd := padLE_digits hb.dig b.scale (loopScale a.scale b.scale) (addN a b)
  exact ⟨xl, yl, by rw [subLE_length _ _ _ (by rw [xl, yl]), xl], xd, yd,
    subLE_digits _ _ _ xd yd (by decide)⟩

theorem SubModel.getD_lt_r {a b : NumRep} (h : SubModel a b) (k : Nat) : (subR a b).getD k 0 < 10 := by
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge k (subR a b).length with hk | hk
  · rw [List.getElem?_eq_getElem hk]; exact h.rd _ (List.getElem_mem _)
  · rw [List.getElem?_eq_none hk]; decide

theorem SubModel.borrow_le {a b : NumRep} (_h : SubModel a b) (k : Nat) : subB a b k ≤ 1 :=
  borrowAt_le _ _ _ _ (by decide)

/-- One position: the digit written and the borrow out. -/
theorem SubModel.step {a b : NumRep} (h : SubModel a b) {k : Nat} (hk : k < addN a b) :
    (subR a b).getD k 0 =
        (if (addXs a b).getD k 0 < (addYs a b).getD k 0 + subB a b k then
          (addXs a b).getD k 0 + 10 - (addYs a b).getD k 0 - subB a b k
        else (addXs a b).getD k 0 - (addYs a b).getD k 0 - subB a b k) ∧
      subB a b (k + 1) =
        if (addXs a b).getD k 0 < (addYs a b).getD k 0 + subB a b k then 1 else 0 :=
  ⟨subLE_getD _ _ _ _ (by rw [h.xl, h.yl]) (by rw [h.xl]; exact hk),
    borrowAt_succ _ _ _ _ (by rw [h.xl, h.yl]) (by rw [h.xl]; exact hk)⟩

/-- The result `bc_new_num` hands over is the difference before any position. -/
theorem subDs_zero (a b : NumRep) (smin : Nat) :
    List.replicate (max a.len b.len + max smin (max a.scale b.scale)) 0 = subDs a b smin 0 := by
  simp only [subDs, addZ]
  rw [sumDs_zero, List.replicate_append_replicate]
  congr 1; simp only [addN, loopLen]; omega

/-- After every position the result is `_bc_do_sub`'s digit array. -/
theorem subDs_full {a b : NumRep} (h : SubModel a b) (smin : Nat) :
    subDs a b smin (addN a b) = subDigits a.len a.scale a.ds b.len b.scale b.ds smin :=
  sumDs_full h.rl

theorem subDs_length {a b : NumRep} (h : SubModel a b) (smin : Nat) {k : Nat} (hk : k ≤ addN a b) :
    (subDs a b smin k).length = max a.len b.len + max smin (max a.scale b.scale) := by
  rw [sumDs_length hk (by rw [h.rl]; exact hk)]
  simp only [addN, loopLen, addZ, List.length_replicate]; omega

/-! ## Frame, context, and result -/

/-- `_bc_do_sub`'s saved registers in its 96-byte frame (offsets from the
lowered `sp`), last stored first. -/
abbrev subSlots : List (Nat × Nat) :=
  [(21, 40), (20, 48), (8, 80), (1, 88), (23, 24), (22, 32), (9, 72), (19, 56), (18, 64)]

/-- The registers `_bc_do_sub` may change. -/
abbrev subClob : List Nat := [6, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29]

/-- The registers changed inside `_bc_do_sub` before its epilogue. -/
abbrev subAll : List Nat :=
  [1, 2, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 29]

/-- The scratch registers of `_bc_do_sub`'s loops. -/
abbrev subTmp : List Nat := [6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 28, 29]

/-- `_bc_do_sub`'s fixed context: its 96-byte frame and `bc_new_num`'s 32
bytes below, above the heap; the entry's `sp` and return address. -/
structure SubCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp : Nat) : Prop where
  frame : StackFrame S sp 128
  above : heapEnd + 128 ≤ sp
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0

/-- The operands: two numbers of the heap (possibly the same), the
subtrahend not longer than the minuend, `scale_min`, and the result's size
in range. -/
structure SubArgs (L : List NumObj) (x1 x2 : NumObj) (smin : Nat) : Prop where
  m1 : x1 ∈ L
  m2 : x2 ∈ L
  le : x2.rep.len ≤ x1.rep.len
  size : max x1.rep.len x2.rep.len + max smin (max x1.rep.scale x2.rep.scale) < 2 ^ 31

/-- `_bc_do_sub`'s result: the new number `y` (positive, normalized, one
reference) holding `_bc_do_sub`'s digit array heads the heap; off the heap
only the stack window changed. -/
structure SubPost (S : Nat → Prop) (Mt0 Mt : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (a b : NumRep) (smin sp : Nat) (y : NumObj) : Prop where
  heap : BcHeap S Mt H F (y :: L)
  num : y.rep.num = ⟨false, dval (subDigits a.len a.scale a.ds b.len b.scale b.ds smin),
    resScale a.scale b.scale smin⟩
  norm : y.rep.Norm
  refs : y.rep.refs = 1
  out : ∀ a, OutHeap a → ¬ frameIn sp 128 a → imgM Mt a = imgM Mt0 a

/-- `_bc_do_sub`'s continuations: the result, or `out_of_memory`. -/
structure SubK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (L : List NumObj) (a b : NumRep) (smin sp : Nat) : Prop where
  ret : ∀ R' Mt' H F y, Keeps subClob R' R0 → R' 10 = BitVec.ofNat 64 y.sb.pay →
    SubPost S Mt0 Mt' H F L a b smin sp y → DW live S Q (R0 1) R' Mt'
  oom : ∀ R' Mt', R' 2 = BitVec.ofNat 64 (sp - 128) →
    (∀ a, OutHeap a → ¬ frameIn sp 128 a → imgM Mt' a = imgM Mt0 a) →
    DW live S Q 0x80002bcc#64 R' Mt'

/-- Inside `_bc_do_sub` after `bc_new_num`: `sp` lowered by 96, the saved
registers in the frame, `s6 = n1`, `s7 = n2`, `s3 = l1`, `s2 = s4 = l2`,
`s5 = S`, `a0` the result's struct `p`, and off the heap only the stack
window changed. -/
structure SubAt (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp : Nat)
    (x1 x2 : NumObj) (p : Nat) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 96)
  saved : SavedWords M (sp - 96) subSlots R0
  r22 : R 22 = BitVec.ofNat 64 x1.rep.p
  r23 : R 23 = BitVec.ofNat 64 x2.rep.p
  r19 : R 19 = BitVec.ofNat 64 x1.rep.len
  r18 : R 18 = BitVec.ofNat 64 x2.rep.len
  r20 : R 20 = BitVec.ofNat 64 x2.rep.len
  r21 : R 21 = BitVec.ofNat 64 (max x1.rep.scale x2.rep.scale)
  r10 : R 10 = BitVec.ofNat 64 p
  regs : Keeps subAll R R0
  out : ∀ a, OutHeap a → ¬ frameIn sp 128 a → imgM M a = imgM Mt0 a

/-- `SubAt` through writes inside the heap. -/
theorem SubAt.heap {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp : Nat}
    {x1 x2 : NumObj} {p : Nat} (st : SubAt S Mt0 M R0 R sp x1 x2 p) (cx : SubCtx S R0 sp)
    (hag : ∀ a, OutHeap a → imgM M' a = imgM M a) : SubAt S Mt0 M' R0 R sp x1 x2 p := by
  have hab := cx.above
  simp only [heapEnd] at hab
  exact
    { st with
      saved := st.saved.transport (lo := 24) (top := 96) (hag := fun a h1 h2 => hag a (by
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega))
      out := fun a ha hf => (hag a ha).trans (st.out a ha hf) }

/-- `SubAt` through changes of the loops' scratch registers. -/
theorem SubAt.keeps {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp : Nat}
    {x1 x2 : NumObj} {p : Nat} (st : SubAt S Mt0 M R0 R sp x1 x2 p) (hk : Keeps subTmp R' R) :
    SubAt S Mt0 M R0 R' sp x1 x2 p :=
  { st with
    r2 := by rw [hk.get 2]; exact st.r2
    r22 := by rw [hk.get 22]; exact st.r22
    r23 := by rw [hk.get 23]; exact st.r23
    r19 := by rw [hk.get 19]; exact st.r19
    r18 := by rw [hk.get 18]; exact st.r18
    r20 := by rw [hk.get 20]; exact st.r20
    r21 := by rw [hk.get 21]; exact st.r21
    r10 := by rw [hk.get 10]; exact st.r10
    regs := (hk.mono (by decide)).trans st.regs }

/-- The epilogue at `0x8000480c`: the saved registers back, `sp` up. -/
theorem sub_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hp : SubPost S Mt0 M H F L x1.rep x2.rep smin sp y) :
    DW live S Q 0x8000480c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hp.heap.heap.own a h1 h2
  have e1 := st.saved.get 1 88
  have e8 := st.saved.get 8 80
  have e9 := st.saved.get 9 72
  have e18 := st.saved.get 18 64
  have e19 := st.saved.get 19 56
  have e20 := st.saved.get 20 48
  have e21 := st.saved.get 21 40
  have e22 := st.saved.get 22 32
  have e23 := st.saved.get 23 24
  have h2 := st.r2
  have h10 := st.r10
  have hal := cx.al
  bc_run hlive hS [h2, e1, e8, e9, e18, e19, e20, e21, e22, e23]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk.ret _ _ H F y (Keeps.unwind (saved := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := st.regs)) (by bsimp [h10]) hp
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0]
  congr 1; omega

/-- The result before `_bc_rm_leading_zeros`: positive, one reference,
`_bc_do_sub`'s digit array at the result scale. -/
structure SubFinal (o a b : NumRep) (smin : Nat) : Prop where
  neg : o.neg = false
  refs : o.refs = 1
  ds : o.ds = subDigits a.len a.scale a.ds b.len b.scale b.ds smin
  scale : o.scale = resScale a.scale b.scale smin
  dsLen : o.ds.length = o.len + o.scale
  lenPos : 1 ≤ o.len

/-- Leading zeros removed: the result. -/
theorem sub_done {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {o : NumRep} {j : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay) (hf : SubFinal o x1.rep x2.rep smin)
    (hj : lzCount (o.len - 1) o.ds = j) (hb : BcHeap S M H F ({ y with rep := o.drop j } :: L)) :
    DW live S Q 0x8000480c#64 R M := by
  obtain ⟨hnum, hnorm, -, -⟩ := NumRep.rmLeadingZeros_spec hf.dsLen hf.lenPos
  have e : o.rmLeadingZeros = o.drop j := by rw [NumRep.rmLeadingZeros, hj]
  rw [e] at hnum hnorm
  refine sub_epi hlive cx hk (y := { y with rep := o.drop j }) st ⟨hb, ?_, hnorm, hf.refs, st.out⟩
  show (o.drop j).num = _
  rw [hnum, NumRep.num, hf.neg, hf.ds, hf.scale]

/-- `_bc_rm_leading_zeros`' loop at `0x80004804`: `j` leading zeros
dropped (`n_value = val + j`, `n_len = len - j`), digits `0..j` zero. -/
theorem sub_rmlz_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {o : NumRep}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hf : SubFinal o x1.rep x2.rep smin) (hp : o.p = y.sb.pay) :
    ∀ n j (R : Nat → BitVec 64) (M : Mem), o.len - 1 - j = n → j < o.len →
      SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F ({ y with rep := o.drop j } :: L) →
      R 15 = BitVec.ofNat 64 (o.val + j) → R 14 = BitVec.ofNat 64 (o.len - j) →
      R 12 = BitVec.ofNat 64 1 → (∀ i, i ≤ j → o.ds.getD i 0 = 0) →
      DW live S Q 0x80004804#64 R M := by
  have hsf := cx.frame
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro n
  induction n with
  | zero =>
    intro j R M hn hj st hb h15 h14 h12 hz
    have hn0 := hb.nums _ List.mem_cons_self
    have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
    num_facts hn0
    have v5 := hn0.shape.vHi; have v7 := hn0.shape.size; have v8 := hn0.shape.lenPos
    have v9 := hn0.shape.vLo; have v6 := hn0.shape.ptrLe
    simp only [NumRep.drop, heapEnd, heapStart] at v5 v7 v8 v9 v6
    bc_run hlive hS [h15, h14, h12, toInt_ofNat_small] at 0x8000480c
    · intro hc; exfalso; (try simp (disch := omega) only [toInt_ofNat_small] at hc); omega
    · intro _
      exact sub_done hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hf
        (lzCount_eq _ _ _ (by omega) (by rw [hf.dsLen]; omega) (fun i hi => hz i (by omega))
          (.inl (by omega))) hb
  | succ n ih =>
    intro j R M hn hj st hb h15 h14 h12 hz
    have hn0 := hb.nums _ List.mem_cons_self
    have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
    num_facts hn0
    have v5 := hn0.shape.vHi; have v7 := hn0.shape.size; have v8 := hn0.shape.lenPos
    have v9 := hn0.shape.vLo; have v6 := hn0.shape.ptrLe
    simp only [NumRep.drop, heapEnd, heapStart] at v5 v7 v8 v9 v6
    have hr10 := st.r10
    bc_run hlive hS [h15, h14, h12, hr10, toInt_ofNat_small] at 0x8000480c 0x800047f0
    · intro hc
      have hb' := BcHeap.advance hb (v1 := BitVec.ofNat 64 (o.len - j - 1))
        (v2 := BitVec.ofNat 64 (o.val + j + 1)) (by simp only [NumRep.drop]; omega)
        (by simp only [NumRep.drop]; rw [toNat_ofNat_mod32 (by omega)]) (by simp only [NumRep.drop])
      simp only [NumRep.drop_drop] at hb'
      have hp' : (o.drop j).p = y.sb.pay := hp
      rw [hp'] at hb'
      have hn1 := hb'.nums _ List.mem_cons_self
      have hl1 := hn1.lbu (i := 0) (by simp only [NumRep.drop]; omega)
      simp only [NumRep.drop, Nat.add_zero, List.getD_eq_getElem?_getD, List.getElem?_drop,
        ← Nat.add_assoc] at hl1
      have st' := (st.heap cx (M' := writeLog (writeLog M [(y.sb.pay + 4, 4,
        BitVec.ofNat 64 (o.len - j - 1))]) [(y.sb.pay + 32, 8, BitVec.ofNat 64 (o.val + j + 1))])
        fun a ha => by
          have := hn0.shape.pLo; have := hn0.shape.pHi
          simp only [NumRep.drop, OutHeap, heapStart, heapEnd] at *
          rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)])
      have hd := hn1.getD_lt 0
      simp only [NumRep.drop, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero] at hd
      bc_run hlive hS [h15, h14, h12, hr10, hl1] at 0x80004804 0x8000480c
      · intro hne
        bv_nat at hne
        rw [Nat.mod_eq_of_lt (by omega)] at hne
        exact sub_done hlive cx hk (st'.keeps (by keeps_tac Keeps.refl _ _)) hf
          (lzCount_eq _ _ _ (by omega) (by rw [hf.dsLen]; omega) (fun i hi => hz i (by omega))
            (.inr (by rw [List.getD_eq_getElem?_getD]; exact hne))) hb'
      · intro he
        bv_nat at he
        rw [Classical.not_not, Nat.mod_eq_of_lt (by omega)] at he
        refine ih (j + 1) _ _ (by omega) (by omega) (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
          (by bsimp [Nat.add_assoc]) (by bsimp [Nat.sub_sub]) (by bsimp [h12]) fun i hi => ?_
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hz i (by omega)
        · rw [show i = j + 1 by omega, List.getD_eq_getElem?_getD]; exact he
    · intro _
      exact sub_done hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hf
        (lzCount_eq _ _ _ (by omega) (by rw [hf.dsLen]; omega) (fun i hi => hz i (by omega))
          (.inl (by omega))) hb

/-- `_bc_rm_leading_zeros` inlined at `0x800047d8`. -/
theorem sub_rmlz {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {o : NumRep}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hf : SubFinal o x1.rep x2.rep smin) (hp : o.p = y.sb.pay)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay) (hb : BcHeap S M H F ({ y with rep := o } :: L)) :
    DW live S Q 0x800047d8#64 R M := by
  have hsf := cx.frame
  have hn := hb.nums _ List.mem_cons_self
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  num_facts hn
  have hv : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 o.val := by rw [← hp]; exact hn.value
  have hlen : ldv .lw M (y.sb.pay + 4) = BitVec.ofNat 64 o.len := by rw [← hp]; exact hn.len
  have hl0 := hn.lbu (i := 0) (by omega)
  have hd := hn.getD_lt 0
  simp only [Nat.add_zero] at hl0 hd
  have hr10 := st.r10
  have hb0 : BcHeap S M H F ({ y with rep := o.drop 0 } :: L) := by rw [NumRep.drop_zero]; exact hb
  bc_run hlive hS [hr10, hv, hl0, hlen] at 0x80004804 0x8000480c
  · intro hne
    bv_nat at hne
    rw [Nat.mod_eq_of_lt (by omega)] at hne
    exact sub_done hlive cx hk (st.keeps (by keeps_tac Keeps.refl _ _)) hf
      (lzCount_eq _ _ _ (by omega) (by rw [hf.dsLen]; omega) (fun i hi => absurd hi (by omega))
        (.inr hne)) hb0
  · intro he
    bv_nat at he
    rw [Classical.not_not, Nat.mod_eq_of_lt (by omega)] at he
    bc_run hlive hS [hr10, hv, hl0, hlen] at 0x80004804
    exact sub_rmlz_loop hlive cx hk hf hp _ 0 _ _ rfl (by omega)
      (st.keeps (by keeps_tac Keeps.refl _ _)) hb0 (by bsimp []) (by bsimp []) (by bsimp [])
      fun i hi => by rw [show i = 0 by omega]; exact he

/-! ## The difference object -/

/-- The object `bc_new_num` returned for the difference, and the model of
the operands `a`, `b`. -/
structure SubSum (y : NumObj) (a b : NumRep) (smin : Nat) : Prop where
  rep : y.rep = zeroRep y.sb.pay y.db.pay (max a.len b.len) (max smin (max a.scale b.scale))
  model : SubModel a b
  size : max a.len b.len + max smin (max a.scale b.scale) < 2 ^ 31
  lenPos : 1 ≤ max a.len b.len

theorem SubSum.N_lt {y : NumObj} {a b : NumRep} {smin : Nat} (h : SubSum y a b smin) :
    addN a b < 2 ^ 31 := by
  have := h.size; simp only [addN, loopLen]; omega

theorem SubSum.p {y : NumObj} {a b : NumRep} {smin : Nat} (h : SubSum y a b smin) :
    y.rep.p = y.sb.pay := by rw [h.rep]; rfl

theorem SubSum.lenScale {y : NumObj} {a b : NumRep} {smin : Nat} (h : SubSum y a b smin) :
    y.rep.len + y.rep.scale = addN a b + (addZ a b smin).length := by
  rw [h.rep]; simp only [zeroRep, addN, loopLen, addZ, List.length_replicate]; omega

/-- After every position, the object before `_bc_rm_leading_zeros`. -/
theorem SubSum.final {y : NumObj} {a b : NumRep} {smin : Nat} (h : SubSum y a b smin) :
    SubFinal { y.rep with ds := subDs a b smin (addN a b) } a b smin := by
  have hm := h.model
  have hl := subDs_length hm smin (Nat.le_refl _)
  exact
    { neg := by show y.rep.neg = false; rw [h.rep]; rfl
      refs := by show y.rep.refs = 1; rw [h.rep]; rfl
      ds := subDs_full hm smin
      scale := by show y.rep.scale = _; rw [h.rep]; rfl
      dsLen := by show (subDs a b smin (addN a b)).length = y.rep.len + y.rep.scale
                  rw [hl, h.rep]; rfl
      lenPos := by show 1 ≤ y.rep.len; rw [h.rep]; exact h.lenPos }

/-- Above `n2`'s digits (from `S + l2` on) the subtrahend is zero and the
minuend is `n1`'s digit. -/
theorem sub_high {a b : NumRep} (ha : NumShape a) (hb : NumShape b) (hl : b.len ≤ a.len) {k : Nat}
    (h1 : max a.scale b.scale + b.len ≤ k) (h2 : k < addN a b) :
    (addXs a b).getD k 0 = a.ds.getD (a.len + max a.scale b.scale - 1 - k) 0 ∧
      (addYs a b).getD k 0 = 0 :=
  ⟨addXs_in ha (by omega) (by simp only [addN, loopLen] at h2; omega), addYs_out hb (.inr (by omega))⟩

/-! ## Above `n2`: the borrow, then a copy of `n1` -/

/-- One step of the copy of `n1`'s top digits at `0x8000483c`: the digit
`r_k` in `a5` into the slot `a3`; then `n1`'s next digit at `a6 + 1`
(`0x80004838`) or, after the last position, `_bc_rm_leading_zeros`. -/
theorem sub_copy_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hk1 : max x1.rep.scale x2.rep.scale + x2.rep.len ≤ k) (hk2 : k < addN x1.rep x2.rep)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin k) :: L))
    (h15 : R 15 = BitVec.ofNat 64 ((subR x1.rep x2.rep).getD k 0))
    (h13 : R 13 = BitVec.ofNat 64 (y.rep.val + (addN x1.rep x2.rep - 1 - k)))
    (h16 : R 16 = BitVec.ofNat 64 (x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - k) - 1))
    (h12 : R 12 = BitVec.ofNat 64 (y.rep.val - 1))
    (hnext : k + 1 < addN x1.rep x2.rep → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (k + 1)) :: L) →
      R' 13 = BitVec.ofNat 64 (y.rep.val + (addN x1.rep x2.rep - 1 - (k + 1))) →
      R' 16 = BitVec.ofNat 64
        (x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k + 1)) - 1) →
      R' 12 = BitVec.ofNat 64 (y.rep.val - 1) → DW live S Q 0x80004838#64 R' M') :
    DW live S Q 0x8000483c#64 R M := by
  have hm := hy.model
  have hNl := hy.N_lt
  have hle := ha.le
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a4 := hs1.vHi
  have hls := hy.lenScale
  simp only [heapStart, heapEnd] at v1 v2 a1 a4
  simp only [addN, loopLen, addZ, List.length_replicate] at hls hNl hk2
  have eN1 : addN x1.rep x2.rep ≤ max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale :=
    Nat.le_refl _
  have eN2 : max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale ≤ addN x1.rep x2.rep :=
    Nat.le_refl _
  have hb' : BcHeap S (writeLog M [(y.rep.val + (addN x1.rep x2.rep - 1 - k) - 1 + 1, 1,
      BitVec.ofNat 64 ((subR x1.rep x2.rep).getD k 0))]) H F
      (withDs y (subDs x1.rep x2.rep smin (k + 1)) :: L) := by
    rw [show y.rep.val + (addN x1.rep x2.rep - 1 - k) - 1 + 1 =
      y.rep.val + (addN x1.rep x2.rep - 1 - k) by simp only [addN, loopLen]; omega]
    exact BcHeap.storeSum hy.lenScale (by simp only [addN, loopLen]; omega)
      (by rw [hm.rl]; simp only [addN, loopLen]; omega) (hm.getD_lt_r k) hb (sbData_ofNat _)
  have st' := st.heap cx (M' := writeLog M [(y.rep.val + (addN x1.rep x2.rep - 1 - k) - 1 + 1, 1,
      BitVec.ofNat 64 ((subR x1.rep x2.rep).getD k 0))]) fun a ha =>
    imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd, addN, loopLen] at ha ⊢; omega)
  bc_run hlive hS [h15, h13, h16, h12] at 0x80004848
  bc_run hlive hS [h12] at 0x80004838 0x800047d8
  · intro hne
    bv_nat at hne
    exact hnext (by simp only [addN, loopLen] at hne ⊢; omega) _ _
      (st'.keeps (by keeps_tac Keeps.refl _ _)) hb' (by bsimp []; congr 1; omega)
      (by bsimp []; congr 1; omega) (by bsimp [h12])
  · intro he
    bv_nat at he
    have eN : k + 1 = addN x1.rep x2.rep := by simp only [addN, loopLen] at he ⊢; omega
    rw [eN] at hb'
    bc_run hlive hS [] at 0x800047d8
    exact sub_rmlz hlive cx hk hy.final hy.p (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'

/-- The copy of `n1`'s top digits from `0x8000483c`, position `k` on, the
borrow used up. -/
theorem sub_copy_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin) :
    ∀ n k (R : Nat → BitVec 64) (M : Mem), addN x1.rep x2.rep - 1 - k = n →
      max x1.rep.scale x2.rep.scale + x2.rep.len ≤ k → k < addN x1.rep x2.rep →
      SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin k) :: L) →
      subB x1.rep x2.rep (k + 1) = 0 →
      R 15 = BitVec.ofNat 64 ((subR x1.rep x2.rep).getD k 0) →
      R 13 = BitVec.ofNat 64 (y.rep.val + (addN x1.rep x2.rep - 1 - k)) →
      R 16 = BitVec.ofNat 64
        (x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - k) - 1) →
      R 12 = BitVec.ofNat 64 (y.rep.val - 1) →
      DW live S Q 0x8000483c#64 R M := by
  have hm := hy.model
  have hle := ha.le
  intro n
  induction n with
  | zero =>
    intro k R M hn hk1 hk2 st hb _ h15 h13 h16 h12
    exact sub_copy_body hlive cx hk hy ha hk1 hk2 st hb h15 h13 h16 h12 fun h => absurd h (by omega)
  | succ n ih =>
    intro k R M hn hk1 hk2 st hb hb0 h15 h13 h16 h12
    refine sub_copy_body hlive cx hk hy ha hk1 hk2 st hb h15 h13 h16 h12
      fun hk3 R' M' st' hb' r13 r16 r12 => ?_
    have hS : HeapOwn S := fun a h1 h2 => hb'.heap.own a h1 h2
    have hn1 := hb'.nums x1 (List.mem_cons_of_mem _ ha.m1)
    have hs1 := hn1.shape
    have hs2 := (hb'.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
    have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a4 := hs1.vHi; have a3 := hs1.size
    simp only [heapStart, heapEnd] at a1 a4
    have hNl := hy.N_lt
    have htx : tohostAddr = 0x8001ad00 := rfl
    have ⟨hx, hy0⟩ := sub_high hs1 hs2 hle (k := k + 1) (by omega) hk3
    have ⟨hr, hbr⟩ := hm.step (k := k + 1) hk3
    rw [hx, hy0, hb0] at hr hbr
    simp only [Nat.add_zero, Nat.not_lt_zero, ite_false, if_false, Nat.sub_zero] at hr hbr
    simp only [addN, loopLen] at hk3 hNl
    have hl := hn1.lbu (i := x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k + 1)) (by omega)
    rw [show x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k + 1)) =
      x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k + 1)) - 1 + 1 by omega] at hl
    bc_run hlive hS [r16, hl] at 0x8000483c
    exact ih (k + 1) _ _ (by omega) (by omega) (by simp only [addN, loopLen]; omega)
      (st'.keeps (by keeps_tac Keeps.refl _ _)) hb' hbr (by bsimp [hr]) (by bsimp [r13])
      (by bsimp [r16]) (by bsimp [r12])

/-- One step of the borrow propagation at `0x800047b8`: `n1`'s digit `x`
at `a6`, the borrow `b` in `a4`. `x - b = -1` writes `9` and keeps the
borrow; otherwise `x - b` goes to the copy (`0x8000483c`). -/
theorem sub_borrow_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hk1 : max x1.rep.scale x2.rep.scale + x2.rep.len ≤ k) (hk2 : k < addN x1.rep x2.rep)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin k) :: L))
    (h16 : R 16 = BitVec.ofNat 64 (x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - k)))
    (h14 : R 14 = BitVec.ofNat 64 (subB x1.rep x2.rep k))
    (h13 : R 13 = BitVec.ofNat 64 (y.rep.val + (addN x1.rep x2.rep - 1 - k)))
    (h12 : R 12 = BitVec.ofNat 64 (y.rep.val - 1))
    (h11 : R 11 = 18446744073709551615#64) (h17 : R 17 = BitVec.ofNat 64 9)
    (hnext : k + 1 < addN x1.rep x2.rep → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (k + 1)) :: L) →
      R' 16 = BitVec.ofNat 64
        (x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k + 1))) →
      R' 14 = BitVec.ofNat 64 (subB x1.rep x2.rep (k + 1)) →
      R' 13 = BitVec.ofNat 64 (y.rep.val + (addN x1.rep x2.rep - 1 - (k + 1))) →
      R' 12 = BitVec.ofNat 64 (y.rep.val - 1) → R' 11 = 18446744073709551615#64 →
      R' 17 = BitVec.ofNat 64 9 → DW live S Q 0x800047b8#64 R' M') :
    DW live S Q 0x800047b8#64 R M := by
  have hm := hy.model
  have hNl := hy.N_lt
  have hle := ha.le
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ ha.m1)
  have hs1 := hn1.shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a4 := hs1.vHi; have a3 := hs1.size
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hls := hy.lenScale
  simp only [heapStart, heapEnd] at a1 a4 v1 v2
  simp only [addN, loopLen, addZ, List.length_replicate] at hls hNl
  have eN1 : addN x1.rep x2.rep ≤ max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale :=
    Nat.le_refl _
  have eN2 : max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale ≤ addN x1.rep x2.rep :=
    Nat.le_refl _
  have ⟨hx, hy0⟩ := sub_high hs1 hs2 hle hk1 hk2
  have ⟨hr, hbr⟩ := hm.step hk2
  rw [hx, hy0, Nat.zero_add] at hr hbr
  simp only [Nat.sub_zero] at hr
  have hbl := hm.borrow_le k
  have hd := hn1.getD_lt (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - k)
  have hl := hn1.lbu (i := x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - k) (by omega)
  by_cases hxb : x1.rep.ds.getD (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - k) 0 <
      subB x1.rep x2.rep k
  · rw [if_pos hxb] at hr hbr
    have hx0 : x1.rep.ds.getD (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - k) 0 = 0 := by omega
    have hb1 : subB x1.rep x2.rep k = 1 := by omega
    rw [hx0] at hl hr
    rw [hb1] at h14 hr
    have hb' : BcHeap S (writeLog M [(y.rep.val + (addN x1.rep x2.rep - 1 - k) - 1 + 1, 1,
        BitVec.ofNat 64 9)]) H F (withDs y (subDs x1.rep x2.rep smin (k + 1)) :: L) := by
      rw [show y.rep.val + (addN x1.rep x2.rep - 1 - k) - 1 + 1 =
        y.rep.val + (addN x1.rep x2.rep - 1 - k) by omega]
      exact BcHeap.storeSum hy.lenScale hk2 (by rw [hm.rl]; exact hk2) (hm.getD_lt_r k) hb
        (by rw [sbData_ofNat, hr])
    have st' := st.heap cx (M' := writeLog M [(y.rep.val + (addN x1.rep x2.rep - 1 - k) - 1 + 1, 1,
        BitVec.ofNat 64 9)]) fun a ha =>
      imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha ⊢; omega)
    bc_run hlive hS [h16, h14, h13, h12, h11, h17, hl] at 0x800047c4
    bc_run hlive hS [h11, h13, h12, h17] at 0x800047b8 0x800047d8
    bc_run hlive hS [h11, h13, h12, h17] at 0x800047b8 0x800047d8
    · intro hne
      bv_nat at hne
      exact hnext (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
        (by bsimp [h16]; congr 1; omega) (by bsimp [hbr]) (by bsimp []; congr 1; omega)
        (by bsimp [h12]) (by bsimp [h11]) (by bsimp [h17])
    · intro he
      bv_nat at he
      have eN : k + 1 = addN x1.rep x2.rep := by omega
      rw [eN] at hb'
      exact sub_rmlz hlive cx hk hy.final hy.p (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
  · rw [if_neg hxb] at hr hbr
    bc_run hlive hS [h16, h14, h13, h12, h11, h17, hl, subw_ofNat] at 0x8000483c 0x800047c8
    · intro hne
      exact sub_copy_loop hlive cx hk hy ha _ k _ _ rfl hk1 hk2
        (st.keeps (by keeps_tac Keeps.refl _ _)) hb hbr (by bsimp [hr]) (by bsimp [h13])
        (by bsimp [h16]) (by bsimp [h12])
    · intro he
      bv_nat at he
      omega

/-- The borrow propagation from `0x800047b8`, position `k` on. -/
theorem sub_borrow_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin) :
    ∀ n k (R : Nat → BitVec 64) (M : Mem), addN x1.rep x2.rep - 1 - k = n →
      max x1.rep.scale x2.rep.scale + x2.rep.len ≤ k → k < addN x1.rep x2.rep →
      SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin k) :: L) →
      R 16 = BitVec.ofNat 64 (x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - k)) →
      R 14 = BitVec.ofNat 64 (subB x1.rep x2.rep k) →
      R 13 = BitVec.ofNat 64 (y.rep.val + (addN x1.rep x2.rep - 1 - k)) →
      R 12 = BitVec.ofNat 64 (y.rep.val - 1) → R 11 = 18446744073709551615#64 →
      R 17 = BitVec.ofNat 64 9 → DW live S Q 0x800047b8#64 R M := by
  intro n
  induction n with
  | zero =>
    intro k R M hn hk1 hk2 st hb h16 h14 h13 h12 h11 h17
    exact sub_borrow_body hlive cx hk hy ha hk1 hk2 st hb h16 h14 h13 h12 h11 h17
      fun h => absurd h (by omega)
  | succ n ih =>
    intro k R M hn hk1 hk2 st hb h16 h14 h13 h12 h11 h17
    exact sub_borrow_body hlive cx hk hy ha hk1 hk2 st hb h16 h14 h13 h12 h11 h17
      fun h R' M' st' hb' => ih (k + 1) R' M' (by omega) (by omega) h st' hb'

/-- `n2`'s positions done at `0x80004790` (`k = S + l2`): with `l1 = l2`
the result is complete; otherwise the borrow propagation over `n1`'s
`l1 - l2` top digits. -/
theorem sub_high_entry {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hk1 : k = max x1.rep.scale x2.rep.scale + x2.rep.len)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin k) :: L))
    (h16 : R 16 = BitVec.ofNat 64 (x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - k)))
    (h14 : R 14 = BitVec.ofNat 64 (subB x1.rep x2.rep k))
    (h13 : R 13 = BitVec.ofNat 64 (y.rep.val + (addN x1.rep x2.rep - 1 - k)))
    (h9 : R 9 = BitVec.ofNat 64 x1.rep.len) :
    DW live S Q 0x80004790#64 R M := by
  have hNl := hy.N_lt
  have hle := ha.le
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have a3 := hs1.size; have b3 := hs2.lenPos
  have hls := hy.lenScale
  simp only [heapStart, heapEnd] at v1 v2
  simp only [addN, loopLen, addZ, List.length_replicate] at hls hNl
  have eN1 : addN x1.rep x2.rep ≤ max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale :=
    Nat.le_refl _
  have eN2 : max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale ≤ addN x1.rep x2.rep :=
    Nat.le_refl _
  have h18 := st.r18; have h19 := st.r19; have h20 := st.r20
  bc_run hlive hS [h18, h19] at 0x800047d8 0x80004794
  · intro he
    bv_nat at he
    have eN : k = addN x1.rep x2.rep := by omega
    rw [eN] at hb
    exact sub_rmlz hlive cx hk hy.final hy.p (st.keeps (by keeps_tac Keeps.refl _ _)) hb
  · intro hne
    bv_nat at hne
    bc_run hlive hS [h9, h20, h13, h16, h14, subw_ofNat, not_blez, se12_fff, word_pred, sxw_ofNat,
      shl_shr32, add_not_ofNat] at 0x800047b8
    bc_run hlive hS [h13, h16, h14, se12_fff, word_pred, sxw_ofNat, shl_shr32, add_not_ofNat]
      at 0x800047b8
    exact sub_borrow_loop hlive cx hk hy ha _ k _ _ rfl (by omega) (by omega)
      (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [h16]) (by bsimp [h14]) (by bsimp [h13])
      (by bsimp []; congr 1; omega) (by bsimp []) (by bsimp [])

end Dc.Mach
