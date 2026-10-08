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

/-- `negw` of a small natural. -/
theorem negw_nat {a : Nat} (ha : a < 2 ^ 30) :
    BitVec.signExtend 64 (0#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 a)) =
      BitVec.ofInt 64 (-(a : Int)) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), toInt_ofInt64 (by omega) (by omega)]
  have e : 0#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) = BitVec.ofInt 32 (-(a : Int)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A small integer word is zero exactly when the integer is. -/
theorem ofInt64_eq_zero {u : Int} (h1 : -2 ^ 63 ≤ u) (h2 : u < 2 ^ 63) :
    (BitVec.ofInt 64 u = 0#64) ↔ u = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toInt h
    rw [toInt_ofInt64 h1 h2] at this
    simpa using this
  · intro h; subst h; rfl

/-- A nonnegative integer word is a natural one. -/
theorem ofInt_nonneg {u : Int} (h : 0 ≤ u) : BitVec.ofInt 64 u = BitVec.ofNat 64 u.toNat := by
  rw [← ofInt_natCast64, Int.toNat_of_nonneg h]

/-- `addiw r, r, 10` on a word holding `-10 ≤ u < 0`. -/
theorem addiw10_int {u : Int} (h1 : -10 ≤ u) (h2 : u < 0) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofInt 64 u + 10#64)) =
      BitVec.ofNat 64 (u + 10).toNat := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, u = -((n : Int) + 1) := ⟨(-u - 1).toNat, by omega⟩
  subst hn
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨
    n = 9) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

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

/-- The borrow stays zero while the subtrahend is zero at every position. -/
theorem borrowAt_eq_zero {xs ys : List Nat} (hl : xs.length = ys.length) :
    ∀ k, k ≤ xs.length → (∀ j, j < k → ys.getD j 0 = 0) → borrowAt xs ys 0 k = 0
  | 0, _, _ => borrowAt_zero _ _ _
  | k + 1, hk, h => by
    rw [borrowAt_succ _ _ _ _ hl (by omega), borrowAt_eq_zero hl k (by omega)
      fun j hj => h j (by omega), h k (by omega)]
    simp

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
    (h16 : R 16 = BitVec.ofNat 64 (x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - k) - 1))
    (h14 : R 14 = BitVec.ofNat 64 (subB x1.rep x2.rep k))
    (h13 : R 13 = BitVec.ofNat 64 (y.rep.val + (addN x1.rep x2.rep - k) - 1))
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
      (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [h16]; congr 1; omega) (by bsimp [h14])
      (by bsimp [h13]; congr 1; omega) (by bsimp []; congr 1; omega) (by bsimp []) (by bsimp [])

/-! ## The subtract loop -/

/-- The subtract loop's geometry: positions from `k0 = S - min s1 s2` on,
`c = l2 + min s1 s2` of them, the operands' digits at `P1`, `P2` and the
result's slots at `Y` going down. -/
structure SubMain (a b : NumRep) (yv k0 c P1 P2 Y : Nat) : Prop where
  k0 : k0 = max a.scale b.scale - min a.scale b.scale
  c : c = b.len + min a.scale b.scale
  P1 : P1 = a.val + (a.len + min a.scale b.scale - 1)
  P2 : P2 = b.val + (b.len + min a.scale b.scale - 1)
  Y : Y = yv + (max a.len b.len + min a.scale b.scale - 1)

/-- The registers of the subtract loop at `0x80004740` after `j`
positions. -/
structure SubRegs (R : Nat → BitVec 64) (P1 P2 Y c j borrow D : Nat) : Prop where
  r12 : R 12 = BitVec.ofNat 64 (P1 - j)
  r11 : R 11 = BitVec.ofNat 64 (P2 - j)
  r17 : R 17 = BitVec.ofNat 64 (Y - j)
  r14 : R 14 = BitVec.ofNat 64 borrow
  r28 : R 28 = BitVec.ofNat 64 (P1 - c)
  r8 : R 8 = BitVec.ofNat 64 c
  r13 : R 13 = BitVec.ofNat 64 Y
  r16 : R 16 = BitVec.ofNat 64 P1
  r9 : R 9 = BitVec.ofNat 64 D

/-- The subtract loop's store at `0x8000476c`: the digit word `v` of
position `k0 + j` into the slot `Y - j`, the borrow out in `a4`. -/
theorem sub_main_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c P1 P2 Y j : Nat} {v : BitVec 64}
    (cx : SubCtx S R0 sp) (hy : SubSum y x1.rep x2.rep smin)
    (hg : SubMain x1.rep x2.rep y.rep.val k0 c P1 P2 Y) (hj : j < c)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin (k0 + j)) :: L))
    (h15 : R 15 = v) (hv : sbData v = BitVec.ofNat 8 ((subR x1.rep x2.rep).getD (k0 + j) 0))
    (h14 : R 14 = BitVec.ofNat 64 (subB x1.rep x2.rep (k0 + j + 1)))
    (h12 : R 12 = BitVec.ofNat 64 (P1 - j - 1)) (h11 : R 11 = BitVec.ofNat 64 (P2 - j - 1))
    (h17 : R 17 = BitVec.ofNat 64 (Y - j - 1)) (h28 : R 28 = BitVec.ofNat 64 (P1 - c))
    (h8 : R 8 = BitVec.ofNat 64 c) (h13 : R 13 = BitVec.ofNat 64 Y)
    (h16 : R 16 = BitVec.ofNat 64 P1) (h9 : R 9 = BitVec.ofNat 64 x1.rep.len)
    (hc : c ≤ P1) (hP : P1 < 2 ^ 63)
    (hnext : j + 1 < c → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (k0 + (j + 1))) :: L) →
      SubRegs R' P1 P2 Y c (j + 1) (subB x1.rep x2.rep (k0 + (j + 1))) x1.rep.len →
      DW live S Q 0x80004740#64 R' M')
    (hexit : j + 1 = c → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (k0 + (j + 1))) :: L) →
      SubRegs R' P1 P2 Y c (j + 1) (subB x1.rep x2.rep (k0 + (j + 1))) x1.rep.len →
      DW live S Q 0x80004774#64 R' M') :
    DW live S Q 0x8000476c#64 R M := by
  have hm := hy.model
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hls := hy.lenScale
  have hNl := hy.N_lt
  have hlp := hy.lenPos
  simp only [heapStart, heapEnd] at v1 v2
  simp only [addN, loopLen, addZ, List.length_replicate] at hls hNl
  have g1 := hg.k0; have g2 := hg.c; have g5 := hg.Y
  have hk : k0 + j < addN x1.rep x2.rep := by simp only [addN, loopLen]; omega
  have hb' : BcHeap S (writeLog M [(Y - j - 1 + 1, 1, v)]) H F
      (withDs y (subDs x1.rep x2.rep smin (k0 + j + 1)) :: L) := by
    rw [show Y - j - 1 + 1 = y.rep.val + (addN x1.rep x2.rep - 1 - (k0 + j)) by
      simp only [addN, loopLen]; omega]
    exact BcHeap.storeSum hy.lenScale hk (by rw [hm.rl]; exact hk) (hm.getD_lt_r _) hb hv
  have st' := st.heap cx (M' := writeLog M [(Y - j - 1 + 1, 1, v)]) fun a ha =>
    imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  bc_run hlive hS [h15, h17, h28, h12] at 0x80004740 0x80004774
  · intro hne
    bv_nat at hne
    exact hnext (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [h12, Nat.sub_sub], by bsimp [h11, Nat.sub_sub], by bsimp [h17, Nat.sub_sub],
        by bsimp [h14, Nat.add_assoc], by bsimp [h28], by bsimp [h8], by bsimp [h13], by bsimp [h16], by bsimp [h9]⟩
  · intro he
    bv_nat at he
    exact hexit (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [h12, Nat.sub_sub], by bsimp [h11, Nat.sub_sub], by bsimp [h17, Nat.sub_sub],
        by bsimp [h14, Nat.add_assoc], by bsimp [h28], by bsimp [h8], by bsimp [h13], by bsimp [h16], by bsimp [h9]⟩

/-- One position of the subtract loop at `0x80004740`: the operands' digits
`d1`, `d2` at `P1 - j`, `P2 - j`, the borrow `b` in. -/
theorem sub_main_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c P1 P2 Y j d1 d2 b : Nat}
    (cx : SubCtx S R0 sp) (hy : SubSum y x1.rep x2.rep smin)
    (hg : SubMain x1.rep x2.rep y.rep.val k0 c P1 P2 Y) (hj : j < c)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin (k0 + j)) :: L))
    (sr : SubRegs R P1 P2 Y c j b x1.rep.len)
    (l1 : ldv .lbu M (P1 - j) = BitVec.ofNat 64 d1) (l2 : ldv .lbu M (P2 - j) = BitVec.ofNat 64 d2)
    (hd1 : d1 < 10) (hd2 : d2 < 10) (hbl : b ≤ 1)
    (a1 : 2147603920 ≤ P1 - j) (a2 : P1 - j < 2273312768)
    (b1 : 2147603920 ≤ P2 - j) (b2 : P2 - j < 2273312768) (hc : c ≤ P1) (hP : P1 < 2 ^ 63)
    (hYj : j < Y)
    (hr : (subR x1.rep x2.rep).getD (k0 + j) 0 =
      if d1 < d2 + b then d1 + 10 - d2 - b else d1 - d2 - b)
    (hbs : subB x1.rep x2.rep (k0 + j + 1) = if d1 < d2 + b then 1 else 0)
    (hnext : j + 1 < c → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (k0 + (j + 1))) :: L) →
      SubRegs R' P1 P2 Y c (j + 1) (subB x1.rep x2.rep (k0 + (j + 1))) x1.rep.len →
      DW live S Q 0x80004740#64 R' M')
    (hexit : j + 1 = c → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (k0 + (j + 1))) :: L) →
      SubRegs R' P1 P2 Y c (j + 1) (subB x1.rep x2.rep (k0 + (j + 1))) x1.rep.len →
      DW live S Q 0x80004774#64 R' M') :
    DW live S Q 0x80004740#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h12 := sr.r12; have h11 := sr.r11; have h17 := sr.r17; have h14 := sr.r14
  have h28 := sr.r28; have h8 := sr.r8; have h13 := sr.r13; have h16 := sr.r16
  have h9 := sr.r9
  by_cases hlt : d1 < d2 + b
  · rw [if_pos hlt] at hr hbs
    bc_run hlive hS [h12, h11, h17, h14, h28, l1, l2, subw_nat, subw_int_nat, toInt_ofInt64,
      BitVec.toInt_zero] at 0x8000476c
    · intro hneg; omega
    · intro hneg
      bc_run hlive hS [h12, h11, h17, h14, h28, addiw10_int] at 0x8000476c
      exact sub_main_tail hlive cx hy hg hj (st.keeps (by keeps_tac Keeps.refl _ _)) hb
        (v := BitVec.ofNat 64 ((↑d1 - ↑d2 - ↑b + 10 : Int).toNat))
        (by bsimp []) (by rw [sbData_ofNat, hr]; congr 1; omega) (by bsimp [hbs])
        (by bsimp [h12]) (by bsimp [h11]) (by bsimp [h17]) (by bsimp [h28]) (by bsimp [h8])
        (by bsimp [h13]) (by bsimp [h16]) (by bsimp [h9]) hc hP hnext hexit
  · rw [if_neg hlt] at hr hbs
    bc_run hlive hS [h12, h11, h17, h14, h28, l1, l2, subw_ofNat, toInt_ofNat_small,
      BitVec.toInt_zero] at 0x8000476c
    · intro _
      exact sub_main_tail hlive cx hy hg hj (st.keeps (by keeps_tac Keeps.refl _ _)) hb
        (v := BitVec.ofNat 64 (d1 - d2 - b))
        (by bsimp []) (by rw [sbData_ofNat, hr]) (by bsimp [hbs])
        (by bsimp [h12]) (by bsimp [h11]) (by bsimp [h17]) (by bsimp [h28]) (by bsimp [h8])
        (by bsimp [h13]) (by bsimp [h16]) (by bsimp [h9]) hc hP hnext hexit
    · intro hneg; omega

/-- After the subtract loop at `0x80004774`: `a3`, `a6` past the `c`
positions, then the positions above `n2`. -/
theorem sub_main_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c P1 P2 Y : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hg : SubMain x1.rep x2.rep y.rep.val k0 c P1 P2 Y)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin (k0 + c)) :: L))
    (sr : SubRegs R P1 P2 Y c c (subB x1.rep x2.rep (k0 + c)) x1.rep.len) :
    DW live S Q 0x80004774#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a3 := hs1.size; have a4 := hs1.vHi
  have b3 := hs2.lenPos
  have hNl := hy.N_lt
  have hle := ha.le
  simp only [heapStart, heapEnd] at v1 a1 a4
  simp only [addN, loopLen] at hNl
  have g1 := hg.k0; have g2 := hg.c; have g3 := hg.P1; have g5 := hg.Y
  have h8 := sr.r8; have h13 := sr.r13; have h16 := sr.r16; have h14 := sr.r14; have h9 := sr.r9
  bc_run hlive hS [h8, h13, h16, se12_fff, word_pred, sxw_ofNat, shl_shr32, sub_ofNat] at 0x80004790
  exact sub_high_entry hlive cx hk hy ha (k := k0 + c) (by omega)
    (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp []; congr 1; omega) (by bsimp [h14])
    (by bsimp []; congr 1; simp only [addN, loopLen]; omega) (by bsimp [h9])

/-- The subtract loop at `0x80004740`: `j` positions after `k0` done. -/
theorem sub_main_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c P1 P2 Y : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hg : SubMain x1.rep x2.rep y.rep.val k0 c P1 P2 Y) :
    ∀ n j (R : Nat → BitVec 64) (M : Mem), c - j = n → j < c →
      SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin (k0 + j)) :: L) →
      SubRegs R P1 P2 Y c j (subB x1.rep x2.rep (k0 + j)) x1.rep.len →
      DW live S Q 0x80004740#64 R M := by
  have hm := hy.model
  have hle := ha.le
  have g1 := hg.k0; have g2 := hg.c; have g4 := hg.P1; have g5 := hg.P2; have g6 := hg.Y
  intro n
  induction n with
  | zero => intro j R M h1 h2; omega
  | succ n ih =>
    intro j R M hn hj st hb sr
    have hn1 := hb.nums x1 (List.mem_cons_of_mem _ ha.m1)
    have hn2 := hb.nums x2 (List.mem_cons_of_mem _ ha.m2)
    have hs1 := hn1.shape; have hs2 := hn2.shape
    have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a3 := hs1.size; have a4 := hs1.vHi
    have b1 := hs2.vLo; have b2 := hs2.ptrLe; have b3 := hs2.size; have b4 := hs2.vHi
    have hn0 := hb.nums _ List.mem_cons_self
    have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
    have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
    simp only [heapStart, heapEnd] at a1 a4 b1 b4 v1
    have hx := addXs_in hs1 (b := x2.rep) (k := k0 + j) (by omega) (by omega)
    have hyy := addYs_in hs2 (a := x1.rep) (k := k0 + j) (by omega) (by omega)
    have l1 := hn1.lbu (i := x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j)) (by omega)
    have l2 := hn2.lbu (i := x2.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j)) (by omega)
    rw [show x1.rep.val + (x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j)) = P1 - j by
      omega] at l1
    rw [show x2.rep.val + (x2.rep.len + max x1.rep.scale x2.rep.scale - 1 - (k0 + j)) = P2 - j by
      omega] at l2
    have hkN : k0 + j < addN x1.rep x2.rep := by simp only [addN, loopLen]; omega
    have ⟨hr, hbs⟩ := hm.step hkN
    rw [hx, hyy] at hr hbs
    exact sub_main_body hlive cx hy hg hj st hb sr l1 l2 (hn1.getD_lt _) (hn2.getD_lt _)
      (hm.borrow_le _) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hr hbs (fun e R' M' => ih (j + 1) R' M' (by omega) e)
      (fun e R' M' st' hb' sr' => by
        rw [e] at hb' sr'
        exact sub_main_exit hlive cx hk hy ha hg st' hb' sr')

/-- The join at `0x8000472c`: `k0` positions done, `c = l2 + min s1 s2`
into `s0`, then the subtract loop. -/
theorem sub_join {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {k0 c P1 P2 Y : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hg : SubMain x1.rep x2.rep y.rep.val k0 c P1 P2 Y)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin k0) :: L))
    (h16 : R 16 = BitVec.ofNat 64 P1) (h13 : R 13 = BitVec.ofNat 64 Y)
    (h11 : R 11 = BitVec.ofNat 64 P2) (h14 : R 14 = BitVec.ofNat 64 (subB x1.rep x2.rep k0))
    (h8 : R 8 = BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale))
    (h9 : R 9 = BitVec.ofNat 64 x1.rep.len) :
    DW live S Q 0x8000472c#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have := hs1.size; have := hs2.size; have := hs1.lenPos; have := hs2.lenPos
  have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a4 := hs1.vHi
  simp only [heapStart, heapEnd] at a1 a4
  have g2 := hg.c; have g3 := hg.P1
  have h20 := st.r20
  have e1 : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 x2.rep.len) +
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale))) =
      BitVec.ofNat 64 c := by
    rw [addw_ofNat (by omega)]; congr 1; omega
  bc_run hlive hS [h20, h8, e1] at 0x80004740 0x80004790
  · intro hc; exact absurd hc (not_blez (by omega) (by omega))
  · intro _
    bc_run hlive hS [h20, h8, e1, h16, h13, sub_ofNat] at 0x80004740
    rw [← Nat.add_zero k0] at hb h14
    exact sub_main_loop hlive cx hk hy ha hg _ 0 _ _ rfl (by omega)
      (st.keeps (by keeps_tac Keeps.refl _ _)) hb
      ⟨by bsimp [h16], by bsimp [h11], by bsimp [h13], by bsimp [h14], by bsimp [h16, e1],
        by bsimp [e1], by bsimp [h13], by bsimp [h16], by bsimp [h9]⟩

/-! ## The fraction digits below the shorter scale -/

/-- The registers of the copy of `n1`'s extra fraction digits at
`0x80004704` after `j` digits: `a5` at `n1`'s digit, `a4` at the result's
slot, `t1` where `a5` stops, `a7 = n - 1`. -/
structure FracARegs (R : Nat → BitVec 64) (A Y0 n P2 m D j : Nat) : Prop where
  r15 : R 15 = BitVec.ofNat 64 (A - j)
  r14 : R 14 = BitVec.ofNat 64 (Y0 - j)
  r6 : R 6 = BitVec.ofNat 64 (A - n)
  r17 : R 17 = BitVec.ofNat 64 (n - 1)
  r13 : R 13 = BitVec.ofNat 64 Y0
  r16 : R 16 = BitVec.ofNat 64 A
  r11 : R 11 = BitVec.ofNat 64 P2
  r8 : R 8 = BitVec.ofNat 64 m
  r9 : R 9 = BitVec.ofNat 64 D

/-- The geometry of the fraction phases: `n1`'s last digit at `A`,
`n2`'s at `B`, the result's last slot at `Y0`. -/
structure FracGeom (a b : NumRep) (yv A B Y0 : Nat) : Prop where
  eA : A = a.val + (a.len + a.scale - 1)
  eB : B = b.val + (b.len + b.scale - 1)
  eY : Y0 = yv + (max a.len b.len + max a.scale b.scale - 1)

/-- After the copy of `n1`'s extra fraction digits, from `0x80004718`. -/
theorem sub_fracA_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A B Y0 : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hs : x2.rep.scale < x1.rep.scale) (hf : FracGeom x1.rep x2.rep y.rep.val A B Y0)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin (x1.rep.scale - x2.rep.scale)) :: L))
    (fr : FracARegs R A Y0 (x1.rep.scale - x2.rep.scale) B x2.rep.scale x1.rep.len
      (x1.rep.scale - x2.rep.scale)) :
    DW live S Q 0x80004718#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a3 := hs1.size; have a4 := hs1.vHi
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hNl := hy.N_lt
  simp only [addN, loopLen] at hNl
  simp only [heapStart, heapEnd] at a1 a4 v1
  have f1 := hf.eA; have f2 := hf.eB; have f3 := hf.eY
  have l1p := hs1.lenPos; have l2p := hs2.lenPos
  have h13 := fr.r13; have h16 := fr.r16; have h17 := fr.r17; have h11 := fr.r11
  have h8 := fr.r8; have h9 := fr.r9
  have hb0 : subB x1.rep x2.rep (x1.rep.scale - x2.rep.scale) = 0 :=
    borrowAt_eq_zero (by rw [hy.model.xl, hy.model.yl]) _
      (by rw [hy.model.xl]; simp only [addN, loopLen]; omega)
      fun j hj => addYs_out hs2 (.inl (by omega))
  have hg : SubMain x1.rep x2.rep y.rep.val (x1.rep.scale - x2.rep.scale)
      (x2.rep.len + x2.rep.scale) (A - (x1.rep.scale - x2.rep.scale)) B
      (Y0 - (x1.rep.scale - x2.rep.scale)) :=
    ⟨by omega, by omega, by omega, by omega, by omega⟩
  bc_run hlive hS [h13, h16, h17, word_pred, sub_ofNat] at 0x8000472c
  exact sub_join hlive cx hk hy ha hg
    (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp []; congr 1; omega)
    (by bsimp []; congr 1; omega) (by bsimp [h11]) (by bsimp [hb0])
    (by bsimp [h8]; congr 1; omega) (by bsimp [h9])

/-- One step of the copy of `n1`'s extra fraction digits at `0x80004704`:
`n1`'s digit `d` at `A - j` into the slot `Y0 - j`. -/
theorem sub_fracA_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A Y0 n P2 m D j d : Nat}
    (cx : SubCtx S R0 sp) (hy : SubSum y x1.rep x2.rep smin)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin j) :: L))
    (fr : FracARegs R A Y0 n P2 m D j) (hj : j < n) (hnA : n ≤ A) (hA : A < 2 ^ 63)
    (hl : ldv .lbu M (A - j) = BitVec.ofNat 64 d) (hr : (subR x1.rep x2.rep).getD j 0 = d)
    (a1 : 2147603920 ≤ A - j) (a2 : A - j < 2273312768) (hjN : j < addN x1.rep x2.rep)
    (hY : Y0 = y.rep.val + (addN x1.rep x2.rep - 1))
    (hnext : j + 1 < n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (j + 1)) :: L) →
      FracARegs R' A Y0 n P2 m D (j + 1) → DW live S Q 0x80004704#64 R' M')
    (hexit : j + 1 = n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (j + 1)) :: L) →
      FracARegs R' A Y0 n P2 m D (j + 1) → DW live S Q 0x80004718#64 R' M') :
    DW live S Q 0x80004704#64 R M := by
  have hm := hy.model
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hls := hy.lenScale
  simp only [heapStart, heapEnd] at v1 v2
  simp only [addN, loopLen, addZ, List.length_replicate] at hls hjN hY
  have hb' : BcHeap S (writeLog M [(Y0 - j - 1 + 1, 1, BitVec.ofNat 64 d)]) H F
      (withDs y (subDs x1.rep x2.rep smin (j + 1)) :: L) := by
    rw [show Y0 - j - 1 + 1 = y.rep.val + (addN x1.rep x2.rep - 1 - j) by
      simp only [addN, loopLen]; omega]
    exact BcHeap.storeSum hy.lenScale (by simp only [addN, loopLen]; omega)
      (by rw [hm.rl]; simp only [addN, loopLen]; omega) (hm.getD_lt_r j) hb
      (by rw [sbData_ofNat, hr])
  have st' := st.heap cx (M' := writeLog M [(Y0 - j - 1 + 1, 1, BitVec.ofNat 64 d)]) fun a ha =>
    imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  have h15 := fr.r15; have h14 := fr.r14; have h6 := fr.r6; have h17 := fr.r17
  have h13 := fr.r13; have h16 := fr.r16; have h11 := fr.r11; have h8 := fr.r8; have h9 := fr.r9
  bc_run hlive hS [h15, h14, hl] at 0x80004714
  bc_run hlive hS [h15, h14, hl, h6] at 0x80004704 0x80004718
  · intro hne
    bv_nat at hne
    exact hnext (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [Nat.sub_sub], by bsimp [Nat.sub_sub], by bsimp [h6], by bsimp [h17], by bsimp [h13],
        by bsimp [h16], by bsimp [h11], by bsimp [h8], by bsimp [h9]⟩
  · intro he
    bv_nat at he
    exact hexit (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [Nat.sub_sub], by bsimp [Nat.sub_sub], by bsimp [h6], by bsimp [h17], by bsimp [h13],
        by bsimp [h16], by bsimp [h11], by bsimp [h8], by bsimp [h9]⟩

/-- The copy of `n1`'s extra fraction digits at `0x80004704` (`s2 < s1`):
`n1`'s last `s1 - s2` digits into the result, then the join. -/
theorem sub_fracA {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A B Y0 : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hs : x2.rep.scale < x1.rep.scale) (hf : FracGeom x1.rep x2.rep y.rep.val A B Y0) :
    ∀ m j (R : Nat → BitVec 64) (M : Mem), x1.rep.scale - x2.rep.scale - j = m →
      j < x1.rep.scale - x2.rep.scale →
      SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin j) :: L) →
      FracARegs R A Y0 (x1.rep.scale - x2.rep.scale) B x2.rep.scale x1.rep.len j →
      DW live S Q 0x80004704#64 R M := by
  have hm := hy.model
  have f1 := hf.eA; have f3 := hf.eY
  intro m
  induction m with
  | zero => intro j R M h1 h2; omega
  | succ m ih =>
    intro j R M hm' hj st hb fr
    have hn1 := hb.nums x1 (List.mem_cons_of_mem _ ha.m1)
    have hs1 := hn1.shape
    have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
    have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a3 := hs1.size; have a4 := hs1.vHi
    simp only [heapStart, heapEnd] at a1 a4
    have hl := hn1.lbu (i := x1.rep.len + x1.rep.scale - 1 - j) (by omega)
    rw [show x1.rep.val + (x1.rep.len + x1.rep.scale - 1 - j) = A - j by omega] at hl
    have hjN : j < addN x1.rep x2.rep := by simp only [addN, loopLen]; omega
    have hx := addXs_in hs1 (b := x2.rep) (k := j) (by omega) (by omega)
    have hy0 := addYs_out hs2 (a := x1.rep) (k := j) (.inl (by omega))
    have hb0 : subB x1.rep x2.rep j = 0 :=
      borrowAt_eq_zero (by rw [hm.xl, hm.yl]) _ (by rw [hm.xl]; omega)
        fun i hi => addYs_out hs2 (.inl (by omega))
    obtain ⟨hr, -⟩ := hm.step hjN
    rw [hx, hy0, hb0] at hr
    simp only [Nat.add_zero, Nat.not_lt_zero, ite_false, if_false, Nat.sub_zero] at hr
    exact sub_fracA_body hlive cx hy st hb fr hj (by omega) (by omega) hl
      (by rw [hr, show x1.rep.len + max x1.rep.scale x2.rep.scale - 1 - j =
        x1.rep.len + x1.rep.scale - 1 - j by omega]) (by omega) (by omega) hjN
      (by simp only [addN, loopLen]; omega)
      (fun e R' M' => ih (j + 1) R' M' (by omega) e)
      (fun e R' M' st' hb' fr' => by
        rw [e] at hb' fr'
        exact sub_fracA_exit hlive cx hk hy ha hs hf st' hb' fr')

/-- The copy's entry at `0x800046e0` (`s1 ≠ min s1 s2`, so `s2 < s1`). -/
theorem sub_fracA_entry {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A B Y0 : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hs : x2.rep.scale < x1.rep.scale) (hf : FracGeom x1.rep x2.rep y.rep.val A B Y0)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin 0) :: L))
    (h15 : R 15 = BitVec.ofNat 64 x1.rep.scale) (h8 : R 8 = BitVec.ofNat 64 x2.rep.scale)
    (h13 : R 13 = BitVec.ofNat 64 Y0) (h16 : R 16 = BitVec.ofNat 64 A)
    (h11 : R 11 = BitVec.ofNat 64 B) (h9 : R 9 = BitVec.ofNat 64 x1.rep.len) :
    DW live S Q 0x800046e0#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have a1 := hs1.vLo; have a2 := hs1.ptrLe; have a3 := hs1.size; have a4 := hs1.vHi
  have f1 := hf.eA
  simp only [heapStart, heapEnd] at a1 a4
  bc_run hlive hS [h15, h8, subw_ofNat, not_blez] at 0x800046e8
  bc_run hlive hS [h15, h8, h13, h16, se12_fff, word_pred, sxw_ofNat, subw_ofNat, shl_shr32,
    add_not_ofNat] at 0x80004704
  exact sub_fracA hlive cx hk hy ha hs hf _ 0 _ _ rfl (by omega)
    (st.keeps (by keeps_tac Keeps.refl _ _)) hb
    ⟨by bsimp [h16], by bsimp [h13], by bsimp []; congr 1; omega, by bsimp [],
      by bsimp [h13], by bsimp [h16], by bsimp [h11], by bsimp [h8], by bsimp [h9]⟩

/-- The registers of the subtraction of `n2`'s extra fraction digits from
zero at `0x80004878` after `j` digits: `a5` at `n2`'s digit, `a7` at the
result's slot, `t4` where `a5` stops, `t3 = n - 1`, `a4` the borrow. -/
structure FracBRegs (R : Nat → BitVec 64) (B Y0 n A m D j borrow : Nat) : Prop where
  r15 : R 15 = BitVec.ofNat 64 (B - j)
  r17 : R 17 = BitVec.ofNat 64 (Y0 - j)
  r29 : R 29 = BitVec.ofNat 64 (B - n)
  r28 : R 28 = BitVec.ofNat 64 (n - 1)
  r14 : R 14 = BitVec.ofNat 64 borrow
  r13 : R 13 = BitVec.ofNat 64 Y0
  r16 : R 16 = BitVec.ofNat 64 A
  r11 : R 11 = BitVec.ofNat 64 B
  r8 : R 8 = BitVec.ofNat 64 m
  r9 : R 9 = BitVec.ofNat 64 D

/-- The store at `0x8000489c` of the subtraction of `n2`'s extra fraction
digits from zero: the digit word `v` (in `t1`) into the slot `Y0 - j`. -/
theorem sub_fracB_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {B Y0 n A m D j : Nat} {v : BitVec 64}
    (cx : SubCtx S R0 sp) (hy : SubSum y x1.rep x2.rep smin)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin j) :: L))
    (hj : j < n) (hnB : n ≤ B) (hB : B < 2 ^ 63)
    (h6 : R 6 = v) (hv : sbData v = BitVec.ofNat 8 ((subR x1.rep x2.rep).getD j 0))
    (h14 : R 14 = BitVec.ofNat 64 (subB x1.rep x2.rep (j + 1)))
    (h15 : R 15 = BitVec.ofNat 64 (B - j - 1)) (h17 : R 17 = BitVec.ofNat 64 (Y0 - j - 1))
    (h29 : R 29 = BitVec.ofNat 64 (B - n)) (h28 : R 28 = BitVec.ofNat 64 (n - 1))
    (h13 : R 13 = BitVec.ofNat 64 Y0) (h16 : R 16 = BitVec.ofNat 64 A)
    (h11 : R 11 = BitVec.ofNat 64 B) (h8 : R 8 = BitVec.ofNat 64 m) (h9 : R 9 = BitVec.ofNat 64 D)
    (hjN : j < addN x1.rep x2.rep) (hY : Y0 = y.rep.val + (addN x1.rep x2.rep - 1))
    (hnext : j + 1 < n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (j + 1)) :: L) →
      FracBRegs R' B Y0 n A m D (j + 1) (subB x1.rep x2.rep (j + 1)) →
      DW live S Q 0x80004878#64 R' M')
    (hexit : j + 1 = n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (j + 1)) :: L) →
      FracBRegs R' B Y0 n A m D (j + 1) (subB x1.rep x2.rep (j + 1)) →
      DW live S Q 0x800048a4#64 R' M') :
    DW live S Q 0x8000489c#64 R M := by
  have hm := hy.model
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hls := hy.lenScale
  simp only [heapStart, heapEnd] at v1 v2
  simp only [addN, loopLen, addZ, List.length_replicate] at hls hjN hY
  have hjN' : j < addN x1.rep x2.rep := by simp only [addN, loopLen]; omega
  have hb' : BcHeap S (writeLog M [(Y0 - j - 1 + 1, 1, v)]) H F
      (withDs y (subDs x1.rep x2.rep smin (j + 1)) :: L) := by
    rw [show Y0 - j - 1 + 1 = y.rep.val + (addN x1.rep x2.rep - 1 - j) by
      simp only [addN, loopLen]; omega]
    exact BcHeap.storeSum hy.lenScale hjN' (by rw [hm.rl]; exact hjN') (hm.getD_lt_r j) hb hv
  have st' := st.heap cx (M' := writeLog M [(Y0 - j - 1 + 1, 1, v)]) fun a ha =>
    imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  bc_run hlive hS [h6, h15, h17, h29] at 0x80004878 0x800048a4
  · intro hne
    bv_nat at hne
    exact hnext (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [h15, Nat.sub_sub], by bsimp [h17, Nat.sub_sub], by bsimp [h29], by bsimp [h28],
        by bsimp [h14], by bsimp [h13], by bsimp [h16], by bsimp [h11], by bsimp [h8],
        by bsimp [h9]⟩
  · intro he
    bv_nat at he
    exact hexit (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      ⟨by bsimp [h15, Nat.sub_sub], by bsimp [h17, Nat.sub_sub], by bsimp [h29], by bsimp [h28],
        by bsimp [h14], by bsimp [h13], by bsimp [h16], by bsimp [h11], by bsimp [h8],
        by bsimp [h9]⟩

/-- One step of the subtraction of `n2`'s extra fraction digits from zero at
`0x80004878`: `n2`'s digit `d` at `B - j`, the borrow `b` in. -/
theorem sub_fracB_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {B Y0 n A m D j d b : Nat}
    (cx : SubCtx S R0 sp) (hy : SubSum y x1.rep x2.rep smin)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin j) :: L))
    (fr : FracBRegs R B Y0 n A m D j b) (hj : j < n) (hnB : n ≤ B) (hB : B < 2 ^ 63)
    (hl : ldv .lbu M (B - j) = BitVec.ofNat 64 d) (hd : d < 10) (hbl : b ≤ 1)
    (hr : (subR x1.rep x2.rep).getD j 0 = if 0 < d + b then 10 - d - b else 0)
    (hbs : subB x1.rep x2.rep (j + 1) = if 0 < d + b then 1 else 0)
    (a1 : 2147603920 ≤ B - j) (a2 : B - j < 2273312768) (hjN : j < addN x1.rep x2.rep)
    (hY : Y0 = y.rep.val + (addN x1.rep x2.rep - 1)) (hYj : j < Y0)
    (hnext : j + 1 < n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (j + 1)) :: L) →
      FracBRegs R' B Y0 n A m D (j + 1) (subB x1.rep x2.rep (j + 1)) →
      DW live S Q 0x80004878#64 R' M')
    (hexit : j + 1 = n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin (j + 1)) :: L) →
      FracBRegs R' B Y0 n A m D (j + 1) (subB x1.rep x2.rep (j + 1)) →
      DW live S Q 0x800048a4#64 R' M') :
    DW live S Q 0x80004878#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h15 := fr.r15; have h17 := fr.r17; have h29 := fr.r29; have h28 := fr.r28
  have h14 := fr.r14; have h13 := fr.r13; have h16 := fr.r16; have h11 := fr.r11
  have h8 := fr.r8; have h9 := fr.r9
  by_cases hz : 0 < d + b
  · rw [if_pos hz] at hr hbs
    bc_run hlive hS [h15, h17, hl, h14, negw_nat, subw_int_nat, ofInt64_eq_zero] at 0x8000489c
    · intro hc; omega
    · intro _
      bc_run hlive hS [h15, h17, addiw10_int] at 0x8000489c
      exact sub_fracB_tail hlive cx hy (st.keeps (by keeps_tac Keeps.refl _ _)) hb hj hnB hB
        (v := BitVec.ofNat 64 ((-(d : Int) - b + 10).toNat)) (by bsimp [])
        (by rw [sbData_ofNat, hr]; congr 1; omega) (by bsimp [hbs]) (by bsimp [h15])
        (by bsimp [h17]) (by bsimp [h29]) (by bsimp [h28]) (by bsimp [h13]) (by bsimp [h16])
        (by bsimp [h11]) (by bsimp [h8]) (by bsimp [h9]) hjN hY hnext hexit
  · rw [if_neg hz] at hr hbs
    bc_run hlive hS [h15, h17, hl, h14, negw_nat, subw_int_nat, ofInt64_eq_zero] at 0x8000489c
    · intro _
      exact sub_fracB_tail hlive cx hy (st.keeps (by keeps_tac Keeps.refl _ _)) hb hj hnB hB
        (v := BitVec.ofNat 64 0) (by bsimp []) (by rw [sbData_ofNat, hr])
        (by bsimp [hbs]; exact (ofInt64_eq_zero (by omega) (by omega)).2 (by omega))
        (by bsimp [h15]) (by bsimp [h17]) (by bsimp [h29]) (by bsimp [h28]) (by bsimp [h13])
        (by bsimp [h16]) (by bsimp [h11]) (by bsimp [h8]) (by bsimp [h9]) hjN hY hnext hexit
    · intro hc; omega

/-- After the subtraction of `n2`'s extra fraction digits, from
`0x800048a4`. -/
theorem sub_fracB_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A B Y0 : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hs : x1.rep.scale < x2.rep.scale) (hf : FracGeom x1.rep x2.rep y.rep.val A B Y0)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin (x2.rep.scale - x1.rep.scale)) :: L))
    (fr : FracBRegs R B Y0 (x2.rep.scale - x1.rep.scale) A x1.rep.scale x1.rep.len
      (x2.rep.scale - x1.rep.scale) (subB x1.rep x2.rep (x2.rep.scale - x1.rep.scale))) :
    DW live S Q 0x800048a4#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have b1 := hs2.vLo; have b2 := hs2.ptrLe; have b3 := hs2.size; have b4 := hs2.vHi
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hNl := hy.N_lt
  simp only [addN, loopLen] at hNl
  simp only [heapStart, heapEnd] at b1 b4 v1
  have f1 := hf.eA; have f2 := hf.eB; have f3 := hf.eY
  have l1p := hs1.lenPos; have l2p := hs2.lenPos
  have h13 := fr.r13; have h16 := fr.r16; have h28 := fr.r28; have h11 := fr.r11
  have h8 := fr.r8; have h9 := fr.r9; have h14 := fr.r14
  have hg : SubMain x1.rep x2.rep y.rep.val (x2.rep.scale - x1.rep.scale)
      (x2.rep.len + x1.rep.scale) A (B - (x2.rep.scale - x1.rep.scale))
      (Y0 - (x2.rep.scale - x1.rep.scale)) :=
    ⟨by omega, by omega, by omega, by omega, by omega⟩
  bc_run hlive hS [h13, h11, h28, word_pred, sub_ofNat] at 0x8000472c
  exact sub_join hlive cx hk hy ha hg
    (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [h16])
    (by bsimp []; congr 1; omega) (by bsimp []; congr 1; omega) (by bsimp [h14])
    (by bsimp [h8]; congr 1; omega) (by bsimp [h9])

/-- The subtraction of `n2`'s extra fraction digits from zero at
`0x80004878` (`s1 < s2`), then the join. -/
theorem sub_fracB {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A B Y0 : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hs : x1.rep.scale < x2.rep.scale) (hf : FracGeom x1.rep x2.rep y.rep.val A B Y0) :
    ∀ m j (R : Nat → BitVec 64) (M : Mem), x2.rep.scale - x1.rep.scale - j = m →
      j < x2.rep.scale - x1.rep.scale →
      SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin j) :: L) →
      FracBRegs R B Y0 (x2.rep.scale - x1.rep.scale) A x1.rep.scale x1.rep.len j
        (subB x1.rep x2.rep j) →
      DW live S Q 0x80004878#64 R M := by
  have hm := hy.model
  have f2 := hf.eB; have f3 := hf.eY
  intro m
  induction m with
  | zero => intro j R M h1 h2; omega
  | succ m ih =>
    intro j R M hm' hj st hb fr
    have hn2 := hb.nums x2 (List.mem_cons_of_mem _ ha.m2)
    have hs2 := hn2.shape
    have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
    have b1 := hs2.vLo; have b2 := hs2.ptrLe; have b3 := hs2.size; have b4 := hs2.vHi
    have hn0 := hb.nums _ List.mem_cons_self
    have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
    have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
    simp only [heapStart, heapEnd] at b1 b4 v1
    have hl := hn2.lbu (i := x2.rep.len + x2.rep.scale - 1 - j) (by omega)
    rw [show x2.rep.val + (x2.rep.len + x2.rep.scale - 1 - j) = B - j by omega] at hl
    have hjN : j < addN x1.rep x2.rep := by simp only [addN, loopLen]; omega
    have hx0 := addXs_out hs1 (b := x2.rep) (k := j) (.inl (by omega))
    have hyy := addYs_in hs2 (a := x1.rep) (k := j) (by omega) (by omega)
    have ⟨hr, hbs⟩ := hm.step hjN
    rw [hx0, hyy, show x2.rep.len + max x1.rep.scale x2.rep.scale - 1 - j =
      x2.rep.len + x2.rep.scale - 1 - j by omega] at hr hbs
    simp only [Nat.zero_add, Nat.zero_sub] at hr
    exact sub_fracB_body hlive cx hy st hb fr hj (by omega) (by omega) hl (hn2.getD_lt _)
      (hm.borrow_le j) hr hbs (by omega) (by omega) hjN
      (by simp only [addN, loopLen]; omega) (by omega)
      (fun e R' M' => ih (j + 1) R' M' (by omega) e)
      (fun e R' M' st' hb' fr' => by
        rw [e] at hb' fr'
        exact sub_fracB_exit hlive cx hk hy ha hs hf st' hb' fr')

/-- The second fraction phase's entry at `0x80004850` (`s1 = min s1 s2`):
none when `s1 = s2`, else the subtraction of `n2`'s extra digits. -/
theorem sub_fracB_entry {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {A B Y0 : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hs : x1.rep.scale ≤ x2.rep.scale) (hf : FracGeom x1.rep x2.rep y.rep.val A B Y0)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin 0) :: L))
    (h17 : R 17 = BitVec.ofNat 64 x2.rep.scale) (h8 : R 8 = BitVec.ofNat 64 x1.rep.scale)
    (h13 : R 13 = BitVec.ofNat 64 Y0) (h16 : R 16 = BitVec.ofNat 64 A)
    (h11 : R 11 = BitVec.ofNat 64 B) (h9 : R 9 = BitVec.ofNat 64 x1.rep.len) :
    DW live S Q 0x80004850#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have b1 := hs2.vLo; have b2 := hs2.ptrLe; have b3 := hs2.size; have b4 := hs2.vHi
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hNl := hy.N_lt
  simp only [addN, loopLen] at hNl
  simp only [heapStart, heapEnd] at b1 b4 v1
  have f1 := hf.eA; have f2 := hf.eB; have f3 := hf.eY
  have l1p := hs1.lenPos; have l2p := hs2.lenPos; have a3 := hs1.size
  have hb0 : subB x1.rep x2.rep 0 = 0 := borrowAt_zero _ _ _
  bc_run hlive hS [h17, h8, subw_ofNat, toInt_ofNat_small] at 0x80004858 0x800048b8
  · intro hc
    have e : x1.rep.scale = x2.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hc); omega
    have hg : SubMain x1.rep x2.rep y.rep.val 0 (x2.rep.len + x1.rep.scale) A B Y0 :=
      ⟨by omega, by omega, by omega, by omega, by omega⟩
    bc_run hlive hS [] at 0x8000472c
    exact sub_join hlive cx hk hy ha hg (st.keeps (by keeps_tac Keeps.refl _ _)) hb
      (by bsimp [h16]) (by bsimp [h13]) (by bsimp [h11]) (by bsimp [hb0])
      (by bsimp [h8]; congr 1; omega) (by bsimp [h9])
  · intro hc
    have e : x1.rep.scale < x2.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hc); omega
    bc_run hlive hS [h17, h8, h13, h11, se12_fff, word_pred, sxw_ofNat, subw_ofNat, shl_shr32,
      add_not_ofNat] at 0x80004878
    exact sub_fracB hlive cx hk hy ha e hf _ 0 _ _ rfl (by omega)
      (st.keeps (by keeps_tac Keeps.refl _ _)) hb
      ⟨by bsimp [h11], by bsimp [h13], by bsimp []; congr 1; omega, by bsimp [],
        by bsimp [hb0], by bsimp [h13], by bsimp [h16], by bsimp [h11], by bsimp [h8], by bsimp [h9]⟩

/-- The setup's arithmetic at `0x800046bc`: the operands' and the result's
last digit addresses, then the dispatch on `n1`'s scale against the
smaller scale `s0`. -/
theorem sub_setup_addr {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin 0) :: L))
    (h8 : R 8 = BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale))
    (h9 : R 9 = BitVec.ofNat 64 x1.rep.len)
    (h6 : R 6 = BitVec.ofNat 64 (max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale))
    (h15 : R 15 = BitVec.ofNat 64 x1.rep.scale) (h17 : R 17 = BitVec.ofNat 64 x2.rep.scale)
    (h12 : R 12 = BitVec.ofNat 64 x1.rep.len) (h14 : R 14 = BitVec.ofNat 64 x2.rep.len)
    (h13 : R 13 = BitVec.ofNat 64 y.rep.val) (h16 : R 16 = BitVec.ofNat 64 x1.rep.val)
    (h11 : R 11 = BitVec.ofNat 64 x2.rep.val) :
    DW live S Q 0x800046bc#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs1 := (hb.nums x1 (List.mem_cons_of_mem _ ha.m1)).shape
  have hs2 := (hb.nums x2 (List.mem_cons_of_mem _ ha.m2)).shape
  have := hs1.size; have := hs2.size; have := hs1.lenPos; have := hs2.lenPos
  have w1 := hs1.vHi; have w2 := hs2.vHi
  have hn0 := hb.nums _ List.mem_cons_self
  have w3 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have hls := hy.lenScale
  have hle := ha.le
  simp only [heapEnd] at w1 w2 w3
  bc_run hlive hS [h6, h15, h17, h12, h14, h13, h16, h11, h8, add2_pred, pred_add_ofNat, word_pred,
    toInt_ofNat_small] at 0x80004850 0x800046e0
  · intro he
    bv_nat at he
    exact sub_fracB_entry hlive cx hk hy ha (by omega)
      (A := x1.rep.val + (x1.rep.len + x1.rep.scale - 1))
      (B := x2.rep.val + (x2.rep.len + x2.rep.scale - 1))
      (Y0 := y.rep.val + (max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale - 1))
      ⟨rfl, rfl, rfl⟩ (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [h17])
      (by bsimp [h8]; try (congr 1; omega)) (by bsimp [h13, h6]; try (congr 1; omega))
      (by bsimp [h16, h12, h15]; try (congr 1; omega)) (by bsimp [h11, h14, h17]; try (congr 1; omega))
      (by bsimp [h9])
  · intro hne
    bv_nat at hne
    exact sub_fracA_entry hlive cx hk hy ha (by omega)
      (A := x1.rep.val + (x1.rep.len + x1.rep.scale - 1))
      (B := x2.rep.val + (x2.rep.len + x2.rep.scale - 1))
      (Y0 := y.rep.val + (max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale - 1))
      ⟨rfl, rfl, rfl⟩ (st.keeps (by keeps_tac Keeps.refl _ _)) hb (by bsimp [h15])
      (by bsimp [h8]; try (congr 1; omega)) (by bsimp [h13, h6]; try (congr 1; omega))
      (by bsimp [h16, h12, h15]; try (congr 1; omega)) (by bsimp [h11, h14, h17]; try (congr 1; omega))
      (by bsimp [h9])

/-- After `bc_new_num` and the zero fill, from `0x800046a0`: the operands'
scales, lengths and `n_value`s, the result's `n_value`. -/
theorem sub_setup {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin 0) :: L))
    (h8 : R 8 = BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale))
    (h9 : R 9 = BitVec.ofNat 64 x1.rep.len)
    (h6 : R 6 = BitVec.ofNat 64 (max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale)) :
    DW live S Q 0x800046a0#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ ha.m1)
  have hn2 := hb.nums x2 (List.mem_cons_of_mem _ ha.m2)
  have hn0 := hb.nums _ List.mem_cons_self
  num_facts hn1
  num_facts hn2
  have yp1 : heapStart ≤ y.rep.p := hn0.shape.pLo
  have yp2 : y.rep.p + 40 ≤ heapEnd := hn0.shape.pHi
  have yp3 : y.rep.p % 8 = 0 := hn0.shape.pAl
  simp only [heapStart, heapEnd] at yp1 yp2
  have hp := hy.p
  have hv0 : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by rw [← hp]; exact hn0.value
  have l1 := hn1.len; have l2 := hn2.len; have c1 := hn1.scale; have c2 := hn2.scale
  have u1 := hn1.value; have u2 := hn2.value
  have h22 := st.r22; have h23 := st.r23; have h10 := st.r10
  bc_run hlive hS [h22, h23, h10, l1, l2, c1, c2, u1, u2, hv0] at 0x800046bc
  exact sub_setup_addr hlive cx hk hy ha (st.keeps (by keeps_tac Keeps.refl _ _)) hb
    (by bsimp [h8]) (by bsimp [h9]) (by bsimp [h6]) (by bsimp [c1]) (by bsimp [c2]) (by bsimp [l1])
    (by bsimp [l2]) (by bsimp [hv0]) (by bsimp [u1]) (by bsimp [u2])

/-! ## The `scale_min` zero fill -/

/-- A zero written into the result before any position changes nothing. -/
theorem BcHeap.subZeroFill {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {y : NumObj} {a b : NumRep} {smin i : Nat}
    (hyl : y.rep.len + y.rep.scale = max a.len b.len + max smin (max a.scale b.scale))
    (hb : BcHeap S M H F (withDs y (subDs a b smin 0) :: L))
    (hi : i < max a.len b.len + max smin (max a.scale b.scale)) {v : BitVec 64}
    (hv : sbData v = BitVec.ofNat 8 0) :
    BcHeap S (writeLog M [(y.rep.val + i, 1, v)]) H F (withDs y (subDs a b smin 0) :: L) := by
  have hst := BcHeap.setDigit (L1 := []) hb (i := i) (d := 0) (by simp only [withDs]; omega)
    (by decide) hv
  simp only [withDs, List.nil_append] at hst ⊢
  rw [← subDs_zero, List.set_replicate_self] at hst
  rw [← subDs_zero]
  exact hst

/-- One zero of the `scale_min` tail at `0x80004694`: `a5` at the `i`-th
digit past `D + S`, `a4` past the last. -/
theorem sub_zfill_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {Z n i : Nat}
    (cx : SubCtx S R0 sp) (hy : SubSum y x1.rep x2.rep smin)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin 0) :: L))
    (hZ : Z = y.rep.val + (max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale))
    (hn : max x1.rep.scale x2.rep.scale + n = smin) (hi : i < n)
    (h15 : R 15 = BitVec.ofNat 64 (Z + i)) (h14 : R 14 = BitVec.ofNat 64 (Z + n))
    (hnext : i + 1 < n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin 0) :: L) →
      R' 15 = BitVec.ofNat 64 (Z + (i + 1)) → R' 14 = BitVec.ofNat 64 (Z + n) →
      R' 8 = R 8 → R' 9 = R 9 → R' 6 = R 6 → DW live S Q 0x80004694#64 R' M')
    (hexit : i + 1 = n → ∀ (R' : Nat → BitVec 64) (M' : Mem),
      SubAt S Mt0 M' R0 R' sp x1 x2 y.sb.pay →
      BcHeap S M' H F (withDs y (subDs x1.rep x2.rep smin 0) :: L) →
      R' 8 = R 8 → R' 9 = R 9 → R' 6 = R 6 → DW live S Q 0x800046a0#64 R' M') :
    DW live S Q 0x80004694#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have v1 : heapStart ≤ y.rep.ptr := hn0.shape.vLo
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have v3 : y.rep.ptr ≤ y.rep.val := hn0.shape.ptrLe
  have hls : y.rep.len + y.rep.scale =
      max x1.rep.len x2.rep.len + max smin (max x1.rep.scale x2.rep.scale) := by rw [hy.rep]; rfl
  simp only [heapStart, heapEnd] at v1 v2
  have hb' := BcHeap.subZeroFill (i := max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale + i)
    (v := 0#64) hls hb (by omega) (sbData_ofNat 0)
  rw [show y.rep.val + (max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale + i) = Z + i by
    omega] at hb'
  have st' := st.heap cx (M' := writeLog M [(Z + i, 1, 0#64)]) fun a ha =>
    imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  have ea : (upd R 15 (R 15 + 1#64) 15 + sign_extend (m := 64) (4095#12)).toNat = Z + i := by
    simp only [upd_apply, ite_true, h15, se12_fff, inc_dec, BitVec.toNat_ofNat]; omega
  dx_run hlive at 0x8000469c
  case hS => bsimp [ea]; exact acc_heap hS (by omega) (by omega)
  all_goals (try bsimp [ea, h15, h14, se12_fff, inc_dec])
  bc_run hlive hS [h15, h14] at 0x80004694 0x800046a0
  · intro hne
    bv_nat at hne
    exact hnext (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb'
      (by bsimp [Nat.add_assoc]) (by bsimp [h14]) (by bsimp []) (by bsimp []) (by bsimp [])
  · intro he
    bv_nat at he
    exact hexit (by omega) _ _ (st'.keeps (by keeps_tac Keeps.refl _ _)) hb' (by bsimp [])
      (by bsimp []) (by bsimp [])

/-- The `scale_min` zero fill at `0x80004694` (`S < scale_min`): `i` zeros
written, then the setup. -/
theorem sub_zfill {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk} {Z n : Nat}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (hZ : Z = y.rep.val + (max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale))
    (hn : max x1.rep.scale x2.rep.scale + n = smin) :
    ∀ m i (R : Nat → BitVec 64) (M : Mem), n - i = m → i < n →
      SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay →
      BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin 0) :: L) →
      R 15 = BitVec.ofNat 64 (Z + i) → R 14 = BitVec.ofNat 64 (Z + n) →
      R 8 = BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale) →
      R 9 = BitVec.ofNat 64 x1.rep.len →
      R 6 = BitVec.ofNat 64 (max x1.rep.len x2.rep.len + max x1.rep.scale x2.rep.scale) →
      DW live S Q 0x80004694#64 R M := by
  intro m
  induction m with
  | zero => intro i R M h1 h2; omega
  | succ m ih =>
    intro i R M hm hi st hb h15 h14 h8 h9 h6
    exact sub_zfill_body hlive cx hy st hb hZ hn hi h15 h14
      (fun hi' R' M' st' hb' e15 e14 e8 e9 e6 =>
        ih (i + 1) R' M' (by omega) hi' st' hb' e15 e14 (e8.trans h8) (e9.trans h9) (e6.trans h6))
      (fun _ R' M' st' hb' e8 e9 e6 =>
        sub_setup hlive cx hk hy ha st' hb' (e8.trans h8) (e9.trans h9) (e6.trans h6))

/-- After `bc_new_num` at `0x80004670`: `scale_min` back from the frame,
`t1 = D + S`; below `scale_min` the zero fill, otherwise the setup. -/
theorem sub_after_new {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 y : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (hy : SubSum y x1.rep x2.rep smin) (ha : SubArgs L x1 x2 smin)
    (st : SubAt S Mt0 M R0 R sp x1 x2 y.sb.pay)
    (hb : BcHeap S M H F (withDs y (subDs x1.rep x2.rep smin 0) :: L))
    (h8 : R 8 = BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale))
    (h9 : R 9 = BitVec.ofNat 64 x1.rep.len)
    (hsm : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 smin) :
    DW live S Q 0x80004670#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn0 := hb.nums _ List.mem_cons_self
  have yp1 : heapStart ≤ y.rep.p := hn0.shape.pLo
  have yp2 : y.rep.p + 40 ≤ heapEnd := hn0.shape.pHi
  have yp3 : y.rep.p % 8 = 0 := hn0.shape.pAl
  have v2 : y.rep.val + y.rep.len + y.rep.scale ≤ heapEnd := hn0.shape.vHi
  have hls := hy.lenScale
  have hsz := ha.size
  have hle := ha.le
  simp only [heapStart, heapEnd] at yp1 yp2 v2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hp := hy.p
  have hv0 : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by rw [← hp]; exact hn0.value
  have h2 := st.r2; have h10 := st.r10; have h21 := st.r21
  bc_run hlive hS [h2, h9, h21, hsm, toInt_ofNat_small] at 0x800046a0 0x8000467c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · intro _
    exact sub_setup hlive cx hk hy ha (st.keeps (by keeps_tac Keeps.refl _ _)) hb
      (by bsimp [h8]) (by bsimp [h9]) (by bsimp [h9, h21]; try (congr 1; omega))
  · intro hlt
    have hlt' : max x1.rep.scale x2.rep.scale < smin := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
    bc_run hlive hS [h2, h9, h21, hsm, h10, hv0, subw_ofNat, shl_shr32] at 0x80004694
    exact sub_zfill hlive cx hk hy ha (n := smin - max x1.rep.scale x2.rep.scale) rfl (by omega)
      _ 0 _ _ rfl (by omega) (st.keeps (by keeps_tac Keeps.refl _ _)) hb
      (by bsimp [hv0, h9, h21]; try (congr 1; omega))
      (by bsimp [hv0, h9, h21]; try (congr 1; omega)) (by bsimp [h8]) (by bsimp [h9])
      (by bsimp [h9, h21]; try (congr 1; omega))

/-! ## The call of `bc_new_num` and the prologue -/

/-- Inside `_bc_do_sub` before `bc_new_num`: `sp` lowered by 96, the saved
registers in the frame, `s6 = n1`, `s7 = n2`, `s3 = l1`, `s2 = l2`, and off
the heap only the stack window changed. -/
structure SubPre (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp : Nat) (x1 x2 : NumObj) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 96)
  saved : SavedWords M (sp - 96) subSlots R0
  r22 : R 22 = BitVec.ofNat 64 x1.rep.p
  r23 : R 23 = BitVec.ofNat 64 x2.rep.p
  r19 : R 19 = BitVec.ofNat 64 x1.rep.len
  r18 : R 18 = BitVec.ofNat 64 x2.rep.len
  regs : Keeps subAll R R0
  out : ∀ a, OutHeap a → ¬ frameIn sp 128 a → imgM M a = imgM Mt0 a

/-- The registers the prologue changes after its saves, besides `SubPre`'s. -/
abbrev subPreTmp : List Nat := [6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21, 28, 29]

/-- `SubPre` through changes of the scratch registers. -/
theorem SubPre.keeps {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp : Nat} {x1 x2 : NumObj}
    (pr : SubPre Mt0 M R0 R sp x1 x2) (hk : Keeps subPreTmp R' R) : SubPre Mt0 M R0 R' sp x1 x2 :=
  { pr with
    r2 := by rw [hk.get 2]; exact pr.r2
    r22 := by rw [hk.get 22]; exact pr.r22
    r23 := by rw [hk.get 23]; exact pr.r23
    r19 := by rw [hk.get 19]; exact pr.r19
    r18 := by rw [hk.get 18]; exact pr.r18
    regs := (hk.mono (by decide)).trans pr.regs }

/-- The new object is the difference before any position. -/
theorem SubSum.withDs_zero {y : NumObj} {a b : NumRep} {smin : Nat} (h : SubSum y a b smin) :
    withDs y (subDs a b smin 0) = y := by
  obtain ⟨p, rep, sb, db⟩ := y
  have hr := h.rep
  simp only at hr
  subst hr
  simp only [withDs, ← subDs_zero, zeroRep]

/-- The `bc_new_num(D, max S scale_min)` call from `0x80004664` (`scale_min`
saved at `sp + 8`); out of memory reaches `SubK.oom`. -/
theorem sub_call {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (ha : SubArgs L x1 x2 smin) (hb : BcHeap S M H F L) (pr : SubPre Mt0 M R0 R sp x1 x2)
    (h8 : R 8 = BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale))
    (h9 : R 9 = BitVec.ofNat 64 x1.rep.len) (h20 : R 20 = BitVec.ofNat 64 x2.rep.len)
    (h21 : R 21 = BitVec.ofNat 64 (max x1.rep.scale x2.rep.scale))
    (h11 : R 11 = BitVec.ofNat 64 (max (max x1.rep.scale x2.rep.scale) smin))
    (h12 : R 12 = BitVec.ofNat 64 smin) :
    DW live S Q 0x80004664#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := ha.size
  have hle := ha.le
  have h2 := pr.r2; have h22 := pr.r22; have h23 := pr.r23; have h19 := pr.r19
  have h18 := pr.r18; have sv := pr.saved
  have hout := pr.out; have hkp := pr.regs
  have hs1 := (hb.nums x1 ha.m1).shape
  have hs2 := (hb.nums x2 ha.m2).shape
  have := hs1.lenPos
  have hoff : ∀ a, sp - 96 + 8 ≤ a → a < sp - 96 + 16 → OutHeap a := fun a h1 h2 => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hb2 : BcHeap S (writeLog M [(sp - 96 + 8, 8, BitVec.ofNat 64 smin)]) H F L :=
    hb.out_frame (P := fun a => sp - 96 + 8 ≤ a ∧ a < sp - 96 + 16)
      (fun a ha => imgM_store_miss _ _ (by omega)) fun a ha => hoff a ha.1 ha.2
  bc_run hlive hS [h2, h9, h12] at 0x80004250
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hsf' : StackFrame S (sp - 96) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine bc_new_num_spec hlive hb2.newHeap hsf' (len := max x1.rep.len x2.rep.len)
    (scale := max (max x1.rep.scale x2.rep.scale) smin) (by simp only [heapEnd]; omega) (by omega)
    (by omega) _ (by bsimp [h9]; try (congr 1; omega)) (by bsimp [h11]) (by bsimp [h2]) (by bsimp [])
    ⟨fun R1 Mt1 H1 F1 y hk1 hp1 hr1 => ?_, fun R' Mt' hr2' hout' => ?_⟩
  · bsimp []
    have hy : SubSum y x1.rep x2.rep smin :=
      ⟨by rw [hp1.rep, Nat.max_comm (max x1.rep.scale x2.rep.scale)], subModel hs1 hs2, hsz,
        by omega⟩
    have hmem : ∀ a, OutHeap a → ¬ frameIn (sp - 96) 32 a →
        imgM Mt1 a = imgM (writeLog M [(sp - 96 + 8, 8, BitVec.ofNat 64 smin)]) a :=
      fun a ha hf => hp1.out a ha hf
    have st : SubAt S Mt0 Mt1 R0 R1 sp x1 x2 y.sb.pay :=
      { r2 := by rw [hk1.get 2]; bsimp [h2]
        saved := sv.transport (lo := 24) (top := 96) (hag := fun a h1 h2' => by
          rw [hmem a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
            (by simp only [frameIn]; omega), imgM_store_miss _ _ (by omega)])
        r22 := by rw [hk1.get 22]; bsimp [h22]
        r23 := by rw [hk1.get 23]; bsimp [h23]
        r19 := by rw [hk1.get 19]; bsimp [h19]
        r18 := by rw [hk1.get 18]; bsimp [h18]
        r20 := by rw [hk1.get 20]; bsimp [h20]
        r21 := by rw [hk1.get 21]; bsimp [h21]
        r10 := hr1
        regs := (hk1.mono (by decide)).trans ((by keeps_tac Keeps.refl _ _ : Keeps subAll _ R).trans hkp)
        out := fun a ha hf => by
          rw [hmem a ha (fun h => hf (by simp only [frameIn] at *; omega)),
            imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]
          exact hout a ha hf }
    have hb' := NewNumPost.insert hb2 hp1
    rw [← hy.withDs_zero] at hb'
    refine sub_after_new hlive cx hk hy ha st hb' (by rw [hk1.get 8]; bsimp [h8])
      (by rw [hk1.get 9]; bsimp [h9]) ?_
    rw [ldv_congr .ld fun j hj => hmem _ (hoff _ (by omega) (by simp only [widthOfM] at hj; omega))
      (by simp only [frameIn]; omega)]
    exact ldv_store_hit _ _ _
  · refine hk.oom R' Mt' (by rw [hr2']; congr 1; try omega) fun a ha hf => ?_
    rw [hout' a ha (fun h => hf (by simp only [frameIn] at *; omega)),
      imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]
    exact hout a ha hf

/-- `max S scale_min` into `a1`, from `0x80004658`. -/
theorem sub_pre4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (ha : SubArgs L x1 x2 smin) (hb : BcHeap S M H F L) (pr : SubPre Mt0 M R0 R sp x1 x2)
    (h8 : R 8 = BitVec.ofNat 64 (min x1.rep.scale x2.rep.scale))
    (h9 : R 9 = BitVec.ofNat 64 x1.rep.len) (h20 : R 20 = BitVec.ofNat 64 x2.rep.len)
    (h21 : R 21 = BitVec.ofNat 64 (max x1.rep.scale x2.rep.scale))
    (h12 : R 12 = BitVec.ofNat 64 smin) :
    DW live S Q 0x80004658#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := ha.size
  bc_run hlive hS [h21, h12, sxw_ofNat, toInt_ofNat_small] at 0x80004664
  · intro hge
    have hge' : smin ≤ max x1.rep.scale x2.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hge); omega
    exact sub_call hlive cx hk ha hb (pr.keeps (by keeps_tac Keeps.refl _ _)) (by bsimp [h8])
      (by bsimp [h9]) (by bsimp [h20]) (by bsimp [h21])
      (by bsimp [h21]; try (congr 1; omega)) (by bsimp [h12])
  · intro hlt
    have hlt' : max x1.rep.scale x2.rep.scale < smin := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
    bc_run hlive hS [h21, h12, sxw_ofNat] at 0x80004664
    exact sub_call hlive cx hk ha hb (pr.keeps (by keeps_tac Keeps.refl _ _)) (by bsimp [h8])
      (by bsimp [h9]) (by bsimp [h20]) (by bsimp [h21])
      (by bsimp [h12]; try (congr 1; omega)) (by bsimp [h12])

/-- The smaller scale into `s0`, from `0x8000464c`. -/
theorem sub_pre3b {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (ha : SubArgs L x1 x2 smin) (hb : BcHeap S M H F L) (pr : SubPre Mt0 M R0 R sp x1 x2)
    (h15 : R 15 = BitVec.ofNat 64 x2.rep.scale) (h14 : R 14 = BitVec.ofNat 64 x1.rep.scale)
    (h9 : R 9 = BitVec.ofNat 64 x1.rep.len) (h20 : R 20 = BitVec.ofNat 64 x2.rep.len)
    (h21 : R 21 = BitVec.ofNat 64 (max x1.rep.scale x2.rep.scale))
    (h12 : R 12 = BitVec.ofNat 64 smin) :
    DW live S Q 0x8000464c#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := ha.size
  bc_run hlive hS [h15, h14, sxw_ofNat, toInt_ofNat_small] at 0x80004658
  · intro hge
    have hge' : x2.rep.scale ≤ x1.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hge); omega
    exact sub_pre4 hlive cx hk ha hb (pr.keeps (by keeps_tac Keeps.refl _ _))
      (by bsimp [h15]; try (congr 1; omega)) (by bsimp [h9]) (by bsimp [h20]) (by bsimp [h21])
      (by bsimp [h12])
  · intro hlt
    have hlt' : x1.rep.scale < x2.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
    bc_run hlive hS [h15, h14, sxw_ofNat] at 0x80004658
    exact sub_pre4 hlive cx hk ha hb (pr.keeps (by keeps_tac Keeps.refl _ _))
      (by bsimp [h14]; try (congr 1; omega)) (by bsimp [h9]) (by bsimp [h20]) (by bsimp [h21])
      (by bsimp [h12])

/-- The smaller length into `s4` from `0x80004640`: `l2`, as `l2 ≤ l1`. -/
theorem sub_pre3a {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (ha : SubArgs L x1 x2 smin) (hb : BcHeap S M H F L) (pr : SubPre Mt0 M R0 R sp x1 x2)
    (h15 : R 15 = BitVec.ofNat 64 x2.rep.scale) (h14 : R 14 = BitVec.ofNat 64 x1.rep.scale)
    (h9 : R 9 = BitVec.ofNat 64 x1.rep.len)
    (h21 : R 21 = BitVec.ofNat 64 (max x1.rep.scale x2.rep.scale))
    (h12 : R 12 = BitVec.ofNat 64 smin) :
    DW live S Q 0x80004640#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := ha.size
  have hle := ha.le
  have h19 := pr.r19; have h18 := pr.r18
  bc_run hlive hS [h19, h18, toInt_ofNat_small] at 0x8000464c
  · intro _
    exact sub_pre3b hlive cx hk ha hb (pr.keeps (by keeps_tac Keeps.refl _ _)) (by bsimp [h15])
      (by bsimp [h14]) (by bsimp [h9]) (by bsimp [h18]) (by bsimp [h21]) (by bsimp [h12])
  · intro hlt
    exfalso
    (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega

/-- The operands' scales and the larger into `s5`, from `0x8000462c`. -/
theorem sub_pre3 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (ha : SubArgs L x1 x2 smin) (hb : BcHeap S M H F L) (pr : SubPre Mt0 M R0 R sp x1 x2)
    (h9 : R 9 = BitVec.ofNat 64 x1.rep.len) (h12 : R 12 = BitVec.ofNat 64 smin) :
    DW live S Q 0x8000462c#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 ha.m1
  have hn2 := hb.nums x2 ha.m2
  num_facts hn1
  num_facts hn2
  have c1 := hn1.scale; have c2 := hn2.scale
  have h22 := pr.r22; have h23 := pr.r23
  bc_run hlive hS [h22, h23, c1, c2, sxw_ofNat, toInt_ofNat_small] at 0x80004640
  · intro hge
    have hge' : x1.rep.scale ≤ x2.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hge); omega
    exact sub_pre3a hlive cx hk ha hb (pr.keeps (by keeps_tac Keeps.refl _ _))
      (by bsimp [c2, sxw_ofNat]) (by bsimp [c1, sxw_ofNat]) (by bsimp [h9])
      (by bsimp [c2, sxw_ofNat]; try (congr 1; omega)) (by bsimp [h12])
  · intro hlt
    have hlt' : x2.rep.scale < x1.rep.scale := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hlt); omega
    bc_run hlive hS [h22, h23, c1, c2, sxw_ofNat] at 0x80004640
    exact sub_pre3a hlive cx hk ha hb (pr.keeps (by keeps_tac Keeps.refl _ _))
      (by bsimp [c2, sxw_ofNat]) (by bsimp [c1, sxw_ofNat]) (by bsimp [h9])
      (by bsimp [c1, sxw_ofNat]; try (congr 1; omega)) (by bsimp [h12])

/-- After the saves, from `0x80004618`: `s6 = n1`, `s7 = n2`, and the
longer length (`l1`) into `s1`. -/
theorem sub_pre1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (ha : SubArgs L x1 x2 smin) (hb : BcHeap S M H F L) (sv : SavedWords M (sp - 96) subSlots R0)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp 128 a → imgM M a = imgM Mt0 a)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (h10 : R 10 = BitVec.ofNat 64 x1.rep.p)
    (h11 : R 11 = BitVec.ofNat 64 x2.rep.p) (h19 : R 19 = BitVec.ofNat 64 x1.rep.len)
    (h18 : R 18 = BitVec.ofNat 64 x2.rep.len) (h12 : R 12 = BitVec.ofNat 64 smin)
    (hkp : Keeps subAll R R0) :
    DW live S Q 0x80004618#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := ha.size
  have hle := ha.le
  have pr : ∀ R', R' 2 = BitVec.ofNat 64 (sp - 96) → R' 22 = BitVec.ofNat 64 x1.rep.p →
      R' 23 = BitVec.ofNat 64 x2.rep.p → R' 19 = BitVec.ofNat 64 x1.rep.len →
      R' 18 = BitVec.ofNat 64 x2.rep.len → Keeps subAll R' R → SubPre Mt0 M R0 R' sp x1 x2 :=
    fun R' r2 r22 r23 r19 r18 hk' =>
      { r2 := r2, saved := sv, r22 := r22, r23 := r23, r19 := r19, r18 := r18,
        regs := hk'.trans hkp, out := hout }
  bc_run hlive hS [h2, h10, h11, h19, h18, sxw_ofNat, toInt_ofNat_small] at 0x8000462c
  · intro _
    exact sub_pre3 hlive cx hk ha hb (pr _ (by bsimp [h2]) (by bsimp [h10]) (by bsimp [h11])
      (by bsimp [h19]) (by bsimp [h18]) (by keeps_tac Keeps.refl _ _)) (by bsimp [h19, sxw_ofNat])
      (by bsimp [h12])
  · intro hge
    have hge' : x1.rep.len ≤ x2.rep.len := by
      (try simp (disch := omega) only [toInt_ofNat_small] at hge); omega
    bc_run hlive hS [h2, h10, h11, h19, h18, sxw_ofNat] at 0x8000462c
    exact sub_pre3 hlive cx hk ha hb (pr _ (by bsimp [h2]) (by bsimp [h10]) (by bsimp [h11])
      (by bsimp [h19]) (by bsimp [h18]) (by keeps_tac Keeps.refl _ _))
      (by bsimp [h18, sxw_ofNat]; try (congr 1; omega)) (by bsimp [h12])

/-- A prologue store of a register still holding its entry value. -/
theorem SavedWords.storeV {M : Mem} {fr : Nat} {slots : List (Nat × Nat)} {R0 : Nat → BitVec 64}
    (h : SavedWords M fr slots R0) (r o : Nat) {v : BitVec 64} (hv : v = R0 r)
    (hd : ∀ p ∈ slots, p.2 + 8 ≤ o ∨ o + 8 ≤ p.2 := by decide) :
    SavedWords (writeLog M [(fr + o, 8, v)]) fr ((r, o) :: slots) R0 := by
  subst hv; exact h.store r o hd

/-- The remaining saves from `0x800045fc`, after `s2`, `s3` were saved and
loaded with `l2`, `l1`. -/
theorem sub_saves {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R0 sp) (hk : SubK live S Q R0 Mt0 L x1.rep x2.rep smin sp)
    (ha : SubArgs L x1 x2 smin) (hb : BcHeap S M H F L)
    (sv2 : SavedWords M (sp - 96) [(19, 56), (18, 64)] R0)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp 128 a → imgM M a = imgM Mt0 a)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (h10 : R 10 = BitVec.ofNat 64 x1.rep.p)
    (h11 : R 11 = BitVec.ofNat 64 x2.rep.p) (h19 : R 19 = BitVec.ofNat 64 x1.rep.len)
    (h18 : R 18 = BitVec.ofNat 64 x2.rep.len) (h12 : R 12 = BitVec.ofNat 64 smin)
    (hk3 : Keeps [2, 18, 19] R R0) :
    DW live S Q 0x800045fc#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have sv := (((((((sv2.storeV 9 72 (hk3.get 9)).storeV 22 32 (hk3.get 22)).storeV 23 24 (hk3.get 23)).storeV 1 88 (hk3.get 1)).storeV 8 80 (hk3.get 8)).storeV 20 48 (hk3.get 20)).storeV 21 40 (hk3.get 21))
  have hpro : MemOnly (frameIn sp 96) (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M [(sp - 96 + 72, 8, R 9)]) [(sp - 96 + 32, 8, R 22)]) [(sp - 96 + 24, 8, R 23)]) [(sp - 96 + 88, 8, R 1)]) [(sp - 96 + 80, 8, R 8)]) [(sp - 96 + 48, 8, R 20)]) [(sp - 96 + 40, 8, R 21)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hb' := hb.out_frame hpro fun a ha => by
    simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha ⊢; omega
  bc_run hlive hS [h2] at 0x80004618
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact sub_pre1 hlive cx hk ha hb' sv (fun a ha hf => by
      rw [hpro a fun h => hf (by simp only [frameIn] at *; omega)]; exact hout a ha hf)
    (by bsimp [h2]) (by bsimp [h10]) (by bsimp [h11]) (by bsimp [h19]) (by bsimp [h18])
    (by bsimp [h12])
    ((by keeps_tac Keeps.refl _ _ : Keeps subAll _ R).trans (hk3.mono (by decide)))

/-- `addi sp, sp, -96`. -/
theorem word_sub96 {x : Nat} (h : 96 ≤ x) :
    BitVec.ofNat 64 x + 18446744073709551520#64 = BitVec.ofNat 64 (x - 96) := by
  change BitVec.ofNat 64 x + -(96#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le x 96 (by decide) h

/-- **`_bc_do_sub(n1, n2, scale_min)`** at `0x800045e8`, for two numbers of
the heap with `n2` not longer than `n1`: a new number holding the
difference of the magnitudes heads the heap (`SubK.ret`), or
`out_of_memory` (`SubK.oom`). -/
theorem bc_do_sub_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {sp smin : Nat} {L : List NumObj} {x1 x2 : NumObj}
    {H : Heap} {F : List Blk}
    (cx : SubCtx S R sp) (ha : SubArgs L x1 x2 smin) (hb : BcHeap S M H F L)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 smin) (hk : SubK live S Q R M L x1.rep x2.rep smin sp) :
    DW live S Q 0x800045e8#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 ha.m1
  have hn2 := hb.nums x2 ha.m2
  num_facts hn1
  num_facts hn2
  have hle := ha.le
  have h2 := cx.sp0
  have sv := ((SavedWords.nil M (sp - 96) R).store 18 64).store 19 56
  have hpro : MemOnly (frameIn sp 96) (writeLog (writeLog M [(sp - 96 + 64, 8, R 18)])
      [(sp - 96 + 56, 8, R 19)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hb' := hb.out_frame hpro fun a ha => by
    simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha ⊢; omega
  have l1 : ldv .lw (writeLog (writeLog M [(sp - 96 + 64, 8, R 18)]) [(sp - 96 + 56, 8, R 19)])
      (x1.rep.p + 4) = BitVec.ofNat 64 x1.rep.len := by
    rw [ldv_congr .lw fun j hj => hpro _ (by simp only [frameIn, widthOfM] at *; omega)]
    exact hn1.len
  have l2 : ldv .lw (writeLog (writeLog M [(sp - 96 + 64, 8, R 18)]) [(sp - 96 + 56, 8, R 19)])
      (x2.rep.p + 4) = BitVec.ofNat 64 x2.rep.len := by
    rw [ldv_congr .lw fun j hj => hpro _ (by simp only [frameIn, widthOfM] at *; omega)]
    exact hn2.len
  bc_run hlive hS [h2, h10, h11, l1, l2, word_sub96] at 0x800045fc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact sub_saves hlive cx hk ha hb' sv (fun a _ hf => hpro a fun h => hf (by
      simp only [frameIn] at *; omega)) (by bsimp []) (by bsimp [h10]) (by bsimp [h11])
    (by bsimp []; (rw [ldv_congr .lw fun j hj => hpro _ (by
      simp only [frameIn, widthOfM] at *; omega)]; exact hn1.len))
    (by bsimp []; (rw [ldv_congr .lw fun j hj => hpro _ (by
      simp only [frameIn, widthOfM] at *; omega)]; exact hn2.len))
    (by bsimp [h12]) (by keeps_tac Keeps.refl _ _)

end Dc.Mach
