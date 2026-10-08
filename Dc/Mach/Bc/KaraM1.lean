import Dc.Mach.Bc.KaraM2
import Dc.Mach.Bc.BcSub

/-!
# `_bc_rec_mul`'s Karatsuba step: the differences and `m1 = u1 · v1`

From `0x80004f70`: `bc_is_zero (u1)`, `bc_is_zero (v1)`; then (both paths)
`_zero_` takes two more references for the slots of `d1` and `d2`,
`d1 = u1 - u0` and `d2 = v0 - v1` by `bc_sub`; then `m1` is a copy of
`_zero_` (`u1` or `v1` zero) or `_bc_rec_mul (u1, v1, &m1)`; then `m2`
(`kara_m2stage`).

- `kara_subCall`: a call of `bc_sub` from the step's frame into one of its
  slots, by `bc_sub_spec`.
- `BcHeap.kzero2`: one store giving `_zero_` two more references.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- **A call of `bc_sub`** from the step's frame (`sp - 192`) into the slot
`sp - 192 + o`: `bc_sub`'s 176 bytes are the top of the step's window. -/
theorem kara_subCall {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {u v : NumRep} {L1 L2 : List NumObj} {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L u v la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W) (o : Nat) (ho : o + 8 ≤ 88) (hoa : o % 8 = 0)
    (hW : 368 ≤ W)
    (ha : BinArgsM (L1 ++ xr :: L2) x1 x2 0)
    (hadd : x1.rep.neg ≠ x2.rep.neg → 1 ≤ x1.rep.len ∧ 1 ≤ x2.rep.len)
    (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr : ResSlot M L1 xr (sp - 192 + o)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 192 + o)) (h13 : R 13 = BitVec.ofNat 64 0)
    (hret : ∀ R' M' H' F' L' y, Keeps binClob R' R →
      BinPost S M M' H' F' L1 L2 xr (sp - 192 + o) (sp - 192) (x1.rep.subM x2.rep 0)
        L' y → DW live S Q (R 1) R' M') :
    DW live S Q 0x80004ac4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have ks := cx.kslot o (by omega) hoa
  exact bc_sub_specM hlive
    ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
      by simp only [heapEnd]; omega,
      ⟨fun i hi => ks.own _ (mem_accAddrs (by omega)), by omega, by omega, by omega⟩,
      fun a ha => ks.out a ha.1 ha.2, .inr (by omega), st.r2, hal⟩
    ha hadd hb hr h10 h11 h12 h13
    ⟨hret, fun R' M' sp' h1 h2 hr2 hout => hk.oom R' M' sp' (by omega) (by omega) hr2
      fun a ha hs hf => by
        rw [hout a ha (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
        exact st.out a ha hs hf⟩

/-- One store of `_zero_`'s reference count: two more `_zero_` handles. -/
theorem BcHeap.kzero2 {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {P A B : List NumObj}
    {z : NumObj} {hs : List Hd} (hb : BcHeap S M H F (KList P hs A B z)) {v : BitVec 64}
    (hv : v.toNat % 2 ^ 32 = z.rep.refs + zeroCount hs + 2)
    (hk : z.rep.refs + zeroCount hs + 2 < 2 ^ 31) :
    BcHeap S (writeLog M [(z.rep.p + 12, 4, v)]) H F (KList P (none :: none :: hs) A B z) := by
  have e : KList P (none :: none :: hs) A B z =
      (P ++ temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs + 2) :: B := by
    simp only [KList, temps, List.filterMap_cons, id, zeroCount_none, Nat.add_assoc]
  rw [e]
  have hb' : BcHeap S M H F ((P ++ temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B) := by
    simpa only [KList, List.append_assoc] using hb
  exact hb'.setRefs hv hk

/-- The step's registers before the differences: the four halves, `q`, `n`,
`la + lb` and `&_zero_`. -/
structure KM1 (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W n la lb : Nat)
    (z : NumObj) (hu1 hu0 hv1 hv0 : Hd) : Prop where
  st : KAt S M0 M R0 R sp q W
  u1 : R 24 = BitVec.ofNat 64 (Hd.p z hu1)
  u0 : R 19 = BitVec.ofNat 64 (Hd.p z hu0)
  v1 : R 27 = BitVec.ofNat 64 (Hd.p z hv1)
  v0 : R 20 = BitVec.ofNat 64 (Hd.p z hv0)
  fl : R 25 = BitVec.ofNat 64 bcFreeAddr
  q : R 9 = BitVec.ofNat 64 q
  n : R 8 = BitVec.ofNat 64 n
  s6 : R 22 = BitVec.ofNat 64 (la + lb)
  s2 : R 18 = BitVec.ofNat 64 zeroAddr

/-- `KM1` through register changes off the step's registers. -/
theorem KM1.keeps {S : Nat → Prop} {M0 M : Mem} {R0 R R' : Nat → BitVec 64}
    {sp q W n la lb : Nat} {z : NumObj} {hu1 hu0 hv1 hv0 : Hd}
    (pk : KM1 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0)
    {ks : List Nat} (kk : Keeps ks R' R)
    (hs : ∀ r ∈ [2, 8, 9, 18, 19, 20, 22, 24, 25, 27], r ∉ ks := by decide)
    (hsub : ∀ r ∈ ks, r ∈ rmAll := by decide) :
    KM1 S M0 M R0 R' sp q W n la lb z hu1 hu0 hv1 hv0 :=
  ⟨⟨pk.st.rm.keeps (kk.mono hsub) (kk _ (hs 2 (by simp))), pk.st.saved2⟩,
    (kk _ (hs 24 (by simp))).trans pk.u1, (kk _ (hs 19 (by simp))).trans pk.u0,
    (kk _ (hs 27 (by simp))).trans pk.v1, (kk _ (hs 20 (by simp))).trans pk.v0,
    (kk _ (hs 25 (by simp))).trans pk.fl, (kk _ (hs 9 (by simp))).trans pk.q,
    (kk _ (hs 8 (by simp))).trans pk.n, (kk _ (hs 22 (by simp))).trans pk.s6,
    (kk _ (hs 18 (by simp))).trans pk.s2⟩

/-- `KM1` with a memory: the frame kept. -/
theorem KM1.mem {S : Nat → Prop} {M0 M M' : Mem} {R0 R : Nat → BitVec 64}
    {sp q W n la lb : Nat} {z : NumObj} {hu1 hu0 hv1 hv0 : Hd}
    (pk : KM1 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0) (st : KAt S M0 M' R0 R sp q W) :
    KM1 S M0 M' R0 R sp q W n la lb z hu1 hu0 hv1 hv0 :=
  { pk with st := st }

/-- `KAt` through a call of `bc_sub` into the slot `sp - 192 + o`. -/
theorem KAt.subCall {S : Nat → Prop} {M0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    (cx : RmCtx S R0 sp q W) (st : KAt S M0 M R0 R sp q W) (o : Nat) (ho : o + 8 ≤ 88)
    (hW : 368 ≤ W)
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - 192 + o) a → ¬ frameIn (sp - 192) 176 a →
      imgM M' a = imgM M a) :
    KAt S M0 M' R0 R sp q W :=
  st.call cx o ho fun a h1 h2 h3 => hout a h1 h2 fun h => h3 (by
    simp only [frameIn] at h ⊢; omega)

/-- A handle's object in the heap and the handle's object agree on the value. -/
theorem Hd.objIn_num (hs : List Hd) (z : NumObj) (h : Hd) :
    (Hd.objIn hs z h).rep.num = (Hd.o z h).rep.num := by
  cases h <;> rfl

/-- ... and on `bc_sub`'s machine result. -/
theorem Hd.objIn_subM (hs : List Hd) (z : NumObj) (h1 h2 : Hd) (smin : Nat) :
    (Hd.objIn hs z h1).rep.subM (Hd.objIn hs z h2).rep smin = (Hd.o z h1).rep.subM (Hd.o z h2).rep smin := by
  cases h1 <;> cases h2 <;> rfl

theorem Hd.objIn_norm (hs : List Hd) (z : NumObj) (h : Hd) :
    (Hd.objIn hs z h).rep.Norm ↔ (Hd.o z h).rep.Norm := by
  cases h <;> rfl

theorem Hd.objIn_len' (hs : List Hd) (z : NumObj) (h : Hd) :
    (Hd.objIn hs z h).rep.len = (Hd.o z h).rep.len := by
  cases h <;> rfl

theorem Hd.objIn_scale (hs : List Hd) (z : NumObj) (h : Hd) :
    (Hd.objIn hs z h).rep.scale = (Hd.o z h).rep.scale := by
  cases h <;> rfl

/-- `bc_sub`'s operands among the handles: normalized, in range. -/
structure KSubArgs (z : NumObj) (x1 x2 : Hd) : Prop where
  n1 : (Hd.o z x1).rep.Norm
  n2 : (Hd.o z x2).rep.Norm
  size : max (Hd.o z x1).rep.len (Hd.o z x2).rep.len + 1 +
    max 0 (max (Hd.o z x1).rep.scale (Hd.o z x2).rep.scale) < 2 ^ 31
  /-- both are halves or differences of magnitudes: non-negative -/
  neg1 : (Hd.o z x1).rep.neg = false
  neg2 : (Hd.o z x2).rep.neg = false
  /-- not both empty: a zero-length high half meets a low half of `n ≥ 1` digits -/
  ne : 1 ≤ (Hd.o z x1).rep.len ∨ 1 ≤ (Hd.o z x2).rep.len

theorem KSubArgs.binArgs {z : NumObj} {x1 x2 : Hd} (h : KSubArgs z x1 x2) {P A B : List NumObj}
    {hs : List Hd} (h1 : x1 ∈ hs) (h2 : x2 ∈ hs) :
    BinArgsM (KList P hs A B z) (Hd.objIn hs z x1) (Hd.objIn hs z x2) 0 :=
  ⟨Hd.objIn_mem h1 P A B z, Hd.objIn_mem h2 P A B z, (Hd.objIn_norm hs z x1).mpr h.n1,
    (Hd.objIn_norm hs z x2).mpr h.n2, by
      simp only [Hd.objIn_len', Hd.objIn_scale]; exact h.size,
    by rw [Hd.objIn_len', Hd.objIn_len']; exact h.ne⟩

/-- Two non-negative operands: `bc_sub` never adds magnitudes. -/
theorem KSubArgs.noAdd {z : NumObj} {x1 x2 : Hd} (h : KSubArgs z x1 x2) (hs : List Hd) :
    (Hd.objIn hs z x1).rep.neg ≠ (Hd.objIn hs z x2).rep.neg →
      1 ≤ (Hd.objIn hs z x1).rep.len ∧ 1 ≤ (Hd.objIn hs z x2).rep.len := by
  rw [Hd.objIn_neg, Hd.objIn_neg, h.neg1, h.neg2]; exact fun e => absurd rfl e

/-- A difference `bc_sub` left: the new number heading the handles. -/
structure KDiff (y : NumObj) (n : Num) : Prop where
  num : y.rep.num = n
  norm : y.rep.Norm
  refs : y.rep.refs = 1
  owns : y.Owns
  /-- `bc_sub`'s result has a digit (`BinPost.pos`) -/
  pos : 1 ≤ y.rep.len

/-- The step after the differences `d1 = u1 - u0` and `d2 = v0 - v1`. -/
structure KSubs (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W n la lb : Nat)
    (z : NumObj) (hu1 hu0 hv1 hv0 : Hd) (y1 y2 : NumObj) : Prop where
  st : KAt S M0 M R0 R sp q W
  tr : KTailRegs z hu1 hu0 hv1 hv0 (some y1) (some y2) q n R
  s6 : R 22 = BitVec.ofNat 64 (la + lb)
  s2 : R 18 = BitVec.ofNat 64 zeroAddr
  l1 : ldv .ld M (sp - 192) = BitVec.ofNat 64 y1.rep.len
  l2 : R 17 = BitVec.ofNat 64 y2.rep.len
  d1 : KDiff y1 ((Hd.o z hu1).rep.subM (Hd.o z hu0).rep 0)
  d2 : KDiff y2 ((Hd.o z hv0).rep.subM (Hd.o z hv1).rep 0)

/-- What the differences hand on (at `pc`): the step, the heap with `d2`, `d1`
heading the handles, the globals kept. -/
def KSubsK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (M0 Ms : Mem) (R0 : Nat → BitVec 64) (sp q W n la lb : Nat) (z : NumObj)
    (hu1 hu0 hv1 hv0 : Hd) (hs : List Hd) (A B : List NumObj) (pc : BitVec 64) : Prop :=
  ∀ R' M' H' F' y1 y2, KSubs S M0 M' R0 R' sp q W n la lb z hu1 hu0 hv1 hv0 y1 y2 →
    BcHeap S M' H' F' (KList [] (some y2 :: some y1 :: hs) A B z) → GlobAgree M' Ms →
    DW live S Q pc R' M'

/-- The heap's first object is a number of the heap. -/
theorem BcHeap.khead {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {A B : List NumObj}
    {z y : NumObj} {hs : List Hd} (hb : BcHeap S M H F (KList [] (some y :: hs) A B z)) :
    NumAt M y.rep ∧ y.rep.p = y.sb.pay := by
  have hm : y ∈ KList [] (some y :: hs) A B z := by
    rw [KList_some]; exact List.mem_cons_self
  exact ⟨hb.nums y hm, (hb.blocks y hm).sPay⟩

/-- `bc_sub`'s freed `_zero_` handle: the new number heads the handles. -/
theorem KList_subDec (y : NumObj) (hs : List Hd) (A B : List NumObj) (z : NumObj) :
    y :: (([] ++ temps (none :: hs) ++ A) ++
      (z.withRefs (z.rep.refs + zeroCount (none :: hs))).decRef :: B) =
      KList [] (some y :: hs) A B z := by
  simp only [KList, temps, List.filterMap_cons, id, zeroCount_none, zeroCount_some, NumObj.decRef,
    NumObj.withRefs, ← Nat.add_assoc, Nat.add_sub_cancel, List.nil_append, List.cons_append]

theorem KList_swapNone (P : List NumObj) (x : NumObj) (hs : List Hd) (A B : List NumObj)
    (z : NumObj) : KList P (some x :: none :: hs) A B z = KList P (none :: some x :: hs) A B z := by
  simp only [KList, temps, List.filterMap_cons, id, zeroCount_none, zeroCount_some]

/-- The `_zero_` handle in a `bc_sub` slot: a `ResSlot` (more than one
reference, so no view matters). -/
theorem KList.resSlot {M : Mem} {z : NumObj} {hs : List Hd} {A : List NumObj} {qs : Nat}
    (hz : 1 ≤ z.rep.refs) (hw : ldv .ld M qs = BitVec.ofNat 64 z.rep.p) :
    ResSlot M ([] ++ temps (none :: hs) ++ A) (z.withRefs (z.rep.refs + zeroCount (none :: hs))) qs :=
  ⟨by simp only [NumObj.withRefs, zeroCount_none]; omega, hw, fun h => absurd h (by
    simp only [NumObj.withRefs, zeroCount_none]; omega)⟩

/-- The nine handles after the differences and `m1`, in the frees' order. -/
theorem kperm9 (a b c d e f g h i : Hd) :
    (g :: f :: e :: i :: h :: [a, b, c, d]).Perm (kHs a b c e d f g h i) := by
  refine (List.perm_middle (l₁ := [g, f, e, i, h]) (l₂ := [b, c, d])).trans (.cons a ?_)
  refine (List.perm_middle (l₁ := [g, f, e, i, h]) (l₂ := [c, d])).trans (.cons b ?_)
  refine (List.perm_middle (l₁ := [g, f, e, i, h]) (l₂ := [d])).trans (.cons c ?_)
  refine (List.perm_middle (l₁ := [g, f]) (l₂ := [i, h, d])).trans (.cons e ?_)
  refine (List.perm_middle (l₁ := [g, f, i, h]) (l₂ := [])).trans (.cons d ?_)
  refine (List.perm_middle (l₁ := [g]) (l₂ := [i, h])).trans (.cons f ?_)
  exact .cons g (List.perm_middle (l₁ := [i]) (l₂ := []))

/-- The four halves' handles, in any order. -/
theorem kperm9_of {hu1 hu0 hv1 hv0 : Hd} {hs0 : List Hd} (hp : hs0.Perm [hu1, hu0, hv1, hv0])
    (hm1 h2 h3 y1 y2 : Hd) :
    (h3 :: h2 :: hm1 :: y2 :: y1 :: hs0).Perm (kHs hu1 hu0 hv1 hm1 hv0 h2 h3 y1 y2) :=
  ((((hp.cons y1).cons y2).cons hm1).cons h2).cons h3 |>.trans
    (kperm9 hu1 hu0 hv1 hv0 hm1 h2 h3 y1 y2)

/-- A number with scale `0`: its value is the digits' value. -/
theorem hdVal_of_num {y : NumObj} {M : Mem} (hy : NumAt M y.rep) {b : Bool} {w : Nat}
    (h : y.rep.num = ⟨b, w, 0⟩) : hdVal y = w := by
  have hl := hy.shape.dsLen
  have hs : y.rep.scale = 0 := by
    have := congrArg Num.scale h; simpa [NumRep.num] using this
  have hv := congrArg Num.mag h
  show dvalBE (y.rep.ds.take y.rep.len) = w
  rw [List.take_of_length_le (by omega)]
  simpa [NumRep.num, dval_eq_dvalBE] using hv

/-- `KSubs` through register changes off the step's registers. -/
theorem KSubs.keeps {S : Nat → Prop} {M0 M : Mem} {R0 R R' : Nat → BitVec 64}
    {sp q W n la lb : Nat} {z : NumObj} {hu1 hu0 hv1 hv0 : Hd} {y1 y2 : NumObj}
    (ps : KSubs S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 y1 y2)
    {ks : List Nat} (kk : Keeps ks R' R)
    (hs : ∀ r ∈ [2, 8, 9, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27], r ∉ ks := by decide)
    (hsub : ∀ r ∈ ks, r ∈ rmAll := by decide) :
    KSubs S M0 M R0 R' sp q W n la lb z hu1 hu0 hv1 hv0 y1 y2 :=
  ⟨⟨ps.st.rm.keeps (kk.mono hsub) (kk _ (hs 2 (by simp))), ps.st.saved2⟩,
    ps.tr.keeps kk fun r hr => hs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega),
    (kk _ (hs 22 (by simp))).trans ps.s6, (kk _ (hs 18 (by simp))).trans ps.s2, ps.l1,
    (kk _ (hs 17 (by simp))).trans ps.l2, ps.d1, ps.d2⟩

/-- The obligations the differences carry into the `m2` stage: their sizes
and the Karatsuba identity (the step's entry supplies them). -/
structure KDiffSpec (z : NumObj) (hu1 hu0 hv1 hv0 : Hd) (u v : NumRep) (n la lb N W : Nat) :
    Prop where
  fit : ∀ y1 y2 : NumObj,
    y1.rep.num = (Hd.o z hu1).rep.subM (Hd.o z hu0).rep 0 →
    y2.rep.num = (Hd.o z hv0).rep.subM (Hd.o z hv1).rep 0 →
    n + y1.rep.len + y2.rep.len ≤ la + lb + 1 ∧ y1.rep.len + y2.rep.len ≤ N ∧
      rmStack (y1.rep.len + y2.rep.len) + 192 ≤ W
  fill : ∀ y1 y2 : NumObj,
    y1.rep.num = (Hd.o z hu1).rep.subM (Hd.o z hu0).rep 0 →
    y2.rep.num = (Hd.o z hv0).rep.subM (Hd.o z hv1).rep 0 →
    KFillVal (hdVal (Hd.o z hu1) * hdVal (Hd.o z hv1)) (hdVal y1 * hdVal y2)
      (hdVal (Hd.o z hu0) * hdVal (Hd.o z hv0)) (10 ^ n) (kUV u v la lb) (la + lb + 1)
      (y1.rep.neg != y2.rep.neg)

/-- The `u0 · v0` obligations of the `m3` stage. -/
structure KM3Spec (z : NumObj) (hu0 hv0 : Hd) (n la lb N W : Nat) : Prop where
  fit : n + (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ la + lb + 1
  size : (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ N
  stack : rmStack ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len) + 192 ≤ W
  /-- the low halves have digits: `new_sub_num (n, 0, …)` with `1 ≤ n` -/
  pu0 : 1 ≤ (Hd.o z hu0).rep.len
  pv0 : 1 ≤ (Hd.o z hv0).rep.len

/-- The `m1` obligations: `2 n` digits for `u1 · v1`, and its size. -/
structure KM1Spec (z : NumObj) (hu1 hv1 : Hd) (n la lb N W : Nat) : Prop where
  fit : 2 * n + (Hd.o z hu1).rep.len + (Hd.o z hv1).rep.len ≤ la + lb + 1
  size : (Hd.o z hu1).rep.len + (Hd.o z hv1).rep.len ≤ N
  stack : rmStack ((Hd.o z hu1).rep.len + (Hd.o z hv1).rep.len) + 192 ≤ W

/-- The handles the `m2` stage sees: `m1`, `d2`, `d1`, then the four halves. -/
abbrev kHs1 (hm1 : Hd) (y1 y2 : NumObj) (hs0 : List Hd) : List Hd :=
  hm1 :: some y2 :: some y1 :: hs0

/-- The step's state entering the `m2` stage from the `m1` stage. -/
theorem km2_of_subs {S : Nat → Prop} {M0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp q W n la lb : Nat} {z : NumObj} {hu1 hu0 hv1 hv0 hm1 : Hd} {y1 y2 : NumObj} {fl : Bool}
    (ps : KSubs S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 y1 y2)
    (hm : ldv .ld M (sp - 192 + 40) = BitVec.ofNat 64 (Hd.p z hm1))
    (h26 : R 26 = BitVec.ofNat 64 (if fl then 1 else 0)) :
    KM2 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 (some y1) (some y2) hm1 fl :=
  ⟨ps.st, ps.tr, hm, ps.s6, h26, ps.s2, ps.l1, ps.l2⟩

/-- **Entering the `m2` stage** with `m1` in its slot: the handles reordered
and the obligations of the three products projected. -/
theorem kara_m2enter {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H : Heap} {F : List Blk} {fl : Bool}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hv0 hm1 : Hd} {hs0 : List Hd} {y1 y2 : NumObj}
    (pk : KM2 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 (some y1) (some y2) hm1 fl)
    (hb : BcHeap S M H F (KList [] (kHs1 hm1 y1 y2 hs0) A B z))
    (hp0 : hs0.Perm [hu1, hu0, hv1, hv0])
    (hown : HdOwned A B z (kHs1 hm1 y1 y2 hs0)) (hok : HdOK (kHs1 hm1 y1 y2 hs0))
    (kz : KZero M z (zeroCount (kHs1 hm1 y1 y2 hs0) + 1 + (4 * (la + lb + 2 - n) + 8)))
    (h12 : R 12 = BitVec.ofNat 64 z.rep.p) (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (hm1z : fl = true → hdVal (Hd.o z hm1) = 0)
    (hfit1 : fl = false → 2 * n + valCount (Hd.o z hm1).rep ≤ la + lb + 1)
    (ds : KDiffSpec z hu1 hu0 hv1 hv0 u v n la lb N W)
    (m3s : KM3Spec z hu0 hv0 n la lb N W)
    (hd1 : y1.rep.num = (Hd.o z hu1).rep.subM (Hd.o z hu0).rep 0)
    (hd2 : y2.rep.num = (Hd.o z hv0).rep.subM (Hd.o z hv1).rep 0)
    (hm1v : hdVal (Hd.o z hm1) = hdVal (Hd.o z hu1) * hdVal (Hd.o z hv1))
    (hd1p : 1 ≤ y1.rep.len) (hd2p : 1 ≤ y2.rep.len)
    (hw1 : fl = false → 1 ≤ (Hd.o z hm1).rep.len) :
    DW live S Q 0x80005050#64 R M := by
  obtain ⟨hf1, hN1, hW1⟩ := ds.fit y1 y2 hd1 hd2
  have hu1m : hu1 ∈ kHs1 hm1 y1 y2 hs0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (hp0.mem_iff.mpr (by simp))))
  have hu0m : hu0 ∈ kHs1 hm1 y1 y2 hs0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (hp0.mem_iff.mpr (by simp))))
  have hv1m : hv1 ∈ kHs1 hm1 y1 y2 hs0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (hp0.mem_iff.mpr (by simp))))
  have hv0m : hv0 ∈ kHs1 hm1 y1 y2 hs0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (hp0.mem_iff.mpr (by simp))))
  refine kara_m2stage hlive ih cx hk pk hb (fun h2 h3 => kperm9_of hp0 hm1 h2 h3 _ _) hown hok
    hu0m hv0m (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_of_mem _ List.mem_cons_self) (kz.mono (by have h3 := m3s.fit; simp only [Hd.o] at h3 ⊢; omega)) h12 hmb hN1 hW1 m3s.size m3s.stack hNla hn1
    hd1p hd2p hm1z hfit1 (by show n + y1.rep.len + y2.rep.len ≤ _; omega) m3s.fit hw1 m3s.pu0 m3s.pv0 ?_
  · show KFillVal _ (hdVal y1 * hdVal y2) _ _ _ _ _
    rw [hm1v]
    exact ds.fill y1 y2 hd1 hd2

/-- **`m1` is a copy of `_zero_`** (`0x8000550c`, `u1` or `v1` zero): its
pointer in `m1`'s slot, one more reference, the flag `s10`; then `m2`. -/
theorem kara_m1zero {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hv0 : Hd} {hs0 : List Hd} {y1 y2 : NumObj}
    (ps : KSubs S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 y1 y2)
    (hb : BcHeap S M H F (KList [] (some y2 :: some y1 :: hs0) A B z))
    (hp0 : hs0.Perm [hu1, hu0, hv1, hv0])
    (hown : HdOwned A B z (some y2 :: some y1 :: hs0))
    (hok : HdOK (some y2 :: some y1 :: hs0))
    (kz : KZero M z (zeroCount (some y2 :: some y1 :: hs0) + 2 + (4 * (la + lb + 2 - n) + 8)))
    (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (ds : KDiffSpec z hu1 hu0 hv1 hv0 u v n la lb N W)
    (m3s : KM3Spec z hu0 hv0 n la lb N W)
    (hz0 : hdVal (Hd.o z hu1) * hdVal (Hd.o z hv1) = 0) :
    DW live S Q 0x8000550c#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hzm : z.withRefs (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0)) ∈
      KList [] (some y2 :: some y1 :: hs0) A B z := List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums _ hzm
  have hrf : ldv .lw M (z.rep.p + 12) =
      BitVec.ofNat 64 (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0)) := hn.refs
  have e1 : 2147603920 ≤ z.rep.p := hn.shape.pLo
  have e2 : z.rep.p + 40 ≤ heapEnd := hn.shape.pHi
  have e3 : z.rep.p % 8 = 0 := hn.shape.pAl
  simp only [heapEnd] at e2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h2 := ps.st.rm.r2
  have h18 := ps.s2
  have hgl := kz.glob
  simp only [zeroAddr] at h18 hgl
  have hab := cx.above; have hW' := cx.big
  simp only [heapEnd] at hab
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hzk := kz.room
  have hrf' : ldv .lw (writeLog M [(sp - 192 + 40, 8, BitVec.ofNat 64 z.rep.p)]) (z.rep.p + 12) =
      BitVec.ofNat 64 (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0)) := by
    rw [ldv_store_miss .lw M _ (by simp only [widthOfM]; omega)]; exact hrf
  have hcst : ∀ b ∈ accAddrs 0x8001cdc8 8, S b := fun b hb' => cx.consts b (by
    have := of_mem_accAddrs hb'; simp only [constBytes, twoAddr, zeroAddr] at this ⊢; omega)
  bc_run hlive hS [h18, hgl, hrf, hrf', h2, sxw_ofNat] at 0x80005050
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hcst | exact acc_heap hS (by omega) (by omega) | (simp only [LdOK, StOK, tohostAddr] at *; omega) | skip
  have hmo : MemOnly (fun a => z.rep.p + 12 ≤ a ∧ a < z.rep.p + 12 + 4)
      (writeLog (writeLog M [(sp - 192 + 40, 8, BitVec.ofNat 64 z.rep.p)])
        [(z.rep.p + 12, 4,
          BitVec.ofNat 64 (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0) + 1))])
      (writeLog M [(sp - 192 + 40, 8, BitVec.ofNat 64 z.rep.p)]) :=
    MemOnly.store _ _ _ _
  have hP1 : ∀ a, (z.rep.p + 12 ≤ a ∧ a < z.rep.p + 12 + 4) → heapStart ≤ a ∧ a < heapEnd :=
    fun a h => by simp only [heapStart, heapEnd]; omega
  have st1 := (ps.st.storeSlot cx 40 (BitVec.ofNat 64 z.rep.p) (by omega)).heapOnly cx hmo hP1
  have hga : GlobAgree (writeLog (writeLog M [(sp - 192 + 40, 8, BitVec.ofNat 64 z.rep.p)])
      [(z.rep.p + 12, 4,
        BitVec.ofNat 64 (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0) + 1))]) M :=
    (GlobAgree.store _ (by omega)).trans (GlobAgree.store _ (by omega))
  have hb2 := (hb.out_frame (MemOnly.store _ (sp - 192 + 40) 8 (BitVec.ofNat 64 z.rep.p))
    fun a ha => by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega).kzero
    (toNat_ofNat_mod32 (by omega)) (by omega)
  have hl1 : ldv .ld (writeLog (writeLog M [(sp - 192 + 40, 8, BitVec.ofNat 64 z.rep.p)])
      [(z.rep.p + 12, 4,
        BitVec.ofNat 64 (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0) + 1))])
      (sp - 192) = BitVec.ofNat 64 y1.rep.len := by
    rw [hmo.ldv_off hP1 (by simp only [heapStart, heapEnd]; omega), ldv_ld_miss _ _ (by omega)]
    exact ps.l1
  have hm1 : ldv .ld (writeLog (writeLog M [(sp - 192 + 40, 8, BitVec.ofNat 64 z.rep.p)])
      [(z.rep.p + 12, 4,
        BitVec.ofNat 64 (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0) + 1))])
      (sp - 192 + 40) = BitVec.ofNat 64 (Hd.p z (none : Hd)) := by
    rw [hmo.ldv_off hP1 (by simp only [heapStart, heapEnd]; omega)]
    exact ldv_store_hit _ _ _
  have ps2 : KSubs S M0 _ R0 R sp q W n la lb z hu1 hu0 hv1 hv0 y1 y2 :=
    ⟨st1, ps.tr, ps.s6, ps.s2, hl1, ps.l2, ps.d1, ps.d2⟩
  have hzv : hdVal z = 0 := by show dvalBE (z.rep.ds.take z.rep.len) = 0; rw [kz.ds, kz.len]; rfl
  refine kara_m2enter hlive ih cx hk
    (km2_of_subs (fl := true) (ps2.keeps (ks := [12, 15, 26]) (by keeps_tac Keeps.refl _ _)) ?_ (by bsimp []))
    hb2 hp0 (hown.cons fun x e => nomatch e) (hok.cons fun x e => nomatch e)
    (hga.zero (kz.mono (by simp only [zeroCount_none]; omega))) (by bsimp [])
    (hga.mulBase hmb) hNla hn1 (fun _ => by rw [Hd.o, hzv])
    (by simp)
    ds m3s ps2.d1.num ps2.d2.num
    (by rw [Hd.o, hzv, hz0]) ps2.d1.pos ps2.d2.pos (by simp)
  exact hm1

/-- **`m1` returned** (`0x80005044`): the product in `m1`'s slot, `d2`'s digit
count reloaded, the flag `s10 = 0`; then `m2`. -/
theorem kara_m1ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H' : Heap} {F' : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu0 hv0 : Hd} {hs0 : List Hd} {x1 x2 y1 y2 ym : NumObj}
    (ps : KSubs S M0 M R0 R sp q W n la lb z (some x1) hu0 (some x2) hv0 y1 y2)
    (hp0 : hs0.Perm [some x1, hu0, some x2, hv0])
    (hown : HdOwned A B z (some y2 :: some y1 :: hs0))
    (hok : HdOK (some y2 :: some y1 :: hs0))
    (hx1 : NumAt M x1.rep) (hx2 : NumAt M x2.rep)
    (kk : Keeps (1 :: binClob) R' R)
    (hsv : ldv .ld M (sp - 192 + 8) = BitVec.ofNat 64 y2.rep.len)
    (post : RmPost S M M' H' F' ((temps (some y2 :: some y1 :: hs0) ++ A) ++
      z.withRefs (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0)) :: B)
      x1.rep x2.rep x1.rep.len x2.rep.len (sp - 192 + 40) (sp - 192) (W - 192) ym)
    (kz : KZero M z (zeroCount (some y2 :: some y1 :: hs0) + 2 + (4 * (la + lb + 2 - n) + 8)))
    (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (ds : KDiffSpec z (some x1) hu0 (some x2) hv0 u v n la lb N W)
    (m3s : KM3Spec z hu0 hv0 n la lb N W)
    (m1s : KM1Spec z (some x1) (some x2) n la lb N W) :
    DW live S Q 0x80005044#64 R' M' := by
  have hab := cx.above; have hW' := cx.big
  simp only [heapEnd] at hab
  have kr := post.kret hx1 hx2
  have hS : HeapOwn S := fun a h1 h2 => kr.heap.heap.own a h1 h2
  have st := ps.st.call cx 40 (by omega) post.out
  have hga : GlobAgree M' M := GlobAgree.call (by omega) (by omega) post.out
  have hfr : ∀ a, sp - 192 ≤ a → a < sp - 192 + 40 → imgM M' a = imgM M a := fun a h1 h2 =>
    post.out a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)
  have hl1 : ldv .ld M' (sp - 192) = BitVec.ofNat 64 y1.rep.len :=
    (ldv_congr .ld fun j hj => hfr _ (by omega) (by simp only [widthOfM] at hj; omega)).trans ps.l1
  have hsv' : ldv .ld M' (sp - 192 + 8) = BitVec.ofNat 64 y2.rep.len :=
    (ldv_congr .ld fun j hj => hfr _ (by omega) (by simp only [widthOfM] at hj; omega)).trans hsv
  have kz' := hga.zero kz
  have h18 := (kk.get 18 (by decide)).trans ps.s2
  have h2 := (kk.get 2 (by decide)).trans ps.st.rm.r2
  have hgl := kz'.glob
  simp only [zeroAddr] at h18 hgl
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hcst : ∀ b ∈ accAddrs 0x8001cdc8 8, S b := fun b hb' => cx.consts b (by
    have := of_mem_accAddrs hb'; simp only [constBytes, twoAddr, zeroAddr] at this ⊢; omega)
  bc_run hlive hS [h18, hgl, h2, hsv'] at 0x80005050
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hcst | skip
  have hvc := kr.vc
  have hm1f := m1s.fit
  simp only [Hd.o] at hm1f
  have mk : ∀ R'', Keeps [12, 17, 26] R'' R' → R'' 26 = BitVec.ofNat 64 0 →
      R'' 17 = BitVec.ofNat 64 y2.rep.len →
      KM2 S M0 M' R0 R'' sp q W n la lb z (some x1) hu0 (some x2) hv0 (some y1) (some y2)
        (some ym) false := by
    intro R'' k h26 h17
    have kkT : Keeps (26 :: 1 :: binClob) R'' R := (k.mono (by decide)).trans (kk.mono (by decide))
    exact ⟨⟨st.rm.keeps (kkT.mono (by decide)) (kkT 2 (by decide)), st.saved2⟩,
      ps.tr.keeps kkT, kr.slot, (kkT 22 (by decide)).trans ps.s6, by rw [h26]; rfl,
      (kkT 18 (by decide)).trans ps.s2, hl1, h17⟩
  refine kara_m2enter hlive ih cx hk
    (mk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp [hsv']))
    kr.heap hp0 (hown.cons fun x e => by cases e; exact kr.owns)
    (hok.cons fun x e => by cases e; exact kr.refs)
    (kz'.mono (by simp only [zeroCount_some]; omega)) (by bsimp []) (hga.mulBase hmb) hNla hn1
    (by simp) (fun _ => by show 2 * n + valCount ym.rep ≤ _; omega) ds m3s ps.d1.num ps.d2.num
    (by rw [Hd.o, Hd.o, Hd.o, kr.val]) ps.d1.pos ps.d2.pos (fun _ => kr.pos)

/-- **The recursive call for `m1`** at `0x80005028` (both halves nonzero):
`d2`'s digit count spilled, then `_bc_rec_mul (u1, n_len (u1), v1,
n_len (v1), &m1)`. -/
theorem kara_m1call {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu0 hv0 : Hd} {hs0 : List Hd} {x1 x2 y1 y2 : NumObj}
    (ps : KSubs S M0 M R0 R sp q W n la lb z (some x1) hu0 (some x2) hv0 y1 y2)
    (hb : BcHeap S M H F (KList [] (some y2 :: some y1 :: hs0) A B z))
    (hp0 : hs0.Perm [some x1, hu0, some x2, hv0])
    (hown : HdOwned A B z (some y2 :: some y1 :: hs0))
    (hok : HdOK (some y2 :: some y1 :: hs0))
    (kz : KZero M z (zeroCount (some y2 :: some y1 :: hs0) + 2 + (4 * (la + lb + 2 - n) + 8)))
    (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (hx1p : 1 ≤ x1.rep.len) (hx2p : 1 ≤ x2.rep.len)
    (ds : KDiffSpec z (some x1) hu0 (some x2) hv0 u v n la lb N W)
    (m3s : KM3Spec z hu0 hv0 n la lb N W)
    (m1s : KM1Spec z (some x1) (some x2) n la lb N W) :
    DW live S Q 0x80005028#64 R M := by
  have hb' : BcHeap S M H F ((temps (some y2 :: some y1 :: hs0) ++ A) ++
      z.withRefs (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0)) :: B) := by
    simpa only [KList, List.nil_append, List.append_assoc] using hb
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hx1m : x1 ∈ (temps (some y2 :: some y1 :: hs0) ++ A) ++
      z.withRefs (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0)) :: B :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_filterMap.mpr
      ⟨some x1, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hp0.mem_iff.mpr (by simp))), rfl⟩))
  have hx2m : x2 ∈ (temps (some y2 :: some y1 :: hs0) ++ A) ++
      z.withRefs (z.rep.refs + zeroCount (some y2 :: some y1 :: hs0)) :: B :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_filterMap.mpr
      ⟨some x2, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hp0.mem_iff.mpr (by simp))), rfl⟩))
  have hx1 := hb'.nums x1 hx1m
  have hx2 := hb'.nums x2 hx2m
  num_facts hx1
  num_facts hx2
  have hln1 := hx1.len; have hln2 := hx2.len
  have h2 := ps.st.rm.r2
  have h24 := ps.tr.u1; have h27 := ps.tr.v1
  simp only [Hd.p] at h24 h27
  have h17 := ps.l2
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW' := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hm1f := m1s.fit
  have hm1s := m1s.size; have hm1w := m1s.stack
  simp only [Hd.o] at hm1f hm1s hm1w
  bc_run hlive hS [h2, h24, h27, h17, hln1, hln2,
    sxw_ofNat (show x1.rep.len < 2 ^ 31 by omega),
    sxw_ofNat (show x2.rep.len < 2 ^ 31 by omega)] at 0x80005040
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | skip
  apply st_80005040 hlive
  have st1 := ps.st.storeSlot cx 8 (BitVec.ofNat 64 y2.rep.len) (by omega)
  have hb1 := hb'.out_frame (MemOnly.store _ (sp - 192 + 8) 8 (BitVec.ofNat 64 y2.rep.len))
    fun a ha => by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hsv : ldv .ld (writeLog M [(sp - 192 + 8, 8, BitVec.ofNat 64 y2.rep.len)]) (sp - 192 + 8) =
      BitVec.ofNat 64 y2.rep.len := ldv_store_hit _ _ _
  have hmb1 : ldv .lw (writeLog M [(sp - 192 + 8, 8, BitVec.ofNat 64 y2.rep.len)]) mulBaseAddr =
      BitVec.ofNat 64 80 :=
    (GlobAgree.store (BitVec.ofNat 64 y2.rep.len) (by omega)).mulBase hmb
  have kz1 : KZero (writeLog M [(sp - 192 + 8, 8, BitVec.ofNat 64 y2.rep.len)]) z
      (zeroCount (some y2 :: some y1 :: hs0) + 2 + (4 * (la + lb + 2 - n) + 8)) :=
    (GlobAgree.store (BitVec.ofNat 64 y2.rep.len) (by omega)).zero kz
  have hl1 : ldv .ld (writeLog M [(sp - 192 + 8, 8, BitVec.ofNat 64 y2.rep.len)]) (sp - 192) =
      BitVec.ofNat 64 y1.rep.len := by rw [ldv_ld_miss _ _ (by omega)]; exact ps.l1
  have ps1 : KSubs S M0 (writeLog M [(sp - 192 + 8, 8, BitVec.ofNat 64 y2.rep.len)]) R0 R sp q W
      n la lb z (some x1) hu0 (some x2) hv0 y1 y2 :=
    ⟨st1, ps.tr, ps.s6, ps.s2, hl1, ps.l2, ps.d1, ps.d2⟩
  refine kara_child ih cx hk (st1.rm.keeps (by keeps_tac Keeps.refl _ _) (by bsimp [h2])) 40
    (by omega) (by decide) hm1s hm1w
    (KZero.withRefs (j := zeroCount (some y2 :: some y1 :: hs0))
      (kz1.mono (by have := hm1f; omega)))
    ⟨hx1m, hx2m, hx1p, hx2p, Nat.le_add_right _ _, Nat.le_add_right _ _,
      by omega, hmb1⟩ hb1 (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
    (by bsimp []) (by bsimp [h2]) ?_
  intro R' M' H' F' ym kk post
  bsimp []
  exact kara_m1ret hlive ih cx hk ps1 hp0 hown hok (hb1.nums x1 hx1m) (hb1.nums x2 hx2m)
    ((kk.mono (fun r hr => List.mem_cons_of_mem _ hr)).trans (by keeps_tac Keeps.refl _ _))
    hsv post kz1 hmb1 hNla hn1 ds m3s m1s

end Dc.Mach
