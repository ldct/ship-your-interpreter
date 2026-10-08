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
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 0) (hb : BcHeap S M H F (L1 ++ xr :: L2))
    (hr : ResSlot M L1 xr (sp - 192 + o)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 192 + o)) (h13 : R 13 = BitVec.ofNat 64 0)
    (hret : ∀ R' M' H' F' L' y, Keeps binClob R' R →
      BinPost S M M' H' F' L1 L2 xr (sp - 192 + o) (sp - 192) (Num.sub x1.rep.num x2.rep.num 0)
        L' y → DW live S Q (R 1) R' M') :
    DW live S Q 0x80004ac4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have ks := cx.kslot o (by omega) hoa
  exact bc_sub_spec hlive
    ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
      by simp only [heapEnd]; omega,
      ⟨fun i hi => ks.own _ (mem_accAddrs (by omega)), by omega, by omega, by omega⟩,
      fun a ha => ks.out a ha.1 ha.2, .inr (by omega), st.r2, hal⟩
    ha hb hr h10 h11 h12 h13
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

theorem KSubArgs.binArgs {z : NumObj} {x1 x2 : Hd} (h : KSubArgs z x1 x2) {P A B : List NumObj}
    {hs : List Hd} (h1 : x1 ∈ hs) (h2 : x2 ∈ hs) :
    BinArgs (KList P hs A B z) (Hd.objIn hs z x1) (Hd.objIn hs z x2) 0 :=
  ⟨Hd.objIn_mem h1 P A B z, Hd.objIn_mem h2 P A B z, (Hd.objIn_norm hs z x1).mpr h.n1,
    (Hd.objIn_norm hs z x2).mpr h.n2, by
      simp only [Hd.objIn_len', Hd.objIn_scale]; exact h.size⟩

/-- A difference `bc_sub` left: the new number heading the handles. -/
structure KDiff (y : NumObj) (n : Num) : Prop where
  num : y.rep.num = n
  norm : y.rep.Norm
  refs : y.rep.refs = 1
  owns : y.Owns

/-- The step after the differences `d1 = u1 - u0` and `d2 = v0 - v1`. -/
structure KSubs (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W n la lb : Nat)
    (z : NumObj) (hu1 hu0 hv1 hv0 : Hd) (y1 y2 : NumObj) : Prop where
  st : KAt S M0 M R0 R sp q W
  tr : KTailRegs z hu1 hu0 hv1 hv0 (some y1) (some y2) q n R
  s6 : R 22 = BitVec.ofNat 64 (la + lb)
  s2 : R 18 = BitVec.ofNat 64 zeroAddr
  l1 : ldv .ld M (sp - 192) = BitVec.ofNat 64 y1.rep.len
  l2 : R 17 = BitVec.ofNat 64 y2.rep.len
  d1 : KDiff y1 (Num.sub (Hd.o z hu1).rep.num (Hd.o z hu0).rep.num 0)
  d2 : KDiff y2 (Num.sub (Hd.o z hv0).rep.num (Hd.o z hv1).rep.num 0)

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

end Dc.Mach
