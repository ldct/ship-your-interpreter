import Dc.Mach.Bc.KaraFill

/-!
# `_bc_rec_mul`'s Karatsuba step: the product's `bc_new_num`

After `m3` (the recursive call at `0x80005148`, or the copy of `_zero_` at
`0x80005440`): `bc_new_num (ulen + vlen + 1, 0)`, its pointer stored through
`prod`, then the fill (`0x80005468` when `m1` was computed, `0x80005164`
when it is `_zero_`).

- `KPre`: the step's state before the product exists (`KMid` without it, with
  `s6 = ulen + vlen` and the `m1`-is-`_zero_` flag `s10`).
- `kara_newRet`: from either return of `bc_new_num` into the fill.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-! ## Reordering the handles -/

theorem zeroCount_perm {hs hs' : List Hd} (h : hs.Perm hs') : zeroCount hs = zeroCount hs' := by
  induction h with
  | nil => rfl
  | cons x _ ih => cases x <;> simp [ih]
  | swap x y l => cases x <;> cases y <;> simp
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem ViewsOwned.suffix : ∀ {L1 L2 : List NumObj}, ViewsOwned (L1 ++ L2) → ViewsOwned L2
  | [], _, h => h
  | _ :: _, _, .cons _ h => ViewsOwned.suffix h

theorem ViewsOwned.prefix {T : List NumObj} (hT : ViewsOwned T) :
    ∀ {P : List NumObj}, (∀ x ∈ P, x.Owns ∨ ∃ w ∈ T, w.Owns ∧ w.db = x.db) → ViewsOwned (P ++ T)
  | [], _ => hT
  | x :: P, h => by
    refine .cons ?_ (ViewsOwned.prefix hT fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x List.mem_cons_self with ho | ⟨w, hw, hwo, hwd⟩
    · exact .inl ho
    · exact .inr ⟨w, List.mem_append_right _ hw, hwo, hwd⟩

/-- Each temporary of `hs` owns its digits or is a view of an owner of the
caller's `A ++ z :: B`. -/
def HdOwned (A B : List NumObj) (z : NumObj) (hs : List Hd) : Prop :=
  ∀ x, some x ∈ hs → x.Owns ∨ ∃ w ∈ A ++ z :: B, w.Owns ∧ w.db = x.db

/-- **The handles reordered**: the number heap under any permutation of the
handles whose views stay before their owners. -/
theorem BcHeap.kperm {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {P A B : List NumObj}
    {z : NumObj} {hs hs' : List Hd} (hb : BcHeap S X M H F (KList P hs A B z)) (hp : hs.Perm hs')
    (hP : ∀ y ∈ P, y.Owns) (ho : HdOwned A B z hs') : BcHeap S X M H F (KList P hs' A B z) := by
  have hL : (KList P hs A B z).Perm (KList P hs' A B z) := by
    simp only [KList, zeroCount_perm hp, List.append_assoc]
    exact (List.Perm.refl P).append ((hp.filterMap id).append (List.Perm.refl _))
  have hT : ViewsOwned (A ++ z.withRefs (z.rep.refs + zeroCount hs') :: B) := by
    have hv := hb.views
    simp only [KList, zeroCount_perm hp, List.append_assoc] at hv
    exact ViewsOwned.suffix (L1 := P ++ temps hs) (by simpa only [List.append_assoc] using hv)
  refine ⟨hb.heap, hb.dead, hb.deadLive, fun x hx => hb.nums x (hL.mem_iff.mpr hx),
    fun x hx => hb.blocks x (hL.mem_iff.mpr hx),
    (List.Perm.append_left F (hL.flatMap_right NumObj.blocks)).nodup_iff.mp hb.distinct, ?_,
    hb.globOwn⟩
  simp only [KList, List.append_assoc]
  refine ViewsOwned.prefix (ViewsOwned.prefix hT ?_) fun y hy => .inl (hP y hy)
  · intro x hx
    rcases ho x (by simpa [temps] using hx) with h | ⟨w, hw, hwo, hwd⟩
    · exact .inl h
    · refine .inr ?_
      rcases List.mem_append.mp hw with hw | hw
      · exact ⟨w, List.mem_append_left _ hw, hwo, hwd⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, hwo, hwd⟩
      · exact ⟨w, List.mem_append_right _ (List.mem_cons_of_mem _ hw), hwo, hwd⟩

/-- **A copy of `_zero_`** (`bc_copy_num`): its count raised, one more
`none` handle. -/
theorem BcHeap.kzero {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {P A B : List NumObj}
    {z : NumObj} {hs : List Hd} (hb : BcHeap S X M H F (KList P hs A B z)) {v : BitVec 64}
    (hv : v.toNat % 2 ^ 32 = z.rep.refs + zeroCount hs + 1)
    (hk : z.rep.refs + zeroCount hs + 1 < 2 ^ 31) :
    BcHeap S X (writeLog M [(z.rep.p + 12, 4, v)]) H F (KList P (none :: hs) A B z) := by
  rw [KList_none]
  have hb' : BcHeap S X M H F ((P ++ temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B) := by
    simpa only [KList, List.append_assoc] using hb
  exact hb'.setRefs hv hk

/-- `KAt` through writes that keep the step's frame and, off the heap, every
byte outside the slot and the window. -/
theorem KAt.stack {S : Nat → Prop} {M0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    (cx : RmCtx S R0 sp q W) (st : KAt S M0 M R0 R sp q W)
    (hfr : ∀ a, sp - 192 ≤ a → a < sp → imgM M' a = imgM M a)
    (hag : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M' a = imgM M a) :
    KAt S M0 M' R0 R sp q W := by
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  exact ⟨st.rm.mem (st.rm.saved.transport (lo := 128) (top := 192) (hag := fun a h1 h2 =>
      hfr a (by omega) (by omega))) hag,
    st.saved2.transport (lo := 88) (top := 160) (hag := fun a h1 h2 => hfr a (by omega) (by omega))⟩

/-- `KSlots` through writes that keep the step's frame. -/
theorem KSlots.stack {z : NumObj} {hm1 hm2 hm3 : Hd} {sp : Nat} {M M' : Mem}
    (sl : KSlots z hm1 hm2 hm3 sp M) (hsp : 192 ≤ sp)
    (hfr : ∀ a, sp - 192 ≤ a → a < sp → imgM M' a = imgM M a) :
    KSlots z hm1 hm2 hm3 sp M' :=
  ⟨(ldv_congr .ld fun j hj => hfr _ (by omega) (by simp only [widthOfM] at hj; omega)).trans sl.m1,
    (ldv_congr .ld fun j hj => hfr _ (by omega) (by simp only [widthOfM] at hj; omega)).trans sl.m2,
    (ldv_congr .ld fun j hj => hfr _ (by omega) (by simp only [widthOfM] at hj; omega)).trans sl.m3⟩

/-- The step's state before the product: its frame, the handles' registers
and slots, `s6 = ulen + vlen`, `s10` whether `m1` is `_zero_`. -/
structure KPre (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W n la lb : Nat)
    (z : NumObj) (hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 : Hd) (fl : Bool) : Prop where
  st : KAt S M0 M R0 R sp q W
  tr : KTailRegs z hu1 hu0 hv1 hv0 hd1 hd2 q n R
  sl : KSlots z hm1 hm2 hm3 sp M
  s6 : R 22 = BitVec.ofNat 64 (la + lb)
  s10 : R 26 = BitVec.ofNat 64 (if fl then 1 else 0)

/-- The step's state before `m3`: `KPre` with only `m1`'s and `m2`'s slots. -/
structure KM3 (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W n la lb : Nat)
    (z : NumObj) (hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 : Hd) (fl : Bool) : Prop where
  st : KAt S M0 M R0 R sp q W
  tr : KTailRegs z hu1 hu0 hv1 hv0 hd1 hd2 q n R
  m1 : ldv .ld M (sp - 192 + 40) = BitVec.ofNat 64 (Hd.p z hm1)
  m2 : ldv .ld M (sp - 192 + 48) = BitVec.ofNat 64 (Hd.p z hm2)
  s6 : R 22 = BitVec.ofNat 64 (la + lb)
  s10 : R 26 = BitVec.ofNat 64 (if fl then 1 else 0)

/-- `KAt` through a store into the step's frame below the saved registers. -/
theorem KAt.storeSlot {S : Nat → Prop} {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    (cx : RmCtx S R0 sp q W) (st : KAt S M0 M R0 R sp q W) (o : Nat) (v : BitVec 64)
    (ho : o + 8 ≤ 88) (hd1 : ∀ p ∈ rmSlots, p.2 + 8 ≤ o ∨ o + 8 ≤ p.2 := by decide)
    (hd2 : ∀ p ∈ rmSlots2, p.2 + 8 ≤ o ∨ o + 8 ≤ p.2 := by decide) :
    KAt S M0 (writeLog M [(sp - 192 + o, 8, v)]) R0 R sp q W := by
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  exact ⟨st.rm.mem (st.rm.saved.storeFrame o v hd1) fun a _ _ hf =>
      imgM_store_miss _ _ (by simp only [frameIn] at hf; omega),
    st.saved2.storeFrame o v hd2⟩

/-- `KPre` through register changes off the step's registers. -/
theorem KPre.keeps {S : Nat → Prop} {M0 M : Mem} {R0 R R' : Nat → BitVec 64}
    {sp q W n la lb : Nat} {z : NumObj} {hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 : Hd} {fl : Bool}
    (pk : KPre S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 fl)
    {ks : List Nat} (kk : Keeps ks R' R)
    (hs : ∀ r ∈ [2, 8, 9, 19, 20, 21, 22, 23, 24, 25, 26, 27], r ∉ ks := by decide)
    (hsub : ∀ r ∈ ks, r ∈ rmAll := by decide) :
    KPre S M0 M R0 R' sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 fl :=
  ⟨⟨pk.st.rm.keeps (kk.mono hsub) (kk _ (hs 2 (by simp))), pk.st.saved2⟩,
    pk.tr.keeps kk fun r hr => hs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega), pk.sl,
    (kk _ (hs 22 (by simp))).trans pk.s6, (kk _ (hs 26 (by simp))).trans pk.s10⟩

/-- `KPre` through a callee's writes below the step's frame and on the heap. -/
theorem KPre.out {S : Nat → Prop} {M0 M M' : Mem} {R0 R : Nat → BitVec 64}
    {sp q W n la lb : Nat} {z : NumObj} {hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 : Hd} {fl : Bool}
    (cx : RmCtx S R0 sp q W)
    (pk : KPre S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 fl) {k : Nat}
    (hkW : 192 + k ≤ W) (ho : OutFrame (frameIn (sp - 192) k) M' M) :
    KPre S M0 M' R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 fl := by
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have hfr : ∀ a, sp - 192 ≤ a → a < sp → imgM M' a = imgM M a := fun a h1 h2 =>
    ho a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [frameIn]; omega)
  exact ⟨pk.st.stack cx hfr fun a ha _ hf => ho a ha (by simp only [frameIn] at hf ⊢; omega),
    pk.tr, pk.sl.stack (by omega) hfr, pk.s6, pk.s10⟩

/-- `KPre` once the product's pointer is in the slot: `KMid`. -/
theorem KPre.toMid {S : Nat → Prop} {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    {sp q W n la lb : Nat} {z : NumObj} {hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 : Hd} {fl : Bool}
    {y : NumObj} (cx : RmCtx S R0 sp q W)
    (pk : KPre S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 fl)
    (kk : Keeps [15] R' R) (hm : MemOnly (slotBytes q) M' M)
    (hq : ldv .ld M' q = BitVec.ofNat 64 y.sb.pay) :
    KMid S M0 M' R0 R' sp q W n z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 y := by
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have hap := cx.slotApart
  have hfr : ∀ a, sp - 192 ≤ a → a < sp → imgM M' a = imgM M a := fun a h1 h2 =>
    hm a fun h => by simp only [slotBytes] at h; omega
  have st2 := pk.st.stack cx hfr fun a _ hs _ => hm a hs
  exact ⟨⟨st2.rm.keeps (kk.mono (by decide)) (kk.get 2), st2.saved2⟩, pk.tr.keeps kk,
    pk.sl.stack (by omega) hfr, hq⟩

/-- **From a return of the product's `bc_new_num`** (`0x80005158` or
`0x8000545c`): the pointer stored through `prod`, then the fill. -/
theorem kara_newRet {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj} {z : NumObj}
    {u v : NumRep} {y : NumObj} {H : Heap} {F : List Blk} {fl : Bool} {pc : BitVec 64}
    (hpc : pc = 0x80005158#64 ∨ pc = 0x8000545c#64)
    (cx : RmCtx S R0 sp q W) (hk : RmK live S X Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2 : Hd}
    (pk : KPre S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 fl)
    (hb : BcHeap S X M H F (y :: KList [] (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) A B z))
    (hok : HdOK (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2)) (hz : 1 ≤ z.rep.refs)
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false) (hyv : y.rep.val = y.rep.ptr)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0) (hP : dvalBE y.rep.ds = 0)
    (h10 : R 10 = BitVec.ofNat 64 y.sb.pay)
    (hm1z : fl = true → hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1) = 0)
    (hfit1 : fl = false →
      2 * n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1).rep ≤ la + lb + 1)
    (hfit3 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3).rep ≤
      la + lb + 1)
    (hfit2 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2).rep ≤
      la + lb + 1)
    (hw1 : fl = false → 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1).rep.len)
    (hw2 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2).rep.len)
    (hw3 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3).rep.len)
    (hv : KFillVal (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3)) (10 ^ n) (kUV u v la lb)
      (la + lb + 1)
      ((Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hd1).rep.neg !=
        (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hd2).rep.neg)) :
    DW live S Q pc R M := by
  have hsf := pk.st.rm
  have hqs := cx.slot
  have q2 := hqs.hi; have q3 := hqs.lo; have q4 := hqs.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hyp : y.rep.p = y.sb.pay := (hb.blocks y List.mem_cons_self).sPay
  have h9 := pk.tr.q
  have h26 := pk.s10
  have go : ∀ R' M', Keeps [15] R' R → R' 15 = BitVec.ofNat 64 y.sb.pay →
      R' 10 = BitVec.ofNat 64 y.sb.pay → MemOnly (slotBytes q) M' M →
      ldv .ld M' q = BitVec.ofNat 64 y.sb.pay →
      (fl = true → DW live S Q 0x80005164#64 R' M') ∧ (fl = false → DW live S Q 0x80005468#64 R' M') :=
    fun R' M' kk r15 r10 hm hq => by
      have km := pk.toMid (y := y) cx kk hm hq
      have hb2 := hb.out_frame hm fun a ha => cx.slotOut a ha
      refine ⟨fun hf => kara_fill5164 hlive cx hk km hb2 hok hz hyo hyr hyn hyv hyl hys (r15.trans (by rw [hyp]))
        (by rw [hP, hm1z hf]; simp) hfit3 hfit2 hw2 hw3 hv,
        fun hf => kara_fill5468 hlive cx hk km hb2 hok hz hyo hyr hyn hyv hyl hys (r10.trans (by rw [hyp]))
          hP (hfit1 hf) hfit3 hfit2 (hw1 hf) hw2 hw3 hv⟩
  have fin := fun (b : Bool) => go (upd R 15 (BitVec.ofNat 64 y.sb.pay))
    (writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)]) (by keeps_tac Keeps.refl _ _) (by bsimp [])
    (by bsimp [h10]) (MemOnly.store _ _ _ _) (ldv_store_hit _ _ _)
  rcases hpc with rfl | rfl <;> cases fl <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h26 <;>
    bc_run hlive hS [h9, h10, h26] at 0x80005164 0x80005468 <;>
    first | exact hqs.acc | exact (fin true).1 (by simp) | exact (fin true).2 (by simp)

/-- **The product's `bc_new_num (ulen + vlen + 1, 0)`** at `0x80004250`,
called from `0x80005154` or `0x80005458`. -/
theorem kara_newCall {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj} {z : NumObj}
    {u v : NumRep} {H : Heap} {F : List Blk} {fl : Bool}
    (hra : R 1 = 0x80005158#64 ∨ R 1 = 0x8000545c#64)
    (cx : RmCtx S R0 sp q W) (hk : RmK live S X Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2 : Hd}
    (pk : KPre S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 fl)
    (hb : BcHeap S X M H F (KList [] (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) A B z))
    (hok : HdOK (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2)) (hz : 1 ≤ z.rep.refs)
    (hN : la + lb < 2 ^ 30)
    (h10 : R 10 = BitVec.ofNat 64 (la + lb + 1)) (h11 : R 11 = 0#64)
    (hm1z : fl = true → hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1) = 0)
    (hfit1 : fl = false →
      2 * n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1).rep ≤ la + lb + 1)
    (hfit3 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3).rep ≤
      la + lb + 1)
    (hfit2 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2).rep ≤
      la + lb + 1)
    (hw1 : fl = false → 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1).rep.len)
    (hw2 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2).rep.len)
    (hw3 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3).rep.len)
    (hv : KFillVal (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3)) (10 ^ n) (kUV u v la lb)
      (la + lb + 1)
      ((Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hd1).rep.neg !=
        (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hd2).rep.neg)) :
    DW live S Q 0x80004250#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hab := cx.above
  simp only [heapEnd] at hab
  have hsf' : StackFrame S (sp - 192) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine bc_new_num_spec (len := la + lb + 1) (scale := 0) hlive hb.newHeap hsf'
    (by simp only [heapEnd]; omega) (by omega) (Nat.le_add_left _ _) _ h10 (by rw [h11])
    (by rw [pk.st.rm.r2]) (by rcases hra with h | h <;> rw [h] <;> decide)
    ⟨fun R1 Mt1 H1 F1 y hk1 hp1 hr1 => ?_, fun R' Mt' hr2 hout => ?_⟩
  · have hrep := hp1.rep
    exact kara_newRet hlive hra cx hk ((pk.out cx (k := 32) (by omega) hp1.out).keeps hk1)
      (NewNumPost.insert hb hp1) hok hz hp1.owns (by rw [hrep]; rfl) (by rw [hrep]; rfl)
      (by rw [hrep]; rfl) (by rw [hrep]; rfl) (by rw [hrep]; rfl)
      (by rw [hrep]; simp only [zeroRep, dvalBE_replicate_zero]) hr1 hm1z hfit1 hfit3 hfit2 hw1 hw2 hw3 hv
  · refine hk.oom R' Mt' (sp - 192 - 32) (by omega) (by omega) hr2 fun a ha hs hf => ?_
    rw [hout a ha fun h => hf (by simp only [frameIn] at *; omega)]
    exact pk.st.rm.out a ha hs hf

/-- **`m3` computed** (`0x8000514c`, after the recursive call): the product's
`bc_new_num`. -/
theorem kara_new514c {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj} {z : NumObj}
    {u v : NumRep} {H : Heap} {F : List Blk} {fl : Bool}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S X Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2 : Hd}
    (pk : KPre S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 fl)
    (hb : BcHeap S X M H F (KList [] (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) A B z))
    (hok : HdOK (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2)) (hz : 1 ≤ z.rep.refs)
    (hN : la + lb < 2 ^ 30)
    (hm1z : fl = true → hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1) = 0)
    (hfit1 : fl = false →
      2 * n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1).rep ≤ la + lb + 1)
    (hfit3 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3).rep ≤
      la + lb + 1)
    (hfit2 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2).rep ≤
      la + lb + 1)
    (hw1 : fl = false → 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1).rep.len)
    (hw2 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2).rep.len)
    (hw3 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3).rep.len)
    (hv : KFillVal (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm1))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm2))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hm3)) (10 ^ n) (kUV u v la lb)
      (la + lb + 1)
      ((Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hd1).rep.neg !=
        (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2) z hd2).rep.neg)) :
    DW live S Q 0x8000514c#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h22 := pk.s6
  bc_run hlive hS [h22, sxw_ofNat] at 0x80005154
  apply st_80005154 hlive
  exact kara_newCall hlive (.inl (by bsimp [])) cx hk (pk.keeps (ks := [1, 10, 11]) (by keeps_tac Keeps.refl _ _)) hb hok hz
    hN (by bsimp [sxw_ofNat (show la + lb + 1 < 2 ^ 31 by omega)]) (by bsimp []) hm1z hfit1 hfit3 hfit2 hw1 hw2 hw3 hv

/-- **`m3 = _zero_`** (`0x80005440`, a factor zero): the copy of `_zero_`
into `m3`'s slot, then the product's `bc_new_num`. -/
theorem kara_new5440 {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj} {z : NumObj}
    {u v : NumRep} {H : Heap} {F : List Blk} {fl : Bool}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S X Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hm1 hv0 hm2 hd1 hd2 : Hd} {hs : List Hd}
    (pk : KM3 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 fl)
    (hb : BcHeap S X M H F (KList [] hs A B z))
    (hpm : (none :: hs).Perm (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2))
    (hown : HdOwned A B z (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2))
    (hok : HdOK (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2)) (hz : 1 ≤ z.rep.refs)
    (hzk : z.rep.refs + zeroCount hs + 1 < 2 ^ 31)
    (h12 : R 12 = BitVec.ofNat 64 z.rep.p) (hN : la + lb < 2 ^ 30)
    (hm1z : fl = true → hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z hm1) = 0)
    (hfit1 : fl = false →
      2 * n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z hm1).rep ≤ la + lb + 1)
    (hfit3 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z none).rep ≤
      la + lb + 1)
    (hfit2 : n + valCount (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z hm2).rep ≤
      la + lb + 1)
    (hw1 : fl = false → 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z hm1).rep.len)
    (hw2 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z hm2).rep.len)
    (hw3 : 1 ≤ (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z none).rep.len)
    (hv : KFillVal (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z hm1))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z hm2))
      (hdVal (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z none)) (10 ^ n) (kUV u v la lb)
      (la + lb + 1)
      ((Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z hd1).rep.neg !=
        (Hd.objIn (kHs hu1 hu0 hv1 hm1 hv0 hm2 none hd1 hd2) z hd2).rep.neg)) :
    DW live S Q 0x80005440#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hzm : z.withRefs (z.rep.refs + zeroCount hs) ∈ KList [] hs A B z :=
    List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums _ hzm
  have hrf : ldv .lw M (z.rep.p + 12) = BitVec.ofNat 64 (z.rep.refs + zeroCount hs) := hn.refs
  have e1 : 2147603920 ≤ z.rep.p := hn.shape.pLo
  have e2 : z.rep.p + 40 ≤ heapEnd := hn.shape.pHi
  have e3 : z.rep.p % 8 = 0 := hn.shape.pAl
  simp only [heapEnd] at e2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h22 := pk.s6
  have h2 := pk.st.rm.r2
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  bc_run hlive hS [h12, hrf, h22, h2, sxw_ofNat] at 0x80005458
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  apply st_80005458 hlive
  have hmo : MemOnly (fun a => z.rep.p + 12 ≤ a ∧ a < z.rep.p + 12 + 4)
      (writeLog M [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + zeroCount hs + 1))]) M :=
    MemOnly.store _ _ _ _
  have hP1 : ∀ a, (z.rep.p + 12 ≤ a ∧ a < z.rep.p + 12 + 4) → heapStart ≤ a ∧ a < heapEnd :=
    fun a h => by simp only [heapStart, heapEnd]; omega
  have st1 := pk.st.heapOnly cx hmo hP1
  have hap : sp - 192 + 56 + 8 ≤ z.rep.p + 12 ∨ z.rep.p + 12 + 4 ≤ sp - 192 + 56 := by omega
  have pk2 : KPre S M0 (writeLog (writeLog M [(z.rep.p + 12, 4,
      BitVec.ofNat 64 (z.rep.refs + zeroCount hs + 1))]) [(sp - 192 + 56, 8, BitVec.ofNat 64 z.rep.p)])
      R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 none fl :=
    ⟨st1.storeSlot cx 56 _ (by omega), pk.tr,
      ⟨by rw [ldv_ld_miss _ _ (by omega), (hmo.ldv_off hP1 (by simp only [heapStart, heapEnd]; omega))]; exact pk.m1,
        by rw [ldv_ld_miss _ _ (by omega), (hmo.ldv_off hP1 (by simp only [heapStart, heapEnd]; omega))]; exact pk.m2,
        ldv_store_hit _ _ _⟩, pk.s6, pk.s10⟩
  have hb2 := ((hb.kzero (toNat_ofNat_mod32 (by omega)) hzk).out_frame (MemOnly.store _ (sp - 192 + 56) 8 (BitVec.ofNat 64 z.rep.p))
    fun a ha => by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega).kperm hpm
    (fun _ h => by simp at h) hown
  exact kara_newCall hlive (.inr (by bsimp [])) cx hk (pk2.keeps (ks := [1, 10, 11, 15])
    (by keeps_tac Keeps.refl _ _)) hb2 hok hz hN (by bsimp []) (by bsimp []) hm1z hfit1 hfit3 hfit2 hw1 hw2 hw3 hv

end Dc.Mach
