import Dc.Mach.Bc.KaraCall
import Dc.Mach.Bc.KaraScanSites

/-!
# `_bc_rec_mul`'s Karatsuba step: `m3 = u0 · v0`

From `0x800050d4`: `bc_is_zero (u0)`, `bc_is_zero (v0)`; either zero, `m3`
is a copy of `_zero_` (`0x80005440`), else `_bc_rec_mul (u0, v0, &m3)`
(`0x80005148`, by `RmIH`); then the product's `bc_new_num`.

- `Hd.o`: a handle's object up to its count (the `Hd.objIn` of any list).
- `KAt.call`: the step's frame through a recursive call into one of its slots.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- A handle's object, `_zero_` for `none` (counts aside). -/
def Hd.o (z : NumObj) : Hd → NumObj
  | some x => x
  | none => z

theorem Hd.objIn_ds (hs : List Hd) (z : NumObj) (h : Hd) :
    (Hd.objIn hs z h).rep.ds = (Hd.o z h).rep.ds := by cases h <;> rfl
theorem Hd.objIn_len (hs : List Hd) (z : NumObj) (h : Hd) :
    (Hd.objIn hs z h).rep.len = (Hd.o z h).rep.len := by cases h <;> rfl
theorem Hd.objIn_neg (hs : List Hd) (z : NumObj) (h : Hd) :
    (Hd.objIn hs z h).rep.neg = (Hd.o z h).rep.neg := by cases h <;> rfl
theorem Hd.hdVal_objIn (hs : List Hd) (z : NumObj) (h : Hd) :
    hdVal (Hd.objIn hs z h) = hdVal (Hd.o z h) := by cases h <;> rfl
theorem Hd.valCount_objIn (hs : List Hd) (z : NumObj) (h : Hd) :
    valCount (Hd.objIn hs z h).rep = valCount (Hd.o z h).rep := by cases h <;> rfl

theorem HdOwned.perm {A B : List NumObj} {z : NumObj} {hs hs' : List Hd} (h : HdOwned A B z hs)
    (hp : hs.Perm hs') : HdOwned A B z hs' := fun x hx => h x (hp.mem_iff.mpr hx)

theorem HdOwned.cons {A B : List NumObj} {z : NumObj} {hs : List Hd} (h : HdOwned A B z hs)
    {h3 : Hd} (h3o : ∀ x, h3 = some x → x.Owns) : HdOwned A B z (h3 :: hs) := fun x hx => by
  rcases List.mem_cons.mp hx with e | hx
  · exact .inl (h3o x e.symm)
  · exact h x hx

theorem HdOK.perm {hs hs' : List Hd} (h : HdOK hs) (hp : hs.Perm hs') : HdOK hs' :=
  fun x hx => h x (hp.mem_iff.mpr hx)

theorem HdOK.cons {hs : List Hd} (h : HdOK hs) {h3 : Hd} (h3o : ∀ x, h3 = some x → x.rep.refs = 1) :
    HdOK (h3 :: hs) := fun x hx => by
  rcases List.mem_cons.mp hx with e | hx
  · exact h3o x e.symm
  · exact h x hx

/-- Objects before `y` in the heap have other struct pointers. -/
theorem BcHeap.p_ne_split {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {y : NumObj} (h : BcHeap S M H F (L1 ++ y :: L2)) {x : NumObj}
    (hx : x ∈ L1) : x.rep.p ≠ y.rep.p := by
  have hd := (List.nodup_append.mp h.distinct).2.1
  rw [objBlocks_append] at hd
  have hne : x.sb ≠ y.sb := (List.nodup_append.mp hd).2.2 _
    (List.mem_flatMap.mpr ⟨x, hx, x.sb_mem_blocks⟩) _
    (List.mem_flatMap.mpr ⟨y, List.mem_cons_self, y.sb_mem_blocks⟩)
  have hxb := h.blocks x (List.mem_append_left _ hx)
  have hyb := h.blocks y (List.mem_append_right _ List.mem_cons_self)
  have hxs := hxb.sSz; have hys := hyb.sSz
  intro e
  rw [hxb.sPay, hyb.sPay] at e
  exact live_apart h.heap hxb.sLive hyb.sLive hne (a := x.sb.pay)
    ⟨Nat.le_refl _, by simp only [Blk.fin, Blk.pay]; omega⟩
    ⟨by omega, by simp only [Blk.fin, Blk.pay] at e ⊢; omega⟩

/-- `KZero` of `_zero_` with `j` more references. -/
theorem KZero.withRefs {M : Mem} {z : NumObj} {k j : Nat} (h : KZero M z (j + k)) :
    KZero M (z.withRefs (z.rep.refs + j)) k :=
  ⟨h.glob, h.len, h.scale, h.ds, by simp only [NumObj.withRefs]; have := h.refs; omega,
    by simp only [NumObj.withRefs]; have := h.room; omega⟩

/-- `KM3` through register changes off the step's registers. -/
theorem KM3.keeps {S : Nat → Prop} {M0 M : Mem} {R0 R R' : Nat → BitVec 64}
    {sp q W n la lb : Nat} {z : NumObj} {hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 : Hd} {fl : Bool}
    (pk : KM3 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 fl)
    {ks : List Nat} (kk : Keeps ks R' R)
    (hs : ∀ r ∈ [2, 8, 9, 19, 20, 21, 22, 23, 24, 25, 26, 27], r ∉ ks := by decide)
    (hsub : ∀ r ∈ ks, r ∈ rmAll := by decide) :
    KM3 S M0 M R0 R' sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 fl :=
  ⟨⟨pk.st.rm.keeps (kk.mono hsub) (kk _ (hs 2 (by simp))), pk.st.saved2⟩,
    pk.tr.keeps kk fun r hr => hs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega), pk.m1, pk.m2,
    (kk _ (hs 22 (by simp))).trans pk.s6, (kk _ (hs 26 (by simp))).trans pk.s10⟩

/-- `KAt` through a recursive call into the slot `sp - 192 + o`. -/
theorem KAt.call {S : Nat → Prop} {M0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    (cx : RmCtx S R0 sp q W) (st : KAt S M0 M R0 R sp q W) (o : Nat) (ho : o + 8 ≤ 88)
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - 192 + o) a → ¬ frameIn (sp - 192) (W - 192) a →
      imgM M' a = imgM M a) :
    KAt S M0 M' R0 R sp q W := by
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have hfr : ∀ a, sp - 192 + 88 ≤ a → a < sp → imgM M' a = imgM M a := fun a h1 h2 =>
    hout a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)
  exact ⟨st.rm.mem (st.rm.saved.transport (lo := 128) (top := 192) (hag := fun a h1 h2 =>
      hfr a (by omega) (by omega))) fun a ha hs hf => hout a ha
        (fun h => hf (by simp only [slotBytes, frameIn] at h ⊢; omega))
        (fun h => hf (by simp only [frameIn] at h ⊢; omega)),
    st.saved2.transport (lo := 88) (top := 160) (hag := fun a h1 h2 => hfr a (by omega) (by omega))⟩

/-- A handle's value is below `10 ^ len`. -/
theorem NumAt.hdVal_lt {M : Mem} {x : NumObj} (h : NumAt M x.rep) : hdVal x < 10 ^ x.rep.len :=
  dvalBE_take_lt h.shape.dig (by rw [h.shape.dsLen]; omega)

/-- A leading zero digit: the value has one digit fewer. -/
theorem valCount_le_of_lt {o : NumRep} (hl : o.ds.length = o.len + o.scale) (h1 : 1 ≤ o.len)
    (hlt : dvalBE o.ds < 10 ^ (o.len + o.scale - 1)) : valCount o ≤ o.len - 1 := by
  unfold valCount
  rcases hds : o.ds with _ | ⟨d, rest⟩
  · rw [hds] at hl; simp at hl; omega
  · rw [hds] at hl hlt
    rw [dvalBE_cons] at hlt
    simp only [List.length_cons] at hl
    have : d = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact h
      · exfalso
        have : 10 ^ rest.length ≤ d * 10 ^ rest.length := Nat.le_mul_of_pos_left _ h
        rw [show o.len + o.scale - 1 = rest.length by omega] at hlt; omega
    simp [this]

/-- What a recursive call's result gives the step: the product `y` heading
the handles, its slot, its value and digit count. -/
structure KRet (S : Nat → Prop) (M' : Mem) (H' : Heap) (F' : List Blk) (hs : List Hd)
    (A B : List NumObj) (z x0 y0 y : NumObj) (qs : Nat) : Prop where
  heap : BcHeap S M' H' F' (KList [] (some y :: hs) A B z)
  owns : y.Owns
  refs : y.rep.refs = 1
  slot : ldv .ld M' qs = BitVec.ofNat 64 (Hd.p z (some y))
  val : hdVal y = hdVal x0 * hdVal y0
  vc : valCount y.rep ≤ x0.rep.len + y0.rep.len

/-- `RmPost` of a recursive call on two handles of the step. -/
theorem RmPost.kret {S : Nat → Prop} {M M' : Mem} {H' : Heap} {F' : List Blk} {hs : List Hd}
    {A B : List NumObj} {z x0 y0 y : NumObj} {qs sp' W' : Nat}
    (post : RmPost S M M' H' F' ((temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B)
      x0.rep y0.rep x0.rep.len y0.rep.len qs sp' W' y)
    (hx0 : NumAt M x0.rep) (hy0 : NumAt M y0.rep) :
    KRet S M' H' F' hs A B z x0 y0 y qs := by
  have hyb := post.heap.blocks y List.mem_cons_self
  have hyn := post.heap.nums y List.mem_cons_self
  have hlen : y.rep.ds.length = y.rep.len := by rw [hyn.shape.dsLen, post.scale]; rfl
  have hyv : hdVal y = hdVal x0 * hdVal y0 := by
    show dvalBE (y.rep.ds.take y.rep.len) = _
    rw [List.take_of_length_le (by omega), post.val]
  have hlt := Nat.mul_lt_mul'' hx0.hdVal_lt hy0.hdVal_lt
  rw [← Nat.pow_add] at hlt
  refine ⟨?_, post.owns, post.refs, post.slot.trans (by rw [← hyb.sPay]; rfl), hyv, ?_⟩
  · have := post.heap
    simpa only [KList, temps, List.filterMap_cons, id, zeroCount_some, List.nil_append,
      List.append_assoc, List.cons_append] using this
  · have := valCount_le_of_lt hyn.shape.dsLen hyn.shape.lenPos (by
      rw [post.len, post.scale, Nat.add_zero, Nat.add_sub_cancel]
      have : dvalBE y.rep.ds = hdVal y := by
        show _ = dvalBE (y.rep.ds.take y.rep.len); rw [List.take_of_length_le (by omega)]
      rw [this, hyv]; exact hlt)
    rw [post.len] at this; omega

/-- **`m3` returned** (`0x8000514c`): `_bc_rec_mul (u0, v0)`'s product in
`m3`'s slot; the handles reordered, then the product's `bc_new_num`. -/
theorem kara_m3ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H' : Heap} {F' : List Blk} {fl : Bool}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hv1 hm1 hm2 hd1 hd2 : Hd} {hs : List Hd} {x0 y0 y : NumObj}
    (pk : KM3 S M0 M R0 R sp q W n la lb z hu1 (some x0) hv1 (some y0) hd1 hd2 hm1 hm2 fl)
    (hpm : ∀ h3 : Hd, (h3 :: hs).Perm (kHs hu1 (some x0) hv1 hm1 (some y0) hm2 h3 hd1 hd2))
    (hown : HdOwned A B z hs) (hok : HdOK hs) (hzr : 1 ≤ z.rep.refs)
    (hx0 : NumAt M x0.rep) (hy0 : NumAt M y0.rep)
    (kk : Keeps (1 :: binClob) R' R)
    (post : RmPost S M M' H' F' ((temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B)
      x0.rep y0.rep x0.rep.len y0.rep.len (sp - 192 + 56) (sp - 192) (W - 192) y)
    (hNla : la + lb < 2 ^ 30)
    (hm1z : fl = true → hdVal (Hd.o z hm1) = 0)
    (hfit1 : fl = false → 2 * n + valCount (Hd.o z hm1).rep ≤ la + lb + 1)
    (hfit2 : n + valCount (Hd.o z hm2).rep ≤ la + lb + 1)
    (hfit3 : n + x0.rep.len + y0.rep.len ≤ la + lb + 1)
    (hv : KFillVal (hdVal (Hd.o z hm1)) (hdVal (Hd.o z hm2)) (hdVal x0 * hdVal y0) (10 ^ n)
      (kUV u v la lb) (la + lb + 1) ((Hd.o z hd1).rep.neg != (Hd.o z hd2).rep.neg)) :
    DW live S Q 0x8000514c#64 R' M' := by
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have kr := post.kret hx0 hy0
  have st := pk.st.call cx 56 (by omega) post.out
  have hfr : ∀ a, sp - 192 + 40 ≤ a → a < sp - 192 + 56 → imgM M' a = imgM M a := fun a h1 h2 =>
    post.out a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)
  have pk2 : KPre S M0 M' R0 R sp q W n la lb z hu1 (some x0) hv1 (some y0) hd1 hd2 hm1 hm2 (some y) fl :=
    ⟨st, pk.tr,
      ⟨(ldv_congr .ld fun j hj => hfr _ (by omega) (by simp only [widthOfM] at hj; omega)).trans pk.m1,
        (ldv_congr .ld fun j hj => hfr _ (by omega) (by simp only [widthOfM] at hj; omega)).trans pk.m2,
        kr.slot⟩, pk.s6, pk.s10⟩
  have hb2 := kr.heap.kperm (hpm (some y)) (fun _ h => nomatch h)
    ((hown.cons fun x e => by cases e; exact kr.owns).perm (hpm (some y)))
  have hvc := kr.vc
  refine kara_new514c hlive cx hk (pk2.keeps kk) hb2 ((hok.cons fun x e => by
      cases e; exact kr.refs).perm (hpm (some y))) hzr hNla ?_ ?_ ?_ ?_ ?_
  · simpa only [Hd.hdVal_objIn] using hm1z
  · simpa only [Hd.valCount_objIn] using hfit1
  · show n + valCount y.rep ≤ _; omega
  · simpa only [Hd.valCount_objIn] using hfit2
  · show KFillVal _ _ (hdVal y) _ _ _ _
    rw [kr.val]; simpa only [Hd.hdVal_objIn, Hd.objIn_neg] using hv

/-- A zero handle's value. -/
theorem HdZero.val {z : NumObj} {h : Hd} (hz : HdZero h) (hzd : z.rep.ds = [0]) (hzl : z.rep.len = 1) :
    hdVal (Hd.o z h) = 0 := by
  cases h with
  | none => show dvalBE (z.rep.ds.take z.rep.len) = 0; rw [hzd, hzl]; rfl
  | some x =>
    show dval (x.rep.ds.take x.rep.len) = 0
    rw [dval_eq_zero_iff]
    intro j hj
    simp only [List.length_take] at hj
    rw [getD_take (by omega)]
    exact hz x rfl j (by omega)

/-- The recursive call for `m3` at `0x8000513c` (both factors nonzero):
`_bc_rec_mul (u0, n_len (u0), v0, n_len (v0), &m3)`. -/
theorem kara_m3call {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H : Heap} {F : List Blk} {fl : Bool}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hv1 hm1 hm2 hd1 hd2 : Hd} {hs : List Hd} {x0 y0 : NumObj}
    (pk : KM3 S M0 M R0 R sp q W n la lb z hu1 (some x0) hv1 (some y0) hd1 hd2 hm1 hm2 fl)
    (hb : BcHeap S M H F (KList [] hs A B z))
    (hpm : ∀ h3 : Hd, (h3 :: hs).Perm (kHs hu1 (some x0) hv1 hm1 (some y0) hm2 h3 hd1 hd2))
    (hown : HdOwned A B z hs) (hok : HdOK hs) (hx0m : some x0 ∈ hs) (hy0m : some y0 ∈ hs)
    (kz : KZero M z (zeroCount hs + (4 * (x0.rep.len + y0.rep.len) + 8)))
    (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (h11 : R 11 = BitVec.ofNat 64 x0.rep.len) (h13 : R 13 = BitVec.ofNat 64 y0.rep.len)
    (hN : x0.rep.len + y0.rep.len ≤ N) (hW : rmStack (x0.rep.len + y0.rep.len) + 192 ≤ W)
    (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (hm1z : fl = true → hdVal (Hd.o z hm1) = 0)
    (hfit1 : fl = false → 2 * n + valCount (Hd.o z hm1).rep ≤ la + lb + 1)
    (hfit2 : n + valCount (Hd.o z hm2).rep ≤ la + lb + 1)
    (hfit3 : n + x0.rep.len + y0.rep.len ≤ la + lb + 1)
    (hv : KFillVal (hdVal (Hd.o z hm1)) (hdVal (Hd.o z hm2)) (hdVal x0 * hdVal y0) (10 ^ n)
      (kUV u v la lb) (la + lb + 1) ((Hd.o z hd1).rep.neg != (Hd.o z hd2).rep.neg)) :
    DW live S Q 0x8000513c#64 R M := by
  have hb' : BcHeap S M H F ((temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B) := by
    simpa only [KList, List.nil_append, List.append_assoc] using hb
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hxm : x0 ∈ (temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_filterMap.mpr ⟨some x0, hx0m, rfl⟩))
  have hym : y0 ∈ (temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_filterMap.mpr ⟨some y0, hy0m, rfl⟩))
  have hx0 := hb'.nums x0 hxm
  have hy0 := hb'.nums y0 hym
  have h2 := pk.st.rm.r2
  have h19 := pk.tr.u0
  have h20 := pk.tr.v0
  simp only [Hd.p] at h19 h20
  have hab := cx.above; have hW' := cx.big
  simp only [heapEnd] at hab
  bc_run hlive hS [h2, h19, h20] at 0x80005148
  apply st_80005148 hlive
  refine kara_child ih cx hk (pk.st.rm.keeps (by keeps_tac Keeps.refl _ _) (by bsimp [h2])) 56
    (by omega) (by decide) hN hW kz.withRefs
    ⟨hxm, hym, hx0.shape.lenPos, hy0.shape.lenPos, Nat.le_add_right _ _, Nat.le_add_right _ _,
      by omega, hmb⟩ hb' (by bsimp []) (by bsimp []) (by bsimp [h11]) (by bsimp [])
    (by bsimp [h13]) (by bsimp [h2]) ?_
  intro R' M' H' F' y kk post
  bsimp []
  exact kara_m3ret hlive cx hk pk hpm hown hok kz.refs hx0 hy0
    ((kk.mono (fun r hr => List.mem_cons_of_mem _ hr)).trans (by keeps_tac Keeps.refl _ _))
    post hNla hm1z hfit1 hfit2 hfit3 hv

/-- **`m3 = u0 · v0`** from `0x800050d4`: `u0` or `v0` zero, a copy of
`_zero_`; else the recursive call; then the product's `bc_new_num`. -/
theorem kara_m3 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H : Heap} {F : List Blk} {fl : Bool}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hv0 hm1 hm2 hd1 hd2 : Hd} {hs : List Hd}
    (pk : KM3 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 fl)
    (hb : BcHeap S M H F (KList [] hs A B z))
    (hpm : ∀ h3 : Hd, (h3 :: hs).Perm (kHs hu1 hu0 hv1 hm1 hv0 hm2 h3 hd1 hd2))
    (hown : HdOwned A B z hs) (hok : HdOK hs) (hu0m : hu0 ∈ hs) (hv0m : hv0 ∈ hs)
    (kz : KZero M z (zeroCount hs + (4 * ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len) + 8)))
    (h12 : R 12 = BitVec.ofNat 64 z.rep.p) (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hN : (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ N)
    (hW : rmStack ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len) + 192 ≤ W)
    (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (hm1z : fl = true → hdVal (Hd.o z hm1) = 0)
    (hfit1 : fl = false → 2 * n + valCount (Hd.o z hm1).rep ≤ la + lb + 1)
    (hfit2 : n + valCount (Hd.o z hm2).rep ≤ la + lb + 1)
    (hfit3 : n + (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ la + lb + 1)
    (hv : KFillVal (hdVal (Hd.o z hm1)) (hdVal (Hd.o z hm2))
      (hdVal (Hd.o z hu0) * hdVal (Hd.o z hv0)) (10 ^ n)
      (kUV u v la lb) (la + lb + 1) ((Hd.o z hd1).rep.neg != (Hd.o z hd2).rep.neg)) :
    DW live S Q 0x800050d4#64 R M := by
  have hb' : BcHeap S M H F ((temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B) := by
    simpa only [KList, List.nil_append, List.append_assoc] using hb
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hzn := hb'.nums _ (List.mem_append_right _ List.mem_cons_self)
  have hzb : z.rep.p < 2 ^ 64 := by
    have := hzn.shape.pHi; simp only [NumObj.withRefs, heapEnd] at this; omega
  have hx : ∀ h, h ∈ hs → ∀ x, h = some x → NumAt M x.rep ∧ x.rep.p ≠ z.rep.p := by
    intro h hm x e
    have hxm : x ∈ temps hs ++ A :=
      List.mem_append_left _ (List.mem_filterMap.mpr ⟨h, hm, by rw [e]; rfl⟩)
    exact ⟨hb'.nums x (List.mem_append_left _ hxm), hb'.p_ne_split hxm⟩
  have hzv : hdVal z = 0 := by show dvalBE (z.rep.ds.take z.rep.len) = 0; rw [kz.ds, kz.len]; rfl
  have hzc : valCount z.rep = 0 := by simp only [valCount, kz.ds, kz.len]; rfl
  have zero : ∀ R', Keeps [10, 11, 13, 14, 15] R' R →
      hdVal (Hd.o z hu0) * hdVal (Hd.o z hv0) = 0 → DW live S Q 0x80005440#64 R' M := by
    intro R' kk hc
    rw [hc] at hv
    have := kz.room
    refine kara_new5440 hlive cx hk (pk.keeps kk) hb (hpm none)
      ((hown.cons (h3 := none) fun x e => nomatch e).perm (hpm none))
      ((hok.cons (h3 := none) fun x e => nomatch e).perm (hpm none))
      kz.refs (by omega) (by rw [kk.get 12]; exact h12) hNla ?_ ?_ ?_ ?_ ?_
    · simpa only [Hd.hdVal_objIn] using hm1z
    · simpa only [Hd.valCount_objIn] using hfit1
    · rw [Hd.valCount_objIn]; show n + valCount z.rep ≤ _; omega
    · simpa only [Hd.valCount_objIn] using hfit2
    · rw [Hd.hdVal_objIn]; show KFillVal _ _ (hdVal z) _ _ _ _; rw [hzv]
      simpa only [Hd.hdVal_objIn, Hd.objIn_neg] using hv
  refine kzero_800050d4 hlive hS pk.tr.u0 h12 hzb (hx _ hu0m) ?_ ?_
  · intro R1 kk1 hz0
    exact zero R1 (kk1.mono (by decide)) (by rw [hz0.val kz.ds kz.len, Nat.zero_mul])
  intro x0 e0 R1 kk1 h11
  subst e0
  refine kzero_80005104 hlive hS ((kk1.get 20).trans pk.tr.v0) ((kk1.get 12).trans h12) hzb
    (hx _ hv0m) ?_ ?_
  · intro R2 kk2 hz1
    exact zero R2 ((kk2.mono (by decide)).trans (kk1.mono (by decide)))
      (by rw [hz1.val kz.ds kz.len, Nat.mul_zero])
  intro y0 e1 R2 kk2 h13
  subst e1
  exact kara_m3call hlive ih cx hk (pk.keeps ((kk2.mono (ks' := [10, 11, 13, 14, 15]) (by decide)).trans
      (kk1.mono (by decide)))) hb hpm hown hok hu0m hv0m kz hmb ((kk2.get 11).trans h11) h13 hN hW
    hNla hn1 hm1z hfit1 hfit2 hfit3 hv

end Dc.Mach
