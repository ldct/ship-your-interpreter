import Dc.Mach.Bc.KaraHalves
import Dc.Mach.Bc.KaraArith

/-!
# `_bc_rec_mul`'s Karatsuba step from the recursion hypothesis

`kara_case`: the Karatsuba case `RmKara` at a level of `la + lb` digits from
the contract `RmIH` for every smaller level (`3 (la + lb) / 4 + 1` digits).
`kara_halves` reaches the `m1` stage; the halves' values (`HalfV`) and the
differences' (`DiffV`) supply `kara_m1`'s obligations: `KSubArgs`, `KM3Spec`,
`KM1Spec` and `KDiffSpec` with the Karatsuba identity (`kfill_val`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- Inside `_bc_rec_mul` the globals (`_zero_`, `mul_base_digits`) are the
entry memory's. -/
theorem RmAt.glob {S : Nat → Prop} {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    (cx : RmCtx S R0 sp q W) (st : RmAt S M0 M R0 R sp q W) : GlobAgree M M0 := fun a h => by
  have hab := cx.above; have hg := cx.slotGlob
  simp only [heapEnd, zeroAddr, mulBaseAddr] at hab hg h
  exact st.out a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
    (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)

/-- A scratch run and the step's spills keep the globals. -/
theorem GlobAgree.of_touch {M M' : Mem} {R0 : Nat → BitVec 64} {fr : Nat}
    (hfr : 2147603920 ≤ fr) (h : MemOnly KTouch M' (kSpillMem M R0 fr)) : GlobAgree M' M :=
  fun a ha => by
    simp only [mulBaseAddr, zeroAddr] at ha
    have ht : ¬ KTouch a := by
      simp only [KTouch, bcFreeBytes, bcFreeAddr, freeListAddr, heapStart, heapEnd]; omega
    exact (h a ht).trans (kSpillMem_off M R0 (by omega))

theorem zeroCount_le : ∀ hs : List Hd, zeroCount hs ≤ hs.length
  | [] => Nat.le_refl 0
  | none :: hs => by simp only [zeroCount_none, List.length_cons]; have := zeroCount_le hs; omega
  | some _ :: hs => by simp only [zeroCount_some, List.length_cons]; have := zeroCount_le hs; omega

/-- A trimmed untrimmed half that is not `_zero_`: a view of `w`'s buffer
with one reference. -/
theorem KRaw.trim_some {w : NumObj} {off k : Nat} {h : Hd} (r : KRaw w off k h) :
    ∀ x, h.trim h.lz = some x → x.rep.refs = 1 ∧ x.db = w.db := by
  cases r with
  | view sb => intro x e; cases e; exact ⟨rfl, rfl⟩
  | zero _ => intro x e; simp at e

/-- The object a handle names is a number of the shape of the heap's. -/
theorem Hd.shape_o {z : NumObj} {h : Hd} {hs : List Hd} (hz : NumShape z.rep)
    (hx : NumShape (Hd.objIn hs z h).rep) : NumShape (Hd.o z h).rep := by
  cases h with
  | none => exact hz
  | some x => exact hx

/-- `k` digits of `w` from `off`, split at `n`: the high part times
`10 ^ n` plus the low part. -/
theorem dvalBE_split (ds : List Nat) {l n : Nat} (hl : l ≤ ds.length) :
    dvalBE (ds.take l) = dvalBE ((ds.drop 0).take (l - n)) * 10 ^ n +
      dvalBE ((ds.drop (l - n)).take (l - (l - n))) := by
  have e : ds.take l = ds.take (l - n) ++ (ds.drop (l - n)).take (l - (l - n)) := by
    rw [← List.take_add]; congr 1; omega
  rw [e, dvalBE_append, List.drop_zero]
  rcases Nat.lt_or_ge l n with h | h
  · rw [show l - n = 0 by omega, List.take_zero, dvalBE_nil, Nat.zero_mul, Nat.zero_mul]
  · rw [show ((ds.drop (l - n)).take (l - (l - n))).length = n by
      simp only [List.length_take, List.length_drop]; omega]

/-- **A trimmed half's value**: `V`, the value of its `k` digits. -/
structure HalfV (z : NumObj) (h : Hd) (k V : Nat) : Prop where
  shape : NumShape (Hd.o z h).rep
  val : hdVal (Hd.o z h) = V
  dv : dval (Hd.o z h).rep.ds = V
  lt : V < 10 ^ k
  len : (Hd.o z h).rep.len ≤ max 1 k
  pos : 1 ≤ k → 1 ≤ (Hd.o z h).rep.len
  lenS : ∀ x, h = some x → x.rep.len ≤ k
  norm : (Hd.o z h).rep.Norm
  neg : (Hd.o z h).rep.neg = false
  scale : (Hd.o z h).rep.scale = 0

theorem KHalf.halfV {z w : NumObj} {h : Hd} {off k : Nat}
    (kh : KHalf z h ((w.rep.ds.drop off).take k)) (hs : NumShape (Hd.o z h).rep)
    (hw : NumShape w.rep) (hfit : off + k ≤ w.rep.len + w.rep.scale) :
    HalfV z h k (dvalBE ((w.rep.ds.drop off).take k)) := by
  have hl : ((w.rep.ds.drop off).take k).length = k := by
    simp only [List.length_take, List.length_drop, hw.dsLen]; omega
  have hdig : Digits ((w.rep.ds.drop off).take k) := fun d hd =>
    hw.dig d (List.mem_of_mem_drop (List.mem_of_mem_take hd))
  have hdv : dval (Hd.o z h).rep.ds = dvalBE ((w.rep.ds.drop off).take k) := congrArg Dc.Num.mag kh.num
  refine ⟨hs, (hdVal_eq_dval hs kh.scale).trans hdv, hdv, ?_, ?_, fun hk => kh.pos ?_,
    fun x e => ?_, kh.norm, kh.neg, kh.scale⟩
  · have := dval_lt hdig; rw [hl, dval_eq_dvalBE] at this; exact this
  · have := kh.len; rwa [hl] at this
  · intro e; rw [e] at hl; simp at hl; omega
  · have := kh.lenS x e; rwa [hl] at this

/-- The arguments of `bc_sub` on two halves. -/
theorem HalfV.subArgs {z : NumObj} {h1 h2 : Hd} {k1 k2 V1 V2 : Nat} (a : HalfV z h1 k1 V1)
    (b : HalfV z h2 k2 V2) (hk : k1 + k2 < 2 ^ 30) (hne : 1 ≤ k1 ∨ 1 ≤ k2) : KSubArgs z h1 h2 where
  n1 := a.norm
  n2 := b.norm
  size := by have := a.len; have := b.len; rw [a.scale, b.scale]; omega
  neg1 := a.neg
  neg2 := b.neg
  ne := by
    rcases hne with h | h
    · exact .inl (a.pos h)
    · exact .inr (b.pos h)

/-- **A difference of two halves**: at most `m` digits when both are below
`10 ^ m`; its value is their distance, its sign the larger's. -/
structure DiffV (y : NumObj) (V1 V2 m : Nat) : Prop where
  len : y.rep.len ≤ m
  val : hdVal y + min V1 V2 = max V1 V2
  negT : y.rep.neg = true → V1 ≤ V2
  negF : y.rep.neg = false → V2 ≤ V1

theorem HalfV.diff {z : NumObj} {h1 h2 : Hd} {k1 k2 V1 V2 : Nat} (a : HalfV z h1 k1 V1)
    (b : HalfV z h2 k2 V2) {y : NumObj}
    (hy : y.rep.num = (Hd.o z h1).rep.subM (Hd.o z h2).rep 0) (hn : y.rep.Norm)
    (hs : NumShape y.rep) {m : Nat} (hm : 1 ≤ m) (h1m : V1 < 10 ^ m) (h2m : V2 < 10 ^ m) :
    DiffV y V1 V2 m := by
  have sv := NumRep.subM_val a.shape b.shape a.scale b.scale a.neg b.neg a.norm b.norm
  rw [← hy, a.dv, b.dv] at sv
  have hsc : y.rep.scale = 0 := sv.scale
  have hval : hdVal y = dval y.rep.ds := hdVal_eq_dval hs hsc
  have hmag : dval y.rep.ds = y.rep.num.mag := rfl
  have hm' := sv.mag
  rw [← hmag] at hm'
  refine ⟨NumRep.len_le_of_lt hs hsc hn hm (by omega), by rw [hval]; exact hm',
    fun e => sv.negT e, fun e => sv.negF e⟩

/-- **The Karatsuba case** at a level of `la + lb` digits, from `_bc_rec_mul`'s
contract for the levels below. -/
theorem kara_case {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S X Q N)
    {M0 : Mem} {R0 : Nat → BitVec 64} {sp q W la lb : Nat} {A B : List NumObj}
    {z uo vo : NumObj}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S X Q R0 M0 (A ++ z :: B) uo.rep vo.rep la lb q sp W)
    (kz : KZero M0 z (4 * (la + lb) + 8)) (hW : rmStack (la + lb) ≤ W)
    (ha : RmArgs M0 (A ++ z :: B) uo vo la lb) (hN : 3 * (la + lb) / 4 + 1 ≤ N) :
    RmKara live S X Q R0 M0 (A ++ z :: B) uo vo la lb q sp W := by
  intro R M H F st kp h80 hla hlb h0 h22 h20 h21 h18 h9 hb
  have hga := RmAt.glob cx st
  have kzM := hga.zero kz
  have hzS : NumShape z.rep := (hb.nums z (List.mem_append_right _ List.mem_cons_self)).shape
  have huS : NumShape uo.rep := (hb.nums uo ha.mu).shape
  have hvS : NumShape vo.rep := (hb.nums vo ha.mv).shape
  have hfu := ha.ul; have hfv := ha.vl; have hsz := ha.size
  have hAB : ∀ x, x ∈ A ++ z :: B → 20 ≤ x.rep.len + x.rep.scale → x ∈ A ++ B := by
    intro x hx hl
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with h | h | h
    · exact .inl h
    · subst h; have := kzM.len; have := kzM.scale; omega
    · exact .inr h
  have h80' : ¬ la + lb < 80 := by omega
  have hst : ∀ s, s ≤ 3 * (la + lb) / 4 + 1 → rmStack s + 192 ≤ W := fun s hs =>
    Nat.le_trans (rmStack_child h80' hs) hW
  have hW368 : 368 ≤ W := by
    have := rmDepth_step h80'; simp only [rmStack] at hW; omega
  have hab := cx.above; simp only [heapEnd] at hab
  refine kara_halves hlive cx hk st kp hb (hAB uo ha.mu (by omega)) (hAB vo ha.mv (by omega))
    hfu hfv hsz hla hlb (kzM.mono (by omega)) h0 h22 h20 h21 h18 h9 ?_
  intro R' M' H' F' hu1 hu0 hv1 hv0 kh
  generalize hn : (max la lb + 1) / 2 = n at kh
  have hn1 : 1 ≤ n := by omega
  -- the four trimmed halves
  have hmem : ∀ t ∈ [hv0.trim hv0.lz, hv1.trim hv1.lz, hu0.trim hu0.lz, hu1.trim hu1.lz],
      NumShape (Hd.o z t).rep := fun t ht =>
    Hd.shape_o hzS (kh.heap.nums _ (Hd.objIn_mem ht [] A B z)).shape
  have U1 := (kh.u1.trim kzM huS (by omega)).halfV (hmem _ (by simp)) huS (by omega)
  have U0 := (kh.u0.trim kzM huS (by omega)).halfV (hmem _ (by simp)) huS (by omega)
  have V1 := (kh.v1.trim kzM hvS (by omega)).halfV (hmem _ (by simp)) hvS (by omega)
  have V0 := (kh.v0.trim kzM hvS (by omega)).halfV (hmem _ (by simp)) hvS (by omega)
  -- the bounds the children need
  have hmU : 1 ≤ la - (la - n) := by omega
  have hmV : 1 ≤ lb - (lb - n) := by omega
  have hC : (la - (la - n)) + (lb - (lb - n)) ≤ 3 * (la + lb) / 4 + 1 := by omega
  have hCf : n + (la - (la - n)) + (lb - (lb - n)) ≤ la + lb + 1 := by omega
  have hU1m : dvalBE ((uo.rep.ds.drop 0).take (la - n)) < 10 ^ (la - (la - n)) :=
    Nat.lt_of_lt_of_le U1.lt (Nat.pow_le_pow_right (by decide) (by omega))
  have hV1m : dvalBE ((vo.rep.ds.drop 0).take (lb - n)) < 10 ^ (lb - (lb - n)) :=
    Nat.lt_of_lt_of_le V1.lt (Nat.pow_le_pow_right (by decide) (by omega))
  have sa1 := U1.subArgs U0 (by omega) (.inr hmU)
  have sa2 := V0.subArgs V1 (by omega) (.inl hmV)
  have m3s : KM3Spec z (hu0.trim hu0.lz) (hv0.trim hv0.lz) n la lb N W :=
    ⟨by have := U0.len; have := V0.len; omega, by have := U0.len; have := V0.len; omega,
      hst _ (by have := U0.len; have := V0.len; omega), U0.pos hmU, V0.pos hmV⟩
  have m1s : ∀ x1 x2, hu1.trim hu1.lz = some x1 → hv1.trim hv1.lz = some x2 →
      1 ≤ x1.rep.len → 1 ≤ x2.rep.len →
      KM1Spec z (hu1.trim hu1.lz) (hv1.trim hv1.lz) n la lb N W := by
    intro x1 x2 e1 e2 p1 p2
    have l1 := U1.lenS x1 e1; have l2 := V1.lenS x2 e2
    rw [e1, e2]
    exact ⟨by show 2 * n + x1.rep.len + x2.rep.len ≤ _; omega,
      by show x1.rep.len + x2.rep.len ≤ _; omega,
      hst _ (by show x1.rep.len + x2.rep.len ≤ _; omega)⟩
  have dsp : KDiffSpec z (hu1.trim hu1.lz) (hu0.trim hu0.lz) (hv1.trim hv1.lz) (hv0.trim hv0.lz)
      uo.rep vo.rep n la lb N W := by
    refine ⟨fun y1 y2 hd1 hd2 n1 n2 s1 s2 => ?_, fun y1 y2 hd1 hd2 n1 n2 s1 s2 => ?_⟩
    · have D1 := U1.diff U0 hd1 n1 s1 hmU hU1m U0.lt
      have D2 := V0.diff V1 hd2 n2 s2 hmV V0.lt hV1m
      have := D1.len; have := D2.len
      exact ⟨by omega, by omega, hst _ (by omega)⟩
    · have D1 := U1.diff U0 hd1 n1 s1 hmU hU1m U0.lt
      have D2 := V0.diff V1 hd2 n2 s2 hmV V0.lt hV1m
      rw [U1.val, U0.val, V1.val, V0.val]
      show KFillVal _ _ _ _ (dvalBE (uo.rep.ds.take la) * dvalBE (vo.rep.ds.take lb)) _ _
      rw [dvalBE_split uo.rep.ds (n := n) (by rw [huS.dsLen]; omega),
        dvalBE_split vo.rep.ds (n := n) (by rw [hvS.dsLen]; omega)]
      exact kfill_val hla hlb hn.symm U1.lt U0.lt V1.lt V0.lt D1.val D2.val D1.negT D1.negF
        D2.negT D2.negF
  -- `_zero_` and `mul_base_digits` at the `m1` stage
  have hgm : GlobAgree M' M0 := (GlobAgree.of_touch (by omega) kh.touch).trans hga
  have kz' : KZero M' z (zeroCount [hv0.trim hv0.lz, hv1.trim hv1.lz, hu0.trim hu0.lz,
      hu1.trim hu1.lz] + 2 + (4 * (la + lb + 2 - n) + 8)) :=
    (hgm.zero kz).mono (by have := zeroCount_le [hv0.trim hv0.lz, hv1.trim hv1.lz,
      hu0.trim hu0.lz, hu1.trim hu1.lz]; simp only [List.length_cons, List.length_nil] at this; omega)
  have hown : HdOwned A B z [hv0.trim hv0.lz, hv1.trim hv1.lz, hu0.trim hu0.lz, hu1.trim hu1.lz] := by
    intro x hx
    have ou := hb.views.owner ha.mu
    have ov := hb.views.owner ha.mv
    obtain ⟨wu, hwu, hou, heu⟩ := ou
    obtain ⟨wv, hwv, hov, hev⟩ := ov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with e | e | e | e
    · exact .inr ⟨wv, hwv, hov, hev.trans (kh.v0.trim_some x e.symm).2.symm⟩
    · exact .inr ⟨wv, hwv, hov, hev.trans (kh.v1.trim_some x e.symm).2.symm⟩
    · exact .inr ⟨wu, hwu, hou, heu.trans (kh.u0.trim_some x e.symm).2.symm⟩
    · exact .inr ⟨wu, hwu, hou, heu.trans (kh.u1.trim_some x e.symm).2.symm⟩
  have hok : HdOK [hv0.trim hv0.lz, hv1.trim hv1.lz, hu0.trim hu0.lz, hu1.trim hu1.lz] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with e | e | e | e
    · exact (kh.v0.trim_some x e.symm).1
    · exact (kh.v1.trim_some x e.symm).1
    · exact (kh.u0.trim_some x e.symm).1
    · exact (kh.u1.trim_some x e.symm).1
  exact kara_m1 hlive ih cx hk kh.pk kh.heap (List.reverse_perm [hu1.trim hu1.lz, hu0.trim hu0.lz, hv1.trim hv1.lz, hv0.trim hv0.lz]) hown hok kz' kh.r17
    (hgm.mulBase ha.mulBase) hW368 hsz hn1 sa1 sa2 dsp m3s m1s

/-- **`_bc_rec_mul`'s contract at every size**: by strong induction on the
digit count, the Karatsuba case's children taking at most
`3 (la + lb) / 4 + 1` digits. -/
theorem rm_spec {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    ∀ N, RmIH live S X Q N := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N IH =>
    intro R0 M sp q W la lb A B z uo vo H F hN hW kz cx hk ha hb h10 h11 h12 h13 h14
    refine rm_entry hlive cx hk ?_ ha hb h10 h11 h12 h13 h14
    intro R M' H' F' st kp h80
    exact kara_case hlive (IH (3 * (la + lb) / 4 + 1) (by omega)) cx hk kz hW ha (Nat.le_refl _)
      R M' H' F' st kp h80

end Dc.Mach
