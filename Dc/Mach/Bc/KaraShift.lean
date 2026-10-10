import Dc.Mach.Bc.KaraTail
import Dc.Mach.Bc.KaraVal

/-!
# `_bc_rec_mul`'s Karatsuba step: the shifted adds into the product

- `KTailRegs`, `KSlots`: the handles' registers and slots from the
  recursive multiplications to the frees.
- `kara_m2`: `_bc_shift_addsub (*prod, m2, n, d1->n_sign != d2->n_sign)` at
  `0x8000519c`, then the frees.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- The handles' registers from the subtractions to the frees, `s9` at
`_bc_Free_list`, `s1` at the product slot, `s0 = n`. -/
structure KTailRegs (z : NumObj) (hu1 hu0 hv1 hv0 hd1 hd2 : Hd) (q n : Nat)
    (R : Nat → BitVec 64) : Prop where
  u1 : R 24 = BitVec.ofNat 64 (Hd.p z hu1)
  u0 : R 19 = BitVec.ofNat 64 (Hd.p z hu0)
  v1 : R 27 = BitVec.ofNat 64 (Hd.p z hv1)
  v0 : R 20 = BitVec.ofNat 64 (Hd.p z hv0)
  d1 : R 21 = BitVec.ofNat 64 (Hd.p z hd1)
  d2 : R 23 = BitVec.ofNat 64 (Hd.p z hd2)
  fl : R 25 = BitVec.ofNat 64 bcFreeAddr
  q : R 9 = BitVec.ofNat 64 q
  n : R 8 = BitVec.ofNat 64 n

theorem KTailRegs.keeps {z : NumObj} {hu1 hu0 hv1 hv0 hd1 hd2 : Hd} {q n : Nat}
    {R R' : Nat → BitVec 64} (t : KTailRegs z hu1 hu0 hv1 hv0 hd1 hd2 q n R) {ks : List Nat}
    (hk : Keeps ks R' R)
    (hs : ∀ r ∈ [8, 9, 19, 20, 21, 23, 24, 25, 27], r ∉ ks := by decide) :
    KTailRegs z hu1 hu0 hv1 hv0 hd1 hd2 q n R' :=
  ⟨(hk _ (hs 24 (by simp))).trans t.u1, (hk _ (hs 19 (by simp))).trans t.u0,
    (hk _ (hs 27 (by simp))).trans t.v1, (hk _ (hs 20 (by simp))).trans t.v0,
    (hk _ (hs 21 (by simp))).trans t.d1, (hk _ (hs 23 (by simp))).trans t.d2,
    (hk _ (hs 25 (by simp))).trans t.fl, (hk _ (hs 9 (by simp))).trans t.q,
    (hk _ (hs 8 (by simp))).trans t.n⟩

/-- The slots of `m1`, `m2`, `m3`. -/
structure KSlots (z : NumObj) (hm1 hm2 hm3 : Hd) (sp : Nat) (M : Mem) : Prop where
  m1 : ldv .ld M (sp - 192 + 40) = BitVec.ofNat 64 (Hd.p z hm1)
  m2 : ldv .ld M (sp - 192 + 48) = BitVec.ofNat 64 (Hd.p z hm2)
  m3 : ldv .ld M (sp - 192 + 56) = BitVec.ofNat 64 (Hd.p z hm3)

/-- Writes inside the heap keep the step's state off the heap. -/
theorem KAt.heapOnly {S : Nat → Prop} {M0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    (cx : RmCtx S R0 sp q W) (st : KAt S M0 M R0 R sp q W) {P : Nat → Prop}
    (hm : MemOnly P M' M) (hP : ∀ a, P a → heapStart ≤ a ∧ a < heapEnd) :
    KAt S M0 M' R0 R sp q W := by
  have hab := cx.above; have hsh := cx.frame.hi; have hW := cx.big
  simp only [heapEnd] at hab
  have hfr : ∀ a, sp - 192 ≤ a → a < sp → imgM M' a = imgM M a := fun a h1 h2 =>
    hm a fun h => by have := hP a h; simp only [heapStart, heapEnd] at this; omega
  exact ⟨st.rm.mem (st.rm.saved.transport (lo := 128) (top := 192) (hag := fun a h1 h2 =>
      hfr a (by omega) (by omega)))
      fun a ha _ _ => hm a fun h => ha.1 (hP a h),
    st.saved2.transport (lo := 88) (top := 160) (hag := fun a h1 h2 => hfr a (by omega) (by omega))⟩

/-- A word off the heap survives writes inside the heap. -/
theorem MemOnly.ldv_off {M M' : Mem} {P : Nat → Prop} (hm : MemOnly P M' M)
    (hP : ∀ a, P a → heapStart ≤ a ∧ a < heapEnd) {a : Nat}
    (ha : a + 8 ≤ heapStart ∨ heapEnd ≤ a) : ldv .ld M' a = ldv .ld M a :=
  ldv_congr .ld fun j hj => hm _ fun h => by
    have := hP _ h; simp only [widthOfM] at hj; omega

theorem KSlots.heapOnly {z : NumObj} {hm1 hm2 hm3 : Hd} {sp : Nat} {M M' : Mem}
    (sl : KSlots z hm1 hm2 hm3 sp M) {P : Nat → Prop} (hm : MemOnly P M' M)
    (hP : ∀ a, P a → heapStart ≤ a ∧ a < heapEnd) (hsp : heapEnd + 192 ≤ sp) :
    KSlots z hm1 hm2 hm3 sp M' :=
  ⟨(hm.ldv_off hP (by omega)).trans sl.m1, (hm.ldv_off hP (by omega)).trans sl.m2,
    (hm.ldv_off hP (by omega)).trans sl.m3⟩

/-- The product of the operands' digits. -/
abbrev kUV (u v : NumRep) (la lb : Nat) : Nat := dvalBE (u.ds.take la) * dvalBE (v.ds.take lb)

/-- `snez` of the difference of two sign words: whether the signs differ. -/
theorem snez_signs (a b : Bool) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (signWord a - signWord b))) =
      BitVec.ofNat 64 (if (a != b) = true then 1 else 0) := by
  cases a <;> cases b <;> decide

/-- A handle's value: its object's first `len` digits. -/
abbrev hdVal (o : NumObj) : Nat := dvalBE (o.rep.ds.take o.rep.len)

/-- After a call that wrote only heap bytes and kept the saved registers:
the product's digits now `ds`, then the frees. -/
theorem kara_ret_frees {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M M2 : Mem} {R0 R R2 : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {y : NumObj} {ds : List Nat} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S X Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    (st : KAt S M0 M R0 R sp q W) {hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2 : Hd}
    (hb2 : BcHeap S X M2 H F
      (withDs y ds :: KList [] [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] A B z))
    (hok : HdOK [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2]) (hz : 1 ≤ z.rep.refs)
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false) (hyv : y.rep.val = y.rep.ptr)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0)
    (hval : dvalBE ds = kUV u v la lb)
    (hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay)
    (tr : KTailRegs z hu1 hu0 hv1 hv0 hd1 hd2 q n R) (sl : KSlots z hm1 hm2 hm3 sp M)
    {P : Nat → Prop} (hm : MemOnly P M2 M) (hP : ∀ a, P a → heapStart ≤ a ∧ a < heapEnd)
    (kk : Keeps [1, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17, 28] R2 R) :
    DW live S Q 0x800051c4#64 R2 M2 := by
  have hW := cx.big
  have hab := cx.above
  have hqs := cx.slot
  have q2 := hqs.hi; have q3 := hqs.lo
  have hq0 := cx.slotOut q ⟨Nat.le_refl _, by omega⟩
  have hq7 := cx.slotOut (q + 7) ⟨by omega, by omega⟩
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hq0 hq7
  have tr2 := tr.keeps kk
  have st2 := st.heapOnly cx hm hP
  have sl2 := sl.heapOnly hm hP (by simp only [heapEnd] at hab ⊢; omega)
  exact kara_frees hlive cx hk ⟨st2.rm.keeps (kk.mono (by decide)) (kk.get 2), st2.saved2⟩ hb2
    hok hz ⟨hyo, hyr, hyn, hyv, hyl, hys, hval⟩
    ((hm.ldv_off hP (by simp only [heapStart, heapEnd]; omega)).trans hq)
    tr2.u1 tr2.u0 tr2.v1 tr2.v0 tr2.d1 tr2.d2 tr2.fl sl2.m1 sl2.m2 sl2.m3

/-- **`m2` shifted in** at `0x8000519c` (added, or subtracted when `d1` and
`d2` differ in sign), then the frees. -/
theorem kara_m2 {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj} {z : NumObj}
    {u v : NumRep} {y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S X Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    (st : KAt S M0 M R0 R sp q W) {hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2 : Hd}
    (hb : BcHeap S X M H F (y :: KList [] [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] A B z))
    (hok : HdOK [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2]) (hz : 1 ≤ z.rep.refs)
    (hyo : y.Owns) (hyr : y.rep.refs = 1) (hyn : y.rep.neg = false) (hyv : y.rep.val = y.rep.ptr)
    (hyl : y.rep.len = la + lb + 1) (hys : y.rep.scale = 0)
    (hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay)
    (tr : KTailRegs z hu1 hu0 hv1 hv0 hd1 hd2 q n R) (sl : KSlots z hm1 hm2 hm3 sp M)
    (hfit : n + valCount (Hd.objIn [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] z hm2).rep ≤
      la + lb + 1)
    (hsub : ((Hd.objIn [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] z hd1).rep.neg !=
        (Hd.objIn [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] z hd2).rep.neg) = true →
      dvalBE y.rep.ds = kUV u v la lb +
        hdVal (Hd.objIn [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] z hm2) * 10 ^ n)
    (hadd : ((Hd.objIn [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] z hd1).rep.neg !=
        (Hd.objIn [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] z hd2).rep.neg) = false →
      dvalBE y.rep.ds +
        hdVal (Hd.objIn [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] z hm2) * 10 ^ n =
          kUV u v la lb)
    (hUV : kUV u v la lb < 10 ^ (la + lb + 1))
    (hwp : 1 ≤ (Hd.objIn [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] z hm2).rep.len) :
    DW live S Q 0x8000519c#64 R M := by
  generalize hhs : [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] = hs at hb hok hfit hsub hadd hwp
  generalize hw2 : Hd.objIn hs z hm2 = w2 at hfit hsub hadd hwp
  generalize ho1 : Hd.objIn hs z hd1 = o1 at hsub hadd
  generalize ho2 : Hd.objIn hs z hd2 = o2 at hsub hadd
  have hm : ∀ h, h ∈ [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] → Hd.objIn hs z h ∈ y :: KList [] hs A B z :=
    fun h hh => List.mem_cons_of_mem _ (Hd.objIn_mem (hhs ▸ hh) _ _ _ _)
  have hw2L : w2 ∈ KList [] hs A B z := hw2 ▸ Hd.objIn_mem (hhs ▸ by simp) _ _ _ _
  have hn2 := hb.nums w2 (List.mem_cons_of_mem _ hw2L)
  have hn1 := hb.nums o1 (ho1 ▸ hm hd1 (by simp))
  have hn3 := hb.nums o2 (ho2 ▸ hm hd2 (by simp))
  have hny := hb.nums y List.mem_cons_self
  have hyp : y.rep.p = y.sb.pay := (hb.blocks y List.mem_cons_self).sPay
  have p2 : w2.rep.p = Hd.p z hm2 := by rw [← hw2, Hd.objIn_p]
  have p1 : o1.rep.p = Hd.p z hd1 := by rw [← ho1, Hd.objIn_p]
  have p3 : o2.rep.p = Hd.p z hd2 := by rw [← ho2, Hd.objIn_p]
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hqs := cx.slot
  have hal := cx.al
  have e2v : ldv .ld M (Hd.p z hm2 + 32) = BitVec.ofNat 64 w2.rep.val := by rw [← p2]; exact hn2.value
  have e2l : ldv .lw M (Hd.p z hm2 + 4) = BitVec.ofNat 64 w2.rep.len := by rw [← p2]; exact hn2.len
  have e1s : ldv .lw M (Hd.p z hd1) = signWord o1.rep.neg := by rw [← p1]; exact hn1.sign
  have e3s : ldv .lw M (Hd.p z hd2) = signWord o2.rep.neg := by rw [← p3]; exact hn3.sign
  num_facts hn2
  num_facts hn1
  num_facts hn3
  have h2 := st.rm.r2
  have q2 := hqs.hi; have q3 := hqs.lo
  bc_run hlive hS [h2, sl.m2, tr.d1, tr.d2, tr.q, tr.n, e2v, e2l, e1s, e3s, hq] at 0x800051c0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hqs.acc | skip
  rw [snez_signs]
  have yv1 := hny.shape.vLo; have yv2 := hny.shape.vHi
  simp only [heapStart, heapEnd] at yv1 yv2
  have ys := hny.shape; have ws := hn2.shape
  have hyd : y.rep.ds.length = y.rep.len + y.rep.scale := ys.dsLen
  have hwl : w2.rep.len ≤ w2.rep.ds.length := by have := ws.dsLen; omega
  apply st_800051c0 hlive
  refine bc_shift_addsub_spec (w := w2) (shift := n) (sub := (o1.rep.neg != o2.rep.neg)) hlive hyo
    (by bsimp []) ⟨hw2L, hwp, by rw [hyl, hys]; exact hfit, ?_⟩ hb (by bsimp [hyp])
    (by bsimp []) (by bsimp []) (by bsimp []) rfl ?_
  · cases hsb : (o1.rep.neg != o2.rep.neg)
    · exact noCarry_add hyd ys.dig (by rw [hyl, hys]; exact hfit) hwl hwp ws.dig (by
        rw [hyl, hys, Nat.add_zero, hadd hsb]; exact hUV)
    · exact noCarry_sub hyd ys.dig (by rw [hyl, hys]; exact hfit) hwl hwp ws.dig (by
        rw [hsub hsb]; exact Nat.le_add_left _ _)
  intro R2 M2 hsh hb2
  subst hhs
  refine kara_ret_frees hlive cx hk st hb2 hok hz hyo hyr hyn hyv hyl hys ?_ hq tr sl hsh.mem
    (fun a ha => by simp only [accBytes, heapStart, heapEnd] at ha ⊢; omega)
    ((hsh.keeps.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
  have hfit' : n + valCount w2.rep ≤ y.rep.len + y.rep.scale := by rw [hyl, hys]; exact hfit
  cases hsb : (o1.rep.neg != o2.rep.neg)
  · rw [shiftDs_add hyd ys.dig hfit' hwl hwp ws.dig (by
      exact noCarry_add hyd ys.dig hfit' hwl hwp ws.dig (by
        rw [hyl, hys, Nat.add_zero, hadd hsb]; exact hUV))]
    exact hadd hsb
  · have := shiftDs_sub hyd ys.dig hfit' hwl hwp ws.dig (by
      exact noCarry_sub hyd ys.dig hfit' hwl hwp ws.dig (by
        rw [hsub hsb]; exact Nat.le_add_left _ _))
    rw [hsub hsb] at this; simp only [hdVal] at this; omega

/-- `slli a, b, 1` of a small word. -/
theorem kshl1 (n : Nat) : BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The nine handles in the order of the frees. -/
abbrev kHs (hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2 : Hd) : List Hd :=
  [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2]

/-- From the recursive multiplications to the frees: the step's frame, the
handles' registers and slots, the product in its slot. -/
structure KMid (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W n : Nat)
    (z : NumObj) (hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 : Hd) (y : NumObj) : Prop where
  st : KAt S M0 M R0 R sp q W
  tr : KTailRegs z hu1 hu0 hv1 hv0 hd1 hd2 q n R
  sl : KSlots z hm1 hm2 hm3 sp M
  hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay

/-- `KMid` through a call that wrote only heap bytes and kept the saved
registers. -/
theorem KMid.after {S : Nat → Prop} {M0 M M2 : Mem} {R0 R R2 : Nat → BitVec 64}
    {sp q W n : Nat} {z : NumObj} {hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 : Hd} {y : NumObj}
    (cx : RmCtx S R0 sp q W) (km : KMid S M0 M R0 R sp q W n z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 y)
    {P : Nat → Prop} (hm : MemOnly P M2 M) (hP : ∀ a, P a → heapStart ≤ a ∧ a < heapEnd)
    (kk : Keeps [1, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17, 28] R2 R) (ds : List Nat) :
    KMid S M0 M2 R0 R2 sp q W n z hu1 hu0 hv1 hv0 hd1 hd2 hm1 hm2 hm3 (withDs y ds) := by
  have hW := cx.big
  have hab := cx.above
  have hqs := cx.slot
  have q2 := hqs.hi; have q3 := hqs.lo
  have hq0 := cx.slotOut q ⟨Nat.le_refl _, by omega⟩
  have hq7 := cx.slotOut (q + 7) ⟨by omega, by omega⟩
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hq0 hq7
  have st2 := km.st.heapOnly cx hm hP
  exact ⟨⟨st2.rm.keeps (kk.mono (by decide)) (kk.get 2), st2.saved2⟩, km.tr.keeps kk,
    km.sl.heapOnly hm hP (by simp only [heapEnd] at hab ⊢; omega),
    (hm.ldv_off hP (by simp only [heapStart, heapEnd]; omega)).trans km.hq⟩

end Dc.Mach
