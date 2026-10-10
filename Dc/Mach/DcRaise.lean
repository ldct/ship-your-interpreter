import Dc.Mach.DcDiv
import Dc.Mach.Bc.RaiseEntry
import Dc.Mach.Bc.SqrtInit

/-!
# dc's exponentiation (M9)

    dc_exp (a, b, kscale, result):
      bc_init_num (result); bc_raise (a, b, result, kscale); return DC_SUCCESS;

`bc_raise` leaves in the slot a new number, the base or `_one_` with one
more reference, or the old number (`RaPost`):

- `DcDen.swap`: two handles exchanged.
- `BcConsts.SameP`: constants at the same addresses (`DcView.sameP`).
- `DcDen.raPost`, `DcAt.raNum`: the slot's handle after `bc_raise`.
- `DcAt.refs_le`, `DcAt.raArgs`: `bc_raise`'s operands from the state.
- `OpRet.of_raPost`: the operation's success from `RaPost`.
- `dc_exp_spec`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **Two handles exchanged.** -/
theorem DcDen.swap {L : List NumObj} {C : BcConsts} {G : DcG} {a b : GV} {hs : List GV} {st : St}
    (d : DcDen L C G (a :: b :: hs) st) : DcDen L C G (b :: a :: hs) st :=
  { d with
    hsDen := fun g hg => d.hsDen g (by
      simp only [List.mem_cons] at hg ⊢; rcases hg with h | h | h <;> simp [h])
    numRefs := fun x hx => by
      rw [d.numRefs x hx]; simp only [List.count_append, List.count_cons]; omega
    strRefs := fun o ho => by
      rw [d.strRefs o ho]; simp only [List.count_append, List.count_cons]; omega }

/-- Constants at the same addresses. -/
structure BcConsts.SameP (C C' : BcConsts) : Prop where
  z : C'.z.rep.p = C.z.rep.p
  o : C'.o.rep.p = C.o.rep.p
  t : C'.t.rep.p = C.t.rep.p

theorem BcConsts.SameP.refl (C : BcConsts) : C.SameP C := ⟨rfl, rfl, rfl⟩

theorem BcConsts.SameP.trans {C1 C2 C3 : BcConsts} (h1 : C1.SameP C2) (h2 : C2.SameP C3) :
    C1.SameP C3 := ⟨h2.z.trans h1.z, h2.o.trans h1.o, h2.t.trans h1.t⟩

theorem BcConsts.sameP_subst (C : BcConsts) {x x' : NumObj} (hp : x'.rep.p = x.rep.p)
    (hn : x'.rep.num = x.rep.num) : C.SameP (C.subst x x') := by
  classical
  exact ⟨(ite_rep hp hn _ _).1, (ite_rep hp hn _ _).1, (ite_rep hp hn _ _).1⟩

/-- The constants' words read the same for constants at the same addresses. -/
theorem DcView.sameP {M : Mem} {G : DcG} {C C' : BcConsts} {st : St} (v : DcView M G C st)
    (h : C.SameP C') : DcView M G C' st :=
  { v with zw := by rw [h.z]; exact v.zw, ow := by rw [h.o]; exact v.ow, tw := by rw [h.t]; exact v.tw }

/-- A handle's number has a reference. -/
theorem DcDen.refs_pos {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {x : NumObj} (d : DcDen L C G (.num x.rep.p :: hs) st) (hx : x ∈ L) : 1 ≤ x.rep.refs := by
  rw [d.numRefs x hx, count_cons_self]; omega

/-- **The slot's handle after `bc_raise`** on the ghost side: one reference
added to `y` (fresh, or a number of the heap), then the slot's old number
`xr` dropped; the handle `.num y.p` replaces `.num xr.p`. -/
theorem DcDen.raPost {L Lm Lf : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {xr y : NumObj} (d : DcDen L C G (.num xr.rep.p :: hs) st) (hd : PDist L) (hxr : xr ∈ L)
    (hadd : AddRef L y Lm) (hdrop : DropAt Lm xr.rep.p Lf) (hdf : PDist Lf)
    (hno : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (how : y.Owns) :
    ∃ C', DcDen Lf C' G (.num y.rep.p :: hs) st ∧ C.SameP C' := by
  cases hadd with
  | fresh hy1 =>
    rcases DropAt.cons_cases hdrop with ⟨hyp, hfr⟩ | ⟨L'', hd', e⟩
    · cases hfr with
      | dec h2 => omega
      | rel _ => exact ⟨C, by rw [hyp]; exact d, .refl C⟩
    · subst e
      obtain ⟨L1, L2, x, rfl, hxp, hfr⟩ := hd'
      have hx : x = xr := hd.eq (List.mem_append_right _ List.mem_cons_self) hxr hxp
      subst hx
      have hdf' : PDist ([] ++ y :: L'') := hdf
      cases hfr with
      | dec _ =>
        exact ⟨_, (d.dec hd.ne).addNum (fun z hz => hdf'.ne z hz) hy1 hno hpos how,
          C.sameP_subst rfl rfl⟩
      | rel h1 =>
        exact ⟨C, (d.rel hd.ne h1).addNum (fun z hz => hdf'.ne z hz) hy1 hno hpos how, .refl C⟩
  | @share A B c =>
    have hdm : PDist (A ++ c.withRefs (c.rep.refs + 1) :: B) :=
      hd.congr (by simp only [List.map_append, List.map_cons]; rfl)
    by_cases hcx : c.rep.p = xr.rep.p
    · have hc : c = xr := hd.eq (List.mem_append_right _ List.mem_cons_self) hxr hcx
      subst hc
      have hr1 := d.refs_pos hxr
      have hfr := DropAt.unique hdm hdrop
      cases hfr with
      | rel h => simp only [NumObj.withRefs_refs] at h; omega
      | dec _ =>
        refine ⟨C, ?_, .refl C⟩
        rw [NumObj.decRef_eq, NumObj.withRefs_withRefs, NumObj.withRefs_refs,
          show c.rep.refs + 1 - 1 = c.rep.refs by omega, NumObj.withRefs_self]
        exact d
    · have d1 := (d.bump hd.ne).swap
      obtain ⟨L1, L2, x, e, hxp, hfr⟩ := hdrop
      rw [e] at d1 hdm
      rw [← hxp] at d1
      cases hfr with
      | dec _ =>
        exact ⟨_, d1.dec hdm.ne, (C.sameP_subst (x := c) (x' := c.withRefs (c.rep.refs + 1)) rfl rfl).trans
          (BcConsts.sameP_subst _ (x := x) (x' := x.decRef) rfl rfl)⟩
      | rel h1 => exact ⟨_, d1.rel hdm.ne h1, C.sameP_subst rfl rfl⟩

/-- **The slot's handle after `bc_raise`**: the state holds `.num y.p`
instead of `.num xr.p`. -/
theorem DcAt.raNum {S : Nat → Prop} {M Mt : Mem} {H H' : Heap} {F F' : List Blk} {L Lf : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {xr y : NumObj} {ps : List Nat} {q sp W : Nat}
    {n : Num} (h : DcAt S M H F L C G (.num xr.rep.p :: hs) st) (hxr : xr ∈ L)
    (hp : RaPost S (G.raws M) M Mt H' F' L xr ps q sp W n Lf y)
    (hgl : ∀ a, DcGlob a → imgM Mt a = imgM M a) :
    ∃ C', DcAt S Mt H' F' Lf C' G (.num y.rep.p :: hs) st := by
  obtain ⟨Lm, hadd, hdrop⟩ := hp.mid
  obtain ⟨C', d', hsp⟩ := h.den.raPost h.heap.pdist hxr hadd hdrop hp.heap.pdist hp.norm hp.pos
    hp.owns
  have hag : ∀ a, InBlocks G.blocks a → imgM Mt a = imgM M a := fun a ⟨c, hc, ha⟩ =>
    hp.heap.raw.img c hc a ha
  exact ⟨C', hp.heap.subRaw (fun c hc => hc) (fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm), h.nodup,
    (h.view.frame hag hgl).sameP hsp, d', h.glob, h.col⟩

/-- A number of the state has at most `7856806 + hs.length + 2 ^ 29` references. -/
theorem DcAt.refs_le {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {x : NumObj} (hx : x ∈ L) : x.rep.refs ≤ 7856806 + hs.length + 2 ^ 29 := by
  rw [h.den.numRefs x hx]
  have := h.count_le (.num x.rep.p)
  have : C.cnt x.rep.p ≤ 3 := by
    unfold BcConsts.cnt; exact Nat.le_trans (List.countP_le_length) (by simp)
  have := Nat.le_trans (List.count_le_length (a := x.rep.p) (l := G.lk)) h.den.lkLen
  omega

/-- **Two numbers of the state as `bc_raise`'s operands**, with the
constants `_zero_` and `_one_`. -/
theorem DcAt.raArgs {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {x1 x2 : NumObj} (h1 : x1 ∈ L) (h2 : x2 ∈ L) (hhs : hs.length ≤ 2 ^ 20) {k : Nat}
    (hsz : ((raExp x2).natAbs + 1) * (x1.rep.len + x1.rep.scale + 1) + k < 2 ^ 24)
    (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80) : RaArgs S M L x1 x2 C.z C.o k :=
  ⟨h1, h2, h.den.mz, h.den.mo, h.den.norm x1 h1, h.den.pos x1 h1, h.den.pos x2 h2, hsz,
    by have := h.refs_le h1; omega, (h.kzero hhs).mono (by omega), h.view.ow, h.den.ov,
    h.den.norm _ h.den.mo, h.den.pos _ h.den.mo, by have := h.refs_le h.den.mo; omega, hmb,
    h.den.owns, h.errFile⟩

/-- **An operation's success from `bc_raise`'s result** `y` in the slot. -/
theorem OpRet.of_raPost {S : Nat → Prop} {M M2 Mt : Mem} {H H3 : Heap} {F F3 : List Blk}
    {L Lf : List NumObj} {x y : NumObj} {C2 : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb : Nat} {na nb n : Num} {f : Nat → Num → Num → Option Num} {ps : List Nat}
    {sp q N sp' W lk : Nat}
    (hd2 : DcAt S M2 H F L C2 G (.num x.rep.p :: .num pa :: .num pb :: hs) st) (hx : x ∈ L)
    (hp : RaPost S (G.raws M2) M2 Mt H3 F3 L x ps q sp' W n Lf y)
    (hval : f st.scale na nb = some n) (hw1 : sp' ≤ sp) (hw2 : sp - N ≤ sp' - W)
    (hab : heapEnd ≤ sp' - W) (hq : sp ≤ q)
    (hout0 : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp N a → imgM M2 a = imgM M a) :
    ∃ C3, ∀ R' : Nat → BitVec 64, R' 10 = 0#64 →
      OpRet S M Mt H3 F3 Lf C3 G G hs st pa pb na nb f R' sp q N lk y.rep.p n := by
  simp only [heapEnd] at hab
  obtain ⟨C3, hd3⟩ := hd2.raNum hx hp fun a ha =>
    hp.out a ha.outHeap (fun hs => by have := ha.lt; simp only [heapStart, slotBytes] at this hs; omega)
      (fun hf => by have := ha.lt; simp only [heapStart, frameIn] at this hf; omega)
  obtain ⟨k, hk⟩ := hp.res
  exact ⟨C3, fun R' ha0 => ⟨ha0, hd3, hval, ⟨y.withRefs k, hk, rfl, hp.num⟩, hp.slot, rfl, by omega,
    fun a ho _ hf hs => by
      rw [hp.out a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]
      exact hout0 a ho hs hf⟩⟩

/-- **`dc_exp`** at `0x80002578`: `bc_init_num (result)`, then
`bc_raise (a, b, result, kscale)`; it always succeeds. -/
theorem dc_exp_spec {live S : Nat → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    DcOp live S 0x80002578 (48 + (512 + rmStack (2 ^ 30))) 0
      (fun k a b => (b.toLong.natAbs + 1) * (a.wid + 1) + k < 2 ^ 24)
      (fun k a b => some (Num.raise a b k).1) := by
  intro Q t M H F L C G hs st pa pb na nb R sp q hin hok hret _ hoom
  have hsf := hin.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := hin.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hqs := hin.slotHi
  have hql := hin.slot.lo; have hqh := hin.slot.hi; have hqa := hin.slot.al
  have hS : HeapOwn S := fun a e1 e2 => hin.h.heap.heap.own a e1 e2
  have h2 := hin.r2; have h10 := hin.r10; have h11 := hin.r11; have h12 := hin.r12
  have h13 := hin.r13
  have hzw := hin.h.view.zw
  bc_run hlive hS [h2, h10, h11, h12, h13, word_sub48] at 0x800049bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine op48_init hlive hin (by omega)
    (fun a ha => by simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)])
    ⟨?_, ?_, ?_, ?_, ?_⟩ _ (by bsimp []) (by bsimp [])
    fun R2 M2 L1 L2 x C2 x1 x2 hk2 hd2 hw2 hxz hx1 e1p e1n hx2 e2p e2n hout2 fr2 => ?_
  · ld48
  · ld48
  · ld48
  · ld48
  · ld48
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have m0 := fr2.w0; have m8 := fr2.w8
  have hmb2 : ldv .lw M2 mulBaseAddr = BitVec.ofNat 64 80 :=
    (hin.mb.transport (M' := M2) fun a e1 e2 => by
      have ⟨o1, _, o3⟩ := mulBase_off e1 e2
      exact hout2 _ o1 (fun hs => by simp only [slotBytes, heapStart] at hs o3; omega)
        fun hf => by simp only [frameIn, heapStart] at hf o3; omega).word
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk2.get 2 (by decide)]; bsimp []
  have r8 : R2 8 = BitVec.ofNat 64 q := by rw [hk2.get 8 (by decide)]; bsimp []
  have r9 : R2 9 = BitVec.ofNat 64 pa := by rw [hk2.get 9 (by decide)]; bsimp []
  have hS2 : HeapOwn S := fun a e1 e2 => hd2.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS2 [q2, r8, r9, m0, m8] at 0x8000660c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  -- the operands' sizes, `_zero_` in the slot
  have hsz : ((raExp x2).natAbs + 1) * (x1.rep.len + x1.rep.scale + 1) + st.scale < 2 ^ 24 := by
    have w1 := NumRep.len_le_wid (hd2.heap.nums x1 hx1).shape (hd2.den.norm x1 hx1)
    have := Nat.mul_le_mul_left ((raExp x2).natAbs + 1)
      (show x1.rep.len + x1.rep.scale + 1 ≤ na.wid + 1 by rw [← e1n]; omega)
    simp only [raExp, e2n] at this ⊢
    omega
  clear hok
  have hxm : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hz0 : ldv .ld M2 zeroAddr = ldv .ld M zeroAddr :=
    ldv_congr .ld fun j hj => hout2 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr,
        bcFreeAddr, widthOfM, dc_addrs] at hj ⊢; omega)
      (fun hs => by simp only [slotBytes, widthOfM, dc_addrs] at hs hj; omega)
      (fun hf => by simp only [frameIn, widthOfM, dc_addrs] at hf hj; omega)
  have hz2 : BitVec.ofNat 64 C2.z.rep.p = BitVec.ofNat 64 C.z.rep.p := by
    rw [← hd2.view.zw, hz0, hzw]
  have hzp : x.rep.p = C2.z.rep.p := by
    have hn0 := hd2.heap.nums C2.z hd2.den.mz
    have hnz := hin.h.heap.nums C.z hin.h.den.mz
    have a1 := hn0.shape.pLo; have a2 := hn0.shape.pHi
    have b1 := hnz.shape.pLo; have b2 := hnz.shape.pHi
    simp only [heapStart, heapEnd] at a1 a2 b1 b2
    rw [hxz]
    bv_nat at hz2
    omega
  have hr2 := hd2.zero_refs hxm hzp
  have hxz' : x = C2.z := hd2.heap.pdist.eq hxm hd2.den.mz hzp
  have hr1 : 1 ≤ x1.rep.refs := by
    have d := hd2.den.swap
    rw [← e1p] at d
    exact d.refs_pos hx1
  refine bc_raise_spec hlive (W := 512 + rmStack (2 ^ 30)) (k := st.scale) (z := C2.z) (o := C2.o)
    ⟨hsf.within (m := 48) (n := 512 + rmStack (2 ^ 30)) (by omega) (by decide),
      by simp only [heapEnd]; omega, by omega, by simp only [stderrAddr]; omega, hin.mb.own,
      fun a ha => hd2.glob a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega),
      by bsimp [q2], by bsimp [],
      ⟨hin.slot, fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega),
        .inr (by omega)⟩,
      .inr (by simp only [dc_addrs]; omega), .inr (by simp only [dc_addrs]; omega)⟩
    (hd2.raArgs hx1 hx2 (by have := hin.hsLen; simp only [List.length_cons]; omega) hsz hmb2)
    ⟨hxm, by omega, hw2, fun _ => hr2, fun _ => hr2, fun _ _ => by
      rw [hxz']; exact ⟨hd2.den.zv, hd2.den.norm _ hd2.den.mz, hd2.den.pos _ hd2.den.mz⟩⟩
    hd2.heap hr1
    ⟨fun R3 Mt H3 F3 Lf y hk3 hp => ?_, fun R3 Mt sp' o1 o2 hr2' hout => ?_⟩
    (by bsimp [e1p]) (by bsimp [e2p]) (by bsimp []) (by bsimp [])
  · -- the result
    have frT := fr2.transport (by omega) fun a e1 e2 =>
      hp.out a (above_sp hab2 e1).1 (fun hs => by simp only [slotBytes] at hs; omega)
        ((above_sp hab2 e1).2.2 _)
    have q3 : R3 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
    have hS3 : HeapOwn S := fun a e1 e2 => hp.heap.heap.own a e1 e2
    bsimp []
    bc_run hlive hS3 [q3, frT.w24, frT.w32, frT.w40]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    · exact hin.al
    obtain ⟨C3, hr⟩ := OpRet.of_raPost (f := fun k a b => some (Num.raise a b k).1) (na := na)
      (nb := nb) (N := 48 + (512 + rmStack (2 ^ 30))) (lk := 0) hd2 hxm hp
      (by rw [← e1n, ← e2n]) (by omega) (by omega) (by simp only [heapEnd]; omega) hqs
      fun a ho hs hf => hout2 a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
    exact hret _ Mt H3 F3 Lf C3 G y.rep.p _
      (Keeps.restore (by rw [h2]; congr 1; omega) (Keeps.upd _ (by decide) (Keeps.restore rfl
        (Keeps.restore rfl (by keeps_tac ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono
          (by decide)).trans (by keeps_tac Keeps.refl _ _)))))))))
      (hr _ (by bsimp []))
  · bc_run hlive hS2 [] at 0x80001e74
    refine hoom R3 Mt sp' ⟨by omega, by omega, hr2', fun a ho hg hf hs => ?_⟩
    rw [hout a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]
    exact hout2 a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

end Dc.Mach
