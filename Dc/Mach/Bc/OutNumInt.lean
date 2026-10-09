import Dc.Mach.Bc.OutNumStack

/-! # `bc_out_num` in a base other than 10: the integer digits

From `0x80007164` the loop pushes `int_part % base` on the digit stack and
divides `int_part` by `base` until it is zero (`bc_is_zero` inlined at
`0x80007184`), landing at `0x80007214` with the digits of the integer part
on the stack, most significant at the head.

- `OgLH`: the loop's state for the current `int_part` value `c`.
- `OgL c`: the loop from `0x80007184` for `c`; `og_loop` proves it for all
  `c` by strong induction, one push per `og_body`.
- `og_s5`: from `0x80007164` (after the setup) into the loop.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- The multiplication base global through the frame's changes. -/
theorem OnAt.mulBase {S G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {slots : List (Nat × Nat)} (h : OnAt S G Mt0 M R0 R sp W slots)
    (hG : ∀ a, G a → ¬ (mulBaseAddr ≤ a ∧ a < mulBaseAddr + 4)) (hab : heapEnd + W ≤ sp) :
    ldv .lw M mulBaseAddr = ldv .lw Mt0 mulBaseAddr :=
  ldv_congr .lw fun j hj => h.out _ (by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, widthOfM,
      mulBaseAddr] at hj ⊢; omega)
    (fun hg => hG _ hg ⟨by omega, by simp only [widthOfM] at hj; omega⟩)
    (by simp only [frameIn, heapEnd, widthOfM, mulBaseAddr] at hj hab ⊢; omega)

/-- An owned handle's number is none of the caller's. -/
theorem BcHeap.own_ne_caller {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk}
    {hs1 hs2 : List RH} {L : List NumObj} {y w : NumObj}
    (h : BcHeap S X M H F (RList (hs1 ++ .own y :: hs2) L)) (hw : w ∈ L) : w.rep.p ≠ y.rep.p := by
  rw [RList.own_split] at h
  exact h.p_ne_all (rBump (hs1 ++ hs2) w)
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem hw)))

/-- A one has magnitude one. -/
theorem IsOneRep.mag {o : NumRep} (hs : NumShape o) (h : IsOneRep o) : o.num.mag = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hl : o.ds.length = 1 := by rw [hs.dsLen]; omega
  rw [NumRep.num_mag]
  match e : o.ds, hl with
  | [d], _ =>
    rw [e] at h3
    simp only [List.getD_cons_zero] at h3
    subst h3
    rfl

/-- **The integer loop's state** for `int_part = c`: the five handles
(`cur_dig` a reference to `_zero_` or the last remainder), the stack from
`p` holding the digits already found below those of `c`. -/
structure OgLH (S : Nat → Prop) (X0 : Raws) (G : Nat → Prop) (I : List Nat → String → Mem → Prop)
    (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat) (H : Heap) (F : List Blk)
    (L : List NumObj) (x : NumObj) (ob : Nat) (sent : List Nat) (t : String)
    (ip fr bs mx : NumObj) (cur : RH) (cells : List Blk) (ds : List Nat) (Mc : Mem) (p c : Nat) :
    Prop where
  st : OgSt S ⟨cells ++ X0.bs, Mc⟩ G I Mt0 M R0 R sp W H F L
    [.own ip, .own fr, cur, .own bs, .own mx] [16, 24, 40, 32, 56] sent t
  curOK : RHOK L cur
  stk : OgStk X0 Mc cells ds p
  p64 : p < 2 ^ 64
  ipn : NewNum ⟨false, c, 0⟩ ip
  dig : Num.digits ob (ogIp x.rep.num).mag = Num.digits ob c ++ ds
  small : c < 10 ^ (x.rep.len + x.rep.scale)
  regs : OgRegs R x ob
  r8 : R 8 = BitVec.ofNat 64 ip.rep.p
  r19 : R 19 = BitVec.ofNat 64 bs.rep.p
  r21 : R 21 = BitVec.ofNat 64 p
  r22 : R 22 = BitVec.ofNat 64 fr.rep.p
  r24 : R 24 = BitVec.ofNat 64 mx.rep.p

/-- The loop from `0x80007184` for `int_part = c`. -/
def OgL (live S : Nat → Prop) (X0 : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x : NumObj) (ob : Nat) (cs : List Nat) (t : String)
    (fr bs mx : NumObj) (c : Nat) : Prop :=
  ∀ (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (ip : NumObj) (cur : RH)
    (cells : List Blk) (ds : List Nat) (Mc : Mem) (p : Nat),
    OgLH S X0 G I Mt0 M R0 R sp W H F L x ob (cs ++ signOut x.rep.num) t ip fr bs mx cur cells ds
      Mc p c →
    R 15 = BitVec.ofNat 64 (ip.rep.len + ip.rep.scale) → DWO live S Q t 0x80007184#64 R M

/-- After the integer loop (`0x80007214`): `int_part` zero, the integer
digits on the stack. -/
def OgK5 (live S : Nat → Prop) (X0 : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x : NumObj) (ob : Nat) (cs : List Nat) (t : String)
    (fr bs mx : NumObj) : Prop :=
  ∀ (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (ip : NumObj) (cur : RH)
    (cells : List Blk) (ds : List Nat) (Mc : Mem) (p : Nat),
    OgLH S X0 G I Mt0 M R0 R sp W H F L x ob (cs ++ signOut x.rep.num) t ip fr bs mx cur cells ds
      Mc p 0 → DWO live S Q t 0x80007214#64 R M

/-- **The inlined `bc_is_zero (int_part)`** at `0x80007184`: zero reaches
`0x80007214`, any other `0x800071a0`. -/
theorem ztest_80007184 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {o : NumRep} (hS : HeapOwn S) (hn : NumAt M o)
    (hlp : 1 ≤ o.len) (hob : R 8 = BitVec.ofNat 64 o.p)
    (h15 : R 15 = BitVec.ofNat 64 (o.len + o.scale))
    (hz : ∀ R', Keeps [13, 14, 15] R' R → o.num.mag = 0 → DW live S Q 0x80007214#64 R' M)
    (hnz : ∀ R', Keeps [13, 14, 15] R' R → o.num.mag ≠ 0 → DW live S Q 0x800071a0#64 R' M) :
    DW live S Q 0x80007184#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  num_facts hn
  have hv := hn.value
  bc_run hlive hS [hob, hv] at 0x80007190
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  refine zscan_80007190 hlive hS hn.shape.dig hn.digit (by omega) (by omega) (by omega)
    (fun R' hex kk => ?_) (fun R' hall kk => ?_) (o.len + o.scale - 1) 0 _ (by omega)
    (fun j hj => absurd hj (Nat.not_lt_zero _)) (Keeps.refl _ _)
    (by bsimp [h15]) (by bsimp [])
  · refine hnz R' ((kk.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) fun h0 => ?_
    obtain ⟨i0, hi0, hnz⟩ := hex
    rw [NumRep.num_mag] at h0
    exact hnz ((dval_eq_zero_iff _).1 h0 i0 (by rw [hn.shape.dsLen]; exact hi0))
  · exact hz R' ((kk.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
      (NumRep.mag_zero_of hn.shape.dsLen hall)

/-- **The loop's back edge** from `0x800071f0` (after `bc_divide`): the new
`int_part` read again, `s5` the pushed cell, then the zero test. -/
theorem og_back {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat} {t : String}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {fr bs mx : NumObj} {c : Nat}
    (ih : OgL live S X0 Q I G Mt0 R0 sp W L x ob cs t fr bs mx c)
    {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {ip : NumObj} {cur : RH}
    {cells : List Blk} {ds : List Nat} {Mc : Mem} {p : Nat}
    (st : OgSt S ⟨cells ++ X0.bs, Mc⟩ G I Mt0 M R0 R sp W H F L
      [.own ip, .own fr, cur, .own bs, .own mx] [16, 24, 40, 32, 56] (cs ++ signOut x.rep.num) t)
    (hcur : RHOK L cur) (sk : OgStk X0 Mc cells ds p) (hp64 : p < 2 ^ 64)
    (hip : NewNum ⟨false, c, 0⟩ ip)
    (hdig : Num.digits ob (ogIp x.rep.num).mag = Num.digits ob c ++ ds)
    (hsmall : c < 10 ^ (x.rep.len + x.rep.scale)) (rg : OgRegs R x ob)
    (h19 : R 19 = BitVec.ofNat 64 bs.rep.p) (h22 : R 22 = BitVec.ofNat 64 fr.rep.p)
    (h24 : R 24 = BitVec.ofNat 64 mx.rep.p) (h25 : R 25 = BitVec.ofNat 64 p) :
    DWO live S Q t 0x800071f0#64 R M := by
  have cx := fx.cx
  have ha := fx.ha
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have hipm : ip ∈ RList ([] ++ .own ip :: [.own fr, cur, .own bs, .own mx]) L := by
    simp [RList, rTemps, RH.tmp]
  have hipn := st.heap.nums ip hipm
  have hips := hipn.shape
  have hne := (show BcHeap S _ M H F (RList ([] ++ .own ip :: [.own fr, cur, .own bs, .own mx]) L)
    from st.heap).own_ne_caller ha.mz
  have hzs := (st.heap.nums _ (RList.mem_caller _ ha.mz)).shape
  have hG : ∀ a, G a → ¬ constBytes a := fun a hg => (cb.off a hg).2.2.1
  have hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p := by
    rw [st.on.glob hG (by omega) (by simp only [twoAddr, zeroAddr]; omega) (by omega)]
    exact ha.zero.glob
  have hz0 : (BitVec.ofNat 64 zeroAddr).toNat = zeroAddr := rfl
  have hldz : LdOK zeroAddr 8 := by simp only [LdOK, zeroAddr, tohostAddr]; omega
  have hcz : ∀ b ∈ accAddrs zeroAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.cc.consts b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  have h2 := st.on.r2
  have hw16 : ldv .ld M (sp - 176 + 16) = BitVec.ofNat 64 ip.rep.p :=
    st.words.get (hs1 := []) (os1 := []) (hs2 := [_, _, _, _]) (os2 := [24, 40, 32, 56]) rfl
  have hl := hipn.len
  have hsc := hipn.scale
  have hlp := hip.pos
  have hne' : z.rep.p ≠ ip.rep.p := hne
  have hip1 : ip.rep.p + 40 ≤ heapEnd := hips.pHi
  have hz1 : z.rep.p + 40 ≤ heapEnd := hzs.pHi
  have hip2 : heapStart ≤ ip.rep.p := hips.pLo
  have hisz := hips.size
  simp only [heapEnd, heapStart] at hip1 hz1 hip2
  bc_run hlive hS [rg.r20, hz0, hzg, h2, hw16, hl, hsc, h25, addw_ofNat] at 0x80007184
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | exact hldz | exact hcz | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  · intro he
    exfalso
    have e := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at e
    omega
  intro _
  bc_run hlive hS [rg.r20, hz0, hzg, h2, hw16, hl, hsc, h25, addw_ofNat] at 0x80007184
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | exact hldz | exact hcz | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  · intro _
    refine ih _ M H F ip cur cells ds Mc p
      ⟨st.regs (ks := [8, 14, 15, 21]) (by keeps_tac Keeps.refl _ _), hcur, sk, hp64, hip, hdig,
        hsmall, rg.keep (ks := [8, 14, 15, 21]) (by keeps_tac Keeps.refl _ _), by bsimp [],
        by bsimp [h19], by bsimp [h25], by bsimp [h22], by bsimp [h24]⟩ ?_
    bsimp []
    rw [Nat.add_comm]
  · intro hc
    exfalso
    rw [toInt_ofNat_small (k := ip.rep.scale + ip.rep.len) (by omega)] at hc
    simp at hc
    omega

/-- **One push** from `0x800071a0` for a nonzero `int_part = c`:
`bc_modulo (int_part, base, &cur_dig, 0)`, a cell for `cur_dig`'s value,
`bc_divide (int_part, base, &int_part, 0)`, back to the zero test. -/
theorem og_body {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat} {t : String}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {fr bs mx : NumObj}
    (hbs : NewNum (Num.ofInt ob) bs) {c : Nat} (hc : c ≠ 0)
    (ih : OgL live S X0 Q I G Mt0 R0 sp W L x ob cs t fr bs mx (c / ob))
    {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {ip : NumObj} {cur : RH}
    {cells : List Blk} {ds : List Nat} {Mc : Mem} {p : Nat}
    (lh : OgLH S X0 G I Mt0 M R0 R sp W H F L x ob (cs ++ signOut x.rep.num) t ip fr bs mx cur
      cells ds Mc p c) :
    DWO live S Q t 0x800071a0#64 R M := by
  have cx := fx.cx
  have ha := fx.ha
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  have st := lh.st
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have h2 := st.on.r2
  have hipm : ip ∈ RList [.own ip, .own fr, cur, .own bs, .own mx] L := by
    simp [RList, rTemps, RH.tmp]
  have hbsm : bs ∈ RList [.own ip, .own fr, cur, .own bs, .own mx] L := by
    simp [RList, rTemps, RH.tmp]
  have hips : NumShape ip.rep := (st.heap.nums ip hipm).shape
  have hbss : NumShape bs.rep := (st.heap.nums bs hbsm).shape
  have hip0 : ip.rep.scale = 0 := by rw [← NumRep.num_scale, lh.ipn.num]
  have hbs0 : bs.rep.scale = 0 := by rw [← NumRep.num_scale, hbs.num]; rfl
  have hbmag : bs.rep.num.mag = ob := by rw [hbs.num]; simp [Num.ofInt]
  have hipsz := NumRep.size_le hips lh.ipn.norm (E := x.rep.len + x.rep.scale)
    (by rw [lh.ipn.num]; exact lh.small)
  have hbssz := NumRep.size_le hbss hbs.norm (E := 10)
    (by rw [hbmag]; have := ha.obHi; omega)
  have hxsz := ha.size
  have hG : ∀ a, G a → ¬ constBytes a := fun a hg => (cb.off a hg).2.2.1
  have hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p := by
    rw [st.on.glob hG (by omega) (by simp only [twoAddr, zeroAddr]; omega) (by omega)]
    exact ha.zero.glob
  have hz8 : KZero M z (5 + 2 ^ 30) := { ha.zero.mono (by omega) with glob := hzg }
  have hrc := rCnt_le [.own ip, .own fr, cur, .own bs, .own mx] z.rep.p
  simp only [List.length_cons, List.length_nil] at hrc
  have hzk : KZero M (rBump [.own ip, .own fr, cur, .own bs, .own mx] z) (2 ^ 30) :=
    KZero.withRefs (hz8.mono (by omega))
  have hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80 :=
    (st.on.mulBase (fun a hg => (cb.off a hg).2.2.2) (by omega)).trans ha.mulBase
  bc_run hlive hS [h2, lh.r8, lh.r19] at 0x80005fd0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine hc_modH (hs1 := [.own ip, .own fr]) (h := cur) (hs2 := [.own bs, .own mx]) (o := 40)
    (u1 := ip) (u2 := bs) (z := rBump [.own ip, .own fr, cur, .own bs, .own mx] z) (k := 0) hlive
    (cx.hcFrame (by omega) rfl) (fx.hK.hcOom t) st.on.out st.heap st.own lh.curOK
    ⟨hipm, hbsm, RList.mem_caller _ ha.mz, lh.ipn.norm, hbs.norm, lh.ipn.pos, by omega, hzk, hmb,
      st.own.all⟩ (by rw [hbmag]; have := ha.obLo; omega)
    (st.words.get (hs1 := [_, _]) (os1 := [16, 24]) (hs2 := [_, _]) (os2 := [32, 56]) rfl)
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp []) (by bsimp []) (by bsimp [])
    (by bsimp []) (by bsimp []) ?_
  intro r hr R1 M1 H1 F1 y hk1 _ hb1 hown1 hres hout1
  have hob := ha.obHi
  have hob2 := ha.obLo
  have hr' : r = ⟨false, c % ob, 0⟩ := by
    rw [lh.ipn.num, hbs.num, show Num.ofInt (ob : Int) = ⟨false, ob, 0⟩ by simp [Num.ofInt],
      Num.modulo, Dc.BcModel.divmodInt c ob (by omega)] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    exact hr.symm
  have hk1' : Keeps ogKs R1 R := (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  have og1 := st.ret (hs1 := [_, _]) (hs2 := [_, _]) (os1 := [16, 24]) (os2 := [32, 56]) cx cb rfl
    hk1' (by decide) hb1 hown1 hres.slot hout1
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 176) := og1.on.r2
  bsimp []
  bc_run hlive hS [q1] at 0x8000096c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine malloc_spec hlive og1.heap.heap (n := 16) (by omega) _ (by bsimp []) (by bsimp [])
    fun R2 M2 H2 hk2 hpost => ?_
  bsimp []
  have hS1 : HeapOwn S := fun a h1 h2 => og1.heap.heap.own a h1 h2
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 176) := by rw [hk2.get 2]; bsimp [q1]
  have hM2 : ∀ a, OutHeap a → imgM M2 a = imgM M1 a := fun a ho =>
    hpost.frame a (OutHeap.not_alloc og1.heap.heap ho)
  cases hres2 : hpost.res with
  | null e1 e2 e3 =>
    iterate 2 all_goals (try bc_run hlive hS1 [e1, q2] at 0x80002bcc)
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact fx.hK.oom t _ _ (sp - 176) (by omega) (by omega) (by bsimp [q2]) fun a ho hg hf => by
      rw [hM2 a ho]
      exact og1.on.out a ho hg hf
  | block b e1 e2 e3 e4 e5 =>
    have hp' : MallocPost S M1 M2 H1 H2 16 (BitVec.ofNat 64 b.pay) := e1 ▸ hpost
    have hbl : b ∈ H2.live := by rw [e3]; exact List.mem_cons_self
    have hne := hp'.pay_ne hbl
    have fbb := hpost.inv.blk (List.mem_append_right _ hbl)
    have hblo : 2147603920 ≤ b.h := fbb.lo
    have hbhi : b.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
    have hbp : b.pay = b.h + 16 := rfl
    have hbf : b.fin = b.h + 16 + b.sz := rfl
    have hb2 := og1.heap.malloc hp'
    have hS2 : HeapOwn S := fun a h1 h2 => hb2.heap.own a h1 h2
    have hym : y ∈ RList [.own ip, .own fr, .own y, .own bs, .own mx] L := by
      simp [RList, rTemps, RH.tmp]
    have hyn := hb2.nums y hym
    have hw40 : ldv .ld M2 (sp - 176 + 40) = BitVec.ofNat 64 y.rep.p := by
      rw [ldv_congr .ld fun j hj => hM2 _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))]
      exact hres.slot
    bc_run hlive hS2 [e1, q2, hw40] at 0x800065a0
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    · intro hc0; exact absurd hc0 hne
    intro _
    bc_run hlive hS2 [e1, q2, hw40] at 0x800065a0
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine bc_num2long_spec hlive hS2 hyn hres.pos _ (by bsimp []) (by bsimp [])
      fun R3 hk3 h103 => ?_
    bsimp []
    have hal16 : b.h % 16 = 0 := fbb.al
    have hdg : c % ob < ob := Nat.mod_lt _ (by omega)
    have g10 : R3 10 = BitVec.ofNat 64 (c % ob) := by
      rw [h103, hres.num, hr', Dc.BcModel.toLong_int _ (by omega)]
      exact ofInt_natCast64 _
    have kk : Keeps [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] R3 R :=
      (hk3.mono (by decide)).trans ((by keeps_tac Keeps.refl _ _ : Keeps [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] _ _).trans
        ((hk2.mono (by decide)).trans ((by keeps_tac Keeps.refl _ _ : Keeps [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] _ _).trans
          ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))))
    have g2 : R3 2 = BitVec.ofNat 64 (sp - 176) := by rw [kk.get 2 (by decide)]; exact h2
    have g21 : R3 21 = BitVec.ofNat 64 p := by rw [kk.get 21 (by decide)]; exact lh.r21
    have g8 : R3 8 = BitVec.ofNat 64 ip.rep.p := by rw [kk.get 8 (by decide)]; exact lh.r8
    have g19 : R3 19 = BitVec.ofNat 64 bs.rep.p := by rw [kk.get 19 (by decide)]; exact lh.r19
    have g25 : R3 25 = BitVec.ofNat 64 b.pay := by rw [hk3.get 25 (by decide)]; bsimp [e1]
    have hbp2 : b.pay = b.h + 16 := rfl
    have hbf2 : b.fin = b.h + 16 + b.sz := rfl
    have hb8 : (BitVec.ofNat 64 (b.pay + 8)).toNat = b.pay + 8 := by
      rw [BitVec.toNat_ofNat]; omega
    have hb0 : (BitVec.ofNat 64 b.pay).toNat = b.pay := by
      rw [BitVec.toNat_ofNat]; omega
    bc_run hlive hS2 [g10, g21, g8, g19, g25, g2, hb8, hb0] at 0x8000589c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | (have e6 : b.pay = b.h + 16 := rfl; have e7 : b.fin = b.h + 16 + b.sz := rfl; exact acc_heap hS2 (by omega) (by omega)) | (have e6 : b.pay = b.h + 16 := rfl; have e7 : b.fin = b.h + 16 + b.sz := rfl; simp only [StOK, LdOK, tohostAddr]; omega) | skip
    obtain ⟨og2, sk2⟩ := og1.push lh.stk cx cb hp' e3 e2 e5 lh.p64 (c % ob)
    have og2r := og2.regs ((by keeps_tac Keeps.refl _ _ : Keeps [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] _ _).trans ((hk3.mono (by decide)).trans
      ((by keeps_tac Keeps.refl _ _ : Keeps [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] _ _).trans ((hk2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _ : Keeps [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] _ _)))))
    have hrc4 := rCnt_le [.own ip, .own fr, .own y, .own bs, .own mx] z.rep.p
    simp only [List.length_cons, List.length_nil] at hrc4
    have hzg4 : ldv .ld (writeLog (writeLog M2 [(b.pay, 8, BitVec.ofNat 64 (c % ob))])
        [(b.pay + 8, 8, BitVec.ofNat 64 p)]) zeroAddr = BitVec.ofNat 64 z.rep.p := by
      rw [og2.on.glob hG (by omega) (by simp only [twoAddr, zeroAddr]; omega) (by omega)]
      exact ha.zero.glob
    refine hc_divH (hs1 := []) (h := .own ip) (hs2 := [.own fr, .own y, .own bs, .own mx]) (o := 16)
      (u1 := ip) (u2 := bs) (z := rBump [.own ip, .own fr, .own y, .own bs, .own mx] z) (k := 0)
      hlive (cx.hcFrame (by omega) rfl) (fx.hK.hcOom t) og2r.on.out og2r.heap og2r.own
      ⟨lh.ipn.refs, lh.ipn.owns⟩ (by simp [RList, rTemps, RH.tmp]) (by simp [RList, rTemps, RH.tmp])
      (RList.mem_caller _ ha.mz)
      (fun _ _ h1 => absurd (IsOneRep.mag hbss h1) (by rw [hbmag]; omega)) (by omega) hzg4
      (by show z.rep.num.mag = 0; rw [ha.zero.num]; rfl) lh.ipn.pos (by rw [hbmag]; omega)
      (og2r.words.get (hs1 := []) (os1 := []) (hs2 := [_, _, _, _]) (os2 := [24, 40, 32, 56]) rfl)
      (by bsimp [g2]) (by bsimp []; try decide) (by bsimp []) (by bsimp []) (by bsimp [])
      (by bsimp []) ?_
    intro m hm R5 M5 H5 F5 y2 hk5 _ hb5 hown5 hres5 hout5
    have hm' : m = ⟨false, c / ob, 0⟩ := by
      rw [lh.ipn.num, hbs.num, show Num.ofInt (ob : Int) = ⟨false, ob, 0⟩ by simp [Num.ofInt],
        Dc.BcModel.divInt c ob (by omega)] at hm
      exact (Option.some.inj hm).symm
    have og3 := og2r.ret (hs1 := []) (hs2 := [_, _, _, _]) (os1 := []) (os2 := [24, 40, 32, 56])
      (ks := ogKs) cx cb rfl ((hk5.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) (by decide)
      hb5 hown5 hres5.slot hout5
    have kk5 : Keeps [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] R5 R :=
      (hk5.mono (by decide)).trans ((by keeps_tac Keeps.refl _ _ :
        Keeps [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] _ _).trans kk)
    refine og_back hlive fx ih og3 ⟨hres.refs, hres.owns⟩ sk2 (by omega)
      { hres5.toNewNum with num := by rw [hres5.num, hm'] } ?_
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) lh.small) (lh.regs.keep kk5)
      (by rw [kk5.get 19 (by decide)]; exact lh.r19) (by rw [kk5.get 22 (by decide)]; exact lh.r22)
      (by rw [kk5.get 24 (by decide)]; exact lh.r24)
      (by rw [hk5.get 25 (by decide)]; bsimp []; exact g25)
    rw [lh.dig, Dc.BcModel.digits_step ob (by omega) c hc, List.append_assoc]; rfl

/-- `OgLH` through register changes off the loop's registers. -/
theorem OgLH.keep {S : Nat → Prop} {X0 : Raws} {G : Nat → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x : NumObj} {ob : Nat} {sent : List Nat}
    {t : String} {ip fr bs mx : NumObj} {cur : RH} {cells : List Blk} {ds : List Nat} {Mc : Mem}
    {p c : Nat}
    (lh : OgLH S X0 G I Mt0 M R0 R sp W H F L x ob sent t ip fr bs mx cur cells ds Mc p c)
    {ks : List Nat} (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] := by
      decide) :
    OgLH S X0 G I Mt0 M R0 R' sp W H F L x ob sent t ip fr bs mx cur cells ds Mc p c := by
  have hk' : Keeps [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] R' R :=
    hk.mono hks
  exact ⟨lh.st.regs hk', lh.curOK, lh.stk, lh.p64, lh.ipn, lh.dig, lh.small, lh.regs.keep hk',
    by rw [hk'.get 8 (by decide)]; exact lh.r8, by rw [hk'.get 19 (by decide)]; exact lh.r19,
    by rw [hk'.get 21 (by decide)]; exact lh.r21, by rw [hk'.get 22 (by decide)]; exact lh.r22,
    by rw [hk'.get 24 (by decide)]; exact lh.r24⟩

/-- **The integer loop** for every `int_part`, by strong induction. -/
theorem og_loop {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat} {t : String}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {fr bs mx : NumObj}
    (hbs : NewNum (Num.ofInt ob) bs) (hk : OgK5 live S X0 Q I G Mt0 R0 sp W L x ob cs t fr bs mx) :
    ∀ c, OgL live S X0 Q I G Mt0 R0 sp W L x ob cs t fr bs mx c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
  intro R M H F ip cur cells ds Mc p lh h15
  have hob := fx.ha.obLo
  have hS : HeapOwn S := fun a h1 h2 => lh.st.heap.heap.own a h1 h2
  have hipm : ip ∈ RList [.own ip, .own fr, cur, .own bs, .own mx] L := by
    simp [RList, rTemps, RH.tmp]
  refine ztest_80007184 hlive hS (lh.st.heap.nums ip hipm) lh.ipn.pos lh.r8 h15
    (fun R' kk hz => ?_) (fun R' kk hnz => ?_)
  · have hc0 : c = 0 := by rw [lh.ipn.num] at hz; exact hz
    subst hc0
    exact hk R' M H F ip cur cells ds Mc p (lh.keep kk)
  · have hc : c ≠ 0 := by rw [lh.ipn.num] at hnz; exact hnz
    exact og_body hlive fx hbs hc (ih (c / ob) (Nat.div_lt_self (by omega) (by omega))) (lh.keep kk)

end Dc.Mach
