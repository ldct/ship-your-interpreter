import Dc.Mach.Bc.RaiseSquare

/-!
# `bc_raise` from its entry (`0x8000660c`)

    660c warn on num2's scale; exponent = bc_num2long (num2)
    681c exponent 0: error for a nonzero integer part; result = _one_
    6648 rscale = MIN (scale1 · exponent, MAX (scale, scale1)) (positive) or
         scale (negative, the exponent negated); the loops (`ra_loops`)
    6740 / 68cc the result from `temp` (`ra_end2`) or from `power` (`ra_endC`)

- `RaSlot.transport`: the result slot through the frame's writes.
- `RaMode`: the sign flag `s8` and `rscale` against `Num.raise`.
- `ra_zero`/`ra_err`/`ra_one`: a zero exponent; `ra_body`/`ra_rscale`/`ra_go`:
  a nonzero one; `ra_num`, `ra_warn` and `bc_raise_spec`: the entry.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The result slot through writes off the heap's complement and the frame. -/
theorem RaSlot.transport {S : Nat → Prop} {R0 : Nat → BitVec 64} {Mt0 M : Mem} {sp W q : Nat}
    {L : List NumObj} {x1 x2 z o xr : NumObj} (cx : RaCtx S R0 sp W q)
    (hs : RaSlot Mt0 L x1 x2 z o xr q)
    (hag : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    RaSlot M L x1 x2 z o xr q :=
  { hs with
    wr := by
      rw [ldv_congr .ld fun j hj => hag _ (cx.slot.out _ (by simp only [widthOfM] at hj; omega))
        (by have := cx.slot.apart; simp only [frameIn, widthOfM] at hj ⊢; omega)]
      exact hs.wr }

/-- `bc_raise`'s sign flag `s8` and `rscale` for the exponent `raExp x2`
(nonzero, magnitude `u`). -/
structure RaMode (x1 x2 : NumObj) (k u rs nf : Nat) : Prop where
  abs : u = (raExp x2).natAbs
  cases : (nf = 0 ∧ 0 < raExp x2 ∧ rs = min (x1.rep.scale * u) (max k x1.rep.scale)) ∨
    (nf = 1 ∧ raExp x2 < 0 ∧ rs = k)

/-- `_one_` has one integer digit and no fraction. -/
theorem one_size {o : NumRep} (hs : NumShape o) (hn : o.Norm) (h1 : o.num = Num.one) :
    o.len + o.scale ≤ 1 := by
  have hsc : o.scale = 0 := by rw [← NumRep.num_scale, h1]; rfl
  have := NumRep.size_le hs hn (E := 1) (by rw [h1]; decide)
  omega

/-- **The result from `temp`** at `0x80006740`: the second loop's exit. -/
theorem ra_end2 {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k u rs nf P : Nat} {H : Heap} {F : List Blk}
    {A B : List NumObj} {x1 x2 z o xr Pw T : NumObj}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u)
    (hK : RaK live S X Q t R0 Mt0 (A ++ x1 :: B) xr [x1.rep.p, o.rep.p] q sp W (Num.raise x1.rep.num x2.rep.num k).1)
    (ha : RaArgs S Mt0 (A ++ x1 :: B) x1 x2 z o k) (hs0 : RaSlot Mt0 (A ++ x1 :: B) x1 x2 z o xr q)
    (hm : RaMode x1 x2 k u rs nf)
    (st : RaP2 S X Mt0 M R0 R sp W q H F A B x1 Pw (some T) P u 0 rs nf) :
    DW live S (DQ live S Q t) 0x80006740#64 R M := by
  have cx := env.cx
  ra_facts cx
  have hsf := cx.frame
  have hb0 := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb0.heap.own a h1 h2
  have hb : BcHeap S X M H F (T :: Pw :: (A ++ x1 :: B)) := by
    have := hb0.kperm (List.Perm.swap (some T) (some Pw) []) (fun _ h => nomatch h) (fun x hx => by
      rcases List.mem_cons.mp hx with h | h
      · cases h; exact .inl st.tm.owns
      · rw [List.mem_singleton] at h; cases h; exact .inl st.pw.owns)
    simpa [KList, zeroCount, temps, NumObj.withRefs_self] using this
  have hs := hs0.transport cx st.ra.out
  have hTn : T.rep.num = Num.powRaise x1.rep.num u := st.tm.num
  have hTs : T.rep.scale = x1.rep.scale * u := by
    rw [← NumRep.num_scale, hTn, Dc.BcModel.powRaise_scale, NumRep.num_scale]
  have hk24 : k < 2 ^ 24 := by have := ha.size; omega
  have hx1sz := (hb.nums x1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha.m1))).shape.size
  rcases hm.cases with ⟨rfl, hpos, hrs⟩ | ⟨rfl, hneg, hrs⟩
  · bc_run hlive hS [st.r24] at 0x8000688c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine ra_pos2 hlive cx hK hs ha.owns st.ra hb (st.t1 T rfl) st.pw1 st.tm.owns st.pw.owns
      st.tm.norm st.tm.len (by rw [hTs, hrs]; omega) (by rw [hrs]; omega) ?_ st.r20 st.r22 st.w8
    have hne : ¬ (raExp x2 == 0) = true := by simp; omega
    have hlt : ¬ (raExp x2 < 0) := by omega
    simp only [Num.raise, raExp] at hne hlt ⊢
    rw [if_neg hne, if_neg hlt, ← hm.abs, ← hTn, NumRep.num_neg, NumRep.num_mag, NumRep.num_scale,
      hTs, hrs]
    rfl
  · bc_run hlive hS [st.r24] at 0x80006744
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hom := ha.mo
    have hos := one_size (hb.nums o (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hom))).shape
      ha.oneNorm ha.oneNum
    have hTm : T ∈ T :: Pw :: (A ++ x1 :: B) := List.mem_cons_self
    have hx1m : x1 ∈ T :: Pw :: (A ++ x1 :: B) :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha.m1)
    have hTz : T.rep.len + T.rep.scale ≤ u * (x1.rep.len + x1.rep.scale) + 1 :=
      st.tm.size (hb.nums T hTm).shape (hb.nums x1 hx1m).shape rfl (by have := env.u1; omega)
    have hLu : u * (x1.rep.len + x1.rep.scale) < 2 ^ 24 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_succ _))
        (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ u)) env.size)
    refine ra_neg2 hlive cx hK ha hs st.ra hb (st.t1 T rfl) st.pw1 st.tm.owns st.pw.owns ?_
      (by omega) ?_ st.r20 (by rw [st.r22, hrs]) st.w8
    · intro h0
      refine ⟨?_, hneg⟩
      rw [hTn, Dc.BcModel.powRaise_mag] at h0
      exact (Nat.pow_eq_zero.mp h0).1
    · have hne : ¬ (raExp x2 == 0) = true := by simp; omega
      simp only [Num.raise, raExp] at hne hneg ⊢
      rw [if_neg hne, if_pos hneg, ← hm.abs, ← hTn]

/-- **The result from `power`** at `0x800068cc` (`u = 2^i`): `temp` and
`power` one number `w` of the heap `A' ++ w :: B'`. -/
theorem ra_endW {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k u rs nf i : Nat} {H H0 : Heap}
    {F F0 : List Blk} {A B A' B' : List NumObj} {x1 x2 z o xr w : NumObj} {hP : Hd}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u)
    (hK : RaK live S X Q t R0 Mt0 (A ++ x1 :: B) xr [x1.rep.p, o.rep.p] q sp W (Num.raise x1.rep.num x2.rep.num k).1)
    (ha : RaArgs S Mt0 (A ++ x1 :: B) x1 x2 z o k) (hs0 : RaSlot Mt0 (A ++ x1 :: B) x1 x2 z o xr q)
    (hb0 : BcHeap S X Mt0 H0 F0 (A ++ x1 :: B)) (hm : RaMode x1 x2 k u rs nf)
    (st : RaC S X Mt0 M R0 R sp W q H F A B x1 hP i rs nf)
    (hKL : KList [] (Hd.cp hP) A B x1 = A' ++ w :: B') (hwp : w.rep.p = Hd.p x1 hP)
    (hw : RaPow x1.rep.num u w) (hw2 : 2 ≤ w.rep.refs)
    (hsame : xr.inK x1 (zeroCount (Hd.cp hP)) = w → 3 ≤ w.rep.refs)
    (hadd : nf = 0 → AddRef (A ++ x1 :: B) ((w.cutTo rs).withRefs (w.rep.refs - 1))
      (A' ++ (w.cutTo rs).withRefs (w.rep.refs - 1) :: B'))
    (hsrc : nf = 0 → w.rep.refs - 1 = 1 ∨ w.rep.p ∈ [x1.rep.p, o.rep.p])
    (hL0 : nf = 1 → (3 ≤ w.rep.refs ∧ A ++ x1 :: B = A' ++ w.withRefs (w.rep.refs - 2) :: B') ∨
      (w.rep.refs = 2 ∧ A ++ x1 :: B = A' ++ B')) :
    DW live S (DQ live S Q t) 0x800068cc#64 R M := by
  have cx := env.cx
  ra_facts cx
  have hsf := cx.frame
  have hb : BcHeap S X M H F (A' ++ w :: B') := hKL ▸ st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hs := hs0.transport cx st.ra.out
  have hcs := env.cst.transport cx st.ra.out
  have hown : ∀ y ∈ A' ++ w :: B', y.Owns := by
    rw [← hKL]
    exact KList.owns (Hd.cp_owns st.pow.owns) env.owns
  have hmem : ∀ y ∈ A ++ x1 :: B, y.inK x1 (zeroCount (Hd.cp hP)) ∈ A' ++ w :: B' :=
    fun y hy => hKL ▸ NumObj.inK_memK (Hd.cp hP) hy
  have hxsm := hmem xr hs.mr
  obtain ⟨L1, L2, hL⟩ := List.append_of_mem hxsm
  obtain ⟨r, hr, hr1, hr2⟩ := xr.inK_rep x1 (zeroCount (Hd.cp hP))
  have hxsr : 1 ≤ (xr.inK x1 (zeroCount (Hd.cp hP))).rep.refs := by rw [hr]; have := hs.rr; exact Nat.le_trans this hr1
  have hxsp := xr.inK_p x1 (zeroCount (Hd.cp hP))
  have hxr_r : (xr.inK x1 (zeroCount (Hd.cp hP))).rep.refs = r := by rw [hr]
  have hbL : BcHeap S X M H F (L1 ++ xr.inK x1 (zeroCount (Hd.cp hP)) :: L2) := hL ▸ hb
  have hwn : w.rep.num = Num.powRaise x1.rep.num u := hw.num
  have hws : w.rep.scale = x1.rep.scale * u := by
    rw [← NumRep.num_scale, hwn, Dc.BcModel.powRaise_scale, NumRep.num_scale]
  have hk24 : k < 2 ^ 24 := by have := ha.size; omega
  have hx1sz := (hb0.nums x1 ha.m1).shape.size
  have h20 : ∀ R' : Nat → BitVec 64, R' 20 = R 18 → R' 20 = BitVec.ofNat 64 w.rep.p := fun R' e => by
    rw [e, st.r18, hwp]
  rcases hm.cases with ⟨rfl, hpos, hrs⟩ | ⟨rfl, hneg, hrs⟩
  · have hadd0 := hadd rfl
    have hsrc0 := hsrc rfl
    bc_run hlive hS [st.r24] at 0x80006890
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine ra_posPow2 hlive cx hK (st.ra.regsA (ks := [20]) (by keeps_tac Keeps.refl _ _))
      (by bsimp [st.r21]) hb hown hL.symm
      ⟨hxsr, by rw [hs.wr, hxsp], fun _ hxo y hy => BcHeap.owner_db_ne hbL
        hxo hy (hown y (by rw [hL]; exact List.mem_append_left _ hy))⟩ hxsp hw2 hsame
      hw.norm hw.len (by rw [hws, hrs]; omega) (by rw [hrs]; omega) hadd0 hsrc0 ?_
      (h20 _ (by bsimp [])) (by bsimp [st.r22]) (by rw [st.w8, hwp])
    have hne : ¬ (raExp x2 == 0) = true := by simp; omega
    have hlt : ¬ (raExp x2 < 0) := by omega
    simp only [Num.raise, raExp] at hne hlt ⊢
    rw [if_neg hne, if_neg hlt, ← hm.abs, ← hwn, NumRep.num_neg, NumRep.num_mag, NumRep.num_scale,
      hws, hrs]
    rfl
  · have hL00 := hL0 rfl
    bc_run hlive hS [st.r24] at 0x800068d4
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hom := hmem o ha.mo
    have hzm := hmem z ha.mz
    have hos := one_size (hb.nums _ hom).shape (by
      obtain ⟨r', e, -, -⟩ := o.inK_rep x1 (zeroCount (Hd.cp hP)); rw [e]; exact ha.oneNorm) (by
      rw [NumObj.inK_num]; exact ha.oneNum)
    have hwz : w.rep.len + w.rep.scale ≤ u * (x1.rep.len + x1.rep.scale) + 1 :=
      hw.size (hb.nums w (List.mem_append_right _ List.mem_cons_self)).shape (hb0.nums x1 ha.m1).shape
        rfl (by have := env.u1; omega)
    have hLu : u * (x1.rep.len + x1.rep.scale) < 2 ^ 24 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_succ _))
        (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ u)) env.size)
    have hzk := KZero.inK (k := 0) x1 (zeroCount (Hd.cp hP)) (hcs.zero.mono (by have := Hd.cp_zero hP; omega))
    refine ra_negPow2 (k := k) hlive cx hK (st.ra.regsA (ks := [20]) (by keeps_tac Keeps.refl _ _))
      (by bsimp [st.r21]) hb hown hL.symm hxsr hxsp (by rw [hs.wr]) hs.mr hs.rr (ha.owns _ hs.mr)
      ?_ hom (by rw [NumObj.inK_num]; exact ha.oneNum) (by rw [NumObj.inK_len]; exact ha.oneLen)
      (by rw [hcs.one, NumObj.inK_p]) hzm (by rw [NumRep.num_mag, hzk.ds]; rfl)
      hzk.glob ?_ (by omega) hw2 hsame hL00 ?_ (by bsimp [st.r18, hwp]) (by bsimp [st.r22, hrs])
    · intro h0
      rw [hwn, Dc.BcModel.powRaise_mag] at h0
      exact hs.zr (Nat.pow_eq_zero.mp h0).1 hneg
    · intro h1
      constructor
      · intro e
        have hp : o.rep.p = xr.rep.p := by rw [← NumObj.inK_p o x1 (zeroCount (Hd.cp hP)), e, NumObj.inK_p]
        have := hb0.eq_of_p ha.mo hs.mr hp
        have := hs.oneRef this.symm; omega
      · intro e
        have hp : z.rep.p = xr.rep.p := by rw [← NumObj.inK_p z x1 (zeroCount (Hd.cp hP)), e, NumObj.inK_p]
        have := hb0.eq_of_p ha.mz hs.mr hp
        have := hs.zeroRef this.symm; omega
    · have hne : ¬ (raExp x2 == 0) = true := by simp; omega
      simp only [Num.raise, raExp] at hne hneg ⊢
      rw [if_neg hne, if_pos hneg, ← hm.abs, ← hwn]

/-- **The result for `u = 2^i`** at `0x800068cc`: `power` a new number (two
references) or `num1` itself (`i = 0`). -/
theorem ra_endC {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k u rs nf i : Nat} {H H0 : Heap}
    {F F0 : List Blk} {A B : List NumObj} {x1 x2 z o xr : NumObj} {hP : Hd}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u)
    (hK : RaK live S X Q t R0 Mt0 (A ++ x1 :: B) xr [x1.rep.p, o.rep.p] q sp W (Num.raise x1.rep.num x2.rep.num k).1)
    (ha : RaArgs S Mt0 (A ++ x1 :: B) x1 x2 z o k) (hs0 : RaSlot Mt0 (A ++ x1 :: B) x1 x2 z o xr q)
    (hb0 : BcHeap S X Mt0 H0 F0 (A ++ x1 :: B)) (hm : RaMode x1 x2 k u rs nf)
    (st : RaC S X Mt0 M R0 R sp W q H F A B x1 hP i rs nf) (hui : u = 2 ^ i) :
    DW live S (DQ live S Q t) 0x800068cc#64 R M := by
  cases hP with
  | some P =>
    have hb := st.heap
    simp only [KList, Hd.cp, temps, zeroCount, List.filterMap_cons, List.filterMap_nil, id,
      List.nil_append, Nat.add_zero, NumObj.withRefs_self, List.singleton_append] at hb
    refine ra_endW (A' := []) (w := P.withRefs 2) (B' := A ++ x1 :: B) hlive env hK ha hs0 hb0 hm st
      (by simp [KList, Hd.cp, temps, zeroCount, NumObj.withRefs_self]) rfl
      (by have := st.pow.withRefs 2; rwa [← hui] at this) (by simp) ?_ ?_
      (fun _ => .inl rfl) ?_
    · intro e
      have hp : (P.withRefs 2).rep.p = xr.rep.p := by
        rw [← e, NumObj.inK_p]
      exact absurd hp (hb.p_ne hs0.mr)
    · intro _
      simp only [List.nil_append, NumObj.cutTo_withRefs, NumObj.withRefs_withRefs]
      exact AddRef.fresh rfl
    · intro _
      exact .inr ⟨rfl, rfl⟩
  | none =>
    have hi := st.base rfl
    subst hi
    have hu1 : u = 1 := by rw [hui]
    have hr1 := env.r1
    refine ra_endW (A' := A) (w := x1.withRefs (x1.rep.refs + 2)) (B' := B) hlive env hK ha hs0 hb0
      hm st (by simp [KList, Hd.cp, temps, zeroCount]) rfl
      (by have := st.pow.withRefs (x1.rep.refs + 2); rwa [← hui] at this) (by simp)
      (fun _ => by simp; omega) ?_ (fun _ => .inr List.mem_cons_self) ?_
    · intro h0
      rcases hm.cases with ⟨_, _, hrs⟩ | ⟨h1, _⟩
      · have hrs' : rs = x1.rep.scale := by rw [hrs, hu1]; omega
        have hc : (x1.withRefs (x1.rep.refs + 2)).cutTo rs = x1.withRefs (x1.rep.refs + 2) := by
          unfold NumObj.cutTo; rw [if_neg (by simp only [hrs']; exact Nat.lt_irrefl _)]
        rw [hc, NumObj.withRefs_withRefs, NumObj.withRefs_refs,
          show x1.rep.refs + 2 - 1 = x1.rep.refs + 1 by omega]
        exact AddRef.share
      · omega
    · intro _
      refine .inl ⟨by simp; omega, ?_⟩
      rw [NumObj.withRefs_withRefs, NumObj.withRefs_refs, Nat.add_sub_cancel, NumObj.withRefs_self]

/-! ## A zero exponent -/

/-- `_one_`'s global through writes off the heap's complement and the frame. -/
theorem RaArgs.oneAt {S : Nat → Prop} {R0 : Nat → BitVec 64} {Mt0 M : Mem} {sp W q k : Nat}
    {L : List NumObj} {x1 x2 z o : NumObj} (cx : RaCtx S R0 sp W q)
    (ha : RaArgs S Mt0 L x1 x2 z o k)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    ldv .ld M oneAddr = BitVec.ofNat 64 o.rep.p := by
  have hab := cx.above
  simp only [heapEnd] at hab
  rw [ldv_congr .ld fun j hj => hout _ (constBytes_out (by
    simp only [widthOfM, constBytes, twoAddr, zeroAddr, oneAddr] at hj ⊢; omega))
    (by simp only [frameIn, widthOfM, oneAddr, zeroAddr] at hj ⊢; omega)]
  exact ha.one

/-- The stderr stream through writes off the heap's complement and the frame. -/
theorem RaArgs.fdAt {S : Nat → Prop} {R0 : Nat → BitVec 64} {Mt0 M : Mem} {sp W q k : Nat}
    {L : List NumObj} {x1 x2 z o : NumObj} (cx : RaCtx S R0 sp W q)
    (ha : RaArgs S Mt0 L x1 x2 z o k)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    FdAt S M stderrAddr 2 := by
  have hfar := cx.far
  simp only [stderrAddr] at hfar
  exact ha.fd.transport fun j hj => hout _
    (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, stderrAddr]; omega)
    (by simp only [frameIn, stderrAddr]; omega)


/-- The last restore of the zero exponent's epilogue (`0x80006870`). -/
theorem ra_oneEpi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} (cx : RaCtx S R0 sp W q) (hS : HeapOwn S)
    (h23 : ldv .ld M (sp - 96 + 24) = R0 23) (h2 : R 2 = BitVec.ofNat 64 (sp - 96))
    (hkp : Keeps raAll R R0) (h1 : R 1 = R0 1) (h8 : R 8 = R0 8) (h18 : R 18 = R0 18)
    (h22 : R 22 = R0 22) (h9 : R 9 = R0 9) (h20 : R 20 = R0 20) (h21 : R 21 = R0 21)
    (h24 : R 24 = R0 24) (hk : ∀ R', Keeps binClob R' R0 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x80006870#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hal := cx.al
  bc_run hlive hS [h2, h23, h1]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (Keeps.unwind (all := raAll) (saved := [1, 2, 8, 9, 18, 20, 21, 22, 23, 24]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp))
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, h2, h1, h8, h18, h22, h9, h20, h21, h24]
  all_goals (try (congr 1; omega))

/-- **`*result = _one_` with one more reference** from `0x80006848` (after
`bc_free_num (result)`), then the epilogue of the prologue's registers. -/
theorem ra_oneRet {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {A B : List NumObj} {y : NumObj} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S X M H F (A ++ y :: B)) (hone : ldv .ld M oneAddr = BitVec.ofNat 64 y.rep.p)
    (hr : y.rep.refs + 1 < 2 ^ 31)
    (sv : SavedWords M (sp - 96) raSlots0 R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 96))
    (hkp : Keeps raAll R R0) (h9 : R 9 = R0 9) (h20 : R 20 = R0 20) (h21 : R 21 = R0 21)
    (h24 : R 24 = R0 24) (h23 : R 23 = BitVec.ofNat 64 q)
    (hk : ∀ R' M', Keeps binClob R' R0 →
      BcHeap S X M' H F (A ++ y.withRefs (y.rep.refs + 1) :: B) →
      ldv .ld M' q = BitVec.ofNat 64 y.rep.p →
      (∀ a, OutHeap a → ¬ slotBytes q a → imgM M' a = imgM M a) → DW live S Q (R0 1) R' M') :
    DW live S Q 0x80006848#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hal := cx.al
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have h1o := cx.slotOne
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hym : y ∈ A ++ y :: B := List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums y hym
  num_facts hn
  have hrf := hn.refs
  have hcst : ∀ b ∈ accAddrs oneAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have hsx : BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (BitVec.ofNat 64 y.rep.refs + 1#64)) = BitVec.ofNat 64 (y.rep.refs + 1) := by
    rw [show BitVec.ofNat 64 y.rep.refs + 1#64 = BitVec.ofNat 64 (y.rep.refs + 1) by
      bv_omega]
    exact sxw_ofNat (by omega)
  have hb1 := hb.setRefs (k := y.rep.refs + 1) (v := BitVec.ofNat 64 (y.rep.refs + 1))
    (toNat_ofNat_mod32 (by omega)) hr
  have hb2 := hb1.out_frame (P := slotBytes q)
    (MemOnly.store _ q 8 (BitVec.ofNat 64 y.rep.p)) hsl.out
  have hq0 := hsl.out q ⟨Nat.le_refl _, by omega⟩
  have hq7 := hsl.out (q + 7) ⟨by omega, by omega⟩
  simp only [OutHeap, heapStart, heapEnd] at hq0 hq7
  bc_run hlive hS [hone, h2, h23, sv.get 1 88, sv.get 8 80, sv.get 18 64, sv.get 22 32,
    hrf, hsx] at 0x80006870
  all_goals first | exact hcst | exact hq.acc | exact frame_acc hsf (by omega) (by omega) | skip
  have hpq : ∀ a, OutHeap a → ¬ slotBytes q a →
      (a < q ∨ q + 8 ≤ a) ∧ (a < y.rep.p + 12 ∨ y.rep.p + 12 + 4 ≤ a) := fun a ha hs => by
    simp only [slotBytes] at hs
    simp only [OutHeap, heapStart, heapEnd] at ha
    omega
  have hsx2 : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (y.rep.refs + 1))) =
      BitVec.ofNat 64 (y.rep.refs + 1) := sxw_ofNat (by omega)
  rw [hsx2]
  refine ra_oneEpi hlive cx hS ?_ (by bsimp [h2]) (by keeps_tac hkp) (by bsimp [])
    (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [h9]) (by bsimp [h20]) (by bsimp [h21])
    (by bsimp [h24]) fun R' hk' => hk R' _ hk' hb2 (ldv_store_hit _ _ _) fun a ha hs => by
      rw [imgM_store_miss _ _ (hpq a ha hs).1, imgM_store_miss _ _ (hpq a ha hs).2]
  rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact sv.get 23 24

/-- **The zero exponent's result** from `0x80006840`: `bc_free_num (result)`,
then `_one_` (`o`) with one more reference in the slot. -/
theorem ra_one {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {x1 x2 z o xr : NumObj} (cx : RaCtx S R0 sp W q)
    (hK : RaK live S X Q t R0 Mt0 L xr [x1.rep.p, o.rep.p] q sp W Num.one)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots0) (h9 : R 9 = R0 9) (h20 : R 20 = R0 20)
    (h21 : R 21 = R0 21) (h24 : R 24 = R0 24)
    (hb : BcHeap S X M H F L) {k : Nat} (ha : RaArgs S Mt0 L x1 x2 z o k)
    (hs0 : RaSlot Mt0 L x1 x2 z o xr q) :
    DW live S (DQ live S Q t) 0x80006840#64 R M := by
  have hs := hs0.transport cx ra.out
  have hone := ha.oneAt cx ra.out
  have hown := ha.owns; have hom := ha.mo; have hon := ha.oneNum; have honz := ha.oneNorm
  have hol := ha.oneLen; have hor := ha.oneRefs
  ra_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi
  have hap := hsl.apart
  have h1o := cx.slotOne
  simp only [oneAddr] at h1o
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have sv := ra.saved
  have h2 := ra.r2
  have hor1 := hs.oneRef
  obtain ⟨X1, X2, rfl⟩ := List.append_of_mem hs.mr
  bc_run hlive hS [h2, ra.r23] at 0x800048c0
  refine ra_freeSlot hlive cx hb ⟨hs.rr, hs.wr, fun _ hxo y hy =>
      hb.owner_db_ne hxo hy (hown y (List.mem_append_left _ hy))⟩
    (by bsimp [h2]) (by bsimp [ra.r23]) (by bsimp []; try decide)
    fun R1 M1 H1 F1 L1 hk1 hfr hb1 ho1 => ?_
  bsimp [hk1.get 1]
  have hone1 : ldv .ld M1 oneAddr = BitVec.ofNat 64 o.rep.p := by
    rw [ldv_congr .ld fun j hj => ho1 _ (constBytes_out (by
      simp only [widthOfM, constBytes, twoAddr, zeroAddr, oneAddr] at hj ⊢; omega))
      (by simp only [slotBytes, widthOfM, oneAddr] at hj ⊢; omega)
      (by simp only [frameIn, widthOfM, oneAddr] at hj ⊢; omega)]
    exact hone
  have sv1 : SavedWords M1 (sp - 96) raSlots0 R0 := sv.transport (lo := 16) (top := 96)
    (hag := fun a h1 h2 => ho1 a
      (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega))
  have hout : ∀ M', (∀ a, OutHeap a → ¬ slotBytes q a → imgM M' a = imgM M1 a) →
      ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M' a = imgM Mt0 a :=
    fun M' ho' a ha hs' hf => by
      rw [ho' a ha hs', ho1 a ha hs' (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
      exact ra.out a ha hf
  have hreg : ∀ r, r ∈ [9, 20, 21, 24] → R1 r = R0 r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (rw [hk1.get _ (by decide)]; bsimp [h9, h20, h21, h24])
  obtain ⟨A, B, hAB⟩ := List.append_of_mem (List.mem_append_left _ hom : o ∈ X1 ++ xr :: X2 ++ [])
  rw [List.append_nil] at hAB
  rcases FreedRest.around hfr hAB with ⟨A', B', rfl, hd, -⟩ | ⟨rfl, rfl, rfl⟩
  · refine ra_oneRet hlive cx (A := A') (B := B') (y := o) hb1 hone1 hor sv1
      (by rw [hk1.get 2]; bsimp [h2]) ((hk1.mono (ks' := raAll) (by decide)).trans (by keeps_tac ra.keep)) (hreg 9 (by simp)) (hreg 20 (by simp))
      (hreg 21 (by simp)) (hreg 24 (by simp)) (by rw [hk1.get 23]; bsimp [ra.r23])
      fun R' M' hk' hb' hq' ho' => hK.ret R' M' H1 F1 _ (o.withRefs (o.rep.refs + 1)) hk'
        ⟨hb', ⟨_, by rw [hAB]; exact AddRef.share, hd _⟩,
          ⟨_, List.mem_append_right _ List.mem_cons_self⟩, .inr (.inr (by simp)), hon, honz, hol, hown o hom, hq', hout M' ho'⟩
  · cases hfr with
    | rel h => have := hor1 rfl; omega
    | dec h =>
      have e : xr.decRef.withRefs (xr.decRef.rep.refs + 1) = xr := by
        rw [NumObj.decRef_eq, NumObj.withRefs_withRefs, NumObj.withRefs_refs,
          Nat.sub_add_cancel (by omega), NumObj.withRefs_self]
      refine ra_oneRet hlive cx (A := X1) (B := X2) (y := xr.decRef) hb1 hone1
        (by simp only [NumObj.decRef]; omega) sv1
        (by rw [hk1.get 2]; bsimp [h2]) ((hk1.mono (ks' := raAll) (by decide)).trans (by keeps_tac ra.keep)) (hreg 9 (by simp)) (hreg 20 (by simp))
        (hreg 21 (by simp)) (hreg 24 (by simp)) (by rw [hk1.get 23]; bsimp [ra.r23])
        fun R' M' hk' hb' hq' ho' =>
          hK.ret R' M' H1 F1 (X1 ++ xr :: X2) (xr.withRefs (xr.rep.refs + 1)) hk' ?_
      rw [e] at hb'
      exact raPost_keep hb' hom hs.rr hon honz hol (hown _ hom) hq' (hout M' ho')

set_option maxRecDepth 100000 in
/-- "exponent too large in raise". -/
theorem raExpMsg : RtMsg 0x80007ea8 27 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Writes below the frame (a callee's) keep `bc_raise`'s state. -/
theorem RaAt.below {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    {sp W q : Nat} {slots : List (Nat × Nat)} (h : RaAt S Mt0 M R0 R sp W q slots)
    (cx : RaCtx S R0 sp W q) (hkp : Keeps raCallClob R' R)
    (hag : ∀ a, (a < sp - W ∨ sp - 96 ≤ a) → imgM M' a = imgM M a) :
    RaAt S Mt0 M' R0 R' sp W q slots where
  r2 := by rw [hkp.get 2]; exact h.r2
  saved := fun p hp => by
    rw [ldv_congr .ld fun j hj => hag _ (.inr (by omega))]
    exact h.saved p hp
  keep := (hkp.mono (by decide)).trans h.keep
  r23 := by rw [hkp.get 23]; exact h.r23
  out := fun a ha hf => by
    rw [hag a (by simp only [frameIn] at hf; omega)]
    exact h.out a ha hf

/-- **"exponent too large in raise"** at `0x80006834`, then the result
`_one_` (`ra_one`). -/
theorem ra_err {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {x1 x2 z o xr : NumObj} (cx : RaCtx S R0 sp W q)
    (hK : RaK live S X Q t R0 Mt0 L xr [x1.rep.p, o.rep.p] q sp W Num.one)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots0) (h9 : R 9 = R0 9) (h20 : R 20 = R0 20)
    (h21 : R 21 = R0 21) (h24 : R 24 = R0 24)
    (hb : BcHeap S X M H F L) (ha : RaArgs S Mt0 L x1 x2 z o k)
    (hs0 : RaSlot Mt0 L x1 x2 z o xr q) :
    DW live S (DQ live S Q t) 0x80006834#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hfar := cx.far
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := ra.r2
  bc_run hlive hS [h2] at 0x80002bd0
  refine rt_error_spec hlive raExpMsg (by decide) ((hsf.shrink (m := 96 + 416) (by omega)).sub (by decide)) (by omega) (ha.fdAt cx ra.out) _ (by bsimp [h2])
    (by bsimp []) (by bsimp []; try decide) fun R1 M1 hk1 ho1 => ?_
  bsimp [hk1.get 1]
  have hkc : Keeps raCallClob R1 R := (hk1.mono (ks' := raCallClob) (by decide)).trans
    (by keeps_tac Keeps.refl _ _)
  have hag : ∀ a, (a < sp - W ∨ sp - 96 ≤ a) → imgM M1 a = imgM M a :=
    fun a h => ho1 a (by omega)
  refine ra_one hlive cx hK (ra.below cx hkc hag) (by rw [hkc.get 9 (by decide)]; exact h9)
    (by rw [hkc.get 20 (by decide)]; exact h20) (by rw [hkc.get 21 (by decide)]; exact h21)
    (by rw [hkc.get 24 (by decide)]; exact h24)
    (hb.out_frame (P := fun a => sp - W ≤ a ∧ a < sp - 96) (fun a h => hag a (by omega))
      fun a h => by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
    ha hs0

/-- **A zero exponent** at `0x8000681c` (`s0` = `num2`): "exponent too large
in raise" when `num2`'s integer part is not `0`, then the result `_one_`. -/
theorem ra_zero {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {x1 x2 z o xr : NumObj} (cx : RaCtx S R0 sp W q)
    (hK : RaK live S X Q t R0 Mt0 L xr [x1.rep.p, o.rep.p] q sp W Num.one)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots0) (h9 : R 9 = R0 9) (h20 : R 20 = R0 20)
    (h21 : R 21 = R0 21) (h24 : R 24 = R0 24)
    (hb : BcHeap S X M H F L) (ha : RaArgs S Mt0 L x1 x2 z o k)
    (hs0 : RaSlot Mt0 L x1 x2 z o xr q) (h8 : R 8 = BitVec.ofNat 64 x2.rep.p) :
    DW live S (DQ live S Q t) 0x8000681c#64 R M := by
  ra_facts cx
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn := hb.nums x2 ha.m2
  num_facts hn
  have hl2 := ha.len2
  have hsz := hn.shape.size
  have hl := hn.len
  have hv := hn.value
  bc_run hlive hS [h8, hl, hv] at 0x80006834 0x80006840
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  all_goals (try intro _)
  · exact ra_err hlive cx hK (ra.regs (by keeps_tac Keeps.refl _ _)) (by bsimp [h9]) (by bsimp [h20])
      (by bsimp [h21]) (by bsimp [h24]) hb ha hs0
  bc_run hlive hS [h8, hv] at 0x80006834 0x80006840
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  all_goals (try intro _)
  · exact ra_one hlive cx hK (ra.regs (by keeps_tac Keeps.refl _ _)) (by bsimp [h9]) (by bsimp [h20])
      (by bsimp [h21]) (by bsimp [h24]) hb ha hs0
  · exact ra_err hlive cx hK (ra.regs (by keeps_tac Keeps.refl _ _)) (by bsimp [h9]) (by bsimp [h20])
      (by bsimp [h21]) (by bsimp [h24]) hb ha hs0

/-! ## A nonzero exponent -/

/-- **The loops and the result** from `0x8000668c`: `ra_loops`, its exits
into `ra_endC` (a power of two) and `ra_end2`. -/
theorem ra_go {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k u rs nf : Nat} {H H0 : Heap}
    {F F0 : List Blk} {A B : List NumObj} {x1 x2 z o xr : NumObj}
    (cx : RaCtx S R0 sp W q)
    (hK : RaK live S X Q t R0 Mt0 (A ++ x1 :: B) xr [x1.rep.p, o.rep.p] q sp W (Num.raise x1.rep.num x2.rep.num k).1)
    (ha : RaArgs S Mt0 (A ++ x1 :: B) x1 x2 z o k) (hs0 : RaSlot Mt0 (A ++ x1 :: B) x1 x2 z o xr q)
    (hb0 : BcHeap S X Mt0 H0 F0 (A ++ x1 :: B)) (hr1 : 1 ≤ x1.rep.refs)
    (hm : RaMode x1 x2 k u rs nf) (hu : u ≠ 0)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots1) (h21 : R 21 = R0 21)
    (hb : BcHeap S X M H F (A ++ x1 :: B))
    (h18 : R 18 = BitVec.ofNat 64 x1.rep.p) (h9 : R 9 = BitVec.ofNat 64 x1.rep.scale)
    (h8 : R 8 = BitVec.ofNat 64 u) (h22 : R 22 = BitVec.ofNat 64 rs)
    (h24 : R 24 = BitVec.ofNat 64 nf) :
    DW live S (DQ live S Q t) 0x8000668c#64 R M := by
  have hsz := ha.size
  rw [← hm.abs] at hsz
  have env : RaEnv S Mt0 R0 sp W q A B x1 z o u :=
    ⟨cx, ha.owns, ha.mz, ha.mo, RaCst.of_args ha, ha.n1, ha.len1, hr1, ha.refs1,
      Nat.one_le_iff_ne_zero.mpr hu, by omega⟩
  exact ra_loops hlive env hK.oom ra h21 hb h18 h9 h8 h22 h24
    (fun _ _ _ _ _ _ st hui => ra_endC hlive env hK ha hs0 hb0 hm st hui)
    (fun _ _ _ _ _ _ _ st => ra_end2 hlive env hK ha hs0 hm st)

/-- **`rscale = MIN (scale1 · exponent, MAX (scale, scale1))`** from
`0x8000666c` (`a0` the product), then `ra_go`. -/
theorem ra_rscale {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k u : Nat} {H H0 : Heap}
    {F F0 : List Blk} {A B : List NumObj} {x1 x2 z o xr : NumObj}
    (cx : RaCtx S R0 sp W q)
    (hK : RaK live S X Q t R0 Mt0 (A ++ x1 :: B) xr [x1.rep.p, o.rep.p] q sp W (Num.raise x1.rep.num x2.rep.num k).1)
    (ha : RaArgs S Mt0 (A ++ x1 :: B) x1 x2 z o k) (hs0 : RaSlot Mt0 (A ++ x1 :: B) x1 x2 z o xr q)
    (hb0 : BcHeap S X Mt0 H0 F0 (A ++ x1 :: B)) (hr1 : 1 ≤ x1.rep.refs)
    (hu : u = (raExp x2).natAbs) (hpos : 0 < raExp x2)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots1) (h21 : R 21 = R0 21)
    (hb : BcHeap S X M H F (A ++ x1 :: B))
    (h18 : R 18 = BitVec.ofNat 64 x1.rep.p) (h9 : R 9 = BitVec.ofNat 64 x1.rep.scale)
    (h8 : R 8 = BitVec.ofNat 64 u) (h22 : R 22 = BitVec.ofNat 64 k)
    (h10 : R 10 = BitVec.ofNat 64 (x1.rep.scale * u)) :
    DW live S (DQ live S Q t) 0x8000666c#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := ha.size
  rw [← hu] at hsz
  have hs1 : x1.rep.scale * u < 2 ^ 24 := by
    have := Nat.mul_le_mul (show u ≤ u + 1 by omega)
      (show x1.rep.scale ≤ x1.rep.len + x1.rep.scale + 1 by omega)
    rw [Nat.mul_comm x1.rep.scale u]; omega
  have hk : k < 2 ^ 24 := by omega
  have hsc : x1.rep.scale < 2 ^ 24 := by
    have := Nat.mul_le_mul (show 1 ≤ u + 1 by omega) (show x1.rep.scale ≤ x1.rep.len + x1.rep.scale + 1 by omega)
    omega
  have hu0 : u ≠ 0 := by omega
  bc_run hlive hS [h9, h10, h22] at 0x8000668c
  all_goals intro hc
  all_goals (try rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hc)
  all_goals bc_run hlive hS [h9, h10, h22] at 0x8000668c
  all_goals intro hc2
  all_goals (try bc_run hlive hS [h9, h10, h22] at 0x8000668c)
  all_goals first
    | exact ra_go hlive cx hK ha hs0 hb0 hr1 (rs := x1.rep.scale * u) ⟨hu, .inl ⟨rfl, hpos, by omega⟩⟩
        hu0 (ra.regsA (ks := [10, 15, 22, 24]) (by keeps_tac Keeps.refl _ _)) (by bsimp [h21]) hb
        (by bsimp [h18]) (by bsimp [h9]) (by bsimp [h8]) (by bsimp []) (by bsimp [])
    | exact ra_go hlive cx hK ha hs0 hb0 hr1 (rs := x1.rep.scale) ⟨hu, .inl ⟨rfl, hpos, by omega⟩⟩
        hu0 (ra.regsA (ks := [10, 15, 22, 24]) (by keeps_tac Keeps.refl _ _)) (by bsimp [h21]) hb
        (by bsimp [h18]) (by bsimp [h9]) (by bsimp [h8]) (by bsimp []) (by bsimp [])
    | exact ra_go hlive cx hK ha hs0 hb0 hr1 (rs := k) ⟨hu, .inl ⟨rfl, hpos, by omega⟩⟩
        hu0 (ra.regsA (ks := [10, 15, 22, 24]) (by keeps_tac Keeps.refl _ _)) (by bsimp [h21]) hb
        (by bsimp [h18]) (by bsimp [h9]) (by bsimp [h8]) (by bsimp []) (by bsimp [])

/-- `neg` of a negative `long`. -/
theorem neg_ofInt_natAbs {e : Int} (h : e < 0) (h2 : -2 ^ 63 < e) :
    0#64 - BitVec.ofInt 64 e = BitVec.ofNat 64 e.natAbs := by
  obtain ⟨u, rfl⟩ : ∃ u : Nat, e = -(u : Int) := ⟨e.natAbs, by omega⟩
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]
  omega

/-- `s1`, `s4`, `s8` saved for a nonzero exponent (`0x80006648`). -/
theorem RaAt.save1 {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    (cx : RaCtx S R0 sp W q) (h : RaAt S Mt0 M R0 R sp W q raSlots0) {v9 v20 v24 : BitVec 64}
    (h9 : v9 = R0 9) (h20 : v20 = R0 20) (h24 : v24 = R0 24) :
    RaAt S Mt0 (writeLog (writeLog (writeLog M [(sp - 96 + 72, 8, v9)]) [(sp - 96 + 48, 8, v20)])
      [(sp - 96 + 16, 8, v24)]) R0 R sp W q raSlots1 := by
  ra_facts cx
  subst h9 h20 h24
  exact { h with
    saved := ((h.saved.store 9 72).store 20 48).store 24 16
    out := fun a ha hf => by
      simp only [frameIn] at hf
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
        imgM_store_miss _ _ (by omega)]
      exact h.out a ha (by simp only [frameIn]; omega) }

/-- **A nonzero exponent** from `0x80006648` (`a0` = `bc_num2long (num2)`):
`s1`, `s4`, `s8` saved, `pwrscale = num1->n_scale`, then the negative
exponent negated (`s8 = 1`, `rscale = scale`) or `ra_rscale` after
`scale1 · exponent`. -/
theorem ra_body {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H H0 : Heap}
    {F F0 : List Blk} {A B : List NumObj} {x1 x2 z o xr : NumObj}
    (cx : RaCtx S R0 sp W q)
    (hK : RaK live S X Q t R0 Mt0 (A ++ x1 :: B) xr [x1.rep.p, o.rep.p] q sp W (Num.raise x1.rep.num x2.rep.num k).1)
    (ha : RaArgs S Mt0 (A ++ x1 :: B) x1 x2 z o k) (hs0 : RaSlot Mt0 (A ++ x1 :: B) x1 x2 z o xr q)
    (hb0 : BcHeap S X Mt0 H0 F0 (A ++ x1 :: B)) (hr1 : 1 ≤ x1.rep.refs)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots0) (h9 : R 9 = R0 9) (h20 : R 20 = R0 20)
    (h21 : R 21 = R0 21) (h24 : R 24 = R0 24)
    (hb : BcHeap S X M H F (A ++ x1 :: B))
    (h18 : R 18 = BitVec.ofNat 64 x1.rep.p) (h22 : R 22 = BitVec.ofNat 64 k)
    (h10 : R 10 = BitVec.ofInt 64 (raExp x2)) (he : raExp x2 ≠ 0) :
    DW live S (DQ live S Q t) 0x80006648#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hal := cx.al
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn1 := hb.nums x1 ha.m1
  num_facts hn1
  have hsc := hn1.scale
  have hsz := ha.size
  have ra1 := ra.save1 cx (v9 := R0 9) (v20 := R0 20) (v24 := R0 24) rfl rfl rfl
  have hp8 : x1.rep.p + 8 + 4 ≤ sp - 96 := by omega
  have hsc24 : x1.rep.scale < 2 ^ 24 := by
    have := Nat.mul_le_mul (show 1 ≤ (raExp x2).natAbs + 1 by omega)
      (show x1.rep.scale ≤ x1.rep.len + x1.rep.scale + 1 by omega)
    omega
  have hu24 : (raExp x2).natAbs < 2 ^ 24 := by
    have := Nat.mul_le_mul (show (raExp x2).natAbs + 1 ≤ (raExp x2).natAbs + 1 by omega)
      (show 1 ≤ x1.rep.len + x1.rep.scale + 1 by omega)
    omega
  have ht : (BitVec.ofInt 64 (raExp x2)).toInt = raExp x2 := toInt_ofInt64 (by omega) (by omega)
  have hP : ∀ a, (sp - 96 + 72 ≤ a ∧ a < sp - 96 + 72 + 8) ∨ (sp - 96 + 48 ≤ a ∧ a < sp - 96 + 48 + 8) ∨
      (sp - 96 + 16 ≤ a ∧ a < sp - 96 + 16 + 8) → OutHeap a := fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hbW : BcHeap S X (writeLog (writeLog (writeLog M [(sp - 96 + 72, 8, R0 9)])
      [(sp - 96 + 48, 8, R0 20)]) [(sp - 96 + 16, 8, R0 24)]) H F (A ++ x1 :: B) :=
    ((hb.out_frame (MemOnly.store _ _ 8 _) (fun a h => hP a (.inl h))).out_frame
      (MemOnly.store _ _ 8 _) (fun a h => hP a (.inr (.inl h)))).out_frame
      (MemOnly.store _ _ 8 _) (fun a h => hP a (.inr (.inr h)))
  bc_run hlive hS [ra.r2, h18, h10, h9, h20, h24, ht] at 0x80006684 0x8000666c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals rw [show ldv .lw (writeLog (writeLog (writeLog M [(sp - 96 + 72, 8, R0 9)])
      [(sp - 96 + 48, 8, R0 20)]) [(sp - 96 + 16, 8, R0 24)]) (x1.rep.p + 8) =
      BitVec.ofNat 64 x1.rep.scale by
    rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega),
      ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega),
      ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]
    exact hsc, BitVec.toInt_zero]
  all_goals intro hc
  · bc_run hlive hS [ra.r2, h18, h10] at 0x8000668c
    have hng := neg_ofInt_natAbs hc (by omega)
    exact ra_go hlive cx hK ha hs0 hb0 hr1 (rs := k) (nf := 1) ⟨rfl, .inr ⟨rfl, hc, rfl⟩⟩
      (by omega) (ra1.regsA (ks := [8, 9, 24]) (by keeps_tac Keeps.refl _ _)) (by bsimp [h21]) hbW
      (by bsimp [h18]) (by bsimp []) (by bsimp [hng]) (by bsimp [h22]) (by bsimp [])
  · have hu : raExp x2 = ((raExp x2).natAbs : Int) := by omega
    rw [hu, ofInt_natCast64] at h10
    bc_run hlive hS [ra.r2, h18, h10] at 0x800078a4
    refine muldi3_spec hlive _ (by bsimp []) fun R1 hk1 h10' => ?_
    bsimp [hk1.get 1]
    have hkk : Keeps [1, 8, 9, 10, 11, 12, 13] R1 R :=
      (hk1.mono (ks' := [1, 8, 9, 10, 11, 12, 13]) (by decide)).trans (by keeps_tac Keeps.refl _ _)
    exact ra_rscale hlive cx hK ha hs0 hb0 hr1 rfl (by omega) (ra1.regsA hkk)
      (by rw [hkk.get 21 (by decide)]; exact h21) hbW
      (by rw [hkk.get 18 (by decide)]; exact h18) (by rw [hk1.get 9 (by decide)]; bsimp [])
      (by rw [hk1.get 8 (by decide)]; bsimp []) (by rw [hkk.get 22 (by decide)]; exact h22)
      (by rw [h10']; bsimp [mul_ofNat])

/-! ## The entry -/

/-- A zero exponent raises to `1`. -/
theorem raise_zero_fst {a b : Num} {k : Nat} (h : b.toLong = 0) : (Num.raise a b k).1 = Num.one := by
  simp [Num.raise, h]

/-- **`exponent = bc_num2long (num2)`** from `0x8000663c` (`s0` = `num2`),
then a zero exponent (`ra_zero`) or a nonzero one (`ra_body`). -/
theorem ra_num {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H H0 : Heap}
    {F F0 : List Blk} {A B : List NumObj} {x1 x2 z o xr : NumObj}
    (cx : RaCtx S R0 sp W q)
    (hK : RaK live S X Q t R0 Mt0 (A ++ x1 :: B) xr [x1.rep.p, o.rep.p] q sp W (Num.raise x1.rep.num x2.rep.num k).1)
    (ha : RaArgs S Mt0 (A ++ x1 :: B) x1 x2 z o k) (hs0 : RaSlot Mt0 (A ++ x1 :: B) x1 x2 z o xr q)
    (hb0 : BcHeap S X Mt0 H0 F0 (A ++ x1 :: B)) (hr1 : 1 ≤ x1.rep.refs)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots0) (h9 : R 9 = R0 9) (h20 : R 20 = R0 20)
    (h21 : R 21 = R0 21) (h24 : R 24 = R0 24)
    (hb : BcHeap S X M H F (A ++ x1 :: B))
    (h8 : R 8 = BitVec.ofNat 64 x2.rep.p) (h18 : R 18 = BitVec.ofNat 64 x1.rep.p)
    (h22 : R 22 = BitVec.ofNat 64 k) :
    DW live S (DQ live S Q t) 0x8000663c#64 R M := by
  ra_facts cx
  have hal := cx.al
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn2 := hb.nums x2 ha.m2
  have hsz := ha.size
  have hu24 : (raExp x2).natAbs < 2 ^ 24 := by
    have := Nat.mul_le_mul (show (raExp x2).natAbs + 1 ≤ (raExp x2).natAbs + 1 by omega)
      (show 1 ≤ x1.rep.len + x1.rep.scale + 1 by omega)
    omega
  bc_run hlive hS [h8] at 0x800065a0
  refine bc_num2long_spec hlive hS hn2 ha.len2 _ (by bsimp [h8]) (by bsimp []) fun R1 hk1 h10 => ?_
  bsimp [hk1.get 1]
  have hkk : Keeps raCallClob R1 R :=
    (hk1.mono (ks' := raCallClob) (by decide)).trans (by keeps_tac Keeps.refl _ _)
  have hre : raExp x2 = x2.rep.num.toLong := rfl
  have ez : BitVec.ofInt 64 x2.rep.num.toLong = 0#64 ↔ raExp x2 = 0 := by
    constructor
    · intro h
      have := congrArg BitVec.toInt h
      rwa [toInt_ofInt64 (by omega) (by omega), BitVec.toInt_zero] at this
    · intro h; rw [show x2.rep.num.toLong = 0 from h]; rfl
  bc_run hlive hS [h10, ez] at 0x8000681c 0x80006648
  · intro hz
    rw [raise_zero_fst hz] at hK
    exact ra_zero hlive cx hK (ra.regs hkk) (by rw [hkk.get 9 (by decide)]; exact h9)
      (by rw [hkk.get 20 (by decide)]; exact h20) (by rw [hkk.get 21 (by decide)]; exact h21)
      (by rw [hkk.get 24 (by decide)]; exact h24) hb ha hs0 (by rw [hkk.get 8 (by decide)]; exact h8)
  · intro hnz
    exact ra_body hlive cx hK ha hs0 hb0 hr1 (ra.regs hkk) (by rw [hkk.get 9 (by decide)]; exact h9)
      (by rw [hkk.get 20 (by decide)]; exact h20) (by rw [hkk.get 21 (by decide)]; exact h21)
      (by rw [hkk.get 24 (by decide)]; exact h24) hb (by rw [hkk.get 18 (by decide)]; exact h18)
      (by rw [hkk.get 22 (by decide)]; exact h22) h10 hnz

set_option maxRecDepth 100000 in
/-- "non-zero scale in exponent". -/
theorem raScaleMsg : RtMsg 0x80007e60 26 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **"non-zero scale in exponent"** at `0x8000687c`, then `ra_num`. -/
theorem ra_warn {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H H0 : Heap}
    {F F0 : List Blk} {A B : List NumObj} {x1 x2 z o xr : NumObj}
    (cx : RaCtx S R0 sp W q)
    (hK : RaK live S X Q t R0 Mt0 (A ++ x1 :: B) xr [x1.rep.p, o.rep.p] q sp W (Num.raise x1.rep.num x2.rep.num k).1)
    (ha : RaArgs S Mt0 (A ++ x1 :: B) x1 x2 z o k) (hs0 : RaSlot Mt0 (A ++ x1 :: B) x1 x2 z o xr q)
    (hb0 : BcHeap S X Mt0 H0 F0 (A ++ x1 :: B)) (hr1 : 1 ≤ x1.rep.refs)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots0) (h9 : R 9 = R0 9) (h20 : R 20 = R0 20)
    (h21 : R 21 = R0 21) (h24 : R 24 = R0 24)
    (hb : BcHeap S X M H F (A ++ x1 :: B))
    (h8 : R 8 = BitVec.ofNat 64 x2.rep.p) (h18 : R 18 = BitVec.ofNat 64 x1.rep.p)
    (h22 : R 22 = BitVec.ofNat 64 k) :
    DW live S (DQ live S Q t) 0x8000687c#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hfar := cx.far
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := ra.r2
  bc_run hlive hS [h2] at 0x80002c50
  refine rt_warn_spec hlive raScaleMsg (by decide)
    ((hsf.shrink (m := 96 + 416) (by omega)).sub (by decide)) (by omega) (ha.fdAt cx ra.out) _
    (by bsimp [h2]) (by bsimp []) (by bsimp []; try decide) fun R1 M1 hk1 ho1 => ?_
  bsimp [hk1.get 1]
  have hkc : Keeps raCallClob R1 R := (hk1.mono (ks' := raCallClob) (by decide)).trans
    (by keeps_tac Keeps.refl _ _)
  have hag : ∀ a, (a < sp - W ∨ sp - 96 ≤ a) → imgM M1 a = imgM M a :=
    fun a h => ho1 a (by omega)
  bc_run hlive hS [] at 0x8000663c
  exact ra_num hlive cx hK ha hs0 hb0 hr1 (ra.below cx hkc hag)
    (by rw [hkc.get 9 (by decide)]; exact h9) (by rw [hkc.get 20 (by decide)]; exact h20)
    (by rw [hkc.get 21 (by decide)]; exact h21) (by rw [hkc.get 24 (by decide)]; exact h24)
    (hb.out_frame (P := fun a => sp - W ≤ a ∧ a < sp - 96) (fun a h => hag a (by omega))
      fun a h => by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
    (by rw [hkc.get 8 (by decide)]; exact h8) (by rw [hkc.get 18 (by decide)]; exact h18)
    (by rw [hkc.get 22 (by decide)]; exact h22)

/-- The prologue's five saved registers. -/
abbrev raPro (M : Mem) (sp : Nat) (R : Nat → BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog M
    [(sp - 96 + 80, 8, R 8)]) [(sp - 96 + 64, 8, R 18)]) [(sp - 96 + 32, 8, R 22)])
    [(sp - 96 + 24, 8, R 23)]) [(sp - 96 + 88, 8, R 1)]

theorem raPro_saved (M : Mem) (sp : Nat) (R : Nat → BitVec 64) :
    SavedWords (raPro M sp R) (sp - 96) raSlots0 R := fun p hp =>
  (((((SavedWords.nil M (sp - 96) R).store 8 80).store 18 64).store 22 32).store 23 24 |>.store
    1 88) p (by
      simp only [raSlots0, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp)

theorem raPro_frame {M : Mem} {sp : Nat} (R : Nat → BitVec 64) (hsp : 96 ≤ sp) :
    MemOnly (frameIn sp 96) (raPro M sp R) M := fun a ha => by
  simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]

/-- **`bc_raise (num1, num2, result, scale)`** at `0x8000660c`: the result
`Num.raise`'s first component in the slot (`RaK.ret`), or `out_of_memory`
(`RaK.oom`). The runtime warning and error go to stderr only. -/
theorem bc_raise_spec {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {x1 x2 z o xr : NumObj}
    (cx : RaCtx S R0 sp W q) (ha : RaArgs S Mt0 L x1 x2 z o k) (hs0 : RaSlot Mt0 L x1 x2 z o xr q)
    (hb : BcHeap S X Mt0 H F L) (hr1 : 1 ≤ x1.rep.refs)
    (hK : RaK live S X Q t R0 Mt0 L xr [x1.rep.p, o.rep.p] q sp W (Num.raise x1.rep.num x2.rep.num k).1)
    (h10 : R0 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R0 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R0 12 = BitVec.ofNat 64 q) (h13 : R0 13 = BitVec.ofNat 64 k) :
    DWO live S Q t 0x8000660c#64 R0 Mt0 := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem ha.m1
  ra_facts cx
  have hsf := cx.frame
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hx2n := hb.nums x2 ha.m2
  num_facts hx2n
  have hm := raPro_frame (M := Mt0) (sp := sp) R0 (by omega)
  have hfz : ∀ a, ¬ frameIn sp W a → imgM (raPro Mt0 sp R0) a = imgM Mt0 a := fun a hf =>
    hm a fun h => hf (by simp only [frameIn] at h ⊢; omega)
  have hb' := hb.out_frame hm fun a ha' => by
    simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha' ⊢; omega
  bc_run hlive hS [cx.sp0, h11, hx2n.scale, word_sub96] at 0x8000663c 0x8000687c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | skip
  all_goals intro _
  · exact ra_warn hlive cx hK ha hs0 hb hr1 ⟨by bsimp [], raPro_saved Mt0 sp R0,
      by keeps_tac Keeps.refl _ _, by bsimp [h12], fun a _ hf => hfz a hf⟩
      (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) hb' (by bsimp [h11])
      (by bsimp [h10]) (by bsimp [h13])
  · exact ra_num hlive cx hK ha hs0 hb hr1 ⟨by bsimp [], raPro_saved Mt0 sp R0,
      by keeps_tac Keeps.refl _ _, by bsimp [h12], fun a _ hf => hfz a hf⟩
      (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) hb' (by bsimp [h11])
      (by bsimp [h10]) (by bsimp [h13])

end Dc.Mach
