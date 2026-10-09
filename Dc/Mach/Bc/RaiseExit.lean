import Dc.Mach.Bc.RaiseTail

/-!
# `bc_raise`'s result: the division, the store, the temporary's release

- `ra_freeTemp` (`0x80006760`): `temp` released, `s5` reloaded on the way.
- `ra_negDiv` (`0x80006744`): `bc_divide (_one_, temp, result, rscale)`.
- `ra_store` (`0x80006898`): `*result = temp`, its scale cut to `rscale`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The continuation at `0x80006798` after `temp` is released: the heap
freed, `s5` the word `w`. -/
def RaTempK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (L1 L2 : List NumObj)
    (x : NumObj) (w : BitVec 64) : Prop :=
  ∀ R' M' H' F' L', Keeps [1, 10, 14, 15, 21] R' R → R' 21 = w → KFreed H F L1 L2 x H' F' L' →
    BcHeap S M' H' F' L' → (∀ a, OutHeap a → imgM M' a = imgM M a) → DW live S Q 0x80006798#64 R' M'

/-- **`bc_free_num (&temp)`** from `0x80006760` (`temp` in `s4`, not `NULL`),
`s5` reloaded from `sp + 40` between the count's load and store. -/
theorem ra_freeTemp {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S M H F (L1 ++ x :: L2)) (ho : x.Owns) (hnv : ∀ y ∈ L1, y.db ≠ x.db)
    (hr : 1 ≤ x.rep.refs) (h2 : R 2 = BitVec.ofNat 64 (sp - 96))
    (h20 : R 20 = BitVec.ofNat 64 x.rep.p) {w : BitVec 64} (hw : ldv .ld M (sp - 96 + 40) = w)
    (hk : RaTempK live S Q R M H F L1 L2 x w) :
    DW live S Q 0x80006760#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hi := hb.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hxm : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums x hxm
  have hxb := hb.blocks x hxm
  num_facts hn
  have hrf := hn.refs
  have hw' : ∀ v, ldv .ld (writeLog M [(x.rep.p + 12, 4, v)]) (sp - 96 + 40) = w := fun v => by
    rw [ldv_ld_miss _ _ (by omega)]; exact hw
  bc_run hlive hS [h20, h2, hrf, hw] at 0x80006764
  all_goals try (intro hc; exact absurd ((ofNat_eq_iff (x := x.rep.p) (y := 0)
    (by omega) (by omega)).mp hc) (by omega))
  intro _
  rcases (show x.rep.refs = 1 ∨ 2 ≤ x.rep.refs from by omega) with hr1 | hr2
  · have h0 : BitVec.ofNat 64 1 + 18446744073709551615#64 = 0#64 := by decide
    bc_run hlive hS [h20, h2, hrf, hw, hr1, h0] at 0x80006798 0x80006778
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hpp : x.rep.p = x.sb.pay := hxb.sPay
    have hsz := hxb.sSz
    have hsph : x.sb.pay = x.sb.h + 16 := rfl
    refine ffree_owner_80006760 (fr := fun _ => False) (R0 := upd (upd (upd R 15 1#64) 21 w) 15
        (BitVec.signExtend 64 (BitVec.extractLsb 31 0 0#64))) hlive hb ho (fun _ => hnv) hr1 rfl
      (hi.transport fun a ha => by
        have hn := live_not_alloc hi hxb.sLive (a := a)
        refine imgM_store_miss _ _ (Classical.byContradiction fun hc => hn ⟨by omega, ?_⟩ ha)
        simp only [Blk.fin] at hc ⊢; omega)
      (by rw [ldv_ld_miss _ _ (by omega)]; exact hb.dead.head)
      (fun a ha => by simp only [OutHeap, heapStart, heapEnd] at ha; exact imgM_store_miss _ _ (by omega))
      (Keeps.refl _ _) (by bsimp [h20]) ?_
    intro R' M' H' F' L' hk' hf hb' ho'
    refine hk R' M' H' F' L' ?_ ?_ hf hb' fun a ha => ho' a ha id
    · have hk2 : Keeps [1, 10, 14, 15, 21] R' (upd (upd (upd R 15 1#64) 21 w) 15
          (BitVec.signExtend 64 (BitVec.extractLsb 31 0 0#64))) :=
        hk'.mono (fun z hz => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢; omega)
      exact hk2.trans (by keeps_tac Keeps.refl _ _)
    · rw [hk'.get 21 (by decide)]; bsimp []
  · have hpr : BitVec.ofNat 64 x.rep.refs + 18446744073709551615#64 =
        BitVec.ofNat 64 (x.rep.refs - 1) := word_pred (by omega)
    have hsx : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (x.rep.refs - 1))) =
        BitVec.ofNat 64 (x.rep.refs - 1) := sxw_ofNat (by omega)
    bc_run hlive hS [h20, h2, hrf, hw, hpr, hsx] at 0x80006798 0x80006778
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals try (intro hc; exact absurd ((ofNat_eq_iff (x := x.rep.refs - 1) (y := 0)
      (by omega) (by omega)).mp (Classical.not_not.mp hc)) (by omega))
    intro _
    refine hk _ _ H F _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (.dec hr2)
      (hb.setRefs (toNat_ofNat_mod32 (by omega)) (by omega)) fun a ha => ?_
    simp only [OutHeap, heapStart, heapEnd] at ha
    exact imgM_store_miss _ _ (by omega)

/-- **A call of `bc_divide`** from `bc_raise`'s frame (`sp - 96`) into the
result slot `q`. -/
theorem ra_divCall {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {n : Option Num}
    {L1 L2 : List NumObj} {x1 x2 xr z : NumObj} {H : Heap} {F : List Blk}
    (cx : RaCtx S R0 sp W q) (hoom : RaOom live S Q Mt0 sp W q)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (ha : DivArgs M L1 L2 xr x1 x2 z n k) (hzm : z.rep.num.mag = 0)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 q) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ m, n = some m → ∀ R' M' H' F' L' y, Keeps binClob R' R →
      BinPostW S M M' H' F' L1 L2 xr q (sp - 96) (W - 96) m L' y → DW live S Q (R 1) R' M')
    (hzero : n = none → ∀ R' M', Keeps binClob R' R →
      (∀ a, ¬ frameIn (sp - 96) (W - 96) a → imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000589c#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  exact bc_divide_spec hlive
    ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
      by simp only [heapEnd]; omega, by omega, hq, hsl.out, by omega, cx.slotZero, cx.consts,
      h2, hal⟩
    ⟨fun m hm R' M' H' F' L' y hk _ hp => hret m hm R' M' H' F' L' y hk hp,
      fun hn R' M' hk _ hf => hzero hn R' M' hk hf,
      fun R' M' sp' h1 h2 hr2 hout => hoom R' M' sp' (by omega) (by omega) hr2
        fun a ha hs hf => by
          rw [hout a ha hs (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
          exact houtM a ha hf⟩
    ha hzm hb hr h10 h11 h12 h13

/-! ## The result -/

theorem FreedRest.pre {X1 X2 L : List NumObj} {x : NumObj} (P : List NumObj)
    (h : FreedRest X1 X2 x L) : FreedRest (P ++ X1) X2 x (P ++ L) := by
  cases h with
  | dec h => rw [← List.append_assoc]; exact .dec h
  | rel h => rw [← List.append_assoc]; exact .rel h

theorem FreedRest.unpre {P X1 X2 L : List NumObj} {x : NumObj} (h : FreedRest (P ++ X1) X2 x L) :
    ∃ L0, L = P ++ L0 ∧ FreedRest X1 X2 x L0 := by
  cases h with
  | dec h => exact ⟨_, by rw [List.append_assoc], .dec h⟩
  | rel h => exact ⟨_, by rw [List.append_assoc], .rel h⟩

/-- **A new number `y` for `n`** in the slot, heading the caller's heap with
the old number dropped. -/
theorem raPost_fresh {S : Nat → Prop} {Mt0 Mt : Mem} {H : Heap} {F : List Blk}
    {X1 X2 L : List NumObj} {xr y : NumObj} {q sp W : Nat} {n : Num}
    (hb : BcHeap S Mt H F (y :: L)) (hr : FreedRest X1 X2 xr L) (hy1 : y.rep.refs = 1)
    (hnum : y.rep.num = n) (hnorm : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (hyo : y.Owns)
    (hslot : ldv .ld Mt q = BitVec.ofNat 64 y.rep.p)
    (hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM Mt a = imgM Mt0 a) :
    RaPost S Mt0 Mt H F (X1 ++ xr :: X2) xr q sp W n (y :: L) y :=
  ⟨hb, ⟨_, .fresh hy1, [y] ++ X1, X2, xr, rfl, rfl, hr.pre [y]⟩, hnum, hnorm, hpos, hyo, hslot, hout⟩

/-- **The old number kept** (a division by zero): one reference added, then
dropped. -/
theorem raPost_keep {S : Nat → Prop} {Mt0 Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {xr : NumObj} {q sp W : Nat} {n : Num}
    (hb : BcHeap S Mt H F L) (hm : xr ∈ L) (hr : 1 ≤ xr.rep.refs)
    (hnum : xr.rep.num = n) (hnorm : xr.rep.Norm) (hpos : 1 ≤ xr.rep.len) (hxo : xr.Owns)
    (hslot : ldv .ld Mt q = BitVec.ofNat 64 xr.rep.p)
    (hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM Mt a = imgM Mt0 a) :
    RaPost S Mt0 Mt H F L xr q sp W n L (xr.withRefs (xr.rep.refs + 1)) := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hm
  have hd : (xr.withRefs (xr.rep.refs + 1)).decRef = xr := by
    simp only [NumObj.decRef_eq, NumObj.withRefs_withRefs]
    simp only [NumObj.withRefs, Nat.add_sub_cancel]
  refine ⟨hb, ⟨_, .share, A, B, _, rfl, rfl, ?_⟩, hnum, hnorm, hpos, hxo, hslot, hout⟩
  have e := FreedRest.dec (L1 := A) (L2 := B) (x := xr.withRefs (xr.rep.refs + 1))
    (by simp only [NumObj.withRefs]; omega)
  rwa [hd] at e

/-- **From `0x8000675c`** (after the division): `temp` and `power` (`T`, `P`,
one reference each, after the numbers `Y`) released, the epilogue. -/
theorem ra_negFree {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {Y L : List NumObj} {T P : NumObj} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S M H F (Y ++ T :: P :: L)) (hY : ∀ y ∈ Y, y.Owns)
    (hT1 : T.rep.refs = 1) (hP1 : P.rep.refs = 1) (hTo : T.Owns) (hPo : P.Owns)
    (ra : RaAt S M M R0 R sp W q raSlots2)
    (h20 : R 20 = BitVec.ofNat 64 T.rep.p)
    (hwP : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 P.rep.p)
    (hk : ∀ R' M' H' F', Keeps binClob R' R0 → BcHeap S M' H' F' (Y ++ L) →
      (∀ a, OutHeap a → imgM M' a = imgM M a) → DW live S Q (R0 1) R' M') :
    DW live S Q 0x8000675c#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have sv := ra.saved
  have h2 := ra.r2
  bc_run hlive hS [h2, hwP] at 0x80006760
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine ra_freeTemp hlive cx (L1 := Y) (L2 := P :: L) hb hTo
    (fun y hy => hb.owner_db_ne hTo hy (hY y hy)) (by omega) (by bsimp [h2]) (by bsimp [h20])
    (w := R0 21) (sv.get 21 40) ?_
  intro R1 M1 H1 F1 L1 hk1 h21 hkf hb1 ho1
  cases hkf with
  | dec h => omega
  | rel _ =>
    have sv1 : SavedWords M1 (sp - 96) raSlots1 R0 := fun p hp => by
      rw [ldv_congr .ld fun j hj => ho1 _ (by
        have := (show ∀ p ∈ raSlots1, 16 ≤ p.2 ∧ p.2 + 8 ≤ 96 by decide) p hp
        simp only [widthOfM] at hj
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)]
      exact sv p (List.mem_cons_of_mem _ hp)
    refine ra_freePow0 hlive cx (L1 := Y) (L2 := L) hb1 hPo
      (fun y hy => hb1.owner_db_ne hPo hy (hY y hy)) (by omega)
      ⟨by rw [hk1.get 2]; bsimp [h2], sv1,
        (hk1.mono (ks' := raAll) (by decide)).trans (by keeps_tac ra.keep),
        by rw [hk1.get 23]; bsimp [ra.r23], fun _ _ _ => rfl⟩
      h21 (by rw [hk1.get 18]; bsimp []) ?_
    intro R3 M3 H3 F3 L3 hk3 hkf3 hb3 ho3
    cases hkf3 with
    | dec h => omega
    | rel _ => exact hk R3 M3 _ _ hk3 hb3 fun a ha => (ho3 a ha).trans (ho1 a ha)

/-- **The negative exponent's tail** from `0x80006744`: `bc_divide (_one_,
temp, result, rscale)`, then `temp` and `power` (`T`, `P`, fresh) released;
the quotient (or, `temp` zero, the old number) is the result. -/
theorem ra_neg2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L0 : List NumObj} {x1 x2 z o xr T P : NumObj} {n : Num}
    (cx : RaCtx S R0 sp W q) (hK : RaK live S Q t R0 Mt0 L0 xr q sp W n)
    (ha : RaArgs S Mt0 L0 x1 x2 z o k) (hs : RaSlot M L0 x1 x2 z o xr q)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots2) (hb : BcHeap S M H F (T :: P :: L0))
    (hT1 : T.rep.refs = 1) (hP1 : P.rep.refs = 1) (hTo : T.Owns) (hPo : P.Owns)
    (hzT : T.rep.num.mag = 0 → x1.rep.num.mag = 0 ∧ raExp x2 < 0)
    (hsz : o.rep.len + o.rep.scale + k + T.rep.len + T.rep.scale < 2 ^ 27)
    (hn : n = (Num.div Num.one T.rep.num k).getD (Num.zero 0))
    (h20 : R 20 = BitVec.ofNat 64 T.rep.p) (h22 : R 22 = BitVec.ofNat 64 k)
    (hwP : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 P.rep.p) :
    DW live S (DQ live S Q t) 0x80006744#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hone : ldv .ld M oneAddr = BitVec.ofNat 64 o.rep.p := by
    rw [ldv_congr .ld fun j hj => ra.out _ (constBytes_out (by
      simp only [widthOfM, constBytes, twoAddr, zeroAddr, oneAddr] at hj ⊢; omega))
      (by simp only [frameIn, widthOfM, oneAddr, zeroAddr] at hj ⊢; omega)]
    exact ha.one
  have hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p := by
    rw [ldv_congr .ld fun j hj => ra.out _ (constBytes_out (by
      simp only [widthOfM, constBytes, twoAddr, zeroAddr, oneAddr] at hj ⊢; omega))
      (by simp only [frameIn, widthOfM, oneAddr, zeroAddr] at hj ⊢; omega)]
    exact ha.zero.glob
  have hcst : ∀ b ∈ accAddrs oneAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have hzm : z.rep.num.mag = 0 := by rw [NumRep.num_mag, ha.zero.ds]; rfl
  have hTx : T ≠ xr := fun e => hb.p_ne (List.mem_cons_of_mem _ hs.mr) (by rw [e])
  have hmo := ha.mo; have hmz := ha.mz
  have hoN := ha.oneNum
  have hown := ha.owns
  obtain ⟨X1, X2, rfl⟩ := List.append_of_mem hs.mr
  have h2 := ra.r2
  bc_run hlive hS [h2, h20, h22, ra.r23, hone] at 0x8000589c
  all_goals first | exact hcst | skip
  refine ra_divCall (L1 := T :: P :: X1) (L2 := X2) (x1 := o) (x2 := T) (z := z) (k := k)
    (n := Num.div o.rep.num T.rep.num k) hlive cx hK.oom ra.out
    ⟨rfl, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmo), List.mem_cons_self,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmz),
      fun h1 => ⟨fun e => by have := hs.oneRef e.symm; omega, hTx,
        fun e => by have := hs.zeroRef e.symm; omega⟩, hsz, hzg, ha.oneLen⟩
    hzm hb ⟨hs.rr, hs.wr, fun _ hxo y hy => hb.owner_db_ne (P := T :: P :: X1) hxo hy (by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hTo
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hPo
      exact hown y (List.mem_append_left _ hy))⟩
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
    ?_ ?_
  · intro m hm R1 M1 H1 F1 L1 y hk1 hp
    obtain ⟨L0', rfl, hfr⟩ := FreedRest.unpre (P := [T, P]) (X1 := X1) hp.rest
    have hb1 := hp.heap
    have hyp : y.rep.p = y.sb.pay := (hb1.blocks y List.mem_cons_self).sPay
    have hag : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M1 a = imgM M a :=
      fun a h1 h2 h3 => hp.out a h1 h2 (fun h => h3 (by simp only [frameIn] at h ⊢; omega))
    bsimp []
    refine ra_negFree hlive cx (Y := [y]) hb1 (by simp only [List.mem_singleton]; rintro _ rfl; exact hp.owns)
      hT1 hP1 hTo hPo
      ⟨by rw [hk1.get 2]; bsimp [h2],
        ra.saved.transport (lo := 16) (top := 96) (hag := fun a h1 h2 => hp.out a
          (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)),
        (hk1.mono (ks' := raAll) (by decide)).trans (by keeps_tac ra.keep),
        by rw [hk1.get 23]; bsimp [ra.r23], fun _ _ _ => rfl⟩
      (by rw [hk1.get 20]; bsimp [h20])
      (by rw [ldv_congr .ld fun j hj => hp.out _
            (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
            (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
            (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
          exact hwP) ?_
    intro R3 M3 H3 F3 hk3 hb3 ho3
    refine hK.ret R3 M3 H3 F3 _ y hk3 (raPost_fresh hb3 hfr hp.refs ?_ hp.norm hp.pos hp.owns ?_ ?_)
    · rw [hp.num, hn, ← hoN, hm]; rfl
    · rw [ldv_congr .ld fun j hj => ho3 _ (hsl.out _ (by simp only [widthOfM] at hj; omega)), hp.slot, hyp]
    · intro a h1 h2 h3
      rw [ho3 a h1, hag a h1 h2 h3]
      exact ra.out a h1 h3
  · intro hn0 R1 M1 hk1 hf1
    have hT0 : T.rep.num.mag = 0 := by
      unfold Num.div at hn0
      split at hn0
      · rename_i h0; simpa using h0
      · simp at hn0
    obtain ⟨hz1, hz2⟩ := hzT hT0
    obtain ⟨hxn, hxN, hxl⟩ := hs.zr hz1 hz2
    have hag : ∀ a, ¬ frameIn sp W a → imgM M1 a = imgM M a :=
      fun a h3 => hf1 a (fun h => h3 (by simp only [frameIn] at h ⊢; omega))
    bsimp []
    refine ra_negFree hlive cx (Y := []) (T := T) (P := P) (L := X1 ++ xr :: X2)
      (hb.out_frame (P := frameIn (sp - 96) (W - 96)) hf1 fun a ha => by
        simp only [frameIn] at ha; simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp) hT1 hP1 hTo hPo
      ⟨by rw [hk1.get 2]; bsimp [h2],
        ra.saved.transport (lo := 16) (top := 96) (hag := fun a h1 h2 => hf1 a
          (by simp only [frameIn]; omega)),
        (hk1.mono (ks' := raAll) (by decide)).trans (by keeps_tac ra.keep),
        by rw [hk1.get 23]; bsimp [ra.r23], fun _ _ _ => rfl⟩
      (by rw [hk1.get 20]; bsimp [h20])
      (by rw [ldv_congr .ld fun j hj => hf1 _ (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
          exact hwP) ?_
    intro R3 M3 H3 F3 hk3 hb3 ho3
    refine hK.ret R3 M3 H3 F3 _ _ hk3 (raPost_keep hb3 hs.mr hs.rr ?_ hxN hxl
      (hown xr hs.mr) ?_ ?_)
    · rw [hn, ← hoN, hn0]; exact hxn
    · rw [ldv_congr .ld fun j hj => ho3 _ (hsl.out _ (by simp only [widthOfM] at hj; omega)),
        ldv_congr .ld fun j hj => hag _ (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
      exact hs.wr
    · intro a h1 h2 h3
      rw [ho3 a h1, hag a h3]
      exact ra.out a h1 h3

end Dc.Mach
