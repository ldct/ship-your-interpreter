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

/-! ## The positive exponent's result -/

/-- `y` cut to the scale `k` when it has more (`MIN (…, rscale)`). -/
def NumObj.cutTo (k : Nat) (y : NumObj) : NumObj :=
  if k < y.rep.scale then { y with rep := y.rep.cutScale k } else y

theorem NumObj.cutTo_p (k : Nat) (y : NumObj) : (y.cutTo k).rep.p = y.rep.p := by
  unfold NumObj.cutTo; split <;> rfl

theorem NumObj.cutTo_refs (k : Nat) (y : NumObj) : (y.cutTo k).rep.refs = y.rep.refs := by
  unfold NumObj.cutTo; split <;> rfl

theorem NumObj.cutTo_len (k : Nat) (y : NumObj) : (y.cutTo k).rep.len = y.rep.len := by
  unfold NumObj.cutTo; split <;> rfl

theorem NumObj.cutTo_owns {k : Nat} {y : NumObj} (h : y.Owns) : (y.cutTo k).Owns := by
  unfold NumObj.cutTo; split
  · exact h
  · exact h

/-- The cut number's value: the magnitude truncated to `k` places. -/
theorem NumObj.cutTo_num {k : Nat} {y : NumObj} (hs : NumShape y.rep) (hk : k ≤ y.rep.scale) :
    (y.cutTo k).rep.num = ⟨y.rep.num.neg, y.rep.num.mag / 10 ^ (y.rep.scale - k), k⟩ := by
  unfold NumObj.cutTo; split
  · exact NumRep.cutScale_num hs (by omega)
  · have e : k = y.rep.scale := by omega
    subst e
    simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
    rfl

theorem NumObj.cutTo_norm {k : Nat} {y : NumObj} (hn : y.rep.Norm) (hl : 1 ≤ y.rep.len) :
    (y.cutTo k).rep.Norm := by
  unfold NumObj.cutTo; split
  · exact NumRep.cutScale_norm hn hl k
  · exact hn

/-- Every number of `T :: P :: X` owns its digits. -/
theorem owns_cons2 {T P : NumObj} {X : List NumObj} (hT : T.Owns) (hP : P.Owns)
    (h : ∀ y ∈ X, y.Owns) : ∀ y ∈ T :: P :: X, y.Owns := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hT
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hP
  exact h y hy

/-- **`*result = temp`, `temp` cut to `rscale`** from `0x80006898` (`temp`
in `s4`, `rscale` in `s6`, the slot in `s7`); `power` reloaded into `s2`. -/
theorem ra_store {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {Ya Yb : List NumObj} {y : NumObj} {pw : BitVec 64} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S M H F (Ya ++ y :: Yb)) (hk31 : k < 2 ^ 31)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (h20 : R 20 = BitVec.ofNat 64 y.rep.p)
    (h22 : R 22 = BitVec.ofNat 64 k) (h23 : R 23 = BitVec.ofNat 64 q)
    (hwP : ldv .ld M (sp - 96 + 8) = pw)
    (hk : ∀ R' M', Keeps [15, 18] R' R → R' 18 = pw → BcHeap S M' H F (Ya ++ y.cutTo k :: Yb) →
      ldv .ld M' q = BitVec.ofNat 64 y.rep.p →
      (∀ a, OutHeap a → ¬ slotBytes q a → imgM M' a = imgM M a) → DW live S Q 0x80006798#64 R' M') :
    DW live S Q 0x80006898#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hym : y ∈ Ya ++ y :: Yb := List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums y hym
  num_facts hn
  have hsc := hn.scale
  have hb1 := hb.out_frame (P := slotBytes q) (MemOnly.store M q 8 (BitVec.ofNat 64 y.rep.p)) hsl.out
  have hsz := hn.shape.size
  have hq0 := hsl.out q ⟨Nat.le_refl _, by omega⟩
  have hq7 := hsl.out (q + 7) ⟨by omega, by omega⟩
  simp only [OutHeap, heapStart, heapEnd] at hq0 hq7
  bc_run hlive hS [h2, h20, h22, h23, hsc]
  all_goals first | exact hq.acc | skip
  · exact frame_acc hsf (by omega) (by omega)
  · intro hge
    rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hge
    have hc : y.cutTo k = y := by
      simp only [NumObj.cutTo, show ¬ k < y.rep.scale by omega, ite_false]
    refine hk _ _ (by keeps_tac Keeps.refl _ _)
      (by bsimp [hwP]; rw [ldv_ld_miss _ _ (by omega)]; exact hwP) (by rw [hc]; exact hb1)
      (ldv_store_hit _ _ _) fun a _ hs => imgM_store_miss _ _ (by simp only [slotBytes] at hs; omega)
  · intro hlt
    rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hlt
    have hc : y.cutTo k = { y with rep := y.rep.cutScale k } := by
      simp only [NumObj.cutTo, show k < y.rep.scale by omega, ite_true]
    bc_run hlive hS [h20, h22] at 0x80006798
    all_goals first | exact acc_heap hS (by omega) (by omega) | skip
    refine hk _ _ (by keeps_tac Keeps.refl _ _)
      (by bsimp [hwP])
      (by rw [hc]; exact hb1.setScale (toNat_ofNat_mod32 (by omega)) (by omega))
      (by rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _) fun a ha hs => ?_
    simp only [slotBytes] at hs
    simp only [OutHeap, heapStart, heapEnd] at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]

/-- **`bc_free_num (result)`** from `bc_raise`'s frame (`sp - 96`, `a0` the
slot), returning to `ra`. -/
theorem ra_freeSlot {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {xr : NumObj} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (h10 : R 10 = BitVec.ofNat 64 q)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L', Keeps freeNumClob R' R → FreedRest L1 L2 xr L' →
      BcHeap S M' H' F' L' →
      (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn (sp - 96) 32 a → imgM M' a = imgM M a) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x800048c0#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hxm : xr ∈ L1 ++ xr :: L2 := List.mem_append_right _ List.mem_cons_self
  have hxn := hb.nums xr hxm
  have hxp' : heapStart ≤ xr.rep.p ∧ xr.rep.p + 16 ≤ heapEnd :=
    ⟨hxn.shape.pLo, by have := hxn.shape.pHi; omega⟩
  have hsf' : StackFrame S (sp - 96) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  have e : FreeEntry S M H F L1 L2 xr q (sp - 96) :=
    FreeEntry.of_slot hb hr hr.noView hq hsl.out hsf' (by simp only [heapEnd]; omega) (by omega)
  refine bc_free_num_spec hlive e R h10 h2 hal
    ⟨fun hx2 R1 Mt1 hk1 hb1 _ hmo => ?_, fun hx1 R1 Mt1 H1 hk1 hrp => ?_⟩
  · refine hk R1 Mt1 H F _ hk1 (.dec hx2) hb1 fun a ha hs _ => hmo a fun hc => ?_
    rcases hc with hc | hc
    · simp only [refsBytes, OutHeap, heapStart, heapEnd] at hc ha hxp'; omega
    · exact hs hc
  · refine hk R1 Mt1 H1 (xr.sb :: F) _ hk1 (.rel hx1) hrp.heap fun a ha hs hf => hrp.frame a fun hc => ?_
    rcases hc with hc | hc | hc | hc | hc
    · exact OutHeap.not_alloc hb.heap ha hc
    · exact ha.1 (live_in_heap hb.heap (hb.blocks xr hxm).sLive hc)
    · exact hs hc
    · exact hf hc
    · exact ha.2.2 hc

/-- **`bc_free_num (result)`** from `0x80006890` (`s7` the slot). -/
theorem ra_posFree {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {xr : NumObj} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (h23 : R 23 = BitVec.ofNat 64 q)
    (hk : ∀ R' M' H' F' L', Keeps [1, 10, 13, 14, 15] R' R → FreedRest L1 L2 xr L' →
      BcHeap S M' H' F' L' →
      (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn (sp - 96) 32 a → imgM M' a = imgM M a) →
      DW live S Q 0x80006898#64 R' M') :
    DW live S Q 0x80006890#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  bc_run hlive hS [h23, h2] at 0x800048c0
  refine ra_freeSlot hlive cx hb hr (by bsimp [h2]) (by bsimp [h23]) (by bsimp []; try decide)
    fun R1 M1 H1 F1 L1 hk1 hfr hb1 ho1 => ?_
  bsimp [hk1.get 1]
  exact hk R1 M1 H1 F1 L1 ((hk1.mono (ks' := [1, 10, 13, 14, 15]) (by decide)).trans
    (by keeps_tac Keeps.refl _ _)) hfr hb1 ho1

/-- **The positive exponent's tail** from `0x8000688c`: `bc_free_num
(result)`, `*result = temp` (`T`) cut to `rscale` (`k`), `power` (`P`)
released; both fresh. -/
theorem ra_pos2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L0 : List NumObj} {x1 x2 z o xr T P : NumObj} {n : Num}
    (cx : RaCtx S R0 sp W q) (hK : RaK live S Q t R0 Mt0 L0 xr q sp W n)
    (hs : RaSlot M L0 x1 x2 z o xr q) (hown : ∀ y ∈ L0, y.Owns)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots2) (hb : BcHeap S M H F (T :: P :: L0))
    (hT1 : T.rep.refs = 1) (hP1 : P.rep.refs = 1) (hTo : T.Owns) (hPo : P.Owns)
    (hTN : T.rep.Norm) (hTl : 1 ≤ T.rep.len) (hkT : k ≤ T.rep.scale) (hk31 : k < 2 ^ 31)
    (hn : n = ⟨T.rep.num.neg, T.rep.num.mag / 10 ^ (T.rep.scale - k), k⟩)
    (h20 : R 20 = BitVec.ofNat 64 T.rep.p) (h22 : R 22 = BitVec.ofNat 64 k)
    (hwP : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 P.rep.p) :
    DW live S (DQ live S Q t) 0x8000688c#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have sv := ra.saved
  have hTs := (hb.nums T List.mem_cons_self).shape
  obtain ⟨X1, X2, rfl⟩ := List.append_of_mem hs.mr
  have h2 := ra.r2
  bc_run hlive hS [h2, sv.get 21 40] at 0x80006890
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine ra_posFree hlive cx (L1 := T :: P :: X1) (L2 := X2) hb
    ⟨hs.rr, hs.wr, fun _ hxo y hy => hb.owner_db_ne (P := T :: P :: X1) hxo hy
      (owns_cons2 hTo hPo (fun y hy => hown y (List.mem_append_left _ hy)) y hy)⟩
    (by bsimp [h2]) (by bsimp [ra.r23]) ?_
  intro R1 M1 H1 F1 L1 hk1 hfr hb1 ho1
  obtain ⟨L0', rfl, hfr'⟩ := FreedRest.unpre (P := [T, P]) (X1 := X1) hfr
  refine ra_store hlive cx (Ya := []) (y := T) (Yb := P :: L0') (pw := BitVec.ofNat 64 P.rep.p) hb1 hk31
    (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 20]; bsimp [h20])
    (by rw [hk1.get 22]; bsimp [h22]) (by rw [hk1.get 23]; bsimp [ra.r23])
    (by rw [ldv_congr .ld fun j hj => ho1 _
          (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
        exact hwP) ?_
  intro R2 M2 hk2 h18 hb2 hq2 ho2
  have sv2 : SavedWords M2 (sp - 96) raSlots1 R0 := fun p hp => by
    have hb' := (show ∀ p ∈ raSlots1, 16 ≤ p.2 ∧ p.2 + 8 ≤ 96 by decide) p hp
    have e : ∀ j, j < widthOfM .ld → imgM M2 (sp - 96 + p.2 + j) = imgM M (sp - 96 + p.2 + j) :=
      fun j hj => by
        simp only [widthOfM] at hj
        exact (ho2 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [slotBytes]; omega)).trans
          (ho1 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
            (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega))
    rw [ldv_congr .ld e]
    exact sv p (List.mem_cons_of_mem _ hp)
  have hT' : (T.cutTo k).Owns := NumObj.cutTo_owns hTo
  refine ra_freePow0 hlive cx (L1 := [T.cutTo k]) (x := P) (L2 := L0') hb2 hPo
    (fun y hy => by
      rw [List.mem_singleton.mp hy]
      exact hb2.owner_db_ne (P := [T.cutTo k]) hPo List.mem_cons_self hT') (by omega)
    ⟨by rw [hk2.get 2, hk1.get 2]; bsimp [h2], sv2,
      (hk2.mono (ks' := raAll) (by decide)).trans ((hk1.mono (ks' := raAll) (by decide)).trans
        (by keeps_tac ra.keep)),
      by rw [hk2.get 23, hk1.get 23]; bsimp [ra.r23], fun _ _ _ => rfl⟩
    (by rw [hk2.get 21, hk1.get 21]; bsimp []) h18 ?_
  intro R3 M3 H3 F3 L3 hk3 hkf hb3 ho3
  cases hkf with
  | dec h => omega
  | rel _ =>
    refine hK.ret R3 M3 _ _ _ _ hk3 (raPost_fresh hb3 hfr' (by rw [NumObj.cutTo_refs]; exact hT1)
      (by rw [NumObj.cutTo_num hTs hkT, hn]) (NumObj.cutTo_norm hTN hTl)
      (by rw [NumObj.cutTo_len]; exact hTl) hT' ?_ ?_)
    · rw [ldv_congr .ld fun j hj => ho3 _ (hsl.out _ (by simp only [widthOfM] at hj; omega)), hq2,
        NumObj.cutTo_p]
    · intro a h1 h2' h3
      rw [ho3 a h1, ho2 a h1 h2', ho1 a h1 h2' (fun h => h3 (by simp only [frameIn] at h ⊢; omega))]
      exact ra.out a h1 h3

/-! ## `temp` and `power` the same number (a power of two) -/

/-- Dropping `x` of `L1 ++ x :: L2 = A ++ w :: B`: at another position than
`w` (`w` kept, any number in its place dropped the same way), or at `w`'s. -/
theorem FreedRest.around {L1 L2 A B L' : List NumObj} {x w : NumObj} (h : FreedRest L1 L2 x L')
    (he : L1 ++ x :: L2 = A ++ w :: B) :
    (∃ A' B', L' = A' ++ w :: B' ∧ (∀ w2, DropAt (A ++ w2 :: B) x.rep.p (A' ++ w2 :: B')) ∧
      DropAt (A ++ B) x.rep.p (A' ++ B')) ∨
    (x = w ∧ L1 = A ∧ L2 = B) := by
  rcases List.append_eq_append_iff.mp he with ⟨a', rfl, h2⟩ | ⟨c', rfl, h2⟩
  · cases a' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact .inr ⟨rfl, by simp, rfl⟩
    | cons a a'' =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      left
      cases h with
      | dec h3 =>
        exact ⟨L1 ++ x.decRef :: a'', B, by simp, fun w2 =>
          ⟨L1, a'' ++ w2 :: B, x, by simp, rfl, by rw [List.append_assoc]; exact .dec h3⟩,
          ⟨L1, a'' ++ B, x, by simp, rfl, by rw [List.append_assoc]; exact .dec h3⟩⟩
      | rel h3 =>
        exact ⟨L1 ++ a'', B, by simp, fun w2 =>
          ⟨L1, a'' ++ w2 :: B, x, by simp, rfl, by rw [List.append_assoc]; exact .rel h3⟩,
          ⟨L1, a'' ++ B, x, by simp, rfl, by rw [List.append_assoc]; exact .rel h3⟩⟩
  · cases c' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact .inr ⟨rfl, by simp, rfl⟩
    | cons c c'' =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      left
      cases h with
      | dec h3 =>
        exact ⟨A, c'' ++ x.decRef :: L2, by simp, fun w2 =>
          ⟨A ++ w2 :: c'', L2, x, by simp, rfl, by
            rw [show A ++ w2 :: (c'' ++ x.decRef :: L2) = (A ++ w2 :: c'') ++ x.decRef :: L2 by simp]
            exact .dec h3⟩,
          ⟨A ++ c'', L2, x, by simp, rfl, by
            rw [show A ++ (c'' ++ x.decRef :: L2) = (A ++ c'') ++ x.decRef :: L2 by simp]
            exact .dec h3⟩⟩
      | rel h3 =>
        exact ⟨A, c'' ++ L2, by simp, fun w2 =>
          ⟨A ++ w2 :: c'', L2, x, by simp, rfl, by
            rw [show A ++ w2 :: (c'' ++ L2) = (A ++ w2 :: c'') ++ L2 by simp]
            exact .rel h3⟩,
          ⟨A ++ c'', L2, x, by simp, rfl, by
            rw [show A ++ (c'' ++ L2) = (A ++ c'') ++ L2 by simp]
            exact .rel h3⟩⟩

theorem DropAt.cons {L L' : List NumObj} {p : Nat} (y : NumObj) (h : DropAt L p L') :
    DropAt (y :: L) p (y :: L') := by
  obtain ⟨L1, L2, x, rfl, hp, hf⟩ := h
  exact ⟨y :: L1, L2, x, rfl, hp, hf.pre [y]⟩

theorem NumObj.cutTo_withRefs (k j : Nat) (y : NumObj) :
    (y.withRefs j).cutTo k = (y.cutTo k).withRefs j := by
  unfold NumObj.cutTo NumObj.withRefs; split <;> rfl

/-- **The positive tail with `temp` = `power`** (`w`, two references more
than its base) from `0x80006890`: `bc_free_num (result)` (`xs`, possibly
`w` itself), `*result = w` cut to `rscale`, one reference of `w` dropped. The
result is `w` with one reference more than its base, `hadd`. -/
theorem ra_posPow2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L0 A B L1 L2 : List NumObj} {w xs xr : NumObj} {n : Num}
    (cx : RaCtx S R0 sp W q) (hK : RaK live S Q t R0 Mt0 L0 xr q sp W n)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots1) (h21 : R 21 = R0 21)
    (hb : BcHeap S M H F (A ++ w :: B)) (hown : ∀ y ∈ A ++ w :: B, y.Owns)
    (he : L1 ++ xs :: L2 = A ++ w :: B) (hr : ResSlot M L1 xs q) (hxp : xs.rep.p = xr.rep.p)
    (hw2 : 2 ≤ w.rep.refs) (hsame : xs = w → 3 ≤ w.rep.refs)
    (hwN : w.rep.Norm) (hwl : 1 ≤ w.rep.len) (hkw : k ≤ w.rep.scale) (hk31 : k < 2 ^ 31)
    (hadd : AddRef L0 ((w.cutTo k).withRefs (w.rep.refs - 1))
      (A ++ (w.cutTo k).withRefs (w.rep.refs - 1) :: B))
    (hn : n = ⟨w.rep.num.neg, w.rep.num.mag / 10 ^ (w.rep.scale - k), k⟩)
    (h20 : R 20 = BitVec.ofNat 64 w.rep.p) (h22 : R 22 = BitVec.ofNat 64 k)
    (hwP : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 w.rep.p) :
    DW live S (DQ live S Q t) 0x80006890#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have sv := ra.saved
  have h2 := ra.r2
  have hws := (hb.nums w (List.mem_append_right _ List.mem_cons_self)).shape
  have hyn : ((w.cutTo k).withRefs (w.rep.refs - 1)).rep.num = n := by
    rw [hn, ← NumObj.cutTo_num hws hkw]; rfl
  have hyN : ((w.cutTo k).withRefs (w.rep.refs - 1)).rep.Norm := NumObj.cutTo_norm hwN hwl
  have hyl : 1 ≤ ((w.cutTo k).withRefs (w.rep.refs - 1)).rep.len := by
    show 1 ≤ (w.cutTo k).rep.len; rw [NumObj.cutTo_len]; exact hwl
  have hyo : ((w.cutTo k).withRefs (w.rep.refs - 1)).Owns :=
    NumObj.cutTo_owns (hown w (List.mem_append_right _ List.mem_cons_self))
  have hyp : ((w.cutTo k).withRefs (w.rep.refs - 1)).rep.p = w.rep.p := NumObj.cutTo_p k w
  have hb0 : BcHeap S M H F (L1 ++ xs :: L2) := he ▸ hb
  have hown0 : ∀ y ∈ L1 ++ xs :: L2, y.Owns := he ▸ hown
  refine ra_posFree hlive cx hb0 hr (by bsimp [h2]) ra.r23 ?_
  intro R1 M1 H1 F1 L' hk1 hfr hb1 ho1
  have hwP1 : ldv .ld M1 (sp - 96 + 8) = BitVec.ofNat 64 w.rep.p := by
    rw [ldv_congr .ld fun j hj => ho1 _
      (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
      (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact hwP
  have hsv : ∀ {M2 : Mem}, (∀ a, OutHeap a → ¬ slotBytes q a → imgM M2 a = imgM M1 a) →
      SavedWords M2 (sp - 96) raSlots1 R0 := fun {M2} ho2 p hp => by
    have hb' := (show ∀ p ∈ raSlots1, 16 ≤ p.2 ∧ p.2 + 8 ≤ 96 by decide) p hp
    have e : ∀ j, j < widthOfM .ld → imgM M2 (sp - 96 + p.2 + j) = imgM M (sp - 96 + p.2 + j) :=
      fun j hj => by
        simp only [widthOfM] at hj
        exact (ho2 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [slotBytes]; omega)).trans
          (ho1 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
            (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega))
    rw [ldv_congr .ld e]
    exact sv p hp
  have hout : ∀ {M2 M3 : Mem}, (∀ a, OutHeap a → ¬ slotBytes q a → imgM M2 a = imgM M1 a) →
      (∀ a, OutHeap a → imgM M3 a = imgM M2 a) →
      ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M3 a = imgM Mt0 a :=
    fun ho2 ho3 a h1 h2' h3 => by
      rw [ho3 a h1, ho2 a h1 h2', ho1 a h1 h2' (fun h => h3 (by simp only [frameIn] at h ⊢; omega))]
      exact ra.out a h1 h3
  have hslot : ∀ {M2 M3 : Mem}, ldv .ld M2 q = BitVec.ofNat 64 w.rep.p →
      (∀ a, OutHeap a → imgM M3 a = imgM M2 a) →
      ldv .ld M3 q = BitVec.ofNat 64 ((w.cutTo k).withRefs (w.rep.refs - 1)).rep.p :=
    fun hq2 ho3 => by
      rw [ldv_congr .ld fun j hj => ho3 _ (hsl.out _ (by simp only [widthOfM] at hj; omega)), hq2, hyp]
  rcases hfr.around he with ⟨A', B', rfl, hdrop, -⟩ | ⟨rfl, rfl, rfl⟩
  · refine ra_store hlive cx (Ya := A') (y := w) (Yb := B') (pw := BitVec.ofNat 64 w.rep.p) hb1 hk31
      (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 20]; bsimp [h20])
      (by rw [hk1.get 22]; bsimp [h22]) (by rw [hk1.get 23]; bsimp [ra.r23]) hwP1 ?_
    intro R2 M2 hk2 h18 hb2 hq2 ho2
    have hown2 : ∀ y ∈ A' ++ w.cutTo k :: B', y.Owns := by
      intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact hfr.owns hown0 y (List.mem_append_left _ h)
      rcases List.mem_cons.mp h with rfl | h
      · exact NumObj.cutTo_owns (hown w (List.mem_append_right _ List.mem_cons_self))
      exact hfr.owns hown0 y (List.mem_append_right _ (List.mem_cons_of_mem _ h))
    refine ra_freePow0 hlive cx (L1 := A') (x := w.cutTo k) (L2 := B') hb2
      (hown2 _ (List.mem_append_right _ List.mem_cons_self))
      (fun y hy => hb2.owner_db_ne (hown2 _ (List.mem_append_right _ List.mem_cons_self)) hy
        (hown2 y (List.mem_append_left _ hy)))
      (by rw [NumObj.cutTo_refs]; omega)
      ⟨by rw [hk2.get 2, hk1.get 2]; bsimp [h2], hsv ho2,
        (hk2.mono (ks' := raAll) (by decide)).trans ((hk1.mono (ks' := raAll) (by decide)).trans
          ra.keep),
        by rw [hk2.get 23, hk1.get 23]; bsimp [ra.r23], fun _ _ _ => rfl⟩
      (by rw [hk2.get 21, hk1.get 21]; exact h21) (by rw [h18, NumObj.cutTo_p]) ?_
    intro R3 M3 H3 F3 L3 hk3 hkf hb3 ho3
    cases hkf with
    | rel h => rw [NumObj.cutTo_refs] at h; omega
    | dec _ =>
      have e : (w.cutTo k).decRef = (w.cutTo k).withRefs (w.rep.refs - 1) := by
        rw [NumObj.decRef_eq, NumObj.cutTo_refs]
      rw [e] at hb3
      refine hK.ret R3 M3 _ _ _ _ hk3 ⟨hb3, ⟨_, hadd, hxp ▸ hdrop _⟩, hyn, hyN, hyl, hyo,
        hslot hq2 ho3, hout ho2 ho3⟩
  · cases hfr with
    | rel h => have := hsame rfl; omega
    | dec _ =>
      refine ra_store hlive cx (Ya := L1) (y := xs.decRef) (Yb := L2)
        (pw := BitVec.ofNat 64 xs.rep.p) hb1 hk31
        (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 20]; bsimp [h20]; rfl)
        (by rw [hk1.get 22]; bsimp [h22]) (by rw [hk1.get 23]; bsimp [ra.r23]) hwP1 ?_
      intro R2 M2 hk2 h18 hb2 hq2 ho2
      have hx3 := hsame rfl
      have hxo : (xs.decRef.cutTo k).Owns :=
        NumObj.cutTo_owns (hown xs (List.mem_append_right _ List.mem_cons_self))
      have hown2 : ∀ y ∈ L1, y.Owns := fun y hy => hown y (List.mem_append_left _ hy)
      refine ra_freePow0 hlive cx (L1 := L1) (x := xs.decRef.cutTo k) (L2 := L2) hb2 hxo
        (fun y hy => hb2.owner_db_ne hxo hy (hown2 y hy))
        (by rw [NumObj.cutTo_refs]; simp only [NumObj.decRef]; omega)
        ⟨by rw [hk2.get 2, hk1.get 2]; bsimp [h2], hsv ho2,
          (hk2.mono (ks' := raAll) (by decide)).trans ((hk1.mono (ks' := raAll) (by decide)).trans
            ra.keep),
          by rw [hk2.get 23, hk1.get 23]; bsimp [ra.r23], fun _ _ _ => rfl⟩
        (by rw [hk2.get 21, hk1.get 21]; exact h21) (by rw [h18, NumObj.cutTo_p]; rfl) ?_
      intro R3 M3 H3 F3 L3 hk3 hkf hb3 ho3
      cases hkf with
      | rel h => rw [NumObj.cutTo_refs] at h; simp only [NumObj.decRef] at h; omega
      | dec _ =>
        have e : (xs.decRef.cutTo k).decRef = ((xs.cutTo k).withRefs (xs.rep.refs - 1)).decRef := by
          rw [NumObj.decRef_eq, NumObj.decRef_eq, NumObj.decRef_eq, NumObj.cutTo_withRefs]
        rw [e] at hb3
        refine hK.ret R3 M3 _ _ _ _ hk3 ⟨hb3, ⟨_, hadd, L1, L2, _, rfl, hyp.trans hxp,
          .dec (by simp only [NumObj.withRefs]; omega)⟩, hyn, hyN, hyl, hyo,
          hslot (by rw [hq2]; rfl) ho3, hout ho2 ho3⟩

/-- **`temp`'s reference dropped** at `0x800068ec` (`temp` = `power` = `v` in
`s2`, two references or more), then `bc_free_num (&power)`. -/
theorem ra_negDec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {P1 P2 : List NumObj} {v : NumObj} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S M H F (P1 ++ v :: P2)) (ho : v.Owns) (hnv : ∀ y ∈ P1, y.db ≠ v.db)
    (hr : 2 ≤ v.rep.refs) (ra : RaAt S M M R0 R sp W q raSlots1) (h21 : R 21 = R0 21)
    (h18 : R 18 = BitVec.ofNat 64 v.rep.p) (hk : RaFreeK live S Q R0 M H F P1 P2 v.decRef) :
    DW live S Q 0x800068ec#64 R M := by
  ra_facts cx
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn := hb.nums v (List.mem_append_right _ List.mem_cons_self)
  num_facts hn
  have hrf := hn.refs
  have hpr : BitVec.ofNat 64 v.rep.refs + 18446744073709551615#64 =
      BitVec.ofNat 64 (v.rep.refs - 1) := word_pred (by omega)
  have hsx : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (v.rep.refs - 1))) =
      BitVec.ofNat 64 (v.rep.refs - 1) := sxw_ofNat (by omega)
  bc_run hlive hS [h18, hrf, hpr, hsx] at 0x8000679c 0x800068fc
  all_goals try (intro hc; first
    | exact absurd ((ofNat_eq_iff (x := v.rep.refs - 1) (y := 0) (by omega) (by omega)).mp hc) (by omega)
    | exact absurd ((ofNat_eq_iff (x := v.rep.refs - 1) (y := 0) (by omega) (by omega)).mp
        (Classical.not_not.mp hc)) (by omega))
  intro _
  refine ra_freePow hlive cx (x := v.decRef) (hb.setRefs (toNat_ofNat_mod32 (by omega)) (by omega))
    ho hnv (by simp only [NumObj.decRef]; omega)
    ((ra.regs (by keeps_tac Keeps.refl _ _)).heapStore (a := v.rep.p + 12) (w := 4)
      (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega) (by simp only [heapEnd]; omega))
    (by bsimp [h21]) (by bsimp [h18]; rfl) fun R' M' H' F' L' hk' hf hb' ho' => ?_
  exact hk R' M' H' F' L' hk' hf hb' fun a ha => (ho' a ha).trans (imgM_store_miss _ _ (by
    simp only [OutHeap, heapStart, heapEnd] at ha; omega))

/-- **The negative tail with `temp` = `power`** (`w`, two references more
than in the caller's `L0`, or fresh with two) from `0x800068d4`:
`bc_divide (_one_, w, result, rscale)` (`o'`, `z'` the current `_one_`,
`_zero_`), then both references of `w` dropped. -/
theorem ra_negPow2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L0 A B L1 L2 : List NumObj} {w xs xr o' z' : NumObj} {n : Num}
    (cx : RaCtx S R0 sp W q) (hK : RaK live S Q t R0 Mt0 L0 xr q sp W n)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots1) (h21 : R 21 = R0 21)
    (hb : BcHeap S M H F (A ++ w :: B)) (hown : ∀ y ∈ A ++ w :: B, y.Owns)
    (he : L1 ++ xs :: L2 = A ++ w :: B) (hxr : 1 ≤ xs.rep.refs) (hxp : xs.rep.p = xr.rep.p)
    (hwq : ldv .ld M q = BitVec.ofNat 64 xr.rep.p)
    (hmr : xr ∈ L0) (hrr : 1 ≤ xr.rep.refs) (hxro : xr.Owns)
    (hzr : w.rep.num.mag = 0 → xr.rep.num = Num.zero 0 ∧ xr.rep.Norm ∧ 1 ≤ xr.rep.len)
    (ho1 : o' ∈ A ++ w :: B) (hon : o'.rep.num = Num.one) (hol : 1 ≤ o'.rep.len)
    (hone : ldv .ld M oneAddr = BitVec.ofNat 64 o'.rep.p)
    (hz1 : z' ∈ A ++ w :: B) (hzm : z'.rep.num.mag = 0)
    (hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z'.rep.p)
    (hapart : xs.rep.refs = 1 → o' ≠ xs ∧ z' ≠ xs)
    (hsz : o'.rep.len + o'.rep.scale + k + w.rep.len + w.rep.scale < 2 ^ 27)
    (hw2 : 2 ≤ w.rep.refs) (hsame : xs = w → 3 ≤ w.rep.refs)
    (hL0 : (3 ≤ w.rep.refs ∧ L0 = A ++ w.withRefs (w.rep.refs - 2) :: B) ∨
      (w.rep.refs = 2 ∧ L0 = A ++ B))
    (hn : n = (Num.div Num.one w.rep.num k).getD (Num.zero 0))
    (h18 : R 18 = BitVec.ofNat 64 w.rep.p) (h22 : R 22 = BitVec.ofNat 64 k) :
    DW live S (DQ live S Q t) 0x800068d4#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hcst : ∀ b ∈ accAddrs oneAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have h2 := ra.r2
  have hb0 : BcHeap S M H F (L1 ++ xs :: L2) := he ▸ hb
  have hown0 : ∀ y ∈ L1 ++ xs :: L2, y.Owns := he ▸ hown
  have hm : ∀ {y}, y ∈ A ++ w :: B → y ∈ L1 ++ xs :: L2 := fun h => he ▸ h
  have hwm : w ∈ A ++ w :: B := List.mem_append_right _ List.mem_cons_self
  have hwo := hown w hwm
  bc_run hlive hS [h2, h18, h22, ra.r23, hone] at 0x8000589c
  all_goals first | exact hcst | skip
  refine ra_divCall (L1 := L1) (L2 := L2) (x1 := o') (x2 := w) (z := z') (k := k)
    (n := Num.div o'.rep.num w.rep.num k) hlive cx hK.oom ra.out
    ⟨rfl, hm ho1, hm hwm, hm hz1,
      fun h1 => ⟨(hapart h1).1, fun e => by rw [← e] at h1; omega, (hapart h1).2⟩, hsz, hzg, hol⟩
    hzm hb0 ⟨hxr, by rw [hwq, hxp], fun _ hxo y hy =>
      hb0.owner_db_ne hxo hy (hown0 y (List.mem_append_left _ hy))⟩
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
    ?_ ?_
  · intro m hm' R1 M1 H1 F1 L' y hk1 hp
    have hb1 := hp.heap
    have hyp : y.rep.p = y.sb.pay := (hb1.blocks y List.mem_cons_self).sPay
    have hyo := hp.owns
    have raN : RaAt S M1 M1 R0 R1 sp W q raSlots1 :=
      ⟨by rw [hk1.get 2]; bsimp [h2],
        ra.saved.transport (lo := 16) (top := 96) (hag := fun a h1 h2 => hp.out a
          (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)),
        (hk1.mono (ks' := raAll) (by decide)).trans (by keeps_tac ra.keep),
        by rw [hk1.get 23]; bsimp [ra.r23], fun _ _ _ => rfl⟩
    have h21' : R1 21 = R0 21 := by rw [hk1.get 21]; bsimp [h21]
    have h18' : R1 18 = BitVec.ofNat 64 w.rep.p := by rw [hk1.get 18]; bsimp [h18]
    have hpost : ∀ {R3 M3 H3 F3 Lf}, Keeps binClob R3 R0 → BcHeap S M3 H3 F3 (y :: Lf) →
        DropAt (y :: L0) xr.rep.p (y :: Lf) → (∀ a, OutHeap a → imgM M3 a = imgM M1 a) →
        DW live S (DQ live S Q t) (R0 1) R3 M3 := fun hk3 hb3 hd ho3 =>
      hK.ret _ _ _ _ _ y hk3 ⟨hb3, ⟨_, .fresh hp.refs, hd⟩,
        by rw [hp.num, hn, ← hon, hm']; rfl, hp.norm, hp.pos, hyo,
        by rw [ldv_congr .ld fun j hj => ho3 _ (hsl.out _ (by simp only [widthOfM] at hj; omega)),
          hp.slot, hyp],
        fun a h1 h2' h3 => by
          rw [ho3 a h1, hp.out a h1 h2' (fun h => h3 (by simp only [frameIn] at h ⊢; omega))]
          exact ra.out a h1 h3⟩
    bsimp []
    rcases hp.rest.around he with ⟨A', B', rfl, hdrop, hdrop2⟩ | ⟨rfl, rfl, rfl⟩
    · have hown1 : ∀ y' ∈ y :: A', y'.Owns := by
        intro y' hy'
        rcases List.mem_cons.mp hy' with rfl | hy'
        · exact hyo
        · exact hp.rest.owns hown0 y' (List.mem_append_left _ hy')
      refine ra_negDec hlive cx (P1 := y :: A') (v := w) (P2 := B') hb1 hwo
        (fun y' hy' => hb1.owner_db_ne (P := y :: A') hwo hy' (hown1 y' hy')) hw2 raN h21' h18' ?_
      intro R3 M3 H3 F3 L3 hk3 hkf hb3 ho3
      cases hkf with
      | dec h =>
        rcases hL0 with ⟨_, rfl⟩ | ⟨h2', _⟩
        · have e : w.decRef.decRef = w.withRefs (w.rep.refs - 2) := by
            simp only [NumObj.decRef_eq, NumObj.withRefs_withRefs]
            simp only [NumObj.withRefs, Nat.sub_sub]
          rw [e] at hb3
          exact hpost hk3 hb3 (hxp ▸ (hdrop _).cons y) ho3
        · simp only [NumObj.decRef] at h; omega
      | rel h =>
        rcases hL0 with ⟨h3, _⟩ | ⟨_, rfl⟩
        · simp only [NumObj.decRef] at h; omega
        · exact hpost hk3 hb3 (hxp ▸ hdrop2.cons y) ho3
    · have hfr := hp.rest
      have hw3 := hsame rfl
      cases hfr with
      | rel h => omega
      | dec _ =>
        have hown1 : ∀ y' ∈ y :: L1, y'.Owns := by
          intro y' hy'
          rcases List.mem_cons.mp hy' with rfl | hy'
          · exact hyo
          · exact hown0 y' (List.mem_append_left _ hy')
        rcases hL0 with ⟨_, rfl⟩ | ⟨h2', _⟩
        · refine ra_negDec hlive cx (P1 := y :: L1) (v := xs.decRef) (P2 := L2) hb1 hwo
            (fun y' hy' => hb1.owner_db_ne (P := y :: L1) hwo hy' (hown1 y' hy'))
            (by simp only [NumObj.decRef]; omega) raN h21' h18' ?_
          intro R3 M3 H3 F3 L3 hk3 hkf hb3 ho3
          have e : xs.decRef.decRef = xs.withRefs (xs.rep.refs - 2) := by
            simp only [NumObj.decRef_eq, NumObj.withRefs_withRefs]
            simp only [NumObj.withRefs, Nat.sub_sub]
          cases hkf with
          | dec h =>
            rw [e] at hb3 h
            exact hpost hk3 hb3 ⟨y :: L1, L2, _, rfl, hxp, .dec h⟩ ho3
          | rel h =>
            rw [e] at h
            exact hpost hk3 hb3 ⟨y :: L1, L2, _, rfl, hxp, .rel h⟩ ho3
        · omega
  · intro hn0 R1 M1 hk1 hf1
    have hw0 : w.rep.num.mag = 0 := by
      unfold Num.div at hn0
      split at hn0
      · rename_i h0; simpa using h0
      · simp at hn0
    obtain ⟨hxn, hxN, hxl⟩ := hzr hw0
    have raN : RaAt S M1 M1 R0 R1 sp W q raSlots1 :=
      ⟨by rw [hk1.get 2]; bsimp [h2],
        ra.saved.transport (lo := 16) (top := 96) (hag := fun a h1 h2 => hf1 a
          (by simp only [frameIn]; omega)),
        (hk1.mono (ks' := raAll) (by decide)).trans (by keeps_tac ra.keep),
        by rw [hk1.get 23]; bsimp [ra.r23], fun _ _ _ => rfl⟩
    have hb1 := hb.out_frame (P := frameIn (sp - 96) (W - 96)) hf1 fun a ha => by
      simp only [frameIn] at ha; simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
    bsimp []
    refine ra_negDec hlive cx (P1 := A) (v := w) (P2 := B) hb1 hwo
      (fun y' hy' => hb1.owner_db_ne hwo hy' (hown y' (List.mem_append_left _ hy'))) hw2 raN
      (by rw [hk1.get 21]; bsimp [h21]) (by rw [hk1.get 18]; bsimp [h18]) ?_
    intro R3 M3 H3 F3 L3 hk3 hkf hb3 ho3
    have hfin : BcHeap S M3 H3 F3 L0 := by
      cases hkf with
      | dec h =>
        rcases hL0 with ⟨_, rfl⟩ | ⟨h2', _⟩
        · have e : w.decRef.decRef = w.withRefs (w.rep.refs - 2) := by
            simp only [NumObj.decRef_eq, NumObj.withRefs_withRefs]
            simp only [NumObj.withRefs, Nat.sub_sub]
          rwa [e] at hb3
        · simp only [NumObj.decRef] at h; omega
      | rel h =>
        rcases hL0 with ⟨h3, _⟩ | ⟨_, rfl⟩
        · simp only [NumObj.decRef] at h; omega
        · exact hb3
    refine hK.ret R3 M3 _ _ _ _ hk3 (raPost_keep hfin hmr hrr ?_ hxN hxl hxro ?_ ?_)
    · rw [hn, ← hon, hn0]; exact hxn
    · rw [ldv_congr .ld fun j hj => (ho3 _ (hsl.out _ (by simp only [widthOfM] at hj; omega))).trans
        (hf1 _ (by simp only [frameIn, widthOfM] at hj ⊢; omega))]
      exact hwq
    · intro a h1 h2' h3
      rw [ho3 a h1, hf1 a (fun h => h3 (by simp only [frameIn] at h ⊢; omega))]
      exact ra.out a h1 h3

end Dc.Mach
