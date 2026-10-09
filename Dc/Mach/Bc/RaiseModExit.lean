import Dc.Mach.Bc.RaiseModLoop

/-!
# `bc_raisemod`'s exit (`0x800063b4` to `0x80006458`)

    63b4 restore s6; free power (s0); free exponent (s8)
    6420 bc_free_num (result); *result = temp; return 0
    6430 the epilogue (also of the `-1` returns after the prologue)

The leaked `parity` and `temp` stay: the heap of the handles `[temp,
parity]` is the caller's with one reference added for each (`RList.final`).

- `RList.snoc_ref`/`RList.snoc_own`: the last handle as a reference added.
- `rx_epi`/`rx_epi0`: the epilogues; `rx_freeSlot`: `bc_free_num (result)`.
- `RxX`: the state at the exit; `rx_exit`: the result.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## The last handles as added references -/

theorem rBump_nil (y : NumObj) : rBump [] y = y := rfl

theorem RList.nil (L : List NumObj) : RList [] L = L := by
  simp only [RList, rTemps_nil, List.nil_append]
  exact (List.map_congr_left fun y _ => rBump_nil y).trans (List.map_id _)

/-- The caller's numbers apart. -/
theorem PDist.caller {hs : List RH} {L : List NumObj} (h : PDist (RList hs L)) : PDist L := by
  unfold PDist RList at *
  rw [List.map_append, map_p_rBump] at h
  exact List.Nodup.sublist (List.sublist_append_right _ _) h

/-- A reference handle last: one reference added to the caller's number. -/
theorem RList.snoc_ref (hs : List RH) {A B : List NumObj} {y : NumObj}
    (hd : ∀ w ∈ A ++ B, w.rep.p ≠ y.rep.p) :
    RList (hs ++ [.ref y]) (A ++ y :: B) = RList hs (A ++ y.withRefs (y.rep.refs + 1) :: B) := by
  rw [← RList.addRef hs hd]
  simp only [RList, List.map_append, List.map_cons, List.append_assoc]
  congr 3
  simp only [rBump, NumObj.withRefs_withRefs, NumObj.withRefs_refs, NumObj.withRefs_p]
  congr 1; omega

/-- An owned handle last: the number added in front of the caller's. -/
theorem RList.snoc_own (hs : List RH) (L : List NumObj) {w : NumObj} (hc : rCnt hs w.rep.p = 0) :
    RList (hs ++ [.own w]) L = RList hs (w :: L) := by
  have hb : rBump (hs ++ [.own w]) = rBump hs := by
    have := rBump_own hs [] w; simpa using this
  have hw : rBump hs w = w := by
    simp only [rBump, hc, Nat.add_zero, NumObj.withRefs_self]
  simp only [RList, hb, rTemps_append, rTemps_own, rTemps_nil, List.map_cons, hw,
    List.append_assoc, List.singleton_append]

/-- No reference handle names an owned number. -/
theorem RH.cnt_ne {h : RH} {p : Nat} (hp : h.p ≠ p) : RH.cnt p h = 0 := by
  cases h with
  | own y => rfl
  | ref y => simp only [RH.cnt]; rw [if_neg (show y.rep.p ≠ p from hp)]

/-- The handle's object with its own reference. -/
theorem RH.obj_ref1 (y : NumObj) : RH.obj [.ref y] (.ref y) = y.withRefs (y.rep.refs + 1) := by
  simp [RH.obj, RH.cnt]

/-- **The heap of the last two handles** `[hT, hX]` is the caller's with a
reference to `hX`'s number added, then one to `hT`'s. -/
theorem RList.final {hT hX : RH} {L : List NumObj} (hd : PDist (RList [hT, hX] L))
    (okT : RHOK L hT) (okX : RHOK L hX) (tx : hT.p ≠ hX.p) :
    ∃ w Lw Lm, AddRef L w Lw ∧ AddRef Lw (RH.obj [hT] hT) Lm ∧ RList [hT, hX] L = Lm := by
  have hdL := hd.caller
  -- the second handle, then the first on the list it leaves
  have step2 : ∀ (Lw : List NumObj), PDist Lw → (∀ y, hT = .ref y → y ∈ Lw) →
      ∃ Lm, AddRef Lw (RH.obj [hT] hT) Lm ∧ RList [hT] Lw = Lm := by
    intro Lw hdw hmem
    cases hT with
    | own y =>
      refine ⟨y :: Lw, .fresh okT.1, ?_⟩
      rw [show [RH.own y] = [] ++ [RH.own y] from rfl, RList.snoc_own [] Lw rfl, RList.nil]
    | ref y =>
      obtain ⟨A, B, rfl⟩ := List.append_of_mem (hmem y rfl)
      refine ⟨_, by rw [RH.obj_ref1]; exact .share, ?_⟩
      rw [show [RH.ref y] = [] ++ [RH.ref y] from rfl, RList.snoc_ref [] hdw.ne, RList.nil]
  cases hX with
  | own w =>
    have hc : rCnt [hT] w.rep.p = 0 := by
      rw [rCnt_cons, RH.cnt_ne (p := w.rep.p) tx]; rfl
    have e1 := RList.snoc_own [hT] L hc
    have hd' : PDist (RList [hT] (w :: L)) := by
      rw [← e1]; exact hd
    obtain ⟨Lm, h2, e⟩ := step2 (w :: L) hd'.caller (fun y e => by
        subst e; obtain ⟨A, B, rfl, _⟩ := okT; simp)
    refine ⟨w, w :: L, Lm, .fresh okX.1, h2, ?_⟩
    rw [show [hT, RH.own w] = [hT] ++ [RH.own w] from rfl, RList.snoc_own [hT] L hc, e]
  | ref z =>
    obtain ⟨A, B, rfl, _⟩ := okX
    have hdz := hdL.ne (x := z) (L1 := A) (L2 := B)
    have hdw : PDist (A ++ z.withRefs (z.rep.refs + 1) :: B) := by
      unfold PDist at hdL ⊢; simpa using hdL
    obtain ⟨Lm, h2, e⟩ := step2 _ hdw (fun y e => by
      subst e
      obtain ⟨A', B', e', _⟩ := okT
      have hy : y ∈ A ++ z :: B := by rw [e']; simp
      have hyz : y ≠ z := fun h => tx (by rw [h])
      simp only [List.mem_append, List.mem_cons] at hy ⊢
      rcases hy with h | h | h
      · exact .inl h
      · exact absurd h hyz
      · exact .inr (.inr h))
    refine ⟨_, _, Lm, .share, h2, ?_⟩
    rw [show [hT, RH.ref z] = [hT] ++ [RH.ref z] from rfl, RList.snoc_ref [hT] hdz, e]

/-! ## The epilogues -/

/-- **The epilogue** at `0x80006430`: the saved registers restored, `sp`
raised, the return with `a0` kept. -/
theorem rx_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} (cx : RxCtx S R0 sp W q) (hS : HeapOwn S)
    (sv : SavedWords M (sp - 112) rxSlots1 R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 112))
    (hkp : Keeps rxAll R R0) (h22 : R 22 = R0 22)
    (hk : ∀ R', Keeps binClob R' R0 → R' 10 = R 10 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x80006430#64 R M := by
  rx_facts cx
  have hsf := cx.frame
  have hal := cx.al
  bc_run hlive hS [h2, sv.get 8 96, sv.get 1 104, sv.get 18 80, sv.get 19 72, sv.get 20 64,
    sv.get 21 56, sv.get 23 40, sv.get 24 32, sv.get 9 88]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (Keeps.unwind (all := rxAll) (saved := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp)) (by bsimp [])
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, h2, h22, sv.get 8 96, sv.get 1 104, sv.get 18 80, sv.get 19 72, sv.get 20 64, sv.get 21 56, sv.get 23 40, sv.get 24 32, sv.get 9 88]
  all_goals (try (congr 1; omega))

/-- **The early `-1`** at `0x800064cc` (`mod` is `_zero_`): `ra` and `s1`
restored. -/
theorem rx_epi0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} (cx : RxCtx S R0 sp W q) (hS : HeapOwn S)
    (sv : SavedWords M (sp - 112) rxSlots0 R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 112))
    (hkp : Keeps [2, 9, 16] R R0)
    (hk : ∀ R', Keeps binClob R' R0 → R' 10 = 0xffffffffffffffff#64 →
      DW live S Q (R0 1) R' M) :
    DW live S Q 0x800064cc#64 R M := by
  rx_facts cx
  have hsf := cx.frame
  have hal := cx.al
  bc_run hlive hS [h2, sv.get 1 104, sv.get 9 88]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (Keeps.unwind (all := [1, 2, 9, 10, 16]) (saved := [1, 2, 9]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp.mono (by decide))) (by bsimp [])
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, h2, sv.get 1 104, sv.get 9 88, hkp.get 1 (by decide)]
  all_goals (try (congr 1; omega))

/-! ## `bc_free_num (result)` and the result -/

/-- **`bc_free_num (result)`** from `bc_raisemod`'s frame (`sp - 112`, `a0`
the slot), returning to `ra`. -/
theorem rx_freeSlot {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {xr : NumObj} (cx : RxCtx S R0 sp W q)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (h10 : R 10 = BitVec.ofNat 64 q)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L', Keeps freeNumClob R' R → FreedRest L1 L2 xr L' →
      BcHeap S M' H' F' L' →
      (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn (sp - 112) 32 a → imgM M' a = imgM M a) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x800048c0#64 R M := by
  rx_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hxm : xr ∈ L1 ++ xr :: L2 := List.mem_append_right _ List.mem_cons_self
  have hxn := hb.nums xr hxm
  have hxp' : heapStart ≤ xr.rep.p ∧ xr.rep.p + 16 ≤ heapEnd :=
    ⟨hxn.shape.pLo, by have := hxn.shape.pHi; omega⟩
  have hsf' : StackFrame S (sp - 112) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  have e : FreeEntry S M H F L1 L2 xr q (sp - 112) :=
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

/-- **The result** from `0x80006420` (the handles `[temp, parity]` left):
`bc_free_num (result)`, `*result = temp`, `0`. -/
theorem rx_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {hT hX : RH} {xr : NumObj} {n : Num} (cx : RxCtx S R0 sp W q)
    (ra : RxAt S Mt0 M R0 R sp W rxSlots1) (h22 : R 22 = R0 22)
    (h23 : R 23 = BitVec.ofNat 64 q) (h21 : R 21 = BitVec.ofNat 64 hT.p)
    (hb : BcHeap S M H F (RList [hT, hX] L)) (hown : RHOwn [hT, hX] L)
    (okT : RHOK L hT) (okX : RHOK L hX) (tx : hT.p ≠ hX.p)
    (hn : hT.base.rep.num = n) (hnn : hT.base.rep.Norm) (hl : 1 ≤ hT.base.rep.len)
    (hs : RxSlot M L xr q)
    (hret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
      RxPost S Mt0 Mt' H' F' L xr q sp W n Lf y → DW live S Q (R0 1) R' Mt') :
    DW live S Q 0x80006420#64 R M := by
  rx_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := ra.r2
  obtain ⟨w, Lw, Lm, hw1, hw2, e⟩ := RList.final hb.pdist okT okX tx
  have hall := hown.all
  rw [e] at hb hall
  have hxm : rBump [hT, hX] xr ∈ Lm := by rw [← e]; exact RList.mem_caller _ hs.mr
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hxm
  have hsr : ResSlot M L1 (rBump [hT, hX] xr) q :=
    ⟨by show 1 ≤ xr.rep.refs + _; have := hs.rr; omega, hs.wr,
      fun _ hxo y hy => hb.owner_db_ne hxo hy (hall y (List.mem_append_left _ hy))⟩
  bc_run hlive hS [h2, h23] at 0x800048c0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine rx_freeSlot hlive cx hb hsr (by bsimp [h2]) (by bsimp [h23]) (by bsimp []; try decide)
    fun R1 M1 H1 F1 L' hk1 hfr hb1 ho1 => ?_
  bsimp []
  have h23' : R1 23 = BitVec.ofNat 64 q := by rw [hk1.get 23 (by decide)]; bsimp [h23]
  have h21' : R1 21 = BitVec.ofNat 64 hT.p := by rw [hk1.get 21 (by decide)]; bsimp [h21]
  have hq0 := hsl.out q ⟨Nat.le_refl _, by omega⟩
  have hq7 := hsl.out (q + 7) ⟨by omega, by omega⟩
  simp only [OutHeap, heapStart, heapEnd] at hq0 hq7
  have hb2 := hb1.out_frame (P := slotBytes q) (MemOnly.store M1 q 8 (BitVec.ofNat 64 hT.p)) hsl.out
  bc_run hlive (fun a h1 h2 => hb1.heap.own a h1 h2) [h23', h21'] at 0x80006430
  all_goals first | exact hq.acc | skip
  have hag : ∀ a, (a < q ∨ q + 8 ≤ a) → OutHeap a → ¬ frameIn (sp - 112) 32 a →
      imgM (writeLog M1 [(q, 8, BitVec.ofNat 64 hT.p)]) a = imgM M a := fun a h1 h3 h4 => by
    rw [imgM_store_miss _ _ h1]
    exact ho1 a h3 (by simp only [slotBytes]; omega) h4
  refine rx_epi hlive cx (fun a h1 h2 => hb2.heap.own a h1 h2)
    (ra.saved.transport (lo := 32) (top := 112) (hag := fun a h1 h2' => hag a (by omega)
      (outHeap_of_ge (by simp only [heapEnd]; omega)) (by simp only [frameIn]; omega)))
    (by bsimp [hk1.get 2 (by decide), h2]) (by keeps_tac ((hk1.mono (by decide)).trans
      (by keeps_tac ra.keep))) (by bsimp []; rw [hk1.get 22 (by decide)]; bsimp [h22])
    fun R' hk' h10' => hret R' _ H1 F1 L' (RH.obj [hT] hT) hk' (by rw [h10']; bsimp [])
      { heap := hb2
        mid := ⟨w, Lw, _, hw1, hw2, L1, L2, _, rfl, rfl, hfr⟩
        num := by rw [RH.obj_num]; exact hn
        norm := (RH.obj_norm _ _).mpr hnn
        pos := by rw [RH.obj_len]; exact hl
        owns := by
          cases hT with
          | own y => exact hown.temps y (by simp)
          | ref o =>
            obtain ⟨A, B, e', _⟩ := okT
            exact hown.caller o (by rw [e']; simp)
        slot := by rw [RH.obj_p]; exact ldv_store_hit _ _ _
        out := fun a ha hsq hf => by
          simp only [slotBytes] at hsq
          rw [hag a (by omega) ha (by simp only [frameIn] at hf ⊢; omega)]
          exact ra.out a ha hf }

/-! ## The frees of `power` and `exponent` -/

/-- The result slot through bytes it does not hold. -/
theorem RxSlot.congr {M M' : Mem} {L : List NumObj} {xr : NumObj} {q : Nat}
    (hs : RxSlot M L xr q) (h : ∀ a, slotBytes q a → imgM M' a = imgM M a) : RxSlot M' L xr q :=
  { hs with wr := by rw [ldv_congr .ld fun j hj => h _ (by simp only [widthOfM] at hj ⊢; omega)]; exact hs.wr }

/-- Inside the frame through a change of the heap alone. -/
theorem RxAt.heap {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {slots : List (Nat × Nat)} (cx : RxCtx S R0 sp W q) (h : RxAt S Mt0 M R0 R sp W slots)
    (hlo : ∀ p ∈ slots, 32 ≤ p.2 := by decide) (htop : ∀ p ∈ slots, p.2 + 8 ≤ 112 := by decide)
    (hag : ∀ a, OutHeap a → imgM M' a = imgM M a) : RxAt S Mt0 M' R0 R sp W slots := by
  rx_facts cx
  exact
    { h with
      saved := h.saved.transport hlo htop fun a h1 h2 =>
        hag a (outHeap_of_ge (by simp only [heapEnd]; omega))
      out := fun a ha hf => (hag a ha).trans (h.out a ha hf) }

/-- A handle dropped. -/
theorem RHOwn.drop {hs1 hs2 : List RH} {h : RH} {L : List NumObj}
    (ho : RHOwn (hs1 ++ h :: hs2) L) : RHOwn (hs1 ++ hs2) L :=
  ⟨fun y hy => ho.temps y (by
    rcases List.mem_append.mp hy with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')), ho.caller⟩

/-- A freed handle's number. -/
theorem KFreed.rest {H H' : Heap} {F F' : List Blk} {L1 L2 L' : List NumObj} {x : NumObj}
    (h : KFreed H F L1 L2 x H' F' L') : FreedRest L1 L2 x L' := by
  cases h with
  | dec h => exact .dec h
  | rel h => exact .rel h

/-- **`exponent` freed** from `0x800063ec`, then the result. -/
theorem rx_exitE {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {hE hT hX : RH} {xr : NumObj} {n : Num} (cx : RxCtx S R0 sp W q)
    (ra : RxAt S Mt0 M R0 R sp W rxSlots1) (h22 : R 22 = R0 22)
    (h23 : R 23 = BitVec.ofNat 64 q) (h21 : R 21 = BitVec.ofNat 64 hT.p)
    (h24 : R 24 = BitVec.ofNat 64 hE.p)
    (hb : BcHeap S M H F (RList [hE, hT, hX] L)) (hown : RHOwn [hE, hT, hX] L)
    (okE : RHOK L hE) (okT : RHOK L hT) (okX : RHOK L hX) (tx : hT.p ≠ hX.p)
    (hn : hT.base.rep.num = n) (hnn : hT.base.rep.Norm) (hl : 1 ≤ hT.base.rep.len)
    (hs : RxSlot M L xr q)
    (hret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
      RxPost S Mt0 Mt' H' F' L xr q sp W n Lf y → DW live S Q (R0 1) R' Mt') :
    DW live S Q 0x800063ec#64 R M := by
  obtain ⟨L1, L2, x, e, hp, hr, hnv, _, _, hfr⟩ :=
    RList.slot (hs1 := []) (h := hE) (hs2 := [hT, hX]) hb okE hown
  have hb' : BcHeap S M H F (RList ([] ++ hE :: [hT, hX]) L) := hb
  rw [e] at hb'
  have hx : R 24 = BitVec.ofNat 64 x.rep.p := by rw [hp]; exact h24
  have k : FreeK [1, 10, 14, 15] live S Q 0x80006420#64 R M (fun _ => False) H F L1 L2 x :=
    fun R' M' H' F' L' hk hkf hb1 hof => by
      have hL : L' = RList [hT, hX] L := hfr L' hkf.rest
      subst hL
      have hag : ∀ a, OutHeap a → imgM M' a = imgM M a := fun a ha => hof a ha id
      exact rx_ret hlive cx ((ra.heap cx (hag := hag)).regs hk) (by rw [hk.get 22 (by decide)]; exact h22)
        (by rw [hk.get 23 (by decide)]; exact h23) (by rw [hk.get 21 (by decide)]; exact h21)
        hb1 (show RHOwn ([] ++ hE :: [hT, hX]) L from hown).drop okT okX tx hn hnn hl
        (hs.congr fun a ha => hag a (cx.slot.out a ha)) hret
  exact ffree_800063ec hlive hb' hr hnv hx k k k

/-- The state at the exit `0x800063bc`: the handles, `temp` holding `n`,
`power`, `exponent`, `temp` in `s0`, `s8`, `s5`, `s6` restored. -/
structure RxX (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (hP hE hT hX : RH) (n : Num) : Prop where
  ra : RxAt S Mt0 M R0 R sp W rxSlots1
  r22 : R 22 = R0 22
  r23 : R 23 = BitVec.ofNat 64 q
  heap : BcHeap S M H F (RList [hP, hE, hT, hX] L)
  own : RHOwn [hP, hE, hT, hX] L
  okP : RHOK L hP
  okE : RHOK L hE
  okT : RHOK L hT
  okX : RHOK L hX
  tx : hT.p ≠ hX.p
  num : hT.base.rep.num = n
  norm : hT.base.rep.Norm
  len : 1 ≤ hT.base.rep.len
  r8 : R 8 = BitVec.ofNat 64 hP.p
  r24 : R 24 = BitVec.ofNat 64 hE.p
  r21 : R 21 = BitVec.ofNat 64 hT.p

/-- **The exit** from `0x800063bc`: `power` and `exponent` freed, then the
result. -/
theorem rx_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {hP hE hT hX : RH} {xr : NumObj} {n : Num} (cx : RxCtx S R0 sp W q)
    (st : RxX S Mt0 M R0 R sp W q H F L hP hE hT hX n) (hs : RxSlot M L xr q)
    (hret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
      RxPost S Mt0 Mt' H' F' L xr q sp W n Lf y → DW live S Q (R0 1) R' Mt') :
    DW live S Q 0x800063bc#64 R M := by
  obtain ⟨L1, L2, x, e, hp, hr, hnv, _, _, hfr⟩ :=
    RList.slot (hs1 := []) (h := hP) (hs2 := [hE, hT, hX]) st.heap st.okP st.own
  have hb' : BcHeap S M H F (RList ([] ++ hP :: [hE, hT, hX]) L) := st.heap
  rw [e] at hb'
  have hx : R 8 = BitVec.ofNat 64 x.rep.p := by rw [hp]; exact st.r8
  have k : FreeK [1, 10, 14, 15] live S Q 0x800063ec#64 R M (fun _ => False) H F L1 L2 x :=
    fun R' M' H' F' L' hk hkf hb1 hof => by
      have hL : L' = RList [hE, hT, hX] L := hfr L' hkf.rest
      subst hL
      have hag : ∀ a, OutHeap a → imgM M' a = imgM M a := fun a ha => hof a ha id
      exact rx_exitE hlive cx ((st.ra.heap cx (hag := hag)).regs hk)
        (by rw [hk.get 22 (by decide)]; exact st.r22) (by rw [hk.get 23 (by decide)]; exact st.r23)
        (by rw [hk.get 21 (by decide)]; exact st.r21) (by rw [hk.get 24 (by decide)]; exact st.r24)
        hb1 (show RHOwn ([] ++ hP :: [hE, hT, hX]) L from st.own).drop st.okE st.okT st.okX st.tx
        st.num st.norm st.len (hs.congr fun a ha => hag a (cx.slot.out a ha)) hret
  rcases (show x.rep.refs = 1 ∨ 2 ≤ x.rep.refs from by omega) with hr1 | hr2
  · exact ffree_rel_800063b8 hlive hb' hr1 (hnv hr1) hx k k
  · exact ffree_dec_800063b8 hlive hb' hr2 hx k

/-- **The loop's exit** at `0x800063b4`: `s6` restored, `power` not `NULL`,
then `rx_exit`. -/
theorem rx_fin {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {xm : NumObj} {k rs B Sc Ee : Nat}
    {hP hE hT hX : RH} {m : Nat} {p tv : Num} {xr : NumObj} (cx : RxCtx S R0 sp W q)
    (st : RxM S Mt0 M R0 R sp W q H F L xm k rs B Sc Ee hP hE hT hX m p tv)
    (r24 : R 24 = BitVec.ofNat 64 hE.p) (hs : RxSlot M L xr q)
    (hret : ∀ R' Mt' H' F' Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
      RxPost S Mt0 Mt' H' F' L xr q sp W tv Lf y → DW live S Q (R0 1) R' Mt') :
    DW live S Q 0x800063b4#64 R M := by
  rx_facts cx
  have hsf := cx.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.f.ra
  have sv := ra.saved
  have hPn := hb.nums _ st.objP
  num_facts hPn
  have hPp : (RH.obj [hP, hE, hT, hX] hP).rep.p = hP.p := RH.obj_p _ _
  bc_run hlive hS [ra.r2, sv.get 22 48, st.r8] at 0x800063bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals try (intro hc; exact absurd ((ofNat_eq_iff (x := hP.p) (y := 0)
    (by omega) (by omega)).mp hc) (by omega))
  intro _
  have sub : rxSlots1 ⊆ rxSlots2 := by decide
  exact rx_exit hlive cx
    { ra :=
        { ra with
          saved := fun p hp => sv p (sub hp)
          keep := by keeps_tac ra.keep
          r2 := by bsimp [ra.r2] }
      r22 := by bsimp []
      r23 := by bsimp [st.f.r23]
      heap := hb
      own := st.own
      okP := st.okP
      okE := st.okE
      okT := st.okT
      okX := st.okX
      tx := st.tx
      num := st.vT.num
      norm := st.nT
      len := st.vT.len
      r8 := by bsimp [st.r8]
      r24 := by bsimp [r24]
      r21 := by bsimp [st.r21] } hs hret

end Dc.Mach
