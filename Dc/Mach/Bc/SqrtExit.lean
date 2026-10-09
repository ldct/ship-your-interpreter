import Dc.Mach.Bc.SqrtLoop

/-!
# `bc_sqrt`'s exit (`0x80006d68` to the return)

    6d68 bc_free_num (num); bc_divide (guess, _one_, num, rscale)
    6d88 free guess (s9), guess1 (s0), point5 (s4), diff (s10)
    6e4c restore s5-s7, s9, s11; return 1 (the epilogue at 6c54)

- `sq_epi`/`sq_ret`: the epilogues; `free_slot_spec`: `bc_free_num` of a
  caller's slot from any frame.
- `SqFr`: the frame and the handles while they are freed; `SqFr.step`:
  one handle freed at a generated free site.
- `sq_exit`: from the loop's exit to the result `Num.sqrtFinish`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## The epilogues -/

/-- **The epilogue** at `0x80006c54`: `ra`, `s0`-`s4`, `s8`, `s10`
restored (`s5`-`s7`, `s9`, `s11` already the caller's), `sp` raised, the
return with `a0` kept. -/
theorem sq_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} (cx : SqCtx S R0 sp W q) (hS : HeapOwn S)
    (sv : SavedWords M (sp - 160) sqSlots0 R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 160))
    (hkp : Keeps sqAll R R0) (hs : ∀ z ∈ [21, 22, 23, 25, 27], R z = R0 z)
    (hk : ∀ R', Keeps binClob R' R0 → R' 10 = R 10 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x80006c54#64 R M := by
  sq_facts cx
  have hsf := cx.cc.frame
  have hal := cx.al
  have h21 := hs 21 (by simp); have h22 := hs 22 (by simp); have h23 := hs 23 (by simp)
  have h25 := hs 25 (by simp); have h27 := hs 27 (by simp)
  have g1 := sv.get 1 152; have g8 := sv.get 8 144; have g9 := sv.get 9 136
  have g18 := sv.get 18 128; have g19 := sv.get 19 120; have g20 := sv.get 20 112
  have g24 := sv.get 24 80; have g26 := sv.get 26 64
  bc_run hlive hS [h2, g1, g8, g9, g18, g19, g20, g24, g26]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (Keeps.unwind (all := sqAll)
    (saved := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp)) (by bsimp [])
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first | (bsimp [cx.sp0, h2, g1, g8, g9, g18, g19, g20, g24, g26, h21, h22, h23, h25, h27]; done) | skip
  rw [upd_same, cx.sp0, show sp - 160 + 160 = sp by omega]

/-- **The return of `1`** from `0x80006e4c`: `s5`-`s7`, `s9`, `s11`
restored, then `sq_epi`. -/
theorem sq_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} (cx : SqCtx S R0 sp W q) (hS : HeapOwn S)
    (sa : SqAt S Mt0 M R0 R sp W sqSlots1)
    (hk : ∀ R', Keeps binClob R' R0 → R' 10 = 1#64 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x80006e4c#64 R M := by
  sq_facts cx
  have hsf := cx.cc.frame
  have sv := sa.saved
  bc_run hlive hS [sa.r2, sv.get 21 104, sv.get 22 96, sv.get 23 88, sv.get 25 72, sv.get 27 56]
    at 0x80006c54
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have sub : sqSlots0 ⊆ sqSlots1 := by decide
  refine sq_epi hlive cx hS (fun p hp => sv p (sub hp)) (by bsimp [sa.r2])
    (by keeps_tac sa.keep) ?_ fun R' hk' h10 => hk R' hk' (by rw [h10]; bsimp [])
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [sv.get 21 104, sv.get 22 96, sv.get 23 88, sv.get 25 72, sv.get 27 56]

/-! ## `bc_free_num` of a caller's slot -/

/-- **`bc_free_num (q)`** called with `sp'` (its 32 bytes below), the slot
`q` holding `xr` of `L1 ++ xr :: L2`: what it leaves, the slot `NULL`, off
the heap only the slot and the 32 bytes changed. -/
theorem free_slot_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {sp' q : Nat} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {xr : NumObj} (hsf : StackFrame S sp' 32) (hab : heapEnd + 32 ≤ sp')
    (hq : PtrSlot S q) (hqo : ∀ a, slotBytes q a → OutHeap a) (hap : q + 8 ≤ sp' - 32 ∨ sp' ≤ q)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr q)
    (h2 : R 2 = BitVec.ofNat 64 sp') (h10 : R 10 = BitVec.ofNat 64 q)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L', Keeps freeNumClob R' R → FreedRest L1 L2 xr L' →
      BcHeap S M' H' F' L' → ldv .ld M' q = 0#64 →
      (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp' 32 a → imgM M' a = imgM M a) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x800048c0#64 R M := by
  have hxm : xr ∈ L1 ++ xr :: L2 := List.mem_append_right _ List.mem_cons_self
  have hxn := hb.nums xr hxm
  have hxp' : heapStart ≤ xr.rep.p ∧ xr.rep.p + 16 ≤ heapEnd :=
    ⟨hxn.shape.pLo, by have := hxn.shape.pHi; omega⟩
  have e : FreeEntry S M H F L1 L2 xr q sp' :=
    FreeEntry.of_slot hb hr hr.noView hq hqo hsf hab hap
  refine bc_free_num_spec hlive e R h10 h2 hal
    ⟨fun hx2 R1 Mt1 hk1 hb1 h0 hmo => ?_, fun hx1 R1 Mt1 H1 hk1 hrp => ?_⟩
  · refine hk R1 Mt1 H F _ hk1 (.dec hx2) hb1 h0 fun a ha hs _ => hmo a fun hc => ?_
    rcases hc with hc | hc
    · simp only [refsBytes, OutHeap, heapStart, heapEnd] at hc ha hxp'; omega
    · exact hs hc
  · refine hk R1 Mt1 H1 (xr.sb :: F) _ hk1 (.rel hx1) hrp.heap hrp.slot
      fun a ha hs hf => hrp.frame a fun hc => ?_
    rcases hc with hc | hc | hc | hc | hc
    · exact OutHeap.not_alloc hb.heap ha hc
    · exact ha.1 (live_in_heap hb.heap (hb.blocks xr hxm).sLive hc)
    · exact hs hc
    · exact hf hc
    · exact ha.2.2 hc

/-! ## The handles freed -/

/-- The frame and the handles `hs` over `L` while they are freed. -/
structure SqFr (S : Nat → Prop) (Mx M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (hs : List RH) : Prop where
  sa : SqAt S Mx M R0 R sp W sqSlots1
  heap : BcHeap S M H F (RList hs L)
  own : RHOwn hs L
  ok : ∀ h ∈ hs, RHOK L h

/-- **One handle freed** at a generated free site (`site`, which takes the
handle's object in the heap and its continuations). -/
theorem SqFr.step {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {Mx M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {hs1 hs2 : List RH} {h : RH} {pc pc' : BitVec 64}
    (cx : SqCtx S R0 sp W q) (st : SqFr S Mx M R0 R sp W H F L (hs1 ++ h :: hs2))
    (site : ∀ L1 L2 x, BcHeap S M H F (L1 ++ x :: L2) → 1 ≤ x.rep.refs →
      (x.rep.refs = 1 → x.Owns → ∀ y ∈ L1, y.db ≠ x.db) → x.rep.p = h.p →
      FreeK [1, 10, 14, 15] live S Q pc' R M (fun _ => False) H F L1 L2 x → DW live S Q pc R M)
    (hk : ∀ R' M' H' F', Keeps [1, 10, 14, 15] R' R →
      SqFr S Mx M' R0 R' sp W H' F' L (hs1 ++ hs2) → DW live S Q pc' R' M') :
    DW live S Q pc R M := by
  obtain ⟨L1, L2, x, e, hp, hr, hnv, _, _, hfr⟩ :=
    RList.slot st.heap (st.ok h (by simp)) st.own
  have hb' : BcHeap S M H F (L1 ++ x :: L2) := by rw [← e]; exact st.heap
  refine site L1 L2 x hb' hr hnv hp fun R' M' H' F' L' hk' hkf hb1 hof => ?_
  have hL : L' = RList (hs1 ++ hs2) L := hfr L' hkf.rest
  subst hL
  have hag : ∀ a, OutHeap a → imgM M' a = imgM M a := fun a ha => hof a ha id
  exact hk R' M' H' F' hk'
    { sa := (st.sa.heap cx (hag := hag)).regs hk'
      heap := hb1
      own := st.own.drop
      ok := fun h' hh => st.ok h' (by
        rcases List.mem_append.mp hh with h1 | h1
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)) }

/-- The last handle owned: the heap is its number in front of the caller's. -/
theorem RList.own1 (y : NumObj) (L : List NumObj) : RList [.own y] L = y :: L := by
  have := RList.snoc_own [] L (w := y) rfl
  rw [RList.nil] at this
  exact this

/-- **The frees of `guess`, `guess1`, `point5` and `diff`** from
`0x80006d88` (the result `y'` after them), then the return of `1`. -/
theorem sq_tail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mx M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {p5 d y y' : NumObj} {G : RH} (cx : SqCtx S R0 sp W q)
    (st : SqFr S Mx M R0 R sp W H F L [.own p5, .own d, .own y, G, .own y'])
    (h25 : R 25 = BitVec.ofNat 64 y.rep.p) (h8 : R 8 = BitVec.ofNat 64 G.p)
    (h20 : R 20 = BitVec.ofNat 64 p5.rep.p) (h26 : R 26 = BitVec.ofNat 64 d.rep.p)
    (hk : ∀ R' M' H' F', Keeps binClob R' R0 → R' 10 = 1#64 →
      (∀ a, OutHeap a → ¬ frameIn sp W a → imgM M' a = imgM Mx a) →
      BcHeap S M' H' F' (y' :: L) → RHOwn [.own y'] L → DW live S Q (R0 1) R' M') :
    DW live S Q 0x80006d88#64 R M := by
  refine SqFr.step (hs1 := [.own p5, .own d]) (hs2 := [G, .own y']) cx st
    (fun L1 L2 x hb hr hnv hp k => ffree_80006d88 hlive hb hr hnv (by rw [hp]; exact h25) k k k)
    fun R1 M1 H1 F1 hk1 st1 => ?_
  refine SqFr.step (hs1 := [.own p5, .own d]) (hs2 := [.own y']) cx st1
    (fun L1 L2 x hb hr hnv hp k => ffree_80006dbc hlive hb hr hnv
      (by rw [hp, hk1.get 8 (by decide)]; exact h8) k k k)
    fun R2 M2 H2 F2 hk2 st2 => ?_
  refine SqFr.step (hs1 := []) (hs2 := [.own d, .own y']) cx st2
    (fun L1 L2 x hb hr hnv hp k => ffree_80006dec hlive hb hr hnv
      (by rw [hp, hk2.get 20 (by decide), hk1.get 20 (by decide)]; exact h20) k k k)
    fun R3 M3 H3 F3 hk3 st3 => ?_
  refine SqFr.step (hs1 := []) (hs2 := [.own y']) cx st3
    (fun L1 L2 x hb hr hnv hp k => ffree_80006e1c hlive hb hr hnv
      (by rw [hp, hk3.get 26 (by decide), hk2.get 26 (by decide), hk1.get 26 (by decide)]
          exact h26) k k k)
    fun R4 M4 H4 F4 _ st4 => ?_
  have hb4 := st4.heap
  rw [show ([] ++ [RH.own y'] : List RH) = [.own y'] from rfl, RList.own1] at hb4
  exact sq_ret hlive cx (fun a h1 h2 => hb4.heap.own a h1 h2) st4.sa fun R' hk' h10 =>
    hk R' M4 H4 F4 hk' h10 st4.sa.out hb4 st4.own

/-! ## `bc_free_num (num)` and the result -/

/-- A caller's number no handle names, freed from under the handles: the
handles over what freeing it from the caller's list leaves. -/
theorem RList.dropCaller {hs : List RH} {A B L' : List NumObj} {x : NumObj}
    (hc : rCnt hs x.rep.p = 0)
    (h : FreedRest (rTemps hs ++ A.map (rBump hs)) (B.map (rBump hs)) x L') :
    ∃ Ld, FreedRest A B x Ld ∧ L' = RList hs Ld := by
  cases h with
  | dec h2 =>
    have e : rBump hs x.decRef = x.decRef := by
      simp only [rBump, show rCnt hs x.decRef.rep.p = 0 from hc, Nat.add_zero,
        NumObj.withRefs_self]
    exact ⟨_, .dec h2, by simp only [RList, List.map_append, List.map_cons, e, List.append_assoc]⟩
  | rel h1 => exact ⟨_, .rel h1, by simp only [RList, List.map_append, List.append_assoc]⟩

/-- Another number stays through a free. -/
theorem FreedRest.mem_of_ne {A B Ld : List NumObj} {x w : NumObj} (h : FreedRest A B x Ld)
    (hw : w ∈ A ++ x :: B) (hne : w ≠ x) : w ∈ Ld := by
  simp only [List.mem_append, List.mem_cons] at hw
  cases h with
  | dec _ =>
    simp only [List.mem_append, List.mem_cons]
    rcases hw with h1 | h1 | h1
    · exact .inl h1
    · exact absurd h1 hne
    · exact .inr (.inr h1)
  | rel _ =>
    simp only [List.mem_append]
    rcases hw with h1 | h1 | h1
    · exact .inl h1
    · exact absurd h1 hne
    · exact .inr h1

/-- A handle other than the freed number names a number of what is left. -/
theorem RHOK.freed {A B Ld : List NumObj} {x : NumObj} {h : RH} (hok : RHOK (A ++ x :: B) h)
    (hp : h.p ≠ x.rep.p) (hf : FreedRest A B x Ld) : RHOK Ld h := by
  cases h with
  | own y => exact hok
  | ref y =>
    obtain ⟨A', B', e, hr⟩ := hok
    have hy : y ∈ A ++ x :: B := by rw [e]; simp
    obtain ⟨A'', B'', e'⟩ := List.append_of_mem (hf.mem_of_ne hy fun h' => hp (by rw [h']; rfl))
    exact ⟨A'', B'', e', hr⟩

/-- **The loop's exit** at `0x80006d68`: `bc_free_num (num)`, `*num =
guess / 1` at `rscale` (`Num.sqrtFinish`), the four frees and the return of
`1` with the result in the slot. -/
theorem sq_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb L : List NumObj} {x zb z o p5 : NumObj} {k rs cs : Nat}
    {G : RH} {d y : NumObj} {g : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) (hoom : RaOom live S Q Mt0 sp W q)
    (hl : SqLeak L z Lb) (st : SqN S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs G d y g)
    (hsy : y.rep.len + y.rep.scale ≤ sqB x k)
    (hret : ∀ R' M' H' F' Lf y', Keeps binClob R' R0 → R' 10 = 1#64 →
      SqPost S Mt0 M' H' F' L x z q sp W (Num.sqrtFinish y.rep.num rs) Lf y' →
      DW live S Q (R0 1) R' M') :
    DW live S Q 0x80006d68#64 R M := by
  have cx := env.cx
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.f.sa
  have h2 := ra.r2
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hcs := env.cst
  have hbs := env.bsmall; have hos := env.oneSize; have hcq := env.sqc_eq
  have hrs : rs ≤ sqc x k := by omega
  obtain ⟨A, B, eL⟩ := List.append_of_mem env.mx
  have hc : rCnt [.own p5, .own d, .own y, G] x.rep.p = 0 := by
    simp only [rCnt_cons, RH.cnt_ne st.gx]; rfl
  have hbx : rBump [.own p5, .own d, .own y, G] x = x := by
    simp only [rBump, hc, Nat.add_zero, NumObj.withRefs_self]
  have e : RList [.own p5, .own d, .own y, G] Lb =
      (rTemps [.own p5, .own d, .own y, G] ++ A.map (rBump [.own p5, .own d, .own y, G])) ++
        x :: B.map (rBump [.own p5, .own d, .own y, G]) := by
    rw [eL, RList.ref_split, hbx]
  have hb' := hb; rw [e] at hb'
  have hall := st.own.all; rw [e] at hall
  have hsr : ResSlot M (rTemps [.own p5, .own d, .own y, G] ++
      A.map (rBump [.own p5, .own d, .own y, G])) x q :=
    ⟨env.rx, st.f.wq, fun _ hxo w hw => hb'.owner_db_ne hxo hw (hall w (List.mem_append_left _ hw))⟩
  bc_run hlive hS [h2, st.f.r19] at 0x800048c0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine free_slot_spec hlive (sp' := sp - 160)
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
    (by simp only [heapEnd]; omega) hq hsl.out (by omega) hb' hsr (by bsimp [h2])
    (by bsimp [st.f.r19]) (by bsimp []; try decide) fun R1 M1 H1 F1 L' hk1 hfr hb1 h0 ho1 => ?_
  bsimp []
  obtain ⟨Ld, hfrA, rfl⟩ := RList.dropCaller hc hfr
  -- memory facts at `M1`
  have hM1 : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn (sp - 160) 32 a → ¬ frameIn sp W a →
      imgM M1 a = imgM Mt0 a := fun a h1 h3 h4 h5 => (ho1 a h1 h3 h4).trans (ra.out a h1 h5)
  have hone : ldv .ld M1 oneAddr = BitVec.ofNat 64 o.rep.p := by
    have hq1 := env.qone
    rw [ldv_congr .ld fun j hj => hM1 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr,
      bcFreeAddr, widthOfM, oneAddr] at hj ⊢; omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
      (by simp only [frameIn, widthOfM, oneAddr] at hj ⊢; omega)
      (by simp only [frameIn, widthOfM, oneAddr] at hj ⊢; omega)]
    exact hcs.one
  have hzg : ldv .ld M1 zeroAddr = BitVec.ofNat 64 zb.rep.p := by
    have hq1 := cx.slotZero
    rw [ldv_congr .ld fun j hj => hM1 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr,
      bcFreeAddr, widthOfM, zeroAddr] at hj ⊢; omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
      (by simp only [frameIn, widthOfM, zeroAddr] at hj ⊢; omega)
      (by simp only [frameIn, widthOfM, zeroAddr] at hj ⊢; omega)]
    exact hcs.zero.glob
  have hw8 : ldv .ld M1 (sp - 160 + 8) = BitVec.ofNat 64 oneAddr := by
    rw [ldv_congr .ld fun j hj => ho1 _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))
      (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
      (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact st.f.w8
  have h2' : R1 2 = BitVec.ofNat 64 (sp - 160) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
  have h19 : R1 19 = BitVec.ofNat 64 q := by rw [hk1.get 19 (by decide)]; bsimp [st.f.r19]
  have h24 : R1 24 = BitVec.ofNat 64 rs := by rw [hk1.get 24 (by decide)]; bsimp [st.f.r24]
  have h25 : R1 25 = BitVec.ofNat 64 y.rep.p := by rw [hk1.get 25 (by decide)]; bsimp [st.r25]
  have hS1 : HeapOwn S := fun a h1 h2 => hb1.heap.own a h1 h2
  have e1 : (BitVec.ofNat 64 oneAddr).toNat = oneAddr := by
    rw [BitVec.toNat_ofNat]; rfl
  bc_run hlive hS1 [h2', hw8, e1, hone, h19, h24, h25] at 0x8000589c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first
    | (have eo : oneAddr = 0x8001cdc0 := rfl; have htx : tohostAddr = 0x8001ad00 := rfl; bc_addr)
    | exact fun b hb' => cx.cc.consts b (by
        have := of_mem_accAddrs hb'
        have eo : oneAddr = 0x8001cdc0 := rfl
        have e0 : zeroAddr = 0x8001cdc8 := rfl; have e2 : twoAddr = 0x8001cdb8 := rfl
        simp only [constBytes]; omega)
    | skip
  have hfx : ∀ w, w ∈ Lb → w.rep.p ≠ x.rep.p → rBump [.own p5, .own d, .own y, G] w ∈
      RList [.own p5, .own d, .own y, G] Ld := fun w hw hp =>
    RList.mem_caller _ (hfrA.mem_of_ne (by rw [← eL]; exact hw) fun h' => hp (by rw [h']))
  have hyL : y ∈ RList [.own p5, .own d, .own y, G] Ld := RH.obj_mem (h := .own y) (by simp) st.oky
  have hone1 : Num.one.mag ≠ 0 := by decide
  refine bc_divide_null_spec hlive (L := RList [.own p5, .own d, .own y, G] Ld) (x1 := y)
    (x2 := rBump [.own p5, .own d, .own y, G] o) (z := rBump [.own p5, .own d, .own y, G] zb)
    (k := rs) (n := Num.div y.rep.num o.rep.num rs)
    (cx.cc.div (F := 160) (by omega) (by omega) (hsl.lift (by omega)) cx.slotZero (by bsimp [h2'])
      (by bsimp []; try decide))
    ⟨fun m hm R' M' H' F' L'' y' hk2 h10' hp' => ?_, fun hn => ?_,
      fun R' M' sp' h1 h3 hr2 hout => hoom R' M' sp' (by omega) (by omega) hr2 fun a ha hs hf => by
        rw [hout a ha hs (fun h' => hf (by simp only [frameIn] at h' ⊢; omega)),
          ho1 a ha hs (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
        exact ra.out a ha hf⟩
    rfl hyL (hfx o env.mo fun h' => env.xo h'.symm) (hfx zb env.mz fun h' => env.xz h'.symm)
    (by show y.rep.len + y.rep.scale + rs + o.rep.len + o.rep.scale < 2 ^ 27; omega) hzg st.ly
    (by show dval zb.rep.ds = 0; rw [hcs.zero.ds]; rfl) hb1 h0 (by bsimp []) (by bsimp []; rfl)
    (by bsimp []) (by bsimp [])
  · have hL : L'' = RList [.own p5, .own d, .own y, G] Ld := hp'.rest
    subst hL
    have hown' : RHOwn [.own p5, .own d, .own y, G, .own y'] Ld :=
      ⟨fun w hw => by
        have hw' : RH.own w ∈ ([.own p5, .own d, .own y, G] ++ [.own y'] : List RH) := hw
        rcases List.mem_append.mp hw' with h | h
        · exact st.own.temps w h
        · simp only [List.mem_singleton, RH.own.injEq] at h; subst h; exact hp'.owns,
       hfrA.owns (by rw [← eL]; exact env.owns)⟩
    have hb2 : BcHeap S M' H' F' (RList [.own p5, .own d, .own y, G, .own y'] Ld) :=
      hp'.heap.perm (RList.cons_perm [.own p5, .own d, .own y, G] [] y' Ld) hown'.all
    have hokG : RHOK Ld G := by
      have := st.okG; rw [eL] at this; exact this.freed st.gx hfrA
    have hk2' : Keeps sqAll R' R0 :=
      (hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac ra.keep)))
    have h8 : R1 8 = BitVec.ofNat 64 G.p := by rw [hk1.get 8 (by decide)]; bsimp [st.r8]
    have h20 : R1 20 = BitVec.ofNat 64 p5.rep.p := by rw [hk1.get 20 (by decide)]; bsimp [st.f.r20]
    have h26 : R1 26 = BitVec.ofNat 64 d.rep.p := by rw [hk1.get 26 (by decide)]; bsimp [st.r26]
    have hyp : y'.rep.p = y'.sb.pay := (hp'.heap.blocks y' List.mem_cons_self).sPay
    have hm' : Num.div y.rep.num Num.one rs = some m := by rw [← env.oneNum]; exact hm
    refine sq_tail hlive cx
      { sa :=
          { r2 := by rw [hk2.get 2 (by decide)]; bsimp [h2']
            saved := ra.saved.transport (lo := 48) (top := 160) (hag := fun a h1 h3 => by
              rw [hp'.out a (outHeap_of_ge (by simp only [heapEnd]; omega))
                (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)]
              exact ho1 a (outHeap_of_ge (by simp only [heapEnd]; omega))
                (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega))
            keep := hk2'
            out := fun _ _ _ => rfl }
        heap := hb2
        own := hown'
        ok := fun h hh => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          rcases hh with rfl | rfl | rfl | rfl | rfl
          · exact env.p5ok
          · exact st.okD
          · exact st.oky
          · exact hokG
          · exact ⟨hp'.refs, hp'.owns⟩ }
      (by rw [hk2.get 25 (by decide)]; bsimp [h25]) (by rw [hk2.get 8 (by decide)]; bsimp [h8])
      (by rw [hk2.get 20 (by decide)]; bsimp [h20]) (by rw [hk2.get 26 (by decide)]; bsimp [h26])
      fun R'' M'' H'' F'' hk'' h10'' hout'' hbF _ => hret R'' M'' H'' F'' (y' :: Ld) y' hk'' h10''
        { heap := hbF
          mid := ⟨Lb, Ld, hl, ⟨A, B, x, eL, rfl, hfrA⟩, .fresh hp'.refs⟩
          num := by
            rw [hp'.num]
            show m = (Num.div y.rep.num Num.one rs).getD y.rep.num
            rw [hm']; rfl
          norm := hp'.norm
          pos := hp'.pos
          owns := hp'.owns
          slot := by
            rw [ldv_congr .ld fun j hj => hout'' _ (hsl.out _ (by simp only [slotBytes, widthOfM] at hj ⊢; omega))
              (by simp only [frameIn, widthOfM] at hj ⊢; omega), hp'.slot, hyp]
          out := fun a ha hs hf => by
            rw [hout'' a ha hf, hp'.out a ha hs (fun h' => hf (by simp only [frameIn] at h' ⊢; omega)),
              ho1 a ha hs (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
            exact ra.out a ha hf }
  · rw [env.oneNum] at hn
    unfold Num.div at hn
    rw [if_neg (by simpa using hone1)] at hn
    cases hn

end Dc.Mach
