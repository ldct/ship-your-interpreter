import Dc.Mach.Bc.SqrtHi

/-!
# `bc_sqrt`'s entry (`0x80006a1c` to the first guess)

    6a1c prologue; `x`'s sign against `_zero_`'s: a negative `x` returns 0 (6c50)
    6c7c _bc_do_compare (x, _zero_, 1): equal → 6eb4: *num = _zero_, one more reference, 1
    6c98 _bc_do_compare (x, _one_, 1) (6e68): equal → 6e7c: *num = _one_, one more reference, 1
    6ed8 s5-s11 saved, rscale, `_zero_`'s count raised by three (guess, guess1, diff),
         point5 = 0.5 by bc_new_num (1, 1)
    6f34 below one → 6d04 (`sq_lo`), above → 6ad4 (`sq_hi`)

- `SqOut.of_*`: the model's result on each machine route.
- `SqE`: the state after the prologue.
- `sq_glob`: `bc_free_num (num)`, then a global with one more reference.
- `sq_setup`: the saves, the references and `point5`, landing `SqS`.
- `bc_sqrt_spec`: the whole function.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## The model on each route -/

theorem Num.cmp_zero_neg {x : Num} (h : x.neg = true) : Num.cmp x (Num.zero 0) = .lt := by
  simp [Num.cmp, Num.zero, h]

theorem Num.cmp_zero_pos {x : Num} (h : x.neg = false) :
    Num.cmp x (Num.zero 0) = Num.cmpMag x (Num.zero 0) := by
  simp [Num.cmp, Num.zero, h]

theorem Num.cmpMag_zero_ne_lt (x : Num) : Num.cmpMag x (Num.zero 0) ≠ .lt := by
  simp only [Num.cmpMag, Num.align, Num.zero, Nat.zero_mul, ne_eq, Nat.compare_eq_lt]
  omega

theorem Num.mag_of_cmpMag_zero {x : Num} (h : Num.cmpMag x (Num.zero 0) = .gt) : x.mag ≠ 0 := by
  intro h0
  simp only [Num.cmpMag, Num.align, Num.zero, Nat.zero_mul, h0, Nat.compare_eq_gt] at h
  omega

theorem SqOut.of_neg {x : Num} {k : Nat} {n : Option Num} (h : SqOut x k n)
    (hc : Num.cmp x (Num.zero 0) = .lt) : n = none := by
  cases h <;> simp_all

theorem SqOut.of_zero {x : Num} {k : Nat} {n : Option Num} (h : SqOut x k n)
    (hc : Num.cmp x (Num.zero 0) = .eq) : n = some (Num.zero 0) := by
  cases h <;> simp_all

theorem SqOut.of_one {x : Num} {k : Nat} {n : Option Num} (h : SqOut x k n)
    (hc : Num.cmp x (Num.zero 0) = .gt) (h1 : Num.cmp x Num.one = .eq) : n = some Num.one := by
  cases h <;> simp_all

theorem SqOut.of_root {x : Num} {k : Nat} {n : Option Num} (h : SqOut x k n)
    (hc : Num.cmp x (Num.zero 0) = .gt) (h1 : Num.cmp x Num.one ≠ .eq) :
    ∃ r, n = some r ∧ Sqrt x k r := by
  cases h with
  | neg h' => simp_all
  | zero h' => simp_all
  | one _ h' => exact absurd h' h1
  | root _ _ hs => exact ⟨_, rfl, hs⟩

theorem KZero.num {M : Mem} {z : NumObj} {k : Nat} (h : KZero M z k) : z.rep.num = Num.zero 0 := by
  simp only [NumRep.num, h.ds, h.scale, h.neg, Num.zero, dval, List.foldl]

/-! ## After the prologue -/

/-- After the prologue: the eight registers saved, `s1 = x`, `s2 = &_zero_`,
`s3 = num`, `s4 = scale`, `s10 = _zero_`, the heap. -/
structure SqE (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (x z : NumObj) (k : Nat) : Prop where
  sa : SqAt S Mt0 M R0 R sp W sqSlots0
  heap : BcHeap S M H F L
  cs : ∀ r ∈ [21, 22, 23, 25, 27], R r = R0 r
  r9 : R 9 = BitVec.ofNat 64 x.rep.p
  r18 : R 18 = BitVec.ofNat 64 zeroAddr
  r19 : R 19 = BitVec.ofNat 64 q
  r20 : R 20 = BitVec.ofNat 64 k
  r26 : R 26 = BitVec.ofNat 64 z.rep.p

/-- **A global with one more reference** in `*num`, from `0x80006e84`
(`_one_` through `sp + 8`) or `0x80006ebc` (`_zero_` through `s2`), then the
epilogue with `a0 = 1`. -/
theorem sq_globTail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {A B : List NumObj} {y : NumObj} {pc : BitVec 64} {ga : Nat} (cx : SqCtx S R0 sp W q)
    (hpc : (pc = 0x80006e84#64 ∧ ga = oneAddr ∧
        ldv .ld M (sp - 160 + 8) = BitVec.ofNat 64 oneAddr) ∨
      (pc = 0x80006ebc#64 ∧ ga = zeroAddr ∧ R 18 = BitVec.ofNat 64 zeroAddr))
    (hb : BcHeap S M H F (A ++ y :: B)) (hga : ldv .ld M ga = BitVec.ofNat 64 y.rep.p)
    (hr : y.rep.refs + 1 < 2 ^ 31)
    (sv : SavedWords M (sp - 160) sqSlots0 R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 160))
    (hkp : Keeps sqAll R R0) (hcs : ∀ r ∈ [21, 22, 23, 25, 27], R r = R0 r)
    (h19 : R 19 = BitVec.ofNat 64 q)
    (hk : ∀ R' M', Keeps binClob R' R0 → R' 10 = 1#64 →
      BcHeap S M' H F (A ++ y.withRefs (y.rep.refs + 1) :: B) →
      ldv .ld M' q = BitVec.ofNat 64 y.rep.p →
      (∀ a, OutHeap a → ¬ slotBytes q a → imgM M' a = imgM M a) → DW live S Q (R0 1) R' M') :
    DW live S Q pc R M := by
  sq_facts cx
  have hsf := cx.cc.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hym : y ∈ A ++ y :: B := List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums y hym
  num_facts hn
  have hrf := hn.refs
  have hsx := addiw1_ofNat (c := y.rep.refs) hr
  have hb1 := hb.setRefs (k := y.rep.refs + 1) (v := BitVec.ofNat 64 (y.rep.refs + 1))
    (toNat_ofNat_mod32 (by omega)) hr
  have hb2 := hb1.out_frame (P := slotBytes q)
    (MemOnly.store _ q 8 (BitVec.ofNat 64 y.rep.p)) hsl.out
  have hq0 := hsl.out q ⟨Nat.le_refl _, by omega⟩
  have hq7 := hsl.out (q + 7) ⟨by omega, by omega⟩
  simp only [OutHeap, heapStart, heapEnd] at hq0 hq7
  have e1 : (BitVec.ofNat 64 oneAddr).toNat = oneAddr := by rw [BitVec.toNat_ofNat]; rfl
  have e0 : (BitVec.ofNat 64 zeroAddr).toNat = zeroAddr := by rw [BitVec.toNat_ofNat]; rfl
  have hpq : ∀ a, OutHeap a → ¬ slotBytes q a →
      (a < q ∨ q + 8 ≤ a) ∧ (a < y.rep.p + 12 ∨ y.rep.p + 12 + 4 ≤ a) := fun a ha hs => by
    simp only [slotBytes] at hs
    simp only [OutHeap, heapStart, heapEnd] at ha
    omega
  have hfr : ∀ a, sp - 160 + 48 ≤ a → a < sp - 160 + 160 →
      imgM (writeLog (writeLog M [(y.rep.p + 12, 4, BitVec.ofNat 64 (y.rep.refs + 1))])
        [(q, 8, BitVec.ofNat 64 y.rep.p)]) a = imgM M a := fun a h1 h2 => by
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have h21 := hcs 21 (by decide); have h22 := hcs 22 (by decide); have h23 := hcs 23 (by decide)
  have h25 := hcs 25 (by decide); have h27 := hcs 27 (by decide)
  have hsx2 : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (y.rep.refs + 1))) =
      BitVec.ofNat 64 (y.rep.refs + 1) := sxw_ofNat (by omega)
  rcases hpc with ⟨rfl, rfl, hg⟩ | ⟨rfl, rfl, hg⟩
  all_goals bc_run hlive hS [h2, hg, e1, e0, hga, hrf, hsx, hsx2, h19] at 0x80006c54
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (guard_target =~ LdOK _ _
       have eo : oneAddr = 0x8001cdc0 := rfl; have ez : zeroAddr = 0x8001cdc8 := rfl
       have htx : tohostAddr = 0x8001ad00 := rfl
       bc_addr)
    | exact hq.acc
    | exact fun b hb' => cx.cc.consts b (by
        have := of_mem_accAddrs hb'
        have eo : oneAddr = 0x8001cdc0 := rfl; have ez : zeroAddr = 0x8001cdc8 := rfl
        have et : twoAddr = 0x8001cdb8 := rfl
        simp only [constBytes]; omega)
    | skip
  all_goals
    refine sq_epi hlive cx hS (sv.transport (lo := 48) (top := 160) (hag := hfr))
      (by bsimp [h2]) (by keeps_tac hkp) (fun r hr' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl <;> bsimp [h21, h22, h23, h25, h27])
      fun R' hk' h10 => hk R' _ hk' (by rw [h10]; bsimp []) hb2 (ldv_store_hit _ _ _)
        fun a ha hs => by
          rw [imgM_store_miss _ _ (hpq a ha hs).1, imgM_store_miss _ _ (hpq a ha hs).2]

/-- **`bc_free_num (num)`, then the global `g` with one more reference in
`*num`** and `1`, from `0x80006e7c` (`_one_`) or `0x80006eb4` (`_zero_`). -/
theorem sq_glob {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {x z o g : NumObj} {pc : BitVec 64} {ga : Nat}
    (cx : SqCtx S R0 sp W q) (ha : SqArgs S Mt0 L x z o q k)
    (st : SqE S Mt0 M R0 R sp W q H F L x z k)
    (hpc : (pc = 0x80006e7c#64 ∧ ga = oneAddr ∧
        ldv .ld M (sp - 160 + 8) = BitVec.ofNat 64 oneAddr) ∨
      (pc = 0x80006eb4#64 ∧ ga = zeroAddr ∧ True))
    (hg : g ∈ L) (hgw : ldv .ld Mt0 ga = BitVec.ofNat 64 g.rep.p)
    (hgr : x.rep.p = g.rep.p → 2 ≤ x.rep.refs) (hgN : g.rep.Norm) (hgl : 1 ≤ g.rep.len)
    (hret : ∀ R' M' H' F' Lf y', Keeps binClob R' R0 → R' 10 = 1#64 →
      SqPost S Mt0 M' H' F' L x z q sp W g.rep.num Lf y' → DW live S Q (R0 1) R' M') :
    DW live S Q pc R M := by
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have sa := st.sa
  have h2 := sa.r2
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hgq : q + 8 ≤ ga ∨ ga + 8 ≤ q := by
    rcases hpc with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact cx.slotOne
    · exact cx.slotZero
  have hgc : ga = oneAddr ∨ ga = zeroAddr := by
    rcases hpc with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact .inl rfl
    · exact .inr rfl
  have hga0 : 0x8001cdc0 ≤ ga ∧ ga + 8 ≤ 0x8001cdd0 := by
    rcases hgc with rfl | rfl <;> exact ⟨by decide, by decide⟩
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem ha.mx
  have hown := ha.owns
  have hwq : ldv .ld M q = BitVec.ofNat 64 x.rep.p := by
    rw [ldv_congr .ld fun j hj => sa.out _ (hsl.out _ (by simp only [widthOfM] at hj; omega))
      (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact ha.wx
  have hsr : ResSlot M L1 x q :=
    ⟨ha.rx, hwq, fun _ hxo w hw => hb.owner_db_ne hxo hw (hown w (List.mem_append_left _ hw))⟩
  have h19 := st.r19
  have h21 := st.cs 21 (by decide); have h22 := st.cs 22 (by decide); have h23 := st.cs 23 (by decide)
  have h25 := st.cs 25 (by decide); have h27 := st.cs 27 (by decide)
  have h18 := st.r18
  rcases hpc with ⟨rfl, hge, hw8⟩ | ⟨rfl, hge, -⟩
  all_goals bc_run hlive hS [h2, h19] at 0x800048c0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals
    refine free_slot_spec hlive (sp' := sp - 160)
      ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
      (by simp only [heapEnd]; omega) hq hsl.out (by omega) hb hsr (by bsimp [h2])
      (by bsimp [h19]) (by bsimp []; try decide) fun R1 M1 H1 F1 Ld hk1 hfr hb1 h0 ho1 => ?_
    bsimp []
    have hM1 : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn (sp - 160) 32 a → ¬ frameIn sp W a →
        imgM M1 a = imgM Mt0 a := fun a h1 h3 h4 h5 => (ho1 a h1 h3 h4).trans (sa.out a h1 h5)
    have hga1 : ldv .ld M1 ga = BitVec.ofNat 64 g.rep.p := by
      have hgo : ∀ j, j < 8 → OutHeap (ga + j) := fun j hj => by
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
      rw [ldv_congr .ld fun j hj => hM1 _ (hgo j (by simp only [widthOfM] at hj; omega))
        (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
        (by simp only [frameIn, widthOfM] at hj ⊢; omega)
        (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
      exact hgw
    have sv1 : SavedWords M1 (sp - 160) sqSlots0 R0 := sa.saved.transport (lo := 48) (top := 160)
      (hag := fun a h1 h2 => ho1 a (outHeap_of_ge (by simp only [heapEnd]; omega))
        (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega))
    have h2' : R1 2 = BitVec.ofNat 64 (sp - 160) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
    have h19' : R1 19 = BitVec.ofNat 64 q := by rw [hk1.get 19 (by decide)]; bsimp [h19]
    have h18' : R1 18 = BitVec.ofNat 64 zeroAddr := by rw [hk1.get 18 (by decide)]; bsimp [h18]
    have hcs1 : ∀ r ∈ [21, 22, 23, 25, 27], R1 r = R0 r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        (rw [hk1.get _ (by decide)]; bsimp [h21, h22, h23, h25, h27])
    have hkp1 : Keeps sqAll R1 R0 :=
      (hk1.mono (ks' := sqAll) (by decide)).trans (by keeps_tac sa.keep)
    have hw81 : ga = oneAddr → ldv .ld M (sp - 160 + 8) = BitVec.ofNat 64 oneAddr →
        ldv .ld M1 (sp - 160 + 8) = BitVec.ofNat 64 oneAddr := fun _ hw8 => by
      rw [ldv_congr .ld fun j hj => ho1 _ (outHeap_of_ge (by
        simp only [heapEnd, widthOfM] at hj ⊢; omega))
        (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
        (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
      exact hw8
    have hout : ∀ M', (∀ a, OutHeap a → ¬ slotBytes q a → imgM M' a = imgM M1 a) →
        ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M' a = imgM Mt0 a :=
      fun M' ho' a ha' hs' hf => by
        rw [ho' a ha' hs']
        exact hM1 a ha' hs' (fun h => hf (by simp only [frameIn] at h ⊢; omega)) hf
    obtain ⟨A, B, hAB⟩ := List.append_of_mem (List.mem_append_left [] hg)
    rw [List.append_nil] at hAB
    rcases FreedRest.around hfr hAB with ⟨A', B', rfl, hd, -⟩ | ⟨rfl, rfl, rfl⟩
    · refine sq_globTail hlive cx (by first | exact .inl ⟨rfl, hge, hw81 hge hw8⟩ | exact .inr ⟨rfl, hge, h18'⟩) hb1 hga1 (by have := ha.refs g hg; omega) sv1 h2' hkp1
        hcs1 h19' fun R' M' hk' h10 hb' hq' ho' => hret R' M' H1 F1 _ _ hk' h10
          ⟨hb', ⟨_, _, .inl rfl, by rw [hAB]; exact hd g, AddRef.share⟩, rfl, hgN, hgl,
            hown g hg, hq', hout M' ho'⟩
    · cases hfr with
      | rel h => have := hgr rfl; omega
      | dec h =>
        refine sq_globTail hlive cx (y := x.decRef)
          (by first | exact .inl ⟨rfl, hge, hw81 hge hw8⟩ | exact .inr ⟨rfl, hge, h18'⟩) hb1 hga1
          (by simp only [NumObj.decRef]; have := ha.refs x hg; omega) sv1 h2' hkp1
          hcs1 h19' fun R' M' hk' h10 hb' hq' ho' => hret R' M' H1 F1 _ _ hk' h10
            ⟨hb', ⟨_, _, .inl rfl, ⟨_, _, x, rfl, rfl, .dec h⟩, AddRef.share⟩, rfl, hgN, hgl,
              hown x hg, hq', hout M' ho'⟩

/-! ## The setup of the Newton loop -/

/-- An owned handle first: its number heads the heap. -/
theorem RList.own_cons (y : NumObj) (hs : List RH) (L : List NumObj) :
    RList (.own y :: hs) L = y :: RList hs L := by
  have h := rBump_own [] hs y
  simp only [List.nil_append] at h
  simp only [RList, rTemps_own, List.cons_append, h]

/-- Three references to `z` of `A ++ z :: B`: its count raised by three. -/
theorem RList.ref3 {A B : List NumObj} {z : NumObj} (hd : ∀ w ∈ A ++ B, w.rep.p ≠ z.rep.p) :
    RList [.ref z, .ref z, .ref z] (A ++ z :: B) = A ++ z.withRefs (z.rep.refs + 3) :: B := by
  have hc : ∀ w ∈ A ++ B, rBump [.ref z, .ref z, .ref z] w = w := fun w hw => by
    simp only [rBump, rCnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RH.cnt,
      if_neg (Ne.symm (hd w hw)), Nat.add_zero, NumObj.withRefs_self]
  simp only [RList, rTemps_ref, rTemps_nil, List.nil_append, List.map_append, List.map_cons]
  rw [List.map_congr_left (fun w hw => hc w (List.mem_append_left _ hw)),
    List.map_congr_left (fun w hw => hc w (List.mem_append_right _ hw)), List.map_id', List.map_id']
  congr 2
  simp only [rBump, rCnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RH.cnt,
    if_pos rfl, ite_true]
  rfl

/-- The fixed facts of the route into the Newton loop: `x > 0`, `x ≠ 1`, the
model's root `r`, the continuations. -/
structure SqSet (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t : String) (Mt0 : Mem) (R0 : Nat → BitVec 64) (sp W q k : Nat) (L : List NumObj)
    (x z o : NumObj) (r : Num) : Prop where
  cx : SqCtx S R0 sp W q
  ha : SqArgs S Mt0 L x z o q k
  oom : RaOom live S (DQ live S Q t) Mt0 sp W q
  xneg : x.rep.neg = false
  x0 : x.rep.num.mag ≠ 0
  ne1 : Num.cmp x.rep.num Num.one ≠ .eq
  xz : x.rep.p ≠ z.rep.p
  xo : x.rep.p ≠ o.rep.p
  oz : o.rep.p ≠ z.rep.p
  ilen : x.rep.num.intLen = x.rep.len
  sqrt : Sqrt x.rep.num k r
  ret : ∀ R' M' H' F' Lf y', Keeps binClob R' R0 → R' 10 = 1#64 →
    SqPost S Mt0 M' H' F' L x z q sp W r Lf y' → DW live S (DQ live S Q t) (R0 1) R' M'

/-- **`point5 = 0.5`** from `0x80006f20` (`bc_new_num (1, 1)` returned
`y`): its second digit `5`, then below one to `sq_lo`, above to `sq_hi`. -/
theorem sq_setNew {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {x z o y : NumObj} {r : Num}
    (g : SqSet live S Q t Mt0 R0 sp W q k L x z o r)
    (sa : SqAt S Mt0 M R0 R sp W sqSlots1)
    (hb : BcHeap S M H F (y :: RList [.ref z, .ref z, .ref z] L))
    (hy : y.rep = zeroRep y.sb.pay y.db.pay 1 1) (h10 : R 10 = BitVec.ofNat 64 y.sb.pay)
    (h8 : R 8 = ordWord (Num.cmp x.rep.num Num.one)) (h19 : R 19 = BitVec.ofNat 64 q)
    (h24 : R 24 = BitVec.ofNat 64 (max k x.rep.scale)) (h26 : R 26 = BitVec.ofNat 64 z.rep.p)
    (wq : ldv .ld M q = BitVec.ofNat 64 x.rep.p)
    (w8 : ldv .ld M (sp - 160 + 8) = BitVec.ofNat 64 oneAddr)
    (w24 : ldv .ld M (sp - 160 + 24) = BitVec.ofNat 64 z.rep.p)
    (w32 : ldv .ld M (sp - 160 + 32) = BitVec.ofNat 64 z.rep.p)
    (w40 : ldv .ld M (sp - 160 + 40) = BitVec.ofNat 64 z.rep.p) :
    DW live S (DQ live S Q t) 0x80006f20#64 R M := by
  have cx := g.cx
  have ha := g.ha
  sq_facts cx
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hyn := hb.nums y List.mem_cons_self
  have hyp : y.rep.p = y.sb.pay := by rw [hy]; rfl
  have hyv : y.rep.val = y.db.pay := by rw [hy]; rfl
  have hyl : y.rep.len = 1 := by rw [hy]; rfl
  have hys : y.rep.scale = 1 := by rw [hy]; rfl
  have hyr : y.rep.refs = 1 := by rw [hy]; rfl
  have hyd : y.rep.ds = [0, 0] := by rw [hy]; rfl
  have hyg : y.rep.neg = false := by rw [hy]; rfl
  have hyo : y.Owns := by
    have := hyn.shape.vLo
    show y.rep.ptr ≠ 0
    rw [hy]; simp only [zeroRep]; rw [← hyv]; simp only [heapStart] at this; omega
  num_facts hyn
  have hval := hyn.value
  rw [← hyp] at h10
  have hb1 := (List.nil_append (y :: RList [.ref z, .ref z, .ref z] L)).symm ▸ hb
  have hb2 := BcHeap.setDigit (L1 := []) hb1 (fun w hw => hb.head_noView hyo w (by simpa using hw))
    (i := 1) (d := 5) (by rw [hyl, hys]; decide) (by decide) (v := BitVec.ofNat 64 5)
    (by rw [sbData_ofNat])
  simp only [List.nil_append] at hb2
  have hc := g.ne1
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi
  have hq0 := hsl.out q ⟨Nat.le_refl _, by omega⟩
  have hq7 := hsl.out (q + 7) ⟨by omega, by omega⟩
  simp only [OutHeap, heapStart, heapEnd] at hq0 hq7
  have hdq : ∀ a, OutHeap a → imgM (writeLog M [(y.rep.val + 1, 1, BitVec.ofNat 64 5)]) a =
      imgM M a := fun a ha' => imgM_store_miss _ _ (by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha'; omega)
  have h5n : ({ y with rep := { y.rep with ds := y.rep.ds.set 1 5 } } : NumObj).rep.num =
      Num.half := by
    show (⟨y.rep.neg, dval (y.rep.ds.set 1 5), y.rep.scale⟩ : Num) = Num.half
    rw [hyg, hyd, hys]; rfl
  obtain ⟨Az, Bz, eZ⟩ := List.append_of_mem ha.mz
  have st : SqS S Mt0 (writeLog M [(y.rep.val + 1, 1, BitVec.ofNat 64 5)]) R0
      (upd (upd (upd (upd R 14 (BitVec.ofNat 64 y.rep.val)) 13 5#64) 15 18446744073709551615#64) 20
        (BitVec.ofNat 64 y.rep.p)) sp W q H F L x z
      { y with rep := { y.rep with ds := y.rep.ds.set 1 5 } } (max k x.rep.scale) :=
    { fr :=
        { sa := (sa.heap cx (hag := hdq)).regs (ks := [14, 13, 15, 20]) (by keeps_tac Keeps.refl _ _)
          heap := by rw [RList.own_cons]; exact hb2
          own := ⟨fun w hw => by
              simp only [List.mem_cons, RH.own.injEq, reduceCtorEq, List.not_mem_nil,
                or_false] at hw
              subst hw; exact hyo, ha.owns⟩
          ok := fun h hh => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
            rcases hh with rfl | rfl | rfl | rfl
            · exact ⟨hyr, hyo⟩
            all_goals exact ⟨Az, Bz, eZ, ha.zero.refs⟩ }
      r19 := by bsimp [h19]
      r20 := by bsimp []
      r24 := by bsimp [h24]
      r26 := by bsimp [h26]
      wq := by rw [ldv_ld_miss _ _ (by omega)]; exact wq
      w8 := by rw [ldv_ld_miss _ _ (by omega)]; exact w8
      w24 := by rw [ldv_ld_miss _ _ (by omega)]; exact w24
      w32 := by rw [ldv_ld_miss _ _ (by omega)]; exact w32
      w40 := by rw [ldv_ld_miss _ _ (by omega)]; exact w40 }
  have h5N : ({ y with rep := { y.rep with ds := y.rep.ds.set 1 5 } } : NumObj).rep.Norm :=
    .inl (by show y.rep.len ≤ 1; omega)
  have hS0 := g.sqrt
  unfold Sqrt at hS0
  cases hcmp : Num.cmp x.rep.num Num.one with
  | eq => exact absurd hcmp hc
  | lt =>
    rw [hcmp] at h8
    simp only [ordWord] at h8
    bc_run hlive hS [h10, hval, h8] at 0x80006d04
    rw [Dc.BcModel.sqrtInit_lo hcmp] at hS0
    exact sq_lo hlive (p5 := { y with rep := { y.rep with ds := y.rep.ds.set 1 5 } }) cx ha g.oom st h5n hyl hys h5N rfl g.xneg hcmp g.x0 g.xz g.xo g.oz hS0 g.ret
  | gt =>
    rw [hcmp] at h8
    simp only [ordWord] at h8
    bc_run hlive hS [h10, hval, h8] at 0x80006ad4
    bc_run hlive hS [] at 0x80006ad4
    rw [Dc.BcModel.sqrtInit_hi (by rw [hcmp]; decide) (by rw [g.ilen]; have := ha.size; omega),
      g.ilen] at hS0
    exact sq_hi hlive (p5 := { y with rep := { y.rep with ds := y.rep.ds.set 1 5 } })
      { cx := cx, ha := ha, oom := g.oom, p5n := h5n, p5l := hyl, p5s := hys, p5N := h5N,
        rsk := rfl, xneg := g.xneg, gt := hcmp, xz := g.xz, xo := g.xo, oz := g.oz,
        loop := hS0, ret := g.ret } st

/-- `addiw` of a small count. -/
theorem addiw_ofNat {c d : Nat} (hc : c + d < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 c + BitVec.ofNat 64 d)) =
      BitVec.ofNat 64 (c + d) := by
  rw [show BitVec.ofNat 64 c + BitVec.ofNat 64 d = BitVec.ofNat 64 (c + d) by
    rw [BitVec.ofNat_add]]
  exact sxw_ofNat hc

/-- **`_zero_`'s count raised by three** and stored as `guess`, `guess1`
and `diff`, then `bc_new_num (1, 1)`, from `0x80006efc`. -/
theorem sq_setRefs {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {x z o : NumObj} {r : Num}
    (g : SqSet live S Q t Mt0 R0 sp W q k L x z o r) (sa : SqAt S Mt0 M R0 R sp W sqSlots1)
    (hb : BcHeap S M H F L)
    (h8 : R 8 = ordWord (Num.cmp x.rep.num Num.one)) (h19 : R 19 = BitVec.ofNat 64 q)
    (h24 : R 24 = BitVec.ofNat 64 (max k x.rep.scale)) (h26 : R 26 = BitVec.ofNat 64 z.rep.p)
    (wq : ldv .ld M q = BitVec.ofNat 64 x.rep.p)
    (w8 : ldv .ld M (sp - 160 + 8) = BitVec.ofNat 64 oneAddr) :
    DW live S (DQ live S Q t) 0x80006efc#64 R M := by
  have cx := g.cx
  have ha := g.ha
  sq_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := sa.r2
  have hsl := cx.slot
  have hq := hsl.slot
  have hap := hsl.apart
  have hql := hq.lo; have hqh := hq.hi
  have hq0 := hsl.out q ⟨Nat.le_refl _, by omega⟩
  have hq7 := hsl.out (q + 7) ⟨by omega, by omega⟩
  simp only [OutHeap, heapStart, heapEnd] at hq0 hq7
  have hzn := hb.nums z ha.mz
  num_facts hzn
  have hzr := ha.refs z ha.mz
  have hx3 := addiw_ofNat (c := z.rep.refs) (d := 3) (by omega)
  obtain ⟨Az, Bz, eZ⟩ := List.append_of_mem ha.mz
  have hd : ∀ w ∈ Az ++ Bz, w.rep.p ≠ z.rep.p := fun w hw => by
    have hp := hb.pdist; rw [eZ] at hp; exact hp.ne w hw
  have hb1 := (eZ ▸ hb).setRefs (k := z.rep.refs + 3) (v := BitVec.ofNat 64 (z.rep.refs + 3))
    (toNat_ofNat_mod32 (by omega)) (by omega)
  rw [← RList.ref3 hd, ← eZ] at hb1
  have hm3 : MemOnly (fun a => sp - 160 + 24 ≤ a ∧ a < sp - 160 + 48)
      (writeLog (writeLog (writeLog
        (writeLog M [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + 3))])
        [(sp - 160 + 24, 8, BitVec.ofNat 64 z.rep.p)]) [(sp - 160 + 32, 8, BitVec.ofNat 64 z.rep.p)])
        [(sp - 160 + 40, 8, BitVec.ofNat 64 z.rep.p)])
      (writeLog M [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + 3))]) := fun a ha' => by
    simp only [not_and, Nat.not_lt] at ha'
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]
  have hb2 := hb1.out_frame hm3 fun a h => outHeap_of_ge (by simp only [heapEnd]; omega)
  have hsx3 : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (z.rep.refs + 3))) =
      BitVec.ofNat 64 (z.rep.refs + 3) := sxw_ofNat (by omega)
  bc_run hlive hS [h2, h26, hzn.refs, hx3, hsx3] at 0x80004250
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hsf' : StackFrame S (sp - 160) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  -- memory at the call against `M` off the heap
  have hMc : ∀ a, OutHeap a → ¬ (sp - 160 + 24 ≤ a ∧ a < sp - 160 + 48) →
      imgM (writeLog (writeLog (writeLog
        (writeLog M [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + 3))])
        [(sp - 160 + 24, 8, BitVec.ofNat 64 z.rep.p)]) [(sp - 160 + 32, 8, BitVec.ofNat 64 z.rep.p)])
        [(sp - 160 + 40, 8, BitVec.ofNat 64 z.rep.p)]) a = imgM M a := fun a ha' hn => by
    rw [hm3 a hn, imgM_store_miss _ _ (by
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha'; omega)]
  refine bc_new_num_spec hlive hb2.newHeap hsf' (len := 1) (scale := 1)
    (by simp only [heapEnd]; omega) (by decide) (Nat.le_refl _) _ (by bsimp []) (by bsimp [])
    (by bsimp [h2]) (by bsimp []) ⟨fun R1 Mt1 H1 F1 y hk1 hp1 hr1 => ?_, fun R' Mt' hr2 hout => ?_⟩
  · bsimp []
    have hM1 : ∀ a, OutHeap a → ¬ (sp - 160 ≤ a ∧ a < sp - 112) → ¬ frameIn (sp - 160) (W - 160) a →
        imgM Mt1 a = imgM M a := fun a ha' h1 h3 => by
      rw [hp1.out a ha' (fun h => h3 (by simp only [frameIn] at h ⊢; omega)),
        hMc a ha' (fun h => h1 (by omega))]
    have hw : ∀ c, sp - 160 ≤ c → c + 8 ≤ sp - 160 + 48 →
        ldv .ld Mt1 c = ldv .ld (writeLog (writeLog (writeLog
          (writeLog M [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + 3))])
          [(sp - 160 + 24, 8, BitVec.ofNat 64 z.rep.p)]) [(sp - 160 + 32, 8, BitVec.ofNat 64 z.rep.p)])
          [(sp - 160 + 40, 8, BitVec.ofNat 64 z.rep.p)]) c := fun c h1 h3 =>
      ldv_congr .ld fun j hj => hp1.out _ (outHeap_of_ge (by
        simp only [heapEnd, widthOfM] at hj ⊢; omega))
        (by simp only [frameIn, widthOfM] at hj ⊢; omega)
    have hk' : Keeps raCallClob R1 R := (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
    refine sq_setNew hlive g
      (sa.call (hsp := by omega) (hW := by omega) (hkp := hk') (hag := hM1)
        (hst := fun a h1 _ => outHeap_of_ge (by simp only [heapEnd]; omega)))
      (NewNumPost.insert hb2 hp1) hp1.rep hr1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hk1.get 8 (by decide)]; bsimp [h8]
    · rw [hk1.get 19 (by decide)]; bsimp [h19]
    · rw [hk1.get 24 (by decide)]; bsimp [h24]
    · rw [hk1.get 26 (by decide)]; bsimp [h26]
    · rw [ldv_congr .ld fun j hj => hM1 _ (hsl.out _ (by simp only [widthOfM] at hj; omega))
        (by simp only [widthOfM] at hj; omega) (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
      exact wq
    · rw [hw _ (by omega) (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
        ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
      exact w8
    · rw [hw _ (by omega) (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
      exact ldv_store_hit _ _ _
    · rw [hw _ (by omega) (by omega), ldv_ld_miss _ _ (by omega)]
      exact ldv_store_hit _ _ _
    · rw [hw _ (by omega) (by omega)]
      exact ldv_store_hit _ _ _
  · refine g.oom R' Mt' (sp - 160 - 32) (by omega) (by omega) hr2 fun a ha' hs hf => ?_
    rw [hout a ha' (fun h => hf (by simp only [frameIn] at h ⊢; omega)),
      hMc a ha' (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
    exact sa.out a ha' hf

/-- The five stores of `s5`, `s6`, `s7`, `s9`, `s11` at `0x80006ed8`. -/
abbrev sq5 (M : Mem) (sp : Nat) (R : Nat → BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog M [(sp - 160 + 104, 8, R 21)])
    [(sp - 160 + 96, 8, R 22)]) [(sp - 160 + 88, 8, R 23)]) [(sp - 160 + 72, 8, R 25)])
    [(sp - 160 + 56, 8, R 27)]

theorem sq5_frame (M : Mem) {sp : Nat} (R : Nat → BitVec 64) {a : Nat}
    (ha : a < sp - 160 + 56 ∨ sp - 160 + 112 ≤ a) : imgM (sq5 M sp R) a = imgM M a := by
  simp only [sq5]
  repeat rw [imgM_store_miss _ _ (by omega)]

/-- After the five stores: the frame with all thirteen saved registers. -/
theorem SqE.saveAt {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z : NumObj} {k : Nat}
    (st : SqE S Mt0 M R0 R sp W q H F L x z k) (cx : SqCtx S R0 sp W q)
    (hk : Keeps sqAll R' R0) (h2 : R' 2 = BitVec.ofNat 64 (sp - 160)) :
    SqAt S Mt0 (sq5 M sp R) R0 R' sp W sqSlots1 := by
  sq_facts cx
  have e : sq5 M sp R = sq5 M sp R0 := by
    simp only [sq5, st.cs 21 (by decide), st.cs 22 (by decide), st.cs 23 (by decide),
      st.cs 25 (by decide), st.cs 27 (by decide)]
  exact
    { r2 := h2
      saved := by
        rw [e]
        exact ((((st.sa.saved.store 21 104).store 22 96).store 23 88).store 25 72).store 27 56
      keep := hk
      out := fun a ha hf => by
        rw [sq5_frame M R (by simp only [frameIn] at hf; omega)]
        exact st.sa.out a ha hf }

theorem SqE.saveHeap {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z : NumObj} {k : Nat}
    (st : SqE S Mt0 M R0 R sp W q H F L x z k) (cx : SqCtx S R0 sp W q) :
    BcHeap S (sq5 M sp R) H F L := by
  sq_facts cx
  exact st.heap.out_frame (P := fun a => sp - 160 + 56 ≤ a ∧ a < sp - 160 + 112)
    (fun a ha => sq5_frame M R (by omega)) fun a h => outHeap_of_ge (by simp only [heapEnd]; omega)

/-- **The setup** from `0x80006ed8` (`x` neither `0` nor `1`): `s5`-`s11`
saved, `rscale = max (scale, x.scale)`, then `sq_setRefs`. -/
theorem sq_setup {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {x z o : NumObj} {r : Num}
    (g : SqSet live S Q t Mt0 R0 sp W q k L x z o r) (st : SqE S Mt0 M R0 R sp W q H F L x z k)
    (w8 : ldv .ld M (sp - 160 + 8) = BitVec.ofNat 64 oneAddr)
    (h8 : R 8 = ordWord (Num.cmp x.rep.num Num.one)) :
    DW live S (DQ live S Q t) 0x80006ed8#64 R M := by
  have cx := g.cx
  have ha := g.ha
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.sa.r2
  have hsl := cx.slot
  have hq := hsl.slot
  have hap := hsl.apart
  have hql := hq.lo; have hqh := hq.hi
  have hxn := hb.nums x ha.mx
  num_facts hxn
  have hsz := ha.size
  have hsk := sxw_ofNat (k := k) (by omega)
  have wq : ldv .ld M q = BitVec.ofNat 64 x.rep.p := by
    rw [ldv_congr .ld fun j hj => st.sa.out _ (hsl.out _ (by simp only [widthOfM] at hj; omega))
      (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact ha.wx
  bc_run hlive hS [h2, st.r9, st.r20, hxn.scale, sxw_ofNat, toInt_ofNat_small] at 0x80006efc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals intro hks
  all_goals try (bc_run hlive hS [st.r20, hsk] at 0x80006efc)
  all_goals
    refine sq_setRefs hlive g (st.saveAt cx (by keeps_tac st.sa.keep) (by bsimp [h2]))
      (st.saveHeap cx) (by bsimp [h8]) (by bsimp [st.r19]) (by bsimp [st.r20]; congr 1; omega)
      (by bsimp [st.r26]) ?_ ?_
    all_goals
      try simp only [sq5]
      repeat rw [ldv_ld_miss _ _ (by omega)]
      first | exact wq | exact w8

end Dc.Mach
