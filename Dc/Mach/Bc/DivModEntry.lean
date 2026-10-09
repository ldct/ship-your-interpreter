import Dc.Mach.Bc.DivMod

/-!
# `bc_divmod`'s entry (`0x80005fd0` to `0x80006068`)

    if (num2 == _zero_ || bc_is_zero (num2)) return -1;   /* inlined */
    rscale = MAX (num1->n_scale, num2->n_scale + scale);
    temp = _zero_; _zero_->n_refs++;
    bc_divide (num1, num2, &temp, scale);

- `dmz_scan`: the inlined zero test of `num2`'s digits at `0x8000601c`.
- `dm_rscale`: `rscale` at `0x8000602c`.
- `DmAt68`: the state after `bc_divide` returns at `0x80006068`: the
  quotient `t` heads the heap, `_zero_` has its reference back.
- `DmPreK`: the continuations of the entry: `DmAt68`, `-1`, out of memory.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- The state at `0x80006068`, after `bc_divide (num1, num2, &temp, scale)`
returned the quotient `t` for `a` in `temp` (`sp - 72`). -/
structure DmAt68 (S : Nat → Prop) (R0 : Nat → BitVec 64) (Mt0 M : Mem) (R : Nat → BitVec 64)
    (H : Heap) (F : List Blk) (L : List NumObj) (x1 x2 z : NumObj) (k sp W : Nat) (a : Num)
    (t : NumObj) : Prop where
  sv : SavedWords M (sp - 80) dmSlots R0
  r2 : R 2 = BitVec.ofNat 64 (sp - 80)
  kp : Keeps dmAll R R0
  heap : BcHeap S M H F (t :: L)
  new : NewNum a t
  slot : ldv .ld M (sp - 80 + 8) = BitVec.ofNat 64 t.sb.pay
  out : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a
  zk : KZero M z (2 ^ 30)
  mb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80
  r8 : R 8 = BitVec.ofNat 64 x1.rep.p
  r9 : R 9 = BitVec.ofNat 64 x2.rep.p
  r18 : R 18 = BitVec.ofNat 64 (max x1.rep.scale (x2.rep.scale + k))
  r19 : R 19 = R0 12
  r21 : R 21 = R0 13

/-- The entry's continuations: the quotient at `0x80006068`, `-1` for a zero
divisor, out of memory. -/
structure DmPreK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (L : List NumObj) (x1 x2 z : NumObj) (k sp W : Nat) :
    Prop where
  div : ∀ a, Num.div x1.rep.num x2.rep.num k = some a → ∀ R M H F t,
    DmAt68 S R0 Mt0 M R H F L x1 x2 z k sp W a t → DW live S Q 0x80006068#64 R M
  zero : x2.rep.num.mag = 0 → DmZero live S Q R0 Mt0 sp W
  oom : DmOom live S Q Mt0 sp W

/-- **`num2`'s zero test** at `0x8000601c` (inlined): digits `0 … i - 1`
zero, `a5 = n - i`, `a6` at digit `i`; the first nonzero digit ends it at
`0x8000602c`, all `n` zero at `0x80006134`. -/
theorem dmz_scan {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {Rb : Nat → BitVec 64} (hS : HeapOwn S) {ds : List Nat} (hd : IsDigits ds)
    {v n : Nat} (hb : ∀ i, i < n → imgM M (v + i) = BitVec.ofNat 8 (ds.getD i 0)) (hn : n < 2 ^ 30)
    (hlo : 2147603920 ≤ v) (hhi : v + n ≤ 2273312768)
    (hfound : ∀ R', (∃ i0, i0 < n ∧ ds.getD i0 0 ≠ 0) → Keeps [15, 16, 17] R' Rb →
      DW live S Q 0x8000602c#64 R' M)
    (hnone : ∀ R', (∀ j, j < n → ds.getD j 0 = 0) → Keeps [15, 16, 17] R' Rb →
      DW live S Q 0x80006134#64 R' M) :
    ∀ k i R, i + 1 + k = n → (∀ j, j < i → ds.getD j 0 = 0) → Keeps [15, 16, 17] R Rb →
      R 15 = BitVec.ofNat 64 (n - i) → R 16 = BitVec.ofNat 64 (v + i) →
      DW live S Q 0x8000601c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  refine count_rec fun k i R ih hi hz kk h15 h16 => ?_
  have hl := lbu_digit (hd.getD i) (hb i (by omega))
  have hdl := hd.getD i
  have e1 : BitVec.ofNat 64 (v + i) + 1#64 = BitVec.ofNat 64 (v + (i + 1)) := by
    rw [show (1#64) = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat]; congr 1
  have e2 := subw_ofNat_le (a := n - i) (b := 1) (by omega) (by omega)
  have hq := ofNat_eq_zero_iff (show ds.getD i 0 < 2 ^ 64 by omega)
  bc_run hlive hS [h15, h16, hl, e1, e2] at 0x8000602c 0x80006018
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro h0
    replace h0 : ds.getD i 0 = 0 := hq.mp h0
    have hz' : ∀ j, j < i + 1 → ds.getD j 0 = 0 := fun j hj => by
      rcases Nat.lt_or_ge j i with h | h
      · exact hz j h
      · rw [show j = i by omega]; exact h0
    have e3 := ofNat_eq_zero_iff (show n - i - 1 < 2 ^ 64 by omega)
    bc_run hlive hS [e3] at 0x80006134 0x8000601c
    · intro h1
      exact hnone _ (fun j hj => hz' j (by omega)) (by keeps_tac kk)
    · intro h1
      rcases k with _ | k
      · omega
      exact ih k rfl _ (by omega) hz' (by keeps_tac kk) (by bsimp []; exact congrArg _ (by omega))
        (by bsimp [])
  · intro h0
    replace h0 : ds.getD i 0 ≠ 0 := fun e => h0 (hq.mpr e)
    exact hfound _ ⟨i, by omega, h0⟩ (by keeps_tac kk)

/-- **The `-1` return** from `0x800060e4` (`a0 = -1`), only the frame
changed. -/
theorem dm_neg {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} (cx : DmCtx S R0 sp W) (hS : HeapOwn S)
    (hz : DmZero live S Q R0 Mt0 sp W)
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (h10 : R 10 = 0xffffffffffffffff#64)
    (hfr : ∀ a, ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    DW live S Q 0x800060e4#64 R M :=
  dm_epi hlive cx hS sv h2 hkp fun R' kk e => hz R' M kk (e.trans h10) hfr

/-- **`rscale`** at `0x8000602c`: `max (num1->n_scale, num2->n_scale + scale)`
in `s2`. -/
theorem dm_rscale {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} (hS : HeapOwn S) {p s1 s2 k : Nat}
    (hp : 2147603920 ≤ p) (hp' : p + 12 ≤ 2273312768) (hs1 : s1 < 2 ^ 30) (hs2 : s2 + k < 2 ^ 30)
    (hl : ldv .lw M (p + 8) = BitVec.ofNat 64 s1)
    (h8 : R 8 = BitVec.ofNat 64 p) (h6 : R 6 = BitVec.ofNat 64 s2)
    (h14 : R 14 = BitVec.ofNat 64 k)
    (hk : ∀ R', Keeps [10, 15, 18] R' R → R' 18 = BitVec.ofNat 64 (max s1 (s2 + k)) →
      DW live S Q 0x8000603c#64 R' M) :
    DW live S Q 0x8000602c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have ea := addw_ofNat (a := k) (b := s2) (by omega)
  have t1 := toInt_ofNat_small (k := k + s2) (by omega)
  have t2 := toInt_ofNat_small (k := s1) (by omega)
  have x1 := sxw_ofNat (k := k + s2) (by omega)
  have x2 := sxw_ofNat (k := s1) (by omega)
  bc_run hlive hS [h8, h6, h14, hl, ea, t1, t2, x1, x2] at 0x8000603c
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro hlt
    bc_run hlive hS [x2] at 0x8000603c
    exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp [x2]; congr 1; omega)
  · intro hge
    exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp [x1]; congr 1; omega)

/-- A number of the heap, with the reference count of one entry changed. -/
theorem mem_setRefs {A B : List NumObj} {z y : NumObj} (k : Nat) (h : y ∈ A ++ z :: B) :
    ∃ j, y.withRefs j ∈ A ++ z.withRefs k :: B := by
  rcases List.mem_append.mp h with h1 | h1
  · exact ⟨y.rep.refs, List.mem_append_left _ (by rw [NumObj.withRefs_self]; exact h1)⟩
  · rcases List.mem_cons.mp h1 with rfl | h2
    · exact ⟨k, List.mem_append_right _ List.mem_cons_self⟩
    · exact ⟨y.rep.refs, List.mem_append_right _
        (List.mem_cons_of_mem _ (by rw [NumObj.withRefs_self]; exact h2))⟩

theorem NumObj.withRefs_succ_decRef (z : NumObj) : (z.withRefs (z.rep.refs + 1)).decRef = z := by
  rw [NumObj.decRef_eq, NumObj.withRefs_withRefs]
  exact NumObj.withRefs_self z

/-- `bc_divide`'s quotient back at `0x80006068`: `_zero_`'s extra reference
dropped, `DmAt68`. -/
theorem dm_divRet {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {Mt0 M Mt' : Mem} {R0 Rc R' : Nat → BitVec 64} {sp W k : Nat} {A B L' : List NumObj}
    {x1 x2 z y : NumObj} {H H' : Heap} {F F' : List Blk} {m : Num}
    (cx : DmCtx S R0 sp W) (hk : DmPreK live S Q R0 Mt0 (A ++ z :: B) x1 x2 z k sp W)
    (ha : DmArgs M (A ++ z :: B) x1 x2 z k) (hb : BcHeap S M H F (A ++ z :: B))
    (sv : SavedWords M (sp - 80) dmSlots R0)
    (hfr : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hm : Num.div x1.rep.num x2.rep.num k = some m)
    (h2 : Rc 2 = BitVec.ofNat 64 (sp - 80)) (hkp : Keeps dmAll Rc R0)
    (h8 : Rc 8 = BitVec.ofNat 64 x1.rep.p) (h9 : Rc 9 = BitVec.ofNat 64 x2.rep.p)
    (h18 : Rc 18 = BitVec.ofNat 64 (max x1.rep.scale (x2.rep.scale + k)))
    (h19 : Rc 19 = R0 12) (h21 : Rc 21 = R0 13) (kk : Keeps binClob R' Rc)
    (hp : BinPostW S (writeLog (writeLog M [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + 1))])
      [(sp - 80 + 8, 8, BitVec.ofNat 64 z.rep.p)]) Mt' H' F' A B (z.withRefs (z.rep.refs + 1))
      (sp - 80 + 8) (sp - 80) (W - 80) m L' y) :
    DW live S Q 0x80006068#64 R' Mt' := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have hzn := hb.nums z ha.mz
  num_facts hzn
  have hzr := ha.zero.refs
  have hL : L' = A ++ z :: B := by
    cases hp.rest with
    | dec h => rw [NumObj.withRefs_succ_decRef]
    | rel h => simp only [NumObj.withRefs] at h; omega
  subst hL
  have hstk : ∀ a, sp - 80 ≤ a → OutHeap a := fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hMt : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM Mt' a = imgM M a := fun a ha' hf => by
    rw [hp.out a ha' (by simp only [slotBytes, frameIn] at hf ⊢; omega)
      (by simp only [frameIn] at hf ⊢; omega), imgM_store_miss _ _ (by
        simp only [frameIn] at hf; omega), imgM_store_miss _ _ (by
        simp only [OutHeap, heapStart, heapEnd] at ha'; omega)]
  have hcst : ∀ j, j < 8 → imgM Mt' (zeroAddr + j) = imgM M (zeroAddr + j) := fun j hj =>
    hMt _ (constBytes_out (by simp only [constBytes, twoAddr, zeroAddr] at hj ⊢; omega))
      (by simp only [frameIn, zeroAddr]; omega)
  have hmbm : ∀ j, j < 4 → imgM Mt' (mulBaseAddr + j) = imgM M (mulBaseAddr + j) := fun j hj =>
    hMt _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, mulBaseAddr]; omega)
      (by simp only [frameIn, mulBaseAddr]; omega)
  refine hk.div m hm R' Mt' H' F' y
    { sv := sv.transport (lo := 24) (top := 80) (hag := fun a h1 h2' => by
        rw [hp.out a (hstk a (by omega)) (by simp only [slotBytes]; omega)
          (by simp only [frameIn]; omega), imgM_store_miss _ _ (by omega),
          imgM_store_miss _ _ (by omega)])
      r2 := by rw [kk.get 2]; exact h2
      kp := (kk.mono (by decide)).trans hkp
      heap := hp.heap
      new := ⟨hp.num, hp.norm, hp.pos, hp.refs, hp.owns⟩
      slot := hp.slot
      out := fun a ha' hf => (hMt a ha' hf).trans (hfr a ha' hf)
      zk := { ha.zero with glob := by rw [ldv_congr .ld hcst]; exact ha.zero.glob }
      mb := by rw [ldv_congr .lw hmbm]; exact ha.mulBase
      r8 := by rw [kk.get 8]; exact h8
      r9 := by rw [kk.get 9]; exact h9
      r18 := by rw [kk.get 18]; exact h18
      r19 := by rw [kk.get 19]; exact h19
      r21 := by rw [kk.get 21]; exact h21 }

/-- **`bc_divide (num1, num2, &temp, scale)`** from `0x8000603c`
(`num2` not `_zero_`, nonzero): `temp = _zero_` with one reference more, the
call, `DmPreK.div` at the return. -/
theorem dm_divCall {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W k : Nat} {L : List NumObj}
    {x1 x2 z : NumObj} {H : Heap} {F : List Blk}
    (cx : DmCtx S R0 sp W) (hk : DmPreK live S Q R0 Mt0 L x1 x2 z k sp W)
    (ha : DmArgs M L x1 x2 z k) (hb : BcHeap S M H F L) (hmag : x2.rep.num.mag ≠ 0)
    (sv : SavedWords M (sp - 80) dmSlots R0)
    (hfr : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 80)) (hkp : Keeps dmAll R R0)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h11 : R 11 = BitVec.ofNat 64 x2.rep.p) (h28 : R 28 = BitVec.ofNat 64 z.rep.p)
    (h12 : R 12 = R0 12) (h13 : R 13 = R0 13) (h14 : R 14 = BitVec.ofNat 64 k)
    (h18 : R 18 = BitVec.ofNat 64 (max x1.rep.scale (x2.rep.scale + k))) :
    DW live S Q 0x8000603c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hzn := hb.nums z ha.mz
  num_facts hzn
  have hzr := ha.zero.refs; have hzm := ha.zero.room
  have hsz := ha.size
  have ex := sxw_ofNat (k := z.rep.refs + 1) (by omega)
  obtain ⟨A, B, rfl⟩ := List.append_of_mem ha.mz
  bc_run hlive hS [h2, h8, h11, h28, h14, hzn.refs, ex] at 0x8000589c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | skip
  obtain ⟨j1, hm1⟩ := mem_setRefs (z.rep.refs + 1) ha.m1
  obtain ⟨j2, hm2⟩ := mem_setRefs (z.rep.refs + 1) ha.m2
  have hb1 := hb.setRefs (v := BitVec.ofNat 64 (z.rep.refs + 1)) (k := z.rep.refs + 1)
    (by rw [BitVec.toNat_ofNat]; omega) (by omega)
  have hb2 := hb1.out_frame (MemOnly.store _ (sp - 80 + 8) 8 (BitVec.ofNat 64 z.rep.p))
    fun a ha' => by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hz0 : ldv .ld (writeLog (writeLog M [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + 1))])
      [(sp - 80 + 8, 8, BitVec.ofNat 64 z.rep.p)]) zeroAddr = BitVec.ofNat 64 z.rep.p := by
    rw [ldv_store_miss _ _ _ (by simp only [widthOfM, zeroAddr]; omega),
      ldv_store_miss _ _ _ (by simp only [widthOfM, zeroAddr]; omega)]
    exact ha.zero.glob
  have hmz : (z.withRefs (z.rep.refs + 1)).rep.num.mag = 0 := by
    show z.rep.num.mag = 0
    rw [NumRep.num_mag, ha.zero.ds]; rfl
  refine bc_divide_spec (n := Num.div x1.rep.num x2.rep.num k) (sp := sp - 80) (q := sp - 80 + 8)
    (W := W - 80) (L1 := A) (L2 := B) (xr := z.withRefs (z.rep.refs + 1))
    (x1 := x1.withRefs j1) (x2 := x2.withRefs j2) (z := z.withRefs (z.rep.refs + 1)) hlive
    ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
      by simp only [heapEnd]; omega, by omega,
      ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩,
      fun a ha' => by simp only [slotBytes] at ha'; simp only [OutHeap, heapStart, heapEnd,
        freeListAddr, bcFreeAddr]; omega,
      .inr (by omega), .inr (by simp only [zeroAddr]; omega), cx.consts, by bsimp [h2],
      by bsimp []; try decide⟩
    ⟨fun m hm R' Mt' H' F' L' y kk _ hp => ?_, fun hn => absurd hn ?_,
      fun R' Mt' sp' hs1 hs2 hr2 hout => hk.oom R' Mt' sp' (by omega) (by omega) hr2
        fun a ha' hf => by
          rw [hout a ha' (by simp only [slotBytes, frameIn] at hf ⊢; omega)
            (by simp only [frameIn] at hf ⊢; omega), imgM_store_miss _ _ (by
              simp only [frameIn] at hf; omega), imgM_store_miss _ _ (by
              simp only [OutHeap, heapStart, heapEnd] at ha'; omega)]
          exact hfr a ha' hf⟩
    ⟨rfl, hm1, hm2, List.mem_append_right _ List.mem_cons_self,
      fun h => by simp only [NumObj.withRefs] at h; omega,
      by simp only [NumObj.withRefs]; omega, hz0, by simp only [NumObj.withRefs]; exact ha.len1⟩
    hmz hb2
    ⟨by simp only [NumObj.withRefs]; omega, ldv_store_hit _ _ _,
      fun h => by simp only [NumObj.withRefs] at h; omega⟩
    (by bsimp [h8]; rfl) (by bsimp [h11]; rfl) (by bsimp []) (by bsimp [h14])
  · bsimp []
    exact dm_divRet cx hk ha hb sv hfr hm (by bsimp [h2]) (by keeps_tac hkp) (by bsimp [h8])
      (by bsimp []) (by bsimp [h18]) (by bsimp [h12]) (by bsimp [h13]) kk hp
  · unfold Num.div
    split
    · rename_i h0; exact absurd (by simpa using h0) hmag
    · simp

end

end Dc.Mach
