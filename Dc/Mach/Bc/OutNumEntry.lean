import Dc.Mach.Bc.OutNumDec

/-!
# `bc_out_num`'s entry (`0x80006f3c`)

    0x80006f3c  the prologue; a negative number: out_char ('-')
    0x80006f7c  num = _zero_, or all its digits zero (the inlined `bc_is_zero`
                at `0x80006fb8`): the tail call out_char ('0') at `0x80007090`
    0x80006fc8  o_base = 10: `0x80006fd4` (`OutNumDec.lean`), otherwise
                `0x800070b8` (`OnBaseGo`)

- `on_zero`: the tail call.
- `on_post`: from after the sign to either branch.
- `on_entry`: the prologue and the sign.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- The sign `bc_out_num` writes first. -/
abbrev signOut (n : Dc.Num) : List Nat := if n.neg then [45] else []

/-- A number at `_zero_`'s address is zero. -/
theorem NumAt.mag_zero_at {M : Mem} {x z : NumRep} (hx : NumAt M x) (hz : NumAt M z)
    (hp : x.p = z.p) (hl : z.len = 1) (hs : z.scale = 0) (hd : z.ds = [0]) : x.num.mag = 0 := by
  have hxs := hx.shape; have hzs := hz.shape
  have := hxs.size; have := hzs.size; have := hxs.vHi; have := hzs.vHi
  have e1 : x.len = z.len := by
    have h := hx.len; rw [hp, hz.len] at h
    exact ((ofNat_eq_iff (by omega) (by omega)).mp h).symm
  have e2 : x.scale = z.scale := by
    have h := hx.scale; rw [hp, hz.scale] at h
    exact ((ofNat_eq_iff (by omega) (by omega)).mp h).symm
  have e3 : x.val = z.val := by
    have h := hx.value; rw [hp, hz.value] at h
    simp only [heapEnd] at *
    exact ((ofNat_eq_iff (by omega) (by omega)).mp h).symm
  refine NumRep.mag_zero_of hxs.dsLen fun j hj => ?_
  have hj0 : j = 0 := by omega
  subst hj0
  have h1 := hx.digit 0 (by omega)
  have h2 := hz.digit 0 (by omega)
  rw [e3, h2, hd] at h1
  have hd0 := IsDigits.getD hxs.dig 0
  have := congrArg BitVec.toNat h1
  simp only [BitVec.toNat_ofNat, List.getD_cons_zero] at this
  omega

/-- A word of the globals the callback leaves, as at entry. -/
theorem OnAt.glob {S G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {slots : List (Nat × Nat)} (h : OnAt S G Mt0 M R0 R sp W slots)
    (hG : ∀ a, G a → ¬ constBytes a) (hab : heapEnd + W ≤ sp) {a : Nat}
    (ha1 : twoAddr ≤ a) (ha2 : a + 8 ≤ zeroAddr + 8) :
    ldv .ld M a = ldv .ld Mt0 a :=
  ldv_congr .ld fun j hj => h.out _ (by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, widthOfM, twoAddr,
      zeroAddr] at hj ha1 ha2 ⊢; omega)
    (fun hg => hG _ hg ⟨by omega, by simp only [widthOfM] at hj; omega⟩)
    (by simp only [frameIn, heapEnd, widthOfM, twoAddr, zeroAddr] at hj hab ha1 ha2 ⊢; omega)

/-- Fewer saved words. -/
theorem OnAt.sub {S G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {slots slots' : List (Nat × Nat)} (h : OnAt S G Mt0 M R0 R sp W slots)
    (hs : ∀ p ∈ slots', p ∈ slots := by decide) : OnAt S G Mt0 M R0 R sp W slots' :=
  { h with saved := fun p hp => h.saved p (hs p hp) }

/-! ## The tail call (`0x80007090`) -/

theorem on_zero {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {pre : List Nat} {t : String}
    (cb : CharFn live S Q (R0 12) d G I) (cx : OnCtx S R0 sp W d)
    (st : OnAt S G Mt0 M R0 R sp W onSlots0) (hb : BcHeap S X M H F L) (hI : I pre t M)
    (hs : ∀ z ∈ [8, 19, 22, 24, 25, 26, 27], R z = R0 z)
    (hK : OnK live S X Q I G R0 Mt0 L sp W (pre ++ [48])) :
    DWO live S Q t 0x80007090#64 R M := by
  on_facts cx
  have hsf := cx.cc.frame
  have sv := st.saved
  have g1 := sv.get 1 168; have g9 := sv.get 9 152; have g18 := sv.get 18 144
  have g20 := sv.get 20 128; have g21 := sv.get 21 120; have g23 := sv.get 23 104
  have hr2 := st.r2; have hr9 := st.cb
  have hal := cx.al
  bc_run hlive hsf [hr2, hr9, g1, g9, g18, g20, g21, g23]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first | exact cx.fal | skip
  have hfr : StackFrame S sp d :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by have := hsf.lo; omega, hsf.hi, hsf.al⟩
  refine cb.call pre 48 t sp _ M hI hfr (by simp only [heapEnd]; omega)
    (by bsimp [hr2, cx.sp0]; congr 1; omega) (by bsimp []) (by decide) (by bsimp [g1]; exact hal)
    fun R' M' t' hk' hI' hm => ?_
  have e1 : ∀ v : BitVec 64, v = R0 1 → DWO live S Q t' v R' M' = DWO live S Q t' (R0 1) R' M' :=
    fun v hv => by rw [hv]
  rw [e1 _ (by bsimp [g1])]
  have hs' := fun z hz => hs z hz
  refine hK.ret R' M' t' H F (hk'.trans (Keeps.unwind (all := onAll)
    (saved := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := st.keep))) hI'
    (hb.out_frame (P := fun a => G a ∨ frameIn sp d a)
      (fun a hp => hm a (fun hg => hp (.inl hg)) (by
        simp only [frameIn, not_or, not_and, Nat.not_lt] at hp ⊢
        by_cases h : sp - d ≤ a
        · exact .inr (hp.2 h)
        · exact .inl (by omega)))
      (fun a ha => by
        rcases ha with hg | hf
        · exact (cb.off a hg).2.1
        · apply outHeap_of_ge; simp only [frameIn, heapEnd] at hf ⊢; omega))
    fun a ha hg hf => by
      rw [hm a hg (by simp only [frameIn] at hf; omega)]; exact st.out a ha hg hf
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | (bsimp [g1, g9, g18, g20, g21, g23, hr9]; done)
    | (bsimp []; exact hs' _ (by decide))
    | skip
  bsimp [hr2, cx.sp0]; congr 1; omega

/-! ## After the sign (`0x80006f7c`) -/

/-- **The branch for a base other than 10** at `0x800070b8`, as a premise:
from the frame with `s0`–`s7` saved, the heap, the sign sent, `s2` the
nonzero number, `a0` `_zero_`, `s4` its global, `s5` zero, `s7` the base. -/
def OnBaseGo (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x z : NumObj) (ob : Nat) (cs : List Nat) : Prop :=
  ∀ (R : Nat → BitVec 64) (M : Mem) (t : String) (H : Heap) (F : List Blk),
    OnAt S G Mt0 M R0 R sp W onSlots2 → BcHeap S X M H F L → I (cs ++ signOut x.rep.num) t M →
    R 18 = BitVec.ofNat 64 x.rep.p → R 10 = BitVec.ofNat 64 z.rep.p →
    R 20 = BitVec.ofNat 64 zeroAddr → R 21 = 0#64 → R 23 = BitVec.ofNat 64 ob →
    (∀ r ∈ [24, 25, 26, 27], R r = R0 r) → x.rep.num.mag ≠ 0 → ob ≠ 10 →
    DWO live S Q t 0x800070b8#64 R M

/-- The characters of a zero. -/
theorem outChars_zero {n : Dc.Num} {ob : Nat} (h : n.mag = 0) :
    Num.outChars n ob = signOut n ++ [48] := by
  simp [Num.outChars, Num.isZero, h, signOut]

/-- With `s6` and `s3` saved (`0x80006f90`, `0x80006f98`). -/
abbrev onSlots1 : List (Nat × Nat) := (19, 136) :: (22, 112) :: onSlots0

/-- The fixed facts of the entry: the callback, the frame, the operands, the
continuation for `x`'s characters after `cs`, and the other branch. -/
structure OnFix (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W d : Nat) (L : List NumObj) (x z o : NumObj) (ob : Nat) (cs : List Nat) : Prop where
  cb : CharFn live S Q (R0 12) d G I
  cx : OnCtx S R0 sp W d
  ha : OnArgs S Mt0 L x z o ob
  hK : OnK live S X Q I G R0 Mt0 L sp W (cs ++ Num.outChars x.rep.num ob)
  go : OnBaseGo live S X Q I G Mt0 R0 sp W L x z ob cs

/-- **The base dispatch** at `0x80006fc8` for a nonzero number: `s0` saved,
then base 10 (`on_dec`) or the other branch. -/
theorem on_found {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d ob : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x z o : NumObj}
    {cs : List Nat} {t : String} (fx : OnFix live S X Q I G Mt0 R0 sp W d L x z o ob cs)
    (st : OnAt S G Mt0 M R0 R sp W onSlots1) (hb : BcHeap S X M H F L)
    (hI : I (cs ++ signOut x.rep.num) t M) (hmag : x.rep.num.mag ≠ 0)
    (h18 : R 18 = BitVec.ofNat 64 x.rep.p) (h10 : R 10 = BitVec.ofNat 64 z.rep.p)
    (h20 : R 20 = BitVec.ofNat 64 zeroAddr) (h23 : R 23 = BitVec.ofNat 64 ob) (h21 : R 21 = 0#64)
    (h19 : R 19 = BitVec.ofNat 64 x.rep.val) (h22 : R 22 = BitVec.ofNat 64 x.rep.len)
    (h11 : R 11 = BitVec.ofNat 64 x.rep.scale) (h8 : R 8 = R0 8)
    (hhi : ∀ r ∈ [24, 25, 26, 27], R r = R0 r) :
    DWO live S Q t 0x80006fc8#64 R M := by
  have cx := fx.cx
  on_facts cx
  have hsf := cx.cc.frame
  have hb' := hb.frameStore (sp := sp) (o := 160) (R 8) (by simp only [heapEnd]; omega) (by omega)
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hI' := fx.cb.frameStore hI (R 8) (b := sp - 176 + 160) (by simp only [heapEnd]; omega)
  have st' := st.store 8 160 h8 (by decide) (by omega) (by omega) (by omega)
  have hr2 := st.r2
  have hobh := fx.ha.obHi
  bc_run hlive hS [h23, hr2] at 0x800070b8 0x80006fd4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · intro hne10
    have hob : ob ≠ 10 := fun e => hne10 (by rw [e]; try rfl)
    refine fx.go _ _ t H F ?_ hb' hI' ?_ ?_ ?_ ?_ ?_ ?_ hmag hob
    · exact st'.regs (ks := [15]) (by keeps_tac Keeps.refl _ _)
    all_goals first | (bsimp [h18, h10, h20, h21, h23]; done) | skip
    intro r hr
    have h15 : r ≠ 15 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega
    simp [upd_apply, h15, hhi r hr]
  · intro he10
    have hob : ob = 10 :=
      (ofNat_eq_iff (x := ob) (y := 10) (by omega) (by decide)).mp (Classical.not_not.mp he10)
    subst hob
    have hxn := hb.nums x fx.ha.mx
    have e : cs ++ Num.outChars x.rep.num 10 = cs ++ signOut x.rep.num ++ intOut x ++ fracOut x := by
      rw [out10_rep hxn.shape fx.ha.nx fx.ha.lenx (by rw [← NumRep.num_mag]; exact hmag)]
      simp only [List.append_assoc]
      rfl
    have hK := fx.hK
    rw [e] at hK
    refine on_dec hlive (H := H) (F := F) ⟨fx.cb, cx, hS, fx.ha.mx, hK⟩ ⟨?_, hb', ?_, ?_⟩ hI'
      fx.ha.lenx ?_ ?_ ?_ ?_
    · exact st'.regs (ks := [15]) (by keeps_tac Keeps.refl _ _)
    all_goals first | (bsimp [h18, h19, h22, h21, h11]; done) | skip
    intro r hr
    have h15 : r ≠ 15 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega
    simp [upd_apply, h15, hhi r hr]

/-- **All digits zero** (`0x80007088`): `s3` and `s6` restored, the tail call. -/
theorem on_none {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {pre : List Nat} {t : String}
    (cb : CharFn live S Q (R0 12) d G I) (cx : OnCtx S R0 sp W d)
    (st : OnAt S G Mt0 M R0 R sp W onSlots1) (hb : BcHeap S X M H F L) (hI : I pre t M)
    (hs : ∀ z ∈ [8, 24, 25, 26, 27], R z = R0 z)
    (hK : OnK live S X Q I G R0 Mt0 L sp W (pre ++ [48])) :
    DWO live S Q t 0x80007088#64 R M := by
  on_facts cx
  have hsf := cx.cc.frame
  have sv := st.saved
  have g19 := sv.get 19 136; have g22 := sv.get 22 112
  have hr2 := st.r2
  bc_run hlive hsf [hr2, g19, g22] at 0x80007090
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine on_zero hlive cb cx ((st.sub (slots' := onSlots0)).regs (ks := [19, 22])
    (by keeps_tac Keeps.refl _ _)) hb hI ?_ hK
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | (bsimp [g19, g22]; done) | (bsimp []; exact hs _ (by decide))

/-- **The zero scan** from `0x80006f8c` (a number other than `_zero_`):
`s6`, `s3` saved, the digits scanned, then `on_found` or `on_none`. -/
theorem on_scan {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d ob : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x z o : NumObj}
    {cs : List Nat} {t : String} (fx : OnFix live S X Q I G Mt0 R0 sp W d L x z o ob cs)
    (st : OnAt S G Mt0 M R0 R sp W onSlots0) (hb : BcHeap S X M H F L)
    (hI : I (cs ++ signOut x.rep.num) t M) (h18 : R 18 = BitVec.ofNat 64 x.rep.p)
    (h10 : R 10 = BitVec.ofNat 64 z.rep.p) (h20 : R 20 = BitVec.ofNat 64 zeroAddr)
    (h23 : R 23 = BitVec.ofNat 64 ob) (h21 : R 21 = 0#64)
    (hs : ∀ r ∈ [8, 19, 22, 24, 25, 26, 27], R r = R0 r) :
    DWO live S Q t 0x80006f8c#64 R M := by
  have cx := fx.cx
  have ha := fx.ha
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hxn := hb.nums x ha.mx
  num_facts hxn
  have hl := hxn.len; have hsc := hxn.scale; have hv := hxn.value
  have hr2 := st.r2
  have h19 := hs 19 (by simp); have h22 := hs 22 (by simp)
  have hsize := ha.size
  have hlen := ha.lenx
  have hti := toInt_ofNat_small (k := x.rep.len + x.rep.scale) (by omega)
  bc_run hlive hS [h18, hr2, hl, hsc, hv, addw_ofNat, hti, ldv_lw_miss, ldv_ld_miss] at 0x80006fb8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | bc_addr | skip
  all_goals first
    | (intro h; exfalso; exact h (by rw [show (0#64).toInt = 0 from by decide]; omega))
    | intro _
  have st2 := (st.store 22 112 h22 (by decide) (by omega) (by omega) (by omega)).store 19 136 h19
    (by decide) (by omega) (by omega) (by omega)
  have hb2 := (hb.frameStore (sp := sp) (o := 112) (R 22) (by simp only [heapEnd]; omega)
    (by omega)).frameStore (sp := sp) (o := 136) (R 19) (by simp only [heapEnd]; omega) (by omega)
  have hI1 : I (cs ++ signOut x.rep.num) t (writeLog M [(sp - 176 + 112, 8, R 22)]) :=
    fx.cb.frameStore hI (R 22) (by simp only [heapEnd]; omega)
  have hI2 : I (cs ++ signOut x.rep.num) t
      (writeLog (writeLog M [(sp - 176 + 112, 8, R 22)]) [(sp - 176 + 136, 8, R 19)]) :=
    fx.cb.frameStore hI1 (R 19) (by simp only [heapEnd]; omega)
  have hdg : ∀ i, i < x.rep.len + x.rep.scale →
      imgM (writeLog (writeLog M [(sp - 176 + 112, 8, R 22)]) [(sp - 176 + 136, 8, R 19)])
        (x.rep.val + i) = BitVec.ofNat 8 (x.rep.ds.getD i 0) := fun i hi => by
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]; exact hxn.digit i hi
  have hhi : ∀ (R' : Nat → BitVec 64) Rb, Keeps [13, 14, 15] R' Rb → Keeps [10, 11, 12, 13, 14, 15, 19,
      20, 22] Rb R → ∀ r ∈ [8, 24, 25, 26, 27], R' r = R0 r := fun R' Rb kk kb r hr => by
    have hr' : r ∉ [13, 14, 15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
    have hr'' : r ∉ [10, 11, 12, 13, 14, 15, 19, 20, 22] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
    rw [kk.get r hr', kb.get r hr'']
    exact hs r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
  refine zscan_80006fb8 hlive hS hxn.shape.dig hdg (by omega) (by omega) (by omega)
    (fun R' hex kk => ?_) (fun R' hall kk => ?_)
    (x.rep.len + x.rep.scale - 1) 0 _ (by omega) (fun j hj => absurd hj (Nat.not_lt_zero _))
    (Keeps.refl _ _) (by bsimp []) (by bsimp [])
  · have hmag : x.rep.num.mag ≠ 0 := fun h0 => by
      obtain ⟨i0, hi0, hnz⟩ := hex
      rw [NumRep.num_mag] at h0
      exact hnz ((dval_eq_zero_iff _).1 h0 i0 (by rw [hxn.shape.dsLen]; exact hi0))
    have hh := hhi R' _ kk (by keeps_tac Keeps.refl _ _)
    refine on_found hlive fx (st2.regs (ks := [10, 11, 12, 13, 14, 15, 19, 20, 22])
      ((kk.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) hb2 hI2 hmag ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hh 8 (by decide))
      fun r hr => hh r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
    all_goals rw [kk.get _ (by decide)]; bsimp [h18, h10, h20, h23, h21]
  · have hm : x.rep.num.mag = 0 := NumRep.mag_zero_of hxn.shape.dsLen hall
    have hK := fx.hK
    rw [outChars_zero hm, ← List.append_assoc] at hK
    exact on_none hlive fx.cb cx (st2.regs (ks := [10, 11, 12, 13, 14, 15, 19, 20, 22])
      ((kk.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) hb2 hI2
      (hhi R' _ kk (by keeps_tac Keeps.refl _ _)) hK

/-- **After the sign** (`0x80006f7c`): the number at `_zero_`'s address
prints `0`, any other is scanned (`on_scan`). -/
theorem on_post {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d ob : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x z o : NumObj}
    {cs : List Nat} {t : String} (fx : OnFix live S X Q I G Mt0 R0 sp W d L x z o ob cs)
    (st : OnAt S G Mt0 M R0 R sp W onSlots0) (hb : BcHeap S X M H F L)
    (hI : I (cs ++ signOut x.rep.num) t M) (h18 : R 18 = BitVec.ofNat 64 x.rep.p)
    (h23 : R 23 = BitVec.ofNat 64 ob) (h21 : R 21 = 0#64)
    (hs : ∀ r ∈ [8, 19, 22, 24, 25, 26, 27], R r = R0 r) :
    DWO live S Q t 0x80006f7c#64 R M := by
  have cx := fx.cx
  have ha := fx.ha
  on_facts cx
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hxn := hb.nums x ha.mx
  have hzn := hb.nums z ha.mz
  num_facts hxn
  num_facts hzn
  have hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p := by
    rw [st.glob (fun a hg => (fx.cb.off a hg).2.2.1) (by simp only [heapEnd]; omega) (by decide)
      (by decide)]
    exact ha.zero.glob
  simp only [zeroAddr] at hzg
  bc_run hlive hS [h18, hzg] at 0x80007090 0x80006f8c
  all_goals first
    | bc_addr
    | exact fun b hb' => cx.cc.consts b (by
        have := of_mem_accAddrs hb'
        have et : twoAddr = 0x8001cdb8 := rfl; have ez : zeroAddr = 0x8001cdc8 := rfl
        simp only [constBytes]; omega)
    | skip
  · intro heq
    have hp : x.rep.p = z.rep.p := (ofNat_eq_iff (by omega) (by omega)).mp heq
    have hm := NumAt.mag_zero_at hxn hzn hp ha.zero.len ha.zero.scale ha.zero.ds
    have hK := fx.hK
    rw [outChars_zero hm, ← List.append_assoc] at hK
    exact on_zero hlive fx.cb cx (st.regs (ks := [10, 20]) (by keeps_tac Keeps.refl _ _)) hb hI
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (bsimp []; exact hs _ (by decide)))
      hK
  · intro _
    exact on_scan hlive fx (st.regs (ks := [10, 20]) (by keeps_tac Keeps.refl _ _)) hb hI
      (by bsimp [h18]) (by bsimp []) (by bsimp []) (by bsimp [h23]) (by bsimp [h21])
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (bsimp []; exact hs _ (by decide))

/-! ## The prologue and the sign (`0x80006f3c`) -/

theorem word_sub176 {x : Nat} (h : 176 ≤ x) :
    BitVec.ofNat 64 x + 18446744073709551440#64 = BitVec.ofNat 64 (x - 176) := by
  change BitVec.ofNat 64 x + -(176#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le x 176 (by decide) h

/-- The prologue's six saves. -/
abbrev onPro (M : Mem) (sp : Nat) (R : Nat → BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M
    [(sp - 176 + 152, 8, R 9)]) [(sp - 176 + 144, 8, R 18)]) [(sp - 176 + 120, 8, R 21)])
    [(sp - 176 + 104, 8, R 23)]) [(sp - 176 + 168, 8, R 1)]) [(sp - 176 + 128, 8, R 20)]

/-- The state after the prologue. -/
theorem OnAt.pro {S G : Nat → Prop} {Mt0 : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    (h2 : R 2 = BitVec.ofNat 64 (sp - 176)) (hk : Keeps onAll R R0) (h9 : R 9 = R0 12)
    (hsp : 176 ≤ sp) (hW : 176 ≤ W) : OnAt S G Mt0 (onPro Mt0 sp R0) R0 R sp W onSlots0 :=
  let s0 : OnAt S G Mt0 Mt0 R0 R sp W [] :=
    ⟨h2, fun _ h => absurd h List.not_mem_nil, hk, h9, fun _ _ _ _ => rfl⟩
  ((((((s0.store 9 152 rfl (by decide) (by omega) hsp hW).store 18 144 rfl (by decide) (by omega) hsp
    hW).store 21 120 rfl (by decide) (by omega) hsp hW).store 23 104 rfl (by decide) (by omega) hsp
    hW).store 1 168 rfl (by decide) (by omega) hsp hW).store 20 128 rfl (by decide) (by omega) hsp
    hW).sub

/-- The minus sign of a negative `num` (`li a0,45; jalr a2`), then the
zero test. -/
theorem on_neg {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d ob : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x z o : NumObj}
    {cs : List Nat} {t : String} (fx : OnFix live S X Q I G Mt0 R0 sp W d L x z o ob cs)
    (st : OnAt S G Mt0 M R0 R sp W onSlots0) (hb : BcHeap S X M H F L) (hI : I cs t M)
    (hneg : x.rep.neg = true) (h12 : R 12 = R0 12) (h18 : R 18 = BitVec.ofNat 64 x.rep.p)
    (h23 : R 23 = BitVec.ofNat 64 ob) (h21 : R 21 = 0#64)
    (hs : ∀ r ∈ [8, 19, 22, 24, 25, 26, 27], R r = R0 r) :
    DWO live S Q t 0x80006f74#64 R M := by
  have cx := fx.cx
  on_facts cx
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  bc_run hlive hS [h12] at 0x80006f7c
  · rw [jalr_tgt _ cx.fal]; exact cx.fal
  rw [jalr_tgt _ cx.fal]
  refine on_call (c := 45) (Mt0 := Mt0) (slots := onSlots0) (R := upd (upd R 10 45#64) 1 2147512188#64) fx.cb cx ?_ (by decide) (by decide) hb hI (by bsimp []) (by decide)
    (by bsimp []) fun R' M' t' hk' hI2 st' hb2 _ => ?_
  · exact st.regs (ks := [1, 10]) (by keeps_tac Keeps.refl _ _)
  bsimp []
  refine on_post hlive fx st' hb2 (by simpa only [signOut, NumRep.num_neg, hneg, if_true] using hI2)
    (by rw [hk'.get 18 (by decide)]; bsimp [h18]) (by rw [hk'.get 23 (by decide)]; bsimp [h23])
    (by rw [hk'.get 21 (by decide)]; bsimp [h21]) fun r hr => ?_
  rw [hk'.get r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)]
  have h1 : r ≠ 1 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega
  have h10 : r ≠ 10 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega
  simp only [upd_apply, h1, h10, if_false, hs r hr]

/-- **`bc_out_num (num, o_base, out_char, 0)`** from its entry, given the
branch for a base other than 10 (`OnFix.go`). -/
theorem on_entry {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x z o : NumObj}
    {cs : List Nat} {t : String} (fx : OnFix live S X Q I G Mt0 R0 sp W d L x z o ob cs)
    (hb : BcHeap S X Mt0 H F L) (hI : I cs t Mt0) (h10 : R0 10 = BitVec.ofNat 64 x.rep.p)
    (h11 : R0 11 = BitVec.ofNat 64 ob) :
    DWO live S Q t 0x80006f3c#64 R0 Mt0 := by
  have cx := fx.cx
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hxn := hb.nums x fx.ha.mx
  num_facts hxn
  have hxs := hxn.sign
  have hlz := cx.lz
  have hmo : MemOnly (fun a => sp - 176 ≤ a ∧ a < sp) (onPro Mt0 sp R0) Mt0 := fun a ha => by
    repeat rw [imgM_store_miss _ _ (by omega)]
  have hb' := hb.out_frame hmo fun a ha => outHeap_of_ge (by simp only [heapEnd]; omega)
  have hI' : I cs t (onPro Mt0 sp R0) := fx.cb.stab cs t Mt0 _ hI fun a hg => hmo a fun h => by
    have := (fx.cb.off a hg).1; simp only [heapStart] at this; omega
  cases hxg : x.rep.neg
  · rw [hxg] at hxs
    bc_run hlive hS [h10, h11, cx.sp0, word_sub176 (show 176 ≤ sp by omega), hxs, signWord_false,
      hlz] at 0x80006f7c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine on_post hlive fx (OnAt.pro (by bsimp []) (by keeps_tac Keeps.refl _ _) (by bsimp [])
      (by omega) (by omega)) hb' (by simpa only [signOut, NumRep.num_neg, hxg, Bool.false_eq_true, if_false,
        List.append_nil] using hI')
      (by bsimp [h10]) (by bsimp [h11]) (by bsimp [hlz]) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bsimp []
  · rw [hxg] at hxs
    bc_run hlive hS [h10, h11, cx.sp0, word_sub176 (show 176 ≤ sp by omega), hxs, signWord_true,
      hlz] at 0x80006f7c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine on_neg hlive fx (OnAt.pro (by bsimp []) (by keeps_tac Keeps.refl _ _) (by bsimp [])
      (by omega) (by omega)) hb' hI' hxg (by bsimp []) (by bsimp [h10]) (by bsimp [h11])
      (by bsimp [hlz]) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bsimp []

end Dc.Mach
