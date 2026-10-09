import Dc.Mach.Bc.OutNumBase

/-!
# `bc_out_num` in base 10 (`0x80006fd4`)

    0x80006fd4  n_len > 1, or the first digit nonzero: print the integer digits
                (`s0` from `n_value` to `n_value + n_len`, the end as `addw`)
    0x80007048  n_scale > 0: '.', then the fraction digits from `s6`
    0x80007434  the epilogue

`dc` passes `leading_zero = 0`, so a lone integer digit `0` prints nothing.

- `OnDec`: the state of the branch (the frame, the heap as at entry, `s2`
  the number, `s8`–`s11` the caller's).
- `on_frac`, `on_dot`, `on_int`, `on_dec`: the fraction loop, the point, the
  integer loop and the branch.
- `out10_rep`: the characters `Num.outChars` gives a represented number.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- The base-10 branch's state: the frame with `s0`–`s7` saved, the heap as
at entry, the number in `s2`, `s8`–`s11` the caller's. -/
structure OnDec (S : Nat → Prop) (X : Raws) (G : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (x : NumObj) : Prop where
  st : OnAt S G Mt0 M R0 R sp W onSlots2
  heap : BcHeap S X M H F L
  num : R 18 = BitVec.ofNat 64 x.rep.p
  hi : ∀ z ∈ [24, 25, 26, 27], R z = R0 z

/-- Through a change of registers outside the saved ones, `s1`, `s2` and
`s8`–`s11`. -/
theorem OnDec.regs {S G : Nat → Prop} {X : Raws} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x : NumObj}
    (h : OnDec S X G Mt0 M R0 R sp W H F L x) {ks : List Nat} (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ onAll ∧ z ≠ 2 ∧ z ≠ 9 ∧ z ≠ 18 ∧ z < 24 := by decide) :
    OnDec S X G Mt0 M R0 R' sp W H F L x where
  st := h.st.regs hk fun z hz => ⟨(hks z hz).1, (hks z hz).2.1, (hks z hz).2.2.1⟩
  heap := h.heap
  num := by rw [hk.get 18 fun hm => (hks 18 hm).2.2.2.1 rfl]; exact h.num
  hi := fun z hz => by
    have : z ∉ ks := fun hm => by
      have := (hks z hm).2.2.2.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; omega
    rw [hk.get z this]; exact h.hi z hz

/-- **The callback in the branch**: the state survives, the characters grow. -/
theorem OnDec.call {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {G : Nat → Prop} {I : List Nat → String → Mem → Prop} {Mt0 M : Mem}
    {R0 R : Nat → BitVec 64} {sp W d c : Nat} {H : Heap} {F : List Blk} {L : List NumObj}
    {x : NumObj} {cs : List Nat} {t : String}
    (cb : CharFn live S Q (R0 12) d G I) (cx : OnCtx S R0 sp W d)
    (h : OnDec S X G Mt0 M R0 R sp W H F L x) (hI : I cs t M) (h10 : R 10 = BitVec.ofNat 64 c)
    (hc : c < 256) (h1 : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' t', Keeps cClob R' R → I (cs ++ [c]) t' M' → OnDec S X G Mt0 M' R0 R' sp W H F L x →
      DWO live S Q t' (R 1) R' M') :
    DWO live S Q t (R0 12) R M :=
  on_call cb cx h.st (by decide) (by decide) h.heap hI h10 hc h1 fun R' M' t' hk' hI' st' hb' _ =>
    hk R' M' t' hk' hI' ⟨st', hb', by rw [hk'.get 18 (by decide)]; exact h.num, fun z hz => by
      have hc : z ∉ cClob := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> decide
      rw [hk'.get z hc]; exact h.hi z hz⟩

/-- The fixed facts of the branch: the callback, the frame, the heap owned,
the number `x` of `L` and the continuation for the characters `target`. -/
structure OnDecFix (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W d : Nat) (L : List NumObj) (x : NumObj) (target : List Nat) : Prop where
  cb : CharFn live S Q (R0 12) d G I
  cx : OnCtx S R0 sp W d
  hS : HeapOwn S
  mx : x ∈ L
  hK : OnK live S X Q I G R0 Mt0 L sp W target

/-- **The end of the branch**: the epilogue and the caller's continuation. -/
theorem on_decEnd {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x : NumObj} {target : List Nat}
    {t : String} (fx : OnDecFix live S X Q I G Mt0 R0 sp W d L x target)
    (h : OnDec S X G Mt0 M R0 R sp W H F L x) (hI : I target t M) :
    DWO live S Q t 0x80007434#64 R M :=
  on_epi hlive fx.cx h.st.saved h.st.r2 h.st.keep h.hi fun R' hk =>
    fx.hK.ret R' M t H F hk hI h.heap h.st.out

/-- The fraction digits of `x`, after its `n_len` integer digits. -/
abbrev fracDs (x : NumObj) : List Nat := x.rep.ds.drop x.rep.len

/-- The `i`-th fraction digit. -/
theorem fracDs_getD (x : NumObj) (i : Nat) : (fracDs x).getD i 0 = x.rep.ds.getD (x.rep.len + i) 0 := by
  simp only [fracDs, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem take_succ_map {l : List Nat} {i : Nat} (hi : i < l.length) (f : Nat → Nat) :
    (l.take (i + 1)).map f = (l.take i).map f ++ [f (l.getD i 0)] := by
  rw [take_succ_getD hi, List.map_append]; rfl

/-! ## The fraction loop (`0x80007060`) -/

theorem on_frac {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x : NumObj} {pre : List Nat}
    (fx : OnDecFix live S X Q I G Mt0 R0 sp W d L x (pre ++ (fracDs x).map Num.decChar)) :
    ∀ k i (R : Nat → BitVec 64) (M : Mem) (t : String), x.rep.scale - i = k → i < x.rep.scale →
      OnDec S X G Mt0 M R0 R sp W H F L x → I (pre ++ ((fracDs x).take i).map Num.decChar) t M →
      R 8 = BitVec.ofNat 64 i → R 22 = BitVec.ofNat 64 (x.rep.val + x.rep.len) →
      DWO live S Q t 0x80007060#64 R M := by
  have cx := fx.cx
  on_facts cx
  have hsf := cx.cc.frame
  intro k
  induction k with
  | zero => intro i R M t hk' hi; omega
  | succ k ih =>
    intro i R M t hk' hi h hI h8 h22
    have hxn := h.heap.nums x fx.mx
    num_facts hxn
    have hdig := hxn.shape.dig
    have hl := lbu_digit (IsDigits.getD hdig (x.rep.len + i)) (hxn.digit (x.rep.len + i) (by omega))
    have hr9 := h.st.cb; have hr2 := h.st.r2
    have hfl : (fracDs x).length = x.rep.scale := by simp only [fracDs, List.length_drop]; omega
    have hd := IsDigits.getD hdig (x.rep.len + i)
    have hz := zext8_ofNat (c := x.rep.ds.getD (x.rep.len + i) 0) (by omega)
    bc_run hlive fx.hS [h8, h22, hr9, hr2, hl, Nat.add_assoc]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    · rw [jalr_tgt _ cx.fal]; exact cx.fal
    rw [jalr_tgt _ cx.fal]
    refine OnDec.call (c := Num.decChar (x.rep.ds.getD (x.rep.len + i) 0)) fx.cb cx
      (h.regs (ks := [1, 10, 8, 15]) (by keeps_tac Keeps.refl _ _)) hI
      (by bsimp [Num.decChar]; congr 1; omega) (by simp only [Num.decChar]; omega) (by bsimp [])
      fun R' M' t' hk1 hI' h' => ?_
    bsimp []
    have hxn' := h'.heap.nums x fx.mx
    have hsc := hxn'.scale
    have r8 : R' 8 = BitVec.ofNat 64 (i + 1) := by rw [hk1.get 8 (by decide)]; bsimp []
    have r22 : R' 22 = BitVec.ofNat 64 (x.rep.val + x.rep.len) := by
      rw [hk1.get 22 (by decide)]; bsimp [h22]
    have r18 := h'.num
    have hti1 := toInt_ofNat_small (k := i + 1) (by omega)
    have hti2 := toInt_ofNat_small (k := x.rep.scale) (by omega)
    have hI2 : I (pre ++ ((fracDs x).take (i + 1)).map Num.decChar) t' M' := by
      rw [take_succ_map (by omega), fracDs_getD, ← List.append_assoc]; exact hI'
    bc_run hlive fx.hS [r8, r18, hsc, hti1, hti2, sxw_ofNat] at 0x80007060 0x80007434
    all_goals first | exact acc_heap fx.hS (by omega) (by omega) | skip
    · intro hlt
      exact ih (i + 1) _ M' t' (by omega) (by omega) (h'.regs (ks := [15, 14]) (by keeps_tac Keeps.refl _ _))
        hI2 (by bsimp [r8]) (by bsimp [r22])
    · intro hge
      have hL : i + 1 = x.rep.scale := by omega
      rw [hL, ← hfl, List.take_of_length_le (Nat.le_refl _)] at hI2
      bc_run hlive fx.hS [] at 0x80007434
      exact on_decEnd hlive fx (h'.regs (ks := [15, 14]) (by keeps_tac Keeps.refl _ _)) hI2

/-! ## The point (`0x80007048`) -/

theorem on_dot {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x : NumObj} {pre : List Nat}
    {t : String}
    (fx : OnDecFix live S X Q I G Mt0 R0 sp W d L x
      (pre ++ if x.rep.scale = 0 then [] else 46 :: (fracDs x).map Num.decChar))
    (h : OnDec S X G Mt0 M R0 R sp W H F L x) (hI : I pre t M)
    (h11 : R 11 = BitVec.ofNat 64 x.rep.scale)
    (h22 : R 22 = BitVec.ofNat 64 (x.rep.val + x.rep.len)) :
    DWO live S Q t 0x80007048#64 R M := by
  have cx := fx.cx
  on_facts cx
  have hsf := cx.cc.frame
  have hxn := h.heap.nums x fx.mx
  num_facts hxn
  have hti := toInt_ofNat_small (k := x.rep.scale) (by omega)
  have hr9 := h.st.cb
  bc_run hlive fx.hS [h11, hti, hr9] at 0x80007434
  · intro hle
    have h0 : x.rep.scale = 0 := by simp at hle; omega
    simp only [h0, if_true, List.append_nil] at fx
    exact on_decEnd hlive fx h hI
  · intro hpos
    have hp : 0 < x.rep.scale := by simp at hpos; omega
    have hne : x.rep.scale ≠ 0 := by omega
    simp only [hne, if_false] at fx
    bc_run hlive fx.hS [h11, hti, hr9]
    · rw [jalr_tgt _ cx.fal]; exact cx.fal
    rw [jalr_tgt _ cx.fal]
    refine OnDec.call (c := 46) fx.cb cx (h.regs (ks := [1, 10]) (by keeps_tac Keeps.refl _ _)) hI
      (by bsimp []) (by decide) (by bsimp []) fun R' M' t' hk1 hI' h' => ?_
    bsimp []
    have hxn' := h'.heap.nums x fx.mx
    have hsc := hxn'.scale
    have r18 := h'.num
    have r22 : R' 22 = BitVec.ofNat 64 (x.rep.val + x.rep.len) := by
      rw [hk1.get 22 (by decide)]; bsimp [h22]
    bc_run hlive fx.hS [r18, hsc, hti] at 0x80007060
    all_goals first | exact acc_heap fx.hS (by omega) (by omega) | skip
    · intro hc; simp at hc; omega
    intro _
    bc_run hlive fx.hS [] at 0x80007060
    have fx' : OnDecFix live S X Q I G Mt0 R0 sp W d L x ((pre ++ [46]) ++ (fracDs x).map Num.decChar) :=
      { fx with hK := by simpa only [List.append_assoc, List.singleton_append] using fx.hK }
    refine on_frac hlive (H := H) (F := F) fx' _ 0 _ M' t' rfl hp ?_
      (by rw [List.take_zero, List.map_nil, List.append_nil]; exact hI') ?_ ?_
    · exact h'.regs (ks := [15, 8]) (by keeps_tac Keeps.refl _ _)
    · bsimp []
    · bsimp [r22]

/-! ## The integer loop (`0x80006fe4`) -/

/-- The integer digits of `x`. -/
abbrev intDs (x : NumObj) : List Nat := x.rep.ds.take x.rep.len

/-- The rest of the branch after the integer digits. -/
abbrev fracOut (x : NumObj) : List Nat :=
  if x.rep.scale = 0 then [] else 46 :: (fracDs x).map Num.decChar

/-- `addw` of a heap address and a count, less the address advanced by `j`. -/
theorem subw_end {v n j : Nat} (hv : v + n < 2 ^ 32) (hj : j ≤ n) (hn : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (BitVec.ofNat 64 v) + BitVec.extractLsb 31 0 (BitVec.ofNat 64 n))) -
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 (v + j))) = BitVec.ofNat 64 (n - j) := by
  rw [exw_ofNat (by omega), exw_ofNat (by omega), exw_ofNat (by omega), ext_sext32]
  rw [← sext32_ofNat (show n - j < 2 ^ 31 by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem on_int {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x : NumObj} {pre : List Nat}
    (fx : OnDecFix live S X Q I G Mt0 R0 sp W d L x (pre ++ (intDs x).map Num.decChar ++ fracOut x)) :
    ∀ k i (R : Nat → BitVec 64) (M : Mem) (t : String), x.rep.len - i = k → i < x.rep.len →
      OnDec S X G Mt0 M R0 R sp W H F L x → I (pre ++ ((intDs x).take i).map Num.decChar) t M →
      R 8 = BitVec.ofNat 64 (x.rep.val + i) →
      R 23 = BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 x.rep.val) +
        BitVec.extractLsb 31 0 (BitVec.ofNat 64 x.rep.len)) →
      R 22 = BitVec.ofNat 64 x.rep.len → R 19 = BitVec.ofNat 64 x.rep.val → R 21 = 0#64 →
      DWO live S Q t 0x80006fe4#64 R M := by
  have cx := fx.cx
  on_facts cx
  have hsf := cx.cc.frame
  intro k
  induction k with
  | zero => intro i R M t hk' hi; omega
  | succ k ih =>
    intro i R M t hk' hi h hI h8 h23 h22 h19 h21
    have hxn := h.heap.nums x fx.mx
    num_facts hxn
    have hdig := hxn.shape.dig
    have hd := IsDigits.getD hdig i
    have hl := lbu_digit hd (hxn.digit i (by omega))
    have hr9 := h.st.cb; have hr2 := h.st.r2
    have hil : (intDs x).length = x.rep.len := by simp only [intDs, List.length_take]; omega
    bc_run hlive fx.hS [h8, hr9, hr2, hl]
    all_goals first | exact acc_heap fx.hS (by omega) (by omega) | skip
    · rw [jalr_tgt _ cx.fal]; exact cx.fal
    rw [jalr_tgt _ cx.fal]
    refine OnDec.call (c := Num.decChar (x.rep.ds.getD i 0)) fx.cb cx
      (h.regs (ks := [1, 10, 8]) (by keeps_tac Keeps.refl _ _)) hI
      (by bsimp [Num.decChar]; congr 1; omega) (by simp only [Num.decChar]; omega) (by bsimp [])
      fun R' M' t' hk1 hI' h' => ?_
    bsimp []
    have r8 : R' 8 = BitVec.ofNat 64 (x.rep.val + (i + 1)) := by
      rw [hk1.get 8 (by decide)]; bsimp []; congr 1
    have r23 : R' 23 = BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 x.rep.val) +
        BitVec.extractLsb 31 0 (BitVec.ofNat 64 x.rep.len)) := by
      rw [hk1.get 23 (by decide)]; bsimp [h23]
    have r22 : R' 22 = BitVec.ofNat 64 x.rep.len := by rw [hk1.get 22 (by decide)]; bsimp [h22]
    have r19 : R' 19 = BitVec.ofNat 64 x.rep.val := by rw [hk1.get 19 (by decide)]; bsimp [h19]
    have r21 : R' 21 = 0#64 := by rw [hk1.get 21 (by decide)]; bsimp [h21]
    have hsw := subw_end (v := x.rep.val) (n := x.rep.len) (j := i + 1) (by omega) (by omega)
      (by omega)
    have hI2 : I (pre ++ ((intDs x).take (i + 1)).map Num.decChar) t' M' := by
      rw [take_succ_map (by omega), ← List.append_assoc]
      simp only [intDs, List.getD_eq_getElem?_getD, List.getElem?_take, show i < x.rep.len from hi,
        if_true] at hI' ⊢
      exact hI'
    have hti := toInt_ofNat_small (k := x.rep.len - (i + 1)) (by omega)
    bc_run hlive fx.hS [r8, r23, hsw, hti] at 0x80006fe4
    · intro hpos
      exact ih (i + 1) _ M' t' (by omega) (by simp at hpos; omega)
        (h'.regs (ks := [15]) (by keeps_tac Keeps.refl _ _)) hI2 r8 r23 r22 r19 r21
    · intro hle
      have hL : i + 1 = x.rep.len := by simp at hle; omega
      rw [hL, ← hil, List.take_of_length_le (Nat.le_refl _)] at hI2
      have hsh := shl_shr32 (n := x.rep.len - 1) (by omega)
      have hxn' := h'.heap.nums x fx.mx
      have hsc := hxn'.scale
      have r18 := h'.num
      bc_run hlive fx.hS [r22, r19, r21, r18, hsc, hsh, word_pred (show 1 ≤ x.rep.len by omega)]
        at 0x80007048
      all_goals first | exact acc_heap fx.hS (by omega) (by omega) | skip
      bc_run hlive fx.hS [r18, hsc] at 0x80007048
      all_goals first | exact acc_heap fx.hS (by omega) (by omega) | skip
      refine on_dot hlive (H := H) (F := F) (pre := pre ++ (intDs x).map Num.decChar) fx ?_ hI2 ?_ ?_
      · exact h'.regs (ks := [8, 10, 11, 13, 14, 15, 19, 22]) (by keeps_tac Keeps.refl _ _)
      · bsimp []
      · bsimp []
        congr 1; omega

/-! ## The branch (`0x80006fd4`) -/

/-- The integer digits the branch prints: none for a lone `0`. -/
abbrev intOut (x : NumObj) : List Nat :=
  if 1 < x.rep.len ∨ x.rep.ds.getD 0 0 ≠ 0 then (intDs x).map Num.decChar else []

theorem on_dec {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x : NumObj} {pre : List Nat}
    {t : String} (fx : OnDecFix live S X Q I G Mt0 R0 sp W d L x (pre ++ intOut x ++ fracOut x))
    (h : OnDec S X G Mt0 M R0 R sp W H F L x) (hI : I pre t M) (hlen : 1 ≤ x.rep.len)
    (h19 : R 19 = BitVec.ofNat 64 x.rep.val) (h22 : R 22 = BitVec.ofNat 64 x.rep.len)
    (h21 : R 21 = 0#64) (h11 : R 11 = BitVec.ofNat 64 x.rep.scale) :
    DWO live S Q t 0x80006fd4#64 R M := by
  have cx := fx.cx
  on_facts cx
  have hxn := h.heap.nums x fx.mx
  num_facts hxn
  have hdig := hxn.shape.dig
  have hti := toInt_ofNat_small (k := x.rep.len) (by omega)
  have hint : ∀ R', OnDec S X G Mt0 M R0 R' sp W H F L x → R' 8 = BitVec.ofNat 64 x.rep.val →
      R' 22 = BitVec.ofNat 64 x.rep.len → R' 19 = BitVec.ofNat 64 x.rep.val → R' 21 = 0#64 →
      (1 < x.rep.len ∨ x.rep.ds.getD 0 0 ≠ 0) → DWO live S Q t 0x80006fe0#64 R' M := by
    intro R' h' r8 r22 r19 r21 hc
    have fx' : OnDecFix live S X Q I G Mt0 R0 sp W d L x (pre ++ (intDs x).map Num.decChar ++ fracOut x) :=
      { fx with hK := by simpa only [intOut, hc, if_true] using fx.hK }
    bc_run hlive fx.hS [r22, r19] at 0x80006fe4
    refine on_int hlive (H := H) (F := F) fx' _ 0 _ M t rfl (by omega) ?_
      (by rw [List.take_zero, List.map_nil, List.append_nil]; exact hI) ?_ ?_ ?_ ?_ ?_
    · exact h'.regs (ks := [23]) (by keeps_tac Keeps.refl _ _)
    all_goals bsimp [r8, r22, r19, r21]
  bc_run hlive fx.hS [h19, h22, h21, hti] at 0x80006fe4
  · intro hle
    have h1 : x.rep.len = 1 := by simp at hle; omega
    have hd0 := IsDigits.getD hdig 0
    have hl0 := lbu_digit hd0 (by have := hxn.digit 0 (by omega); rwa [Nat.add_zero] at this)
    bc_run hlive fx.hS [h19, h22, h21, hl0, h1] at 0x80006fe4 0x80007048
    all_goals first | exact acc_heap fx.hS (by omega) (by omega) | skip
    · intro hz
      have h0 : x.rep.ds.getD 0 0 = 0 := (ofNat_eq_zero_iff (by omega)).mp hz
      bc_run hlive fx.hS [h19, h22, h21, hl0, h1] at 0x80006fe4 0x80007048
      bc_run hlive fx.hS [h19, h22, h21, hl0, h1] at 0x80006fe4 0x80007048
      have hio : intOut x = [] := by
        unfold intOut; rw [if_neg]; rintro (h | h); omega; exact h h0
      rw [hio, List.append_nil] at fx
      refine on_dot hlive (H := H) (F := F) (pre := pre) fx ?_ hI ?_ ?_
      · exact h.regs (ks := [8, 10, 11, 13, 14, 15, 19, 22]) (by keeps_tac Keeps.refl _ _)
      · bsimp [h11]
      · bsimp [h1]
    · intro hz
      have h0 : x.rep.ds.getD 0 0 ≠ 0 := fun e => hz ((ofNat_eq_zero_iff (by omega)).mpr e)
      bc_run hlive fx.hS [h19, h22, h21, hl0, h1] at 0x80006fe4
      refine hint _ ?_ ?_ ?_ ?_ ?_ (.inr h0)
      · exact h.regs (ks := [8, 10, 11, 13, 14, 15, 19, 22, 23]) (by keeps_tac Keeps.refl _ _)
      all_goals bsimp [h1, h21, h19, h22]
  · intro hgt
    have h1 : 1 < x.rep.len := by simp at hgt; omega
    refine hint _ ?_ ?_ ?_ ?_ ?_ (.inl h1)
    · exact h.regs (ks := [8, 10, 11, 13, 14, 15, 19, 22, 23]) (by keeps_tac Keeps.refl _ _)
    all_goals bsimp [h21, h19, h22]

/-! ## The model -/

/-- **The base-10 characters of a represented number**: the sign, the
integer digits (none for a lone `0`), then `.` and the fraction digits. -/
theorem out10_rep {o : NumRep} (hs : NumShape o) (hn : o.Norm) (hl : 1 ≤ o.len)
    (hnz : dval o.ds ≠ 0) :
    Num.outChars o.num 10 = (if o.neg then [45] else []) ++
      ((if 1 < o.len ∨ o.ds.getD 0 0 ≠ 0 then (o.ds.take o.len).map Num.decChar else []) ++
      (if o.scale = 0 then [] else 46 :: (o.ds.drop o.len).map Num.decChar)) := by
  have hsplit : o.ds = o.ds.take o.len ++ o.ds.drop o.len := (List.take_append_drop _ _).symm
  have hdl := hs.dsLen
  have hfl : (o.ds.drop o.len).length = o.scale := by simp only [List.length_drop]; omega
  have hil : (o.ds.take o.len).length = o.len := by simp only [List.length_take]; omega
  have hdig := hs.dig
  have hhead : (o.ds.take o.len).head? = some (o.ds.getD 0 0) := by
    obtain ⟨n, hn'⟩ : ∃ n, o.len = n + 1 := ⟨o.len - 1, by omega⟩
    rw [hn']
    cases hds : o.ds with
    | nil => rw [hds] at hdl; simp at hdl; omega
    | cons a r => simp
  have e : o.num = ⟨o.neg, dvalBE (o.ds.take o.len ++ o.ds.drop o.len), (o.ds.drop o.len).length⟩ := by
    rw [NumRep.num_eq, ← hsplit, hfl]
  rw [e, out10_chars _ _ _ (fun d h => hdig d (List.mem_of_mem_take h))
    (fun d h => hdig d (List.mem_of_mem_drop h)) (by omega) ?_ (by rw [← hsplit]; exact hnz)]
  · simp only [out10, hil, hfl, hhead, ne_eq, Option.some.injEq, List.append_assoc]
  · intro h1 dd hd
    rw [hhead, Option.mem_def, Option.some.injEq] at hd
    subst hd
    rcases hn with hn | hn
    · omega
    · exact hn

end Dc.Mach
