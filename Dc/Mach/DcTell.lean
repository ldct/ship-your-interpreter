import Dc.Mach.DcRotate
import Dc.Mach.DcBinop

/-!
# `dc_tell_stackdepth` (M9)

    dc_tell_stackdepth ():
      for (n = 0, t = dc_stack; t; t = t->link) ++n;
      return n;

The count walks the stack chain (`h.view.stk.toP`); every node is a block of
the state, so the depth is at most `DcAt.blocks_len` and the 32-bit `addiw`
counts exactly.

- `tsd_walk`: the loop at `0x800037f0`.
- `dc_tell_stackdepth_spec`: `a0` the model's stack length.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `dc_tell_stackdepth`'s loop (`0x800037f0`, `a5` the node `b`, `a0` the
nodes counted before it). -/
theorem tsd_walk {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {P : Blk → GV → Prop} :
    ∀ {b : Blk} {x : GV} {l : List (Blk × GV)} {k : Nat},
    PChain M 24 P (BitVec.ofNat 64 b.pay) ((b, x) :: l) →
    (∀ bx ∈ (b, x) :: l, heapStart + 16 ≤ bx.1.pay ∧ bx.1.pay + 32 ≤ heapEnd ∧ bx.1.pay % 16 = 0) →
    k + 1 + l.length < 2 ^ 31 →
    ∀ {ra : BitVec 64} (R : Nat → BitVec 64), ra.toNat % 4 = 0 → R 1 = ra → R 15 = BitVec.ofNat 64 b.pay →
    R 10 = BitVec.ofNat 64 k →
    (∀ R', Keeps [10, 15] R' R → R' 10 = BitVec.ofNat 64 (k + 1 + l.length) →
      DW live S Q ra R' M) →
    DW live S Q 0x800037f0#64 R M := by
  intro b x l
  induction l generalizing b x with
  | nil => ?_
  | cons y l ih => ?_
  all_goals
    intro k hc hb hlen ra R hal h1 h15 h10 hk
    have htx : tohostAddr = 0x8001ad00 := rfl
    obtain ⟨hb1, hb2, hb3⟩ := hb (b, x) List.mem_cons_self
    simp only [heapStart, heapEnd] at hb1 hb2
    obtain ⟨-, hl⟩ := hc.uncons
    have wk : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (k + 1))) =
        BitVec.ofNat 64 (k + 1) := sxw_ofNat (by simp only [List.length_cons, List.length_nil] at hlen; omega)
  -- the last node: the link is null
  · have hz := hl.nil_eq
    bc_run hlive hS [h1, h15, h10, hz, word_succ, wk]
    all_goals try (intro hc; exact (hc rfl).elim)
    try intro _
    try bc_run hlive hS [h1, h15, h10, hz, word_succ, wk]
    all_goals first | exact hal | skip
    exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp [h10, word_succ, wk]; rfl)
  -- a next node: around the loop
  · obtain ⟨b', x'⟩ := y
    have he := hl.head_eq
    obtain ⟨hb1', hb2', -⟩ := hb (b', x') (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [heapStart, heapEnd] at hb1' hb2'
    have hnz : BitVec.ofNat 64 b'.pay ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    bc_run hlive hS [h15, h10, he, word_succ, wk] at 0x800037f8
    bc_run hlive hS [h15, h10, he, word_succ, wk]
    all_goals try (intro hc; exact (hc hnz).elim)
    try intro _
    refine ih (k := k + 1) (by rw [← he]; exact hl) (fun bx hm => hb bx (List.mem_cons_of_mem _ hm))
      (by simp only [List.length_cons] at hlen ⊢; omega) _ hal (by bsimp [h1]) (by bsimp [he])
      (by bsimp [word_succ, wk]) fun R' hk' e10 => ?_
    exact hk R' (hk'.trans (by keeps_tac Keeps.refl _ _))
      (by rw [e10]; simp only [List.length_cons]; congr 1; omega)

/-- The stack is at most as long as the state has blocks. -/
theorem DcAt.stk_len {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) :
    G.stk.length ≤ 7856803 := by
  have := h.blocks_len
  simp only [DcG.blocks, List.length_append, List.length_map] at this
  omega

/-- **`dc_tell_stackdepth ()`** at `0x800037e0`: `a0` the model's stack
length, memory unchanged. -/
theorem dc_tell_stackdepth_spec {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 15] R' R → R' 10 = BitVec.ofNat 64 st.stack.length →
      DWO live S Q t (R 1) R' M) :
    DWO live S Q t 0x800037e0#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hG := h.glob
  have hch := h.view.stk.toP
  have hle : G.stk.length = st.stack.length := h.den.stk.length_eq
  have hbl := h.stk_len
  have geo := h.stkGeo
  rcases hst : G.stk with _ | ⟨⟨b, g⟩, rest⟩
  · rw [hst] at hch
    have hz := hch.nil_eq
    rw [hst] at hle
    bc_run hlive hS []
    all_goals first | (intro hc; exact absurd hz hc) | skip
    intro _
    try bc_run hlive hS []
    all_goals first | exact hal | skip
    exact hk _ (by keeps_tac Keeps.refl _ _) (by rw [← hle]; bsimp []; rfl)
  · rw [hst] at hch hle hbl
    have hgb := geo.bnd
    rw [hst] at hgb
    have he := hch.head_eq
    obtain ⟨hb1, hb2, -⟩ := hgb (b, g) List.mem_cons_self
    simp only [heapStart, heapEnd] at hb1 hb2
    have hnz : BitVec.ofNat 64 b.pay ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    bc_run hlive hS []
    all_goals first | (intro hc; exact absurd (he.symm.trans hc) hnz) | skip
    try intro _
    rw [he]
    refine tsd_walk hlive hS (k := 0) (by rw [← he]; exact hch) hgb
      (by simp only [List.length_cons] at hbl; omega) _ hal (by bsimp []) (by bsimp []) (by bsimp [])
      fun R' hk' e10 => ?_
    exact hk R' (hk'.trans (by keeps_tac Keeps.refl _ _))
      (by rw [e10, ← hle]; simp only [List.length_cons]; congr 1; omega)

/-! ## `dc_numlen` -/

theorem digitsIn_len : ∀ (m fuel n : Nat), 10 ^ m ≤ n → n < 10 ^ (m + 1) → m < fuel →
    (Dc.Num.digitsIn 10 fuel n).length = m + 1
  | _, 0, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | 0, fuel + 1, n, h1, h2, _ => by
    have e : n / 10 = 0 := Nat.div_eq_of_lt (by simpa using h2)
    have hz : Dc.Num.digitsIn 10 fuel 0 = [] := by cases fuel <;> rfl
    simp only [Dc.Num.digitsIn, e, hz]
    have : (n == 0) = false := by simp only [Nat.pow_zero] at h1; simp; omega
    simp [this]
  | m + 1, fuel + 1, n, h1, h2, hf => by
    have : (n == 0) = false := by
      have := Nat.one_le_two_pow (n := m + 1); have := Nat.pow_le_pow_left (show 2 ≤ 10 by omega) (m + 1)
      simp; omega
    simp only [Dc.Num.digitsIn, this, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_cons,
      List.length_nil]
    rw [digitsIn_len m fuel (n / 10) ?_ ?_ (by omega)]
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [← Nat.pow_succ]; exact h1)
    · exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [← Nat.pow_succ]; exact h2)

/-- The digits of a digit list's value with a nonzero lead: one per digit. -/
theorem digits_dval_len {d : Nat} {r : List Nat} (hd : Digits (d :: r)) (h0 : d ≠ 0) :
    (Dc.Num.digits 10 (dval (d :: r))).length = r.length + 1 := by
  have hlo : 10 ^ r.length ≤ dval (d :: r) := by
    have := dval_ge_head (d := d) (ds := r)
    exact Nat.le_trans (Nat.le_mul_of_pos_left _ (by omega)) this
  have hhi := dval_lt hd
  simp only [List.length_cons] at hhi
  exact digitsIn_len _ _ _ hlo hhi (by have := Nat.lt_pow_self (n := r.length) (show 1 < 10 by omega); omega)

/-- **`numLen` of a represented number**: its digits less the leading
zeros `dc_numlen` skips, at least one. -/
theorem numLen_rep {ds : List Nat} (hd : Digits ds) {n : Nat} (hl : ds.length = n) (h1 : 1 ≤ n)
    (neg : Bool) (sc : Nat) : Dc.Num.numLen ⟨neg, dval ds, sc⟩ = n - lzCount (n - 1) ds := by
  have hk := lzCount_le (n - 1) ds
  have e := dval_drop_zeros (lzCount (n - 1) ds) ds (lzCount_zeros (n - 1) ds)
  simp only [Dc.Num.numLen]
  rw [← e]
  have hdr : Digits (ds.drop (lzCount (n - 1) ds)) := fun d hm => hd d (List.mem_of_mem_drop hm)
  rcases lzCount_stop (n - 1) ds (by omega) with hs | hs
  · rw [hs]
    have hl1 : (ds.drop (n - 1)).length = 1 := by rw [List.length_drop]; omega
    rw [hs] at hdr
    match hm : ds.drop (n - 1), hl1, hdr with
    | [d], _, hdr =>
      by_cases h0 : d = 0
      · subst h0; simp only [dval_cons, dval_nil]; simp [Dc.Num.digits, Dc.Num.digitsIn]; omega
      · rw [digits_dval_len hdr h0]; simp; omega
  · have hlen : (ds.drop (lzCount (n - 1) ds)).length = n - lzCount (n - 1) ds := by
      rw [List.length_drop]; omega
    match hm : ds.drop (lzCount (n - 1) ds), hlen, hdr with
    | [], hlen, _ => simp only [List.length_nil] at hlen; omega
    | d :: r, hlen, hdr =>
      have hd0 : ds.getD (lzCount (n - 1) ds) 0 = d := by
        have := List.getElem?_drop (xs := ds) (i := lzCount (n - 1) ds) (j := 0)
        rw [hm, Nat.add_zero] at this
        rw [List.getD_eq_getElem?_getD, ← this]; rfl
      rw [digits_dval_len hdr (hd0 ▸ hs)]
      simp only [List.length_cons] at hlen; omega

/-- `dc_numlen`'s scan (`0x800029f0`, `a4` at digit `i`, `a5` the `n - i`
digits from it, digits before `i` zero). -/
theorem nl_walk {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {o : NumRep} (hn : NumAt M o)
    {n : Nat} (hnl : o.len + o.scale = n) {ra : BitVec 64} (hal : ra.toNat % 4 = 0) :
    ∀ m i (R : Nat → BitVec 64), n - 2 - i = m → i + 2 ≤ n → R 1 = ra → R 12 = 1#64 →
    R 14 = BitVec.ofNat 64 (o.val + i) → R 15 = BitVec.ofNat 64 (n - i) →
    (∀ j, j < i → o.ds.getD j 0 = 0) →
    (∀ R', Keeps [10, 13, 14, 15] R' R → R' 10 = BitVec.ofNat 64 (n - lzCount (n - 1) o.ds) →
      DW live S Q ra R' M) →
    DW live S Q 0x800029f0#64 R M := by
  intro m
  induction m with
  | zero => ?_
  | succ m ih => ?_
  all_goals
    intro i R hm hi h1 h12 h14 h15 hz hk
    num_facts hn
    have hl := hn.lbu (i := i) (by omega)
    have hd := hn.getD_lt i
    have hdl : o.ds.length = n := by omega
    have wp := sxw_pred (k := n - i) (by omega) (by omega)
    bc_run hlive hS [h1, h12, h14, h15, hl] at 0x800029fc 0x800029e8
    -- a zero digit: one fewer
    · intro he
      bv_nat at he
      rw [Nat.mod_eq_of_lt (by omega)] at he
      bc_run hlive hS [h1, h12, h14, h15, wp] at 0x800029fc 0x800029f0
      · intro h1'
        bv_nat at h1'
        bc_run hlive hS [h1, h12, h14, h15, wp]
        all_goals first | exact hal | skip
        refine hk _ (by keeps_tac Keeps.refl _ _) ?_
        rw [lzCount_eq (n - 1) o.ds (n - 1) (Nat.le_refl _) (by omega) (fun j hj => by
          rcases Nat.lt_or_ge j i with h | h
          · exact hz j h
          · rw [show j = i by omega]; exact he) (.inl rfl)]
        bsimp [wp]; congr 1; omega
      · intro hne1
        bv_nat at hne1
        first
        | (exfalso; omega)
        | (refine ih (i + 1) _ (by omega) (by omega) (by bsimp [h1]) (by bsimp [h12])
            (by bsimp [Nat.add_assoc]) (by bsimp [wp]; rw [Nat.sub_sub]) (fun j hj => by
              rcases Nat.lt_or_ge j i with h | h
              · exact hz j h
              · rw [show j = i by omega]; exact he) fun R' hk' e10 => ?_
           exact hk R' (hk'.trans (by keeps_tac Keeps.refl _ _)) e10)
    -- a nonzero digit: the count
    · intro hne
      bv_nat at hne
      rw [Nat.mod_eq_of_lt (by omega)] at hne
      bc_run hlive hS [h1, h12, h14, h15]
      all_goals first | exact hal | skip
      refine hk _ (by keeps_tac Keeps.refl _ _) ?_
      rw [lzCount_eq (n - 1) o.ds i (by omega) (by omega) hz (.inr hne)]
      bsimp [h15]

/-- **`dc_numlen (n)`** at `0x800029cc`: `a0` the model's `numLen` of a
represented number with an integer digit, memory unchanged. -/
theorem dc_numlen_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {o : NumRep} (hn : NumAt M o)
    (hpos : 1 ≤ o.len) (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 o.p)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 12, 13, 14, 15] R' R → R' 10 = BitVec.ofNat 64 o.num.numLen →
      DW live S Q (R 1) R' M) :
    DW live S Q 0x800029cc#64 R M := by
  num_facts hn
  have hnl := hn.len; have hsc := hn.scale; have hvl := hn.value
  have e : o.num.numLen = o.len + o.scale - lzCount (o.len + o.scale - 1) o.ds :=
    numLen_rep hn.shape.dig (by omega) (by omega) o.neg o.scale
  have w := addw_ofNat (a := o.scale) (b := o.len) (by omega)
  have ti : (BitVec.ofNat 64 (o.scale + o.len)).toInt = ((o.scale + o.len : Nat) : Int) :=
    toInt_ofNat_small (by omega)
  bc_run hlive hS [h10, hnl, hsc, hvl, w, ti] at 0x800029fc 0x800029f0
  · intro hle
    rw [show (1#64).toInt = 1 by decide] at hle
    have e1 : o.scale + o.len = 1 := by omega
    bc_run hlive hS [h10, hnl, hsc, hvl, w, ti]
    all_goals first | exact hal | skip
    refine hk _ (by keeps_tac Keeps.refl _ _) ?_
    rw [e, show o.len + o.scale - 1 = 0 by omega]
    bsimp [e1]; simp only [lzCount]; congr 1; omega
  · intro hgt
    rw [show (1#64).toInt = 1 by decide] at hgt
    bc_run hlive hS [h10, hvl] at 0x800029f0
    refine nl_walk hlive hS hn rfl hal _ 0 _ rfl ?_ ?_ ?_ ?_ ?_
      (fun j hj => absurd hj (Nat.not_lt_zero _)) fun R' hk' e10 => ?_
    · omega
    · bsimp []
    · bsimp []
    · bsimp [hvl]
    · bsimp [Nat.add_comm]
    · exact hk R' ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) (by rw [e10, e])

/-! ## `dc_tell_scale` -/

theorem word_sub32 {x : Nat} (h : 32 ≤ x) :
    BitVec.ofNat 64 x + 18446744073709551584#64 = BitVec.ofNat 64 (x - 32) := by
  change BitVec.ofNat 64 x + -(32#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le x 32 (by decide) h

/-- The registers `dc_tell_scale` changes. -/
abbrev tellScaleClob : List Nat := [1, 2, 10, 13, 14, 15]

/-- **`dc_tell_scale (num, 0)`** at `0x80002a04`, as `dc_func`'s `X` calls
it: `a0` the scale of the held number `x`, the handle released by
`bc_free_num`. -/
theorem dc_tell_scale_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {x : NumObj}
    (h : DcAt S M H F L C G (.num x.rep.p :: hs) st) (hx : x ∈ L)
    {sp : Nat} (hsf : StackFrame S sp 64) (hab : heapEnd + 64 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 x.rep.p)
    (h11 : R 11 = 0#64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps tellScaleClob R' R → R' 2 = R 2 →
      R' 10 = BitVec.ofNat 64 x.rep.scale → DcAt S M' H' F' L' C' G hs st → StkOut sp 64 M' M →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80002a04#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hn := h.heap.nums x hx
  num_facts hn
  have hsc := hn.scale
  bc_run hlive hS [h2, h10, h11, word_sub32 (show 32 ≤ sp by omega)] at 0x800048c0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have g8 : ldv .lw (writeLog (writeLog M [(sp - 32 + 24, 8, R 1)])
      [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) (x.rep.p + 8) = BitVec.ofNat 64 x.rep.scale := by
    rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega), ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact hsc
  rw [g8]
  bc_run hlive hS [] at 0x800048c0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM2 : MemOnly (frameIn sp 32) (writeLog (writeLog (writeLog M [(sp - 32 + 24, 8, R 1)])
      [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) [(sp - 32, 8, BitVec.ofNat 64 x.rep.scale)]) M :=
    fun a ha => by
      simp only [frameIn] at ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have m8 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 32 + 24, 8, R 1)])
      [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) [(sp - 32, 8, BitVec.ofNat 64 x.rep.scale)])
      (sp - 32 + 8) = BitVec.ofNat 64 x.rep.p := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have m0 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 32 + 24, 8, R 1)])
      [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) [(sp - 32, 8, BitVec.ofNat 64 x.rep.scale)])
      (sp - 32) = BitVec.ofNat 64 x.rep.scale := ldv_store_hit _ _ _
  have m24 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 32 + 24, 8, R 1)])
      [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) [(sp - 32, 8, BitVec.ofNat 64 x.rep.scale)])
      (sp - 32 + 24) = R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize writeLog (writeLog (writeLog M [(sp - 32 + 24, 8, R 1)])
      [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) [(sp - 32, 8, BitVec.ofNat 64 x.rep.scale)] = M2
    at hM2 m8 m0 m24 ⊢
  have hab2 : heapEnd ≤ sp - 64 := by simp only [heapEnd]; omega
  have h2' := h.outWrite hM2 fun a ha =>
    ⟨(above_sp (sp := sp - 32) (by simp only [heapEnd]; omega) (by simp only [frameIn] at ha; omega)).1,
      (above_sp (sp := sp - 32) (by simp only [heapEnd]; omega) (by simp only [frameIn] at ha; omega)).2.1⟩
  refine bc_free_num_dc hlive h2' (hsf.slot (by omega) (by omega) (by omega))
    (by simp only [heapEnd]; omega) m8 (hsf.within (m := 32) (n := 32) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (.inr (by omega)) _ (by bsimp [h2]) (by bsimp [h2]) (by bsimp [])
    fun R6 M6 H6 F6 L6 C6 hk6 hd6 hz6 hout6 => ?_
  have hab3 : heapEnd ≤ sp - 32 := by simp only [heapEnd]; omega
  have k0 : ∀ o, o < 32 → (o + 8 ≤ 8 ∨ 16 ≤ o) → ∀ j, j < 8 → imgM M6 (sp - 32 + o + j) = imgM M2 (sp - 32 + o + j) :=
    fun o ho h8 j hj => hout6 _ (above_sp hab3 (by omega)).1 (above_sp hab3 (by omega)).2.1
      ((above_sp hab3 (by omega)).2.2 _) (fun hs' => by simp only [slotBytes] at hs'; omega)
  have g0 : ldv .ld M6 (sp - 32) = BitVec.ofNat 64 x.rep.scale :=
    (ldv_congr .ld fun j hj => by simpa using k0 0 (by omega) (by omega) j (by have : widthOfM .ld = 8 := rfl; omega)).trans m0
  have g24 : ldv .ld M6 (sp - 32 + 24) = R 1 :=
    (ldv_congr .ld fun j hj => k0 24 (by omega) (by omega) j (by have : widthOfM .ld = 8 := rfl; omega)).trans m24
  have q6 : R6 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk6.get 2 (by decide)]; bsimp [h2]
  have hS6 : HeapOwn S := fun a e1 e2 => hd6.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS6 [q6, g0, g24]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ M6 H6 F6 L6 C6 ?_ ?_ ?_ hd6 fun a ho hg hf => ?_
  · exact by keeps_tac ((hk6.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
  · bsimp [h2]; try (congr 1; omega)
  · bsimp []
  · rw [hout6 a ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
      (fun hs' => hf (by simp only [slotBytes, frameIn] at hs' ⊢; omega))]
    exact hM2 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

/-! ## `dc_tell_length` -/

/-- `Z`'s length of a value: a number's `numLen`, a string's length. -/
def _root_.Dc.Val.zLen : Dc.Val → Nat
  | .num n => n.numLen
  | .str s => s.length

/-- A string of the state fits the heap. -/
theorem DcAt.str_len {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {o : StrObj} (ho : o ∈ G.strs) : o.s.length < 2 ^ 31 := by
  have ht := (h.view.strs o ho).tsz
  have hb : o.tb ∈ G.blocks :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho, by simp⟩))
  have := blk_bounds h.heap.heap (h.heap.raw.live _ hb)
  simp only [heapStart, heapEnd] at this
  omega

/-- The registers `dc_tell_length` changes. -/
abbrev tellLenClob : List Nat := [1, 2, 10, 11, 12, 13, 14, 15]

/-- `dc_tell_length (num, 0)` on a number. -/
theorem tl_num {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {x : NumObj}
    (h : DcAt S M H F L C G (.num x.rep.p :: hs) st) (hx : x ∈ L)
    {sp : Nat} (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : (R 10).toNat % 2 ^ 32 = 1)
    (h11 : R 11 = BitVec.ofNat 64 x.rep.p) (h12 : R 12 = 0#64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps tellLenClob R' R → R' 2 = R 2 →
      R' 10 = BitVec.ofNat 64 x.rep.num.numLen → DcAt S M' H' F' L' C' G hs st → StkOut sp 80 M' M →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80003804#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have ht := sxw_lo32 h10 (by decide)
  bc_run hlive hS [h2, ht, h11, h12, word_sub48 (show 48 ≤ sp by omega)] at 0x800029cc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [h11, h12] at 0x800029cc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 48) (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, BitVec.ofNat 64 x.rep.p)]) [(sp - 48 + 8, 8, 0#64)]) M :=
    fun a ha => by
      simp only [frameIn] at ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
        imgM_store_miss _ _ (by omega)]
  have m8 : ldv .ld (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, BitVec.ofNat 64 x.rep.p)]) [(sp - 48 + 8, 8, 0#64)])
      (sp - 48 + 8) = 0#64 := ldv_store_hit _ _ _
  have m24 : ldv .ld (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, BitVec.ofNat 64 x.rep.p)]) [(sp - 48 + 8, 8, 0#64)])
      (sp - 48 + 24) = BitVec.ofNat 64 x.rep.p := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have m40 : ldv .ld (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, BitVec.ofNat 64 x.rep.p)]) [(sp - 48 + 8, 8, 0#64)])
      (sp - 48 + 40) = R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, BitVec.ofNat 64 x.rep.p)]) [(sp - 48 + 8, 8, 0#64)] = M1
    at hM1 m8 m24 m40 ⊢
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have hP : ∀ a, frameIn sp 48 a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have h1 := h.outWrite hM1 hP
  refine dc_numlen_spec hlive hS (h1.heap.nums x hx) (h1.den.pos x hx) _ (by bsimp []) (by bsimp [])
    fun R3 hk3 e3 => ?_
  have q3 : R3 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk3.get 2 (by decide)]; bsimp []
  bsimp []
  bc_run hlive hS [q3, m8, e3] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [q3, m8, e3] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM2 : MemOnly (frameIn sp 48) (writeLog M1 [(sp - 48 + 8, 8, BitVec.ofNat 64 x.rep.num.numLen)]) M1 :=
    fun a ha => by simp only [frameIn] at ha; rw [imgM_store_miss _ _ (by omega)]
  have n8 : ldv .ld (writeLog M1 [(sp - 48 + 8, 8, BitVec.ofNat 64 x.rep.num.numLen)]) (sp - 48 + 8) =
      BitVec.ofNat 64 x.rep.num.numLen := ldv_store_hit _ _ _
  have n24 : ldv .ld (writeLog M1 [(sp - 48 + 8, 8, BitVec.ofNat 64 x.rep.num.numLen)]) (sp - 48 + 24) =
      BitVec.ofNat 64 x.rep.p := by rw [ldv_ld_miss _ _ (by omega), m24]
  have n40 : ldv .ld (writeLog M1 [(sp - 48 + 8, 8, BitVec.ofNat 64 x.rep.num.numLen)]) (sp - 48 + 40) =
      R 1 := by rw [ldv_ld_miss _ _ (by omega), m40]
  generalize writeLog M1 [(sp - 48 + 8, 8, BitVec.ofNat 64 x.rep.num.numLen)] = M2 at hM2 n8 n24 n40 ⊢
  have h2' := h1.outWrite hM2 hP
  refine dc_free_num_spec hlive h2' (hsf.slot (by omega) (by omega) (by omega))
    (by simp only [heapEnd]; omega) n24 (hsf.within (m := 48) (n := 32) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (.inr (by omega)) _ (by bsimp []) (by bsimp [q3]) (by bsimp [])
    fun R6 M6 H6 F6 L6 C6 hk6 hd6 hz6 hout6 => ?_
  have k0 : ∀ o, o < 48 → (o + 8 ≤ 24 ∨ 32 ≤ o) → ∀ j, j < 8 →
      imgM M6 (sp - 48 + o + j) = imgM M2 (sp - 48 + o + j) :=
    fun o ho h8 j hj => hout6 _ (above_sp hab2 (by omega)).1 (above_sp hab2 (by omega)).2.1
      ((above_sp hab2 (by omega)).2.2 _) (fun hs' => by simp only [slotBytes] at hs'; omega)
  have g8 : ldv .ld M6 (sp - 48 + 8) = BitVec.ofNat 64 x.rep.num.numLen :=
    (ldv_congr .ld fun j hj => k0 8 (by omega) (by omega) j (by have : widthOfM .ld = 8 := rfl; omega)).trans n8
  have g40 : ldv .ld M6 (sp - 48 + 40) = R 1 :=
    (ldv_congr .ld fun j hj => k0 40 (by omega) (by omega) j (by have : widthOfM .ld = 8 := rfl; omega)).trans n40
  have q6 : R6 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk6.get 2 (by decide)]; bsimp [q3]
  have hS6 : HeapOwn S := fun a e1 e2 => hd6.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS6 [q6, g8, g40]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ M6 H6 F6 L6 C6 ?_ ?_ ?_ hd6 fun a ho hg hf => ?_
  · exact by keeps_tac ((hk6.mono (by decide)).trans (by keeps_tac ((hk3.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))))
  · bsimp [h2]; try (congr 1; omega)
  · bsimp []
  · rw [hout6 a ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
      (fun hs' => hf (by simp only [slotBytes, frameIn] at hs' ⊢; omega))]
    rw [hM2 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

/-- `dc_tell_length (str, 0)` on a string. -/
theorem tl_str {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {o : StrObj}
    (h : DcAt S M H F L C G (.str o.hb.pay :: hs) st) (ho : o ∈ G.strs)
    {sp : Nat} (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : (R 10).toNat % 2 ^ 32 = 2)
    (h11 : R 11 = BitVec.ofNat 64 o.hb.pay) (h12 : R 12 = 0#64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' G', Keeps tellLenClob R' R → R' 2 = R 2 →
      R' 10 = BitVec.ofNat 64 o.s.length → SameNodes G G' → DcAt S M' H' F L C G' hs st →
      StkOut sp 80 M' M → StrPin G.strs G'.strs hs →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80003804#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have ht := sxw_lo32 h10 (by decide)
  bc_run hlive hS [h2, ht, h11, h12, word_sub48 (show 48 ≤ sp by omega)] at 0x80003c6c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [h11, h12] at 0x80003c6c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 48) (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, BitVec.ofNat 64 o.hb.pay)]) [(sp - 48 + 8, 8, 0#64)]) M :=
    fun a ha => by
      simp only [frameIn] at ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
        imgM_store_miss _ _ (by omega)]
  have m8 : ldv .ld (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, BitVec.ofNat 64 o.hb.pay)]) [(sp - 48 + 8, 8, 0#64)])
      (sp - 48 + 8) = 0#64 := ldv_store_hit _ _ _
  have m24 : ldv .ld (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, BitVec.ofNat 64 o.hb.pay)]) [(sp - 48 + 8, 8, 0#64)])
      (sp - 48 + 24) = BitVec.ofNat 64 o.hb.pay := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have m40 : ldv .ld (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, BitVec.ofNat 64 o.hb.pay)]) [(sp - 48 + 8, 8, 0#64)])
      (sp - 48 + 40) = R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, BitVec.ofNat 64 o.hb.pay)]) [(sp - 48 + 8, 8, 0#64)] = M1
    at hM1 m8 m24 m40 ⊢
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have hP : ∀ a, frameIn sp 48 a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have h1 := h.outWrite hM1 hP
  have hlen := (h1.view.strs o ho).len
  have wl := sxw_ofNat (k := o.s.length) (h.str_len ho)
  have hb : o.hb ∈ G.blocks :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho, by simp⟩))
  have hbb := blk_bounds h.heap.heap (h.heap.raw.live _ hb)
  have hbs := (h1.view.strs o ho).hsz
  simp only [heapStart, heapEnd] at hbb
  bc_run hlive hS [m8, hlen, wl] at 0x800039a4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [] at 0x800039a4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM2 : MemOnly (frameIn sp 48) (writeLog M1 [(sp - 48 + 8, 8, BitVec.ofNat 64 o.s.length)]) M1 :=
    fun a ha => by simp only [frameIn] at ha; rw [imgM_store_miss _ _ (by omega)]
  have n8 : ldv .ld (writeLog M1 [(sp - 48 + 8, 8, BitVec.ofNat 64 o.s.length)]) (sp - 48 + 8) =
      BitVec.ofNat 64 o.s.length := ldv_store_hit _ _ _
  have n24 : ldv .ld (writeLog M1 [(sp - 48 + 8, 8, BitVec.ofNat 64 o.s.length)]) (sp - 48 + 24) =
      BitVec.ofNat 64 o.hb.pay := by rw [ldv_ld_miss _ _ (by omega), m24]
  have n40 : ldv .ld (writeLog M1 [(sp - 48 + 8, 8, BitVec.ofNat 64 o.s.length)]) (sp - 48 + 40) =
      R 1 := by rw [ldv_ld_miss _ _ (by omega), m40]
  generalize writeLog M1 [(sp - 48 + 8, 8, BitVec.ofNat 64 o.s.length)] = M2 at hM2 n8 n24 n40 ⊢
  have h2' := h1.outWrite hM2 hP
  refine dc_free_str_spec hlive h2' (hsf.slot (by omega) (by omega) (by omega))
    n24 (hsf.within (m := 48) (n := 32) (by omega) (by decide))
    (by simp only [heapEnd]; omega) _ (by bsimp []) (by bsimp []) (by bsimp [])
    fun R6 M6 H6 G6 hk6 hsn6 hd6 hout6 hpin6 => ?_
  have k0 : ∀ o, o < 48 → ∀ j, j < 8 →
      imgM M6 (sp - 48 + o + j) = imgM M2 (sp - 48 + o + j) :=
    fun o ho j hj => hout6 _ (above_sp hab2 (by omega)).1 (above_sp hab2 (by omega)).2.1
      ((above_sp hab2 (by omega)).2.2 _)
  have g8 : ldv .ld M6 (sp - 48 + 8) = BitVec.ofNat 64 o.s.length :=
    (ldv_congr .ld fun j hj => k0 8 (by omega) j (by have : widthOfM .ld = 8 := rfl; omega)).trans n8
  have g40 : ldv .ld M6 (sp - 48 + 40) = R 1 :=
    (ldv_congr .ld fun j hj => k0 40 (by omega) j (by have : widthOfM .ld = 8 := rfl; omega)).trans n40
  have q6 : R6 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk6.get 2 (by decide)]; bsimp []
  have hS6 : HeapOwn S := fun a e1 e2 => hd6.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS6 [q6, g8, g40]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ M6 H6 G6 ?_ ?_ ?_ hsn6 hd6 (fun a ho hg hf => ?_) hpin6
  · exact by keeps_tac ((hk6.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
  · bsimp [h2]; try (congr 1; omega)
  · bsimp []
  · rw [hout6 a ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))]
    rw [hM2 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

/-- **`dc_tell_length (value, 0)`** at `0x80003804`, as `dc_func`'s `Z`
calls it with the popped datum `g` denoting `v`: `a0` the model's length
(`Val.zLen`), the datum's reference released. -/
theorem dc_tell_length_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {g : GV} {v : Dc.Val}
    (h : DcAt S M H F L C G (g :: hs) st) (hv : g.Den ⟨L, G.strs⟩ v)
    {sp : Nat} (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : (R 10).toNat % 2 ^ 32 = g.tag)
    (h11 : R 11 = BitVec.ofNat 64 g.ptr) (h12 : R 12 = 0#64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps tellLenClob R' R → R' 2 = R 2 →
      R' 10 = BitVec.ofNat 64 v.zLen → SameNodes G G' → DcAt S M' H' F' L' C' G' hs st →
      StkOut sp 80 M' M → StrPin G.strs G'.strs hs → DW live S Q (R 1) R' M') :
    DW live S Q 0x80003804#64 R M := by
  match g, v, hv with
  | .num _, .num _, ⟨x, hx, rfl, rfl⟩ =>
    exact tl_num hlive h hx hsf hab R h2 h10 h11 h12 hal fun R' M' H' F' L' C' k1 k2 k3 k4 k5 =>
      hk R' M' H' F' L' C' G k1 k2 k3 ⟨rfl, rfl, rfl⟩ k4 k5 (StrPin.refl _ _)
  | .str _, .str _, ⟨o, ho, rfl, rfl⟩ =>
    exact tl_str hlive h ho hsf hab R h2 h10 h11 h12 hal fun R' M' H' G' k1 k2 k3 k4 k5 k6 k7 =>
      hk R' M' H' F L C G' k1 k2 k3 k4 k5 k6 k7
  | .num _, .str _, hv => exact hv.elim
  | .str _, .num _, hv => exact hv.elim

end Dc.Mach
