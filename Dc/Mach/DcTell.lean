import Dc.Mach.DcRotate

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

end Dc.Mach
