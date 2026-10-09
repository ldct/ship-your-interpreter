import Dc.Mach.Bc.SqrtInit

/-!
# `bc_sqrt`'s first guess above one (`0x80006ad4`)

`guess = bc_int2num (10)`, `guess1 = bc_int2num (n_len)`, `guess1 *= 0.5`
cut to scale `0`, `guess = bc_raise (guess, guess1)`, `guess1` freed: the
guess `10 ^ (n_len / 2)` at `cscale = 3` (`Dc.BcModel.sqrtInit_hi`).

The handles are `[point5, diff, guess, guess1]`; `diff` keeps its `_zero_`
reference, so after `guess1` is freed they are the loop's `[point5, diff,
guess]` with no `guess1` in `s10`.

- `sq_i2nH`: `bc_int2num` on a handle's slot.
- `SqGo`: the fixed facts of the path; `SqH`: the frame and the handles
  between its calls (`SqH.call` through a callee).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- **`bc_int2num (&h, v)`** on the handle `h` of `bc_sqrt` (its word at
`sp - 160 + o`): the new number replaces it. -/
theorem sq_i2nH {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o : Nat} {v : Int}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {H : Heap} {F : List Blk}
    (cx : SqCtx S R0 sp W q) (hoom : RaOom live S Q Mt0 sp W q) (ho : o + 8 ≤ 48) (ho8 : o % 8 = 0)
    (houtM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S X M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h) (hw : ldv .ld M (sp - 160 + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 160)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 (sp - 160 + o)) (h11 : R 11 = BitVec.ofInt 64 v)
    (hvl : -2 ^ 31 < v) (hvh : v < 2 ^ 31)
    (hret : ∀ R' M' H' F' y, Keeps i2nClob R' R →
      BcHeap S X M' H' F' (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      y.rep.num = Num.ofInt v → y.rep.Norm → y.rep.refs = 1 →
      ldv .ld M' (sp - 160 + o) = BitVec.ofNat 64 y.rep.p →
      (∀ a, OutHeap a → ¬ slotBytes (sp - 160 + o) a → ¬ frameIn (sp - 160) 128 a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000690c#64 R M := by
  sq_facts cx
  have hsl := cx.fslot ho ho8
  obtain ⟨L1, L2, x, e, hp, hr1, hnv, _, _, hfr⟩ := RList.slot hb hh hown
  rw [e] at hb
  have ic := cx.cc.i2n (F := 160) (v := v) (by omega) (by omega) hsl h2 hal hvl hvh
  refine bc_int2num_spec hlive ic (FreeEntry.of_slot hb ⟨hr1, by rw [hw, hp], hnv⟩ hnv hsl.slot hsl.out
    (StackFrame.sub (m := 96) (n := 32) ic.frame (by decide)) (by have := ic.above; omega)
    (.inr (by omega))) h10 h11
    ⟨fun R' M' H' F' L' y hk hp' => ?_, fun R' M' hr2 hout => ?_⟩
  · have hyp : y.rep.p = y.sb.pay := (hp'.heap.blocks y List.mem_cons_self).sPay
    exact hret R' M' H' F' y hk (RList.replace hown hp'.owns hp'.heap (hfr L' hp'.rest))
      (hown.set hp'.owns) hp'.num hp'.norm hp'.refs (by rw [hp'.slot, hyp]) hp'.out
  · refine hoom R' M' (sp - 160 - 128) (by omega) (by omega) hr2 fun a ha hs hf => ?_
    rw [hout a ha (fun h' => hf (by simp only [slotBytes, frameIn] at h' ⊢; omega))
      (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
    exact houtM a ha hs hf

/-- The fixed facts of the path above one: `x > 1` with the Newton loop
from the first guess, and the continuations. -/
structure SqGo (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t : String) (Mt0 : Mem) (R0 : Nat → BitVec 64) (sp W q k : Nat) (L : List NumObj)
    (x z o p5 : NumObj) (rs : Nat) (r : Num) : Prop where
  cx : SqCtx S R0 sp W q
  ha : SqArgs S Mt0 L x z o q k
  oom : RaOom live S (DQ live S Q t) Mt0 sp W q
  p5n : p5.rep.num = Num.half
  p5l : p5.rep.len = 1
  p5s : p5.rep.scale = 1
  p5N : p5.rep.Norm
  rsk : rs = max k x.rep.scale
  xneg : x.rep.neg = false
  gt : Num.cmp x.rep.num Num.one = .gt
  xz : x.rep.p ≠ z.rep.p
  xo : x.rep.p ≠ o.rep.p
  oz : o.rep.p ≠ z.rep.p
  loop : Dc.SqrtLoop x.rep.num rs ⟨false, 10 ^ (x.rep.len / 2), 0⟩ 3 r
  ret : ∀ R' M' H' F' Lf y', Keeps binClob R' R0 → R' 10 = 1#64 →
    SqPost S X Mt0 M' H' F' L x z q sp W r Lf y' → DW live S (DQ live S Q t) (R0 1) R' M'

/-- Between the calls: the frame, the handles `hs`, `s1 = &guess`, `num`,
`point5`, `rscale`, `&_one_` and `diff = _zero_`. -/
structure SqH (S : Nat → Prop) (X : Raws) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (x z p5 : NumObj) (rs : Nat) (hs : List RH) :
    Prop where
  fr : SqFr S X Mt0 M R0 R sp W H F L hs
  r9 : R 9 = BitVec.ofNat 64 (sp - 160 + 24)
  r19 : R 19 = BitVec.ofNat 64 q
  r20 : R 20 = BitVec.ofNat 64 p5.rep.p
  r24 : R 24 = BitVec.ofNat 64 rs
  wq : ldv .ld M q = BitVec.ofNat 64 x.rep.p
  w8 : ldv .ld M (sp - 160 + 8) = BitVec.ofNat 64 oneAddr
  w40 : ldv .ld M (sp - 160 + 40) = BitVec.ofNat 64 z.rep.p

/-- Through a callee that changes the caller-saved registers, the frame word
at `o` and the bytes below the frame, and the handles. -/
theorem SqH.call {S : Nat → Prop} {X : Raws} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H H' : Heap} {F F' : List Blk} {L : List NumObj} {x z p5 : NumObj} {rs o : Nat}
    {hs hs' : List RH} (cx : SqCtx S R0 sp W q) (st : SqH S X Mt0 M R0 R sp W q H F L x z p5 rs hs)
    (ho : 16 ≤ o) (ho' : o + 8 ≤ 40) (hk : Keeps raCallClob R' R)
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - 160 + o) a → ¬ frameIn (sp - 160) (W - 160) a →
      imgM M' a = imgM M a)
    (hb : BcHeap S X M' H' F' (RList hs' L)) (hown : RHOwn hs' L) (hok : ∀ h ∈ hs', RHOK L h) :
    SqH S X Mt0 M' R0 R' sp W q H' F' L x z p5 rs hs' := by
  sq_facts cx
  have hsl := cx.slot
  have hap := hsl.apart
  have hag : ∀ a, OutHeap a → ¬ (sp - 160 ≤ a ∧ a < sp - 112) →
      ¬ frameIn (sp - 160) (W - 160) a → imgM M' a = imgM M a := fun a h1 h2 h3 =>
    hout a h1 (by simp only [slotBytes]; omega) h3
  exact
    { fr :=
        { sa := st.fr.sa.call (hsp := by omega) (hW := by omega) (hkp := hk) (hag := hag)
            (hst := fun a h1 _ => outHeap_of_ge (by simp only [heapEnd]; omega))
          heap := hb
          own := hown
          ok := hok }
      r9 := by rw [hk.get 9 (by decide)]; exact st.r9
      r19 := by rw [hk.get 19 (by decide)]; exact st.r19
      r20 := by rw [hk.get 20 (by decide)]; exact st.r20
      r24 := by rw [hk.get 24 (by decide)]; exact st.r24
      wq := by
        rw [ldv_congr .ld fun j hj => hout _ (hsl.out _ (by simp only [slotBytes, widthOfM] at hj ⊢; omega)) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
        exact st.wq
      w8 := by
        rw [ldv_congr .ld fun j hj => hout _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega)) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
        exact st.w8
      w40 := by rw [sq_word2 cx (o := 40) (o' := o) (by omega) (.inr ho') hout]; exact st.w40 }

/-- `bc_int2num`'s out-of-frame agreement as a callee's of `bc_sqrt`'s frame. -/
theorem sq_i2nOut {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp W q o : Nat} {M M' : Mem}
    (cx : SqCtx S R0 sp W q)
    (h : ∀ a, OutHeap a → ¬ slotBytes (sp - 160 + o) a → ¬ frameIn (sp - 160) 128 a →
      imgM M' a = imgM M a) :
    ∀ a, OutHeap a → ¬ slotBytes (sp - 160 + o) a → ¬ frameIn (sp - 160) (W - 160) a →
      imgM M' a = imgM M a := by
  sq_facts cx
  exact fun a h1 h2 h3 => h a h1 h2 fun h' => h3 (by simp only [frameIn] at h' ⊢; omega)

/-- **`bc_int2num (&h, v)`** on a handle of the path's state (its word at
`sp - 160 + o`): the state with the new number's handle. -/
theorem sq_i2nS {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o rs : Nat} {v : Int}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {x z p5 : NumObj} {H : Heap} {F : List Blk}
    (cx : SqCtx S R0 sp W q) (hoom : RaOom live S Q Mt0 sp W q)
    (st : SqH S X Mt0 M R0 R sp W q H F L x z p5 rs (hs1 ++ h :: hs2))
    (ho : 16 ≤ o) (ho' : o + 8 ≤ 40) (ho8 : o % 8 = 0)
    (hh : RHOK L h) (hw : ldv .ld M (sp - 160 + o) = BitVec.ofNat 64 h.p)
    (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 (sp - 160 + o)) (h11 : R 11 = BitVec.ofInt 64 v)
    (hvl : -2 ^ 31 < v) (hvh : v < 2 ^ 31)
    (hnext : ∀ R' M' H' F' y, SqH S X Mt0 M' R0 R' sp W q H' F' L x z p5 rs (hs1 ++ .own y :: hs2) →
      y.rep.num = Num.ofInt v → y.rep.Norm → y.rep.refs = 1 →
      ldv .ld M' (sp - 160 + o) = BitVec.ofNat 64 y.rep.p →
      (∀ o', o' ≤ 40 → o' + 8 ≤ o ∨ o + 8 ≤ o' → ldv .ld M' (sp - 160 + o') = ldv .ld M (sp - 160 + o')) →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x8000690c#64 R M := by
  sq_facts cx
  refine sq_i2nH hlive (hs1 := hs1) (h := h) (hs2 := hs2) (o := o) (v := v) cx hoom (by omega) ho8
    (fun a ha _ hf => st.fr.sa.out a ha hf) st.fr.heap st.fr.own hh hw st.fr.sa.r2 hal h10 h11 hvl hvh
    fun R1 M1 H1 F1 y hk1 hb1 hown1 hn hN hr hw' hout => ?_
  have hk' : Keeps raCallClob R1 R := (hk1.mono (by decide))
  refine hnext R1 M1 H1 F1 y (SqH.call cx st ho ho' hk' (sq_i2nOut cx hout) hb1 hown1 ?_) hn hN hr hw'
    fun o' h1 h2 => sq_word2 cx (by omega) h2 (sq_i2nOut cx hout)
  intro h' hh'
  rcases List.mem_append.mp hh' with h1 | h1
  · exact st.fr.ok _ (List.mem_append_left _ h1)
  · rcases List.mem_cons.mp h1 with rfl | h1
    · exact ⟨hr, hown1.temps _ (List.mem_append_right _ List.mem_cons_self)⟩
    · exact st.fr.ok _ (List.mem_append_right _ (List.mem_cons_of_mem _ h1))

/-- **`guess = bc_int2num (10)`** from `0x80006ad4`, into the second `_zero_`
handle. -/
theorem sq_hiTen {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z o p5 : NumObj} {r : Num}
    (g : SqGo live S X Q t Mt0 R0 sp W q k L x z o p5 rs r)
    (st : SqS S X Mt0 M R0 R sp W q H F L x z p5 rs)
    (hnext : ∀ R' M' H' F' gg, SqH S X Mt0 M' R0 R' sp W q H' F' L x z p5 rs
        [.own p5, .ref z, .own gg, .ref z] → gg.rep.num = Num.ofInt 10 → gg.rep.Norm →
      gg.rep.refs = 1 → ldv .ld M' (sp - 160 + 24) = BitVec.ofNat 64 gg.rep.p →
      ldv .ld M' (sp - 160 + 32) = BitVec.ofNat 64 z.rep.p →
      DW live S (DQ live S Q t) 0x80006ae4#64 R' M') :
    DW live S (DQ live S Q t) 0x80006ad4#64 R M := by
  have cx := g.cx
  sq_facts cx
  have hb := st.fr.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.fr.sa.r2
  bc_run hlive hS [h2] at 0x8000690c
  refine sq_i2nS hlive (hs1 := [.own p5, .ref z]) (h := .ref z) (hs2 := [.ref z]) (o := 24)
    (v := 10) (rs := rs) (x := x) (z := z) (p5 := p5) (H := H) (F := F) cx g.oom ?_ (by omega) (by omega) (by decide) (st.fr.ok _ (by simp)) st.w24
    (by bsimp []; try decide) (by bsimp []) (by bsimp []; rfl) (by decide) (by decide)
    fun R1 M1 H1 F1 y st1 hn hN hr hw hag => ?_
  · exact { fr := { st.fr with sa := st.fr.sa.regs (ks := [1, 9, 10, 11]) (by keeps_tac Keeps.refl _ _) }
            r9 := by bsimp [], r19 := by bsimp [st.r19], r20 := by bsimp [st.r20]
            r24 := by bsimp [st.r24], wq := st.wq, w8 := st.w8, w40 := st.w40 }
  · bsimp []
    exact hnext R1 M1 H1 F1 y st1 hn hN hr hw
      (by rw [hag 32 (by omega) (.inr (by omega))]; exact st.w32)

@[simp] theorem NumObj.withRefs_len (x : NumObj) (k : Nat) :
    (x.withRefs k).rep.len = x.rep.len := rfl

/-- **`guess1 = bc_int2num (n_len)`** from `0x80006ae4`, into the last
`_zero_` handle. -/
theorem sq_hiLen {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z o p5 gg : NumObj} {r : Num}
    (g : SqGo live S X Q t Mt0 R0 sp W q k L x z o p5 rs r)
    (st : SqH S X Mt0 M R0 R sp W q H F L x z p5 rs [.own p5, .ref z, .own gg, .ref z])
    (w24 : ldv .ld M (sp - 160 + 24) = BitVec.ofNat 64 gg.rep.p)
    (w32 : ldv .ld M (sp - 160 + 32) = BitVec.ofNat 64 z.rep.p)
    (hnext : ∀ R' M' H' F' l, SqH S X Mt0 M' R0 R' sp W q H' F' L x z p5 rs
        [.own p5, .ref z, .own gg, .own l] → l.rep.num = Num.ofInt x.rep.len → l.rep.Norm →
      l.rep.refs = 1 → ldv .ld M' (sp - 160 + 24) = BitVec.ofNat 64 gg.rep.p →
      ldv .ld M' (sp - 160 + 32) = BitVec.ofNat 64 l.rep.p →
      DW live S (DQ live S Q t) 0x80006af4#64 R' M') :
    DW live S (DQ live S Q t) 0x80006ae4#64 R M := by
  have cx := g.cx
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.fr.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hq := cx.slot.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hxn := hb.nums _ (RList.mem_caller _ g.ha.mx)
  num_facts hxn
  have hxl := hxn.len
  simp only [rBump, NumObj.withRefs_p, NumObj.withRefs_len] at *
  have hsz := g.ha.size
  have hx := sxw_ofNat (show x.rep.len < 2 ^ 31 by omega)
  have h2 := st.fr.sa.r2
  bc_run hlive hS [h2, st.r19, st.wq, hxl, hx] at 0x8000690c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hq.acc | skip
  refine sq_i2nS hlive (hs1 := [.own p5, .ref z, .own gg]) (h := .ref z) (hs2 := []) (o := 32)
    (v := (x.rep.len : Int)) (rs := rs) (x := x) (z := z) (p5 := p5) (H := H) (F := F) cx g.oom ?_
    (by omega) (by omega) (by decide) (st.fr.ok _ (by simp)) w32 (by bsimp []; try decide)
    (by bsimp []) (by rw [BitVec.ofInt_natCast]; bsimp []) (by omega) (by omega)
    fun R1 M1 H1 F1 y st1 hn hN hr hw hag => ?_
  · exact { st with
              fr := { st.fr with sa := st.fr.sa.regs (ks := [1, 10, 11, 15]) (by keeps_tac Keeps.refl _ _) }
              r9 := by bsimp [st.r9], r19 := by bsimp [st.r19], r20 := by bsimp [st.r20]
              r24 := by bsimp [st.r24] }
  · bsimp []
    exact hnext R1 M1 H1 F1 y st1 hn hN hr
      (by rw [hag 24 (by omega) (.inl (by omega))]; exact w24) hw

/-- A number of `n ≥ 1` without fraction digits has at least one integer
digit, and at most `m` for `n < 10 ^ m`. -/
theorem NumRep.len_of_int {o : NumRep} (hs : NumShape o) (hn : o.Norm) {m : Nat}
    (hsc : o.scale = 0) (h1 : 1 ≤ dval o.ds) (hm : dval o.ds < 10 ^ m) (hm1 : 1 ≤ m) :
    1 ≤ o.len ∧ o.len ≤ m := by
  refine ⟨Nat.pos_of_ne_zero fun h0 => by rw [NumRep.mag_eq_zero hs h0] at h1; omega, ?_⟩
  rcases Nat.lt_or_ge 1 o.len with h | h
  · have := NumRep.mag_ge hs hn h
    rw [hsc, Nat.add_zero] at this
    have := Nat.pow_lt_pow_iff_right (a := 10) (by decide) |>.mp (Nat.lt_of_le_of_lt this hm)
    omega
  · omega

/-- **`guess1 = guess1 * 0.5`** at scale `0` from `0x80006af4`. -/
theorem sq_hiMul {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z o p5 gg l : NumObj} {r : Num}
    (g : SqGo live S X Q t Mt0 R0 sp W q k L x z o p5 rs r)
    (st : SqH S X Mt0 M R0 R sp W q H F L x z p5 rs [.own p5, .ref z, .own gg, .own l])
    (hln : l.rep.num = Num.ofInt x.rep.len) (hlN : l.rep.Norm) (hlr : l.rep.refs = 1)
    (w24 : ldv .ld M (sp - 160 + 24) = BitVec.ofNat 64 gg.rep.p)
    (w32 : ldv .ld M (sp - 160 + 32) = BitVec.ofNat 64 l.rep.p)
    (hnext : ∀ R' M' H' F' m, SqH S X Mt0 M' R0 R' sp W q H' F' L x z p5 rs
        [.own p5, .ref z, .own gg, .own m] →
      MulRes M' (sp - 160 + 32) (Num.mul (Num.ofInt x.rep.len) Num.half 0) m →
      ldv .ld M' (sp - 160 + 24) = BitVec.ofNat 64 gg.rep.p →
      DW live S (DQ live S Q t) 0x80006b08#64 R' M') :
    DW live S (DQ live S Q t) 0x80006af4#64 R M := by
  have cx := g.cx
  have ha := g.ha
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.fr.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.fr.sa
  have h2 := ra.r2
  have hcs := (SqCst.mk (ha.zero.mono (by omega)) ha.one ha.mulBase).transport cx ra.out
  have objl : l ∈ RList [.own p5, .ref z, .own gg, .own l] L :=
    RH.obj_mem (h := .own l) (by simp) ⟨hlr, st.fr.own.temps _ (by simp)⟩
  have objp : p5 ∈ RList [.own p5, .ref z, .own gg, .own l] L :=
    RH.obj_mem (h := .own p5) (by simp) (st.fr.ok _ (by simp))
  have hls := (hb.nums _ objl).shape
  have hsz := ha.size; have hlx := ha.lenx
  have hlv : dval l.rep.ds = x.rep.len := by
    rw [← NumRep.num_mag, hln]; simp [Num.ofInt]
  have hlsc : l.rep.scale = 0 := by rw [← NumRep.num_scale, hln]; rfl
  obtain ⟨hl1, hl7⟩ := NumRep.len_of_int (m := 7) hls hlN hlsc (by omega) (by
    rw [hlv]; exact Nat.lt_of_lt_of_le (by omega : x.rep.len < 2 ^ 20) (by decide)) (by decide)
  have hp5l := g.p5l; have hp5s := g.p5s
  bc_run hlive hS [h2, w32, st.r20] at 0x8000573c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine sq_mulH hlive (hs1 := [.own p5, .ref z, .own gg]) (h := .own l) (hs2 := []) (o := 32)
    (k := 0) (u1 := l) (u2 := p5) (z := rBump [.own p5, .ref z, .own gg, .own l] z) cx g.oom
    (by omega) (by decide) (fun a ha _ hf => ra.out a ha hf) hb st.fr.own (st.fr.ok _ (by simp))
    { m1 := objl, m2 := objp, mz := RList.mem_caller _ ha.mz
      p1 := by omega
      p2 := by omega
      size := by omega
      scale := by decide
      zero := KZero.rBump _ (by simp) (hcs.zero.mono (by omega))
      mulBase := hcs.mulBase }
    w32 (by bsimp [h2]) (by bsimp []; try decide) (by bsimp [w32]) (by bsimp [st.r20])
    (by bsimp []) (by bsimp []) ?_
  intro R1 M1 H1 F1 y hk1 hb1 hown1 hres hout1
  have hk' := hk1.mono (ks' := raCallClob) (by decide)
  bsimp []
  refine hnext R1 M1 H1 F1 y (SqH.call (hs := [.own p5, .ref z, .own gg, .own l]) (H := H) (F := F) cx ?_
    (o := 32) (by omega) (by omega) hk' hout1 hb1 hown1 ?_)
    (by rw [hln, g.p5n] at hres; exact hres)
    (by rw [sq_word2 cx (o := 24) (o' := 32) (by omega) (.inl (by omega)) hout1]; exact w24)
  · exact { st with
              fr := { st.fr with sa := st.fr.sa.regs (ks := [1, 10, 11, 12, 13]) (by keeps_tac Keeps.refl _ _) }
              r9 := by bsimp [st.r9], r19 := by bsimp [st.r19], r20 := by bsimp [st.r20]
              r24 := by bsimp [st.r24] }
  · intro h hh
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl
    · exact st.fr.ok _ (by simp)
    · exact st.fr.ok _ (by simp)
    · exact st.fr.ok _ (by simp)
    · exact ⟨hres.refs, hres.owns⟩

/-- Every number of the heap referenced, from its temporaries and the
caller's numbers. -/
theorem RList.pos {hs : List RH} {L : List NumObj} (ht : ∀ y, .own y ∈ hs → 1 ≤ y.rep.refs)
    (hL : ∀ y ∈ L, 1 ≤ y.rep.refs) : ∀ y ∈ RList hs L, 1 ≤ y.rep.refs := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · obtain ⟨h0, hh, hy⟩ := List.mem_flatMap.mp h
    cases h0 with
    | own x =>
      simp only [RH.tmp, List.mem_singleton] at hy
      subst hy; exact ht _ hh
    | ref _ => cases hy
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    have := hL w hw
    simp only [rBump, NumObj.withRefs_refs]; omega

/-- **`guess = bc_raise (guess, guess1)`** at `0x8000660c` with `guess1` cut
to scale `0` (`n_len / 2`): `guess`'s handle replaced by the power's
(`raPost_handle`). -/
theorem sq_hiRaise {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z o p5 gg m : NumObj} {r : Num}
    (g : SqGo live S X Q t Mt0 R0 sp W q k L x z o p5 rs r)
    (st : SqH S X Mt0 M R0 R sp W q H F L x z p5 rs [.own p5, .ref z, .own gg, .own m])
    (hgn : gg.rep.num = Num.ofInt 10) (hgN : gg.rep.Norm) (hgr : gg.rep.refs = 1)
    (hmn : m.rep.num = ⟨false, x.rep.len / 2, 0⟩) (hml : 1 ≤ m.rep.len) (hmr : m.rep.refs = 1)
    (w24 : ldv .ld M (sp - 160 + 24) = BitVec.ofNat 64 gg.rep.p)
    (h1 : R 1 = 0x80006b24#64) (h8 : R 8 = BitVec.ofNat 64 m.rep.p)
    (h10 : R 10 = BitVec.ofNat 64 gg.rep.p) (h11 : R 11 = BitVec.ofNat 64 m.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 160 + 24)) (h13 : R 13 = BitVec.ofNat 64 0)
    (hnext : ∀ R' M' H' F' y h, SqH S X Mt0 M' R0 R' sp W q H' F' L x z p5 rs
        [.own p5, .ref z, h, .own m] → RaH S X M' H' F' [.own p5, .ref z] [.own m] L o y h →
      y.rep.num = ⟨false, 10 ^ (x.rep.len / 2), 0⟩ → y.rep.Norm → 1 ≤ y.rep.len →
      R' 8 = BitVec.ofNat 64 m.rep.p →
      ldv .ld M' (sp - 160 + 24) = BitVec.ofNat 64 h.p →
      DW live S (DQ live S Q t) 0x80006b24#64 R' M') :
    DW live S (DQ live S Q t) 0x8000660c#64 R M := by
  have cx := g.cx
  have ha := g.ha
  sq_facts cx
  have hb := st.fr.heap
  have hown := st.fr.own
  have hok5 := st.fr.ok (.own p5) (by simp)
  have objg : gg ∈ RList [.own p5, .ref z, .own gg, .own m] L :=
    RH.obj_mem (h := .own gg) (by simp) ⟨hgr, hown.temps _ (by simp)⟩
  have objm : m ∈ RList [.own p5, .ref z, .own gg, .own m] L :=
    RH.obj_mem (h := .own m) (by simp) ⟨hmr, hown.temps _ (by simp)⟩
  have hgs := (hb.nums _ objg).shape
  have hgsc : gg.rep.scale = 0 := by rw [← NumRep.num_scale, hgn]; rfl
  have hgv : dval gg.rep.ds = 10 := by rw [← NumRep.num_mag, hgn]; rfl
  obtain ⟨hgl1, hgl2⟩ := NumRep.len_of_int (m := 2) hgs hgN hgsc (by omega) (by rw [hgv]; decide)
    (by decide)
  have hcs := (SqCst.mk (ha.zero.mono (by omega)) ha.one ha.mulBase).transport cx st.fr.sa.out
  have hsz := ha.size
  have hexp : (raExp m).natAbs = x.rep.len / 2 := by
    unfold raExp
    rw [hmn]
    simp only [Num.toLong, Num.intPart, Nat.pow_zero, Nat.div_one, Bool.false_eq_true, if_false]
    rw [if_pos (by unfold Num.longMax; omega)]
    rfl
  have hro := ha.refs o ha.mo
  have c4 := rCnt_le [.own p5, .ref z, .own gg, .own m] o.rep.p
  simp only [List.length_cons, List.length_nil] at c4
  have hfd : FdAt S M stderrAddr 2 := by
    have hfar := cx.far
    simp only [stderrAddr] at hfar
    exact ha.fd.transport fun j hj => st.fr.sa.out _
      (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, stderrAddr]; omega)
      (by simp only [frameIn, stderrAddr]; omega)
  have hsize : ((raExp m).natAbs + 1) * (gg.rep.len + gg.rep.scale + 1) + 0 < 2 ^ 24 := by
    rw [hexp, hgsc]
    have := Nat.mul_le_mul (show x.rep.len / 2 + 1 ≤ 2 ^ 19 + 1 by omega)
      (show gg.rep.len + 0 + 1 ≤ 3 by omega)
    omega
  have rc := cx.cc.ra (F := 160) (q := sp - 160 + 24) (R := R) (by omega) (by omega) cx.far
    (cx.fslot (o := 24) (by omega) (by decide)) (.inr (by simp only [zeroAddr]; omega))
    (.inr (by simp only [oneAddr]; omega)) st.fr.sa.r2 (by rw [h1]; decide)
  refine bc_raise_spec hlive (t := t) (Q := Q) rc (L := RList [.own p5, .ref z, .own gg, .own m] L)
    (x1 := gg) (x2 := m) (z := rBump [.own p5, .ref z, .own gg, .own m] z)
    (o := rBump [.own p5, .ref z, .own gg, .own m] o) (xr := gg) (k := 0)
    { m1 := objg, m2 := objm, mz := RList.mem_caller _ ha.mz, mo := RList.mem_caller _ ha.mo
      n1 := hgN, len1 := hgl1, len2 := hml, size := hsize, refs1 := by omega
      zero := KZero.rBump _ (by simp) (hcs.zero.mono (by omega))
      one := hcs.one, oneNum := ha.oneNum, oneNorm := ha.oneNorm, oneLen := ha.oneLen
      oneRefs := by simp only [rBump, NumObj.withRefs_refs]; omega
      mulBase := hcs.mulBase, owns := hown.all, fd := hfd }
    { mr := objg, rr := by omega, wr := w24
      oneRef := fun e => absurd (show gg.rep.p = o.rep.p by rw [e]; rfl)
        (RList.own_ne_caller hb.pdist (by simp) ha.mo)
      zeroRef := fun e => absurd (show gg.rep.p = z.rep.p by rw [e]; rfl)
        (RList.own_ne_caller hb.pdist (by simp) ha.mz)
      zr := fun h0 => absurd h0 (by rw [hgn]; decide) }
    hb (by omega) ⟨fun R' M' H' F' Lf y hk hp => ?_, fun R' M' sp' e1 e2 hr2 hout => ?_⟩
    h10 h11 h12 h13
  · have hpos : ∀ c ∈ RList ([.own p5, .ref z] ++ .own gg :: [.own m]) L, 1 ≤ c.rep.refs :=
      RList.pos (fun y hy => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, RH.own.injEq,
          reduceCtorEq, List.mem_singleton, List.not_mem_nil, or_false, false_or] at hy
        rcases hy with rfl | rfl | rfl
        · exact Nat.le_of_eq hok5.1.symm
        · omega
        · omega) ha.live
    obtain ⟨h, hh⟩ := raPost_handle (hs1 := [.own p5, .ref z]) (hs2 := [.own m]) hb.pdist hown hgr
      hpos ha.mo ha.oneRefs hp
    have hk' := hk.mono (ks' := raCallClob) (by decide)
    rw [h1]
    refine hnext R' M' H' F' y h (SqH.call cx st (o := 24) (by omega) (by omega) hk' hp.out hh.heap
      hh.own ?_) hh ?_ hp.norm hp.pos (by rw [hk.get 8 (by decide)]; exact h8)
      (by rw [hp.slot, hh.p])
    · intro h' hh'
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hh'
      rcases hh' with rfl | rfl | rfl | rfl
      · exact st.fr.ok _ (by simp)
      · exact st.fr.ok _ (by simp)
      · exact hh.ok
      · exact st.fr.ok _ (by simp)
    · rw [hp.num, hgn, hmn]
      exact Dc.BcModel.raise_ten _ (by unfold Num.longMax; omega)
  · refine g.oom R' M' sp' (by omega) (by omega) hr2 fun a ha' hs hf => ?_
    rw [hout a ha' (fun h' => hf (by simp only [slotBytes, frameIn] at h' ⊢; omega))
      (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
    exact st.fr.sa.out a ha' hf

/-- **`guess1->n_scale = 0`** from `0x80006b08`, then `bc_raise`. -/
theorem sq_hiCut {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z o p5 gg m : NumObj} {r : Num}
    (g : SqGo live S X Q t Mt0 R0 sp W q k L x z o p5 rs r)
    (st : SqH S X Mt0 M R0 R sp W q H F L x z p5 rs [.own p5, .ref z, .own gg, .own m])
    (hgn : gg.rep.num = Num.ofInt 10) (hgN : gg.rep.Norm) (hgr : gg.rep.refs = 1)
    (hres : MulRes M (sp - 160 + 32) (Num.mul (Num.ofInt x.rep.len) Num.half 0) m)
    (w24 : ldv .ld M (sp - 160 + 24) = BitVec.ofNat 64 gg.rep.p)
    (hnext : ∀ R' M' H' F' y h, SqH S X Mt0 M' R0 R' sp W q H' F' L x z p5 rs
        [.own p5, .ref z, h, .own { m with rep := m.rep.cutScale 0 }] →
      RaH S X M' H' F' [.own p5, .ref z] [.own { m with rep := m.rep.cutScale 0 }] L o y h →
      y.rep.num = ⟨false, 10 ^ (x.rep.len / 2), 0⟩ → y.rep.Norm → 1 ≤ y.rep.len →
      R' 8 = BitVec.ofNat 64 m.rep.p →
      ldv .ld M' (sp - 160 + 24) = BitVec.ofNat 64 h.p →
      DW live S (DQ live S Q t) 0x80006b24#64 R' M') :
    DW live S (DQ live S Q t) 0x80006b08#64 R M := by
  have cx := g.cx
  have ha := g.ha
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.fr.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hown := st.fr.own
  have hmo : m.Owns := hres.owns
  have objm : m ∈ RList [.own p5, .ref z, .own gg, .own m] L :=
    RH.obj_mem (h := .own m) (by simp) ⟨hres.refs, hmo⟩
  have hmN := hb.nums _ objm
  num_facts hmN
  have hms := hmN.shape
  have hlx := ha.lenx
  have hmn0 : m.rep.num = ⟨false, 5 * x.rep.len, 1⟩ :=
    hres.num.trans (Dc.BcModel.mul_half _ hlx)
  have hmsc : m.rep.scale = 1 := by rw [← NumRep.num_scale, hmn0]
  have hmv : dval m.rep.ds = 5 * x.rep.len := by rw [← NumRep.num_mag, hmn0]
  have hmneg : m.rep.neg = false := by rw [← NumRep.num_neg, hmn0]
  have h2 := st.fr.sa.r2
  have hq := cx.slot
  have hqo := hq.out q (by simp only [slotBytes]; omega)
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hqo
  bc_run hlive hS [h2, hres.slot, w24, st.r9] at 0x8000660c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have e : RList [.own p5, .ref z, .own gg, .own m] L = _ := RList.own_split [.own p5, .ref z, .own gg] [] m L
  rw [e] at hb
  have hb' := BcHeap.setScale hb (v := 0#64) (s := 0) (by decide) (Nat.zero_le _)
  have e' : RList [.own p5, .ref z, .own gg, .own { m with rep := m.rep.cutScale 0 }] L = _ :=
    RList.own_split [.own p5, .ref z, .own gg] [] { m with rep := m.rep.cutScale 0 } L
  rw [← e'] at hb'
  have hcut := NumRep.cutScale_num hms (s := 0) (Nat.zero_le _)
  rw [hmsc, hmneg, NumRep.num_mag, hmv] at hcut
  refine sq_hiRaise hlive g (m := { m with rep := m.rep.cutScale 0 }) (H := H) (F := F) ?_ hgn hgN hgr
    (by rw [hcut]; simp only [Nat.sub_zero, Nat.pow_one]; congr 1; omega) hres.pos hres.refs ?_
    (by bsimp []) (by bsimp [hres.slot]; rfl) (by bsimp [w24]) (by bsimp [hres.slot]; rfl)
    (by bsimp []) (by bsimp []) hnext
  · exact
      { fr :=
          { sa := (st.fr.sa.heap cx (hag := fun a ha' => imgM_store_miss _ _ (by
              simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha'; omega))).regs
              (ks := [1, 8, 10, 11, 12, 13]) (by keeps_tac Keeps.refl _ _)
            heap := hb'
            own := hown.set (h := .own m) (hs1 := [.own p5, .ref z, .own gg]) (hs2 := []) hmo
            ok := fun h hh => by
              simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hh
              rcases hh with rfl | rfl | rfl | rfl
              · exact st.fr.ok _ (by simp)
              · exact st.fr.ok _ (by simp)
              · exact st.fr.ok _ (by simp)
              · exact ⟨hres.refs, hmo⟩ }
        r9 := by bsimp [st.r9], r19 := by bsimp [st.r19], r20 := by bsimp [st.r20]
        r24 := by bsimp [st.r24]
        wq := by rw [ldv_ld_miss _ _ (by omega)]; exact st.wq
        w8 := by rw [ldv_ld_miss _ _ (by omega)]; exact st.w8
        w40 := by rw [ldv_ld_miss _ _ (by omega)]; exact st.w40 }
  · rw [ldv_ld_miss _ _ (by omega)]; exact w24

/-- **`bc_free_num (&guess1)`** inlined at `0x80006b24`. -/
theorem sq_hiFree {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z p5 m : NumObj} {h : RH}
    (cx : SqCtx S R0 sp W q)
    (st : SqH S X Mt0 M R0 R sp W q H F L x z p5 rs [.own p5, .ref z, h, .own m])
    (h8 : R 8 = BitVec.ofNat 64 m.rep.p)
    (hnext : ∀ R' M' H' F', SqH S X Mt0 M' R0 R' sp W q H' F' L x z p5 rs [.own p5, .ref z, h] →
      Keeps [1, 10, 14, 15] R' R → (∀ a, OutHeap a → imgM M' a = imgM M a) →
      DW live S Q 0x80006b54#64 R' M') :
    DW live S Q 0x80006b24#64 R M := by
  sq_facts cx
  have hsl := cx.slot
  refine SqFr.step (hs1 := [.own p5, .ref z, h]) (hs2 := []) cx st.fr
    (fun L1 L2 x hb hr hnv hp k => ffree_80006b24 hlive hb hr hnv (by rw [hp]; exact h8) k k k)
    fun R' M' H' F' hk hag st1 => hnext R' M' H' F'
      { fr := st1
        r9 := by rw [hk.get 9 (by decide)]; exact st.r9
        r19 := by rw [hk.get 19 (by decide)]; exact st.r19
        r20 := by rw [hk.get 20 (by decide)]; exact st.r20
        r24 := by rw [hk.get 24 (by decide)]; exact st.r24
        wq := by
          rw [ldv_congr .ld fun j hj => hag _ (hsl.out _ (by simp only [slotBytes, widthOfM] at hj ⊢; omega))]
          exact st.wq
        w8 := by
          rw [ldv_congr .ld fun j hj => hag _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))]
          exact st.w8
        w40 := by
          rw [ldv_congr .ld fun j hj => hag _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))]
          exact st.w40 } hk hag

/-- **Into the Newton loop** from `0x80006b54`: `guess` the power's handle,
`cscale = 3`, no `guess1`. -/
theorem sq_hiLoop {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z o p5 y : NumObj} {h : RH} {r : Num}
    (g : SqGo live S X Q t Mt0 R0 sp W q k L x z o p5 rs r)
    (st : SqH S X Mt0 M R0 R sp W q H F L x z p5 rs [.own p5, .ref z, h])
    (hp : h.p = y.rep.p) (hbase : ∃ k, h.base = y.withRefs k)
    (hsrc : (∃ t, h = .own t) ∨ h = .ref o)
    (hyn : y.rep.num = ⟨false, 10 ^ (x.rep.len / 2), 0⟩) (hyN : y.rep.Norm) (hyl : 1 ≤ y.rep.len)
    (w24 : ldv .ld M (sp - 160 + 24) = BitVec.ofNat 64 h.p) :
    DW live S (DQ live S Q t) 0x80006b54#64 R M := by
  have cx := g.cx
  have ha := g.ha
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.fr.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := st.fr.sa.r2
  have hx3 := sxw_ofNat (show rs + 1 < 2 ^ 31 by have := ha.size; have := g.rsk; omega)
  bc_run hlive hS [h2, w24, st.r24, hx3] at 0x80006b74
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hon := hb.nums _ (RList.mem_caller _ ha.mo)
  have hos0 := NumRep.one_size hon.shape (by exact ha.oneNorm) (by exact ha.oneNum)
  have hos : o.rep.len + o.rep.scale ≤ 2 := hos0
  have h5ok : RHOK L (.own p5) := st.fr.ok _ (by simp)
  have env := SqArgs.env cx ha (.inl rfl) ha.mz (.inl rfl) g.xz g.oz g.xo g.xneg g.rsk g.p5n
    g.p5l g.p5s g.p5N h5ok hos
  have hxn := hb.nums _ (RList.mem_caller _ ha.mx)
  have hgt := Dc.BcModel.cmp_one (x := x.rep.num) g.xneg
  rw [g.gt] at hgt
  have hg1 : 10 ^ x.rep.scale ≤ x.rep.num.mag := by
    have := Nat.compare_eq_gt.mp hgt.symm; rw [NumRep.num_scale] at this; omega
  have hhi0 := NumRep.hi_bound hxn.shape (by exact ha.nx) (by exact ha.lenx) (by exact hg1)
  have hhi : 10 ^ (x.rep.len / 2 + x.rep.num.scale) ≤ x.rep.num.mag := hhi0
  obtain ⟨kb, hkb⟩ := hbase
  have hpx : h.p ≠ x.rep.p := by
    rcases hsrc with ⟨t', rfl⟩ | rfl
    · exact RList.own_ne_caller hb.pdist (by simp) ha.mx
    · exact Ne.symm g.xo
  have hpz : h.p ≠ z.rep.p := by
    rcases hsrc with ⟨t', rfl⟩ | rfl
    · exact RList.own_ne_caller hb.pdist (by simp) ha.mz
    · exact g.oz
  refine sq_run hlive env g.oom (.inl rfl) g.loop
    (D := .ref z) (G := h) (G1 := none)
    { f :=
        { sa := st.fr.sa.regs (ks := [8, 27, 26, 18, 23, 22, 21]) (by keeps_tac Keeps.refl _ _)
          r9 := by bsimp [st.r9]
          r19 := by bsimp [st.r19]
          r20 := by bsimp [st.r20]
          r21 := by bsimp []
          r22 := by bsimp []
          r23 := by bsimp []
          r24 := by bsimp [st.r24]
          wq := st.wq
          w8 := st.w8 }
      heap := hb
      own := st.fr.own
      okD := st.fr.ok _ (by simp)
      okG := st.fr.ok _ (by simp)
      okT := fun _ hh => by simp at hh
      vG := by rw [hkb]; exact hyn
      nG := by rw [hkb]; exact hyN
      lG := by rw [hkb]; exact hyl
      gx := hpx
      gz := hpz
      model := Dc.BcModel.sqG_initHi hhi
      w24 := w24
      w40 := st.w40
      r8 := by bsimp [w24]
      r18 := by bsimp []
      r27 := by bsimp []
      r26 := by bsimp []; rfl }
    g.ret

/-- **The first guess above one** from `0x80006ad4`, on to the loop and its
exit. -/
theorem sq_hi {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z o p5 : NumObj} {r : Num}
    (g : SqGo live S X Q t Mt0 R0 sp W q k L x z o p5 rs r)
    (st : SqS S X Mt0 M R0 R sp W q H F L x z p5 rs) :
    DW live S (DQ live S Q t) 0x80006ad4#64 R M :=
  sq_hiTen hlive g st fun _ _ _ _ _ st1 hgn hgN hgr w1 w2 =>
    sq_hiLen hlive g st1 w1 w2 fun _ _ _ _ _ st2 hln hlN hlr w3 w4 =>
      sq_hiMul hlive g st2 hln hlN hlr w3 w4 fun _ _ _ _ _ st3 hres w5 =>
        sq_hiCut hlive g st3 hgn hgN hgr hres w5 fun _ _ _ _ _ _ st4 hh hyn hyN hyl h8 w6 =>
          sq_hiFree hlive g.cx st4 h8 fun _ _ _ _ st5 _ hag5 =>
            sq_hiLoop hlive g st5 hh.p hh.base hh.src hyn hyN hyl (by
              have cx := g.cx
              sq_facts cx
              rw [ldv_congr .ld fun j hj => hag5 _
                (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))]
              exact w6)

end Dc.Mach
