import Dc.Mach.Bc.DivSpec
import Dc.Mach.Bc.BcMul
import Dc.Mach.Bc.BcSub
import Dc.Mach.Bc.FreeSites

/-!
# `bc_divmod` (`lib/number.c`, `0x80005fd0`): the contract and its tail

`bc_divmod (num1, num2, quot, rem, scale)`:

    if (bc_is_zero (num2)) return -1;
    rscale = MAX (num1->n_scale, num2->n_scale + scale);
    bc_init_num (&temp);                     /* _zero_, one reference more */
    bc_divide (num1, num2, &temp, scale);
    if (quot) quotient = bc_copy_num (temp); /* one reference more */
    bc_multiply (temp, num2, &temp, rscale);
    bc_sub (num1, temp, rem, rscale);
    bc_free_num (&temp);                     /* inlined */
    if (quot) { bc_free_num (quot); *quot = quotient; }
    return 0;

against `Num.divmod`. The two inlined frees of `temp` are generated
(`ffree_800060a8`, `ffree_80006168`, `FreeSites.lean`).

- `DmCtx`: the frame (80 bytes, then the deepest callee: `bc_multiply` over
  operands of fewer than `2^30` digits), `mul_base_digits` and the
  constants owned.
- `DmSlot`: a result slot off the heap, apart from the window.
- `DmArgs`: the operands, `_zero_` with room for the references taken, and
  every number of the heap an owner (outside `_bc_rec_mul` there are no
  views).
- `ResNum`: a result: the new number in its slot.
- `DropAt L p L'`: one reference of the number at `p` dropped.
- `DmPostQ` / `DmPostR`: the post with and without the quotient.
- `DmKQ` / `DmKR`: the continuations.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `bc_divmod`'s context: the 80-byte frame and room for its callees. -/
structure DmCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp W : Nat) : Prop where
  frame : StackFrame S sp W
  above : heapEnd + W ≤ sp
  big : 176 + rmStack (2 ^ 30) ≤ W
  mulBase : ∀ a, mulBaseAddr ≤ a → a < mulBaseAddr + 4 → S a
  consts : ∀ a, constBytes a → S a
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0

/-- A result slot: off the heap, apart from the window. -/
structure DmSlot (S : Nat → Prop) (sp W q : Nat) : Prop where
  slot : PtrSlot S q
  out : ∀ a, slotBytes q a → OutHeap a
  apart : q + 8 ≤ sp - W ∨ sp ≤ q

/-- The operands. -/
structure DmArgs (M : Mem) (L : List NumObj) (x1 x2 z : NumObj) (k : Nat) : Prop where
  m1 : x1 ∈ L
  m2 : x2 ∈ L
  mz : z ∈ L
  n1 : x1.rep.Norm
  n2 : x2.rep.Norm
  /-- `bc_new_num` takes a positive integer length -/
  len1 : 1 ≤ x1.rep.len
  size : x1.rep.len + x1.rep.scale + k + x2.rep.len + x2.rep.scale < 2 ^ 27
  zero : KZero M z (2 ^ 30)
  mulBase : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80
  owns : ∀ y ∈ L, y.Owns

/-- A new number `y` for `n`: normalized, with an integer digit, one
reference, its own buffer. -/
structure NewNum (n : Num) (y : NumObj) : Prop where
  num : y.rep.num = n
  norm : y.rep.Norm
  pos : 1 ≤ y.rep.len
  refs : y.rep.refs = 1
  owns : y.Owns

/-- A result `y` for `n` in the slot `q`. -/
structure ResNum (M : Mem) (q : Nat) (n : Num) (y : NumObj) : Prop extends NewNum n y where
  slot : ldv .ld M q = BitVec.ofNat 64 y.sb.pay

/-- `L'` is `L` with one reference of the number at `p` dropped. -/
def DropAt (L : List NumObj) (p : Nat) (L' : List NumObj) : Prop :=
  ∃ L1 L2 x, L = L1 ++ x :: L2 ∧ x.rep.p = p ∧ FreedRest L1 L2 x L'

/-- With the quotient: the remainder `yr` and quotient `yq` head the heap
left by dropping the old remainder `xr`, then the old quotient `xq`. -/
structure DmPostQ (S : Nat → Prop) (Mt0 Mt : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (xq xr : NumObj) (qq qr sp W : Nat) (m : Num × Num) (Lf : List NumObj) (yq yr : NumObj) :
    Prop where
  heap : BcHeap S Mt H F (yr :: yq :: Lf)
  mid : ∃ Lm, DropAt L xr.rep.p Lm ∧ DropAt Lm xq.rep.p Lf
  quo : ResNum Mt qq m.1 yq
  rem : ResNum Mt qr m.2 yr
  out : ∀ a, OutHeap a → ¬ slotBytes qq a → ¬ slotBytes qr a → ¬ frameIn sp W a →
    imgM Mt a = imgM Mt0 a

/-- Without the quotient. -/
structure DmPostR (S : Nat → Prop) (Mt0 Mt : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (xr : NumObj) (qr sp W : Nat) (r : Num) (Lf : List NumObj) (yr : NumObj) : Prop where
  heap : BcHeap S Mt H F (yr :: Lf)
  mid : DropAt L xr.rep.p Lf
  rem : ResNum Mt qr r yr
  out : ∀ a, OutHeap a → ¬ slotBytes qr a → ¬ frameIn sp W a → imgM Mt a = imgM Mt0 a

/-- `out_of_memory`, with only the window changed off the heap. -/
def DmOom (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (Mt0 : Mem)
    (sp W : Nat) : Prop :=
  ∀ R' Mt' sp', sp - W ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
    (∀ a, OutHeap a → ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) →
    DW live S Q 0x80002bcc#64 R' Mt'

/-- A division by zero: `-1`, only the window changed. -/
def DmZero (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (sp W : Nat) : Prop :=
  ∀ R' Mt', Keeps binClob R' R0 → R' 10 = 0xffffffffffffffff#64 →
    (∀ a, ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) → DW live S Q (R0 1) R' Mt'

/-- `bc_divmod`'s continuations with the quotient slot `qq`. -/
structure DmKQ (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (L : List NumObj) (xq xr : NumObj) (qq qr sp W : Nat)
    (n : Option (Num × Num)) : Prop where
  ret : ∀ m, n = some m → ∀ R' Mt' H F Lf yq yr, Keeps binClob R' R0 → R' 10 = 0#64 →
    DmPostQ S Mt0 Mt' H F L xq xr qq qr sp W m Lf yq yr → DW live S Q (R0 1) R' Mt'
  zero : n = none → DmZero live S Q R0 Mt0 sp W
  oom : DmOom live S Q Mt0 sp W

/-- `bc_divmod`'s continuations without the quotient (`bc_modulo`). -/
structure DmKR (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (L : List NumObj) (xr : NumObj) (qr sp W : Nat)
    (n : Option Num) : Prop where
  ret : ∀ r, n = some r → ∀ R' Mt' H F Lf yr, Keeps binClob R' R0 → R' 10 = 0#64 →
    DmPostR S Mt0 Mt' H F L xr qr sp W r Lf yr → DW live S Q (R0 1) R' Mt'
  zero : n = none → DmZero live S Q R0 Mt0 sp W
  oom : DmOom live S Q Mt0 sp W

/-- The prologue's saved registers (offsets from the lowered `sp`). -/
abbrev dmSlots : List (Nat × Nat) :=
  [(21, 24), (20, 32), (19, 40), (18, 48), (9, 56), (1, 72), (8, 64)]

/-- The registers `bc_divmod` changes before its epilogue. -/
abbrev dmAll : List Nat :=
  [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 28, 29, 30, 31]

/-- The epilogue from `0x800060e4` (`a0` already set). -/
theorem dm_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} (cx : DmCtx S R0 sp W) (hS : HeapOwn S)
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0)
    (hk : ∀ R', Keeps binClob R' R0 → R' 10 = R 10 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x800060e4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hal := cx.al
  bc_run hlive hS [h2, sv.get 1 72, sv.get 8 64, sv.get 9 56, sv.get 18 48, sv.get 19 40,
    sv.get 20 32, sv.get 21 24]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (Keeps.unwind (all := dmAll) (saved := [1, 2, 8, 9, 18, 19, 20, 21]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp)) (by bsimp [])
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, h2, sv.get 1 72, sv.get 8 64, sv.get 9 56, sv.get 18 48, sv.get 19 40, sv.get 20 32, sv.get 21 24]
  all_goals (try (congr 1; omega))

/-- The quotient stored at `0x80006124` (`*quot = quotient`), then `a0 = 0`
and the epilogue. -/
theorem dm_qstore {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W qq qr : Nat} {L Lf : List NumObj}
    {xq xr yq yr : NumObj} {H : Heap} {F : List Blk} {n : Option (Num × Num)} {a b : Num}
    (cx : DmCtx S R0 sp W) (sq : DmSlot S sp W qq) (hqr : qq + 8 ≤ qr ∨ qr + 8 ≤ qq)
    (hk : DmKQ live S Q R0 Mt0 L xq xr qq qr sp W n) (hn : n = some (a, b))
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hb : BcHeap S M H F (yr :: yq :: Lf))
    (hmid : ∃ Lm, DropAt L xr.rep.p Lm ∧ DropAt Lm xq.rep.p Lf)
    (hyq : NewNum a yq) (hyr : ResNum M qr b yr)
    (hout : ∀ a, OutHeap a → ¬ slotBytes qq a → ¬ slotBytes qr a → ¬ frameIn sp W a →
      imgM M a = imgM Mt0 a)
    (h19 : R 19 = BitVec.ofNat 64 qq) (h20 : R 20 = BitVec.ofNat 64 yq.sb.pay) :
    DW live S Q 0x80006124#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hq := sq.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := sq.apart
  bc_run hlive hS [h19, h20] at 0x800060e4
  all_goals first | exact hq.acc | skip
  have sv' := sv.transport (lo := 24) (top := 80)
    (M' := writeLog M [(qq, 8, BitVec.ofNat 64 yq.sb.pay)])
    (hag := fun a h1 h2' => imgM_store_miss _ _ (by omega))
  refine dm_epi hlive cx hS sv' (by bsimp [h2]) (by keeps_tac hkp) fun R' hk' h10 => ?_
  refine hk.ret _ hn R' _ H F Lf yq yr hk' (by rw [h10]; bsimp []) ?_
  have hsr := hyr.slot
  exact
    { heap := hb.out_frame (P := slotBytes qq) (fun a ha => imgM_store_miss _ _ (by
        simp only [slotBytes] at ha; omega)) sq.out
      mid := hmid
      quo := { hyq with slot := ldv_store_hit _ _ _ }
      rem := { hyr with slot := by rw [ldv_ld_miss _ _ (by omega)]; exact hsr }
      out := fun a ha hs1 hs2 hf => by
        rw [imgM_store_miss _ _ (by simp only [slotBytes] at hs1; omega)]
        exact hout a ha hs1 hs2 hf }

/-- The old quotient freed at `0x8000611c` (`bc_free_num (quot)`), then the
store. -/
theorem dm_qtail {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W qq qr : Nat} {L A B : List NumObj}
    {xq xr x yq yr : NumObj} {H : Heap} {F : List Blk} {n : Option (Num × Num)} {a b : Num}
    (cx : DmCtx S R0 sp W) (sq : DmSlot S sp W qq) (sr : DmSlot S sp W qr)
    (hqr : qq + 8 ≤ qr ∨ qr + 8 ≤ qq)
    (hk : DmKQ live S Q R0 Mt0 L xq xr qq qr sp W n) (hn : n = some (a, b))
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hb : BcHeap S M H F (yr :: yq :: (A ++ x :: B)))
    (hown : ∀ y ∈ A, y.Owns)
    (hmid : DropAt L xr.rep.p (A ++ x :: B)) (hxp : x.rep.p = xq.rep.p) (hx1 : 1 ≤ x.rep.refs)
    (hqw : ldv .ld M qq = BitVec.ofNat 64 x.rep.p)
    (hyq : NewNum a yq) (hyr : ResNum M qr b yr)
    (hout : ∀ a, OutHeap a → ¬ slotBytes qq a → ¬ slotBytes qr a → ¬ frameIn sp W a →
      imgM M a = imgM Mt0 a)
    (h19 : R 19 = BitVec.ofNat 64 qq) (h20 : R 20 = BitVec.ofNat 64 yq.sb.pay) :
    DW live S Q 0x8000611c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hq := sq.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := sq.apart; have hapr := sr.apart
  have hxm : x ∈ yr :: yq :: (A ++ x :: B) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have hxn := hb.nums x hxm
  have hxp' : heapStart ≤ x.rep.p ∧ x.rep.p + 16 ≤ heapEnd :=
    ⟨hxn.shape.pLo, by have := hxn.shape.pHi; omega⟩
  have hxb := hb.blocks x hxm
  have hb' : BcHeap S M H F ((yr :: yq :: A) ++ x :: B) := hb
  have hnv : x.rep.refs = 1 → x.Owns → ∀ z ∈ yr :: yq :: A, z.db ≠ x.db := fun _ hxo z hz =>
    hb'.owner_db_ne hxo hz (by
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hyr.owns
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hyq.owns
      exact hown z hz)
  bc_run hlive hS [h19, h2] at 0x800048c0
  have hsf' : StackFrame S (sp - 80) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  have e : FreeEntry S M H F (yr :: yq :: A) B x qq (sp - 80) :=
    FreeEntry.of_slot (L0 := yr :: yq :: A) hb' ⟨hx1, hqw, hnv⟩ hnv hq sq.out hsf'
      (by simp only [heapEnd]; omega) (by omega)
  have hsr := hyr.slot
  refine bc_free_num_spec hlive e _ (by bsimp [h19]) (by bsimp [h2]) (by bsimp [])
    ⟨fun hx2 R1 Mt1 hk1 hb1 _ hmo => ?_, fun hx1' R1 Mt1 H1 hk1 hrp => ?_⟩
  · bsimp []
    have hfr : ∀ a, ¬ (refsBytes x.rep a ∨ slotBytes qq a) → imgM Mt1 a = imgM M a := hmo
    have sv1 := sv.transport (lo := 24) (top := 80) (M' := Mt1) (hag := fun a h1 h2' =>
      hfr a fun hc => by
        rcases hc with hc | hc
        · simp only [refsBytes, heapStart, heapEnd] at hc hxp'; omega
        · simp only [slotBytes] at hc; omega)
    have hsr1 : ldv .ld Mt1 qr = BitVec.ofNat 64 yr.sb.pay := by
      rw [ldv_congr .ld fun j hj => hfr _ fun hc => by
        have := sr.out (qr + j) ⟨by omega, by simp only [widthOfM] at hj; omega⟩
        rcases hc with hc | hc
        · simp only [refsBytes, OutHeap, heapStart, heapEnd] at hc this hxp'; omega
        · simp only [slotBytes, widthOfM] at hc hj; omega]
      exact hsr
    refine dm_qstore hlive cx sq hqr hk hn sv1 (by rw [hk1.get 2]; bsimp [h2])
      ((hk1.mono (by decide)).trans (by keeps_tac hkp)) hb1
      ⟨_, hmid, A, B, x, rfl, hxp, .dec hx2⟩ hyq { hyr with slot := hsr1 }
      (fun a ha hs1 hs2 hf => by
        rw [hfr a fun hc => by
          rcases hc with hc | hc
          · simp only [refsBytes, OutHeap, heapStart, heapEnd] at hc ha hxp'; omega
          · exact hs1 hc]
        exact hout a ha hs1 hs2 hf)
      (by rw [hk1.get 19]; bsimp [h19]) (by rw [hk1.get 20]; bsimp [h20])
  · bsimp []
    have hfr : ∀ a, ¬ (AllocByte H a ∨ x.sb.In a ∨ slotBytes qq a ∨ frameIn (sp - 80) 32 a ∨
        bcFreeBytes a) → imgM Mt1 a = imgM M a := hrp.frame
    have hoff : ∀ a, OutHeap a → ¬ slotBytes qq a → ¬ frameIn (sp - 80) 32 a →
        imgM Mt1 a = imgM M a := fun a ha hs hf => hfr a fun hc => by
      rcases hc with hc | hc | hc | hc | hc
      · exact OutHeap.not_alloc hb.heap ha hc
      · exact ha.1 (live_in_heap hb.heap hxb.sLive hc)
      · exact hs hc
      · exact hf hc
      · exact ha.2.2 hc
    have hstk : ∀ a, sp - 80 ≤ a → OutHeap a := fun a h => by
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
    have sv1 := sv.transport (lo := 24) (top := 80) (M' := Mt1) (hag := fun a h1 h2' =>
      hoff a (hstk a (by omega)) (by simp only [slotBytes]; omega)
        (by simp only [frameIn]; omega))
    have hsr1 : ldv .ld Mt1 qr = BitVec.ofNat 64 yr.sb.pay := by
      rw [ldv_congr .ld fun j hj => hoff _ (sr.out _ ⟨by omega, by
        simp only [widthOfM] at hj; omega⟩) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
        (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
      exact hsr
    refine dm_qstore hlive cx sq hqr hk hn sv1 (by rw [hk1.get 2]; bsimp [h2])
      ((hk1.mono (by decide)).trans (by keeps_tac hkp)) hrp.heap
      ⟨_, hmid, A, B, x, rfl, hxp, .rel hx1'⟩ hyq { hyr with slot := hsr1 }
      (fun a ha hs1 hs2 hf => by
        rw [hoff a ha hs1 (by simp only [frameIn] at hf ⊢; omega)]
        exact hout a ha hs1 hs2 hf)
      (by rw [hk1.get 19]; bsimp [h19]) (by rw [hk1.get 20]; bsimp [h20])

end Dc.Mach
