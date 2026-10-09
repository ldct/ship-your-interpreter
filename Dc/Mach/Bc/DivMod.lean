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
  size : x1.rep.len + x1.rep.scale + k + x2.rep.len + x2.rep.scale < 2 ^ 24
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

/-- The quotient and remainder slots of `bc_divmod`, the numbers they hold
at entry: the old quotient dropped after the old remainder (so it needs a
second reference when it is the same number). -/
structure DmQSlots (S : Nat → Prop) (Mt0 : Mem) (L : List NumObj) (xq xr : NumObj)
    (qq qr sp W : Nat) : Prop where
  sq : DmSlot S sp W qq
  sr : DmSlot S sp W qr
  apart : qq + 8 ≤ qr ∨ qr + 8 ≤ qq
  pos : 0 < qq
  mq : xq ∈ L
  mr : xr ∈ L
  rq : 1 ≤ xq.rep.refs
  rr : 1 ≤ xr.rep.refs
  same : xq = xr → 2 ≤ xr.rep.refs
  wq : ldv .ld Mt0 qq = BitVec.ofNat 64 xq.rep.p
  wr : ldv .ld Mt0 qr = BitVec.ofNat 64 xr.rep.p

/-- After the old remainder is dropped, the old quotient is still a number of
the heap. -/
theorem FreedRest.locate {A0 B0 Lm : List NumObj} {xr y : NumObj} (h : FreedRest A0 B0 xr Lm)
    (hy : y ∈ A0 ++ xr :: B0) (hok : y = xr → 2 ≤ xr.rep.refs) (hy1 : 1 ≤ y.rep.refs) :
    ∃ A B x, Lm = A ++ x :: B ∧ x.rep.p = y.rep.p ∧ 1 ≤ x.rep.refs := by
  have hs : y = xr ∨ y ∈ A0 ∨ y ∈ B0 := by
    rcases List.mem_append.mp hy with h1 | h1
    · exact .inr (.inl h1)
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact .inl h2
      · exact .inr (.inr h2)
  cases h with
  | dec h2 =>
    rcases hs with rfl | h1 | h1
    · exact ⟨A0, B0, y.decRef, rfl, rfl, by simp only [NumObj.decRef]; omega⟩
    · obtain ⟨A1, A2, rfl⟩ := List.append_of_mem h1
      exact ⟨A1, A2 ++ xr.decRef :: B0, y, by simp, rfl, hy1⟩
    · obtain ⟨B1, B2, rfl⟩ := List.append_of_mem h1
      exact ⟨A0 ++ xr.decRef :: B1, B2, y, by simp, rfl, hy1⟩
  | rel h1 =>
    rcases hs with rfl | h3 | h3
    · have := hok rfl; omega
    · obtain ⟨A1, A2, rfl⟩ := List.append_of_mem h3
      exact ⟨A1, A2 ++ B0, y, by simp, rfl, hy1⟩
    · obtain ⟨B1, B2, rfl⟩ := List.append_of_mem h3
      exact ⟨A0 ++ B1, B2, y, by simp, rfl, hy1⟩

/-- Dropping a reference keeps every number an owner. -/
theorem FreedRest.owns {A0 B0 Lm : List NumObj} {xr : NumObj} (h : FreedRest A0 B0 xr Lm)
    (ho : ∀ y ∈ A0 ++ xr :: B0, y.Owns) : ∀ y ∈ Lm, y.Owns := by
  intro y hy
  cases h with
  | dec _ =>
    rcases List.mem_append.mp hy with h1 | h1
    · exact ho y (List.mem_append_left _ h1)
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact ho xr (List.mem_append_right _ List.mem_cons_self)
      · exact ho y (List.mem_append_right _ (List.mem_cons_of_mem _ h2))
  | rel _ =>
    rcases List.mem_append.mp hy with h1 | h1
    · exact ho y (List.mem_append_left _ h1)
    · exact ho y (List.mem_append_right _ (List.mem_cons_of_mem _ h1))

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

/-- After the inlined free of `temp` (`0x8000611c`): the product released. -/
theorem dm_qafter {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp W qq qr : Nat} {L A B L' : List NumObj}
    {xq xr x yq yr ym : NumObj} {H H' : Heap} {F F' : List Blk} {n : Option (Num × Num)}
    {a b : Num}
    (cx : DmCtx S R0 sp W) (sq : DmSlot S sp W qq) (sr : DmSlot S sp W qr)
    (hqr : qq + 8 ≤ qr ∨ qr + 8 ≤ qq)
    (hk : DmKQ live S Q R0 Mt0 L xq xr qq qr sp W n) (hn : n = some (a, b))
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hm1 : ym.rep.refs = 1)
    (hkf : KFreed H F [yr] (yq :: (A ++ x :: B)) ym H' F' L') (hb : BcHeap S M' H' F' L')
    (hof : OutFrame (fun _ => False) M' M) (hR : Keeps [1, 10, 14, 15] R' R)
    (hown : ∀ y ∈ A, y.Owns)
    (hmid : DropAt L xr.rep.p (A ++ x :: B)) (hxp : x.rep.p = xq.rep.p) (hx1 : 1 ≤ x.rep.refs)
    (hqw : ldv .ld M qq = BitVec.ofNat 64 x.rep.p)
    (hyq : NewNum a yq) (hyr : ResNum M qr b yr)
    (hout : ∀ a, OutHeap a → ¬ slotBytes qq a → ¬ slotBytes qr a → ¬ frameIn sp W a →
      imgM M a = imgM Mt0 a)
    (h19 : R 19 = BitVec.ofNat 64 qq) (h20 : R 20 = BitVec.ofNat 64 yq.sb.pay) :
    DW live S Q 0x8000611c#64 R' M' := by
  cases hkf with
  | dec h => omega
  | rel _ =>
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have hun : ∀ a, OutHeap a → imgM M' a = imgM M a := fun a ha => hof a ha id
  have hstk : ∀ a, sp - 80 ≤ a → OutHeap a := fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hsr := hyr.slot
  have hsr1 : ldv .ld M' qr = BitVec.ofNat 64 yr.sb.pay := by
    rw [ldv_congr .ld fun j hj => hun _ (sr.out _ ⟨by omega, by
      simp only [widthOfM] at hj; omega⟩)]; exact hsr
  exact dm_qtail hlive cx sq sr hqr hk hn
    (sv.transport (lo := 24) (top := 80) (hag := fun a h1 h2' => hun a (hstk a (by omega))))
    (by rw [hR.get 2]; exact h2) ((hR.mono (by decide)).trans hkp) hb hown hmid hxp hx1
    (by rw [ldv_congr .ld fun j hj => hun _ (sq.out _ ⟨by omega, by
      simp only [widthOfM] at hj; omega⟩)]; exact hqw) hyq { hyr with slot := hsr1 }
    (fun a ha hs1 hs2 hf => (hun a ha).trans (hout a ha hs1 hs2 hf))
    (by rw [hR.get 19]; exact h19) (by rw [hR.get 20]; exact h20)

/-- `bnez s3` at `0x800060dc` with a quotient slot. -/
theorem dm_q60dc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {qq : Nat} (hS : HeapOwn S)
    (h19 : R 19 = BitVec.ofNat 64 qq) (hq0 : 0 < qq) (hq1 : qq < 2 ^ 64)
    (hk : DW live S Q 0x8000611c#64 R M) : DW live S Q 0x800060dc#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h19] at 0x8000611c
  · intro _; exact hk
  · intro hc
    exact absurd ((ofNat_eq_iff (x := qq) (y := 0) (by omega) (by omega)).mp
      (Classical.not_not.mp hc)) (by omega)

/-- **The free of `temp`** at `0x800060a8` (quotient path): the product,
one reference, released. -/
theorem dm_qsite {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W qq qr : Nat} {L A B : List NumObj}
    {xq xr x yq yr ym : NumObj} {H : Heap} {F : List Blk} {n : Option (Num × Num)}
    {a b : Num}
    (cx : DmCtx S R0 sp W) (sq : DmSlot S sp W qq) (sr : DmSlot S sp W qr)
    (hqr : qq + 8 ≤ qr ∨ qr + 8 ≤ qq) (hq0 : 0 < qq)
    (hk : DmKQ live S Q R0 Mt0 L xq xr qq qr sp W n) (hn : n = some (a, b))
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hb : BcHeap S M H F (yr :: ym :: yq :: (A ++ x :: B)))
    (hm1 : ym.rep.refs = 1) (hmo : ym.Owns)
    (hown : ∀ y ∈ A, y.Owns)
    (hmid : DropAt L xr.rep.p (A ++ x :: B)) (hxp : x.rep.p = xq.rep.p) (hx1 : 1 ≤ x.rep.refs)
    (hqw : ldv .ld M qq = BitVec.ofNat 64 x.rep.p)
    (hyq : NewNum a yq) (hyr : ResNum M qr b yr)
    (hout : ∀ a, OutHeap a → ¬ slotBytes qq a → ¬ slotBytes qr a → ¬ frameIn sp W a →
      imgM M a = imgM Mt0 a)
    (h9 : R 9 = BitVec.ofNat 64 ym.rep.p)
    (h19 : R 19 = BitVec.ofNat 64 qq) (h20 : R 20 = BitVec.ofNat 64 yq.sb.pay) :
    DW live S Q 0x800060a8#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hqh := sq.slot.hi
  have hb' : BcHeap S M H F ([yr] ++ ym :: (yq :: (A ++ x :: B))) := hb
  refine ffree_800060a8 (fr := fun _ => False) hlive hb' (by omega)
    (fun _ hxo y hy => hb'.owner_db_ne hxo hy (by
      rcases List.mem_singleton.mp hy with rfl; exact hyr.owns)) h9
    (fun R' M' H' F' L' hR hkf hb1 hof => ?_) (fun R' M' H' F' L' hR hkf hb1 hof => ?_)
    (fun R' M' H' F' L' hR hkf hb1 hof => ?_)
  · exact dm_qafter hlive cx sq sr hqr hk hn sv h2 hkp hm1 hkf hb1 hof hR hown hmid hxp hx1 hqw
      hyq hyr hout h19 h20
  · exact dm_q60dc hlive (fun a h1 h2 => hb1.heap.own a h1 h2) (by rw [hR.get 19]; exact h19)
      hq0 (by omega)
      (dm_qafter hlive cx sq sr hqr hk hn sv h2 hkp hm1 hkf hb1 hof (Keeps.refl _ _ |>.trans hR)
        hown hmid hxp hx1 hqw hyq hyr hout h19 h20)
  · exact dm_qafter hlive cx sq sr hqr hk hn sv h2 hkp hm1 hkf hb1 hof hR hown hmid hxp hx1 hqw
      hyq hyr hout h19 h20

/-- **A call of `bc_sub`** from `bc_divmod`'s frame (`sp - 80`) into the
remainder slot. -/
theorem dm_subCall {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W qr smin : Nat}
    {L1 L2 : List NumObj} {x1 x2 xr : NumObj} {H : Heap} {F : List Blk}
    (cx : DmCtx S R0 sp W) (sr : DmSlot S sp W qr) (hoom : DmOom live S Q Mt0 sp W)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (ha : BinArgs (L1 ++ xr :: L2) x1 x2 smin)
    (hadd : x1.rep.neg ≠ x2.rep.neg → 1 ≤ x1.rep.len ∧ 1 ≤ x2.rep.len)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr qr)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 80)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 qr) (h13 : R 13 = BitVec.ofNat 64 smin)
    (hret : ∀ R' M' H' F' L' y, Keeps binClob R' R →
      BinPost S M M' H' F' L1 L2 xr qr (sp - 80) (Num.sub x1.rep.num x2.rep.num smin) L' y →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80004ac4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have hap := sr.apart
  exact bc_sub_spec hlive
    ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
      by simp only [heapEnd]; omega, sr.slot, sr.out, by omega, h2, hal⟩
    ha hadd hb hr h10 h11 h12 h13
    ⟨hret, fun R' M' sp' h1 h2 hr2 hout => hoom R' M' sp' (by omega) (by omega) hr2
      fun a ha hf => by
        rw [hout a ha (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
        exact houtM a ha hf⟩

/-- **`bc_sub (num1, temp, rem, rscale)`** from `0x80006090` (quotient
path): the remainder, then the free of `temp`. -/
theorem dm_qsub {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W qq qr rs : Nat} {L : List NumObj}
    {xq xr x1 yq ym : NumObj} {H : Heap} {F : List Blk} {n : Option (Num × Num)}
    {a b c : Num}
    (cx : DmCtx S R0 sp W) (sl : DmQSlots S Mt0 L xq xr qq qr sp W)
    (hk : DmKQ live S Q R0 Mt0 L xq xr qq qr sp W n) (hn : n = some (a, b))
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hb : BcHeap S M H F (ym :: yq :: L))
    (hown : ∀ y ∈ L, y.Owns) (hx1 : x1 ∈ L) (hn1 : x1.rep.Norm) (hl1 : 1 ≤ x1.rep.len)
    (hym : NewNum c ym) (hyq : NewNum a yq) (hbv : Num.sub x1.rep.num c rs = b)
    (hsz : ym.rep.len + ym.rep.scale + x1.rep.len + x1.rep.scale + rs < 2 ^ 30)
    (hslot : ldv .ld M (sp - 80 + 8) = BitVec.ofNat 64 ym.sb.pay)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h18 : R 18 = BitVec.ofNat 64 rs)
    (h19 : R 19 = BitVec.ofNat 64 qq) (h20 : R 20 = BitVec.ofNat 64 yq.sb.pay)
    (h21 : R 21 = BitVec.ofNat 64 qr) :
    DW live S Q 0x80006090#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have sq := sl.sq; have sr := sl.sr
  have hapq := sq.apart; have hapr := sr.apart; have hqr := sl.apart
  have hqh := sq.slot.hi; have hrh := sr.slot.hi
  obtain ⟨A0, B0, rfl⟩ := List.append_of_mem sl.mr
  have hb' : BcHeap S M H F ((ym :: yq :: A0) ++ xr :: B0) := hb
  have hymp : ym.rep.p = ym.sb.pay := (hb.blocks ym List.mem_cons_self).sPay
  have hymn := hb.nums ym List.mem_cons_self
  num_facts hymn
  have hx1n := hb.nums x1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx1))
  num_facts hx1n
  have hstk : ∀ a, sp - 80 ≤ a → OutHeap a := fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hwr : ldv .ld M qr = BitVec.ofNat 64 xr.rep.p := by
    rw [ldv_congr .ld fun j hj => houtM _ (sr.out _ ⟨by omega, by
      simp only [widthOfM] at hj; omega⟩) (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact sl.wr
  have hwq : ldv .ld M qq = BitVec.ofNat 64 xq.rep.p := by
    rw [ldv_congr .ld fun j hj => houtM _ (sq.out _ ⟨by omega, by
      simp only [widthOfM] at hj; omega⟩) (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact sl.wq
  have hl1' := hym.pos
  have hnvr : xr.rep.refs = 1 → xr.Owns → ∀ z ∈ ym :: yq :: A0, z.db ≠ xr.db := fun _ hxo z hz =>
    hb'.owner_db_ne hxo hz (by
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hym.owns
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hyq.owns
      exact hown z (List.mem_append_left _ hz))
  bc_run hlive hS [h2, hslot, h18, h21, h8] at 0x80004ac4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dm_subCall (x1 := x1) (x2 := ym) (smin := rs) hlive cx sr hk.oom houtM
    ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx1), List.mem_cons_self, hn1, hym.norm,
      by omega, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    (fun _ => ⟨hl1, hl1'⟩) hb' ⟨sl.rr, hwr, hnvr⟩ (by bsimp [h2]) (by bsimp []; try decide)
    (by bsimp [h8]) (by bsimp [hymp]) (by bsimp [h21]) (by bsimp [h18]) ?_
  intro R' M' H' F' Lr y hk' hp
  bsimp []
  have ⟨Lm, hLr, hfr⟩ : ∃ Lm, Lr = ym :: yq :: Lm ∧ FreedRest A0 B0 xr Lm := by
    cases hp.rest with
    | dec h => exact ⟨_, rfl, .dec h⟩
    | rel h => exact ⟨_, rfl, .rel h⟩
  subst hLr
  obtain ⟨A, B, x, rfl, hxp, hxr1⟩ := hfr.locate sl.mq sl.same sl.rq
  have hown' := hfr.owns hown
  have hpo := hp.out
  have hun : ∀ a, OutHeap a → ¬ slotBytes qr a → ¬ frameIn (sp - 80) 176 a →
      imgM M' a = imgM M a := hpo
  have hc := hym.num
  refine dm_qsite hlive cx sq sr hqr sl.pos hk hn
    (sv.transport (lo := 24) (top := 80) (hag := fun a h1 h2' => hun a (hstk a (by omega))
      (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)))
    (by rw [hk'.get 2]; bsimp [h2]) ((hk'.mono (by decide)).trans (by keeps_tac hkp)) hp.heap
    hym.refs hym.owns (fun y hy => hown' y (List.mem_append_left _ hy))
    ⟨A0, B0, xr, rfl, rfl, hfr⟩ hxp hxr1
    (by rw [ldv_congr .ld fun j hj => hun _ (sq.out _ ⟨by omega, by
      simp only [widthOfM] at hj; omega⟩) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
      (by simp only [frameIn, widthOfM] at hj ⊢; omega), hwq, hxp])
    hyq ⟨⟨by rw [hp.num, NumRep.num_eq ym.rep, ← NumRep.num_eq, hc, hbv], hp.norm, hp.pos,
      hp.refs, hp.owns⟩, hp.slot⟩
    (fun a ha hs1 hs2 hf => by
      rw [hun a ha hs2 (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
      exact houtM a ha hf)
    (by rw [hk'.get 9]; bsimp [hymp]) (by rw [hk'.get 19]; bsimp [h19])
    (by rw [hk'.get 20]; bsimp [h20])

/-- `rmStack` is monotone. -/
theorem rmStack_mono {a b : Nat} (h : a ≤ b) : rmStack a ≤ rmStack b := by
  unfold rmStack; have := rmDepth_mono h; omega

/-- **A call of `bc_multiply`** from `bc_divmod`'s frame (`sp - 80`) into
`temp` (`sp - 72`). -/
theorem dm_mulCall {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W k : Nat}
    {L1 L2 : List NumObj} {x1 x2 xr z : NumObj} {H : Heap} {F : List Blk}
    (cx : DmCtx S R0 sp W) (hoom : DmOom live S Q Mt0 sp W)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (ha : MulArgs M (L1 ++ xr :: L2) x1 x2 z k)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr (sp - 80 + 8))
    (h2 : R 2 = BitVec.ofNat 64 (sp - 80)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 80 + 8)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ R' M' H' F' L' y, Keeps binClob R' R →
      BinPostW S M M' H' F' L1 L2 xr (sp - 80 + 8) (sp - 80) (W - 80)
        (Num.mul x1.rep.num x2.rep.num k) L' y → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000573c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hsz := ha.size
  have hrs := rmStack_mono (show x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale) ≤ 2 ^ 30
    by omega)
  exact bc_multiply_spec hlive
    ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
      by simp only [heapEnd]; omega, by omega,
      ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩,
      fun a ha => by simp only [slotBytes] at ha; simp only [OutHeap, heapStart, heapEnd,
        freeListAddr, bcFreeAddr]; omega,
      .inr (by omega), cx.mulBase, cx.consts, h2, hal⟩
    ha (by omega) hb hr h10 h11 h12 h13
    ⟨hret, fun R' M' sp' h1 h2 hr2 hout => hoom R' M' sp' (by omega) (by omega) hr2
      fun a ha hf => by
        rw [hout a ha (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
        exact houtM a ha hf⟩

/-! ## Sizes of the intermediate numbers -/

/-- A normalized number has no more digits than its magnitude needs. -/
theorem NumRep.size_le {o : NumRep} (hs : NumShape o) (hn : o.Norm) {E : Nat}
    (hE : o.num.mag < 10 ^ E) : o.len + o.scale ≤ max E (1 + o.scale) := by
  rcases hn with hl | h0
  · omega
  · rcases Nat.lt_or_ge o.len 2 with hl | hl
    · omega
    have hlen : 1 ≤ o.ds.length := by rw [hs.dsLen]; omega
    have h1 := Dc.BcModel.dvalBE_ge_of_first hlen (Nat.pos_of_ne_zero h0)
    rw [hs.dsLen] at h1
    have h2 : 10 ^ (o.len + o.scale - 1) < 10 ^ E := Nat.lt_of_le_of_lt h1 hE
    have := (Nat.pow_lt_pow_iff_right (by omega)).mp h2
    omega

/-- `Num.mul`'s magnitude is at most the product of the magnitudes. -/
theorem Num.mul_mag_le (a b : Num) (k : Nat) : (Num.mul a b k).mag ≤ a.mag * b.mag :=
  Nat.div_le_self _ _

/-- `Num.mul`'s scale is at most the sum of the scales. -/
theorem Num.mul_scale_le (a b : Num) (k : Nat) : (Num.mul a b k).scale ≤ a.scale + b.scale :=
  Nat.min_le_left _ _

/-- The product of `bc_divmod` has at most the operands' digits and one. -/
theorem mul_size_le {o1 o2 o : NumRep} (h1 : NumShape o1) (h2 : NumShape o2) (hs : NumShape o)
    (hn : o.Norm) {k : Nat} (ho : o.num = Num.mul o1.num o2.num k) :
    o.len + o.scale ≤ o1.len + o1.scale + (o2.len + o2.scale) + 1 := by
  have m1 := NumRep.mag_lt h1; have m2 := NumRep.mag_lt h2
  have hm : o.num.mag < 10 ^ (o1.len + o1.scale + (o2.len + o2.scale)) := by
    rw [ho, Nat.pow_add]
    exact Nat.lt_of_le_of_lt (Num.mul_mag_le _ _ _) (Nat.mul_lt_mul'' m1 m2)
  have hsc : o.scale ≤ o1.scale + o2.scale := by
    have := Num.mul_scale_le o1.num o2.num k; rw [← ho] at this; exact this
  have := NumRep.size_le hs hn hm
  omega

/-- A second reference on a number with one: dropped again, it is the same
number. -/
theorem NumObj.withRefs2_decRef {y : NumObj} (h : y.rep.refs = 1) : (y.withRefs 2).decRef = y := by
  show { y with rep := { y.rep with refs := 2 - 1 } } = y
  rw [show 2 - 1 = y.rep.refs by omega]

/-- **`quotient = bc_copy_num (temp); bc_multiply (temp, num2, &temp,
rscale)`** from `0x80006070` (quotient path). -/
theorem dm_qmul {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W qq qr rs : Nat} {L : List NumObj}
    {xq xr x1 x2 z yq : NumObj} {H : Heap} {F : List Blk} {n : Option (Num × Num)}
    {a b : Num}
    (cx : DmCtx S R0 sp W) (sl : DmQSlots S Mt0 L xq xr qq qr sp W)
    (hk : DmKQ live S Q R0 Mt0 L xq xr qq qr sp W n) (hn : n = some (a, b))
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hb : BcHeap S M H F (yq :: L))
    (hown : ∀ y ∈ L, y.Owns) (hx1 : x1 ∈ L) (hn1 : x1.rep.Norm) (hl1 : 1 ≤ x1.rep.len)
    (hx2 : x2 ∈ L) (hp2 : 1 ≤ x2.rep.len + x2.rep.scale) (hz : z ∈ L)
    (hzk : KZero M z (2 ^ 30)) (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hyq : NewNum a yq) (hbv : Num.sub x1.rep.num (Num.mul a x2.rep.num rs) rs = b)
    (hsz : yq.rep.len + yq.rep.scale + 2 * (x2.rep.len + x2.rep.scale) + x1.rep.len +
      x1.rep.scale + rs < 2 ^ 27)
    (hslot : ldv .ld M (sp - 80 + 8) = BitVec.ofNat 64 yq.sb.pay)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h9 : R 9 = BitVec.ofNat 64 x2.rep.p)
    (h18 : R 18 = BitVec.ofNat 64 rs)
    (h19 : R 19 = BitVec.ofNat 64 qq) (h20 : R 20 = BitVec.ofNat 64 yq.sb.pay)
    (h21 : R 21 = BitVec.ofNat 64 qr) :
    DW live S Q 0x80006070#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hyp : yq.rep.p = yq.sb.pay := (hb.blocks yq List.mem_cons_self).sPay
  have hyn := hb.nums yq List.mem_cons_self
  num_facts hyn
  have hrf := hyn.refs
  rw [hyq.refs] at hrf
  have h20' : R 20 = BitVec.ofNat 64 yq.rep.p := by rw [h20, hyp]
  have hb0 : BcHeap S M H F ([] ++ yq :: L) := hb
  have hx2n := hb.nums x2 (List.mem_cons_of_mem _ hx2)
  num_facts hx2n
  have hstk : ∀ a, sp - 80 ≤ a → OutHeap a := fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have e2 : BitVec.signExtend 64 (BitVec.extractLsb 31 0 2#64) = 2#64 := by decide
  bc_run hlive hS [h2, h20', hrf, h9, h18, e2] at 0x8000573c
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  have hb1 := hb0.setRefs (k := 2) (v := BitVec.signExtend 64 (BitVec.extractLsb 31 0 2#64))
    (by decide) (by decide)
  have hun1 : ∀ a, OutHeap a → imgM (writeLog M [(yq.rep.p + 12, 4,
      BitVec.signExtend 64 (BitVec.extractLsb 31 0 2#64))]) a = imgM M a :=
    fun a ha => imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  refine dm_mulCall (x1 := yq.withRefs 2) (x2 := x2) (z := z) (k := rs) hlive cx hk.oom
    (fun a ha hf => (hun1 a ha).trans (houtM a ha hf))
    ⟨List.mem_cons_self, List.mem_cons_of_mem _ hx2, List.mem_cons_of_mem _ hz,
      by simp only [NumObj.withRefs]; have := hyq.pos; omega, hp2,
      by simp only [NumObj.withRefs]; omega, by omega,
      { hzk with
        glob := by
          rw [ldv_congr .ld fun j hj => hun1 _ (constBytes_out (by
            simp only [constBytes, twoAddr, zeroAddr, widthOfM] at hj ⊢; omega))]
          exact hzk.glob
        room := by simp only [NumObj.withRefs]; have := hzk.room; omega },
      by rw [ldv_congr .lw fun j hj => hun1 _ (by
          simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, mulBaseAddr,
            widthOfM] at hj ⊢; omega)]; exact hmb⟩
    hb1 ⟨by simp only [NumObj.withRefs]; omega, by
      rw [ldv_congr .ld fun j hj => hun1 _ (hstk _ (by omega))]
      simp only [NumObj.withRefs]; rw [hslot, hyp], fun _ _ z hz => absurd hz List.not_mem_nil⟩
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp [h20']; rfl) (by bsimp [h9])
    (by bsimp [h2]) (by bsimp [h18]) ?_
  intro R' M' H' F' Lr ym hk' hp
  bsimp []
  have hLr : Lr = yq :: L := by
    cases hp.rest with
    | dec h => exact congrArg (· :: L) (NumObj.withRefs2_decRef hyq.refs)
    | rel h => simp only [NumObj.withRefs] at h; omega
  subst hLr
  have hpo := hp.out
  have hun : ∀ a, OutHeap a → ¬ slotBytes (sp - 80 + 8) a → ¬ frameIn (sp - 80) (W - 80) a →
      imgM M' a = imgM (writeLog M [(yq.rep.p + 12, 4,
        BitVec.signExtend 64 (BitVec.extractLsb 31 0 2#64))]) a := hpo
  have hun' : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M' a = imgM Mt0 a := fun a ha hf => by
    rw [hun a ha (by simp only [slotBytes, frameIn] at hf ⊢; omega)
      (by simp only [frameIn] at hf ⊢; omega), hun1 a ha]
    exact houtM a ha hf
  have hbm := hp.heap
  have hymn := hbm.nums ym List.mem_cons_self
  have hyqn := hbm.nums yq (List.mem_cons_of_mem _ List.mem_cons_self)
  have hx1n := hbm.nums x1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx1))
  num_facts hx1n
  have hmz := mul_size_le hyqn.shape hx2n.shape hymn.shape hp.norm (k := rs) hp.num
  have hsx := hyqn.shape.size
  refine dm_qsub hlive cx sl hk hn
    (sv.transport (lo := 24) (top := 80) (hag := fun a h1 h2' => by
      rw [hun a (hstk a (by omega)) (by simp only [slotBytes]; omega)
        (by simp only [frameIn]; omega), hun1 a (hstk a (by omega))]))
    (by rw [hk'.get 2]; bsimp [h2]) ((hk'.mono (by decide)).trans (by keeps_tac hkp)) hbm
    hown hx1 hn1 hl1 ⟨rfl, hp.norm, hp.pos, hp.refs, hp.owns⟩ hyq
    (by rw [hp.num, show (yq.withRefs 2).rep.num = a from hyq.num]; exact hbv) (by omega)
    hp.slot hun'
    (by rw [hk'.get 8]; bsimp [h8]) (by rw [hk'.get 18]; bsimp [h18])
    (by rw [hk'.get 19]; bsimp [h19]) (by rw [hk'.get 20]; bsimp [h20])
    (by rw [hk'.get 21]; bsimp [h21])

/-! ## Without the quotient (`bc_modulo`) -/

/-- The remainder returned from `0x800060e0` (`a0 = 0`, the epilogue). -/
theorem dm_rend {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W qr : Nat} {L Lf : List NumObj}
    {xr yr : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {b : Num}
    (cx : DmCtx S R0 sp W) (hk : DmKR live S Q R0 Mt0 L xr qr sp W n) (hn : n = some b)
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hp : DmPostR S Mt0 M H F L xr qr sp W b Lf yr) :
    DW live S Q 0x800060e0#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hp.heap.heap.own a h1 h2
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [] at 0x800060e4
  exact dm_epi hlive cx hS sv (by bsimp [h2]) (by keeps_tac hkp) fun R' hk' h10 =>
    hk.ret _ hn R' M H F Lf yr hk' (by rw [h10]; bsimp []) hp

/-- After the inlined free of `temp` (no quotient): the product released. -/
theorem dm_rafter {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp W qr : Nat} {L Lm L' : List NumObj}
    {xr yr ym : NumObj} {H H' : Heap} {F F' : List Blk} {n : Option Num} {b : Num}
    (cx : DmCtx S R0 sp W) (sr : DmSlot S sp W qr) (hk : DmKR live S Q R0 Mt0 L xr qr sp W n)
    (hn : n = some b)
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hm1 : ym.rep.refs = 1)
    (hkf : KFreed H F [yr] Lm ym H' F' L') (hb : BcHeap S M' H' F' L')
    (hof : OutFrame (fun _ => False) M' M) (hR : Keeps [1, 10, 14, 15, 20] R' R)
    (hmid : DropAt L xr.rep.p Lm) (hyr : ResNum M qr b yr)
    (hout : ∀ a, OutHeap a → ¬ slotBytes qr a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    DW live S Q 0x800060e0#64 R' M' := by
  cases hkf with
  | dec h => omega
  | rel _ =>
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have hun : ∀ a, OutHeap a → imgM M' a = imgM M a := fun a ha => hof a ha id
  have hstk : ∀ a, sp - 80 ≤ a → OutHeap a := fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hsr := hyr.slot
  have hsr1 : ldv .ld M' qr = BitVec.ofNat 64 yr.sb.pay := by
    rw [ldv_congr .ld fun j hj => hun _ (sr.out _ ⟨by omega, by
      simp only [widthOfM] at hj; omega⟩)]; exact hsr
  exact dm_rend hlive cx hk hn
    (sv.transport (lo := 24) (top := 80) (hag := fun a h1 h2' => hun a (hstk a (by omega))))
    (by rw [hR.get 2]; exact h2) ((hR.mono (by decide)).trans hkp)
    ⟨hb, hmid, { hyr with slot := hsr1 }, fun a ha hs hf => (hun a ha).trans (hout a ha hs hf)⟩

/-- `bnez s3` at `0x800060dc` without a quotient slot. -/
theorem dm_r60dc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} (hS : HeapOwn S) (h19 : R 19 = 0#64)
    (hk : DW live S Q 0x800060e0#64 R M) : DW live S Q 0x800060dc#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h19] at 0x800060e0
  all_goals first | exact hk | (intro hc; exact absurd rfl hc) | skip

/-- **The free of `temp`** at `0x80006168` (no quotient): the product, one
reference, released. -/
theorem dm_rsite {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W qr : Nat} {L Lm : List NumObj}
    {xr yr ym : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {b : Num}
    (cx : DmCtx S R0 sp W) (sr : DmSlot S sp W qr) (hk : DmKR live S Q R0 Mt0 L xr qr sp W n)
    (hn : n = some b)
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hb : BcHeap S M H F (yr :: ym :: Lm))
    (hm1 : ym.rep.refs = 1) (hmo : ym.Owns)
    (hmid : DropAt L xr.rep.p Lm) (hyr : ResNum M qr b yr)
    (hout : ∀ a, OutHeap a → ¬ slotBytes qr a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h9 : R 9 = BitVec.ofNat 64 ym.rep.p) (h19 : R 19 = 0#64) :
    DW live S Q 0x80006168#64 R M := by
  have hb' : BcHeap S M H F ([yr] ++ ym :: Lm) := hb
  refine ffree_80006168 (fr := fun _ => False) hlive hb' (by omega)
    (fun _ hxo y hy => hb'.owner_db_ne hxo hy (by
      rcases List.mem_singleton.mp hy with rfl; exact hyr.owns)) h9
    (fun R' M' H' F' L' hR hkf hb1 hof => ?_) (fun R' M' H' F' L' hR hkf hb1 hof => ?_)
    (fun R' M' H' F' L' hR hkf hb1 hof => ?_)
  · exact dm_rafter hlive cx sr hk hn sv h2 hkp hm1 hkf hb1 hof hR hmid hyr hout
  · exact dm_r60dc hlive (fun a h1 h2 => hb1.heap.own a h1 h2) (by rw [hR.get 19]; exact h19)
      (dm_rafter hlive cx sr hk hn sv h2 hkp hm1 hkf hb1 hof hR hmid hyr hout)
  · exact dm_rafter hlive cx sr hk hn sv h2 hkp hm1 hkf hb1 hof hR hmid hyr hout

/-- **`bc_sub (num1, temp, rem, rscale)`** from `0x80006150` (no
quotient): the remainder, then the free of `temp`. -/
theorem dm_rsub {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W qr rs : Nat} {L : List NumObj}
    {xr x1 ym : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {b c : Num}
    (cx : DmCtx S R0 sp W) (sr : DmSlot S sp W qr) (hmr : xr ∈ L) (hrr : 1 ≤ xr.rep.refs)
    (hwr0 : ldv .ld Mt0 qr = BitVec.ofNat 64 xr.rep.p)
    (hk : DmKR live S Q R0 Mt0 L xr qr sp W n) (hn : n = some b)
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hb : BcHeap S M H F (ym :: L))
    (hown : ∀ y ∈ L, y.Owns) (hx1 : x1 ∈ L) (hn1 : x1.rep.Norm) (hl1 : 1 ≤ x1.rep.len)
    (hym : NewNum c ym) (hbv : Num.sub x1.rep.num c rs = b)
    (hsz : ym.rep.len + ym.rep.scale + x1.rep.len + x1.rep.scale + rs < 2 ^ 30)
    (hslot : ldv .ld M (sp - 80 + 8) = BitVec.ofNat 64 ym.sb.pay)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h18 : R 18 = BitVec.ofNat 64 rs)
    (h19 : R 19 = 0#64) (h21 : R 21 = BitVec.ofNat 64 qr) :
    DW live S Q 0x80006150#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hapr := sr.apart
  have hrh := sr.slot.hi
  obtain ⟨A0, B0, rfl⟩ := List.append_of_mem hmr
  have hb' : BcHeap S M H F ((ym :: A0) ++ xr :: B0) := hb
  have hymp : ym.rep.p = ym.sb.pay := (hb.blocks ym List.mem_cons_self).sPay
  have hymn := hb.nums ym List.mem_cons_self
  num_facts hymn
  have hx1n := hb.nums x1 (List.mem_cons_of_mem _ hx1)
  num_facts hx1n
  have hstk : ∀ a, sp - 80 ≤ a → OutHeap a := fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hwr : ldv .ld M qr = BitVec.ofNat 64 xr.rep.p := by
    rw [ldv_congr .ld fun j hj => houtM _ (sr.out _ ⟨by omega, by
      simp only [widthOfM] at hj; omega⟩) (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact hwr0
  have hl1' := hym.pos
  have hnvr : xr.rep.refs = 1 → xr.Owns → ∀ z ∈ ym :: A0, z.db ≠ xr.db := fun _ hxo z hz =>
    hb'.owner_db_ne hxo hz (by
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hym.owns
      exact hown z (List.mem_append_left _ hz))
  bc_run hlive hS [h2, hslot, h18, h21, h8] at 0x80004ac4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dm_subCall (x1 := x1) (x2 := ym) (smin := rs) hlive cx sr hk.oom houtM
    ⟨List.mem_cons_of_mem _ hx1, List.mem_cons_self, hn1, hym.norm,
      by omega, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    (fun _ => ⟨hl1, hl1'⟩) hb' ⟨hrr, hwr, hnvr⟩ (by bsimp [h2]) (by bsimp []; try decide)
    (by bsimp [h8]) (by bsimp [hymp]) (by bsimp [h21]) (by bsimp [h18]) ?_
  intro R' M' H' F' Lr y hk' hp
  bsimp []
  have ⟨Lm, hLr, hfr⟩ : ∃ Lm, Lr = ym :: Lm ∧ FreedRest A0 B0 xr Lm := by
    cases hp.rest with
    | dec h => exact ⟨_, rfl, .dec h⟩
    | rel h => exact ⟨_, rfl, .rel h⟩
  subst hLr
  have hpo := hp.out
  have hun : ∀ a, OutHeap a → ¬ slotBytes qr a → ¬ frameIn (sp - 80) 176 a →
      imgM M' a = imgM M a := hpo
  have hc := hym.num
  exact dm_rsite hlive cx sr hk hn
    (sv.transport (lo := 24) (top := 80) (hag := fun a h1 h2' => hun a (hstk a (by omega))
      (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)))
    (by rw [hk'.get 2]; bsimp [h2]) ((hk'.mono (by decide)).trans (by keeps_tac hkp)) hp.heap
    hym.refs hym.owns ⟨A0, B0, xr, rfl, rfl, hfr⟩
    ⟨⟨by rw [hp.num, NumRep.num_eq ym.rep, ← NumRep.num_eq, hc, hbv], hp.norm, hp.pos,
      hp.refs, hp.owns⟩, hp.slot⟩
    (fun a ha hs hf => by
      rw [hun a ha hs (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
      exact houtM a ha hf)
    (by rw [hk'.get 9]; bsimp [hymp]) (by rw [hk'.get 19]; bsimp [h19])

/-- **`bc_multiply (temp, num2, &temp, rscale)`** from `0x8000613c` (no
quotient: `temp` released by the call). -/
theorem dm_rmul {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W qr rs : Nat} {L : List NumObj}
    {xr x1 x2 z yq : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {a b : Num}
    (cx : DmCtx S R0 sp W) (sr : DmSlot S sp W qr) (hmr : xr ∈ L) (hrr : 1 ≤ xr.rep.refs)
    (hwr0 : ldv .ld Mt0 qr = BitVec.ofNat 64 xr.rep.p)
    (hk : DmKR live S Q R0 Mt0 L xr qr sp W n) (hn : n = some b)
    (sv : SavedWords M (sp - 80) dmSlots R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 80))
    (hkp : Keeps dmAll R R0) (hb : BcHeap S M H F (yq :: L))
    (hown : ∀ y ∈ L, y.Owns) (hx1 : x1 ∈ L) (hn1 : x1.rep.Norm) (hl1 : 1 ≤ x1.rep.len)
    (hx2 : x2 ∈ L) (hp2 : 1 ≤ x2.rep.len + x2.rep.scale) (hz : z ∈ L)
    (hzk : KZero M z (2 ^ 30)) (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hyq : NewNum a yq) (hbv : Num.sub x1.rep.num (Num.mul a x2.rep.num rs) rs = b)
    (hsz : yq.rep.len + yq.rep.scale + 2 * (x2.rep.len + x2.rep.scale) + x1.rep.len +
      x1.rep.scale + rs < 2 ^ 27)
    (hslot : ldv .ld M (sp - 80 + 8) = BitVec.ofNat 64 yq.sb.pay)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h8 : R 8 = BitVec.ofNat 64 x1.rep.p) (h9 : R 9 = BitVec.ofNat 64 x2.rep.p)
    (h18 : R 18 = BitVec.ofNat 64 rs) (h19 : R 19 = 0#64)
    (h20 : R 20 = BitVec.ofNat 64 yq.sb.pay) (h21 : R 21 = BitVec.ofNat 64 qr) :
    DW live S Q 0x8000613c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hyp : yq.rep.p = yq.sb.pay := (hb.blocks yq List.mem_cons_self).sPay
  have hyn := hb.nums yq List.mem_cons_self
  num_facts hyn
  have h20' : R 20 = BitVec.ofNat 64 yq.rep.p := by rw [h20, hyp]
  have hb0 : BcHeap S M H F ([] ++ yq :: L) := hb
  have hx2n := hb.nums x2 (List.mem_cons_of_mem _ hx2)
  num_facts hx2n
  have hstk : ∀ a, sp - 80 ≤ a → OutHeap a := fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  bc_run hlive hS [h2, h20', h9, h18] at 0x8000573c
  refine dm_mulCall (x1 := yq) (x2 := x2) (z := z) (k := rs) hlive cx hk.oom houtM
    ⟨List.mem_cons_self, List.mem_cons_of_mem _ hx2, List.mem_cons_of_mem _ hz,
      by have := hyq.pos; omega, hp2, by omega, by omega,
      { hzk with room := by have := hzk.room; omega }, hmb⟩
    hb0 ⟨by rw [hyq.refs]; omega, by rw [hslot, hyp], fun _ _ z hz => absurd hz List.not_mem_nil⟩
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp [h20']) (by bsimp [h9])
    (by bsimp [h2]) (by bsimp [h18]) ?_
  intro R' M' H' F' Lr ym hk' hp
  bsimp []
  have hLr : Lr = L := by
    cases hp.rest with
    | dec h => rw [hyq.refs] at h; omega
    | rel h => rfl
  subst hLr
  have hpo := hp.out
  have hun : ∀ a, OutHeap a → ¬ slotBytes (sp - 80 + 8) a → ¬ frameIn (sp - 80) (W - 80) a →
      imgM M' a = imgM M a := hpo
  have hun' : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M' a = imgM Mt0 a := fun a ha hf => by
    rw [hun a ha (by simp only [slotBytes, frameIn] at hf ⊢; omega)
      (by simp only [frameIn] at hf ⊢; omega)]
    exact houtM a ha hf
  have hbm := hp.heap
  have hymn := hbm.nums ym List.mem_cons_self
  have hx1n := hbm.nums x1 (List.mem_cons_of_mem _ hx1)
  num_facts hx1n
  have hmz := mul_size_le hyn.shape hx2n.shape hymn.shape hp.norm (k := rs) hp.num
  have hsx := hyn.shape.size
  exact dm_rsub hlive cx sr hmr hrr hwr0 hk hn
    (sv.transport (lo := 24) (top := 80) (hag := fun a h1 h2' => by
      rw [hun a (hstk a (by omega)) (by simp only [slotBytes]; omega)
        (by simp only [frameIn]; omega)]))
    (by rw [hk'.get 2]; bsimp [h2]) ((hk'.mono (by decide)).trans (by keeps_tac hkp)) hbm
    hown hx1 hn1 hl1 ⟨rfl, hp.norm, hp.pos, hp.refs, hp.owns⟩
    (by rw [hp.num, hyq.num]; exact hbv) (by omega) hp.slot hun'
    (by rw [hk'.get 8]; bsimp [h8]) (by rw [hk'.get 18]; bsimp [h18])
    (by rw [hk'.get 19]; bsimp [h19]) (by rw [hk'.get 21]; bsimp [h21])

/-- The quotient of `bc_divmod` has at most the dividend's digits, the
divisor's scale and `k`, and one. -/
theorem div_size_le {o1 o2 o : NumRep} (h1 : NumShape o1) (hs : NumShape o) (hn : o.Norm)
    {k : Nat} {q : Num} (hd : Num.div o1.num o2.num k = some q) (ho : o.num = q) :
    o.len + o.scale ≤ o1.len + o1.scale + o2.scale + k + 1 := by
  have m1 := NumRep.mag_lt h1
  unfold Num.div at hd
  split at hd
  · exact absurd hd (by simp)
  rename_i h0
  simp only [Option.some.injEq] at hd
  subst hd
  have hsc : o.scale = k := by have := congrArg Num.scale ho; exact this
  have hm : o.num.mag < 10 ^ (o1.len + o1.scale + (o2.scale + k)) := by
    rw [ho, Nat.pow_add, NumRep.num_mag, NumRep.num_scale, ← Nat.pow_add]
    refine Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ?_
    have hp : 0 < 10 ^ (o2.scale + k) := Nat.pos_of_ne_zero (by simp)
    rw [Nat.pow_add 10 (o1.len + o1.scale)]
    exact Nat.mul_lt_mul_of_pos_right m1 hp
  have := NumRep.size_le hs hn hm
  omega

end Dc.Mach
