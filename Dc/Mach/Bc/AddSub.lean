import Dc.Mach.Bc.DoSub
import Dc.Mach.Bc.Compare

/-!
# `bc_add` and `bc_sub`: the shared context, result and tail

`bc_add(n1, n2, result, scale_min)` and `bc_sub(…)` dispatch on the signs and
`_bc_do_compare` to `_bc_do_add` or `_bc_do_sub` (or a zero from
`bc_new_num`), set the sign of the new number, free `*result` and store the
new number there. This file holds what both share:

- `BinCtx`: the 176-byte stack window (48 for the frame, 128 for
  `_bc_do_sub`'s), the result slot `q` off the heap and the window.
- `BinArgs`: two normalized numbers of the heap and the size bound.
- `BinPost`/`BinK`: the new number `y` for the `Dc.Num` value `n` heads the
  heap left by freeing the slot's old number `x`; the slot holds `y`.
- `FreeEntry.of_slot`: the entry facts of `bc_free_num` for the slot after the
  new number joined the heap; `binPost_dec`/`binPost_rel` assemble `BinPost`
  after `bc_free_num` and the store of `y` in the slot.
- `RepNum`: the value lemmas of `Dc/BcModel/Add.lean` restated on `NumRep.num`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- The registers `bc_add` and `bc_sub` may change. -/
abbrev binClob : List Nat := [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- `bc_add`/`bc_sub`'s fixed context: the 48-byte frame and the 128 bytes of
`_bc_do_sub` below it, above the heap; the result slot `q` off the heap and
apart from the window; the entry's `sp` and return address. -/
structure BinCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp q : Nat) : Prop where
  frame : StackFrame S sp 176
  above : heapEnd + 176 ≤ sp
  slot : PtrSlot S q
  slotOut : ∀ a, slotBytes q a → OutHeap a
  slotApart : q + 8 ≤ sp - 176 ∨ sp ≤ q
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0

/-- The operands: two normalized numbers of the heap (possibly the same, or
the slot's), and the result's size in range. -/
structure BinArgs (L : List NumObj) (x1 x2 : NumObj) (smin : Nat) : Prop where
  m1 : x1 ∈ L
  m2 : x2 ∈ L
  n1 : x1.rep.Norm
  n2 : x2.rep.Norm
  size : max x1.rep.len x2.rep.len + 1 + max smin (max x1.rep.scale x2.rep.scale) < 2 ^ 31
  /-- an operand without integer digits is compared against a nonzero one:
  what `_bc_do_compare`'s length test needs to be correct -/
  e1 : x1.rep.len = 0 → 0 < dval x2.rep.ds
  e2 : x2.rep.len = 0 → 0 < dval x1.rep.ds

/-- The result slot `q` holds the number `x` (`L = L1 ++ x :: L2`); no view
before it reads an owner's buffer. -/
structure ResSlot (Mt : Mem) (L1 : List NumObj) (x : NumObj) (q : Nat) : Prop where
  refs : 1 ≤ x.rep.refs
  word : ldv .ld Mt q = BitVec.ofNat 64 x.rep.p
  noView : x.rep.refs = 1 → x.Owns → ∀ z ∈ L1, z.db ≠ x.db

/-- The result: the new number `y` for `n` (normalized, one reference) heads
the heap left by freeing `x`, its struct is in the slot, and off the heap only
the slot and the stack window changed. -/
structure BinPost (S : Nat → Prop) (Mt0 Mt : Mem) (H : Heap) (F : List Blk)
    (L1 L2 : List NumObj) (x : NumObj) (q sp : Nat) (n : Num) (L : List NumObj) (y : NumObj) :
    Prop where
  heap : BcHeap S Mt H F (y :: L)
  rest : FreedRest L1 L2 x L
  num : y.rep.num = n
  norm : y.rep.Norm
  refs : y.rep.refs = 1
  owns : y.Owns
  slot : ldv .ld Mt q = BitVec.ofNat 64 y.sb.pay
  out : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 176 a → imgM Mt a = imgM Mt0 a

/-- The continuations: the result, or `out_of_memory` with `sp` inside the
window. -/
structure BinK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (L1 L2 : List NumObj) (x : NumObj) (q sp : Nat) (n : Num) :
    Prop where
  ret : ∀ R' Mt' H F L y, Keeps binClob R' R0 → BinPost S Mt0 Mt' H F L1 L2 x q sp n L y →
    DW live S Q (R0 1) R' Mt'
  oom : ∀ R' Mt' sp', sp - 176 ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
    (∀ a, OutHeap a → ¬ frameIn sp 176 a → imgM Mt' a = imgM Mt0 a) →
    DW live S Q 0x80002bcc#64 R' Mt'

/-- `bc_free_num`'s entry facts for the slot `q` holding `x` of the heap. -/
theorem FreeEntry.of_slot {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L0 L1 L2 : List NumObj} {x : NumObj} {q sp : Nat} (h : BcHeap S Mt H F (L1 ++ x :: L2))
    (hr : ResSlot Mt L0 x q) (hnv : x.rep.refs = 1 → x.Owns → ∀ z ∈ L1, z.db ≠ x.db) (hq : PtrSlot S q)
    (hout : ∀ a, slotBytes q a → OutHeap a)
    (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp) (hap : q + 8 ≤ sp - 32 ∨ sp ≤ q) :
    FreeEntry S Mt H F L1 L2 x q sp := by
  have hq0 := hout q ⟨Nat.le_refl _, by omega⟩
  have hq7 := hout (q + 7) ⟨by omega, by omega⟩
  refine ⟨h, hr.refs, hq, ⟨fun a ha => OutHeap.not_alloc h.heap (hout a ha),
    fun b hb a ha hba => ?_, ?_, hap⟩, hr.word, hsf, hab, hnv⟩
  · have hbl : b ∈ H.live := by
      rcases List.mem_append.mp hb with hb | hb
      · exact (h.deadLive b hb).1
      · obtain ⟨y, hy, hby⟩ := List.mem_flatMap.mp hb
        have hyb := h.blocks y hy
        unfold NumObj.blocks at hby
        split at hby <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hby
        · subst hby; exact hyb.sLive
        · rcases hby with rfl | rfl
          · exact hyb.sLive
          · exact hyb.dLive
    exact (hout a ha).1 (live_in_heap h.heap hbl hba)
  · simp only [OutHeap] at hq0 hq7
    omega

/-- With an owner `y` heading the heap, the slot's object has no view before
it in `y :: L1`. -/
theorem ResSlot.noView_cons {S : Nat → Prop} {Mt M : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x y : NumObj} {q : Nat} (hb : BcHeap S M H F (y :: (L1 ++ x :: L2)))
    (hyo : y.Owns) (hr : ResSlot Mt L1 x q) :
    x.rep.refs = 1 → x.Owns → ∀ z ∈ y :: L1, z.db ≠ x.db := by
  intro hx1 hxo z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · have hd := hb.distinct
    rw [objBlocks_cons, NumObj.blocks_own hyo] at hd
    intro e
    have hxm : z.db ∈ objBlocks (L1 ++ x :: L2) :=
      e ▸ mem_objBlocks_db (List.mem_append_right _ List.mem_cons_self) hxo
    exact (List.nodup_append.mp (List.nodup_append.mp hd).2.1).2.2 z.db (by simp) z.db hxm rfl
  · exact hr.noView hx1 hxo z hz

/-- After `bc_free_num` dropped one reference: the slot written with `y`. -/
theorem binPost_dec {S : Nat → Prop} {Mt0 M Mt' : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x y : NumObj} {q sp : Nat} {n : Num}
    (hout : ∀ a, slotBytes q a → OutHeap a)
    (hm : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 176 a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S Mt' H F (y :: (L1 ++ x.decRef :: L2)))
    (hmo : MemOnly (fun a => refsBytes x.rep a ∨ slotBytes q a) Mt' M)
    (hxp : heapStart ≤ x.rep.p ∧ x.rep.p + 16 ≤ heapEnd)
    (hnum : y.rep.num = n) (hnorm : y.rep.Norm) (hrefs : y.rep.refs = 1) (hyo : y.Owns)
    (hx2 : 2 ≤ x.rep.refs) :
    BinPost S Mt0 (writeLog Mt' [(q, 8, BitVec.ofNat 64 y.sb.pay)]) H F L1 L2 x q sp n
      (L1 ++ x.decRef :: L2) y :=
  { heap := hb.out_frame (P := slotBytes q) (fun a ha => imgM_store_miss _ _ (by
      simp only [slotBytes] at ha; omega)) hout
    rest := .dec hx2
    num := hnum
    norm := hnorm
    refs := hrefs
    owns := hyo
    slot := ldv_store_hit _ _ _
    out := fun a ha hs hf => by
      rw [imgM_store_miss _ _ (by simp only [slotBytes] at hs; omega), hmo a fun hc => ?_]
      · exact hm a ha hs hf
      · rcases hc with hc | hc
        · simp only [refsBytes, OutHeap, heapStart, heapEnd] at hc ha hxp; omega
        · exact hs hc }

/-- After `bc_free_num` released the last reference: the slot written with `y`. -/
theorem binPost_rel {S : Nat → Prop} {Mt0 M Mt' : Mem} {H H' : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x y : NumObj} {q sp : Nat} {n : Num}
    (hout : ∀ a, slotBytes q a → OutHeap a)
    (hm : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 176 a → imgM M a = imgM Mt0 a)
    (hb0 : BcHeap S M H F (y :: (L1 ++ x :: L2)))
    (hrp : ReleasePost S M Mt' H H' F (y :: L1) L2 x q (sp - 48))
    (hsp : heapEnd + 176 ≤ sp)
    (hnum : y.rep.num = n) (hnorm : y.rep.Norm) (hrefs : y.rep.refs = 1) (hyo : y.Owns)
    (hx1 : x.rep.refs = 1) :
    BinPost S Mt0 (writeLog Mt' [(q, 8, BitVec.ofNat 64 y.sb.pay)]) H' (x.sb :: F) L1 L2 x q sp n
      (L1 ++ L2) y :=
  { heap := hrp.heap.out_frame (P := slotBytes q) (fun a ha => imgM_store_miss _ _ (by
      simp only [slotBytes] at ha; omega)) hout
    rest := .rel hx1
    num := hnum
    norm := hnorm
    refs := hrefs
    owns := hyo
    slot := ldv_store_hit _ _ _
    out := fun a ha hs hf => by
      have hxb := hb0.blocks x (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
      rw [imgM_store_miss _ _ (by simp only [slotBytes] at hs; omega), hrp.frame a fun hc => ?_]
      · exact hm a ha hs hf
      · rcases hc with hc | hc | hc | hc | hc
        · exact OutHeap.not_alloc hb0.heap ha hc
        · exact ha.1 (live_in_heap hb0.heap hxb.sLive hc)
        · exact hs hc
        · simp only [frameIn, OutHeap, heapStart, heapEnd] at hc hf ha hsp; omega
        · exact ha.2.2 hc }

/-! ## Values on `NumRep.num` -/

theorem dval_eq_dvalBE : dval = dvalBE := rfl

/-- A number's value from its parts. -/
theorem NumRep.num_eq (o : NumRep) : o.num = ⟨o.neg, dvalBE o.ds, o.scale⟩ := rfl

/-- A sign word's low 32 bits. -/
theorem signWord_toNat (b : Bool) : (signWord b).toNat % 2 ^ 32 = b.toNat := by
  cases b <;> decide

/-- Equal sign words, equal signs. -/
theorem signWord_inj {a b : Bool} (h : signWord a = signWord b) : a = b := by
  cases a <;> cases b <;> simp_all [signWord]

/-! ## Inside `bc_add`/`bc_sub` -/

/-- The registers changed inside `bc_add`/`bc_sub` before the epilogue. -/
abbrev binAll : List Nat := [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 28, 29, 30, 31]

/-- The scratch registers between the calls. -/
abbrev binTmp : List Nat := [1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 28, 29, 30, 31]

/-- Inside `bc_add`/`bc_sub`: `sp` lowered by 48, `ra`, `s0`, `s1` in the
frame, `s1` the slot, and off the heap only the stack window changed. -/
structure BinAt (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp q : Nat) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 48)
  saved : SavedWords M (sp - 48) [(1, 40), (9, 24), (8, 32)] R0
  r9 : R 9 = BitVec.ofNat 64 q
  regs : Keeps binAll R R0
  out : ∀ a, OutHeap a → ¬ frameIn sp 176 a → imgM M a = imgM Mt0 a

/-- `BinAt` through changes of the scratch registers. -/
theorem BinAt.keeps {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp q : Nat}
    (st : BinAt S Mt0 M R0 R sp q) (hk : Keeps binTmp R' R) : BinAt S Mt0 M R0 R' sp q :=
  { st with
    r2 := by rw [hk.get 2]; exact st.r2
    r9 := by rw [hk.get 9]; exact st.r9
    regs := (hk.mono (by decide)).trans st.regs }

/-- `BinAt` through a callee that changed only the heap and the window below
the frame. -/
theorem BinAt.call {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp q : Nat}
    (st : BinAt S Mt0 M R0 R sp q) (hab : heapEnd + 176 ≤ sp) (hk : Keeps binTmp R' R)
    (hm : ∀ a, OutHeap a → ¬ frameIn (sp - 48) 128 a → imgM M' a = imgM M a) :
    BinAt S Mt0 M' R0 R' sp q :=
  { st.keeps hk with
    saved := st.saved.transport (lo := 24) (top := 48) (hag := fun a h1 h2 => hm a (by
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hab ⊢; omega)
      (by simp only [frameIn]; omega))
    out := fun a ha hf => (hm a ha fun h => hf (by simp only [frameIn] at *; omega)).trans
      (st.out a ha hf) }

/-- `memset(val, 0, len + scale)` over a fresh number changes nothing it holds. -/
theorem BcHeap.zeroAgain {S : Nat → Prop} {M Mt' : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {y : NumObj} {len sc : Nat}
    (hb : BcHeap S M H F (y :: L)) (hy : y.rep = zeroRep y.sb.pay y.db.pay len sc)
    (hf : Filled Mt' M y.rep.val (len + sc) fun _ => 0#8) : BcHeap S Mt' H F (y :: L) := by
  have hn := hb.nums y List.mem_cons_self
  have hls : y.rep.len + y.rep.scale = len + sc := by rw [hy]; rfl
  have hall : ∀ a, imgM Mt' a = imgM M a := fun a => by
    by_cases h : y.rep.val ≤ a ∧ a < y.rep.val + (len + sc)
    · have e1 := hf.fill (a - y.rep.val) (by omega)
      have e2 := hn.digit (a - y.rep.val) (by omega)
      rw [show y.rep.val + (a - y.rep.val) = a by omega] at e1 e2
      rw [e1, e2, hy]
      simp only [zeroRep, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    · exact hf.rest a (by omega)
  exact hb.transport (fun a _ => hall a) (fun _ _ a _ => hall a) (fun j _ => hall _)

/-- The slot keeps its word while only the heap and the window change. -/
theorem ResSlot.of_out {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q : Nat}
    {L1 : List NumObj} {x : NumObj} (cx : BinCtx S R0 sp q) (st : BinAt S Mt0 M R0 R sp q)
    (h : ResSlot Mt0 L1 x q) : ResSlot M L1 x q := by
  have hap := cx.slotApart
  refine ⟨h.refs, ?_, h.noView⟩
  rw [ldv_congr .ld fun j hj => st.out _ (cx.slotOut _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩)
    (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
  exact h.word

/-- The number with another sign. -/
theorem NumRep.num_withNeg {o : NumRep} {b : Bool} {v s : Nat} (h : o.num = ⟨false, v, s⟩) :
    ({ o with neg := b } : NumRep).num = ⟨b, v, s⟩ := by
  have e1 : dval o.ds = v := congrArg Num.mag h
  have e2 : o.scale = s := congrArg Num.scale h
  show (⟨b, dval o.ds, o.scale⟩ : Num) = ⟨b, v, s⟩
  rw [e1, e2]

/-- `BinAt` through stores into the low half of the frame (`sp - 48` to
`sp - 24`, below the saved registers). -/
theorem BinAt.low {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp q : Nat}
    (st : BinAt S Mt0 M R0 R sp q) (hk : Keeps binTmp R' R)
    (hm : MemOnly (fun a => sp - 48 ≤ a ∧ a < sp - 24) M' M) : BinAt S Mt0 M' R0 R' sp q :=
  { st.keeps hk with
    saved := st.saved.transport (lo := 24) (top := 48) (hag := fun a h1 h2 => hm a (by omega))
    out := fun a ha hf => (hm a fun h => hf (by simp only [frameIn]; omega)).trans
      (st.out a ha hf) }

/-- `addi sp, sp, -48`. -/
theorem word_sub48 {x : Nat} (h : 48 ≤ x) :
    BitVec.ofNat 64 x + 18446744073709551568#64 = BitVec.ofNat 64 (x - 48) := by
  change BitVec.ofNat 64 x + -(48#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le x 48 (by decide) h

end Dc.Mach
