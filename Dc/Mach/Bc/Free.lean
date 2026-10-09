import Dc.Mach.Bc.HeapClosure
import Dc.Mach.Bc.Small

/-!
# `bc_free_num` (`lib/number.c`)

```
800048c0 ld a4,0(a0) ; 800048c4 beqz a4,80004944 ; 800048c8 lw a3,12(a4)
800048cc mv a5,a0 ; 800048d0 addiw a3,a3,-1 ; 800048d4 sw a3,12(a4)
800048d8 bnez a3,8000493c ; 800048dc ld a0,24(a4) ; 800048e0 beqz a0,80004924
800048e4 addi sp,sp,-32 ; 800048e8 sd ra,24(sp) ; 800048ec sd a5,8(sp)
800048f0 jal free ; 800048f4 ld a5,8(sp) ; 800048f8 auipc a3,0x18
800048fc ld a3,1208(a3) (_bc_Free_list) ; 80004900 ld ra,24(sp) ; 80004904 ld a4,0(a5)
80004908 sd a3,16(a4) ; 8000490c ld a4,0(a5) ; 80004910 sd zero,0(a5)
80004914 auipc a3,0x18 ; 80004918 sd a4,1180(a3) (_bc_Free_list) ; 8000491c addi sp,sp,32
80004920 ret ; 80004924 … (n_ptr == NULL) ; 8000493c sd zero,0(a5) ; 80004940 ret
80004944 ret
```

`bc_free_num(num)` drops one reference to `*num` and clears the slot. The
last reference frees the digit buffer (`n_ptr`; a view has none) and pushes
the struct on `_bc_Free_list`: the object leaves the number heap and its
struct joins the dead chain (`ReleasePost`). An owner is released only when
no view before it in the heap reads its buffer (`FreeEntry.noView`).

The slot may lie inside another live heap block (a `dc_list` node, a
register or array node): `SlotOff` only separates it from allocator bytes,
the number heap's blocks, `_bc_Free_list` and the callee frame.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The registers `bc_free_num` may change. -/
abbrev freeNumClob : List Nat := [10, 13, 14, 15]

/-- The object with one reference fewer. -/
def NumObj.decRef (x : NumObj) : NumObj := { x with rep := { x.rep with refs := x.rep.refs - 1 } }

/-- What freeing the old number left: `x` with one reference fewer, or gone. -/
inductive FreedRest (L1 L2 : List NumObj) (x : NumObj) : List NumObj → Prop
  | dec : 2 ≤ x.rep.refs → FreedRest L1 L2 x (L1 ++ x.decRef :: L2)
  | rel : x.rep.refs = 1 → FreedRest L1 L2 x (L1 ++ L2)

/-- The bytes of `_bc_Free_list`. -/
abbrev bcFreeBytes (a : Nat) : Prop := bcFreeAddr ≤ a ∧ a < bcFreeAddr + 8

/-- The eight bytes of the slot `q`. -/
abbrev slotBytes (q a : Nat) : Prop := q ≤ a ∧ a < q + 8

/-- The slot `q` is apart from the allocator's bytes, the number heap's blocks,
`_bc_Free_list` and `bc_free_num`'s 32-byte frame below `sp`. -/
structure SlotOff (H : Heap) (F : List Blk) (X : Raws) (L : List NumObj) (sp q : Nat) : Prop where
  alloc : ∀ a, slotBytes q a → ¬ AllocByte H a
  blocks : ∀ b ∈ F ++ objBlocks L, ∀ a, slotBytes q a → ¬ b.In a
  glob : q + 8 ≤ bcFreeAddr ∨ bcFreeAddr + 8 ≤ q
  frame : q + 8 ≤ sp - 32 ∨ sp ≤ q
  raw : ∀ b ∈ X.bs, ∀ a, slotBytes q a → ¬ b.In a

/-- The last reference released: the digit buffer is free, the struct heads
the dead chain, the object has left the number heap, and the slot is `NULL`.
Only allocator bytes, the struct, the slot, the frame and `_bc_Free_list`
change. -/
structure ReleasePost (S : Nat → Prop) (X : Raws) (Mt Mt' : Mem) (H H' : Heap) (F : List Blk)
    (L1 L2 : List NumObj) (x : NumObj) (q sp : Nat) : Prop where
  heap : BcHeap S X Mt' H' (x.sb :: F) (L1 ++ L2)
  /-- an owner's buffer is freed -/
  owned : x.Owns → H'.free = x.db :: H.free ∧ (∀ b, b ∈ H'.live ↔ b ∈ H.live ∧ b ≠ x.db) ∧
    H'.braw = H.braw
  /-- a view leaves the allocator alone -/
  view : ¬ x.Owns → H' = H
  slot : ldv .ld Mt' q = 0#64
  frame : MemOnly (fun a => AllocByte H a ∨ x.sb.In a ∨ slotBytes q a ∨ frameIn sp 32 a ∨
    bcFreeBytes a) Mt' Mt

/-- `bc_free_num`'s continuations for the object `x` (`L = L1 ++ x :: L2`)
in the slot: one reference fewer (`dec`), or released (`rel`). -/
structure FreeNumK (live S : Nat → Prop) (X : Raws) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt0 : Mem) (H0 : Heap) (F0 : List Blk) (L1 L2 : List NumObj)
    (x : NumObj) (q sp : Nat) : Prop where
  dec : 2 ≤ x.rep.refs → ∀ R' Mt', Keeps freeNumClob R' R0 →
    BcHeap S X Mt' H0 F0 (L1 ++ x.decRef :: L2) → ldv .ld Mt' q = 0#64 →
    MemOnly (fun a => refsBytes x.rep a ∨ slotBytes q a) Mt' Mt0 → DW live S Q (R0 1) R' Mt'
  rel : x.rep.refs = 1 → ∀ R' Mt' H', Keeps freeNumClob R' R0 →
    ReleasePost S X Mt0 Mt' H0 H' F0 L1 L2 x q sp → DW live S Q (R0 1) R' Mt'

/-! ## The number heap after `bc_free_num` -/

/-- The blocks of `L1 ++ x :: L2` are `x`'s and those of `L1 ++ L2`. -/
theorem objBlocks_perm (L1 L2 : List NumObj) (x : NumObj) :
    (objBlocks (L1 ++ x :: L2)).Perm (x.blocks ++ objBlocks (L1 ++ L2)) := by
  rw [objBlocks_append, objBlocks_cons, objBlocks_append]
  exact List.perm_append_comm_assoc _ _ _

/-- What the block uniqueness of `F ++ objBlocks (L1 ++ x :: L2)` says about
`x`; the facts about its buffer hold for an owner. -/
structure SplitFacts (F : List Blk) (L1 L2 : List NumObj) (x : NumObj) : Prop where
  sF : x.sb ∉ F
  sRest : x.sb ∉ objBlocks (L1 ++ L2)
  nodup : (F ++ objBlocks (L1 ++ L2)).Nodup
  disj : ∀ b ∈ F, ∀ c ∈ objBlocks (L1 ++ L2), b ≠ c
  sd : x.Owns → x.sb ≠ x.db
  dF : x.Owns → x.db ∉ F
  dRest : x.Owns → x.db ∉ objBlocks (L1 ++ L2)

theorem SplitFacts.of_nodup {F : List Blk} {L1 L2 : List NumObj} {x : NumObj}
    (h : (F ++ objBlocks (L1 ++ x :: L2)).Nodup) : SplitFacts F L1 L2 x := by
  have hp : (F ++ objBlocks (L1 ++ x :: L2)).Perm (x.blocks ++ (F ++ objBlocks (L1 ++ L2))) :=
    ((objBlocks_perm L1 L2 x).append_left F).trans (List.perm_append_comm_assoc _ _ _)
  have hn := hp.nodup_iff.mp h
  obtain ⟨hx, hn, hc⟩ := List.nodup_append.mp hn
  have hs : x.sb ∉ F ++ objBlocks (L1 ++ L2) := fun hb => hc x.sb x.sb_mem_blocks x.sb hb rfl
  have hdm : x.Owns → x.db ∈ x.blocks := fun ho => by rw [NumObj.blocks_own ho]; simp
  refine ⟨fun hb => hs (List.mem_append_left _ hb), fun hb => hs (List.mem_append_right _ hb), hn,
    fun b hb c hc' e => ?_, fun ho e => ?_, fun ho hb => hc _ (hdm ho) _ (List.mem_append_left _ hb) rfl,
    fun ho hb => hc _ (hdm ho) _ (List.mem_append_right _ hb) rfl⟩
  · subst e
    exact (List.nodup_append.mp hn).2.2 b hb b hc' rfl
  · rw [NumObj.blocks_own ho] at hx
    exact (List.nodup_cons.mp hx).1 (by rw [e]; simp)

theorem mem_split {L1 L2 : List NumObj} {x y : NumObj} (hy : y ∈ L1 ++ L2) : y ∈ L1 ++ x :: L2 := by
  rcases List.mem_append.mp hy with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- An object of `L1 ++ L2` beside `x` in `L1 ++ x :: L2`: its blocks are
not `x`'s struct. -/
theorem BcHeap.otherS {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x y : NumObj} (h : BcHeap S X Mt H F (L1 ++ x :: L2))
    (hy : y ∈ L1 ++ L2) : y.sb ≠ x.sb ∧ y.db ≠ x.sb :=
  ⟨fun e => (SplitFacts.of_nodup h.distinct).sRest (e ▸ mem_objBlocks hy),
    fun e => h.sb_ne_db (List.mem_append_right _ List.mem_cons_self) (mem_split hy) e.symm⟩

/-- An object of `L1 ++ L2` that is no view of `x`: its blocks are not `x`'s
buffer. -/
theorem BcHeap.otherD {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x y : NumObj} (h : BcHeap S X Mt H F (L1 ++ x :: L2))
    (hy : y ∈ L1 ++ L2) (hnv : y.db ≠ x.db) : y.sb ≠ x.db ∧ y.db ≠ x.db :=
  ⟨h.sb_ne_db (mem_split hy) (List.mem_append_right _ List.mem_cons_self), hnv⟩

/-- A byte a store into `L1 ++ x :: L2` may write: no allocator byte, not
`_bc_Free_list`, in no dead block and no block of another object. -/
structure HeapWriteOK (H : Heap) (F : List Blk) (X : Raws) (L1 L2 : List NumObj) (a : Nat) :
    Prop where
  alloc : ¬ AllocByte H a
  glob : ¬ bcFreeBytes a
  dead : ∀ b ∈ F, ¬ b.In a
  sb : ∀ y ∈ L1 ++ L2, ¬ y.sb.In a
  db : ∀ y ∈ L1 ++ L2, ¬ y.db.In a
  raw : ∀ b ∈ X.bs, ¬ b.In a

/-- A byte of `x`'s struct may be written. -/
theorem BcHeap.sb_writeOK {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S X Mt H F (L1 ++ x :: L2)) {a : Nat}
    (ha : x.sb.In a) : HeapWriteOK H F X L1 L2 a := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hxb := h.blocks x hx
  have hi := h.heap
  have sf := SplitFacts.of_nodup h.distinct
  have fb := hi.blk (List.mem_append_right _ hxb.sLive)
  have hb1 := fb.lo; have hb2 := fb.fin; have hb3 := fb.top
  refine ⟨live_not_alloc hi hxb.sLive ha, ?_, fun b hb hba => ?_, fun y hy hya => ?_,
    fun y hy hya => ?_, fun b hb hba => live_apart hi (h.raw.live b hb) hxb.sLive
      (h.raw_ne hb (List.mem_append_right _ (mem_objBlocks hx))) hba ha⟩
  · intro hg
    simp only [bcFreeBytes, bcFreeAddr] at hg
    simp only [Blk.In, Blk.pay, Blk.fin] at ha hb2
    simp only [heapStart] at hb1
    omega
  · exact live_apart hi (h.deadLive b hb).1 hxb.sLive (fun e' => sf.sF (e' ▸ hb)) hba ha
  · exact live_apart hi (h.blocks y (mem_split hy)).sLive hxb.sLive (h.otherS hy).1 hya ha
  · exact live_apart hi (h.blocks y (mem_split hy)).dLive hxb.sLive (h.otherS hy).2 hya ha

/-- A byte of an owner's buffer that no other object reads may be written. -/
theorem BcHeap.db_writeOK {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S X Mt H F (L1 ++ x :: L2)) (ho : x.Owns)
    (hnv : ∀ y ∈ L1 ++ L2, y.db ≠ x.db) {a : Nat} (ha : x.db.In a) :
    HeapWriteOK H F X L1 L2 a := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hxb := h.blocks x hx
  have hi := h.heap
  have sf := SplitFacts.of_nodup h.distinct
  have fb := hi.blk (List.mem_append_right _ hxb.dLive)
  have hb1 := fb.lo; have hb2 := fb.fin; have hb3 := fb.top
  refine ⟨live_not_alloc hi hxb.dLive ha, ?_, fun b hb hba => ?_, fun y hy hya => ?_,
    fun y hy hya => ?_, fun b hb hba => live_apart hi (h.raw.live b hb) hxb.dLive
      (h.raw_ne hb (List.mem_append_right _ (mem_objBlocks_db hx ho))) hba ha⟩
  · intro hg
    simp only [bcFreeBytes, bcFreeAddr] at hg
    simp only [Blk.In, Blk.pay, Blk.fin] at ha hb2
    simp only [heapStart] at hb1
    omega
  · exact live_apart hi (h.deadLive b hb).1 hxb.dLive (fun e' => sf.dF ho (e' ▸ hb)) hba ha
  · exact live_apart hi (h.blocks y (mem_split hy)).sLive hxb.dLive (h.otherD hy (hnv y hy)).1 hya ha
  · exact live_apart hi (h.blocks y (mem_split hy)).dLive hxb.dLive (hnv y hy) hya ha

/-- **One reference fewer**: the object `x'` replaces `x` (same blocks) in a
memory that differs from the old one only inside `x`'s struct block and in
bytes off the allocator, `_bc_Free_list` and every other heap block. -/
theorem BcHeap.update {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x x' : NumObj} (h : BcHeap S X Mt H F (L1 ++ x :: L2))
    (hsb : x'.sb = x.sb) (hdb : x'.db = x.db) (hptr : x'.rep.ptr = x.rep.ptr)
    (hbl : x'.Blocks H) (hn : NumAt Mt' x'.rep)
    {P : Nat → Prop} (hfr : MemOnly P Mt' Mt) (hP : ∀ a, P a → HeapWriteOK H F X L1 L2 a) :
    BcHeap S X Mt' H F (L1 ++ x' :: L2) := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hob : objBlocks (L1 ++ x' :: L2) = objBlocks (L1 ++ x :: L2) := by
    rw [objBlocks_append, objBlocks_cons, objBlocks_append, objBlocks_cons]
    simp only [NumObj.blocks, hsb, hdb, hptr]
  have hmem : ∀ y ∈ L1 ++ x' :: L2, y = x' ∨ y ∈ L1 ++ L2 := by
    intro y hy
    rcases List.mem_append.mp hy with h1 | h1
    · exact .inr (List.mem_append_left _ h1)
    · rcases List.mem_cons.mp h1 with rfl | h1
      · exact .inl rfl
      · exact .inr (List.mem_append_right _ h1)
  refine
    { heap := h.heap.transport fun a ha => hfr a fun hp => (hP a hp).alloc ha
      dead := h.dead.frame (ldv_congr .ld fun j hj => hfr _ fun hp => (hP _ hp).glob
          ⟨by omega, by simp only [widthOfM] at hj; omega⟩)
        fun b hb j hj => hfr _ fun hp => (hP _ hp).dead b hb (by
          have := (h.deadLive b hb).2
          simp only [Blk.In, Blk.fin, Blk.pay]; omega)
      deadLive := h.deadLive
      nums := ?_
      blocks := ?_
      distinct := by rw [hob]; exact h.distinct
      views := ViewsOwned.replace hptr hdb h.views
      globOwn := h.globOwn
      raw := (h.raw.frame fun b hb a ha => hfr a fun hp => (hP a hp).raw b hb ha).relist
        fun c hc => by rw [← hob]; exact hc }
  · intro y hy
    rcases hmem y hy with rfl | hy
    · exact hn
    · have hyL := mem_split (x := x) hy
      refine (h.nums y hyL).frame fun a ha => ?_
      rcases NumObj.foot_blocks (h.nums y hyL) (h.blocks y hyL) ha with hs | hd
      · exact hfr a fun hp => (hP a hp).sb y hy hs
      · exact hfr a fun hp => (hP a hp).db y hy hd
  · intro y hy
    rcases hmem y hy with rfl | hy
    · exact hbl
    · exact h.blocks y (mem_split hy)

/-- A byte of the allocator after `free` of the live block `d` was one before,
or lies in `d`'s payload. -/
theorem AllocByte.of_free {H : Heap} {lpre lpost : List Blk} {d : Blk}
    (hl : H.live = lpre ++ d :: lpost) {a : Nat}
    (h : AllocByte ⟨H.braw, d :: H.free, lpre ++ lpost⟩ a) : AllocByte H a ∨ d.In a := by
  have hsub : ∀ b ∈ lpre ++ lpost, b ∈ H.live := fun b hb => by
    rw [hl]
    rcases List.mem_append.mp hb with h1 | h1
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)
  have hd : d ∈ H.live := by rw [hl]; exact List.mem_append_right _ List.mem_cons_self
  cases h with
  | glob h1 h2 => exact .inl (.glob h1 h2)
  | hdr b hb h1 h2 =>
    refine .inl (.hdr b ?_ h1 h2)
    simp only [Heap.blocks, List.cons_append, List.mem_cons, List.mem_append] at hb
    rcases hb with rfl | hb | hb
    · exact List.mem_append_right _ hd
    · exact List.mem_append_left _ hb
    · exact List.mem_append_right _ (hsub b (List.mem_append.mpr hb))
  | freePay b hb h1 h2 =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact .inr ⟨h1, h2⟩
    · exact .inl (.freePay b hb h1 h2)
  | top h1 h2 => exact .inl (.top (by simpa [Heap.brk] using h1) h2)

/-- A block of `F` or of an object of `L1 ++ L2` is a block of the entry heap. -/
theorem SplitFacts.rest_mem {F : List Blk} {L1 L2 : List NumObj} {x : NumObj} {b : Blk}
    (hb : b ∈ F ++ objBlocks (L1 ++ L2)) : b ∈ F ++ objBlocks (L1 ++ x :: L2) := by
  rcases List.mem_append.mp hb with hb | hb
  · exact List.mem_append_left _ hb
  · obtain ⟨y, hy, hby⟩ := List.mem_flatMap.mp hb
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨y, mem_split hy, hby⟩)

/-- **The object leaves the heap**: `x`'s struct linked in front of the dead
chain, every other block kept and still live in `H'` (an owner's buffer may
have been freed), the views of `L1 ++ L2` owned. -/
theorem BcHeap.unlink {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H H' : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S X Mt H F (L1 ++ x :: L2))
    (hvw : ViewsOwned (L1 ++ L2)) (hlive : ∀ b ∈ H.live, (x.Owns → b ≠ x.db) → b ∈ H'.live)
    (hi : HeapInv S Mt' H')
    (hhead : ldv .ld Mt' bcFreeAddr = BitVec.ofNat 64 x.sb.pay)
    (hnext : ldv .ld Mt' (x.sb.pay + 16) = BitVec.ofNat 64 (deadHead F))
    (hkeep : ∀ b ∈ F ++ objBlocks (L1 ++ L2) ++ X.bs, ∀ a, b.In a → imgM Mt' a = imgM Mt a) :
    BcHeap S X Mt' H' (x.sb :: F) (L1 ++ L2) := by
  have sf := SplitFacts.of_nodup h.distinct
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hxb := h.blocks x hx
  have hdm : ∀ y ∈ L1 ++ L2, y.db ∈ objBlocks (L1 ++ L2) := fun y hy => by
    obtain ⟨w, hw, hwo, he⟩ := hvw.owner hy
    rw [← he]; exact mem_objBlocks_db hw hwo
  have hFk : ∀ b ∈ F, ∀ a, b.In a → imgM Mt' a = imgM Mt a := fun b hb =>
    hkeep b (List.mem_append_left _ (List.mem_append_left _ hb))
  refine
    { heap := hi
      dead := .cons hhead (h.dead.move (hnext.trans h.dead.head.symm) fun b hb j hj =>
        hFk b hb _ (by
          have := (h.deadLive b hb).2
          simp only [Blk.In, Blk.fin, Blk.pay]; omega))
      deadLive := ?_
      nums := ?_
      blocks := ?_
      distinct := ?_
      views := hvw
      globOwn := h.globOwn
      raw := h.raw.rebase (fun b hb => hlive b (h.raw.live b hb) fun hxo e =>
          h.raw_ne hb (List.mem_append_right _ (mem_objBlocks_db hx hxo)) e)
        (fun c hc => .inl (by
          rw [List.cons_append] at hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact List.mem_append_right _ (mem_objBlocks hx)
          · exact SplitFacts.rest_mem hc))
        fun b hb => hkeep b (List.mem_append_right _ hb) }
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨hlive _ hxb.sLive fun _ => h.sb_ne_db hx hx, hxb.sSz⟩
    · exact ⟨hlive b (h.deadLive b hb).1 fun ho e => sf.dF ho (e ▸ hb), (h.deadLive b hb).2⟩
  · intro y hy
    have hyL := mem_split (x := x) hy
    have hyb := h.blocks y hyL
    refine (h.nums y hyL).frame fun a ha => ?_
    rcases NumObj.foot_blocks (h.nums y hyL) hyb ha with hs | hd
    · exact hkeep _ (List.mem_append_left _ (List.mem_append_right _ (mem_objBlocks hy))) a hs
    · exact hkeep _ (List.mem_append_left _ (List.mem_append_right _ (hdm y hy))) a hd
  · intro y hy
    have hyL := mem_split (x := x) hy
    have hyb := h.blocks y hyL
    exact { hyb with
      sLive := hlive _ hyb.sLive fun _ => h.sb_ne_db hyL hx
      dLive := hlive _ hyb.dLive fun ho e => sf.dRest ho (e ▸ hdm y hy) }
  · rw [List.cons_append]
    exact List.nodup_cons.mpr ⟨fun hb => by
      rcases List.mem_append.mp hb with h1 | h1
      · exact sf.sF h1
      · exact sf.sRest h1, sf.nodup⟩

/-- **The last reference to an owner released**: with `x`'s digit block freed
(`FreePost` shape), `x` leaves the number heap and its struct heads the
chain. -/
theorem BcHeap.release {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S X Mt H F (L1 ++ x :: L2))
    (ho : x.Owns) (hnv : ∀ y ∈ L1, y.db ≠ x.db) {lpre lpost : List Blk}
    (hl : H.live = lpre ++ x.db :: lpost)
    (hi : HeapInv S Mt' ⟨H.braw, x.db :: H.free, lpre ++ lpost⟩)
    (hhead : ldv .ld Mt' bcFreeAddr = BitVec.ofNat 64 x.sb.pay)
    (hnext : ldv .ld Mt' (x.sb.pay + 16) = BitVec.ofNat 64 (deadHead F))
    (hkeep : ∀ b ∈ F ++ objBlocks (L1 ++ L2) ++ X.bs, ∀ a, b.In a → imgM Mt' a = imgM Mt a) :
    BcHeap S X Mt' ⟨H.braw, x.db :: H.free, lpre ++ lpost⟩ (x.sb :: F) (L1 ++ L2) := by
  refine h.unlink (ViewsOwned.remove h.views fun _ => hnv) (fun b hb hne => ?_) hi hhead hnext
    hkeep
  have hb' : b ∈ lpre ++ x.db :: lpost := hl ▸ hb
  rcases List.mem_append.mp hb' with h1 | h1
  · exact List.mem_append_left _ h1
  · rcases List.mem_cons.mp h1 with rfl | h1
    · exact absurd rfl (hne ho)
    · exact List.mem_append_right _ h1

/-- **The last reference to a view released**: the allocator is untouched. -/
theorem BcHeap.releaseView {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S X Mt H F (L1 ++ x :: L2)) (hv : ¬ x.Owns)
    (hi : HeapInv S Mt' H)
    (hhead : ldv .ld Mt' bcFreeAddr = BitVec.ofNat 64 x.sb.pay)
    (hnext : ldv .ld Mt' (x.sb.pay + 16) = BitVec.ofNat 64 (deadHead F))
    (hkeep : ∀ b ∈ F ++ objBlocks (L1 ++ L2) ++ X.bs, ∀ a, b.In a → imgM Mt' a = imgM Mt a) :
    BcHeap S X Mt' H (x.sb :: F) (L1 ++ L2) :=
  h.unlink (ViewsOwned.remove h.views fun ho => absurd ho hv) (fun b hb _ => hb) hi hhead hnext
    hkeep

/-- **`bc_free_num(num)`** at `0x800048c0` on a `NULL` slot: returns at once. -/
theorem bc_free_num_null {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {q : Nat} (hq : PtrSlot S q) (h0 : ldv .ld Mt q = 0#64)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [14] R' R → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x800048c0#64 R Mt := by
  have hql := hq.lo; have hqh := hq.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive
  all_goals bsimp [h10, h0]
  all_goals first | bc_addr | exact hq.acc | skip
  all_goals (try (intro hc; exact absurd hc (by decide)))
  all_goals (try bc_intro_true)
  dx_run hlive
  all_goals bsimp []
  exact hk _ (by keeps_tac Keeps.refl _ _)

/-- The facts about `x` and the slot `bc_free_num` uses. -/
structure FreeEntry (S : Nat → Prop) (X : Raws) (Mt : Mem) (H : Heap) (F : List Blk)
    (L1 L2 : List NumObj) (x : NumObj) (q sp : Nat) : Prop where
  heap : BcHeap S X Mt H F (L1 ++ x :: L2)
  refs : 1 ≤ x.rep.refs
  slot : PtrSlot S q
  off : SlotOff H F X (L1 ++ x :: L2) sp q
  word : ldv .ld Mt q = BitVec.ofNat 64 x.rep.p
  stack : StackFrame S sp 32
  above : heapEnd + 32 ≤ sp
  /-- no view before an owner with one reference reads its buffer -/
  noView : x.rep.refs = 1 → x.Owns → ∀ y ∈ L1, y.db ≠ x.db

theorem FreeEntry.mem {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} {q sp : Nat} (_ : FreeEntry S X Mt H F L1 L2 x q sp) :
    x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self

/-- The slot is apart from `x`'s struct. -/
theorem FreeEntry.slot_apart {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} {q sp : Nat} (e : FreeEntry S X Mt H F L1 L2 x q sp) :
    q + 8 ≤ x.sb.pay ∨ x.sb.fin ≤ q := by
  have hs := e.off.blocks x.sb (List.mem_append_right _ (mem_objBlocks e.mem))
  have hz := (e.heap.blocks x e.mem).sSz
  rcases Nat.lt_or_ge q x.sb.pay with h1 | h1
  · refine Classical.byContradiction fun hc => hs x.sb.pay ⟨by omega, by omega⟩ ⟨Nat.le_refl _, ?_⟩
    simp only [Blk.fin, Blk.pay]; omega
  · refine Classical.byContradiction fun hc => hs q ⟨Nat.le_refl _, by omega⟩ ⟨h1, ?_⟩
    omega

/-- The decrement path's return, from `0x8000493c` (`*num = NULL`). -/
theorem free_num_clear {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {Mt : Mem} {q : Nat} (hq : PtrSlot S q)
    (R : Nat → BitVec 64) (h15 : R 15 = BitVec.ofNat 64 q) (hal : (R 1).toNat % 4 = 0)
    (hk : DW live S Q (R 1) R (writeLog Mt [(q, 8, 0#64)])) :
    DW live S Q 0x8000493c#64 R Mt := by
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive
  all_goals bsimp [h15]
  all_goals first | exact hk | bc_addr | exact hq.acc | skip

/-- The slot is apart from every kept block: the dead chain, the other
objects and the raw blocks. -/
theorem SlotOff.keep {H : Heap} {F : List Blk} {X : Raws} {L1 L2 : List NumObj} {x : NumObj}
    {sp q : Nat} (o : SlotOff H F X (L1 ++ x :: L2) sp q) {b : Blk}
    (hb : b ∈ F ++ objBlocks (L1 ++ L2) ++ X.bs) : ∀ a, slotBytes q a → ¬ b.In a := by
  rcases List.mem_append.mp hb with hb | hb
  · exact o.blocks b (SplitFacts.rest_mem hb)
  · exact o.raw b hb

/-- The blocks of `F ++ objBlocks (L1 ++ L2)` and the raw blocks are live and
apart from `x`'s. -/
theorem BcHeap.rest_live {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S X Mt H F (L1 ++ x :: L2))
    {b : Blk} (hb : b ∈ F ++ objBlocks (L1 ++ L2) ++ X.bs) :
    b ∈ H.live ∧ b ≠ x.sb ∧ (x.Owns → b ≠ x.db) := by
  have sf := SplitFacts.of_nodup h.distinct
  rcases List.mem_append.mp hb with hb | hr
  · rcases List.mem_append.mp hb with hf | ho
    · exact ⟨(h.deadLive b hf).1, fun e => sf.sF (e ▸ hf), fun hxo e => sf.dF hxo (e ▸ hf)⟩
    · refine ⟨?_, fun e => sf.sRest (e ▸ ho), fun hxo e => sf.dRest hxo (e ▸ ho)⟩
      obtain ⟨y, hy, hby⟩ := List.mem_flatMap.mp ho
      have hyb := h.blocks y (mem_split hy)
      unfold NumObj.blocks at hby
      split at hby <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hby
      · subst hby; exact hyb.sLive
      · rcases hby with rfl | rfl
        · exact hyb.sLive
        · exact hyb.dLive
  · have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
    exact ⟨h.raw.live b hr, h.raw_ne hr (List.mem_append_right _ (mem_objBlocks hx)),
      fun hxo => h.raw_ne hr (List.mem_append_right _ (mem_objBlocks_db hx hxo))⟩

/-- The state after `free(n_ptr)` returns to `0x800048f4`: the allocator's
post, the memory before the call (`M2`: `n_refs` cleared, the frame
written), the two saved words, and the registers. -/
structure AfterFree (S : Nat → Prop) (Mt M2 Mt3 : Mem) (H : Heap) (x : NumObj)
    (lpre lpost : List Blk) (q sp : Nat) (R R1 : Nat → BitVec 64) : Prop where
  post : FreePost S M2 Mt3 H ⟨H.braw, x.db :: H.free, lpre ++ lpost⟩ x.db lpre lpost
  mem : ∀ a, ¬ (x.sb.pay + 12 ≤ a ∧ a < x.sb.pay + 16) → ¬ frameIn sp 32 a →
    imgM M2 a = imgM Mt a
  w8 : ldv .ld M2 (sp - 32 + 8) = BitVec.ofNat 64 q
  w24 : ldv .ld M2 (sp - 32 + 24) = R 1
  r2 : R1 2 = BitVec.ofNat 64 (sp - 32)
  regs : ∀ z, z ≠ 1 → z ≠ 2 → z ≠ 10 → z ≠ 13 → z ≠ 14 → z ≠ 15 → R1 z = R z

/-- The release path's final memory: `ReleasePost`. -/
theorem release_post {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} {q sp : Nat} (e : FreeEntry S X Mt H F L1 L2 x q sp)
    (ho : x.Owns) (hr1 : x.rep.refs = 1) {lpre lpost : List Blk}
    (hl : H.live = lpre ++ x.db :: lpost) {M2 Mt3 : Mem} {R R1 : Nat → BitVec 64} (af : AfterFree S Mt M2 Mt3 H x lpre lpost q sp R R1)
    {Mt' : Mem}
    (hM4e : writeLog (writeLog (writeLog Mt3
      [(x.rep.p + 16, 8, BitVec.ofNat 64 (deadHead F))]) [(q, 8, 0#64)])
      [(2147601840, 8, BitVec.ofNat 64 x.rep.p)] = Mt') :
    ReleasePost S X Mt Mt' H ⟨H.braw, x.db :: H.free, lpre ++ lpost⟩ F L1 L2 x q sp := by
  have h := e.heap
  have hi := h.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hx := e.mem
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  num_facts hn
  have hq := e.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hsf := e.stack
  have hspl := hsf.hi; have hspa := hsf.al
  have hsp := e.above
  simp only [heapEnd] at hsp
  have hrf := hn.refs
  have hpt := hn.ptr
  have hw := e.word
  have hpp : x.rep.p = x.sb.pay := hxb.sPay
  have hdp : x.rep.ptr = x.db.pay := hxb.dPay ho
  have hqs := e.slot_apart
  have hsz := hxb.sSz
  have sf := SplitFacts.of_nodup h.distinct
  have fbs := hi.blk (List.mem_append_right _ hxb.sLive)
  have fbd := hi.blk (List.mem_append_right _ hxb.dLive)
  have hs1 : 2147603920 ≤ x.sb.h := fbs.lo
  have hs2 : x.sb.fin ≤ H.brk := fbs.fin
  have hs3 : H.brk ≤ 2273312768 := fbs.top
  have hd1 : 2147603920 ≤ x.db.h := fbd.lo
  have hd2 : x.db.fin ≤ H.brk := fbd.fin
  have hsfin : x.sb.fin = x.sb.h + 16 + x.sb.sz := rfl
  have hdfin : x.db.fin = x.db.h + 16 + x.db.sz := rfl
  have hsph : x.sb.pay = x.sb.h + 16 := rfl
  have hdph : x.db.pay = x.db.h + 16 := rfl
  have hsd : x.sb.fin ≤ x.db.h ∨ x.db.fin ≤ x.sb.h :=
    apart_of_mem hi.apart (List.mem_append_right _ hxb.sLive) (List.mem_append_right _ hxb.dLive) (h.sb_ne_db hx hx)
  have hgl : ∀ b ∈ accAddrs 2147601840 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact h.globOwn b (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega)
  have hoffg := e.off.glob
  have hofff := e.off.frame
  simp only [bcFreeAddr] at hoffg
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hfp := af.post
  have hM2 := af.mem
  have hnotA : ∀ a, frameIn sp 32 a → ¬ AllocByte H a := fun a hf ha => by
    rcases AllocByte.glob_or_heap hi ha with h' | h' <;>
      simp only [freeListAddr, heapStart, heapEnd, frameIn] at h' hf <;> omega
  have hM3 : ∀ a, ¬ AllocByte H a → imgM Mt3 a = imgM M2 a := hfp.frame
  have hfr3 : ∀ a, frameIn sp 32 a → imgM Mt3 a = imgM M2 a := fun a ha => hM3 a (hnotA a ha)
  have hq3 : ∀ a, slotBytes q a → imgM Mt3 a = imgM Mt a := fun a ha => by
    rw [hM3 a (e.off.alloc a ha), hM2 a (by omega) (by simp only [frameIn]; omega)]
  have hg3 : ∀ a, bcFreeBytes a → imgM Mt3 a = imgM Mt a := fun a ha => by
    simp only [bcFreeBytes, bcFreeAddr] at ha
    rw [hM3 a fun ha' => by
        rcases AllocByte.glob_or_heap hi ha' with h' | h' <;>
          simp only [freeListAddr, heapStart, heapEnd] at h' <;> omega,
      hM2 a (by omega) (by simp only [frameIn]; omega)]
  have hsfin : x.sb.fin = x.sb.h + 16 + x.sb.sz := rfl
  have hdfin : x.db.fin = x.db.h + 16 + x.db.sz := rfl
  have hsph : x.sb.pay = x.sb.h + 16 := rfl
  have hdph : x.db.pay = x.db.h + 16 := rfl
  have hpp' : x.rep.p = x.sb.h + 16 := hpp
  have hM4 : ∀ a, ¬ (x.sb.pay + 16 ≤ a ∧ a < x.sb.pay + 24) → ¬ slotBytes q a →
      ¬ bcFreeBytes a → imgM Mt' a = imgM Mt3 a := by
    intro a h1 h3 h4
    simp only [bcFreeBytes, bcFreeAddr] at h4
    rw [← hM4e, imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]
  have hH' := hfp.inv
  -- a byte off the four written regions of `Mt` is unchanged
  have hrest : ∀ a, ¬ AllocByte H a → ¬ x.sb.In a → ¬ slotBytes q a → ¬ frameIn sp 32 a →
      ¬ bcFreeBytes a → imgM Mt' a = imgM Mt a := fun a h1 h3 h4 h5 h6 => by
    rw [hM4 a (fun h' => h3 ⟨by omega, by omega⟩) h4 h6, hM3 a h1,
      hM2 a (fun h' => h3 ⟨by omega, by omega⟩) h5]
  have hkeep : ∀ b ∈ F ++ objBlocks (L1 ++ L2) ++ X.bs, ∀ a, b.In a → imgM Mt' a = imgM Mt a := by
    intro b hb a ha
    have ⟨hbl, hbs, _⟩ := h.rest_live hb
    have fb := hi.blk (List.mem_append_right _ hbl)
    have hb1 : 2147603920 ≤ b.h := fb.lo
    have hb2 : b.fin ≤ H.brk := fb.fin
    have hbp : b.pay = b.h + 16 := rfl
    have hbf : b.fin = b.h + 16 + b.sz := rfl
    simp only [Blk.In] at ha
    refine hrest a (live_not_alloc hi hbl ha) (fun h' => live_apart hi hbl hxb.sLive hbs ha h')
      (fun h' => e.off.keep hb a h' ha)
      (by simp only [frameIn]; omega) (by simp only [bcFreeBytes, bcFreeAddr]; omega)
  have hi' : HeapInv S Mt' ⟨H.braw, x.db :: H.free, lpre ++ lpost⟩ := by
    refine hH'.transport fun a ha => hM4 a ?_ ?_ ?_
    · intro h'
      rcases AllocByte.of_free hl ha with ha | ha
      · exact live_not_alloc hi hxb.sLive ⟨by omega, by omega⟩ ha
      · simp only [Blk.In] at ha; omega
    · intro h'
      rcases AllocByte.of_free hl ha with ha | ha
      · exact e.off.alloc a h' ha
      · exact e.off.blocks x.db (List.mem_append_right _ (mem_objBlocks_db hx ho)) a h' ha
    · intro h'
      simp only [bcFreeBytes, bcFreeAddr] at h'
      rcases AllocByte.of_free hl ha with ha | ha
      · rcases AllocByte.glob_or_heap hi ha with h'' | h'' <;>
          simp only [freeListAddr, heapStart, heapEnd] at h'' <;> omega
      · simp only [Blk.In] at ha; omega
  have hhead : ldv .ld Mt' bcFreeAddr = BitVec.ofNat 64 x.sb.pay := by
    rw [← hM4e, ← hpp]; exact ldv_store_hit _ _ _
  have hnext : ldv .ld Mt' (x.sb.pay + 16) = BitVec.ofNat 64 (deadHead F) := by
    rw [← hM4e, ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), hpp]
    exact ldv_store_hit _ _ _
  have hlive' : ∀ b, b ∈ lpre ++ lpost ↔ b ∈ H.live ∧ b ≠ x.db := fun b => by
    have hnd := hi.live_nodup
    rw [hl] at hnd
    have hdn : x.db ∉ lpre ++ lpost := (List.nodup_cons.mp (List.perm_middle.nodup_iff.mp hnd)).1
    show b ∈ lpre ++ lpost ↔ b ∈ H.live ∧ b ≠ x.db
    rw [hl]
    constructor
    · intro hb
      refine ⟨?_, fun e' => hdn (e' ▸ hb)⟩
      rcases List.mem_append.mp hb with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)
    · rintro ⟨hb, hne⟩
      rcases List.mem_append.mp hb with h1 | h1
      · exact List.mem_append_left _ h1
      · rcases List.mem_cons.mp h1 with rfl | h1
        · exact absurd rfl hne
        · exact List.mem_append_right _ h1
  exact
    { heap := BcHeap.release h ho (e.noView hr1 ho) hl hi' hhead hnext hkeep
      owned := fun _ => ⟨rfl, hlive', rfl⟩
      view := fun hv => absurd ho hv
      slot := by rw [← hM4e, ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _
      frame := fun a ha => by
        simp only [not_or] at ha
        exact hrest a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 }

/-- The machine steps of the release path after `free` (`0x800048f4` to the
return): link the struct into `_bc_Free_list`, clear the slot. -/
theorem free_num_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt3 : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {sp q p d : Nat}
    (hsf : StackFrame S sp 32) (hsp : heapEnd + 32 ≤ sp) (hq : PtrSlot S q)
    (hp1 : 2147603920 ≤ p) (hp2 : p + 40 ≤ 2273312768) (hp3 : p % 8 = 0)
    (hgl : ∀ b ∈ accAddrs 2147601840 8, S b) (R R1 : Nat → BitVec 64)
    (hal : (R 1).toNat % 4 = 0) (r2 : R1 2 = BitVec.ofNat 64 (sp - 32))
    (w8 : ldv .ld Mt3 (sp - 32 + 8) = BitVec.ofNat 64 q) (w24 : ldv .ld Mt3 (sp - 32 + 24) = R 1)
    (wq : ldv .ld Mt3 q = BitVec.ofNat 64 p)
    (wq3 : ldv .ld (writeLog Mt3 [(p + 16, 8, BitVec.ofNat 64 d)]) q = BitVec.ofNat 64 p)
    (wg : ldv .ld Mt3 2147601840 = BitVec.ofNat 64 d)
    (hk : ∀ R', R' 1 = R 1 → R' 2 = BitVec.ofNat 64 sp →
      (∀ z, z ≠ 1 → z ≠ 2 → z ≠ 13 → z ≠ 14 → z ≠ 15 → R' z = R1 z) →
      DW live S Q (R 1) R' (writeLog (writeLog (writeLog Mt3
        [(p + 16, 8, BitVec.ofNat 64 d)]) [(q, 8, 0#64)]) [(2147601840, 8, BitVec.ofNat 64 p)])) :
    DW live S Q 0x800048f4#64 R1 Mt3 := by
  have hspl := hsf.hi; have hspa := hsf.al
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hsp
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [r2, w8] at 0x800048fc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  apply st_800048fc hlive
  · bsimp []; bc_addr
  · bsimp []; exact hgl
  bsimp [wg]
  bc_run hlive hS [r2, w8, w24, wq, wq3, ldv_ld_miss]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hq.acc | exact hgl | exact hal | bc_addr | skip
  refine hk _ ?_ ?_ fun z z1 z2 z13 z14 z15 => ?_
  · bsimp [w24]
  · bsimp [r2]; congr 1; omega
  · simp only [upd_apply, z1, z2, z13, z14, z15, ite_false]

/-- The release path after `free`, from `0x800048f4`. -/
theorem free_num_tail {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {q sp : Nat} (e : FreeEntry S X Mt H F L1 L2 x q sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0) (hk : FreeNumK live S X Q R Mt H F L1 L2 x q sp)
    (hr1 : x.rep.refs = 1) (ho : x.Owns) {lpre lpost : List Blk}
    (hl : H.live = lpre ++ x.db :: lpost)
    {M2 Mt3 : Mem} {R1 : Nat → BitVec 64}
    (af : AfterFree S Mt M2 Mt3 H x lpre lpost q sp R R1) :
    DW live S Q 0x800048f4#64 R1 Mt3 := by
  have h := e.heap
  have hi := h.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hx := e.mem
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  num_facts hn
  have hq := e.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hsf := e.stack
  have hspl := hsf.hi; have hspa := hsf.al
  have hsp := e.above
  simp only [heapEnd] at hsp
  have hrf := hn.refs
  have hpt := hn.ptr
  have hw := e.word
  have hpp : x.rep.p = x.sb.pay := hxb.sPay
  have hdp : x.rep.ptr = x.db.pay := hxb.dPay ho
  have hqs := e.slot_apart
  have hsz := hxb.sSz
  have sf := SplitFacts.of_nodup h.distinct
  have fbs := hi.blk (List.mem_append_right _ hxb.sLive)
  have fbd := hi.blk (List.mem_append_right _ hxb.dLive)
  have hs1 : 2147603920 ≤ x.sb.h := fbs.lo
  have hs2 : x.sb.fin ≤ H.brk := fbs.fin
  have hs3 : H.brk ≤ 2273312768 := fbs.top
  have hd1 : 2147603920 ≤ x.db.h := fbd.lo
  have hd2 : x.db.fin ≤ H.brk := fbd.fin
  have hsfin : x.sb.fin = x.sb.h + 16 + x.sb.sz := rfl
  have hdfin : x.db.fin = x.db.h + 16 + x.db.sz := rfl
  have hsph : x.sb.pay = x.sb.h + 16 := rfl
  have hdph : x.db.pay = x.db.h + 16 := rfl
  have hsd : x.sb.fin ≤ x.db.h ∨ x.db.fin ≤ x.sb.h :=
    apart_of_mem hi.apart (List.mem_append_right _ hxb.sLive) (List.mem_append_right _ hxb.dLive) (h.sb_ne_db hx hx)
  have hgl : ∀ b ∈ accAddrs 2147601840 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact h.globOwn b (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega)
  have hoffg := e.off.glob
  have hofff := e.off.frame
  simp only [bcFreeAddr] at hoffg
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hfp := af.post
  have hM2 := af.mem
  have hsfin : x.sb.fin = x.sb.h + 16 + x.sb.sz := rfl
  have hdfin : x.db.fin = x.db.h + 16 + x.db.sz := rfl
  have hsph : x.sb.pay = x.sb.h + 16 := rfl
  have hdph : x.db.pay = x.db.h + 16 := rfl
  have hpp' : x.rep.p = x.sb.h + 16 := hpp
  have hdp' : x.rep.ptr = x.db.h + 16 := hdp
  have hnotA : ∀ a, frameIn sp 32 a → ¬ AllocByte H a := fun a hf ha => by
    rcases AllocByte.glob_or_heap hi ha with h' | h' <;>
      simp only [freeListAddr, heapStart, heapEnd, frameIn] at h' hf <;> omega
  have hM3 : ∀ a, ¬ AllocByte H a → imgM Mt3 a = imgM M2 a := hfp.frame
  have hfr3 : ∀ a, frameIn sp 32 a → imgM Mt3 a = imgM M2 a := fun a ha => hM3 a (hnotA a ha)
  have hq3 : ∀ a, slotBytes q a → imgM Mt3 a = imgM Mt a := fun a ha => by
    rw [hM3 a (e.off.alloc a ha), hM2 a (by omega) (by simp only [frameIn]; omega)]
  have hg3 : ∀ a, bcFreeBytes a → imgM Mt3 a = imgM Mt a := fun a ha => by
    simp only [bcFreeBytes, bcFreeAddr] at ha
    rw [hM3 a fun ha' => by
        rcases AllocByte.glob_or_heap hi ha' with h' | h' <;>
          simp only [freeListAddr, heapStart, heapEnd] at h' <;> omega,
      hM2 a (by omega) (by simp only [frameIn]; omega)]
  have w8 : ldv .ld Mt3 (sp - 32 + 8) = BitVec.ofNat 64 q := by
    rw [ldv_congr .ld fun j hj => hfr3 _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩]
    exact af.w8
  have w24 : ldv .ld Mt3 (sp - 32 + 24) = R 1 := by
    rw [ldv_congr .ld fun j hj => hfr3 _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩]
    exact af.w24
  have wq : ldv .ld Mt3 q = BitVec.ofNat 64 x.rep.p := by
    rw [ldv_congr .ld fun j hj => hq3 _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩]; exact hw
  have wg : ldv .ld Mt3 2147601840 = BitVec.ofNat 64 (deadHead F) := by
    rw [ldv_congr .ld fun j hj => hg3 _ ⟨by simp only [bcFreeAddr]; omega,
      by simp only [widthOfM, bcFreeAddr] at hj ⊢; omega⟩]
    exact h.dead.head
  have r2 := af.r2
  have hpp0 : x.rep.p = x.sb.h + 16 := hpp
  have wq3 : ldv .ld (writeLog Mt3 [(x.rep.p + 16, 8, BitVec.ofNat 64 (deadHead F))]) q =
      BitVec.ofNat 64 x.rep.p := by
    rw [ldv_ld_miss _ _ (by omega)]; exact wq
  refine free_num_ret hlive hS hsf (by simp only [heapEnd]; omega) hq (by omega) (by omega) (by omega) hgl R R1 hal r2
    w8 w24 wq wq3 wg fun R' e1 e2 hr => ?_
  refine hk.rel hr1 R' _ _ ?_ (release_post e ho hr1 hl af rfl)
  intro z hz
  simp only [freeNumClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
  rcases (show z = 1 ∨ z = 2 ∨ (z ≠ 1 ∧ z ≠ 2) by omega) with rfl | rfl | ⟨z1, z2⟩
  · exact e1
  · rw [e2, h2]
  · rw [hr z z1 z2 hz.2.1 hz.2.2.1 hz.2.2.2]
    exact af.regs z z1 z2 hz.1 hz.2.1 hz.2.2.1 hz.2.2.2

/-- The last reference, from `0x800048c0` with `n_refs = 1`. -/
theorem free_num_release {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {q sp : Nat} (e : FreeEntry S X Mt H F L1 L2 x q sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0) (hk : FreeNumK live S X Q R Mt H F L1 L2 x q sp)
    (hr1 : x.rep.refs = 1) (ho : x.Owns) :
    DW live S Q 0x800048c0#64 R Mt := by
  have h := e.heap
  have hi := h.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hx := e.mem
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  num_facts hn
  have hq := e.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hsf := e.stack
  have hspl := hsf.hi; have hspa := hsf.al
  have hsp := e.above
  simp only [heapEnd] at hsp
  have hrf := hn.refs
  have hpt := hn.ptr
  have hw := e.word
  have hpp : x.rep.p = x.sb.pay := hxb.sPay
  have hdp : x.rep.ptr = x.db.pay := hxb.dPay ho
  have hqs := e.slot_apart
  have hsz := hxb.sSz
  have sf := SplitFacts.of_nodup h.distinct
  have fbs := hi.blk (List.mem_append_right _ hxb.sLive)
  have fbd := hi.blk (List.mem_append_right _ hxb.dLive)
  have hs1 : 2147603920 ≤ x.sb.h := fbs.lo
  have hs2 : x.sb.fin ≤ H.brk := fbs.fin
  have hs3 : H.brk ≤ 2273312768 := fbs.top
  have hd1 : 2147603920 ≤ x.db.h := fbd.lo
  have hd2 : x.db.fin ≤ H.brk := fbd.fin
  have hsfin : x.sb.fin = x.sb.h + 16 + x.sb.sz := rfl
  have hdfin : x.db.fin = x.db.h + 16 + x.db.sz := rfl
  have hsph : x.sb.pay = x.sb.h + 16 := rfl
  have hdph : x.db.pay = x.db.h + 16 := rfl
  have hsd : x.sb.fin ≤ x.db.h ∨ x.db.fin ≤ x.sb.h :=
    apart_of_mem hi.apart (List.mem_append_right _ hxb.sLive) (List.mem_append_right _ hxb.dLive) (h.sb_ne_db hx hx)
  have hgl : ∀ b ∈ accAddrs 2147601840 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact h.globOwn b (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega)
  have hoffg := e.off.glob
  have hofff := e.off.frame
  simp only [bcFreeAddr] at hoffg
  have htx : tohostAddr = 0x8001ad00 := rfl
  -- to the `free` call
  iterate 2
    try bc_run hlive hS [h10, h2, hw, hrf, hr1, ldv_ld_miss, hpt] at 0x800048f0
    all_goals first | exact hq.acc | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals try (intro hc; bv_nat at hc; omega)
    all_goals try intro _
  bc_run hlive hS [h10, h2, hw, hrf, hr1, ldv_ld_miss, hpt] at 0x800048f0
  · intro hc
    exact absurd ((ofNat_eq_iff (x := x.rep.ptr) (y := 0) (by omega) (by omega)).mp hc) (by omega)
  intro _
  bc_run hlive hS [h10, h2, hw, hrf, hr1, ldv_ld_miss, hpt] at 0x800048f0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hsfin : x.sb.fin = x.sb.h + 16 + x.sb.sz := rfl
  have hdfin : x.db.fin = x.db.h + 16 + x.db.sz := rfl
  have hsph : x.sb.pay = x.sb.h + 16 := rfl
  have hdph : x.db.pay = x.db.h + 16 := rfl
  generalize hM2e : writeLog (writeLog (writeLog Mt [(x.rep.p + 12, 4, 0#64)])
    [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)] = M2
  have hM2 : ∀ a, ¬ (x.sb.pay + 12 ≤ a ∧ a < x.sb.pay + 16) → ¬ frameIn sp 32 a →
      imgM M2 a = imgM Mt a := by
    intro a h1 h3
    simp only [frameIn] at h3
    rw [← hM2e, imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]
  have hnotA : ∀ a, frameIn sp 32 a → ¬ AllocByte H a := fun a hf ha => by
    rcases AllocByte.glob_or_heap hi ha with h' | h' <;>
      simp only [freeListAddr, heapStart, heapEnd, frameIn] at h' hf <;> omega
  have hi2 : HeapInv S M2 H := hi.transport fun a ha => hM2 a
    (fun h1 => live_not_alloc hi hxb.sLive ⟨by omega, by omega⟩ ha) fun h3 => hnotA a h3 ha
  obtain ⟨lpre, lpost, hl⟩ := List.append_of_mem hxb.dLive
  apply st_800048f0 hlive
  refine free_spec hlive hi2 hl _ (by bsimp [hdp]) (by bsimp []) ?_
  intro R1 Mt3 hk1 hfp
  bsimp []
  refine free_num_tail hlive e R h10 h2 hal hk hr1 ho hl
    ⟨hfp, hM2, by rw [← hM2e]; exact ldv_store_hit _ _ _,
      by rw [← hM2e, ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _,
      by rw [hk1.get 2]; bsimp [h2],
      fun z z1 z2 z10 z13 z14 z15 => by
        rw [hk1 z (by simp; omega)]
        simp only [upd_apply, z1, z2, z10, z13, z14, z15, ite_false]⟩

/-- The view release path's final memory: `ReleasePost` with the allocator
untouched. -/
theorem release_post_view {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} {q sp : Nat} (e : FreeEntry S X Mt H F L1 L2 x q sp)
    (hv : ¬ x.Owns) {Mt' : Mem}
    (hM : ∀ a, ¬ x.sb.In a → ¬ slotBytes q a → ¬ bcFreeBytes a → imgM Mt' a = imgM Mt a)
    (hhead : ldv .ld Mt' bcFreeAddr = BitVec.ofNat 64 x.sb.pay)
    (hnext : ldv .ld Mt' (x.sb.pay + 16) = BitVec.ofNat 64 (deadHead F))
    (hslot : ldv .ld Mt' q = 0#64) :
    ReleasePost S X Mt Mt' H H F L1 L2 x q sp := by
  have h := e.heap
  have hi := h.heap
  have hxb := h.blocks x e.mem
  have hnG : ∀ a, AllocByte H a → ¬ bcFreeBytes a := fun a ha hg => by
    simp only [bcFreeBytes, bcFreeAddr] at hg
    rcases AllocByte.glob_or_heap hi ha with h' | h' <;>
      simp only [freeListAddr, heapStart, heapEnd] at h' <;> omega
  have hi' : HeapInv S Mt' H := hi.transport fun a ha =>
    hM a (fun hs => live_not_alloc hi hxb.sLive hs ha) (fun hq => e.off.alloc a hq ha) (hnG a ha)
  have hkeep : ∀ b ∈ F ++ objBlocks (L1 ++ L2) ++ X.bs, ∀ a, b.In a → imgM Mt' a = imgM Mt a := by
    intro b hb a ha
    have ⟨hbl, hbs, _⟩ := h.rest_live hb
    have fb := hi.blk (List.mem_append_right _ hbl)
    have hb1 : 2147603920 ≤ b.h := fb.lo
    have hbp : b.pay = b.h + 16 := rfl
    simp only [Blk.In] at ha
    exact hM a (fun h' => live_apart hi hbl hxb.sLive hbs ha h')
      (fun h' => e.off.keep hb a h' ha)
      (by simp only [bcFreeBytes, bcFreeAddr]; omega)
  exact
    { heap := h.releaseView hv hi' hhead hnext hkeep
      owned := fun ho => absurd ho hv
      view := fun _ => rfl
      slot := hslot
      frame := fun a ha => by
        simp only [not_or] at ha
        exact hM a ha.2.1 ha.2.2.1 ha.2.2.2.2 }

/-- The last reference to a view, from `0x800048c0` with `n_refs = 1` and
`n_ptr = NULL` (`0x80004924`): no `free` call. -/
theorem free_num_view {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {q sp : Nat} (e : FreeEntry S X Mt H F L1 L2 x q sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q)
    (hal : (R 1).toNat % 4 = 0) (hk : FreeNumK live S X Q R Mt H F L1 L2 x q sp)
    (hr1 : x.rep.refs = 1) (hv : ¬ x.Owns) :
    DW live S Q 0x800048c0#64 R Mt := by
  have h := e.heap
  have hi := h.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hx := e.mem
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  num_facts hn
  have hq := e.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hrf := hn.refs
  have hpt := hn.ptr
  have hw := e.word
  have hv0 : x.rep.ptr = 0 := Classical.not_not.mp hv
  have hpp : x.rep.p = x.sb.pay := hxb.sPay
  have hqs := e.slot_apart
  have hsz := hxb.sSz
  have fbs := hi.blk (List.mem_append_right _ hxb.sLive)
  have hs1 : 2147603920 ≤ x.sb.h := fbs.lo
  have hs2 : x.sb.fin ≤ H.brk := fbs.fin
  have hs3 : H.brk ≤ 2273312768 := fbs.top
  have hsfin : x.sb.fin = x.sb.h + 16 + x.sb.sz := rfl
  have hsph : x.sb.pay = x.sb.h + 16 := rfl
  have hgl : ∀ b ∈ accAddrs 2147601840 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact h.globOwn b (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega)
  have hoffg := e.off.glob
  simp only [bcFreeAddr] at hoffg
  have htx : tohostAddr = 0x8001ad00 := rfl
  have wg : ldv .ld Mt 2147601840 = BitVec.ofNat 64 (deadHead F) := h.dead.head
  have hp0 : 2147603936 ≤ x.rep.p := by rw [hpp]; simp only [Blk.pay]; omega
  have hpq : x.rep.p + 24 ≤ q ∨ q + 8 ≤ x.rep.p := by
    rw [hpp]; simp only [Blk.pay, Blk.fin] at hqs ⊢; omega
  iterate 2
    try bc_run hlive hS [h10, hw, hrf, hr1, ldv_ld_miss, hpt, hv0] at 0x80004928
    all_goals first | exact hq.acc | skip
    all_goals try (intro hc; bv_nat at hc; omega)
    all_goals try intro _
  bc_run hlive hS [h10, hw, hrf, hr1, ldv_ld_miss, hpt, hv0] at 0x80004928
  all_goals first | exact hq.acc | skip
  bc_run hlive hS [h10, hw] at 0x80004928
  apply st_80004928 hlive
  · bsimp []; bc_addr
  · bsimp []; exact hgl
  have wg' : ldv .ld (writeLog Mt [(x.rep.p + 12, 4, 0#64)]) 2147601840 =
      BitVec.ofNat 64 (deadHead F) := by
    rw [ldv_ld_miss _ _ (by omega)]; exact wg
  have wq2 : ldv .ld (writeLog (writeLog Mt [(x.rep.p + 12, 4, 0#64)])
      [(x.rep.p + 16, 8, BitVec.ofNat 64 (deadHead F))]) q = BitVec.ofNat 64 x.rep.p := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hw
  bsimp [wg']
  bc_run hlive hS [h10, hw, wq2, ldv_ld_miss]
  all_goals first | exact hq.acc | exact hgl | exact hal | bc_addr | skip
  have hfin : x.sb.fin = x.rep.p + x.sb.sz := by rw [hpp]
  refine hk.rel hr1 _ _ H (by keeps_tac Keeps.refl _ _) (release_post_view e hv ?_ ?_ ?_ ?_)
  · intro a h1 h2 h3
    simp only [Blk.In, ← hpp, hfin] at h1
    simp only [slotBytes] at h2
    simp only [bcFreeBytes, bcFreeAddr] at h3
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  · rw [← hpp]; simp only [bcFreeAddr]
    rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _
  · rw [← hpp, ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
    exact ldv_store_hit _ _ _
  · exact ldv_store_hit _ _ _

/-- The memory after one reference fewer: the count lowered, the slot cleared. -/
abbrev decMem (Mt : Mem) (x : NumObj) (q : Nat) : Mem :=
  writeLog (writeLog Mt [(x.rep.p + 12, 4, BitVec.ofNat 64 (x.rep.refs - 1))]) [(q, 8, 0#64)]

/-- One reference fewer keeps the number heap, with `x` decremented. -/
theorem free_num_dec_heap {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} {q sp : Nat} (e : FreeEntry S X Mt H F L1 L2 x q sp)
    (hr2 : 2 ≤ x.rep.refs) : BcHeap S X (decMem Mt x q) H F (L1 ++ x.decRef :: L2) := by
  have h := e.heap
  have hi := h.heap
  have hx := e.mem
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  num_facts hn
  have hq := e.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hpp : x.rep.p = x.sb.pay := hxb.sPay
  have hqs := e.slot_apart
  have hsz := hxb.sSz
  have hsfin : x.sb.fin = x.sb.pay + x.sb.sz := rfl
  have hset := hn.setRefs (v := BitVec.ofNat 64 (x.rep.refs - 1)) (k := x.rep.refs - 1)
    (toNat_ofNat_mod32 (by omega)) (by omega)
  refine BcHeap.update h rfl rfl rfl
    ⟨hxb.sLive, hxb.dLive, hxb.sPay, hxb.sSz, hxb.dPay, hxb.dLo, hxb.dFit⟩
    (hset.frame fun a ha => ?_) (P := fun a => refsBytes x.rep a ∨ slotBytes q a) ?_ ?_
  · refine imgM_store_miss _ _ ?_
    have hs := e.off.blocks x.sb (List.mem_append_right _ (mem_objBlocks hx))
    have hd := e.off.blocks x.db (List.mem_append_right _ (h.db_mem hx))
    have hfa := NumObj.foot_blocks hn hxb (a := a) ha
    by_cases hsq : slotBytes q a
    · rcases hfa with h1 | h1
      · exact absurd h1 (hs a hsq)
      · exact absurd h1 (hd a hsq)
    · simp only [slotBytes] at hsq; omega
  · intro a ha
    simp only [not_or, refsBytes, slotBytes, NumObj.decRef] at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  · intro a ha
    rcases ha with ha | ha
    · exact h.sb_writeOK ⟨by omega, by omega⟩
    · refine ⟨e.off.alloc a ha, ?_, fun b hb => e.off.blocks b (List.mem_append_left _ hb) a ha,
        fun y hy => e.off.blocks _ (List.mem_append_right _ (mem_objBlocks (mem_split hy))) a ha,
        fun y hy => e.off.blocks _ (List.mem_append_right _ (h.db_mem (mem_split hy))) a ha,
        fun b hb => e.off.raw b hb a ha⟩
      have := e.off.glob; simp only [bcFreeBytes]; omega

/-- One reference fewer writes only the count and the slot. -/
theorem free_num_dec_frame {Mt : Mem} {x : NumObj} {q : Nat} :
    MemOnly (fun a => refsBytes x.rep a ∨ slotBytes q a) (decMem Mt x q) Mt := by
  intro a ha
  simp only [not_or] at ha
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]

/-- **`bc_free_num(num)`** at `0x800048c0` on a slot holding the object `x`
(`L = L1 ++ x :: L2`, `n_refs ≥ 1`): `FreeNumK.dec` when references remain,
`FreeNumK.rel` (`ReleasePost`) for the last one; clobbers `a0`, `a3`–`a5`. -/
theorem bc_free_num_spec {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {q sp : Nat} (e : FreeEntry S X Mt H F L1 L2 x q sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0) (hk : FreeNumK live S X Q R Mt H F L1 L2 x q sp) :
    DW live S Q 0x800048c0#64 R Mt := by
  have h := e.heap
  have hi := h.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hx := e.mem
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  num_facts hn
  have hq := e.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hrf := hn.refs
  have hw := e.word
  have hpp : x.rep.p = x.sb.pay := hxb.sPay
  have hqs := e.slot_apart
  have hsz := hxb.sSz
  have hsfin : x.sb.fin = x.sb.pay + x.sb.sz := rfl
  rcases (show x.rep.refs = 1 ∨ 2 ≤ x.rep.refs from by have := e.refs; omega) with hr1 | hr2
  · by_cases ho : x.Owns
    · exact free_num_release hlive e R h10 h2 hal hk hr1 ho
    · exact free_num_view hlive e R h10 hal hk hr1 ho
  · -- one reference fewer
    bc_run hlive hS [h10, hw, hrf] at 0x8000493c
    all_goals first | exact hq.acc | skip
    all_goals try (intro hc; bv_nat at hc; omega)
    intro _
    have hpr : BitVec.ofNat 64 x.rep.refs + 18446744073709551615#64 =
        BitVec.ofNat 64 (x.rep.refs - 1) := word_pred (by omega)
    have hsx : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (x.rep.refs - 1))) =
        BitVec.ofNat 64 (x.rep.refs - 1) := sxw_ofNat (by omega)
    bc_run hlive hS [h10, hw, hrf, hpr, hsx] at 0x8000493c
    all_goals first | exact hq.acc | skip
    all_goals intro hc
    all_goals try (exact absurd ((ofNat_eq_iff (x := x.rep.refs - 1) (y := 0)
      (by omega) (by omega)).mp (Classical.not_not.mp hc)) (by omega))
    refine free_num_clear hlive hq _ ?_ ?_ ?_
    · bsimp [h10]
    · bsimp [hal]
    bsimp []
    refine hk.dec hr2 _ _ (by keeps_tac Keeps.refl _ _) (free_num_dec_heap e hr2)
      (ldv_store_hit _ _ _) free_num_dec_frame

end Dc.Mach
