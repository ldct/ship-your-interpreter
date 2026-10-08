import Dc.Mach.Bc.Base

/-!
# The heap of number objects (M3)

`lib/number.c` keeps every `bc_num` in two `malloc` blocks: the 40-byte
struct and the digit buffer `n_ptr`. A struct whose reference count reached
zero goes to `_bc_Free_list` (linked through `n_next` at `+16`) with its
digits freed; `bc_new_num` reuses it.

- `DeadChain Mt a F`: the list `F` of dead struct blocks threaded from the
  pointer word at `a` through `n_next`.
- `NumObj`: a number object with its two blocks; `NumObj.Blocks H x`: both
  are live blocks of the allocator heap `H`, the struct fits its block and
  the digits lie in the buffer's block. An object owns its digit block
  (`Owns`: `n_ptr` its payload) or is a view (`new_sub_num`: `n_ptr = NULL`,
  the digits inside another object's block).
- `BcHeap S Mt H F L`: the allocator invariant, the dead chain `F`, and the
  live number objects `L` (each `NumAt`), with every struct block and owned
  digit block of `F` and `L` distinct (`objBlocks`), and every view's digit
  block owned by a later object of `L` (`ViewsOwned`). Reference counts
  are the objects' `n_refs`; that they count the
  references held by dc's state is part of dc's state representation (M9).
- Footprints: `NumObj.foot_blocks` (a number's bytes lie in its blocks),
  `BcHeap.foot_disjoint` (distinct objects have disjoint footprints),
  `BcHeap.foot_not_alloc` (no number byte is an allocator byte).
- Frames: `LiveFrame H sb Mt' Mt` (every live payload of `H` but `sb`'s is
  unchanged) and `OutFrame fr Mt' Mt` (every byte outside the heap, the
  allocator's and `_bc_Free_list`'s words, and `fr` is unchanged); a
  `BcHeap` survives both (`BcHeap.transport`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `_bc_Free_list`: dead structs threaded through `n_next` (`+16`), ending in `NULL`. -/
inductive DeadChain (Mt : Mem) : Nat → List Blk → Prop
  | nil {a : Nat} : ldv .ld Mt a = 0#64 → DeadChain Mt a []
  | cons {a : Nat} {b : Blk} {l : List Blk} : ldv .ld Mt a = BitVec.ofNat 64 b.pay →
      DeadChain Mt (b.pay + 16) l → DeadChain Mt a (b :: l)

/-- The value of a chain's first word: its head's payload, or `NULL`. -/
def deadHead : List Blk → Nat
  | [] => 0
  | b :: _ => b.pay

theorem DeadChain.head {Mt : Mem} {a : Nat} {l : List Blk} (h : DeadChain Mt a l) :
    ldv .ld Mt a = BitVec.ofNat 64 (deadHead l) := by
  cases h with
  | nil h0 => exact h0
  | cons h0 _ => exact h0

/-- A chain survives a memory agreeing on its first word and on the link words
of its blocks. -/
theorem DeadChain.frame {Mt Mt' : Mem} :
    ∀ {a : Nat} {l : List Blk}, DeadChain Mt a l →
      ldv .ld Mt' a = ldv .ld Mt a →
      (∀ b ∈ l, ∀ j, j < 8 → imgM Mt' (b.pay + 16 + j) = imgM Mt (b.pay + 16 + j)) →
      DeadChain Mt' a l
  | _, _, .nil h, ha, _ => .nil (ha.trans h)
  | _, _, .cons h hl, ha, hb =>
    .cons (ha.trans h) (hl.frame (ldv_congr .ld fun j hj => hb _ List.mem_cons_self j hj)
      fun c hc => hb c (List.mem_cons_of_mem _ hc))

/-- A number object with its struct block `sb` and digit block `db`. A view
(`new_sub_num`, `n_ptr = NULL`) reads its digits inside `db`, the buffer of
the object it was cut from. -/
structure NumObj where
  rep : NumRep
  sb : Blk
  db : Blk

/-- `x` owns its digit buffer (`n_ptr ≠ NULL`); otherwise it is a view. -/
abbrev NumObj.Owns (x : NumObj) : Prop := x.rep.ptr ≠ 0

/-- The two blocks of `x`, live in `H`, hold its struct and digits. -/
structure NumObj.Blocks (H : Heap) (x : NumObj) : Prop where
  sLive : x.sb ∈ H.live
  dLive : x.db ∈ H.live
  sPay : x.rep.p = x.sb.pay
  sSz : 40 ≤ x.sb.sz
  /-- an owned buffer is `n_ptr` -/
  dPay : x.Owns → x.rep.ptr = x.db.pay
  dLo : x.db.pay ≤ x.rep.val
  dFit : x.rep.val + x.rep.len + x.rep.scale ≤ x.db.fin

/-- The blocks an object owns: its struct, and its digit buffer unless it is
a view. -/
def NumObj.blocks (x : NumObj) : List Blk := if x.rep.ptr = 0 then [x.sb] else [x.sb, x.db]

/-- The blocks of a list of objects. -/
def objBlocks (L : List NumObj) : List Blk := L.flatMap NumObj.blocks

theorem NumObj.blocks_own {x : NumObj} (h : x.Owns) : x.blocks = [x.sb, x.db] := by
  simp only [NumObj.blocks, h, ite_false]

theorem NumObj.blocks_view {x : NumObj} (h : x.rep.ptr = 0) : x.blocks = [x.sb] := by
  simp only [NumObj.blocks, h, ite_true]

theorem NumObj.sb_mem_blocks (x : NumObj) : x.sb ∈ x.blocks := by
  unfold NumObj.blocks; split <;> simp

theorem mem_objBlocks {L : List NumObj} {x : NumObj} (hx : x ∈ L) : x.sb ∈ objBlocks L :=
  List.mem_flatMap.mpr ⟨x, hx, x.sb_mem_blocks⟩

theorem mem_objBlocks_db {L : List NumObj} {x : NumObj} (hx : x ∈ L) (ho : x.Owns) :
    x.db ∈ objBlocks L :=
  List.mem_flatMap.mpr ⟨x, hx, by rw [NumObj.blocks_own ho]; simp⟩

theorem objBlocks_cons (x : NumObj) (L : List NumObj) :
    objBlocks (x :: L) = x.blocks ++ objBlocks L := by
  simp only [objBlocks, List.flatMap_cons]

theorem objBlocks_append (L1 L2 : List NumObj) :
    objBlocks (L1 ++ L2) = objBlocks L1 ++ objBlocks L2 := by
  simp only [objBlocks, List.flatMap_append]

/-- Every view's digit buffer is owned by an object after it in the list
(views are cut from objects already present). -/
inductive ViewsOwned : List NumObj → Prop
  | nil : ViewsOwned []
  | cons {x : NumObj} {L : List NumObj} :
      (x.Owns ∨ ∃ w ∈ L, w.Owns ∧ w.db = x.db) → ViewsOwned L → ViewsOwned (x :: L)

theorem ViewsOwned.owner : ∀ {L : List NumObj}, ViewsOwned L → ∀ {x : NumObj}, x ∈ L →
    ∃ w ∈ L, w.Owns ∧ w.db = x.db
  | _, .cons hx hL, _, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · rcases hx with ho | ⟨w, hw, ho, he⟩
      · exact ⟨_, List.mem_cons_self, ho, rfl⟩
      · exact ⟨w, List.mem_cons_of_mem _ hw, ho, he⟩
    · obtain ⟨w, hw, ho, he⟩ := hL.owner hm
      exact ⟨w, List.mem_cons_of_mem _ hw, ho, he⟩

/-- An object replaced by one with the same buffer and ownership. -/
theorem ViewsOwned.replace {x x' : NumObj} (hp : x'.rep.ptr = x.rep.ptr) (hd : x'.db = x.db) :
    ∀ {L1 L2 : List NumObj}, ViewsOwned (L1 ++ x :: L2) → ViewsOwned (L1 ++ x' :: L2)
  | [], _, .cons hx hL => .cons (by simpa only [NumObj.Owns, hp, hd] using hx) hL
  | y :: L1, L2, .cons hy hL => by
    refine .cons ?_ (ViewsOwned.replace hp hd hL)
    rcases hy with ho | ⟨w, hw, ho, he⟩
    · exact .inl ho
    · rcases List.mem_append.mp hw with hw | hw
      · exact .inr ⟨w, List.mem_append_left _ hw, ho, he⟩
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact .inr ⟨x', List.mem_append_right _ List.mem_cons_self,
            by simpa only [NumObj.Owns, hp] using ho, hd.trans he⟩
        · exact .inr ⟨w, List.mem_append_right _ (List.mem_cons_of_mem _ hw), ho, he⟩

/-- An object removed: no view before it reads its buffer. -/
theorem ViewsOwned.remove {x : NumObj} :
    ∀ {L1 L2 : List NumObj}, ViewsOwned (L1 ++ x :: L2) →
      (x.Owns → ∀ y ∈ L1, y.db ≠ x.db) → ViewsOwned (L1 ++ L2)
  | [], _, .cons _ hL, _ => hL
  | y :: L1, L2, .cons hy hL, hnv => by
    refine .cons ?_ (ViewsOwned.remove hL fun ho z hz => hnv ho z (List.mem_cons_of_mem _ hz))
    rcases hy with ho | ⟨w, hw, ho, he⟩
    · exact .inl ho
    · rcases List.mem_append.mp hw with hw | hw
      · exact .inr ⟨w, List.mem_append_left _ hw, ho, he⟩
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact absurd he.symm (hnv ho y List.mem_cons_self)
        · exact .inr ⟨w, List.mem_append_right _ hw, ho, he⟩

/-- A byte of a block's payload. -/
abbrev Blk.In (b : Blk) (a : Nat) : Prop := b.pay ≤ a ∧ a < b.fin

/-- **The number heap.** -/
structure BcHeap (S : Nat → Prop) (Mt : Mem) (H : Heap) (F : List Blk) (L : List NumObj) :
    Prop where
  heap : HeapInv S Mt H
  dead : DeadChain Mt bcFreeAddr F
  deadLive : ∀ b ∈ F, b ∈ H.live ∧ 40 ≤ b.sz
  nums : ∀ x ∈ L, NumAt Mt x.rep
  blocks : ∀ x ∈ L, x.Blocks H
  distinct : (F ++ objBlocks L).Nodup
  views : ViewsOwned L
  globOwn : ∀ a, bcFreeAddr ≤ a → a < bcFreeAddr + 8 → S a

/-- Every object's digit block is a block of the heap's objects. -/
theorem BcHeap.db_mem {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    (h : BcHeap S Mt H F L) {x : NumObj} (hx : x ∈ L) : x.db ∈ objBlocks L := by
  obtain ⟨w, hw, ho, he⟩ := h.views.owner hx
  rw [← he]; exact mem_objBlocks_db hw ho

/-- Blocks of two different objects of a list of distinct blocks differ. -/
theorem objBlocks_separate {L : List NumObj} (hd : (objBlocks L).Nodup)
    {x y : NumObj} (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y)
    {b c : Blk} (hb : b ∈ x.blocks) (hc : c ∈ y.blocks) : b ≠ c := by
  induction L with
  | nil => cases hx
  | cons z L ih =>
    have hd' : (z.blocks ++ objBlocks L).Nodup := hd
    obtain ⟨_, ht, hcross⟩ := List.nodup_append.mp hd'
    rcases List.mem_cons.mp hx with rfl | hxt
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact False.elim (hne rfl)
      · exact hcross b hb c (List.mem_flatMap.mpr ⟨y, hy, hc⟩)
    · rcases List.mem_cons.mp hy with rfl | hyt
      · exact fun he => hcross c hc b (List.mem_flatMap.mpr ⟨x, hxt, hb⟩) he.symm
      · exact ih ht hxt hyt

/-- One object's blocks are distinct. -/
theorem objBlocks_blocks_nodup {L : List NumObj} (hd : (objBlocks L).Nodup) {x : NumObj}
    (hx : x ∈ L) : x.blocks.Nodup := by
  induction L with
  | nil => cases hx
  | cons z L ih =>
    have hd' : (z.blocks ++ objBlocks L).Nodup := hd
    obtain ⟨hz, ht, _⟩ := List.nodup_append.mp hd'
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact hz
    · exact ih ht hxt

/-- A struct block is no owned digit buffer. -/
theorem objBlocks_sb_ne_db {L : List NumObj} (hd : (objBlocks L).Nodup) {x w : NumObj}
    (hx : x ∈ L) (hw : w ∈ L) (ho : w.Owns) : x.sb ≠ w.db := by
  by_cases hxw : x = w
  · subst hxw
    have hn := objBlocks_blocks_nodup hd hx
    rw [NumObj.blocks_own ho] at hn
    simpa using hn
  · exact objBlocks_separate hd hx hw hxw x.sb_mem_blocks (by rw [NumObj.blocks_own ho]; simp)

/-- Two objects' structs differ. -/
theorem objBlocks_sb_ne_sb {L : List NumObj} (hd : (objBlocks L).Nodup) {x y : NumObj}
    (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y) : x.sb ≠ y.sb :=
  objBlocks_separate hd hx hy hne x.sb_mem_blocks y.sb_mem_blocks

/-- Two owners' digit buffers differ. -/
theorem objBlocks_db_ne_db {L : List NumObj} (hd : (objBlocks L).Nodup) {x y : NumObj}
    (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y) (hox : x.Owns) (hoy : y.Owns) : x.db ≠ y.db :=
  objBlocks_separate hd hx hy hne (by rw [NumObj.blocks_own hox]; simp)
    (by rw [NumObj.blocks_own hoy]; simp)

/-- A struct block is no digit buffer of the heap. -/
theorem BcHeap.sb_ne_db {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    (h : BcHeap S Mt H F L) {x y : NumObj} (hx : x ∈ L) (hy : y ∈ L) : x.sb ≠ y.db := by
  obtain ⟨w, hw, ho, he⟩ := h.views.owner hy
  rw [← he]
  exact objBlocks_sb_ne_db (List.nodup_append.mp h.distinct).2.1 hx hw ho

/-- The owner at the head of the heap lends its buffer to no other object. -/
theorem BcHeap.head_noView {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {x : NumObj} {L : List NumObj} (h : BcHeap S Mt H F (x :: L)) (ho : x.Owns) :
    ∀ y ∈ L, y.db ≠ x.db := by
  intro y hy e
  have hL : ViewsOwned L := by cases h.views with | cons _ hL => exact hL
  obtain ⟨w, hw, hwo, he⟩ := hL.owner hy
  have hd := (List.nodup_append.mp h.distinct).2.1
  have hne : x ≠ w := fun hxw => by
    subst hxw
    have hn : (x.blocks ++ objBlocks L).Nodup := hd
    exact (List.nodup_append.mp hn).2.2 x.sb x.sb_mem_blocks x.sb (mem_objBlocks hw) rfl
  exact objBlocks_db_ne_db hd List.mem_cons_self (List.mem_cons_of_mem _ hw) hne ho hwo
    (he.trans e).symm

/-! ## Footprints -/

/-- A number's bytes lie in its two blocks. -/
theorem NumObj.foot_blocks {Mt : Mem} {H : Heap} {x : NumObj} (_h : NumAt Mt x.rep)
    (hb : x.Blocks H) {a : Nat} (ha : x.rep.Foot a) : x.sb.In a ∨ x.db.In a := by
  have := hb.sPay; have := hb.sSz; have := hb.dLo; have := hb.dFit
  simp only [Blk.In, Blk.fin, Blk.pay] at *
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨by omega, by omega⟩
  · exact .inr ⟨by omega, by omega⟩

/-- Distinct live blocks have disjoint payloads. -/
theorem live_apart {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {b c : Blk}
    (hb : b ∈ H.live) (hc : c ∈ H.live) (hne : b ≠ c) {a : Nat} (h1 : b.In a) (h2 : c.In a) :
    False := by
  have := apart_of_mem hi.apart (List.mem_append_right _ hb) (List.mem_append_right _ hc) hne
  simp only [Blk.In, Blk.Apart, Blk.fin, Blk.pay] at *; omega

/-- A chain moved to a new first word holding the same pointer, its link words
unchanged. -/
theorem DeadChain.move {Mt Mt' : Mem} {a a' : Nat} {l : List Blk} (h : DeadChain Mt a l)
    (ha : ldv .ld Mt' a' = ldv .ld Mt a)
    (hb : ∀ b ∈ l, ∀ j, j < 8 → imgM Mt' (b.pay + 16 + j) = imgM Mt (b.pay + 16 + j)) :
    DeadChain Mt' a' l := by
  cases h with
  | nil h0 => exact .nil (ha.trans h0)
  | cons h0 hl =>
    exact .cons (ha.trans h0) (hl.frame (ldv_congr .ld fun j hj => hb _ List.mem_cons_self j hj)
      fun c hc => hb c (List.mem_cons_of_mem _ hc))

/-- A block consed onto the live list is not in the rest of it. -/
theorem HeapInv.head_not_mem {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {b : Blk} {L : List Blk} (e : H.live = b :: L) : b ∉ L := fun hb => by
  have hp := hi.apart
  rw [Heap.blocks, e] at hp
  have := (List.pairwise_cons.1 (List.pairwise_append.1 hp).2.1).1 b hb
  exact Blk.Apart.irrefl b this

/-- A live payload byte is not an allocator byte. -/
theorem live_not_alloc {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {b : Blk}
    (hb : b ∈ H.live) {a : Nat} (h : b.In a) : ¬ AllocByte H a :=
  (hi.live_fresh hb h.1 h.2).1

/-- An allocator byte is `free_list`/`brk_ptr` or in the heap. -/
theorem AllocByte.glob_or_heap {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {a : Nat} (h : AllocByte H a) :
    (freeListAddr ≤ a ∧ a < freeListAddr + 16) ∨ (heapStart ≤ a ∧ a < heapEnd) := by
  have hb := AllocByte.bound hi h
  cases h with
  | glob h1 h2 => exact .inl ⟨h1, h2⟩
  | hdr b hb' h1 h2 => exact .inr ⟨Nat.le_trans (hi.lo b hb') h1, hb.2⟩
  | freePay b hb' h1 h2 =>
    exact .inr ⟨Nat.le_trans (hi.lo b (List.mem_append_left _ hb')) (by simp only [Blk.pay] at h1; omega), hb.2⟩
  | top h1 h2 => exact .inr ⟨Nat.le_trans hi.brk_lo h1, h2⟩

/-! ## Frames -/

/-- A byte outside the heap and the allocator's and `_bc_Free_list`'s words. -/
def OutHeap (a : Nat) : Prop :=
  ¬ (heapStart ≤ a ∧ a < heapEnd) ∧ ¬ (freeListAddr ≤ a ∧ a < freeListAddr + 16) ∧
    ¬ (bcFreeAddr ≤ a ∧ a < bcFreeAddr + 8)

/-- Every byte outside the heap, the globals and `fr` is unchanged. -/
def OutFrame (fr : Nat → Prop) (Mt' Mt : Mem) : Prop :=
  ∀ a, OutHeap a → ¬ fr a → imgM Mt' a = imgM Mt a

/-- Every live payload byte of `H` outside `sb` is unchanged. -/
def LiveFrame (H : Heap) (sb : Blk) (Mt' Mt : Mem) : Prop :=
  ∀ c ∈ H.live, c ≠ sb → ∀ a, c.In a → imgM Mt' a = imgM Mt a

/-- A non-allocator byte survives `malloc`/`free` (their `frame`). -/
theorem OutHeap.not_alloc {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {a : Nat}
    (h : OutHeap a) : ¬ AllocByte H a := fun ha => by
  rcases AllocByte.glob_or_heap hi ha with h1 | h1
  · exact h.2.1 h1
  · exact h.1 h1

/-- The `n` bytes of stack frame below `sp`. -/
abbrev frameIn (sp n a : Nat) : Prop := sp - n ≤ a ∧ a < sp

/-- An access inside a stack frame owns its bytes. -/
theorem frame_acc {S : Nat → Prop} {sp n : Nat} (hsf : StackFrame S sp n) {a w : Nat}
    (h1 : sp - n ≤ a) (h2 : a + w ≤ sp) : ∀ b ∈ accAddrs a w, S b := fun b hb => by
  have := of_mem_accAddrs hb; exact hsf.own b (by omega) (by omega)

/-! ## `bc_new_num`'s result -/

/-- The object `bc_new_num(len, scale)` builds: positive, `n_refs = 1`, all
digits zero, `n_value = n_ptr`. -/
def zeroRep (p ptr len scale : Nat) : NumRep :=
  ⟨p, ptr, ptr, false, len, scale, 1, List.replicate (len + scale) 0⟩

/-- Where `bc_new_num`'s blocks come from: the struct is the dead chain's head
(`reuse`) or fresh (`fresh`, the chain empty); the digit buffer is fresh. -/
inductive NewSrc (H H' : Heap) (F F' : List Blk) (x : NumObj) : Prop
  | reuse : F = x.sb :: F' → H'.live = x.db :: H.live → NewSrc H H' F F' x
  | fresh : F = [] → F' = [] → H'.live = x.db :: x.sb :: H.live → NewSrc H H' F F' x

/-- `bc_new_num`'s postcondition. -/
structure NewNumPost (S : Nat → Prop) (Mt Mt' : Mem) (H H' : Heap) (F F' : List Blk)
    (fr : Nat → Prop) (len scale : Nat) (x : NumObj) : Prop where
  inv : HeapInv S Mt' H'
  dead : DeadChain Mt' bcFreeAddr F'
  num : NumAt Mt' x.rep
  rep : x.rep = zeroRep x.sb.pay x.db.pay len scale
  sSz : 40 ≤ x.sb.sz
  dSz : len + scale ≤ x.db.sz
  src : NewSrc H H' F F' x
  live : LiveFrame H x.sb Mt' Mt
  out : OutFrame fr Mt' Mt

end Dc.Mach
