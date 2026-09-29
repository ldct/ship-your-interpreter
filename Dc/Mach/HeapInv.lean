import Dc.Mach.Stdio

/-!
# dc's heap: the invariant of `malloc`/`free`/`realloc`

`dc-port/libc/libc.c`'s allocator: a 16-byte header before each block (the
payload size at `h`, the free-list link at `h + 8`), a first-fit free list
headed at `free_list` (blocks reused whole), and a bump pointer `brk_ptr`
from the aligned `_end` (`heapStart`) to `__heap_end` (`heapEnd`); `brk_ptr`
is `0` until the first bump.

The abstract heap `Heap` lists the free blocks in free-list order and the live
(allocated) blocks; `HeapInv S Mt H` says `Mt` represents it. `AllocByte H`
are the allocator's bytes (the globals, every header, the free payloads, the
unused top); a client owns the payloads of its live blocks.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `free_list` (`.bss`). -/
abbrev freeListAddr : Nat := 0x8001cd48
/-- `brk_ptr` (`.bss`). -/
abbrev brkAddr : Nat := 0x8001cd50
/-- `_end` rounded up to 16: the first header. -/
abbrev heapStart : Nat := 0x8001d5d0
/-- `__heap_end`. -/
abbrev heapEnd : Nat := 0x87800000

/-- The allocator's addresses as literals, for `omega`. -/
macro "heap_consts" : tactic =>
  `(tactic| (have _hc1 : freeListAddr = 2147601736 := rfl
             have _hc2 : brkAddr = 2147601744 := rfl
             have _hc3 : heapStart = 2147603920 := rfl
             have _hc4 : heapEnd = 2273312768 := rfl))

/-- `omega` after reducing structure projections. -/
macro "homega" : tactic => `(tactic| ((try dsimp only at *); omega))

/-- A block: header at `h`, `sz` payload bytes at `h + 16`. -/
structure Blk where
  h : Nat
  sz : Nat
  deriving DecidableEq

/-- The payload address (what `malloc` returns). -/
abbrev Blk.pay (b : Blk) : Nat := b.h + 16
/-- The end of the block. -/
abbrev Blk.fin (b : Blk) : Nat := b.h + 16 + b.sz

/-- Two blocks do not overlap. -/
def Blk.Apart (b c : Blk) : Prop := b.fin ≤ c.h ∨ c.fin ≤ b.h

theorem Blk.Apart.symm {b c : Blk} (h : b.Apart c) : c.Apart b := Or.symm h

/-- `omega` after unfolding block arithmetic and apartness. -/
macro "bomega" : tactic =>
  `(tactic| ((try simp only [Blk.pay, Blk.fin, Blk.Apart] at *); heap_consts; have _htx : tohostAddr = 0x8001ad00 := rfl; omega))

/-- The abstract heap: the raw `brk_ptr`, the free list, the live blocks. -/
structure Heap where
  braw : Nat
  free : List Blk
  live : List Blk

/-- The bump pointer (`heapStart` before the first bump). -/
def Heap.brk (H : Heap) : Nat := if H.braw = 0 then heapStart else H.braw

/-- Every block. -/
abbrev Heap.blocks (H : Heap) : List Blk := H.free ++ H.live

/-- The free list, threaded from the pointer word at `a` through the blocks'
link words (`h + 8`), ending in `NULL`. -/
inductive Chain (Mt : Mem) : Nat → List Blk → Prop
  | nil {a : Nat} : ldv .ld Mt a = 0#64 → Chain Mt a []
  | cons {a : Nat} {b : Blk} {l : List Blk} : ldv .ld Mt a = BitVec.ofNat 64 b.h →
      Chain Mt (b.h + 8) l → Chain Mt a (b :: l)

/-- **The heap invariant.** -/
structure HeapInv (S : Nat → Prop) (Mt : Mem) (H : Heap) : Prop where
  brkWord : ldv .ld Mt brkAddr = BitVec.ofNat 64 H.braw
  brkZero : H.braw = 0 → H.blocks = []
  brkLo : H.braw ≠ 0 → heapStart ≤ H.braw
  brkHi : H.braw ≤ heapEnd
  brkAl : H.braw % 16 = 0
  links : Chain Mt freeListAddr H.free
  hdr : ∀ b ∈ H.blocks, ldv .ld Mt b.h = BitVec.ofNat 64 b.sz
  hAl : ∀ b ∈ H.blocks, b.h % 16 = 0
  szAl : ∀ b ∈ H.blocks, b.sz % 16 = 0
  lo : ∀ b ∈ H.blocks, heapStart ≤ b.h
  hi : ∀ b ∈ H.blocks, b.fin ≤ H.brk
  apart : H.blocks.Pairwise Blk.Apart
  own : ∀ a, heapStart ≤ a → a < heapEnd → S a
  globOwn : ∀ a, freeListAddr ≤ a → a < freeListAddr + 16 → S a

/-- The allocator's bytes. -/
inductive AllocByte (H : Heap) (a : Nat) : Prop
  | glob : freeListAddr ≤ a → a < freeListAddr + 16 → AllocByte H a
  | hdr (b : Blk) : b ∈ H.blocks → b.h ≤ a → a < b.pay → AllocByte H a
  | freePay (b : Blk) : b ∈ H.free → b.pay ≤ a → a < b.fin → AllocByte H a
  | top : H.brk ≤ a → a < heapEnd → AllocByte H a

/-! ## Arithmetic of the bump pointer -/

theorem Heap.brk_lo (H : Heap) (hinv : H.braw ≠ 0 → heapStart ≤ H.braw) : heapStart ≤ H.brk := by
  unfold Heap.brk; split
  · exact Nat.le_refl _
  · exact hinv ‹_›

theorem Heap.brk_of_ne {H : Heap} (h : H.braw ≠ 0) : H.brk = H.braw := by
  unfold Heap.brk; simp [h]

theorem Heap.brk_of_eq {H : Heap} (h : H.braw = 0) : H.brk = heapStart := by
  unfold Heap.brk; simp [h]

theorem HeapInv.brk_hi {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) :
    H.brk ≤ heapEnd := by
  unfold Heap.brk; split
  · decide
  · exact hi.brkHi

theorem HeapInv.brk_lo {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) :
    heapStart ≤ H.brk := H.brk_lo hi.brkLo

theorem HeapInv.brk_al {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) :
    H.brk % 16 = 0 := by
  unfold Heap.brk; split
  · decide
  · exact hi.brkAl

/-! ## The free list in memory -/

/-- The pointer words a chain reads. -/
def chainWords (a : Nat) : List Blk → List Nat
  | [] => [a]
  | b :: l => a :: chainWords (b.h + 8) l

/-- A chain survives any memory that agrees on its pointer words. -/
theorem Chain.frame {Mt Mt' : Mem} :
    ∀ {a : Nat} {l : List Blk}, Chain Mt a l →
      (∀ x ∈ chainWords a l, ldv .ld Mt' x = ldv .ld Mt x) → Chain Mt' a l
  | _, _, .nil h, hw => .nil ((hw _ (by simp [chainWords])).trans h)
  | _, _, .cons h hl, hw =>
    .cons ((hw _ (by simp [chainWords])).trans h)
      (hl.frame fun x hx => hw x (by simp only [chainWords]; exact List.mem_cons_of_mem _ hx))

/-- The address of the pointer word after a prefix of the chain. -/
def linkOf (a : Nat) : List Blk → Nat
  | [] => a
  | b :: l => linkOf (b.h + 8) l

/-- The pointer words of a prefix before its last link. -/
def preWords (a : Nat) : List Blk → List Nat
  | [] => []
  | b :: l => a :: preWords (b.h + 8) l

theorem mem_chainWords {a x : Nat} :
    ∀ {l : List Blk}, x ∈ chainWords a l → x = a ∨ ∃ c ∈ l, x = c.h + 8
  | [], hx => by simp [chainWords] at hx; exact .inl hx
  | b :: l, hx => by
    simp only [chainWords, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact .inl rfl
    · rcases mem_chainWords hx with rfl | ⟨c, hc, rfl⟩
      · exact .inr ⟨b, List.mem_cons_self, rfl⟩
      · exact .inr ⟨c, List.mem_cons_of_mem _ hc, rfl⟩

/-- A chain moved to a new pointer word `y` holding the old head's pointer. -/
theorem Chain.move {Mt Mt' : Mem} {x y : Nat} {l : List Blk} (h : Chain Mt x l)
    (hy : ldv .ld Mt' y = ldv .ld Mt x)
    (hl : ∀ c ∈ l, ldv .ld Mt' (c.h + 8) = ldv .ld Mt (c.h + 8)) : Chain Mt' y l := by
  cases h with
  | nil h0 => exact .nil (hy.trans h0)
  | @cons _ b l' h0 h1 =>
    refine .cons (hy.trans h0) (h1.frame fun z hz => ?_)
    rcases mem_chainWords hz with rfl | ⟨c, hc, rfl⟩
    · exact hl b List.mem_cons_self
    · exact hl c (List.mem_cons_of_mem _ hc)

/-- The head of the rest of the list, as `free_list`/a link word stores it. -/
def headOf : List Blk → Nat
  | [] => 0
  | b :: _ => b.h

/-- A chain's first word holds its head. -/
theorem Chain.head {Mt : Mem} {a : Nat} {l : List Blk} (h : Chain Mt a l) :
    ldv .ld Mt a = BitVec.ofNat 64 (headOf l) := by
  cases h with
  | nil h0 => exact h0
  | cons h0 _ => exact h0

/-- **Unlinking** a block from the chain: the pointer word before it takes the
block's link, every other pointer word is unchanged. -/
theorem Chain.unlink {Mt Mt' : Mem} :
    ∀ (pre : List Blk) (a : Nat) (b : Blk) (post : List Blk),
      Chain Mt a (pre ++ b :: post) →
      ldv .ld Mt' (linkOf a pre) = ldv .ld Mt (b.h + 8) →
      (∀ x ∈ preWords a pre, ldv .ld Mt' x = ldv .ld Mt x) →
      (∀ c ∈ post, ldv .ld Mt' (c.h + 8) = ldv .ld Mt (c.h + 8)) →
      Chain Mt' a (pre ++ post)
  | [], a, b, post, h, hw, _, hpost => by
    cases h with
    | cons _ h1 => exact h1.move hw hpost
  | c :: pre, a, b, post, h, hw, hpre, hpost => by
    cases h with
    | cons h0 h1 =>
      refine .cons ((hpre a (by simp [preWords])).trans h0) ?_
      exact Chain.unlink pre (c.h + 8) b post h1 hw
        (fun x hx => hpre x (by simp only [preWords]; exact List.mem_cons_of_mem _ hx)) hpost


/-- A chain's pointer word before `b`, and `b`'s link. -/
theorem Chain.at {Mt : Mem} :
    ∀ (pre : List Blk) {a : Nat} {b : Blk} {post : List Blk}, Chain Mt a (pre ++ b :: post) →
      ldv .ld Mt (linkOf a pre) = BitVec.ofNat 64 b.h ∧
        ldv .ld Mt (b.h + 8) = BitVec.ofNat 64 (headOf post)
  | [], _, _, _, .cons h0 h1 => ⟨h0, h1.head⟩
  | _ :: pre, _, _, _, .cons _ h1 => Chain.at pre h1

theorem linkOf_snoc (a : Nat) (b : Blk) : ∀ pre : List Blk, linkOf a (pre ++ [b]) = b.h + 8
  | [] => rfl
  | c :: pre => by simp only [List.cons_append, linkOf]; exact linkOf_snoc (c.h + 8) b pre

theorem linkOf_mem (a : Nat) : ∀ l : List Blk, linkOf a l = a ∨ ∃ c ∈ l, linkOf a l = c.h + 8
  | [] => .inl rfl
  | c :: l => by
    simp only [linkOf]
    rcases linkOf_mem (c.h + 8) l with e | ⟨d, hd, e⟩
    · exact .inr ⟨c, List.mem_cons_self, e⟩
    · exact .inr ⟨d, List.mem_cons_of_mem _ hd, e⟩

theorem Blk.Apart.irrefl (b : Blk) : ¬ b.Apart b := by
  unfold Blk.Apart Blk.fin; omega

/-- Distinct members of a pairwise-apart list are apart. -/
theorem apart_of_mem {l : List Blk} (hp : l.Pairwise Blk.Apart) {b c : Blk} (hb : b ∈ l)
    (hc : c ∈ l) (hne : b ≠ c) : b.Apart c := by
  induction l with
  | nil => cases hb
  | cons d l ih =>
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hb with h1 | h1 <;> rcases List.mem_cons.mp hc with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1]; exact hp.1 c h2
    · rw [h2]; exact (hp.1 b h1).symm
    · exact ih hp.2 h1 h2

/-- Two words eight bytes apart. -/
abbrev Sep8 (x y : Nat) : Prop := x + 8 ≤ y ∨ y + 8 ≤ x


/-- The pointer words before the last link of a prefix are apart from it. -/
theorem preWords_sep : ∀ (pre : List Blk) (a : Nat), pre.Pairwise Blk.Apart →
    (∀ d ∈ pre, Sep8 a (d.h + 8)) → ∀ x ∈ preWords a pre, Sep8 x (linkOf a pre)
  | [], _, _, _, x, hx => by simp [preWords] at hx
  | c :: pre, a, hp, ha, x, hx => by
    rw [List.pairwise_cons] at hp
    simp only [preWords, List.mem_cons] at hx
    simp only [linkOf]
    rcases hx with rfl | hx
    · rcases linkOf_mem (c.h + 8) pre with e | ⟨d, hd, e⟩
      · rw [e]; exact ha c List.mem_cons_self
      · rw [e]; exact ha d (List.mem_cons_of_mem _ hd)
    · refine preWords_sep pre (c.h + 8) hp.2 (fun d hd => ?_) x hx
      have := hp.1 d hd
      unfold Blk.Apart Blk.fin at this; omega

theorem blocks_perm_take (pre post live : List Blk) (b : Blk) :
    ((pre ++ b :: post) ++ live).Perm ((pre ++ post) ++ b :: live) := by
  have h1 : ((pre ++ b :: post) ++ live).Perm (b :: (pre ++ post ++ live)) := by
    simp
  have h2 : ((pre ++ post) ++ b :: live).Perm (b :: (pre ++ post ++ live)) :=
    List.perm_middle
  exact h1.trans h2.symm

theorem apart_symm : ∀ {b c : Blk}, b.Apart c → c.Apart b := fun h => h.symm

/-- Facts about a block of an invariant heap. -/
structure BlkFacts (H : Heap) (b : Blk) : Prop where
  lo : heapStart ≤ b.h
  fin : b.fin ≤ H.brk
  top : H.brk ≤ heapEnd
  al : b.h % 16 = 0
  szal : b.sz % 16 = 0

theorem HeapInv.blk {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {b : Blk}
    (hb : b ∈ H.blocks) : BlkFacts H b :=
  ⟨hi.lo b hb, hi.hi b hb, hi.brk_hi, hi.hAl b hb, hi.szAl b hb⟩

/-- **Taking** the free block `b` (`malloc`'s first fit): the pointer word
before it takes its link; `b` becomes live. -/
theorem HeapInv.take {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {pre : List Blk} {b : Blk} {post : List Blk} (hf : H.free = pre ++ b :: post) :
    HeapInv S (writeLog Mt [(linkOf freeListAddr pre, 8, BitVec.ofNat 64 (headOf post))])
      ⟨H.braw, pre ++ post, b :: H.live⟩ := by
  heap_consts
  have hp : ((pre ++ b :: post) ++ H.live).Perm ((pre ++ post) ++ b :: H.live) :=
    blocks_perm_take pre post H.live b
  have hbl : H.blocks = (pre ++ b :: post) ++ H.live := by rw [Heap.blocks, hf]
  have hmem : ∀ c, c ∈ ((pre ++ post) ++ b :: H.live) → c ∈ H.blocks := fun c hc => by
    rw [hbl]; exact hp.mem_iff.2 hc
  have hb : b ∈ H.blocks := by rw [hbl]; simp
  have happ := hi.apart
  rw [hbl] at happ
  have hpre : (pre ++ b :: post).Pairwise Blk.Apart := (List.pairwise_append.1 happ).1
  have hpre' := List.pairwise_append.1 hpre
  -- where the link word is
  have hw : linkOf freeListAddr pre = freeListAddr ∨
      ∃ c ∈ pre, linkOf freeListAddr pre = c.h + 8 := linkOf_mem _ _
  have hcpre : ∀ c ∈ pre, c ∈ H.blocks := fun c hc => by rw [hbl]; simp [hc]
  -- every header word is apart from the link word
  have hsepH : ∀ c ∈ H.blocks, Sep8 c.h (linkOf freeListAddr pre) := by
    intro c hc
    have fc := (hi.blk hc).lo
    rcases hw with e | ⟨c0, hc0, e⟩
    · rw [e]; omega
    · rw [e]
      by_cases hcc : c = c0
      · subst hcc; omega
      · have := apart_of_mem hi.apart hc (hcpre c0 hc0) hcc
        unfold Blk.Apart Blk.fin at this; omega
  refine
    { brkWord := ?_, brkZero := ?_, brkLo := hi.brkLo, brkHi := hi.brkHi, brkAl := hi.brkAl,
      links := ?_, hdr := ?_, hAl := fun c hc => hi.hAl c (hmem c hc),
      szAl := fun c hc => hi.szAl c (hmem c hc), lo := fun c hc => hi.lo c (hmem c hc),
      hi := fun c hc => hi.hi c (hmem c hc), apart := ?_, own := hi.own, globOwn := hi.globOwn }
  · have hs : Sep8 brkAddr (linkOf freeListAddr pre) := by
      rcases hw with e | ⟨c0, hc0, e⟩
      · rw [e]; omega
      · rw [e]; have := hi.blk (hcpre c0 hc0); have := this.lo; omega
    rw [ldv_ld_miss _ _ hs]
    exact hi.brkWord
  · intro h0; have := hi.brkZero h0; rw [this] at hb; cases hb
  · have hch := hi.links
    rw [hf] at hch
    refine Chain.unlink pre freeListAddr b post hch ?_ ?_ ?_
    · rw [ldv_store_hit]; exact (Chain.at pre hch).2.symm
    · intro x hx
      refine ldv_ld_miss _ _ ?_
      refine preWords_sep pre freeListAddr hpre'.1 (fun d hd => ?_) x hx
      have := (hi.blk (hcpre d hd)).lo; omega
    · intro c hc
      have hcb : c ∈ H.blocks := by rw [hbl]; simp [hc]
      have fc := (hi.blk hcb).lo
      refine ldv_ld_miss _ _ ?_
      rcases hw with e | ⟨c0, hc0, e⟩
      · rw [e]; omega
      · rw [e]
        have := hpre'.2.2 c0 hc0 c (List.mem_cons_of_mem _ hc)
        unfold Blk.Apart Blk.fin at this; omega
  · intro c hc
    rw [ldv_ld_miss _ _ (hsepH c (hmem c hc))]
    exact hi.hdr c (hmem c hc)
  · show ((pre ++ post) ++ b :: H.live).Pairwise Blk.Apart
    exact (hp.pairwise_iff apart_symm).1 happ


/-- `malloc`'s first bump sets `brk_ptr` to `heapStart`. -/
theorem HeapInv.init {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    (h0 : H.braw = 0) :
    HeapInv S (writeLog Mt [(brkAddr, 8, BitVec.ofNat 64 heapStart)]) ⟨heapStart, H.free, H.live⟩ := by
  heap_consts
  have hbl : H.blocks = [] := hi.brkZero h0
  have hfree : H.free = [] := (List.append_eq_nil_iff.1 hbl).1
  have hlive : H.live = [] := (List.append_eq_nil_iff.1 hbl).2
  have hbl' : (⟨heapStart, H.free, H.live⟩ : Heap).blocks = [] := by simp [hfree, hlive]
  refine
    { brkWord := ldv_store_hit _ _ _, brkZero := fun _ => hbl', brkLo := fun _ => Nat.le_refl _,
      brkHi := by homega, brkAl := by homega, links := ?_, hdr := ?_, hAl := ?_, szAl := ?_,
      lo := ?_, hi := ?_, apart := ?_, own := hi.own, globOwn := hi.globOwn }
  · have hch := hi.links
    rw [hfree] at hch ⊢
    cases hch with
    | nil h => exact .nil (by rw [ldv_ld_miss _ _ (by homega)]; exact h)
  all_goals (try (intro c hc; rw [hbl'] at hc; cases hc))
  rw [hbl']; exact List.Pairwise.nil

/-- **Bumping** `size` bytes (plus the header) at the bump pointer: a new live
block, the header word written, `brk_ptr` advanced. -/
theorem HeapInv.bump {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    (hne : H.braw ≠ 0) {size : Nat} (hsz : size % 16 = 0) (hroom : H.braw + 16 + size ≤ heapEnd) :
    HeapInv S (writeLog (writeLog Mt [(H.braw, 8, BitVec.ofNat 64 size)])
        [(brkAddr, 8, BitVec.ofNat 64 (H.braw + 16 + size))])
      ⟨H.braw + 16 + size, H.free, ⟨H.braw, size⟩ :: H.live⟩ := by
  heap_consts
  have hbrk : H.brk = H.braw := Heap.brk_of_ne hne
  have hlo := hi.brkLo hne
  have hal := hi.brkAl
  have hold : ∀ c ∈ H.blocks, c.fin ≤ H.braw := fun c hc => hbrk ▸ hi.hi c hc
  have hp : (H.free ++ ⟨H.braw, size⟩ :: H.live).Perm (⟨H.braw, size⟩ :: H.blocks) :=
    List.perm_middle
  have hmem : ∀ c, c ∈ H.free ++ ⟨H.braw, size⟩ :: H.live → c = ⟨H.braw, size⟩ ∨ c ∈ H.blocks :=
    fun c hc => List.mem_cons.1 (hp.mem_iff.1 hc)
  have hnew : (⟨H.braw + 16 + size, H.free, ⟨H.braw, size⟩ :: H.live⟩ : Heap).brk =
      H.braw + 16 + size := Heap.brk_of_ne (by homega)
  refine
    { brkWord := ldv_store_hit _ _ _, brkZero := fun h => absurd h (by homega),
      brkLo := fun _ => by homega, brkHi := hroom, brkAl := by homega, links := ?_, hdr := ?_,
      hAl := ?_, szAl := ?_, lo := ?_, hi := ?_, apart := ?_, own := hi.own,
      globOwn := hi.globOwn }
  · refine hi.links.frame fun x hx => ?_
    have hx' : x = freeListAddr ∨ ∃ c ∈ H.blocks, x = c.h + 8 := by
      rcases mem_chainWords hx with e | ⟨c, hc, e⟩
      · exact .inl e
      · exact .inr ⟨c, List.mem_append_left _ hc, e⟩
    have hs : Sep8 x brkAddr ∧ Sep8 x H.braw := by
      rcases hx' with rfl | ⟨c, hc, rfl⟩
      · omega
      · have := hold c hc; have := hi.lo c hc; unfold Blk.fin at *; homega
    rw [ldv_ld_miss _ _ hs.1, ldv_ld_miss _ _ hs.2]
  · intro c hc
    rcases hmem c hc with rfl | hc
    · rw [ldv_ld_miss _ _ (by homega), ldv_store_hit]
    · have := hold c hc; have := hi.lo c hc
      rw [ldv_ld_miss _ _ (by unfold Blk.fin at *; homega),
        ldv_ld_miss _ _ (by unfold Blk.fin at *; homega)]
      exact hi.hdr c hc
  · intro c hc; rcases hmem c hc with rfl | hc
    · exact hal
    · exact hi.hAl c hc
  · intro c hc; rcases hmem c hc with rfl | hc
    · exact hsz
    · exact hi.szAl c hc
  · intro c hc; rcases hmem c hc with rfl | hc
    · exact hlo
    · exact hi.lo c hc
  · intro c hc; rw [hnew]; rcases hmem c hc with rfl | hc
    · exact Nat.le_refl _
    · have := hold c hc; homega
  · refine (hp.pairwise_iff apart_symm).2 (List.pairwise_cons.2 ⟨fun c hc => ?_, hi.apart⟩)
    exact .inr (hold c hc)

/-- **Freeing** the live block `b`: its link word takes the old head,
`free_list` points to it. -/
theorem HeapInv.push {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {lpre : List Blk} {b : Blk} {lpost : List Blk} (hl : H.live = lpre ++ b :: lpost) :
    HeapInv S (writeLog (writeLog Mt [(b.h + 8, 8, BitVec.ofNat 64 (headOf H.free))])
        [(freeListAddr, 8, BitVec.ofNat 64 b.h)])
      ⟨H.braw, b :: H.free, lpre ++ lpost⟩ := by
  heap_consts
  have hbl : H.blocks = H.free ++ (lpre ++ b :: lpost) := by rw [Heap.blocks, hl]
  have hp : (H.free ++ (lpre ++ b :: lpost)).Perm ((b :: H.free) ++ (lpre ++ lpost)) := by
    have h1 : (H.free ++ (lpre ++ b :: lpost)).Perm (b :: (H.free ++ lpre ++ lpost)) := by
      simpa using (List.perm_middle (a := b) (l₁ := H.free ++ lpre) (l₂ := lpost))
    exact h1.trans (by simp)
  have hmem : ∀ c, c ∈ (b :: H.free) ++ (lpre ++ lpost) → c ∈ H.blocks := fun c hc => by
    rw [hbl]; exact hp.mem_iff.2 hc
  have hb : b ∈ H.blocks := by rw [hbl]; simp
  have fb := hi.blk hb
  have hsepH : ∀ c ∈ H.blocks, Sep8 c.h (b.h + 8) := by
    intro c hc
    by_cases e : c = b
    · subst e; homega
    · have := apart_of_mem hi.apart hc hb e
      unfold Blk.Apart Blk.fin at this; homega
  refine
    { brkWord := ?_, brkZero := ?_, brkLo := hi.brkLo, brkHi := hi.brkHi, brkAl := hi.brkAl,
      links := ?_, hdr := ?_, hAl := fun c hc => hi.hAl c (hmem c hc),
      szAl := fun c hc => hi.szAl c (hmem c hc), lo := fun c hc => hi.lo c (hmem c hc),
      hi := fun c hc => hi.hi c (hmem c hc), apart := ?_, own := hi.own, globOwn := hi.globOwn }
  · have := fb.lo
    rw [ldv_ld_miss _ _ (by homega), ldv_ld_miss _ _ (by homega)]; exact hi.brkWord
  · intro h0; have := hi.brkZero h0; rw [this] at hb; cases hb
  · refine .cons (ldv_store_hit _ _ _) (hi.links.move ?_ fun c hc => ?_)
    · have := fb.lo
      rw [ldv_ld_miss _ _ (by homega), ldv_store_hit, hi.links.head]
    · have hcb : c ∈ H.blocks := List.mem_append_left _ hc
      have fc := (hi.blk hcb).lo
      have happ := hi.apart
      rw [hbl] at happ
      have := (List.pairwise_append.1 happ).2.2 c hc b (by simp)
      unfold Blk.Apart Blk.fin at this
      rw [ldv_ld_miss _ _ (by homega), ldv_ld_miss _ _ (by homega)]
  · intro c hc
    have hcb := hmem c hc
    have := (hi.blk hcb).lo
    rw [ldv_ld_miss _ _ (by homega), ldv_ld_miss _ _ (hsepH c hcb)]
    exact hi.hdr c hcb
  · show ((b :: H.free) ++ (lpre ++ lpost)).Pairwise Blk.Apart
    have happ := hi.apart
    rw [hbl] at happ
    exact (hp.pairwise_iff apart_symm).1 happ


/-! ## Frames and results -/

/-- A store whose bytes all satisfy `P` leaves every other byte. -/
theorem imgM_store_off {P : Nat → Prop} (Mt : Mem) {x w a : Nat} (v : BitVec 64)
    (hw : ∀ j, j < w → P (x + j)) (ha : ¬ P a) : imgM (writeLog Mt [(x, w, v)]) a = imgM Mt a := by
  refine imgM_store_miss _ _ (Classical.byContradiction fun hc => ha ?_)
  have := hw (a - x) (by omega)
  rwa [Nat.add_sub_cancel' (by omega)] at this

/-- The allocator's bytes lie in its globals or the heap. -/
theorem AllocByte.bound {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {a : Nat}
    (h : AllocByte H a) : freeListAddr ≤ a ∧ a < heapEnd := by
  have htop := hi.brk_hi
  cases h with
  | glob h1 h2 => heap_consts; omega
  | hdr b hb h1 h2 => have fb := hi.blk hb; have := fb.lo; have := fb.fin; bomega
  | freePay b hb h1 h2 =>
    have fb := hi.blk (List.mem_append_left _ hb); have := fb.lo; have := fb.fin; bomega
  | top h1 h2 => have := hi.brk_lo; heap_consts; omega

/-- A doubleword load depends only on its eight bytes. -/
theorem ldv_ld_congr {Mt Mt' : Mem} {a : Nat}
    (h : ∀ j, j < 8 → imgM Mt' (a + j) = imgM Mt (a + j)) : ldv .ld Mt' a = ldv .ld Mt a := by
  unfold ldv bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  exact h j (List.mem_range.mp hj)

/-- **Transport**: the invariant reads only allocator bytes. -/
theorem HeapInv.transport {S : Nat → Prop} {Mt Mt' : Mem} {H : Heap} (hi : HeapInv S Mt H)
    (hag : ∀ a, AllocByte H a → imgM Mt' a = imgM Mt a) : HeapInv S Mt' H := by
  have hhdr : ∀ b ∈ H.blocks, ∀ j, j < 16 → imgM Mt' (b.h + j) = imgM Mt (b.h + j) :=
    fun b hb j hj => hag _ (.hdr b hb (by omega) (by simp only [Blk.pay]; omega))
  refine { hi with brkWord := ?_, links := ?_, hdr := ?_ }
  · rw [ldv_ld_congr fun j hj => hag _ (.glob (by heap_consts; omega) (by heap_consts; omega))]
    exact hi.brkWord
  · refine hi.links.frame fun x hx => ?_
    rcases mem_chainWords hx with rfl | ⟨c, hc, rfl⟩
    · exact ldv_ld_congr fun j hj => hag _ (.glob (by heap_consts; omega) (by heap_consts; omega))
    · exact ldv_ld_congr fun j hj => by
        rw [Nat.add_assoc]; exact hhdr c (List.mem_append_left _ hc) (8 + j) (by omega)
  · intro b hb
    rw [ldv_ld_congr fun j hj => hhdr b hb j (by omega)]
    exact hi.hdr b hb

/-- The result of `malloc(n)`: `NULL` with the same blocks, or a block of at
least `n` bytes taken from the free list or the top, now live. -/
inductive MallocRes (H H' : Heap) (n : Nat) (r : BitVec 64) : Prop
  | null : r = 0#64 → H'.free = H.free → H'.live = H.live → MallocRes H H' n r
  | block (b : Blk) : r = BitVec.ofNat 64 b.pay → n ≤ b.sz → H'.live = b :: H.live →
      (∀ c ∈ H'.free, c ∈ H.free) → (∀ a, b.h ≤ a → a < b.fin → AllocByte H a) →
      MallocRes H H' n r

/-- `malloc`'s postcondition: the invariant, the result, and the frame (only
allocator bytes change). -/
structure MallocPost (S : Nat → Prop) (Mt Mt' : Mem) (H H' : Heap) (n : Nat) (r : BitVec 64) :
    Prop where
  inv : HeapInv S Mt' H'
  res : MallocRes H H' n r
  frame : ∀ a, ¬ AllocByte H a → imgM Mt' a = imgM Mt a

/-- A live block's payload is the client's: no allocator byte, apart from the
other live blocks. -/
theorem HeapInv.live_fresh {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {b : Blk} (hb : b ∈ H.live) {a : Nat} (h1 : b.pay ≤ a) (h2 : a < b.fin) :
    ¬ AllocByte H a ∧ ∀ c ∈ H.live, c ≠ b → a < c.pay ∨ c.fin ≤ a := by
  heap_consts
  have hbb : b ∈ H.blocks := List.mem_append_right _ hb
  have fb := hi.blk hbb
  have hblo := fb.lo
  have hbfin := fb.fin
  refine ⟨fun ha => ?_, fun c hc hne => ?_⟩
  · cases ha with
    | glob h3 h4 => bomega
    | hdr c hc h3 h4 =>
      by_cases e : c = b
      · subst e; bomega
      · have := apart_of_mem hi.apart hc hbb e; bomega
    | freePay c hc h3 h4 =>
      have := (List.pairwise_append.1 hi.apart).2.2 c hc b hb
      bomega
    | top h3 h4 => bomega
  · have := apart_of_mem hi.apart (List.mem_append_right _ hc) hbb hne
    bomega

/-- The link word before `b` in the free list: aligned, owned, the
allocator's. -/
structure LinkWord (S : Nat → Prop) (H : Heap) (w : Nat) : Prop where
  al : w % 8 = 0
  lo : freeListAddr ≤ w
  hi : w + 8 ≤ heapEnd
  own : ∀ j, j < 8 → S (w + j)
  alloc : ∀ j, j < 8 → AllocByte H (w + j)
  brk : Sep8 w brkAddr

theorem HeapInv.linkWord {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {pre : List Blk} {b : Blk} {post : List Blk} (hf : H.free = pre ++ b :: post) :
    LinkWord S H (linkOf freeListAddr pre) := by
  heap_consts
  rcases linkOf_mem freeListAddr pre with e | ⟨c, hc, e⟩
  · rw [e]
    exact ⟨by omega, Nat.le_refl _, by omega, fun j hj => hi.globOwn _ (by omega) (by omega),
      fun j hj => .glob (by omega) (by omega), by omega⟩
  · have hcb : c ∈ H.blocks := List.mem_append_left _ (by rw [hf]; exact List.mem_append_left _ hc)
    have fc := hi.blk hcb
    have := fc.fin; have := fc.lo; have := fc.top; have := fc.al
    rw [e]
    exact ⟨by omega, by omega, by unfold Blk.fin at *; omega,
      fun j hj => hi.own _ (by omega) (by unfold Blk.fin at *; omega),
      fun j hj => .hdr c hcb (by omega) (by bomega), by omega⟩

end Dc.Mach
