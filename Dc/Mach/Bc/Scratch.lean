import Dc.Mach.Bc.KaraViews

/-!
# Scratch buffers beside the number heap

`bc_divide` works in three raw `malloc` buffers (`num1`, `num2`, `mval`)
that hold no number object. A raw buffer is a live block of the allocator
outside the dead chain and the objects' blocks; the number heap survives:

- `BcHeap.malloc`: any `malloc` call (`MallocPost`), and `MallocRes.fresh`
  for the new block's separation from the heap's blocks;
- `BcHeap.rawWrite`: stores confined to a raw buffer's payload;
- `BcHeap.freeRaw`: `free` of a raw buffer (`FreePost`).

`BcHeap.transportOwn` is the transport behind them: agreement on the
allocator's bytes, the dead chain's and the objects' blocks only.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- Every block of the dead chain and the objects is live. -/
theorem BcHeap.owned_live {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S X Mt H F L) {b : Blk} (hb : b ∈ F ++ objBlocks L ++ X.bs) :
    b ∈ H.live := by
  rcases List.mem_append.mp hb with hb | hr
  · rcases List.mem_append.mp hb with hf | ho
    · exact (h.deadLive b hf).1
    · exact h.objBlocks_live ho
  · exact h.raw.live b hr

/-- **Rebase** onto a new memory and allocator state: the invariant there,
the dead chain's and the objects' blocks still live, their bytes and
`_bc_Free_list` unchanged. -/
theorem BcHeap.rebase {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H H' : Heap}
    {F : List Blk} {L : List NumObj} (h : BcHeap S X Mt H F L) (hi : HeapInv S Mt' H')
    (hkeep : ∀ b ∈ F ++ objBlocks L ++ X.bs, b ∈ H'.live)
    (hl : ∀ b ∈ F ++ objBlocks L ++ X.bs, ∀ a, b.In a → imgM Mt' a = imgM Mt a)
    (hg : ∀ j, j < 8 → imgM Mt' (bcFreeAddr + j) = imgM Mt (bcFreeAddr + j)) :
    BcHeap S X Mt' H' F L := by
  have hl' : ∀ b ∈ F ++ objBlocks L, ∀ a, b.In a → imgM Mt' a = imgM Mt a := fun b hb =>
    hl b (List.mem_append_left _ hb)
  have hkeep' : ∀ b ∈ F ++ objBlocks L, b ∈ H'.live := fun b hb =>
    hkeep b (List.mem_append_left _ hb)
  refine ⟨hi, ?_, ?_, ?_, ?_, h.distinct, h.views, h.globOwn,
    h.raw.rebase (fun b hb => hkeep b (List.mem_append_right _ hb)) (fun c hc => .inl hc)
      fun b hb => hl b (List.mem_append_right _ hb)⟩
  · refine h.dead.frame (ldv_congr .ld hg) ?_
    intro b hb j hj
    have hsz := (h.deadLive b hb).2
    apply hl' b (List.mem_append_left _ hb)
    simp only [Blk.In, Blk.fin, Blk.pay]
    omega
  · intro b hb
    exact ⟨hkeep' b (List.mem_append_left _ hb), (h.deadLive b hb).2⟩
  · intro x hx
    refine (h.nums x hx).frame fun a hax => ?_
    have hb := h.blocks x hx
    rcases NumObj.foot_blocks (h.nums x hx) hb hax with hs | hd
    · exact hl' x.sb (List.mem_append_right _ (mem_objBlocks hx)) a hs
    · exact hl' x.db (List.mem_append_right _ (h.db_mem hx)) a hd
  · intro x hx
    exact { h.blocks x hx with
      sLive := hkeep' _ (List.mem_append_right _ (mem_objBlocks hx))
      dLive := hkeep' _ (List.mem_append_right _ (h.db_mem hx)) }

/-- Transport through agreement on the allocator's bytes, the dead chain's
and the objects' blocks, and `_bc_Free_list`. -/
theorem BcHeap.transportOwn {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} (h : BcHeap S X Mt H F L)
    (ha : ∀ a, AllocByte H a → imgM Mt' a = imgM Mt a)
    (hl : ∀ b ∈ F ++ objBlocks L ++ X.bs, ∀ a, b.In a → imgM Mt' a = imgM Mt a)
    (hg : ∀ j, j < 8 → imgM Mt' (bcFreeAddr + j) = imgM Mt (bcFreeAddr + j)) :
    BcHeap S X Mt' H F L :=
  h.rebase (h.heap.transport ha) (fun _ hb => h.owned_live hb) hl hg

/-- The live list after `malloc` contains the old one. -/
theorem MallocRes.live_mono {H H' : Heap} {n : Nat} {r : BitVec 64} (h : MallocRes H H' n r)
    {b : Blk} (hb : b ∈ H.live) : b ∈ H'.live := by
  cases h with
  | null _ _ hl => rw [hl]; exact hb
  | block c _ _ hl _ _ => rw [hl]; exact List.mem_cons_of_mem _ hb

/-- **The number heap survives `malloc`.** -/
theorem BcHeap.malloc {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H H' : Heap} {F : List Blk}
    {L : List NumObj} {n : Nat} {r : BitVec 64} (h : BcHeap S X Mt H F L)
    (hp : MallocPost S Mt Mt' H H' n r) : BcHeap S X Mt' H' F L :=
  h.rebase hp.inv (fun _ hb => hp.res.live_mono (h.owned_live hb))
    (fun b hb a ha => hp.frame a (live_not_alloc h.heap (h.owned_live hb) ha))
    (fun j hj => hp.frame _ fun ha => not_bcFree_of_alloc h.heap ha
      (by simp only [bcFreeBytes]; omega))

/-- A block `malloc` returns is none of the heap's owned blocks. -/
theorem BcHeap.fresh_not_owned {S : Nat → Prop} {X : Raws} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S X Mt H F L) {b : Blk} (hsz : 1 ≤ b.sz)
    (hal : ∀ a, b.h ≤ a → a < b.fin → AllocByte H a) : b ∉ F ++ objBlocks L ++ X.bs := fun hb =>
  live_not_alloc h.heap (h.owned_live hb) (show b.In b.pay by
    simp only [Blk.In, Blk.pay, Blk.fin]; omega)
    (hal _ (by simp only [Blk.pay]; omega) (by simp only [Blk.pay, Blk.fin]; omega))

/-- **Stores into a raw buffer** (a live block apart from the heap's owned
blocks) keep the number heap. -/
theorem BcHeap.rawWrite {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S X Mt H F L) {b : Blk} (hb : b ∈ H.live)
    (hno : b ∉ F ++ objBlocks L ++ X.bs) (hm : MemOnly b.In Mt' Mt) : BcHeap S X Mt' H F L :=
  h.transportOwn (fun a ha => hm a fun hi => live_not_alloc h.heap hb hi ha)
    (fun c hc a ha => hm a fun hi =>
      live_apart h.heap hb (h.owned_live hc) (fun e => hno (e ▸ hc)) hi ha)
    (fun j hj => hm _ fun hi => by
      have := live_in_heap h.heap hb hi
      simp only [bcFreeAddr, heapStart, heapEnd] at this; omega)

/-- **`free` of a raw buffer** keeps the number heap. -/
theorem BcHeap.freeRaw {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H H' : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S X Mt H F L) {lpre lpost : List Blk} {b : Blk}
    (hl : H.live = lpre ++ b :: lpost) (hno : b ∉ F ++ objBlocks L ++ X.bs)
    (hp : FreePost S Mt Mt' H H' b lpre lpost) : BcHeap S X Mt' H' F L :=
  h.rebase hp.inv
    (fun c hc => by
      have hcl := h.owned_live hc
      rw [hl] at hcl
      rw [hp.live]
      rcases List.mem_append.mp hcl with h1 | h1
      · exact List.mem_append_left _ h1
      · rcases List.mem_cons.mp h1 with h2 | h2
        · exact absurd (h2 ▸ hc) hno
        · exact List.mem_append_right _ h2)
    (fun c hc a ha => hp.frame a (live_not_alloc h.heap (h.owned_live hc) ha))
    (fun j hj => hp.frame _ fun ha => not_bcFree_of_alloc h.heap ha
      (by simp only [bcFreeBytes]; omega))

end Dc.Mach
