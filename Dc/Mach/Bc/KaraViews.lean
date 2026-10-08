import Dc.Mach.Bc.KaraTrimSites

/-!
# `_bc_rec_mul`'s Karatsuba step: the four halves

The step cuts `u` and `v` in two at `n = (max la lb + 1) / 2` digits and makes
a view (`new_sub_num`, inlined) of each half, taking the struct off
`_bc_Free_list` or from `malloc(40)` when the list is empty. A half with no
digits is a reference to `_zero_` instead.

This module has the layer the four inlined sites share: reading a word out of
a doubleword store (`ldv_lw_hit8lo`/`hi`, the `sd` of `n_scale`/`n_refs`) and
`viewSrc_of_pop`, which turns the six stores of one site into the `ViewSrc`
that `BcHeap.pushView` consumes.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

theorem pow256_4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide

/-- The low word of a doubleword just stored, on the image. -/
theorem imgLE_store8_lo (Mt : Mem) (b : Nat) (v : BitVec 64) :
    VsaIris.Interp.imgLE (imgM (writeLog Mt [(b, 8, v)])) b 4 = v.toNat % 2 ^ 32 := by
  have h8 := VsaIris.Interp.imgLE_imgM_store Mt b v
  have hsp := VsaIris.Interp.imgLE_split (imgM (writeLog Mt [(b, 8, v)])) b 4 4
  have l1 := VsaIris.Interp.imgLE_lt (imgM (writeLog Mt [(b, 8, v)])) b 4
  have l2 := VsaIris.Interp.imgLE_lt (imgM (writeLog Mt [(b, 8, v)])) (b + 4) 4
  rw [pow256_4] at l1 l2
  rw [show (4 + 4) = 8 from rfl, pow256_4] at hsp
  omega

/-- The high word of a doubleword just stored, on the image. -/
theorem imgLE_store8_hi (Mt : Mem) (b : Nat) (v : BitVec 64) :
    VsaIris.Interp.imgLE (imgM (writeLog Mt [(b, 8, v)])) (b + 4) 4 = v.toNat / 2 ^ 32 := by
  have h8 := VsaIris.Interp.imgLE_imgM_store Mt b v
  have hsp := VsaIris.Interp.imgLE_split (imgM (writeLog Mt [(b, 8, v)])) b 4 4
  have l1 := VsaIris.Interp.imgLE_lt (imgM (writeLog Mt [(b, 8, v)])) b 4
  have l2 := VsaIris.Interp.imgLE_lt (imgM (writeLog Mt [(b, 8, v)])) (b + 4) 4
  rw [pow256_4] at l1 l2
  rw [show (4 + 4) = 8 from rfl, pow256_4] at hsp
  omega

/-- A word load of the low half of a doubleword just stored. -/
theorem ldv_lw_hit8lo (Mt : Mem) {a b : Nat} {v : BitVec 64} {k : Nat} (h : a = b)
    (hv : v.toNat % 2 ^ 32 = k) (hk : k < 2 ^ 31) :
    ldv .lw (writeLog Mt [(b, 8, v)]) a = BitVec.ofNat 64 k := by
  rw [h, ldv_lw_img, imgLE_store8_lo, hv]; exact sext32_small hk

/-- A word load of the high half of a doubleword just stored. -/
theorem ldv_lw_hit8hi (Mt : Mem) {a b : Nat} {v : BitVec 64} {k : Nat} (h : a = b + 4)
    (hv : v.toNat / 2 ^ 32 = k) (hk : k < 2 ^ 31) :
    ldv .lw (writeLog Mt [(b, 8, v)]) a = BitVec.ofNat 64 k := by
  rw [h, ldv_lw_img, imgLE_store8_hi, hv]; exact sext32_small hk

/-- The chain word is in writable RAM, aligned, off the HTIF words. -/
theorem ldOK_bcFree : LdOK bcFreeAddr 8 := by
  simp only [LdOK, bcFreeAddr, tohostAddr]; omega

theorem stOK_bcFree : StOK bcFreeAddr 8 := by
  simp only [StOK, bcFreeAddr, tohostAddr]
  refine ⟨by omega, by omega, by omega, ?_⟩
  decide

theorem ldOK_zero : LdOK zeroAddr 8 := by
  simp only [LdOK, zeroAddr, tohostAddr]; omega

/-- An allocator byte is not one of `_zero_`'s pointer word's. -/
theorem not_zeroAddr_of_alloc {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {a : Nat} (h : AllocByte H a) : ¬ (zeroAddr ≤ a ∧ a < zeroAddr + 8) := by
  rcases AllocByte.glob_or_heap hi h with h' | h' <;>
    simp only [freeListAddr, heapStart, heapEnd, zeroAddr] at h' ⊢ <;> omega

/-- An allocator byte is not one of `_bc_Free_list`'s. -/
theorem not_bcFree_of_alloc {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {a : Nat} (h : AllocByte H a) : ¬ bcFreeBytes a := by
  rcases AllocByte.glob_or_heap hi h with h' | h' <;>
    simp only [freeListAddr, heapStart, heapEnd, bcFreeBytes, bcFreeAddr] at h' ⊢ <;> omega

/-- **The struct one inlined `new_sub_num` site got**, at the point where the
list head is already updated: where the block came from (`ViewFrom`), the
allocator's invariant and the head word at the reached memory `M`, and `M`'s
agreement with the site's entry memory `Mt` off the block and the list word. -/
structure ViewStruct (S : Nat → Prop) (Mt M : Mem) (H H' : Heap) (F F' : List Blk)
    (sb : Blk) (L : List NumObj) : Prop where
  src : ViewFrom H H' F F' sb
  inv : HeapInv S M H'
  live : sb ∈ H'.live
  mono : ∀ c ∈ H.live, c ∈ H'.live
  notObj : sb ∉ objBlocks L
  sSz : 40 ≤ sb.sz
  head : ldv .ld M bcFreeAddr = BitVec.ofNat 64 (deadHead F')
  base : ∀ a, ¬ AllocByte H a → ¬ sb.In a → ¬ bcFreeBytes a → imgM M a = imgM Mt a

/-- **The struct popped off `_bc_Free_list`**: the list's head, its tail the
rest of the chain. -/
theorem ViewStruct.pop {S : Nat → Prop} {Mt M : Mem} {H : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} (hb : BcHeap S Mt H F L) (hF : F = sb :: F')
    (hhead : ldv .ld M bcFreeAddr = BitVec.ofNat 64 (deadHead F'))
    (hfr : ∀ a, ¬ bcFreeBytes a → imgM M a = imgM Mt a) :
    ViewStruct S Mt M H H F F' sb L :=
  { src := .pop hF rfl
    mono := fun _ hc => hc
    notObj := fun hm => by
      have hd := hb.distinct
      rw [hF] at hd
      exact (List.nodup_cons.mp hd).1 (List.mem_append_right _ hm)
    inv := hb.heap.transport fun a ha => hfr a (not_bcFree_of_alloc hb.heap ha)
    live := (hb.deadLive sb (by rw [hF]; exact List.mem_cons_self)).1
    sSz := (hb.deadLive sb (by rw [hF]; exact List.mem_cons_self)).2
    head := hhead
    base := fun a _ _ hg => hfr a hg }

/-- Every block of the heap's objects is a live block. -/
theorem BcHeap.objBlocks_live {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (hb : BcHeap S Mt H F L) {b : Blk} (h : b ∈ objBlocks L) :
    b ∈ H.live := by
  obtain ⟨x, hx, hbx⟩ := List.mem_flatMap.mp h
  have hxb := hb.blocks x hx
  unfold NumObj.blocks at hbx
  split at hbx
  · rcases List.mem_singleton.mp hbx with rfl; exact hxb.sLive
  · rcases List.mem_cons.mp hbx with rfl | hbx
    · exact hxb.sLive
    · rcases List.mem_singleton.mp hbx with rfl; exact hxb.dLive

/-- **The struct freshly allocated**, `_bc_Free_list` empty: `malloc`'s block
is a block of neither the chain nor the objects, since its bytes were the
allocator's. -/
theorem ViewStruct.fresh {S : Nat → Prop} {Mt M : Mem} {H H' : Heap} {F : List Blk}
    {L : List NumObj} {sb : Blk} (hb : BcHeap S Mt H F L) (hF : F = [])
    (hinv : HeapInv S M H') (hfr : ∀ a, ¬ AllocByte H a → imgM M a = imgM Mt a)
    (hl : H'.live = sb :: H.live) (hsz : 40 ≤ sb.sz)
    (hal : ∀ a, sb.h ≤ a → a < sb.fin → AllocByte H a) :
    ViewStruct S Mt M H H' F [] sb L := by
  have hpay : sb.h ≤ sb.pay := by simp only [Blk.pay]; omega
  have hfin : sb.pay < sb.fin := by simp only [Blk.pay, Blk.fin]; omega
  have hlive : sb ∈ H'.live := by rw [hl]; exact List.mem_cons_self
  have hmono : ∀ c ∈ H.live, c ∈ H'.live := fun c hc => by
    rw [hl]; exact List.mem_cons_of_mem _ hc
  have hno : sb ∉ objBlocks L := fun hm => live_not_alloc hb.heap (hb.objBlocks_live hm)
    (show sb.In sb.pay from ⟨Nat.le_refl _, hfin⟩) (hal sb.pay hpay hfin)
  have hd := hb.dead
  rw [hF] at hd
  have hhead : ldv .ld M bcFreeAddr = BitVec.ofNat 64 (deadHead ([] : List Blk)) := by
    rw [← hd.head]
    exact ldv_congr .ld fun j hj => hfr _ fun ha => not_bcFree_of_alloc hb.heap ha
      (by simp only [bcFreeBytes, bcFreeAddr, widthOfM] at hj ⊢; omega)
  exact ⟨.fresh hF rfl hl, hinv, hlive, hmono, hno, hsz, hhead, fun a h1 _ _ => hfr a h1⟩

/-- The tail of the chain, read out of the popped struct's link word. -/
theorem BcHeap.popNext {S : Nat → Prop} {Mt : Mem} {H : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} (hb : BcHeap S Mt H F L) (hF : F = sb :: F') :
    ldv .ld Mt (sb.pay + 16) = BitVec.ofNat 64 (deadHead F') := by
  rw [hF] at hb
  cases hb.dead with
  | cons _ ht => exact ht.head

/-- A chain's head is a heap address, so it fits a word. -/
theorem BcHeap.deadHead_lt {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (hb : BcHeap S Mt H F L) : deadHead F < 2 ^ 64 := by
  cases F with
  | nil => simp only [deadHead]; omega
  | cons b t =>
    have fb := hb.heap.blk (List.mem_append_right _ (hb.deadLive b List.mem_cons_self).1)
    have h1 := fb.fin; have h2 := fb.top
    simp only [heapEnd] at h2
    have h3 : b.pay = b.h + 16 := rfl
    have h4 : b.fin = b.h + 16 + b.sz := rfl
    simp only [deadHead]; omega

/-- **The head word is `NULL` exactly when the chain is empty**: the test that
sends an inlined `new_sub_num` to `malloc`. -/
theorem BcHeap.deadHead_eq_zero_iff {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (hb : BcHeap S Mt H F L) : deadHead F = 0 ↔ F = [] := by
  cases F with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons b t =>
    have fb := hb.heap.blk (List.mem_append_right _ (hb.deadLive b List.mem_cons_self).1)
    have h1 := fb.lo
    simp only [heapStart] at h1
    have h3 : b.pay = b.h + 16 := rfl
    exact ⟨fun h => by simp only [deadHead] at h; omega, fun h => by cases h⟩

/-- **The struct taken off the chain**: the link word read out of the head
struct and stored back into `_bc_Free_list`. -/
theorem ViewStruct.popAt {S : Nat → Prop} {Mt : Mem} {H : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} (hb : BcHeap S Mt H F L) (hF : F = sb :: F') (v : BitVec 64)
    (hv : v = BitVec.ofNat 64 (deadHead F')) :
    ViewStruct S Mt (writeLog Mt [(bcFreeAddr, 8, v)]) H H F F' sb L := by
  subst hv
  refine .pop hb hF (ldv_store_hit _ _ _) fun a hg => imgM_store_miss _ _ ?_
  simp only [bcFreeBytes] at hg; omega

/-- **The view's struct written**: the five fields of one site's stores turn
the struct into the `ViewSrc` that `BcHeap.pushView` consumes. -/
theorem ViewStruct.toSrc {S : Nat → Prop} {Mt M Mt' : Mem} {H H' : Heap} {F F' : List Blk}
    {sb : Blk} {L : List NumObj} {val k : Nat} (hv : ViewStruct S Mt M H H' F F' sb L)
    (hsign : ldv .lw Mt' sb.pay = 0#64) (hlen : ldv .lw Mt' (sb.pay + 4) = BitVec.ofNat 64 k)
    (hscale : ldv .lw Mt' (sb.pay + 8) = 0#64) (hrefs : ldv .lw Mt' (sb.pay + 12) = 1#64)
    (hptr : ldv .ld Mt' (sb.pay + 24) = 0#64)
    (hvalue : ldv .ld Mt' (sb.pay + 32) = BitVec.ofNat 64 val)
    (hfr : ∀ a, ¬ sb.In a → imgM Mt' a = imgM M a) :
    ViewSrc S Mt Mt' H H' F F' sb val k := by
  have hbf := hv.inv.blk (List.mem_append_right _ hv.live)
  have hlo := hbf.lo
  have hpay : bcFreeAddr + 8 ≤ sb.pay := by
    simp only [bcFreeAddr, heapStart, Blk.pay] at hlo ⊢; omega
  have hinv : HeapInv S Mt' H' :=
    hv.inv.transport fun a ha => hfr a fun hin => live_not_alloc hv.inv hv.live hin ha
  have hframe : ∀ a, ¬ AllocByte H a → ¬ sb.In a → ¬ bcFreeBytes a → imgM Mt' a = imgM Mt a :=
    fun a h1 h2 h3 => (hfr a h2).trans (hv.base a h1 h2 h3)
  refine ⟨hinv, hv.src, hv.sSz, ?_, hsign, hlen, hscale, hrefs, hptr, hvalue, hframe⟩
  rw [ldv_congr .ld fun j hj => hfr _ (by
    simp only [Blk.In, Blk.pay, Blk.fin, bcFreeAddr, widthOfM] at hj hpay ⊢; omega)]
  exact hv.head


/-- **A byte of an object's struct is off the view's struct**: the blocks are
distinct live blocks. -/
theorem ViewStruct.sb_off {S : Nat → Prop} {Mt M : Mem} {H H' : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} (hv : ViewStruct S Mt M H H' F F' sb L)
    (hb : BcHeap S Mt H F L) {x : NumObj} (hx : x ∈ L) {a : Nat} (ha : x.sb.In a) : ¬ sb.In a :=
  fun hin => live_apart hv.inv (hv.mono _ (hb.blocks x hx).sLive) hv.live
    (fun he => hv.notObj (he ▸ mem_objBlocks hx)) ha hin

/-- A byte of an object's digit buffer is off the view's struct. -/
theorem ViewStruct.db_off {S : Nat → Prop} {Mt M : Mem} {H H' : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} (hv : ViewStruct S Mt M H H' F F' sb L)
    (hb : BcHeap S Mt H F L) {x : NumObj} (hx : x ∈ L) {a : Nat} (ha : x.db.In a) : ¬ sb.In a := by
  obtain ⟨y, hy, ho, he⟩ := hb.views.owner hx
  refine fun hin => live_apart hv.inv (hv.mono _ (hb.blocks x hx).dLive) hv.live
    (fun hne => hv.notObj ?_) ha hin
  rw [← hne, ← he]
  exact mem_objBlocks_db hy ho


/-- The struct block's bounds and alignment. -/
structure BlkBounds (sb : Blk) : Prop where
  lo : 2147603936 ≤ sb.pay
  hi : sb.pay + 40 ≤ 2273312768
  al : sb.pay % 8 = 0
  sz : 40 ≤ sb.sz

theorem ViewStruct.bounds {S : Nat → Prop} {Mt M : Mem} {H H' : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} (hv : ViewStruct S Mt M H H' F F' sb L) : BlkBounds sb := by
  have hbf := hv.inv.blk (List.mem_append_right _ hv.live)
  have hlo := hbf.lo; have hfin := hbf.fin; have htop := hbf.top; have hal := hbf.al
  have hsz := hv.sSz
  simp only [heapStart] at hlo
  simp only [heapEnd] at htop
  have h1 : sb.pay = sb.h + 16 := rfl
  have h2 : sb.fin = sb.h + 16 + sb.sz := rfl
  exact ⟨by omega, by omega, by omega, hsz⟩

/-- A word of an object's struct is off the view's struct. -/
theorem ViewStruct.word_off {S : Nat → Prop} {Mt M : Mem} {H H' : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} {x : NumObj} (hv : ViewStruct S Mt M H H' F F' sb L)
    (hb : BcHeap S Mt H F L) (hx : x ∈ L) {o : Nat} (ho : o < 40) : ¬ sb.In (x.rep.p + o) := by
  have hxb := hb.blocks x hx
  have hxp := hxb.sPay; have hxsz := hxb.sSz
  exact hv.sb_off hb hx (by simp only [Blk.In, Blk.pay, Blk.fin] at hxp hxsz ⊢; omega)


/-- **A word of an object's struct is unchanged** at the point where the site
has its struct: the pop touched only `_bc_Free_list`, a `malloc` only the
allocator's bytes. -/
theorem ViewStruct.word_agree {S : Nat → Prop} {Mt M : Mem} {H H' : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} {x : NumObj} (hv : ViewStruct S Mt M H H' F F' sb L)
    (hb : BcHeap S Mt H F L) (hx : x ∈ L) {o : Nat} (ho : o + 8 ≤ 40) :
    ldv .ld M (x.rep.p + o) = ldv .ld Mt (x.rep.p + o) := by
  have hxb := hb.blocks x hx
  have hxp := hxb.sPay; have hxsz := hxb.sSz
  have hbf := hb.heap.blk (List.mem_append_right _ hxb.sLive)
  have hlo := hbf.lo; have hfin := hbf.fin; have htop := hbf.top
  simp only [heapStart] at hlo
  simp only [heapEnd] at htop
  refine ldv_congr .ld fun j hj => hv.base _ ?_ ?_ ?_
  · exact live_not_alloc hb.heap hxb.sLive
      (by simp only [Blk.In, Blk.pay, Blk.fin, widthOfM] at hxp hxsz hj ⊢; omega)
  · rw [Nat.add_assoc]
    exact hv.word_off hb hx (o := o + j) (by simp only [widthOfM] at hj; omega)
  · simp only [Blk.pay, Blk.fin, bcFreeBytes, bcFreeAddr, widthOfM] at hxp hj ⊢; omega

end Dc.Mach
