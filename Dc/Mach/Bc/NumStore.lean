import Dc.Mach.Bc.Free
import Dc.Mach.Bc.New

/-!
# Stores into the number heap

Facts every bc machine proof composes: `BcHeap.newHeap` (a number heap feeds
`bc_new_num`), `BcHeap.out_frame` (stores outside the heap),
`BcHeap.setDigit` (one digit byte of a represented number rewritten), and
`BcHeap.setSign` (its sign word).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A number heap supplies `bc_new_num`'s precondition. -/
theorem BcHeap.newHeap {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S Mt H F L) : NewHeap S Mt H F :=
  { inv := h.heap
    dead := h.dead
    deadOK := h.deadLive
    nodup := (List.nodup_append.mp h.distinct).1
    glob := h.globOwn }

/-- Every byte of a live block lies in the heap. -/
theorem live_in_heap {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {b : Blk}
    (hb : b ∈ H.live) {a : Nat} (ha : b.In a) : heapStart ≤ a ∧ a < heapEnd := by
  have fb := hi.blk (List.mem_append_right _ hb)
  have h1 : 2147603920 ≤ b.h := fb.lo
  have h2 : b.fin ≤ H.brk := fb.fin
  have h3 : H.brk ≤ 2273312768 := fb.top
  have hp : b.pay = b.h + 16 := rfl
  simp only [Blk.In] at ha
  simp only [heapStart, heapEnd]
  omega

/-- A number heap survives any memory change confined to bytes outside the
heap and the allocator's and `_bc_Free_list`'s words. -/
theorem BcHeap.out_frame {S : Nat → Prop} {Mt Mt' : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S Mt H F L) {P : Nat → Prop} (hfr : MemOnly P Mt' Mt)
    (hP : ∀ a, P a → OutHeap a) : BcHeap S Mt' H F L :=
  h.transport (fun a ha => hfr a fun hp => OutHeap.not_alloc h.heap (hP a hp) ha)
    (fun b hb a ha => hfr a fun hp => (hP a hp).1 (live_in_heap h.heap hb ha))
    (fun j hj => hfr _ fun hp => (hP _ hp).2.2 ⟨by omega, by omega⟩)

/-- The object `y` with digit list `ds`. -/
abbrev withDs (y : NumObj) (ds : List Nat) : NumObj := { y with rep := { y.rep with ds := ds } }

/-- A digit byte rewritten. -/
theorem NumAt.setDigit {Mt : Mem} {o : NumRep} (h : NumAt Mt o) {i d : Nat}
    (hi : i < o.len + o.scale) (hd : d < 10) {v : BitVec 64} (hv : sbData v = BitVec.ofNat 8 d) :
    NumAt (writeLog Mt [(o.val + i, 1, v)]) { o with ds := o.ds.set i d } := by
  have hs := h.shape
  have hsep := hs.sep; have hpl := hs.ptrLe
  have hshape : NumShape { o with ds := o.ds.set i d } :=
    { hs with
      dsLen := by simp only [List.length_set]; exact hs.dsLen
      dig := fun e he => by
        rcases List.mem_or_eq_of_mem_set he with he | rfl
        · exact hs.dig e he
        · exact hd }
  have hmiss : ∀ off, off < 40 → o.val + i < o.p + off ∨ o.p + off + 1 ≤ o.val + i := by
    intro off hoff; omega
  refine ⟨hshape, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.sign
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.len
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.scale
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.refs
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.ptr
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.value
  · dsimp only at hj ⊢
    by_cases hji : j = i
    · subst hji
      rw [imgM_sb, hv]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hs.dsLen]; exact hj),
        Option.getD_some]
    · rw [imgM_store_miss _ _ (by omega)]
      rw [h.digit j hj]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hji)]

/-- An object no other object shares a buffer with owns its buffer. -/
theorem BcHeap.owns_of_noView {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (L1 ++ x :: L2))
    (hnv : ∀ y ∈ L1 ++ L2, y.db ≠ x.db) : x.Owns := by
  obtain ⟨w, hw, hwo, he⟩ := h.views.owner (List.mem_append_right L1 List.mem_cons_self)
  rcases List.mem_append.mp hw with hw | hw
  · exact absurd he (hnv w (List.mem_append_left _ hw))
  · rcases List.mem_cons.mp hw with rfl | hw
    · exact hwo
    · exact absurd he (hnv w (List.mem_append_right _ hw))

/-- One digit byte of the object `x` rewritten, no other object reading its
buffer: the heap holds `x` with that digit. Only the byte changes; it lies in
`x`'s digit block. -/
theorem BcHeap.setDigit {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (L1 ++ x :: L2))
    (hnv : ∀ y ∈ L1 ++ L2, y.db ≠ x.db) {i d : Nat}
    (hi : i < x.rep.len + x.rep.scale) (hd : d < 10) {v : BitVec 64}
    (hv : sbData v = BitVec.ofNat 8 d) :
    BcHeap S (writeLog Mt [(x.rep.val + i, 1, v)]) H F
      (L1 ++ { x with rep := { x.rep with ds := x.rep.ds.set i d } } :: L2) := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  have hdf := hxb.dFit; have hdl := hxb.dLo
  have hfin : x.db.fin = x.db.pay + x.db.sz := rfl
  have hin : ∀ a, a = x.rep.val + i → x.db.In a := fun a ha => ⟨by omega, by omega⟩
  exact BcHeap.update h rfl rfl rfl
    ⟨hxb.sLive, hxb.dLive, hxb.sPay, hxb.sSz, hxb.dPay, hxb.dLo, hxb.dFit⟩
    (hn.setDigit hi hd hv) (P := fun a => a = x.rep.val + i)
    (fun a ha => imgM_store_miss _ _ (by omega))
    fun a ha => h.db_writeOK (h.owns_of_noView hnv) hnv (hin a ha)

/-- The sign word of the object `x` rewritten: the heap holds `x` with that
sign. Only the four bytes of `n_sign` change; they lie in `x`'s struct. -/
theorem BcHeap.setSign {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (L1 ++ x :: L2)) {v : BitVec 64}
    (b : Bool) (hv : v.toNat % 2 ^ 32 = b.toNat) :
    BcHeap S (writeLog Mt [(x.rep.p, 4, v)]) H F
      (L1 ++ { x with rep := { x.rep with neg := b } } :: L2) := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  have hsp := hxb.sPay; have hsz := hxb.sSz
  have hfin : x.sb.fin = x.sb.pay + x.sb.sz := rfl
  have hin : ∀ a, x.rep.p ≤ a ∧ a < x.rep.p + 4 → x.sb.In a := fun a ha => ⟨by omega, by omega⟩
  exact BcHeap.update h rfl rfl rfl
    ⟨hxb.sLive, hxb.dLive, hxb.sPay, hxb.sSz, hxb.dPay, hxb.dLo, hxb.dFit⟩
    (hn.setSign b hv) (P := fun a => x.rep.p ≤ a ∧ a < x.rep.p + 4)
    (fun a ha => imgM_store_miss _ _ (by omega)) fun a ha => h.sb_writeOK (hin a ha)

end Dc.Mach
