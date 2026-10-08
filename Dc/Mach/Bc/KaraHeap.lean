import Dc.Mach.Bc.NumStore

/-!
# The number heap under `_bc_rec_mul`'s Karatsuba step

`_bc_rec_mul` inlines `new_sub_num`, `bc_copy_num(_zero_)` and
`bc_free_num`. Their effects on the number heap:

- `BcHeap.setRefs`: an object's reference count rewritten (the copies of
  `_zero_` and the frees that leave a reference).
- `BcHeap.pushView`: a view (`n_ptr = NULL`) of `k` digits of `w` from `off`
  heads the heap, its struct from `_bc_Free_list` or `malloc(40)`
  (`ViewSrc`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The object with reference count `k`. -/
def NumObj.withRefs (x : NumObj) (k : Nat) : NumObj :=
  { x with rep := { x.rep with refs := k } }

theorem NumObj.withRefs_sb (x : NumObj) (k : Nat) : (x.withRefs k).sb = x.sb := rfl
theorem NumObj.withRefs_db (x : NumObj) (k : Nat) : (x.withRefs k).db = x.db := rfl
theorem NumObj.withRefs_withRefs (x : NumObj) (k j : Nat) :
    (x.withRefs k).withRefs j = x.withRefs j := rfl
theorem NumObj.withRefs_self (x : NumObj) : x.withRefs x.rep.refs = x := rfl
theorem NumObj.decRef_eq (x : NumObj) : x.decRef = x.withRefs (x.rep.refs - 1) := rfl

/-- **A reference count rewritten**: the word stored at `n_refs` of `x`. -/
theorem BcHeap.setRefs {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (L1 ++ x :: L2))
    {v : BitVec 64} {k : Nat} (hv : v.toNat % 2 ^ 32 = k) (hk : k < 2 ^ 31) :
    BcHeap S (writeLog Mt [(x.rep.p + 12, 4, v)]) H F (L1 ++ x.withRefs k :: L2) := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hb := h.blocks x hx
  have hp := hb.sPay; have hz := hb.sSz
  refine h.update rfl rfl rfl ⟨hb.sLive, hb.dLive, hb.sPay, hb.sSz, hb.dPay, hb.dLo, hb.dFit⟩
    ((h.nums x hx).setRefs hv hk) (MemOnly.store _ _ _ _)
    fun a ha => h.sb_writeOK ⟨by omega, by simp only [Blk.fin, Blk.pay] at *; omega⟩

/-- A view's representation: `k` digits of `w` from `off`, its struct at `p`. -/
def viewRep (p : Nat) (w : NumRep) (off k : Nat) : NumRep :=
  ⟨p, 0, w.val + off, false, k, 0, 1, (w.ds.drop off).take k⟩

/-- The view object of `w`'s buffer with struct block `sb`. -/
def viewObj (sb : Blk) (w : NumObj) (off k : Nat) : NumObj :=
  ⟨viewRep sb.pay w.rep off k, sb, w.db⟩

/-- Where a view's struct block `sb` came from: the head of `_bc_Free_list`
(`pop`), or `malloc(40)` with the list empty (`fresh`). -/
inductive ViewFrom (H H' : Heap) (F F' : List Blk) (sb : Blk) : Prop
  | pop : F = sb :: F' → H' = H → ViewFrom H H' F F' sb
  | fresh : F = [] → F' = [] → H'.live = sb :: H.live → ViewFrom H H' F F' sb

/-- The memory after `new_sub_num` wrote the view's struct: the allocator's
invariant, the list head, the fields, and nothing else changed off the
allocator's bytes, the struct and `_bc_Free_list`. -/
structure ViewSrc (S : Nat → Prop) (Mt Mt' : Mem) (H H' : Heap) (F F' : List Blk) (sb : Blk)
    (val k : Nat) : Prop where
  inv : HeapInv S Mt' H'
  src : ViewFrom H H' F F' sb
  sSz : 40 ≤ sb.sz
  head : ldv .ld Mt' bcFreeAddr = BitVec.ofNat 64 (deadHead F')
  sign : ldv .lw Mt' sb.pay = 0#64
  len : ldv .lw Mt' (sb.pay + 4) = BitVec.ofNat 64 k
  scale : ldv .lw Mt' (sb.pay + 8) = 0#64
  refs : ldv .lw Mt' (sb.pay + 12) = 1#64
  ptr : ldv .ld Mt' (sb.pay + 24) = 0#64
  value : ldv .ld Mt' (sb.pay + 32) = BitVec.ofNat 64 val
  frame : ∀ a, ¬ AllocByte H a → ¬ sb.In a → ¬ bcFreeBytes a → imgM Mt' a = imgM Mt a

/-- **A view pushed**: `k ≥ 1` digits of `w` (an object of the heap) from
`off`, in a struct from `ViewSrc`, head the heap. -/
theorem BcHeap.pushView {S : Nat → Prop} {Mt Mt' : Mem} {H H' : Heap} {F F' : List Blk}
    {L : List NumObj} {w : NumObj} {sb : Blk} {off k : Nat} (h : BcHeap S Mt H F L)
    (hw : w ∈ L) (hk : 1 ≤ k) (hfit : off + k ≤ w.rep.len + w.rep.scale)
    (hv : ViewSrc S Mt Mt' H H' F F' sb (w.rep.val + off) k) :
    BcHeap S Mt' H' F' (viewObj sb w off k :: L) := by
  have hi := h.heap
  have hi' := hv.inv
  have hwn := h.nums w hw
  have hws := hwn.shape
  have hwb := h.blocks w hw
  -- the old live blocks
  have hold : ∀ b ∈ F ++ objBlocks L, b ∈ H.live := fun b hb => by
    rcases List.mem_append.mp hb with hf | hl
    · exact (h.deadLive b hf).1
    · obtain ⟨y, hy, hb⟩ := List.mem_flatMap.mp hl
      have hby := h.blocks y hy
      unfold NumObj.blocks at hb
      split at hb <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      · subst hb; exact hby.sLive
      · rcases hb with rfl | rfl
        · exact hby.sLive
        · exact hby.dLive
  have hsub : ∀ c ∈ H.live, c ∈ H'.live := fun c hc => by
    cases hv.src with
    | pop _ e => rw [e]; exact hc
    | fresh _ _ e => rw [e]; exact List.mem_cons_of_mem _ hc
  have hsbL : sb ∈ H'.live := by
    cases hv.src with
    | pop e e' => rw [e']; exact (h.deadLive sb (by rw [e]; exact List.mem_cons_self)).1
    | fresh _ _ e => rw [e]; exact List.mem_cons_self
  -- `sb` is none of the old blocks of the objects (nor of `F'`)
  have hbase : (sb :: (F' ++ objBlocks L)).Nodup := by
    cases hv.src with
    | pop e _ => simpa only [e, List.cons_append] using h.distinct
    | fresh e e' hl =>
      have hn := hi'.live_nodup
      rw [hl] at hn
      obtain ⟨hsb, _⟩ := List.nodup_cons.mp hn
      rw [e']
      simp only [List.nil_append]
      refine List.nodup_cons.mpr ⟨fun hb => hsb (hold _ (List.mem_append_right _ hb)), ?_⟩
      have hd := h.distinct
      simpa only [e, List.nil_append] using hd
  have hsbF : ∀ b ∈ F' ++ objBlocks L, b ≠ sb := fun b hb e =>
    (List.nodup_cons.mp hbase).1 (e ▸ hb)
  have hF'F : ∀ b ∈ F', b ∈ F := fun b hb => by
    cases hv.src with
    | pop e _ => rw [e]; exact List.mem_cons_of_mem _ hb
    | fresh _ e _ => rw [e] at hb; cases hb
  have hFold : ∀ b ∈ F' ++ objBlocks L, b ∈ F ++ objBlocks L := fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact List.mem_append_left _ (hF'F b hb)
    · exact List.mem_append_right _ hb
  -- a byte of an old block other than `sb` keeps its value
  have hkeep : ∀ b ∈ F' ++ objBlocks L, ∀ a, b.In a → imgM Mt' a = imgM Mt a := by
    intro b hb a ha
    have hbH := hold b (hFold b hb)
    have fb := hi.blk (List.mem_append_right _ hbH)
    have h1 := fb.lo
    simp only [heapStart, Blk.In, Blk.pay] at h1 ha
    refine hv.frame a (live_not_alloc hi hbH ha)
      (fun hs => live_apart hi' (hsub b hbH) hsbL (hsbF b hb) ha hs) ?_
    simp only [bcFreeBytes, bcFreeAddr]; omega
  have hdb : w.db ∈ objBlocks L := by
    obtain ⟨o, ho, hoo, he⟩ := h.views.owner hw
    rw [← he]; exact mem_objBlocks_db ho hoo
  have hwdb : w.db ≠ sb := hsbF _ (List.mem_append_right _ hdb)
  have fsb := hi'.blk (List.mem_append_right _ hsbL)
  have hsz := hv.sSz
  have s1 := fsb.lo; have s2 := fsb.fin; have s3 := fsb.top; have s4 := fsb.al
  simp only [heapStart, heapEnd, Blk.fin] at s1 s2 s3
  have hdl := hwb.dLo; have hdf := hwb.dFit
  have hvl := hws.vLo; have hvh := hws.vHi
  simp only [heapStart, heapEnd] at hvl hvh
  -- the new view's digits lie in `w`'s buffer, apart from `sb`
  have hdig : ∀ i, i < k → ¬ sb.In (w.rep.val + off + i) := fun i hi hs =>
    live_apart hi' (hsub _ hwb.dLive) hsbL hwdb
      ⟨by omega, by simp only [Blk.fin, Blk.pay] at hdf ⊢; omega⟩ hs
  have hsep : w.rep.val + off + k ≤ sb.pay ∨ sb.pay + 40 ≤ w.rep.val + off := by
    refine Classical.byContradiction fun hc => ?_
    have hc' := not_or.mp hc
    exact hdig (max (w.rep.val + off) sb.pay - (w.rep.val + off)) (by omega)
      ⟨by simp only [Blk.pay] at hc' ⊢; omega, by simp only [Blk.fin, Blk.pay] at hc' ⊢; omega⟩
  have hget : ((w.rep.ds.drop off).take k).getD 0 0 = w.rep.ds.getD off 0 ∧
      ∀ i, i < k → ((w.rep.ds.drop off).take k).getD i 0 = w.rep.ds.getD (off + i) 0 := by
    refine ⟨?_, fun i hi => ?_⟩ <;>
      simp [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, *,
        show 0 < k by omega]
  have hnum : NumAt Mt' (viewRep sb.pay w.rep off k) := by
    have hsize := hws.size
    have hdsl := hws.dsLen
    refine ⟨⟨?_, ?_, hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      hv.sign, hv.len, hv.scale, hv.refs, hv.ptr, hv.value, fun i hi => ?_⟩
    all_goals simp only [viewRep, heapStart, heapEnd, Blk.pay, Nat.add_zero] at hi ⊢
    any_goals omega
    · simp only [List.length_take, List.length_drop, hdsl]; omega
    · intro d hd
      exact hws.dig d (List.mem_of_mem_drop (List.mem_of_mem_take hd))
    · have hdi := hwn.digit (off + i) (by omega)
      rw [← Nat.add_assoc] at hdi
      rw [hkeep w.db (List.mem_append_right _ hdb) _
          ⟨by omega, by simp only [Blk.fin, Blk.pay] at hdf ⊢; omega⟩, hdi, hget.2 i hi]
  refine
    { heap := hi'
      dead := ?_
      deadLive := fun b hb => ⟨hsub b (h.deadLive b (hF'F b hb)).1, (h.deadLive b (hF'F b hb)).2⟩
      nums := ?_
      blocks := ?_
      distinct := ?_
      views := .cons (x := viewObj sb w off k) (.inr (h.views.owner (x := w) hw)) h.views
      globOwn := h.globOwn }
  · cases hv.src with
    | pop e _ =>
      have hdt : DeadChain Mt (sb.pay + 16) F' := by
        have := h.dead; rw [e] at this; cases this with | cons _ h => exact h
      refine hdt.move (hv.head.trans hdt.head.symm) fun b hb j hj => ?_
      have hbF := (h.deadLive b (hF'F b hb)).2
      exact hkeep b (List.mem_append_left _ hb) _ ⟨by omega, by simp only [Blk.fin, Blk.pay]; omega⟩
    | fresh _ e _ => rw [e]; exact .nil (by rw [hv.head, e]; rfl)
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hnum
    · refine (h.nums y hy).frame fun a ha => ?_
      rcases NumObj.foot_blocks (h.nums y hy) (h.blocks y hy) ha with hs | hd
      · exact hkeep _ (List.mem_append_right _ (mem_objBlocks hy)) a hs
      · obtain ⟨o, ho, hoo, he⟩ := h.views.owner hy
        exact hkeep _ (List.mem_append_right _ (he ▸ mem_objBlocks_db ho hoo)) a hd
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hsbL, hsub _ hwb.dLive, rfl, hsz, fun ho => absurd rfl ho,
        by simp only [viewObj, viewRep]; omega,
        by simp only [viewObj, viewRep, Blk.fin, Blk.pay] at hdf ⊢; omega⟩
    · have hyb := h.blocks y hy
      exact { hyb with sLive := hsub _ hyb.sLive, dLive := hsub _ hyb.dLive }
  · have hob : objBlocks (viewObj sb w off k :: L) = sb :: objBlocks L := by
      rw [objBlocks_cons, NumObj.blocks_view rfl]; rfl
    rw [hob]
    exact List.perm_middle.nodup_iff.mpr hbase


/-- The struct pushed on `_bc_Free_list` (`sd x, _bc_Free_list` then
`sd old_head, 16(x)`): the stores off the allocator's bytes of `H'`. -/
theorem HeapInv.pushStruct {S : Nat → Prop} {Mt : Mem} {H' : Heap} (hi : HeapInv S Mt H')
    {sb : Blk} (hsb : sb ∈ H'.live) (hsz : 40 ≤ sb.sz) (v w : BitVec 64) :
    HeapInv S (writeLog (writeLog Mt [(bcFreeAddr, 8, v)]) [(sb.pay + 16, 8, w)]) H' := by
  refine hi.transport fun a ha => ?_
  have hn := live_not_alloc hi hsb (a := a)
  rw [imgM_store_miss _ _ ?_, imgM_store_miss _ _ ?_]
  · rcases AllocByte.glob_or_heap hi ha with h1 | h1 <;>
      simp only [freeListAddr, heapStart, heapEnd, bcFreeAddr] at h1 ⊢ <;> omega
  · refine Classical.byContradiction fun hc => hn ⟨by omega, ?_⟩ ha
    simp only [Blk.fin, Blk.pay] at hc ⊢; omega

/-- **The last reference to an owner dropped inline**: `n_refs` stored, the
buffer freed (`FreePost`), the struct pushed on `_bc_Free_list`. -/
theorem BcHeap.freeOwner {S : Nat → Prop} {Mt Mt3 : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (L1 ++ x :: L2)) (ho : x.Owns)
    (hnv : ∀ y ∈ L1, y.db ≠ x.db) {lpre lpost : List Blk} (hl : H.live = lpre ++ x.db :: lpost)
    {v : BitVec 64}
    (hfp : FreePost S (writeLog Mt [(x.rep.p + 12, 4, v)]) Mt3 H
      ⟨H.braw, x.db :: H.free, lpre ++ lpost⟩ x.db lpre lpost) :
    BcHeap S (writeLog (writeLog Mt3 [(bcFreeAddr, 8, BitVec.ofNat 64 x.rep.p)])
        [(x.rep.p + 16, 8, BitVec.ofNat 64 (deadHead F))])
      ⟨H.braw, x.db :: H.free, lpre ++ lpost⟩ (x.sb :: F) (L1 ++ L2) := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hxb := h.blocks x hx
  have hp := hxb.sPay
  have hi := h.heap
  have hsbH' : x.sb ∈ lpre ++ lpost := by
    have : x.sb ∈ lpre ++ x.db :: lpost := hl ▸ hxb.sLive
    rcases List.mem_append.mp this with h1 | h1
    · exact List.mem_append_left _ h1
    · rcases List.mem_cons.mp h1 with e | h1
      · exact absurd e (h.sb_ne_db hx hx)
      · exact List.mem_append_right _ h1
  rw [hp]
  refine h.release ho hnv hl (hfp.inv.pushStruct hsbH' hxb.sSz _ _) ?_ (ldv_store_hit _ _ _) ?_
  · rw [ldv_ld_miss _ _ (by
      have fb := hi.blk (List.mem_append_right _ hxb.sLive)
      have := fb.lo; simp only [heapStart, bcFreeAddr, Blk.pay] at *; omega)]
    exact ldv_store_hit _ _ _
  · intro b hb a ha
    obtain ⟨hbL, hbs, hbd⟩ := h.rest_live hb
    have fb := hi.blk (List.mem_append_right _ hbL)
    have fs := hi.blk (List.mem_append_right _ hxb.sLive)
    have l1 := fb.lo; have l2 := fs.lo
    have hnx : ¬ x.sb.In a := fun hs => live_apart hi hbL hxb.sLive hbs ha hs
    have hxz := hxb.sSz
    have e1 : x.sb.pay = x.sb.h + 16 := rfl
    simp only [Blk.In, Blk.fin, Blk.pay, heapStart] at ha hnx l1 l2 ⊢
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by simp only [bcFreeAddr]; omega),
      hfp.frame a (live_not_alloc hi hbL ha), imgM_store_miss _ _ (by omega)]

/-- **The last reference to a view dropped inline**: `n_refs` stored, the
struct pushed on `_bc_Free_list`. -/
theorem BcHeap.freeView {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (L1 ++ x :: L2)) (hv : ¬ x.Owns)
    (v : BitVec 64) :
    BcHeap S (writeLog (writeLog (writeLog Mt [(x.rep.p + 12, 4, v)])
        [(bcFreeAddr, 8, BitVec.ofNat 64 x.rep.p)]) [(x.rep.p + 16, 8, BitVec.ofNat 64 (deadHead F))])
      H (x.sb :: F) (L1 ++ L2) := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hxb := h.blocks x hx
  have hp := hxb.sPay
  have hi := h.heap
  have fs := hi.blk (List.mem_append_right _ hxb.sLive)
  have := fs.lo
  rw [hp]
  have hi1 : HeapInv S (writeLog Mt [(x.sb.pay + 12, 4, v)]) H := hi.transport fun a ha => by
    have hn := live_not_alloc hi hxb.sLive (a := a)
    refine imgM_store_miss _ _ (Classical.byContradiction fun hc => hn ⟨by omega, ?_⟩ ha)
    have := hxb.sSz
    simp only [Blk.fin, Blk.pay] at hc ⊢; omega
  refine h.releaseView hv (hi1.pushStruct hxb.sLive hxb.sSz _ _) ?_ (ldv_store_hit _ _ _) ?_
  · rw [ldv_ld_miss _ _ (by simp only [heapStart, bcFreeAddr, Blk.pay] at *; omega)]
    exact ldv_store_hit _ _ _
  · intro b hb a ha
    obtain ⟨hbL, hbs, _⟩ := h.rest_live hb
    have fb := hi.blk (List.mem_append_right _ hbL)
    have := fb.lo
    have hnx : ¬ x.sb.In a := fun hs => live_apart hi hbL hxb.sLive hbs ha hs
    have hxz := hxb.sSz
    simp only [Blk.In, Blk.fin, Blk.pay, heapStart] at ha hnx this ⊢
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by simp only [bcFreeAddr]; omega),
      imgM_store_miss _ _ (by omega)]

end Dc.Mach
