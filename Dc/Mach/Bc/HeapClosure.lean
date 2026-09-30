import Dc.Mach.Bc.Heap

/-!
# Number-heap footprint and frame closure

The allocator's block separation and the number heap's block uniqueness
supply disjoint number footprints. Memory transport reuses the allocator,
dead-chain, and number frame lemmas at their respective owned bytes.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

private theorem objBlocks_separate {L : List NumObj} (hd : (objBlocks L).Nodup)
    {x y : NumObj} (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y)
    {b c : Blk} (hb : b ∈ [x.sb, x.db]) (hc : c ∈ [y.sb, y.db]) : b ≠ c := by
  induction L with
  | nil => cases hx
  | cons z L ih =>
    have hd' : ([z.sb, z.db] ++ objBlocks L).Nodup := hd
    obtain ⟨_, ht, hcross⟩ := List.nodup_append.mp hd'
    rcases List.mem_cons.mp hx with rfl | hxt
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact False.elim (hne rfl)
      · exact hcross b hb c (List.mem_flatMap.mpr ⟨y, hy, hc⟩)
    · rcases List.mem_cons.mp hy with rfl | hyt
      · exact fun he => hcross c hc b (List.mem_flatMap.mpr ⟨x, hxt, hb⟩) he.symm
      · exact ih ht hxt hyt

/-- Distinct represented objects cannot share a byte: their allocated blocks
are distinct by `BcHeap.distinct` and apart by `HeapInv.apart`. -/
theorem BcHeap.foot_disjoint {S : Nat → Prop} {Mt : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} (h : BcHeap S Mt H F L)
    {x y : NumObj} (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y)
    {a : Nat} (hax : x.rep.Foot a) (hay : y.rep.Foot a) : False := by
  have hd := (List.nodup_append.mp h.distinct).2.1
  have hxb := h.blocks x hx
  have hyb := h.blocks y hy
  have hs : ∀ {b c : Blk}, b ∈ [x.sb, x.db] → c ∈ [y.sb, y.db] → b ≠ c :=
    fun hb hc => objBlocks_separate hd hx hy hne hb hc
  rcases NumObj.foot_blocks (h.nums x hx) hxb hax with hxs | hxd <;>
    rcases NumObj.foot_blocks (h.nums y hy) hyb hay with hys | hyd
  · exact live_apart h.heap hxb.sLive hyb.sLive (hs (by simp) (by simp)) hxs hys
  · exact live_apart h.heap hxb.sLive hyb.dLive (hs (by simp) (by simp)) hxs hyd
  · exact live_apart h.heap hxb.dLive hyb.sLive (hs (by simp) (by simp)) hxd hys
  · exact live_apart h.heap hxb.dLive hyb.dLive (hs (by simp) (by simp)) hxd hyd

/-- Every represented number footprint is disjoint from allocator metadata. -/
theorem BcHeap.foot_not_alloc {S : Nat → Prop} {Mt : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} (h : BcHeap S Mt H F L)
    {x : NumObj} (hx : x ∈ L) {a : Nat} (ha : x.rep.Foot a) : ¬ AllocByte H a := by
  have hb := h.blocks x hx
  rcases NumObj.foot_blocks (h.nums x hx) hb ha with hs | hd
  · exact live_not_alloc h.heap hb.sLive hs
  · exact live_not_alloc h.heap hb.dLive hd

/-- Transport through memory agreement on the three owned regions. The
allocator frame supplies `ha`, live-block frames supply `hl`, and the
caller's global-word frame supplies `hg`. No unrelated bytes are read. -/
theorem BcHeap.transport {S : Nat → Prop} {Mt Mt' : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} (h : BcHeap S Mt H F L)
    (ha : ∀ a, AllocByte H a → imgM Mt' a = imgM Mt a)
    (hl : ∀ b ∈ H.live, ∀ a, b.In a → imgM Mt' a = imgM Mt a)
    (hg : ∀ j, j < 8 → imgM Mt' (bcFreeAddr + j) = imgM Mt (bcFreeAddr + j)) :
    BcHeap S Mt' H F L := by
  refine { h with heap := h.heap.transport ha, dead := ?_, nums := ?_ }
  · refine h.dead.frame (ldv_congr .ld hg) ?_
    intro b hb j hj
    obtain ⟨hbl, hsz⟩ := h.deadLive b hb
    apply hl b hbl
    simp only [Blk.In, Blk.fin, Blk.pay]
    omega
  · intro x hx
    refine (h.nums x hx).frame fun a hax => ?_
    have hb := h.blocks x hx
    rcases NumObj.foot_blocks (h.nums x hx) hb hax with hs | hd
    · exact hl x.sb hb.sLive a hs
    · exact hl x.db hb.dLive a hd

/-- The source of a newly allocated number retains all previous live blocks. -/
theorem NewSrc.live_mono {H H' : Heap} {F F' : List Blk} {x : NumObj}
    (h : NewSrc H H' F F' x) {b : Blk} (hb : b ∈ H.live) : b ∈ H'.live := by
  cases h with
  | reuse _ he => rw [he]; exact List.mem_cons_of_mem _ hb
  | fresh _ _ he => rw [he]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb)

/-- Both blocks of a new number are live and cover its represented bytes. -/
theorem NewNumPost.blocks {S : Nat → Prop} {Mt Mt' : Mem} {H H' : Heap}
    {F F' : List Blk} {fr : Nat → Prop} {len scale : Nat} {x : NumObj}
    (h : NewNumPost S Mt Mt' H H' F F' fr len scale x)
    (hd : ∀ b ∈ F, b ∈ H.live) : x.Blocks H' := by
  have hl : x.sb ∈ H'.live ∧ x.db ∈ H'.live := by
    cases h.src with
    | reuse he hf =>
      rw [hf]
      exact ⟨List.mem_cons_of_mem _ (hd _ (by rw [he]; exact List.mem_cons_self)), List.mem_cons_self⟩
    | fresh _ _ hf => rw [hf]; simp
  refine ⟨hl.1, hl.2, ?_, h.sSz, ?_, ?_⟩
  · rw [h.rep]; rfl
  · rw [h.rep]; rfl
  · rw [h.rep]
    change x.db.pay + len + scale ≤ x.db.fin
    have := h.dSz
    simp only [Blk.fin, Blk.pay] at *
    omega

/-- The allocator's live list contains each block at most once. -/
theorem HeapInv.live_nodup {S : Nat → Prop} {Mt : Mem} {H : Heap}
    (h : HeapInv S Mt H) : H.live.Nodup := by
  have hp := (List.pairwise_append.mp h.apart).2.1
  exact hp.imp fun {b c} hab he => by
    subst c
    exact Blk.Apart.irrefl b hab

/-- A successful `bc_new_num` extends the number heap by its returned object.
The old objects survive the actual allocation's `LiveFrame`; `NewSrc` supplies
freshness and the exact dead-chain update. -/
theorem NewNumPost.insert {S : Nat → Prop} {Mt Mt' : Mem} {H H' : Heap}
    {F F' : List Blk} {fr : Nat → Prop} {len scale : Nat} {x : NumObj}
    {L : List NumObj} (h : BcHeap S Mt H F L)
    (p : NewNumPost S Mt Mt' H H' F F' fr len scale x) :
    BcHeap S Mt' H' F' (x :: L) := by
  have hold : ∀ b ∈ F ++ objBlocks L, b ∈ H.live := by
    intro b hb
    rcases List.mem_append.mp hb with hf | hl
    · exact (h.deadLive b hf).1
    · obtain ⟨y, hy, hb⟩ := List.mem_flatMap.mp hl
      have hby := h.blocks y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact hby.sLive
      · exact hby.dLive
  have hbase : (x.sb :: (F' ++ objBlocks L)).Nodup := by
    cases p.src with
    | reuse he _ => simpa only [he, List.cons_append] using h.distinct
    | fresh he he' hl =>
      have hn := p.inv.live_nodup
      rw [hl] at hn
      obtain ⟨_, hn⟩ := List.nodup_cons.mp hn
      obtain ⟨hsb, _⟩ := List.nodup_cons.mp hn
      rw [he']
      simp only [List.nil_append]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · exact fun hb => hsb (hold _ (List.mem_append_right _ hb))
      · have hd := h.distinct
        simpa only [he, List.nil_append] using hd
  obtain ⟨hsb, hrest⟩ := List.nodup_cons.mp hbase
  have hsub : ∀ b ∈ F', b ∈ F := by
    cases p.src with
    | reuse he _ => rw [he]; exact fun b hb => List.mem_cons_of_mem _ hb
    | fresh _ he _ => rw [he]; exact fun b hb => False.elim (List.not_mem_nil hb)
  have hdb : x.db ∉ x.sb :: (F' ++ objBlocks L) := by
    cases p.src with
    | reuse he hl =>
      have hn := p.inv.head_not_mem hl
      intro hb
      rcases List.mem_cons.mp hb with hb | hb
      · exact hn (hb.symm ▸ hold _ (List.mem_append_left _ (by rw [he]; exact List.mem_cons_self)))
      · rcases List.mem_append.mp hb with hf | ho
        · exact hn (hold _ (List.mem_append_left _ (hsub _ hf)))
        · exact hn (hold _ (List.mem_append_right _ ho))
    | fresh _ he hl =>
      have hn := p.inv.head_not_mem hl
      intro hb
      rcases List.mem_cons.mp hb with hb | hb
      · exact hn (List.mem_cons.mpr (.inl hb))
      · rw [he, List.nil_append] at hb
        exact hn (List.mem_cons_of_mem _ (hold _ (List.mem_append_right _ hb)))
  have hnew := List.nodup_cons.mpr ⟨hdb, hbase⟩
  have horder : (F' ++ x.sb :: x.db :: objBlocks L).Perm
      (x.db :: x.sb :: (F' ++ objBlocks L)) :=
    List.perm_middle.trans ((List.perm_middle.cons x.sb).trans (List.Perm.swap _ _ _))
  refine {
    heap := p.inv
    dead := p.dead
    deadLive := ?_
    nums := ?_
    blocks := ?_
    distinct := ?_
    globOwn := h.globOwn }
  · intro b hb
    obtain ⟨hbl, hsz⟩ := h.deadLive b (hsub b hb)
    exact ⟨p.src.live_mono hbl, hsz⟩
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact p.num
    · have hb := h.blocks y hy
      refine (h.nums y hy).frame fun a ha => ?_
      have hys : y.sb ≠ x.sb := fun he =>
        hsb (List.mem_append_right _ (he ▸ (mem_objBlocks hy).1))
      have hyd : y.db ≠ x.sb := fun he =>
        hsb (List.mem_append_right _ (he ▸ (mem_objBlocks hy).2))
      rcases NumObj.foot_blocks (h.nums y hy) hb ha with hs | hd
      · exact p.live y.sb hb.sLive hys a hs
      · exact p.live y.db hb.dLive hyd a hd
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact p.blocks fun b hb => (h.deadLive b hb).1
    · have hb := h.blocks y hy
      exact { hb with sLive := p.src.live_mono hb.sLive, dLive := p.src.live_mono hb.dLive }
  · exact horder.nodup_iff.mpr hnew

end Dc.Mach
