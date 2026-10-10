import Dc.Mach.DcArrSet

/-!
# Rotating the stack (M9)

`dc_stack_rotate (n)` at `0x80003768` moves the node `k = min(|n| - 1,
depth - 1)` positions down to the top (`n > 0`) or the top node down to
position `k` (`n < 0`), relinking the nodes in place (`rotate`).

- `DcAt.permStk`: the stack's nodes relinked into another order; the stores
  touch only the nodes' link words and `dc_stack`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- An `LChain` with a weaker node predicate. -/
theorem LChain.imp {α : Type} {Mt : Mem} {off : Nat} {P P' : Blk → α → Prop} :
    ∀ {a : Nat} {l : List (Blk × α)}, LChain Mt off P a l →
      (∀ bx ∈ l, P bx.1 bx.2 → P' bx.1 bx.2) → LChain Mt off P' a l
  | _, _, .nil h, _ => .nil h
  | _, _, .cons h hp hl, hq =>
    .cons h (hq _ List.mem_cons_self hp) (hl.imp fun bx hm => hq bx (List.mem_cons_of_mem _ hm))

theorem DcG.blocks_permStk (G : DcG) {l' : List (Blk × GV)} (hp : l'.Perm G.stk) :
    ({ G with stk := l' } : DcG).blocks.Perm G.blocks := by
  simp only [DcG.blocks]
  exact ((hp.map _).append_right _).append_right _ |>.append_right _

theorem DcG.vals_permStk (G : DcG) {l' : List (Blk × GV)} (hp : l'.Perm G.stk) :
    ({ G with stk := l' } : DcG).vals.Perm G.vals := by
  simp only [DcG.vals]
  exact (hp.map _).append_right _

/-- The bytes `dc_stack_rotate` may store: `dc_stack` and the stack nodes'
link words. -/
def StkLinks (G : DcG) (x : Nat) : Prop :=
  StkWord x ∨ ∃ bg ∈ G.stk, bg.1.pay + 24 ≤ x ∧ x < bg.1.pay + 32

/-- **The stack relinked**: the nodes of `G.stk` in the order `l'`, the
data `m'`; the memory changes only at `dc_stack` and the nodes' link words. -/
theorem DcAt.permStk {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {l' : List (Blk × GV)} {m' : List Val}
    (h : DcAt S M H F L C G hs st) (hp : l'.Perm G.stk) (hm : MemOnly (StkLinks G) M' M)
    (hch : LChain M' 24 (fun _ _ => True) dcStackAddr l')
    (hden : List.Forall₂ (fun (bg : Blk × GV) v => bg.2.Den ⟨L, G.strs⟩ v) l' m') :
    DcAt S M' H F L C { G with stk := l' } hs { st with stack := m' } := by
  have hi := h.heap.heap
  have hsn : ∀ bg ∈ G.stk, SNodeAt M bg.1 bg.2 := fun bg hm' => h.view.stk.forall bg hm'
  have hsl : ∀ bg ∈ G.stk, bg.1 ∈ H.live := fun bg hm' => h.heap.raw.live _ (G.stk_mem hm')
  -- a changed heap byte lies in a stack node, at or above its link word
  have hchg : ∀ x, StkLinks G x → StkWord x ∨ ∃ bg ∈ G.stk, bg.1.In x ∧ bg.1.pay + 24 ≤ x :=
    fun x hx => hx.elim .inl fun ⟨bg, hm', h1, h2⟩ => .inr ⟨bg, hm', by
      have := (hsn bg hm').sz
      simp only [Blk.In, Blk.pay, Blk.fin] at h1 h2 this ⊢; omega, h1⟩
  have hsw : ∀ x, StkWord x → ¬ (heapStart ≤ x ∧ x < heapEnd) := fun x hx h' => by
    simp only [StkWord, dc_addrs, heapStart] at hx h'; omega
  -- bytes of a live block other than the stack nodes are unchanged
  have hoff : ∀ c ∈ H.live, (∀ bg ∈ G.stk, bg.1 ≠ c) → ∀ x, c.In x → imgM M' x = imgM M x :=
    fun c hc hn x hx => hm x fun hP => by
      rcases hchg x hP with hw | ⟨bg, hm', hbx, -⟩
      · exact hsw x hw (live_in_heap hi hc hx)
      · exact live_apart hi (hsl bg hm') hc (hn bg hm') hbx hx
  -- the first 24 bytes of a stack node are unchanged
  have hlow : ∀ bg ∈ G.stk, ∀ x, bg.1.pay ≤ x → x < bg.1.pay + 24 → imgM M' x = imgM M x :=
    fun bg hm' x h1 h2 => hm x fun hP => by
      have hsz := (hsn bg hm').sz
      have hbx : bg.1.In x := by simp only [Blk.In, Blk.pay, Blk.fin] at h1 h2 hsz ⊢; omega
      rcases hchg x hP with hw | ⟨bg', hm'', hbx', h3⟩
      · exact hsw x hw (live_in_heap hi (hsl bg hm') hbx)
      · by_cases he : bg'.1 = bg.1
        · rw [he] at h3; omega
        · exact live_apart hi (hsl bg' hm'') (hsl bg hm') he hbx' hbx
  have hnheap : ∀ x, ¬ (heapStart ≤ x ∧ x < heapEnd) → ¬ StkWord x → imgM M' x = imgM M x :=
    fun x hx hs' => hm x fun hP => by
      rcases hchg x hP with hw | ⟨bg, hm', hbx, -⟩
      · exact hs' hw
      · exact hx (live_in_heap hi (hsl bg hm') hbx)
  -- blocks of the state off the stack
  have hstkB : ∀ c ∈ G.blocks, (∃ bg ∈ G.stk, bg.1 = c) ∨ ∀ bg ∈ G.stk, bg.1 ≠ c := fun c _ => by
    by_cases hc : ∃ bg ∈ G.stk, bg.1 = c
    · exact .inl hc
    · exact .inr fun bg hm' e => hc ⟨bg, hm', e⟩
  have hnd := h.nodup
  have hsplit : ∀ c, c ∈ G.stk.map (·.1) → ∀ c' ∈ G.blocks, c' ∉ G.stk.map (·.1) → c ≠ c' :=
    fun c hc c' _ hc' e => hc' (e ▸ hc)
  have hblkP := G.blocks_permStk hp
  -- the number heap
  have hb0 : BcHeap S (G.rawsOff (G.stk.map (·.1)) M) M H F L :=
    h.heap.subRaw (fun c hc => (DcG.mem_rawsOff.mp hc).1) fun _ _ _ _ => rfl
  have hb1 : BcHeap S (G.rawsOff (G.stk.map (·.1)) M) M' H F L :=
    hb0.transportOwn (fun x hx => hm x fun hP => by
        rcases hchg x hP with hw | ⟨bg, hm', hbx, -⟩
        · rcases AllocByte.glob_or_heap hi hx with h1 | h1
          · simp only [StkWord, dc_addrs, freeListAddr] at hw h1; omega
          · exact hsw x hw h1
        · exact live_not_alloc hi (hsl bg hm') hbx hx)
      (fun c hc x hx => by
        rcases List.mem_append.mp hc with hc | hc
        · exact hoff c (h.heap.owned_live (List.mem_append_left _ hc))
            (fun bg hm' e => h.heap.raw.out _ (G.stk_mem hm') (e ▸ hc)) x hx
        · obtain ⟨hcG, hcE⟩ := DcG.mem_rawsOff.mp hc
          exact hoff c (h.heap.raw.live c hcG)
            (fun bg hm' e => hcE (e ▸ List.mem_map.mpr ⟨bg, hm', rfl⟩)) x hx)
      fun j hj => hnheap _ (fun h' => by simp only [bcFreeAddr, heapStart] at h'; omega)
        fun h' => by simp only [StkWord, bcFreeAddr, dc_addrs] at h'; omega
  have hb2 := hb1.addRaws (bs := G.stk.map (·.1))
    (fun c hc => by obtain ⟨bg, hm', rfl⟩ := List.mem_map.mp hc; exact hsl bg hm')
    fun c hc => by
      obtain ⟨bg, hm', rfl⟩ := List.mem_map.mp hc
      exact h.heap.raw.out _ (G.stk_mem hm')
  -- unchanged blocks of the state
  have hGoff : ∀ c ∈ G.blocks, (∀ bg ∈ G.stk, bg.1 ≠ c) → ∀ x, c.In x → imgM M' x = imgM M x :=
    fun c hc hn => hoff c (h.heap.raw.live c hc) hn
  have hnotStk : ∀ c ∈ G.blocks, c ∉ G.stk.map (·.1) → ∀ bg ∈ G.stk, bg.1 ≠ c :=
    fun c _ hc bg hm' e => hc (List.mem_map.mpr ⟨bg, hm', e⟩)
  -- stack blocks are not register or string blocks
  have hdisj : ∀ c ∈ G.stk.map (·.1), c ∉ (List.range 256).flatMap
      (fun r => (G.regs r).flatMap RLev.blocks) ++ G.strs.flatMap (fun o => [o.hb, o.tb]) ++
        G.lbuf.toList := fun c hc hc' => by
    simp only [DcG.blocks, List.append_assoc] at hnd
    exact (List.nodup_append.mp hnd).2.2 c hc c (by simpa [List.append_assoc] using hc') rfl
  have hglob : ∀ x, DcGlob x → ¬ ChainWords x → imgM M' x = imgM M x := fun x hx hc =>
    hnheap x (fun h' => by have := hx.lt; omega) fun hs' => hc (.inl hs')
  refine
    { heap := hb2.subRaw (fun c hc => ?_) fun _ _ _ _ => rfl
      nodup := hblkP.nodup_iff.mpr hnd
      view := h.view.withChains rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun o ho x hx => hx.elim
          (fun hx => hGoff _ (G.str_mem ho).1 (fun bg hm' e => hdisj _
            (List.mem_map.mpr ⟨bg, hm', rfl⟩) (by
              rw [e]; simp only [List.mem_append, List.mem_flatMap]
              exact .inl (.inr ⟨o, ho, by simp⟩))) x hx)
          fun hx => hGoff _ (G.str_mem ho).2 (fun bg hm' e => hdisj _
            (List.mem_map.mpr ⟨bg, hm', rfl⟩) (by
              rw [e]; simp only [List.mem_append, List.mem_flatMap]
              exact .inl (.inr ⟨o, ho, by simp⟩))) x hx)
        hglob ?_ fun r hr => ?_
      den := ?_
      glob := h.glob
      col := h.col }
  · have hc' := hblkP.mem_iff.mp hc
    by_cases hcS : c ∈ G.stk.map (·.1)
    · exact List.mem_append_left _ hcS
    · exact List.mem_append_right _ (DcG.mem_rawsOff.mpr ⟨hc', hcS⟩)
  · refine hch.imp fun bg hm' _ => ?_
    have hm0 := hp.mem_iff.mp hm'
    have hq := hsn bg hm0
    exact ⟨DatAt.congr16 (fun x h1 h2 => hlow bg hm0 x h1 (by omega)) hq.dat,
      (ldv_congr .ld fun j hj => hlow bg hm0 _ (by omega) (by simp only [widthOfM] at hj; omega)).trans
        hq.arr, hq.sz⟩
  · exact regChain_frame (h.view.regs r hr) (ldv_congr .ld fun j hj => hnheap _ (by
      simp only [widthOfM, heapStart, regAddr, dc_addrs] at hj ⊢; omega) fun hc => by
        simp only [widthOfM, StkWord, regAddr, dc_addrs] at hj hc; omega)
      fun be hmm c hc x hx => hGoff c (G.lev_mem hr hmm hc) (fun bg hm' e => hdisj _
        (List.mem_map.mpr ⟨bg, hm', rfl⟩) (by
          rw [e]; simp only [List.mem_append, List.mem_flatMap]
          exact .inl (.inl ⟨r, List.mem_range.mpr hr, be, hmm, hc⟩))) x hx
  · have hd := h.den
    have hcount : ∀ y, (({ G with stk := l' } : DcG).vals ++ hs).count y = (G.vals ++ hs).count y :=
      fun y => by
        have := List.perm_iff_count.mp (G.vals_permStk hp) y
        simp only [List.count_append] at this ⊢; omega
    exact
      { hd with
        stk := hden
        numRefs := fun x hx => by rw [hcount]; exact hd.numRefs x hx
        strRefs := fun o ho => by rw [hcount]; exact hd.strRefs o ho }

end Dc.Mach
