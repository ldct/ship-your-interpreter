import Dc.Mach.DcArray

/-!
# Storing into a register array (M9)

`dc_array_set (r, i, value)` at `0x80003c7c` replaces the datum of the node
with index `i` in register `r`'s top array, or inserts a fresh node before
the first node with a larger index (`arrSet`).

- `DcAt.setArr`: register `r`'s head level gets a new array chain `arr'`,
  built from the old nodes and fresh blocks `N`; the stores touch only those
  blocks and the level's array word. Both the replacement (viewed through a
  pending datum window) and the insertion are instances.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- Register `r`'s head level `be` shares no block with the rest of the state. -/
structure LevOnly (G : DcG) (r : Nat) (be : Blk × RLev) (l : List (Blk × RLev)) : Prop where
  stk : ∀ bg ∈ G.stk, bg.1 ∉ RLev.blocks be
  regs : ∀ r', r' < 256 → r' ≠ r → ∀ be' ∈ G.regs r', ∀ c ∈ RLev.blocks be', c ∉ RLev.blocks be
  tail : ∀ be' ∈ l, ∀ c ∈ RLev.blocks be', c ∉ RLev.blocks be
  strs : ∀ o ∈ G.strs, o.hb ∉ RLev.blocks be ∧ o.tb ∉ RLev.blocks be
  nodup : (RLev.blocks be).Nodup

theorem DcG.levOnly {G : DcG} {r : Nat} {be : Blk × RLev} {l : List (Blk × RLev)}
    (hnd : G.blocks.Nodup) (hr : r < 256) (hl : G.regs r = be :: l) : LevOnly G r be l := by
  obtain ⟨P, Q, hPQ, hf, -⟩ := flatMap_range_upd (f := fun r' => (G.regs r').flatMap RLev.blocks)
    (g := fun r' => (G.regs r').flatMap RLev.blocks) hr fun _ _ => rfl
  have hcount : ∀ c, (G.stk.map (·.1)).count c +
      (P.flatMap fun r' => (G.regs r').flatMap RLev.blocks).count c + (RLev.blocks be).count c +
      (l.flatMap RLev.blocks).count c + (Q.flatMap fun r' => (G.regs r').flatMap RLev.blocks).count c +
      (G.strs.flatMap fun o => [o.hb, o.tb]).count c ≤ 1 := fun c => by
    have h1 := nodup_count_le_one hnd c
    unfold DcG.blocks at h1
    rw [hf, hl] at h1
    simp only [List.count_append, List.flatMap_cons] at h1
    omega
  have z : ∀ (l' : List Blk) (c : Blk), l'.count c = 0 → ∀ c' ∈ l', c' ≠ c := fun l' c h0 c' hcl e => by
    subst e; exact List.count_eq_zero.mp h0 hcl
  have pos : ∀ c ∈ RLev.blocks be, 1 ≤ (RLev.blocks be).count c := fun c hc =>
    List.count_pos_iff.mpr hc
  refine ⟨fun bg hbg hc => z (G.stk.map (·.1)) bg.1 (by have := hcount bg.1; have := pos _ hc; omega) _
      (List.mem_map.mpr ⟨bg, hbg, rfl⟩) rfl,
    fun r' hr' hne be' hbe c hcm hc => ?_,
    fun be' hbe c hcm hc => z (l.flatMap RLev.blocks) c (by have := hcount c; have := pos _ hc; omega) _
      (List.mem_flatMap.mpr ⟨be', hbe, hcm⟩) rfl,
    fun o ho => ⟨fun hc => z (G.strs.flatMap fun o => [o.hb, o.tb]) o.hb (by have := hcount o.hb; have := pos _ hc; omega) _
        (List.mem_flatMap.mpr ⟨o, ho, by simp⟩) rfl,
      fun hc => z (G.strs.flatMap fun o => [o.hb, o.tb]) o.tb (by have := hcount o.tb; have := pos _ hc; omega) _
        (List.mem_flatMap.mpr ⟨o, ho, by simp⟩) rfl⟩,
    List.nodup_iff_count.mpr fun c => by have := hcount c; omega⟩
  have hm : r' ∈ P ++ r :: Q := hPQ ▸ List.mem_range.mpr hr'
  rcases List.mem_append.mp hm with hm | hm
  · exact z (P.flatMap fun r' => (G.regs r').flatMap RLev.blocks) c (by have := hcount c; have := pos _ hc; omega) _
      (List.mem_flatMap.mpr ⟨r', hm, List.mem_flatMap.mpr ⟨be', hbe, hcm⟩⟩) rfl
  · rcases List.mem_cons.mp hm with e | hm
    · exact hne e
    · exact z (Q.flatMap fun r' => (G.regs r').flatMap RLev.blocks) c (by have := hcount c; have := pos _ hc; omega) _
        (List.mem_flatMap.mpr ⟨r', hm, List.mem_flatMap.mpr ⟨be', hbe, hcm⟩⟩) rfl

/-- A datum through a memory agreeing on its 16 bytes. -/
theorem DatAt.congr16 {Mt Mt' : Mem} {a : Nat} {g : GV}
    (hag : ∀ x, a ≤ x → x < a + 16 → imgM Mt' x = imgM Mt x) (h : DatAt Mt a g) : DatAt Mt' a g :=
  ⟨by rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact h.tag,
    by rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact h.ptr⟩

/-- **Register `r`'s top array replaced**: the new chain `arr'` from the
level's array word, its blocks the old array's and the fresh blocks `N`, its
data the old array's data with `hs0` traded for `hs`. The memory changes
only inside `N`, the old array's nodes and the level's array word. -/
theorem DcAt.setArr {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs0 hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {en : Entry} {es : List Entry} {arr' : List (Blk × ANode)}
    {am : List (Nat × Val)} {N : List Blk}
    (h : DcAt S M H F L C G hs0 st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hst : st.regs r = en :: es) (hN : ∀ c ∈ N, DcFresh H F L G c) (hNd : N.Nodup)
    (hperm : (arr'.map (·.1)).Perm (N ++ e.arr.map (·.1)))
    (hcnt : ∀ y, (arr'.map (·.2.v) ++ hs).count y = (e.arr.map (·.2.v) ++ hs0).count y)
    (hm : MemOnly (fun x => InBlocks (N ++ e.arr.map (·.1)) x ∨ (b.pay + 16 ≤ x ∧ x < b.pay + 24)) M' M)
    (hch : LChain M' 24 (ANodeAt M') (b.pay + 16) arr')
    (hden : List.Forall₂ (fun (be : Blk × ANode) (iv : Nat × Val) => be.2.idx = iv.1 ∧
      be.2.v.Den ⟨L, G.strs⟩ iv.2) arr' am)
    (hsd : ∀ g ∈ hs, ∃ v, g.Den ⟨L, G.strs⟩ v) :
    DcAt S M' H F L C (G.setReg r ((b, { e with arr := arr' }) :: l)) hs
      (st.setReg r ({ en with arr := am } :: es)) := by
  have hi := h.heap.heap
  have lo := G.levOnly h.nodup hr hl
  have hbe : (b, e) ∈ G.regs r := by rw [hl]; exact List.mem_cons_self
  have hlevG : ∀ c ∈ RLev.blocks (b, e), c ∈ G.blocks := fun c hc => G.lev_mem hr hbe hc
  have hbG : b ∈ G.blocks := hlevG b List.mem_cons_self
  have hbl := h.heap.raw.live b hbG
  have hchg : ∀ x, InBlocks (N ++ e.arr.map (·.1)) x ∨ (b.pay + 16 ≤ x ∧ x < b.pay + 24) →
      ∃ c, (c ∈ N ∨ c ∈ RLev.blocks (b, e)) ∧ c ∈ H.live ∧ c.In x := fun x hx => by
    rcases hx with ⟨c, hc, hcx⟩ | hw
    · rcases List.mem_append.mp hc with hc | hc
      · exact ⟨c, .inl hc, (hN c hc).live, hcx⟩
      · have hc' : c ∈ RLev.blocks (b, e) := List.mem_cons_of_mem _ hc
        exact ⟨c, .inr hc', h.heap.raw.live c (hlevG c hc'), hcx⟩
    · have hv0 := h.view.regs r hr
      rw [hl] at hv0
      have hsz : 32 ≤ b.sz := by cases hv0 with | cons _ hp _ => exact hp.sz
      exact ⟨b, .inr List.mem_cons_self, hbl, by simp only [Blk.In, Blk.pay, Blk.fin] at hw ⊢; omega⟩
  -- bytes of other live blocks are unchanged
  have hoff : ∀ c' ∈ H.live, c' ∉ N → c' ∉ RLev.blocks (b, e) → ∀ x, c'.In x →
      imgM M' x = imgM M x := fun c' hc' hn hlv x hx => hm x fun hP => by
    obtain ⟨c, hc, hcl, hcx⟩ := hchg x hP
    exact live_apart hi hc' hcl (fun e => hc.elim (fun hc => hn (e ▸ hc)) fun hc => hlv (e ▸ hc)) hx hcx
  have hGoff : ∀ c' ∈ G.blocks, c' ∉ RLev.blocks (b, e) → ∀ x, c'.In x → imgM M' x = imgM M x :=
    fun c' hc' hlv => hoff c' (h.heap.raw.live c' hc') (fun hn => (hN c' hn).notG hc') hlv
  have hnheap : ∀ x, ¬ (heapStart ≤ x ∧ x < heapEnd) → imgM M' x = imgM M x := fun x hx =>
    hm x fun hP => by
      obtain ⟨c, -, hcl, hcx⟩ := hchg x hP
      exact hx (live_in_heap hi hcl hcx)
  have hglob : ∀ x, DcGlob x → imgM M' x = imgM M x := fun x hx =>
    hnheap x fun h' => by have := hx.lt; omega
  -- the new block list
  have hperm' : (G.setReg r ((b, { e with arr := arr' }) :: l)).blocks.Perm (N ++ G.blocks) := by
    rw [List.perm_iff_count]
    intro y
    have h1 := G.setReg_blocks_count hr ((b, { e with arr := arr' }) :: l) y
    have h2 := List.perm_iff_count.mp hperm y
    rw [hl] at h1
    simp only [List.flatMap_cons, RLev.blocks, List.count_append, List.count_cons] at h1 h2 ⊢
    omega
  have hnd' : (N ++ G.blocks).Nodup := List.nodup_append.mpr ⟨hNd, h.nodup,
    fun c hc c' hc' e => (hN c hc).notG (e ▸ hc')⟩
  -- the number heap
  have hb0 : BcHeap S (G.rawsOff (RLev.blocks (b, e)) M) M H F L :=
    h.heap.subRaw (fun c hc => (DcG.mem_rawsOff.mp hc).1) fun _ _ _ _ => rfl
  have hb1 : BcHeap S (G.rawsOff (RLev.blocks (b, e)) M) M' H F L :=
    hb0.transportOwn (fun x hx => hm x fun hP => by
        obtain ⟨c, -, hcl, hcx⟩ := hchg x hP
        exact live_not_alloc hi hcl hcx hx)
      (fun c hc x hx => by
        rcases List.mem_append.mp hc with hc | hc
        · exact hoff c (h.heap.owned_live (List.mem_append_left _ hc))
            (fun hn => (hN c hn).notNum hc) (fun hlv => h.heap.raw.out c (hlevG c hlv) hc) x hx
        · obtain ⟨hcG, hcE⟩ := DcG.mem_rawsOff.mp hc
          exact hGoff c hcG hcE x hx)
      fun j hj => hnheap _ fun h' => by simp only [bcFreeAddr, heapStart] at h'; omega
  have hb2 := hb1.addRaws (bs := N ++ RLev.blocks (b, e))
    (fun c hc => (List.mem_append.mp hc).elim (fun hc => (hN c hc).live)
      fun hc => h.heap.raw.live c (hlevG c hc))
    fun c hc => (List.mem_append.mp hc).elim (fun hc => (hN c hc).notNum)
      fun hc => h.heap.raw.out c (hlevG c hc)
  -- the old register chain and denotation
  have hv0 := h.view.regs r hr
  rw [hl] at hv0
  have hd0 := h.den.regs r hr
  rw [hl, hst] at hd0
  cases hv0 with
  | cons hw0 hp0 hrest0 =>
  cases hd0 with
  | cons hen hdrest =>
  have hsz := hp0.sz
  refine
    { heap := hb2.subRaw (fun c hc => ?_) fun _ _ _ _ => rfl
      nodup := hperm'.nodup_iff.mpr hnd'
      view := h.view.withChains rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun o ho x hx => hx.elim (fun hx => hGoff _ (G.str_mem ho).1 (lo.strs o ho).1 x hx)
          fun hx => hGoff _ (G.str_mem ho).2 (lo.strs o ho).2 x hx)
        (fun x hx _ => hglob x hx)
        (stkChain_frame h.view.stk (ldv_congr .ld fun j hj => hglob _ (by
          simp only [widthOfM, DcGlob, dc_addrs] at hj ⊢; omega))
          fun bg hmm x hx => hGoff _ (G.stk_mem hmm) (lo.stk bg hmm) x hx) fun r' hr' => ?_
      den := ?_
      glob := h.glob
      col := h.col }
  · rcases List.mem_append.mp (hperm'.mem_iff.mp hc) with hc | hc
    · exact List.mem_append_left _ (List.mem_append_left _ hc)
    · by_cases hcE : c ∈ RLev.blocks (b, e)
      · exact List.mem_append_left _ (List.mem_append_right _ hcE)
      · exact List.mem_append_right _ (DcG.mem_rawsOff.mpr ⟨hc, hcE⟩)
  · have e1 : (G.setReg r ((b, { e with arr := arr' }) :: l)).regs r' =
        if r' = r then (b, { e with arr := arr' }) :: l else G.regs r' := rfl
    rw [e1]
    split
    · subst_vars
      have hdat : ∀ x, b.pay ≤ x → x < b.pay + 16 → imgM M' x = imgM M x := fun x h1 h2 =>
        hm x fun hP => by
          rcases hP with ⟨c, hc, hcx⟩ | hw
          · rcases List.mem_append.mp hc with hc | hc
            · exact live_apart hi (hN c hc).live hbl (fun e => (hN c hc).notG (e ▸ hbG)) hcx
                (by simp only [Blk.In, Blk.pay, Blk.fin] at h1 h2 hcx hsz ⊢; omega)
            · obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hc
              have hne : bn.1 ≠ b := fun e => List.nodup_cons.mp lo.nodup |>.1
                (e ▸ List.mem_map.mpr ⟨bn, hbn, rfl⟩)
              exact live_apart hi (h.heap.raw.live _ (G.arr_mem hr' hbe hbn)) hbl hne hcx
                (by simp only [Blk.In, Blk.pay, Blk.fin] at h1 h2 hcx hsz ⊢; omega)
          · omega
      refine .cons ((ldv_congr .ld fun j hj => hglob _ (by
          simp only [widthOfM, DcGlob, regAddr, dc_addrs] at hj ⊢; omega)).trans hw0)
        ⟨?_, hch, hsz⟩ (regChain_frame hrest0 (ldv_congr .ld fun j hj => hm _ fun hP => by
          rcases hP with ⟨c, hc, hcx⟩ | hw
          · rcases List.mem_append.mp hc with hc | hc
            · exact live_apart hi (hN c hc).live hbl (fun e => (hN c hc).notG (e ▸ hbG)) hcx
                (by simp only [widthOfM, Blk.In, Blk.pay, Blk.fin] at hj hcx hsz ⊢; omega)
            · obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hc
              have hne : bn.1 ≠ b := fun e => List.nodup_cons.mp lo.nodup |>.1
                (e ▸ List.mem_map.mpr ⟨bn, hbn, rfl⟩)
              exact live_apart hi (h.heap.raw.live _ (G.arr_mem hr' hbe hbn)) hbl hne hcx
                (by simp only [widthOfM, Blk.In, Blk.pay, Blk.fin] at hj hcx hsz ⊢; omega)
          · simp only [widthOfM] at hj; omega)
          fun be hmm c hc x hx => hGoff c (G.lev_mem hr' (by rw [hl]; exact List.mem_cons_of_mem _ hmm) hc)
            (lo.tail be hmm c hc) x hx)
      have hd := hp0.dat
      revert hd
      cases e.v with
      | some g => exact fun hd => DatAt.congr16 hdat hd
      | none =>
        intro hd
        simp only at hd ⊢
        rw [ldv_congr .lw fun j hj => hdat _ (by omega) (by simp only [widthOfM] at hj; omega)]
        exact hd
    · exact regChain_frame (h.view.regs r' hr') (ldv_congr .ld fun j hj => hglob _ (by
        simp only [widthOfM, DcGlob, regAddr, dc_addrs] at hj ⊢; omega))
        fun be hmm c hc x hx => hGoff c (G.lev_mem hr' hmm hc) (lo.regs r' hr' ‹_› be hmm c hc) x hx
  · have hd := h.den
    have hcount : ∀ y, ((G.setReg r ((b, { e with arr := arr' }) :: l)).vals ++ hs).count y =
        (G.vals ++ hs0).count y := fun y => by
      have h1 := G.setReg_vals_count hr ((b, { e with arr := arr' }) :: l) y
      have h2 := hcnt y
      rw [hl] at h1
      simp only [List.flatMap_cons, RLev.vals, List.count_append] at h1 h2 ⊢
      omega
    refine { hd with
      regs := fun r' hr' => ?_
      regsHi := fun r' hr' => ?_
      hsDen := hsd
      numRefs := fun x hx => by rw [hcount]; exact hd.numRefs x hx
      strRefs := fun o ho => by rw [hcount]; exact hd.strRefs o ho }
    · simp only [DcG.setReg, St.setReg]
      split
      · subst_vars; exact .cons ⟨hen.val, hden⟩ hdrest
      · exact hd.regs r' hr'
    · have hne : r' ≠ r := by omega
      simp only [DcG.setReg, St.setReg, hne, ite_false]; exact hd.regsHi r' hr'

end Dc.Mach
