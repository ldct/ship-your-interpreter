import Dc.Mach.DcArrFree

/-!
# Register levels pushed and popped (M9)

`dc_register_push (r, value)` at `0x80002e24` pushes a new level holding the
datum (`DcAt.consLev`); `dc_register_pop (r, &result)` at `0x80003670` pops
the top level (`DcAt.unconsLev`): its datum goes to the slot, its array is
freed by `dc_array_free_spec`, its node by `free`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- Register `r`'s word set to the link of its top node `c`. -/
abbrev popRegW (M : Mem) (r : Nat) (c : Blk) : Mem :=
  writeLog M [(regAddr r, 8, ldv .ld M (c.pay + 24))]

/-- **The top level of register `r` popped**: register `r`'s word holds the
next level; the level's node `c` and array nodes leave the state, their data
handles to the caller. -/
structure LevPopped (S : Nat → Prop) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G : DcG) (hs : List GV) (st : St) (r : Nat) (c : Blk) (e : RLev)
    (l : List (Blk × RLev)) (ent : Entry) (es : List Entry) : Prop where
  regs : st.regs r = ent :: es
  den : e.Den ⟨L, G.strs⟩ ent
  dc : DcAt S (popRegW M r c) H F L C (G.setReg r l)
    (e.arr.map (·.2.v) ++ (e.v.toList ++ hs)) (st.setReg r es)
  fresh : DcFresh H F L (G.setReg r l) c
  node : RLevAt M c e
  arr : AfNodes (popRegW M r c) H F L (G.setReg r l)
    (ldv .ld M (c.pay + 16)) e.arr

theorem DcAt.unconsLev {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {r : Nat} {c : Blk} {e : RLev}
    {l : List (Blk × RLev)} (h : DcAt S M H F L C G hs st) (hr : r < 256) (hl : G.regs r = (c, e) :: l) :
    ∃ ent es, LevPopped S M H F L C G hs st r c e l ent es := by
  have hi := h.heap.heap
  have hm : MemOnly (RegWord r) (popRegW M r c) M := MemOnly.store M _ 8 _
  have hrw : ∀ a, RegWord r a → OutHeap a ∧ DcGlob a := fun a ha => by
    simp only [RegWord, regAddr, dc_addrs] at ha
    exact ⟨DcGlob.outHeap (by simp only [DcGlob, dc_addrs]; omega),
      by simp only [DcGlob, dc_addrs]; omega⟩
  have hblk : ∀ a, InBlocks G.blocks a → imgM (popRegW M r c) a = imgM M a := fun a ha => hm a fun hw => by
    have := (h.inBlocks_heap ha).1; have := (hrw a hw).1.1; contradiction
  -- the blocks
  have hperm : G.blocks.Perm ((c :: e.arr.map (·.1)) ++ (G.setReg r l).blocks) := by
    rw [List.perm_iff_count]
    intro y
    have := G.setReg_blocks_count hr l y
    rw [hl] at this
    simp only [List.flatMap_cons, RLev.blocks, List.count_append, List.count_cons] at this ⊢
    omega
  have hnd := hperm.nodup_iff.mp h.nodup
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hnd
  obtain ⟨hcn, harrnd, hG'nd, hdisj⟩ := hnd
  have hsub : ∀ b ∈ (G.setReg r l).blocks, b ∈ G.blocks := fun b hb =>
    hperm.mem_iff.mpr (List.mem_append_right _ hb)
  have hcG : c ∈ G.blocks := hperm.mem_iff.mpr List.mem_cons_self
  have harrG : ∀ bn ∈ e.arr, bn.1 ∈ G.blocks := fun bn hbn =>
    hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨bn, hbn, rfl⟩)))
  have hcG' : c ∉ (G.setReg r l).blocks := fun hm' => hcn (List.mem_append_right _ hm')
  have harrG' : ∀ bn ∈ e.arr, bn.1 ∉ (G.setReg r l).blocks := fun bn hbn hm' =>
    hdisj _ (List.mem_map.mpr ⟨bn, hbn, rfl⟩) _ hm' rfl
  -- the values
  have hcount : ∀ y, ((G.setReg r l).vals ++ (e.arr.map (·.2.v) ++ (e.v.toList ++ hs))).count y =
      (G.vals ++ hs).count y := fun y => by
    have := G.setReg_vals_count hr l y
    rw [hl] at this
    simp only [List.flatMap_cons, RLev.vals, List.count_append] at this ⊢
    omega
  -- the chains
  have hv0 := h.view.regs r hr
  rw [hl] at hv0
  have hd := h.den
  have hd0 := hd.regs r hr
  rw [hl] at hd0
  generalize hse : st.regs r = sr at hd0
  cases hv0 with
  | cons h0 hn hlink =>
  cases hd0 with
  | cons hde hdes =>
  rename_i ent es
  refine ⟨ent, es, ⟨hse, hde, ?_, ⟨h.heap.raw.live c hcG, hcG', h.heap.raw.out c hcG⟩, hn, ?_⟩⟩
  · have hcin : ∀ x, c.In x → ¬ RegWord r x := fun x hx hw =>
      (hrw x hw).1.1 (live_in_heap hi (h.heap.raw.live c hcG) hx)
    have hsz := hn.sz
    have hl24 : ldv .ld (popRegW M r c) (c.pay + 24) = ldv .ld M (c.pay + 24) :=
      ldv_congr .ld fun j hj => hm _ (hcin _ (by simp only [Blk.In, Blk.pay, Blk.fin, widthOfM] at hj ⊢; omega))
    have hregs : ∀ r', r' < 256 → LChain (popRegW M r c) 24 (RLevAt (popRegW M r c)) (regAddr r') ((G.setReg r l).regs r') := by
      intro r' hr'
      have e1 : (G.setReg r l).regs r' = if r' = r then l else G.regs r' := rfl
      rw [e1]
      split
      · subst_vars
        refine (regChain_frame hlink hl24 fun be hbe c' hc' x hx => hblk x ⟨c', ?_, hx⟩).reword ?_
        · exact G.lev_mem hr (by rw [hl]; exact List.mem_cons_of_mem _ hbe) hc'
        · rw [ldv_store_hit, hl24]
      · rename_i hne
        exact regChain_frame (h.view.regs r' hr') (ldv_congr .ld fun j hj => hm _ fun hw => by
          simp only [RegWord, regAddr, widthOfM] at hw hj; omega)
          fun be hmm c' hc' x hx => hblk x ⟨c', G.lev_mem hr' hmm hc', hx⟩
    refine
      { heap := (h.heap.out_frame hm fun a ha => (hrw a ha).1).subRaw hsub
          fun b hb a ha => (hblk a ⟨b, hsub b hb, ha⟩).symm
        nodup := hG'nd
        view := h.view.withChains rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
          (fun o ho x hx => hx.elim (fun hx => hblk x ⟨_, (G.str_mem ho).1, hx⟩)
            fun hx => hblk x ⟨_, (G.str_mem ho).2, hx⟩)
          (fun a ha hc => hm a fun hw => hc (.inr (by simp only [RegWord, regAddr] at hw; omega)))
          (stkChain_frame h.view.stk (ldv_congr .ld fun j hj => hm _ fun hw => by
            simp only [RegWord, regAddr, dc_addrs, widthOfM] at hw hj; omega)
            fun bg hmm x hx => hblk x ⟨_, G.stk_mem hmm, hx⟩) hregs
        den := ?_
        glob := h.glob
        col := h.col }
    refine { hd with
      regs := fun r' hr' => ?_
      regsHi := fun r' hr' => ?_
      hsDen := fun g hg => ?_
      numRefs := fun x hx => by rw [hcount]; exact hd.numRefs x hx
      strRefs := fun o ho => by rw [hcount]; exact hd.strRefs o ho }
    · simp only [DcG.setReg, St.setReg]
      split
      · subst_vars; exact hdes
      · exact hd.regs r' hr'
    · have hne : r' ≠ r := by omega
      simp only [DcG.setReg, St.setReg, hne, ite_false]; exact hd.regsHi r' hr'
    · rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hg
        obtain ⟨iv, hiv⟩ := forall₂_left hde.arr bn hbn
        exact ⟨_, hiv.2⟩
      · rcases List.mem_append.mp hg with hg | hg
        · have hv := hde.val
          cases hev : e.v with
          | none => rw [hev] at hg; cases hg
          | some g0 =>
            rw [hev, Option.toList_some, List.mem_singleton] at hg
            subst hg
            rw [hev] at hv
            generalize ent.val = b at hv
            cases hv with
            | some hr' => exact ⟨_, hr'⟩
        · exact hd.hsDen g hg
  · refine ⟨(hn.arr.toP).frameA fun bn hbn a ha => hblk a ⟨_, harrG bn hbn, ha⟩, fun bn hbn =>
      ⟨h.heap.raw.live _ (harrG bn hbn), harrG' bn hbn, h.heap.raw.out _ (harrG bn hbn)⟩, harrnd⟩

end Dc.Mach
