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
  cArr : c ∉ e.arr.map (·.1)

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
  refine ⟨ent, es, ⟨hse, hde, ?_, ⟨h.heap.raw.live c hcG, hcG', h.heap.raw.out c hcG⟩, hn, ?_, ?_⟩⟩
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
  · exact fun hm' => hcn (List.mem_append_left _ hm')

/-- `"%s: stack register "` at `0x80007df8`. -/
theorem regEmptyMsg : ProgMsg 0x80007df8 17 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

/-- `" is empty\n"` at `0x80007e10`. -/
theorem regIsEmptyMsg : RtMsg 0x80007e10 10 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide⟩

/-- `dc_register_pop` on an empty register or a level without value
(`0x8000371c`, `sp` lowered by 32, `a5` the register): the two messages to
`stderr`, status `2`. -/
theorem rpop_err {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp r : Nat} (hr : r < 256)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h15 : R 15 = BitVec.ofNat 64 r)
    {ra s0 : BitVec 64} (hra : ldv .ld M (sp - 32 + 24) = ra) (hs0 : ldv .ld M (sp - 32 + 16) = s0)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M', Keeps (1 :: 2 :: 8 :: fprintfClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 10 = 2#64 → (∀ a, (a < sp - 336 ∨ sp ≤ a) → imgM M' a = imgM M a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x8000371c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hpn := h.view.prog
  have hG := h.glob
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  refine st_8000371c hlive ?_
  refine stR_80003720 hlive ?_ ?_ ?_
  · bsimp []; decide
  · bsimp []; exact hro
  rw [ldvf_stderr (by bsimp []; decide)]
  refine st_80003724 hlive ?_
  refine st_80003728 hlive ?_ ?_ ?_
  · bsimp []; decide
  · bsimp []
    rw [show (2147497764#64 + BitVec.signExtend 64 (25#20 +++ 0#12) + 1596#64).toNat =
      0x8001cd60 by decide]
    intro b hb; have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs]; omega)
  bc_run hlive hS [h2, hpn, h15] at 0x80000774
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hwin : ∀ a, (a < sp - 336 ∨ sp ≤ a) → a < sp - 32 - 304 ∨ sp - 32 ≤ a :=
    fun a ha => by rw [Nat.sub_sub]; omega
  have hfd := h.errFile.transport (M' := writeLog M [(sp - 32, 8, BitVec.ofNat 64 r)]) fun j hj => by
    simp only [stderrAddr] at *
    rw [imgM_store_miss _ _ (by omega)]
  refine fprintf_prog_spec hlive regEmptyMsg (by decide) (hsf.sub (m := 32) (n := 304) (by decide))
    (by simp only [stderrAddr]; omega) hfd _ (by bsimp [h2]) (by bsimp [stderrAddr]) (by bsimp [])
    (by bsimp []) (by bsimp []) fun R1 M1 hk1 hfr1 => ?_
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  have q8 : R1 8 = BitVec.ofNat 64 stderrAddr := by rw [hk1.get 8]; bsimp []
  have hl0 : ldv .ld M1 (sp - 32) = BitVec.ofNat 64 r := by
    rw [ldv_congr .ld fun j hj => hfr1 _ (.inr (by simp only [widthOfM] at hj; omega))]
    exact ldv_store_hit _ _ _
  bsimp []
  bc_run hlive hS [q2, q8, hl0] at 0x80001ec0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hfd1 := hfd.transport (M' := M1) fun j hj => hfr1 _ (.inl (by simp only [stderrAddr]; omega))
  refine dc_show_id_spec hlive (sp := sp - 32) (f := stderrAddr) (fd := 2) (id := r) (m := 0x80007e10)
    (hsf.sub (m := 32) (n := 304) (by decide)) hfd1 (.inl (by simp only [stderrAddr]; omega))
    regIsEmptyMsg.roStr (by rw [msgBytes_length]; decide) _ (by bsimp [stderrAddr]) (by bsimp [])
    (by omega) (by bsimp []) (by bsimp [q2]) (by bsimp []) fun R2 M2 hk2 hfr2 => ?_
  rw [fdOut_ne (by decide), String.append_empty]
  have q3 : R2 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk2.get 2]; bsimp [q2]
  have hld : ∀ o, 8 ≤ o → o + 8 ≤ 32 → ldv .ld M2 (sp - 32 + o) = ldv .ld M (sp - 32 + o) := fun o h1 h2 => by
    rw [ldv_congr .ld fun j hj => (hfr2 _ (.inr (by simp only [widthOfM] at hj; omega))).trans
      (hfr1 _ (.inr (by simp only [widthOfM] at hj; omega)))]
    rw [ldv_ld_miss _ _ (by omega)]
  have hra2 := (hld 24 (by omega) (by omega)).trans hra
  have hs02 := (hld 16 (by omega) (by omega)).trans hs0
  bsimp []
  bc_run hlive hS [q3, hra2, hs02]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hal
  refine hk _ M2 (by keeps_tac (((hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)).trans
      ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))
    (by bsimp []) (by rw [upd_same]; congr 1; omega) (by bsimp []) (by bsimp []) fun a ha => ?_
  rw [hfr2 a (hwin a ha), hfr1 a (hwin a ha), imgM_store_miss _ _ (by omega)]

/-- `dc_register_pop` on a level with a value (`0x800036b0`, `sp` lowered by
32, `s0` the top node `c`, `a6` the slot `q`): the datum to `q`, register `r`
to the next level, the level's array and node freed. -/
theorem rpop_some {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp q r : Nat} (hr : r < 256) {c : Blk} {e : RLev}
    {l : List (Blk × RLev)} {g : GV} (hl : G.regs r = (c, e) :: l) (hev : e.v = some g)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h8 : R 8 = BitVec.ofNat 64 c.pay)
    (h16 : R 16 = BitVec.ofNat 64 q) (hra4 : R 14 + R 12 = BitVec.ofNat 64 (regAddr r))
    {ra s0 : BitVec 64} (hra : ldv .ld M (sp - 32 + 24) = ra) (hs0 : ldv .ld M (sp - 32 + 16) = s0)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G' ent es v, st.regs r = ent :: es → ent.val = some v →
      Keeps (1 :: 2 :: 8 :: popClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 10 = 0#64 → DcAt S M' H' F' L' C' G' (g :: hs) (st.setReg r es) →
      g.Den ⟨L', G'.strs⟩ v → HsKeep ⟨L, G.strs⟩ ⟨L', G'.strs⟩ hs → StrPin G.strs G'.strs (g :: hs) →
      DatAt M' q g →
      PopOut sp q M' M → DWO live S Q t ra R' M') :
    DWO live S Q t 0x800036b0#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hq1 := hq.lo; have hq2 := hq.hi; have hq3 := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := h.heap.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hG := h.glob
  have hcG : c ∈ G.blocks := G.reg_mem hr (by rw [hl]; exact List.mem_cons_self)
  have hbb := blk_bounds hi (h.heap.raw.live c hcG)
  simp only [heapStart, heapEnd] at hbb
  have hn := (h.view.regs r hr)
  rw [hl] at hn
  have hnode : RLevAt M c e := by cases hn with | cons _ hn _ => exact hn
  have hsz := hnode.sz
  have hdat : DatAt M c.pay g := by have := hnode.dat; rw [hev] at this; exact this
  have hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs, regAddr] at this ⊢; omega)
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  have hrA : 2147601872 ≤ regAddr r ∧ regAddr r + 8 ≤ 2147603920 := by
    simp only [regAddr, dcRegAddr]; omega
  bc_run hlive hS [h2, h8, h16, hra4, hra8] at 0x80003e20
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [StOK, regAddr, dcRegAddr]; omega) | skip
  all_goals first
    | (intro b hb; have := of_mem_accAddrs hb; have := hq.own (b - q) (by omega)
       rwa [Nat.add_sub_cancel' (by omega)] at this)
    | skip
  have hl8 : ldv .ld (writeLog M [(q, 8, ldv .ld M c.pay)]) (c.pay + 8) = ldv .ld M (c.pay + 8) :=
    ldv_ld_miss _ _ (by omega)
  rw [hl8]
  have hqo : ∀ a, (q ≤ a ∧ a < q + 16) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have hMq : MemOnly (fun a => q ≤ a ∧ a < q + 16)
      (writeLog (writeLog M [(q, 8, ldv .ld M c.pay)]) [(q + 8, 8, ldv .ld M (c.pay + 8))]) M :=
    fun a ha => by rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  obtain ⟨ent, es, hp⟩ := (h.outWrite hMq hqo).unconsLev hr hl
  have e24 : ldv .ld (writeLog (writeLog M [(q, 8, ldv .ld M c.pay)]) [(q + 8, 8, ldv .ld M (c.pay + 8))])
      (c.pay + 24) = ldv .ld M (c.pay + 24) := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
  have e16 : ldv .ld (writeLog (writeLog M [(q, 8, ldv .ld M c.pay)]) [(q + 8, 8, ldv .ld M (c.pay + 8))])
      (c.pay + 16) = ldv .ld M (c.pay + 16) := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
  have hdc := hp.dc
  have harr := hp.arr
  simp only [popRegW, e24] at hdc harr
  rw [e16] at harr
  have hval := hp.den.val
  rw [hev] at hval
  obtain ⟨v, hv0, hgv⟩ : ∃ v, ent.val = some v ∧ g.Den ⟨L, G.strs⟩ v := by
    revert hval; generalize ent.val = w; intro hval; cases hval with | some h => exact ⟨_, rfl, h⟩
  refine dc_array_free_spec hlive hdc harr
    (StackFrame.sub (m := 32) (n := 80) (hsf.shrink (m := 112) (by omega)) (by decide))
    (by simp only [heapEnd]; omega) _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    fun R1 M1 H1 F1 L1 C1 G1 hk1 hpost hdc1 hkeep hpin => ?_
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  have q8 : R1 8 = BitVec.ofNat 64 c.pay := by rw [hk1.get 8]; bsimp [h8]
  bsimp []
  bc_run hlive hS [q2, q8] at 0x80000a0c
  obtain ⟨hcf1, -⟩ := hpost.fresh c hp.fresh hp.cArr
  refine af_freeNode hlive hdc1 hcf1 (p := 0#64) (rest := [])
    ⟨.nil, (fun _ hm => nomatch hm), List.nodup_nil⟩ (fun hm => nomatch hm) _ (by bsimp [q8])
    (by bsimp [] <;> decide) fun R2 M2 H2 hk2 hdc2 _ hpost2 => ?_
  have hfrq : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn (sp - 32) 80 a → imgM M2 a =
      imgM (writeLog (writeLog (writeLog M [(q, 8, ldv .ld M c.pay)]) [(q + 8, 8, ldv .ld M (c.pay + 8))])
        [(regAddr r, 8, ldv .ld M (c.pay + 24))]) a := fun a ho hg hf =>
    (hpost2.out a ho hg fun h' => by simp only [frameIn] at h'; omega).trans (hpost.out a ho hg hf)
  have hfr : ∀ a, sp - 32 ≤ a → a < sp → imgM M2 a = imgM M a := fun a h1 h2 => by
    rw [hfrq a (outHeap_of_ge (by simp only [heapEnd]; omega))
      (fun hg => by have := hg.lt; simp only [heapStart] at this; omega)
      (by simp only [frameIn]; omega),
      imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hra2 : ldv .ld M2 (sp - 32 + 24) = ra := by
    rw [ldv_congr .ld fun j hj => hfr _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)]; exact hra
  have hs02 : ldv .ld M2 (sp - 32 + 16) = s0 := by
    rw [ldv_congr .ld fun j hj => hfr _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)]; exact hs0
  have q2' : R2 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk2.get 2]; bsimp [q2]
  bsimp []
  bc_run hlive hS [q2', hra2, hs02]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first | exact hal | skip
  have hqm : ∀ k, k + 8 ≤ 16 → ldv .ld M2 (q + k) = ldv .ld
      (writeLog (writeLog M [(q, 8, ldv .ld M c.pay)]) [(q + 8, 8, ldv .ld M (c.pay + 8))]) (q + k) :=
    fun k hk => by
      rw [ldv_congr .ld fun j hj => (hfrq _ (hqo _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩).1
        (hqo _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩).2
        (by simp only [frameIn, widthOfM] at hj ⊢; omega))]
      rw [ldv_ld_miss _ _ (by omega)]
  have hdq : DatAt M2 q g := by
    refine ⟨?_, ?_⟩
    · have e := hqm 0 (by omega)
      simp only [Nat.add_zero] at e
      rw [e, ldv_ld_miss _ _ (by omega), ldv_store_hit]; exact hdat.tag
    · rw [hqm 8 (by omega), ldv_store_hit]; exact hdat.ptr
  rw [hev] at hdc2 hkeep hpin
  refine hk _ M2 H2 F1 L1 C1 G1 ent es v hp.regs hv0
    (by keeps_tac (((hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)).trans
      ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))
    (by bsimp []) (by bsimp []; congr 1; omega) (by bsimp []) (by bsimp []) hdc2
    (hkeep g List.mem_cons_self v hgv) (hkeep.mono fun x hx => List.mem_cons_of_mem _ hx) hpin hdq
    fun a ho hg hf hqa => ?_
  rw [hfrq a ho hg fun h' => hf (by simp only [frameIn] at h' ⊢; omega)]
  simp only [DcGlob, dc_addrs, not_or] at hg
  rw [imgM_store_miss _ _ (by simp only [regAddr] at *; omega), imgM_store_miss _ _ (by omega),
    imgM_store_miss _ _ (by omega)]

/-- `dc_register_pop` on a top node `c` (`0x80003698`, `sp` lowered by 32):
the value's type selects the error exit or `rpop_some`. -/
theorem rpop_lev {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp q r : Nat} (hr : r < 256) {c : Blk} {e : RLev}
    {l : List (Blk × RLev)} (hl : G.regs r = (c, e) :: l)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h8 : R 8 = BitVec.ofNat 64 c.pay)
    (h11 : R 11 = BitVec.ofNat 64 q) (h15 : R 15 = BitVec.ofNat 64 r)
    (hra4 : R 14 + R 12 = BitVec.ofNat 64 (regAddr r))
    {ra s0 : BitVec 64} (hra : ldv .ld M (sp - 32 + 24) = ra) (hs0 : ldv .ld M (sp - 32 + 16) = s0)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ g, e.v = some g → ∀ R' M' H' F' L' C' G' ent es v, st.regs r = ent :: es →
      ent.val = some v → Keeps (1 :: 2 :: 8 :: popClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = s0 → R' 10 = 0#64 →
      DcAt S M' H' F' L' C' G' (g :: hs) (st.setReg r es) →
      g.Den ⟨L', G'.strs⟩ v → HsKeep ⟨L, G.strs⟩ ⟨L', G'.strs⟩ hs → StrPin G.strs G'.strs (g :: hs) →
      DatAt M' q g →
      PopOut sp q M' M → DWO live S Q t ra R' M')
    (herr : e.v = none → ∀ R' M', Keeps (1 :: 2 :: 8 :: fprintfClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = s0 → R' 10 = 2#64 →
      (∀ a, (a < sp - 336 ∨ sp ≤ a) → imgM M' a = imgM M a) → DWO live S Q t ra R' M') :
    DWO live S Q t 0x80003698#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := h.heap.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hcG : c ∈ G.blocks := G.reg_mem hr (by rw [hl]; exact List.mem_cons_self)
  have hbb := blk_bounds hi (h.heap.raw.live c hcG)
  simp only [heapStart, heapEnd] at hbb
  have hn := h.view.regs r hr
  rw [hl] at hn
  have hnode : RLevAt M c e := by cases hn with | cons _ hn _ => exact hn
  have hsz := hnode.sz
  have hdat := hnode.dat
  revert hdat
  cases hev : e.v with
  | none =>
    intro hdat
    bc_run hlive hS [h8, hdat] at 0x8000371c
    refine rpop_err hlive h hr hsf (by simp only [heapEnd]; omega) _ ?_ ?_ hra hs0 hal
      fun R' M' hk1 e1 e2 e8 e10 hfr => ?_
    · bsimp [h2]
    · bsimp [h15]
    exact herr hev R' M' ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) e1 e2 e8 e10 hfr
  | some g =>
    intro hdat
    have htag := hdat.lw
    obtain ⟨htg1, htg2⟩ := g.tag_pos
    have wp : BitVec.ofNat 64 g.tag + 18446744073709551615#64 = BitVec.ofNat 64 (g.tag - 1) :=
      word_pred htg1
    have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (g.tag - 1))) =
        BitVec.ofNat 64 (g.tag - 1) := sxw_ofNat (by omega)
    have hne : BitVec.ofNat 64 g.tag ≠ 0#64 := by cases g <;> simp only [GV.tag] <;> decide
    bc_run hlive hS [h8, htag, wp, wq] at 0x800036ac
    all_goals try (intro hc; exact absurd hc hne)
    intro _
    bsimp []
    bc_run hlive hS [h8, htag, wp, wq] at 0x800036ac
    refine st_800036ac hlive (fun hc => absurd hc ?_) fun _ => ?_
    · bsimp []; omega
    refine rpop_some hlive h hr hl hev hsf (by simp only [heapEnd]; omega) hq _ ?_ ?_ ?_ ?_ hra hs0 hal
      fun R' M' H' F' L' C' G' ent es v he hv hk1 e1 e2 e8 e10 hdc hgd hkeep hpin hdq hfr => ?_
    · bsimp [h2]
    · bsimp [h8]
    · bsimp [h11]
    · bsimp [hra4]
    exact hk g hev R' M' H' F' L' C' G' ent es v he hv
      ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) e1 e2 e8 e10 hdc hgd hkeep hpin hdq hfr

/-- The memory of `dc_register_pop`'s frame after the prologue's stores. -/
abbrev rpopProW (M : Mem) (sp : Nat) (R : Nat → BitVec 64) : Mem :=
  writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]

theorem rpop_rl {M : Mem} {sp r : Nat} {w : BitVec 64}
    (hrA : 2147601872 ≤ regAddr r ∧ regAddr r + 8 ≤ 2147603920) (hab : 2273312768 ≤ sp) :
    ldv .ld (writeLog M [(sp - 32 + 16, 8, w)]) (regAddr r) = ldv .ld M (regAddr r) :=
  ldv_ld_miss _ _ (by omega)

/-- `dc_register_pop`'s prologue (`0x80003670`): the frame stored, register
`r`'s word loaded, the branch on it. -/
theorem rpop_pro {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) (hG : ∀ a, DcGlob a → S a)
    {M : Mem} {sp q r : Nat} (hr : r < 256) (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 r) (h11 : R 11 = BitVec.ofNat 64 q)
    (h2 : R 2 = BitVec.ofNat 64 sp)
    (hz : ldv .ld M (regAddr r) = 0#64 → ∀ R0 : Nat → BitVec 64, R0 2 = BitVec.ofNat 64 (sp - 32) →
      R0 15 = BitVec.ofNat 64 r → Keeps (2 :: 8 :: popClob) R0 R →
      DWO live S Q t 0x8000371c#64 R0 (rpopProW M sp R))
    (hnz : ldv .ld M (regAddr r) ≠ 0#64 → ∀ R0 : Nat → BitVec 64, R0 2 = BitVec.ofNat 64 (sp - 32) →
      R0 8 = ldv .ld M (regAddr r) → R0 11 = BitVec.ofNat 64 q → R0 15 = BitVec.ofNat 64 r →
      R0 14 + R0 12 = BitVec.ofNat 64 (regAddr r) → Keeps (2 :: 8 :: popClob) R0 R →
      DWO live S Q t 0x80003698#64 R0 (rpopProW M sp R)) :
    DWO live S Q t 0x80003670#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  have hrA : 2147601872 ≤ regAddr r ∧ regAddr r + 8 ≤ 2147603920 := by
    simp only [regAddr, dcRegAddr]; omega
  have hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs, regAddr] at this ⊢; omega)
  bc_run hlive hS [h2, h10, regWord_addr hr, hra8] at 0x8000371c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [LdOK, regAddr, dcRegAddr]; omega) | skip
  · intro hc
    refine hz ((rpop_rl hrA (by omega)).symm.trans hc) _ ?_ ?_ (by keeps_tac Keeps.refl _ _)
    · bsimp [h2]
    · bsimp [and255_small hr]
  · intro hc
    refine hnz (fun e => hc ((rpop_rl hrA (by omega)).trans e)) _ ?_ ?_ ?_ ?_ ?_ (by keeps_tac Keeps.refl _ _)
    · bsimp [h2]
    · bsimp []; exact rpop_rl hrA (by omega)
    · bsimp [h11]
    · bsimp [and255_small hr]
    · bsimp [h10]; exact regWord_addr hr

/-- **`dc_register_pop(regid, result)`** at `0x80003670`, `r = regid`: the
top level's value moves to the slot `q` (`0` returned), its array and node
freed; on an empty register or a level without value, the message to
`stderr` and `2`. -/
theorem dc_register_pop_spec {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp q r : Nat} (hr : r < 256)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 r) (h11 : R 11 = BitVec.ofNat 64 q)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G' g ent es v, st.regs r = ent :: es → ent.val = some v →
      Keeps popClob R' R → R' 10 = 0#64 → DcAt S M' H' F' L' C' G' (g :: hs) (st.setReg r es) →
      g.Den ⟨L', G'.strs⟩ v → HsKeep ⟨L, G.strs⟩ ⟨L', G'.strs⟩ hs → StrPin G.strs G'.strs (g :: hs) →
      DatAt M' q g →
      PopOut sp q M' M → DWO live S Q t (R 1) R' M')
    (hkn : (∀ ent es, st.regs r = ent :: es → ent.val = none) → ∀ R' M', Keeps popClob R' R →
      R' 10 = 2#64 → DcAt S M' H F L C G hs st → PopOut sp q M' M → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80003670#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi
  simp only [heapEnd] at hab
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hP : ∀ a, frameIn sp 336 a → OutHeap a ∧ ¬ DcGlob a := fun a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have hM1 : MemOnly (frameIn sp 336) (rpopProW M sp R) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hM1 hP
  have hra1 : ldv .ld (rpopProW M sp R) (sp - 32 + 24) = R 1 := ldv_store_hit _ _ _
  have hs01 : ldv .ld (rpopProW M sp R) (sp - 32 + 16) = R 8 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have hout : ∀ M', PopOut sp q M' (rpopProW M sp R) → PopOut sp q M' M :=
    fun M' hm a ho hg hf hqa => (hm a ho hg hf hqa).trans (hM1 a hf)
  -- the error exit's continuation
  have herr : (∀ ent es, st.regs r = ent :: es → ent.val = none) →
      ∀ R0 : Nat → BitVec 64, Keeps (2 :: 8 :: popClob) R0 R →
      ∀ R' M', Keeps (1 :: 2 :: 8 :: fprintfClob) R' R0 → R' 1 = R 1 →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = R 8 → R' 10 = 2#64 →
      (∀ a, (a < sp - 336 ∨ sp ≤ a) → imgM M' a = imgM (rpopProW M sp R) a) →
      DWO live S Q t (R 1) R' M' :=
    fun hn R0 hk0 R' M' hk1 e1 e2 e8 e10 hfr => by
      have hfr' : MemOnly (frameIn sp 336) M' (rpopProW M sp R) :=
        fun x hx => hfr x (by simp only [frameIn] at hx; omega)
      exact hkn hn R' M' (hk1.restore3 hk0 e1 (by rw [e2, h2]) e8) e10 (h1.outWrite hfr' hP)
        (hout M' fun x _ _ hf _ => hfr' x hf)
  have hv := h.view.regs r hr
  have hd := h.den.regs r hr
  generalize hl : G.regs r = l at hv hd
  refine rpop_pro hlive hS h.glob hr hsf (by simp only [heapEnd]; omega) R h10 h11 h2
    (fun hz R0 e2 e15 hk0 => rpop_err hlive h1 hr hsf (by simp only [heapEnd]; omega) R0 e2 e15
      hra1 hs01 hal (herr ?_ R0 hk0))
    fun hnz R0 e2 e8 e11 e15 e14 hk0 => ?_
  · intro ent es he
    cases hv with
    | nil => revert hd; rw [he]; intro hd; cases hd
    | cons h0 => exact absurd hz (by rw [h0]; exact blk_ptr_ne h.heap.heap (h.heap.raw.live _
        (G.reg_mem hr (by rw [hl]; exact List.mem_cons_self))))
  cases hv with
  | nil h0 => exact absurd h0 hnz
  | @cons _ b e l' h0 hb hl' =>
    obtain ⟨v0, rest, hst, hde⟩ : ∃ v0 rest, st.regs r = v0 :: rest ∧ e.Den ⟨L, G.strs⟩ v0 := by
      revert hd; generalize st.regs r = m; intro hd; cases hd with | cons h _ => exact ⟨_, _, rfl, h⟩
    rw [h0] at e8
    refine rpop_lev hlive h1 hr hl hsf (by simp only [heapEnd]; omega) hq R0 e2 e8 e11 e15 e14
      hra1 hs01 hal
      (fun g hev R' M' H' F' L' C' G' ent es v he hv hk1 e1 e2 e8 e10 hdc hgd hkeep hpin hdq hfr =>
        hk R' M' H' F' L' C' G' g ent es v he hv
          (hk1.restore3 hk0 e1 (by rw [e2, h2]) e8) e10 hdc hgd hkeep hpin hdq (hout M' hfr))
      (fun hev => herr (fun ent es he => ?_) R0 hk0)
    rw [hst] at he; cases he
    have hval := hde.val; rw [hev] at hval
    revert hval; generalize v0.val = w; intro hval; cases hval; rfl

/-- `dc_register_push`'s node stores and return (`0x80002e70`, `sp` lowered
by 32, `a0` the node at `p`, `a2`/`a3` the datum words, `a4` the old top,
`a5` the register's word at `w`). -/
theorem rpush_stores {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp p w : Nat}
    (hsf : StackFrame S sp 48) (hp : p + 32 ≤ 2273312768 ∧ 2147603936 ≤ p ∧ p % 16 = 0)
    (hw : ∀ b ∈ accAddrs w 8, S b) (hwa : w % 8 = 0 ∧ 2147601872 ≤ w ∧ w + 8 ≤ 2147603920)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h10 : R 10 = BitVec.ofNat 64 p)
    (h15 : R 15 = BitVec.ofNat 64 w) {x0 x1 x2 : BitVec 64} (h12 : R 12 = x0) (h13 : R 13 = x1)
    (h14 : R 14 = x2) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [2] R' R → R' 2 = BitVec.ofNat 64 sp →
      DW live S Q (R 1) R' (writeLog (writeLog (writeLog (writeLog (writeLog M
        [(p + 16, 8, 0#64)]) [(p, 8, x0)]) [(p + 8, 8, x1)]) [(p + 24, 8, x2)])
        [(w, 8, BitVec.ofNat 64 p)])) :
    DW live S Q 0x80002e70#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hpw : (BitVec.ofNat 64 p).toNat = p := by simp only [BitVec.toNat_ofNat]; omega
  have hww : (BitVec.ofNat 64 w).toNat = w := by simp only [BitVec.toNat_ofNat]; omega
  have hpS : ∀ k, k + 8 ≤ 32 → ∀ b ∈ accAddrs (p + k) 8, S b := fun k hk b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  bc_run hlive hS [h2, h10, h15, h12, h13, h14, hpw, hww]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hw | exact hpS 0 (by omega) | exact hpS 8 (by omega) | exact hpS 16 (by omega) | exact hpS 24 (by omega) | (simp only [StOK, htx]; omega) | skip
  all_goals first | exact hal | skip
  refine hk _ ?_ ?_
  · keeps_tac Keeps.refl _ _
  · rw [upd_same]; congr 1; omega

/-- `dc_register_push` after `dc_malloc` (`0x80002e44`, `sp` lowered by 32,
`a0` the fresh node `c`): the node's datum, empty array and link stored,
register `r` set to it, the frame restored. -/
theorem rpush_tail {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {v : Val}
    {w0 w1 : BitVec 64} (h : DcAt S M H F L C G (g :: hs) st) {sp r : Nat} (hr : r < 256)
    {c : Blk} (hf : DcFresh H F L G c) (hcsz : 32 ≤ c.sz)
    (hd : DatRegs w0 w1 g) (hv : g.Den ⟨L, G.strs⟩ v)
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h8 : R 8 = BitVec.ofNat 64 r)
    (h10 : R 10 = BitVec.ofNat 64 c.pay) {s0 ra : BitVec 64}
    (l0 : ldv .ld M (sp - 32) = w0) (l8 : ldv .ld M (sp - 32 + 8) = w1)
    (l16 : ldv .ld M (sp - 32 + 16) = s0) (l24 : ldv .ld M (sp - 32 + 24) = ra)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M', Keeps (1 :: 2 :: 8 :: mallocClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = s0 →
      DcAt S M' H F L C (G.setReg r ((c, ⟨some g, []⟩) :: G.regs r)) hs
        (st.setReg r (⟨some v, []⟩ :: st.regs r)) →
      (∀ a, OutHeap a → ¬ DcGlob a → imgM M' a = imgM M a) → DW live S Q ra R' M') :
    DW live S Q 0x80002e44#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := h.heap.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hG := h.glob
  simp only [heapEnd] at hab
  have hcb := blk_bounds hi hf.live
  simp only [heapStart, heapEnd] at hcb
  obtain ⟨hc1, hc2, hc3⟩ := hcb
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  have hrA : 2147601872 ≤ regAddr r ∧ regAddr r + 8 ≤ 2147603920 := by
    simp only [regAddr, dcRegAddr]; omega
  have hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs, regAddr] at this ⊢; omega)
  bc_run hlive hS [h2, h8, h10, regWord_addr hr, hra8] at 0x80002e68
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [LdOK, StOK, regAddr, dcRegAddr]; omega) | skip
  have lst : ∀ a, a + 8 ≤ c.pay + 24 ∨ c.pay + 32 ≤ a →
      ldv .ld (writeLog M [(c.pay + 24, 8, 0#64)]) a = ldv .ld M a := fun a ha => ldv_ld_miss _ _ ha
  have m0 := lst (sp - 32) (by omega)
  have m8 := lst (sp - 32 + 8) (by omega)
  have m16 := lst (sp - 32 + 16) (by omega)
  have m24 := lst (sp - 32 + 24) (by omega)
  have mr := lst (regAddr r) (by omega)
  rw [mr, m0, m8, l0, l8]
  bc_run hlive hS [h2] at 0x80002e70
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have k16 : ldv .ld (writeLog M [(c.pay + 24, 8, 0#64)]) (sp - 32 + 16) = s0 :=
    (ldv_ld_miss _ _ (by omega)).trans l16
  have k24 : ldv .ld (writeLog M [(c.pay + 24, 8, 0#64)]) (sp - 32 + 24) = ra :=
    (ldv_ld_miss _ _ (by omega)).trans l24
  rw [k16, k24]
  have hrw : regAddr r % 8 = 0 ∧ 2147601872 ≤ regAddr r ∧ regAddr r + 8 ≤ 2147603920 := by
    simp only [regAddr, dcRegAddr]; omega
  refine rpush_stores hlive hS hsf ⟨by omega, hc1, hc3⟩ hrown hrw (x0 := w0) (x1 := w1)
    (x2 := ldv .ld M (regAddr r)) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    fun R' hk2 e2 => ?_
  · bsimp [h2]
  · bsimp [h10]
  · bsimp []
  · bsimp []
  · bsimp []
  · bsimp []
  · bsimp []; exact hal
  have e1c : c.fin = c.pay + c.sz := rfl
  have hm : MemOnly (fun a => c.In a ∨ RegWord r a) (writeLog (writeLog (writeLog (writeLog
      (writeLog (writeLog M [(c.pay + 24, 8, 0#64)]) [(c.pay + 16, 8, 0#64)]) [(c.pay, 8, w0)])
      [(c.pay + 8, 8, w1)]) [(c.pay + 24, 8, ldv .ld M (regAddr r))])
      [(regAddr r, 8, BitVec.ofNat 64 c.pay)]) M := fun x hx => by
    simp only [Blk.In, RegWord, e1c, not_or] at hx
    repeat rw [imgM_store_miss _ _ (by omega)]
  have hn : RLevAt (writeLog (writeLog (writeLog (writeLog
      (writeLog (writeLog M [(c.pay + 24, 8, 0#64)]) [(c.pay + 16, 8, 0#64)]) [(c.pay, 8, w0)])
      [(c.pay + 8, 8, w1)]) [(c.pay + 24, 8, ldv .ld M (regAddr r))])
      [(regAddr r, 8, BitVec.ofNat 64 c.pay)]) c ⟨some g, []⟩ :=
    ⟨⟨by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
        ldv_store_hit]; exact hd.tag,
      by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]; exact hd.ptr⟩,
      .nil (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
        ldv_ld_miss _ _ (by omega), ldv_store_hit]), hcsz⟩
  have hdc := DcAt.consLev (ov := some g) (ovv := some v) h hr hf hm (ldv_store_hit _ _ _) hn
    (by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]) (.some hv)
  refine hk R' _ ?_ ?_ e2 ?_ hdc fun x ho hg => ?_
  · exact (hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  · rw [hk2.get 1]; bsimp []
  · rw [hk2.get 8]; bsimp []
  have hx := ho.1
  have hrx : x < regAddr r ∨ regAddr r + 8 ≤ x := Classical.byContradiction fun hc =>
    hg (by simp only [DcGlob, regAddr, dc_addrs] at hc ⊢; omega)
  simp only [heapStart, heapEnd] at hx
  rw [imgM_store_miss _ _ hrx]
  try (repeat rw [imgM_store_miss _ _ (by omega)])

/-- **`dc_register_push(regid, value)`** at `0x80002e24`, `r = regid`: a
fresh node holding the datum `g` (in `a1`/`a2`, the caller's handle) becomes
register `r`'s top level; `dc_malloc` may run out of memory. -/
theorem dc_register_push_spec {live S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {v : Val}
    {w0 w1 : BitVec 64} (h : DcAt S M H F L C G (g :: hs) st) {sp r : Nat} (hr : r < 256)
    (hd : DatRegs w0 w1 g) (hv : g.Den ⟨L, G.strs⟩ v)
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 r) (h11 : R 11 = w0) (h12 : R 12 = w1)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' c, Keeps mallocClob R' R →
      DcAt S M' H' F L C (G.setReg r ((c, ⟨some g, []⟩) :: G.regs r)) hs
        (st.setReg r (⟨some v, []⟩ :: st.regs r)) →
      StkOut sp 48 M' M → DW live S Q (R 1) R' M')
    (hoom : ∀ R' M', StkOut sp 48 M' M → DW live S Q 0x80001e74#64 R' M') :
    DW live S Q 0x80002e24#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  simp only [heapEnd, heapStart] at hab
  have hP : ∀ a, frameIn sp 48 a → OutHeap a ∧ ¬ DcGlob a := fun a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  bc_run hlive hS [h2, h10, h11, h12] at 0x80001ea0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM2 : MemOnly (frameIn sp 48) (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, w1)])
      [(sp - 32, 8, w0)]) M := fun x hx => by
    simp only [frameIn] at hx; repeat rw [imgM_store_miss _ _ (by omega)]
  have h2' := h.outWrite hM2 hP
  refine dc_malloc_spec hlive h2'.heap.heap (n := 32) (by decide)
    (StackFrame.sub (m := 32) (n := 16) hsf (by decide))
    (by simp only [heapEnd]; omega) _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    (fun R1 Mm H' c hk1 hp e10 => ?_) fun R1 Mm _ hfr => hoom R1 Mm fun x ho hg hf => ?_
  rotate_left
  · rw [hfr x (OutHeap.not_alloc h2'.heap.heap ho) (by simp only [frameIn] at hf ⊢; omega)]
    exact hM2 x fun h' => hf h'
  obtain ⟨h3, hf⟩ := h2'.malloc hp (by decide) (by simp only [heapEnd]; omega)
  have hfm : ∀ a, sp - 32 ≤ a → a < sp → imgM Mm a =
      imgM (writeLog (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
        [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, w1)]) [(sp - 32, 8, w0)]) a := fun a h1 h2 =>
    hp.frame _ (OutHeap.not_alloc h2'.heap.heap (outHeap_of_ge (by simp only [heapEnd]; omega)))
      (by simp only [frameIn]; omega)
  have l0 : ldv .ld Mm (sp - 32) = w0 := by
    rw [ldv_congr .ld fun j hj => hfm _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)]
    exact ldv_store_hit _ _ _
  have l8 : ldv .ld Mm (sp - 32 + 8) = w1 := by
    rw [ldv_congr .ld fun j hj => hfm _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)]
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have l16 : ldv .ld Mm (sp - 32 + 16) = R 8 := by
    rw [ldv_congr .ld fun j hj => hfm _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)]
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_store_hit]
  have l24 : ldv .ld Mm (sp - 32 + 24) = R 1 := by
    rw [ldv_congr .ld fun j hj => hfm _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)]
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  refine rpush_tail hlive h3 hr hf hp.size hd hv hsf (by simp only [heapEnd]; omega) R1
    (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h10]) e10 l0 l8 l16 l24 hal
    fun R' Mf hk2 e1 e2 e8 hdc hfr => hk R' Mf _ c ?_ hdc fun x ho hg hf' => ?_
  · exact Keeps.restore3 (R1 := R) (hk2.trans ((hk1.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))) (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2]) e8
  rw [hfr x ho hg, hp.frame x (OutHeap.not_alloc h2'.heap.heap ho)
    (by simp only [frameIn] at hf' ⊢; omega)]
  exact hM2 x hf'

end Dc.Mach
