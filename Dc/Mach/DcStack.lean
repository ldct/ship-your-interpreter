import Dc.Mach.StateOps

/-!
# `dc/stack.c`: the evaluation stack (M9)

- `DatRegs w0 w1 g`: a `dc_data` passed in two registers (the type in the low
  word of `w0`, the pointer in `w1`).
- `push_tail`, `push_post`: `dc_push`'s node stores and the state after them.
- `dc_push_spec`: `dc_push` moves the caller's handle onto the stack.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- A `dc_data` in two registers. -/
structure DatRegs (w0 w1 : BitVec 64) (g : GV) : Prop where
  tag : w0.toNat % 2 ^ 32 = g.tag
  ptr : w1 = BitVec.ofNat 64 g.ptr

theorem GV.tag_pos (g : GV) : 1 ≤ g.tag ∧ g.tag ≤ 2 := by cases g <;> simp [GV.tag]

/-- The registers `dc_push` may change. -/
abbrev pushClob : List Nat := [10, 11, 12, 13, 14, 15]

/-- Memory changed only in the heap, `dc_stack`, and the window below `sp`. -/
def StkOut (sp W : Nat) (M' M : Mem) : Prop :=
  ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp W a → imgM M' a = imgM M a

/-- The node stores of `dc_push` (`0x80002df4` to the `ret`): the saved
handle words `w0`/`w1` go to the node at `p`, its link to the old `dc_stack`,
and `dc_stack` to `p`. -/
theorem push_tail {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {Mt : Mem} {R : Nat → BitVec 64}
    {sp p : Nat} {w0 w1 ra : BitVec 64}
    (hsf : StackFrame S sp 64) (hab : heapEnd + 64 ≤ sp)
    (hp1 : 2147603936 ≤ p) (hp2 : p + 32 ≤ 2273312768) (hp3 : p % 16 = 0)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h15 : R 15 = BitVec.ofNat 64 p)
    (hl0 : ldv .ld Mt (sp - 48 + 16) = w0) (hl1 : ldv .ld Mt (sp - 48 + 24) = w1)
    (hl2 : ldv .ld Mt (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hg : ∀ b ∈ accAddrs dcStackAddr 8, S b)
    (hk : ∀ R', Keeps [1, 2, 12, 13, 14] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      DW live S Q ra R' (writeLog (writeLog (writeLog (writeLog Mt [(p, 8, w0)])
        [(p + 24, 8, ldv .ld Mt dcStackAddr)]) [(p + 8, 8, w1)]) [(dcStackAddr, 8, BitVec.ofNat 64 p)])) :
    DW live S Q 0x80002df4#64 R Mt := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h2, hl0, hl1, word_sub48] at 0x80002e00
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have ea : (2147601916#64 + sign_extend (m := 64) (0xf9c#12)).toNat = 2147601816 := by decide
  refine st_80002e00 hlive ?_ ?_ ?_
  · rw [upd_same, ea]; exact ldOK_dcStack
  · rw [upd_same, ea]; exact hg
  rw [upd_same, ea]
  bc_run hlive hS [h2, h15, hl2, word_sub48] at 0x80002e18
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have eb : (2147601940#64 + sign_extend (m := 64) (0xf84#12)).toNat = 2147601816 := by decide
  refine st_80002e18 hlive ?_ ?_ ?_
  · rw [upd_same, eb]; exact stOK_dcStack
  · rw [upd_same, eb]; exact hg
  rw [upd_same, eb]
  bc_run hlive hS [h2, h15, hl2, word_sub48] at 0x80002e20
  refine st_80002e20 hlive (by bsimp [hal]) ?_
  exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp [h2]; congr 1; omega)

/-- The memory `dc_push` leaves: three zero stores into the fresh node `b`,
the handle words, the link, then `dc_stack`. -/
abbrev pushMem (M : Mem) (p : Nat) (w0 w1 : BitVec 64) : Mem :=
  let M3 := writeLog (writeLog (writeLog M [(p, 4, 0#64)]) [(p + 16, 8, 0#64)]) [(p + 24, 8, 0#64)]
  writeLog (writeLog (writeLog (writeLog M3 [(p, 8, w0)]) [(p + 24, 8, ldv .ld M3 dcStackAddr)])
    [(p + 8, 8, w1)]) [(dcStackAddr, 8, BitVec.ofNat 64 p)]

/-- **The state after `dc_push`'s stores**: `b` is the new top node. -/
theorem push_post {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {v : Val} {b : Blk}
    {w0 w1 : BitVec 64}
    (h : DcAt S M H F L C G (g :: hs) st) (hf : DcFresh H F L G b) (hv : g.Den ⟨L, G.strs⟩ v)
    (hd : DatRegs w0 w1 g) (hsz : 32 ≤ b.sz) (hp1 : 2147603936 ≤ b.pay) :
    DcAt S (pushMem M b.pay w0 w1) H F L C { G with stk := (b, g) :: G.stk } hs (st.push v) ∧
      MemOnly (fun a => b.In a ∨ (dcStackAddr ≤ a ∧ a < dcStackAddr + 8)) (pushMem M b.pay w0 w1) M := by
  have e1 : b.fin = b.pay + b.sz := by simp only [Blk.fin, Blk.pay]
  have hds : dcStackAddr = 2147601816 := rfl
  obtain ⟨htg1, htg2⟩ := g.tag_pos
  have ht := hd.tag
  have hm5 : MemOnly b.In (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(b.pay, 4, 0#64)]) [(b.pay + 16, 8, 0#64)]) [(b.pay + 24, 8, 0#64)]) [(b.pay, 8, w0)])
      [(b.pay + 24, 8, ldv .ld (writeLog (writeLog (writeLog M [(b.pay, 4, 0#64)])
        [(b.pay + 16, 8, 0#64)]) [(b.pay + 24, 8, 0#64)]) dcStackAddr)]) [(b.pay + 8, 8, w1)]) M :=
    fun a ha => by
      simp only [Blk.In] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have h5 := h.rawWrite hf hm5
  have hn : SNodeAt (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(b.pay, 4, 0#64)]) [(b.pay + 16, 8, 0#64)]) [(b.pay + 24, 8, 0#64)]) [(b.pay, 8, w0)])
      [(b.pay + 24, 8, ldv .ld (writeLog (writeLog (writeLog M [(b.pay, 4, 0#64)])
        [(b.pay + 16, 8, 0#64)]) [(b.pay + 24, 8, 0#64)]) dcStackAddr)]) [(b.pay + 8, 8, w1)]) b g :=
    { dat := { tag := by
                rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]; exact ht
               ptr := by rw [ldv_store_hit, hd.ptr] }
      arr := by
        rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
          ldv_ld_miss _ _ (by omega), ldv_store_hit]
      sz := hsz }
  have hl : ldv .ld (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(b.pay, 4, 0#64)]) [(b.pay + 16, 8, 0#64)]) [(b.pay + 24, 8, 0#64)]) [(b.pay, 8, w0)])
      [(b.pay + 24, 8, ldv .ld (writeLog (writeLog (writeLog M [(b.pay, 4, 0#64)])
        [(b.pay + 16, 8, 0#64)]) [(b.pay + 24, 8, 0#64)]) dcStackAddr)]) [(b.pay + 8, 8, w1)])
      (b.pay + 24) = ldv .ld (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(b.pay, 4, 0#64)]) [(b.pay + 16, 8, 0#64)]) [(b.pay + 24, 8, 0#64)]) [(b.pay, 8, w0)])
      [(b.pay + 24, 8, ldv .ld (writeLog (writeLog (writeLog M [(b.pay, 4, 0#64)])
        [(b.pay + 16, 8, 0#64)]) [(b.pay + 24, 8, 0#64)]) dcStackAddr)]) [(b.pay + 8, 8, w1)])
      dcStackAddr := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit, hds]
    repeat rw [ldv_ld_miss _ _ (by omega)]
  refine ⟨h5.pushNode hf hn hl hv, fun a ha => ?_⟩
  simp only [not_or] at ha
  rw [imgM_store_miss _ _ (by omega)]
  exact hm5 a ha.1

/-- **`dc_push(value)`** at `0x80002da4`: the handle `g` (denoting `v`) in
`a0`/`a1` becomes the top of the stack. -/
theorem dc_push_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {v : Val}
    (h : DcAt S M H F L C G (g :: hs) st) (hv : g.Den ⟨L, G.strs⟩ v) {sp : Nat}
    (hsf : StackFrame S sp 64) (hab : heapEnd + 64 ≤ sp)
    (R : Nat → BitVec 64) (hd : DatRegs (R 10) (R 11) g) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' c, Keeps pushClob R' R →
      DcAt S M' H' F L C { G with stk := (c, g) :: G.stk } hs (st.push v) → StkOut sp 64 M' M →
      DW live S Q (R 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 64) → StkOut sp 64 M' M →
      DW live S Q 0x80001e74#64 R' M') :
    DW live S Q 0x80002da4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  obtain ⟨htg1, htg2⟩ := g.tag_pos
  have ht := hd.tag
  bc_run hlive hS [h2, word_sub48] at 0x80001ea0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 48) (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 24, 8, R 11)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hP : ∀ a, frameIn sp 48 a → OutHeap a ∧ ¬ DcGlob a := fun a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by have := hg.lt; simp only [heapStart] at this; omega⟩
  have h1 := h.outWrite hM1 hP
  refine dc_malloc_spec hlive h1.heap.heap (n := 32) (sp := sp - 48) (by omega)
    (hsf.sub (m := 48) (n := 16) (by decide)) (by simp only [heapEnd]; omega) _ (by bsimp []) (by bsimp []) (by bsimp [])
    (fun R1 M2 H2 b hk1 hp hr10 => ?_) (fun R1 M2 hr2 hfr => ?_)
  rotate_left
  · refine hoom _ _ (by rw [hr2, Nat.sub_sub]) fun a ho hg hf => ?_
    rw [hfr a (OutHeap.not_alloc h1.heap.heap ho) fun hf' => hf (by
      simp only [frameIn] at hf' ⊢; omega)]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
  obtain ⟨h2', hfr⟩ := h1.malloc hp (by decide) (by simp only [heapEnd]; omega)
  have hbsz := hp.size
  have hcl := hfr.live
  have fbb := h2'.heap.heap.blk (List.mem_append_right _ hcl)
  have hblo : 2147603920 ≤ b.h := fbb.lo
  have hbhi : b.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : b.h % 16 = 0 := fbb.al
  have hpl : 2147603936 ≤ b.pay ∧ b.pay + 32 ≤ 2273312768 ∧ b.pay % 16 = 0 := by
    simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp []
  have hS2 : HeapOwn S := fun a h1 h2 => h2'.heap.heap.own a h1 h2
  have htag : ldv .lw M2 (sp - 48 + 16) = BitVec.ofNat 64 g.tag := by
    rw [ldv_congr .lw fun j hj => hp.frame _ (fun ha => by
        have := (AllocByte.glob_or_heap h1.heap.heap ha)
        simp only [widthOfM, freeListAddr, heapStart, heapEnd] at hj this; omega)
      fun hf => by simp only [frameIn, widthOfM] at hf hj; omega]
    rw [ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega), VsaIris.Interp.ldv_lw_store8 _ _ rfl (by omega), ht]
  have wp : BitVec.ofNat 64 g.tag + 18446744073709551615#64 = BitVec.ofNat 64 (g.tag - 1) := word_pred htg1
  have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (g.tag - 1))) =
      BitVec.ofNat 64 (g.tag - 1) := sxw_ofNat (by omega)
  bsimp []
  bc_run hlive hS2 [q1, hr10, htag, se12_fff, wp, wq] at 0x80002dd0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bsimp []
  bc_run hlive hS2 [q1, hr10, htag, se12_fff, wp, wq] at 0x80002dd8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine st_80002dd8 hlive (fun _ => ?_) (fun hc => absurd ?_ hc)
  rotate_left
  · simp [upd]; omega
  have hfrm : ∀ o, 8 ≤ o → o + 8 ≤ 48 → ldv .ld M2 (sp - 48 + o) =
      ldv .ld (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 10)]) [(sp - 48 + 40, 8, R 1)])
        [(sp - 48 + 24, 8, R 11)]) (sp - 48 + o) := fun o ho1 ho2 =>
    ldv_congr .ld fun j hj => hp.frame _ (fun ha => by
        have := (AllocByte.glob_or_heap h1.heap.heap ha)
        simp only [widthOfM, freeListAddr, heapStart, heapEnd] at hj this; omega)
      fun hf => by simp only [frameIn, widthOfM] at hf hj; omega
  have hv0 : ldv .ld M2 (sp - 48 + 16) = R 10 := by
    rw [hfrm 16 (by omega) (by omega)]; simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]
  have hv1 : ldv .ld M2 (sp - 48 + 24) = R 11 := by
    rw [hfrm 24 (by omega) (by omega)]; simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]
  have hv2 : ldv .ld M2 (sp - 48 + 40) = R 1 := by
    rw [hfrm 40 (by omega) (by omega)]; simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]
  have hm3 : ∀ o, 8 ≤ o → o + 8 ≤ 48 → ldv .ld (writeLog (writeLog (writeLog M2 [(b.pay, 4, 0#64)])
      [(b.pay + 16, 8, 0#64)]) [(b.pay + 24, 8, 0#64)]) (sp - 48 + o) = ldv .ld M2 (sp - 48 + o) :=
    fun o _ _ => by
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
  refine push_tail hlive hS2 hsf (by simp only [heapEnd]; omega) hpl1 hpl2 hpl3 (by bsimp [q1])
    (by bsimp []) ((hm3 16 (by omega) (by omega)).trans hv0) ((hm3 24 (by omega) (by omega)).trans hv1)
    ((hm3 40 (by omega) (by omega)).trans hv2) hal h2'.stkAcc fun R2 hk2 hr1 hr2 => ?_
  obtain ⟨h6, hm6⟩ := push_post h2' hfr hv hd hbsz hpl1
  refine hk R2 _ H2 b (fun z hz => ?_) h6 fun a ho hg hf => ?_
  · by_cases e1 : z = 1
    · subst e1; exact hr1
    by_cases e2 : z = 2
    · subst e2; rw [hr2, h2]
    simp only [pushClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨n10, n11, n12, n13, n14, n15⟩ := hz
    rw [hk2 z (by simp; omega)]
    simp only [upd, n13, n14, n15, ite_false]
    rw [hk1 z (by simp; omega)]
    simp only [upd, e1, e2, n10, ite_false]
  · have hnb : ¬ b.In a := fun hb => by
      simp only [Blk.In, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hb ho; omega
    rw [hm6 a fun hc => hc.elim hnb fun hs => hg (by simp only [DcGlob, dc_addrs] at hs ⊢; omega)]
    rw [hp.frame a (OutHeap.not_alloc h1.heap.heap ho) fun hf' => hf (by
      simp only [frameIn] at hf' ⊢; omega)]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

end Dc.Mach
