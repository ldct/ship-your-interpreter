import Dc.Mach.DcPop

/-!
# `dc_top_of_stack` (M9)

    dc_top_of_stack (dc_data *result):
      if (dc_stack == NULL)
        { fprintf (stderr, "%s: stack empty\n", progname); return DC_FAIL; }
      if (type is neither number nor string) dc_garbage (...);
      *result = dc_stack->value; return DC_SUCCESS;

The result is a shallow copy: the slot `q` holds the top datum's words and
the dc state is unchanged.

- `top_empty`: the message path (`0x80002ef4`).
- `top_some`: the copy (`0x80002ea0`).
- `dc_top_spec`: the whole function.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- Registers through a callee that restores `ra` and `sp`. -/
theorem Keeps.restore2 {ks : List Nat} {R' R1 R : Nat → BitVec 64}
    (h1 : Keeps (1 :: 2 :: ks) R' R1) (h0 : Keeps (2 :: ks) R1 R)
    (e1 : R' 1 = R 1) (e2 : R' 2 = R 2) : Keeps ks R' R := fun z hz => by
  by_cases z1 : z = 1
  · subst z1; exact e1
  by_cases z2 : z = 2
  · subst z2; exact e2
  rw [h1 z (by simp [z1, z2, hz]), h0 z (by simp [z2, hz])]

/-- The message path of `dc_top_of_stack` (`0x80002ef4`), the 32-byte frame
at `sp - 32` holding `ra`. -/
theorem top_empty {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) {ra : BitVec 64}
    (hra : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M', Keeps (1 :: 2 :: fprintfClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 10 = 2#64 → (∀ a, (a < sp - 336 ∨ sp - 32 ≤ a) → imgM M' a = imgM M a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x80002ef4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hwin : ∀ a, (a < sp - 336 ∨ sp - 32 ≤ a) → a < sp - 32 - 304 ∨ sp - 32 ≤ a :=
    fun a ha => by rw [Nat.sub_sub]; omega
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hpn := h.view.prog
  have hG := h.glob
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hS [h2, hpn, stderr_word] at 0x80000774
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hfd := h.errFile
  refine fprintf_prog_spec hlive stackEmptyMsg (by decide) (hsf.sub (m := 32) (n := 304) (by decide))
    (by simp only [stderrAddr]; omega) hfd _ (by bsimp [h2]) (by bsimp [stderrAddr]) (by bsimp []) (by bsimp [])
    (by bsimp []) fun R1 M1 hk1 hfr1 => ?_
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  have hra1 : ldv .ld M1 (sp - 32 + 24) = ra := by
    rw [ldv_congr .ld fun j hj => hfr1 _ (.inr (by simp only [widthOfM] at hj; omega))]; exact hra
  bsimp []
  bc_run hlive hS [q2, hra1]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hal
  refine hk _ M1 (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (by bsimp []) (by rw [upd_same]; congr 1; omega) (by bsimp []) ?_
  intro a ha
  exact hfr1 a (hwin a ha)

/-- The memory after `dc_top_of_stack`'s copy of the node at `p` to `q`. -/
abbrev topMem (M : Mem) (q p : Nat) : Mem :=
  writeLog (writeLog M [(q, 8, ldv .ld M p)])
    [(q + 8, 8, ldv .ld (writeLog M [(q, 8, ldv .ld M p)]) (p + 8))]

/-- `dc_top_of_stack` on a non-empty stack, from the type check
(`0x80002ea0`, `a5` the top node `c`, `a0` the slot `q`). -/
theorem top_some {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {c : Blk} {g : GV} {hs : List GV} {st : St} {v : Val}
    (h : DcAt S M H F L C { G with stk := (c, g) :: G.stk } hs (st.push v)) {sp q : Nat}
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h15 : R 15 = BitVec.ofNat 64 c.pay)
    (h10 : R 10 = BitVec.ofNat 64 q) {ra : BitVec 64}
    (hra : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps (1 :: 2 :: popClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 10 = 0#64 → DcAt S (topMem M q c.pay) H F L C { G with stk := (c, g) :: G.stk } hs (st.push v) →
      DatAt (topMem M q c.pay) q g → DWO live S Q t ra R' (topMem M q c.pay)) :
    DWO live S Q t 0x80002ea0#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hq1 := hq.lo; have hq2 := hq.hi; have hq3 := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hv := h.view.stk
  cases hv with
  | cons h0 hn hl =>
  have hcG : c ∈ ({ G with stk := (c, g) :: G.stk } : DcG).blocks := by
    rw [G.blocks_pushStk]; exact List.mem_cons_self
  have hcl := h.heap.raw.live c hcG
  have fbb := h.heap.heap.blk (List.mem_append_right _ hcl)
  have hblo : 2147603920 ≤ c.h := fbb.lo
  have hbhi : c.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : c.h % 16 = 0 := fbb.al
  have hbsz := hn.sz
  have hpl : 2147603936 ≤ c.pay ∧ c.pay + 32 ≤ 2273312768 ∧ c.pay % 16 = 0 := by
    simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  have htag := hn.dat.lw
  obtain ⟨htg1, htg2⟩ := g.tag_pos
  have wp : BitVec.ofNat 64 g.tag + 18446744073709551615#64 = BitVec.ofNat 64 (g.tag - 1) := word_pred htg1
  have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (g.tag - 1))) =
      BitVec.ofNat 64 (g.tag - 1) := sxw_ofNat (by omega)
  have hqS : ∀ b ∈ accAddrs q 8, S b := fun b hb => by
    have := of_mem_accAddrs hb; have e := hq.own (b - q) (by omega)
    rwa [show q + (b - q) = b by omega] at e
  have hqS8 : ∀ b ∈ accAddrs (q + 8) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb; have e := hq.own (b - q) (by omega)
    rwa [show q + (b - q) = b by omega] at e
  bc_run hlive hS [h15, h10, htag, wp, wq] at 0x80002eb0
  refine st_80002eb0 hlive (fun _ => ?_) fun hc => absurd ?_ hc
  rotate_left
  · bsimp []; omega
  have hp8 : ldv .ld (writeLog M [(q, 8, ldv .ld M c.pay)]) (c.pay + 8) = ldv .ld M (c.pay + 8) :=
    ldv_ld_miss _ _ (by omega)
  bc_run hlive hS [h2, h15, h10, hp8]
  all_goals first | exact hqS | exact hqS8 | exact frame_acc hsf (by omega) (by omega) | skip
  have hra2 : ldv .ld (topMem M q c.pay) (sp - 32 + 24) = ra := by
    simp only [topMem]; rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hra
  · rw [hra2]; exact hal
  have hqo : ∀ a, (q ≤ a ∧ a < q + 16) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have hd : DatAt (topMem M q c.pay) q g := by
    refine ⟨?_, ?_⟩
    · simp only [topMem]
      rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
      exact hn.dat.tag
    · simp only [topMem]
      rw [ldv_store_hit, ldv_ld_miss _ _ (by omega)]; exact hn.dat.ptr
  have h' := h.outWrite (P := fun a => q ≤ a ∧ a < q + 16) (M' := topMem M q c.pay)
    (fun a ha => by
      simp only [topMem]
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)])
    fun a ha => hqo a ha
  have hra2 : ldv .ld (topMem M q c.pay) (sp - 32 + 24) = ra := by
    simp only [topMem]; rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hra
  rw [hra2]
  exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp [hra2]) (by rw [upd_same]; congr 1; omega)
    (by bsimp []) h' hd

/-- **`dc_top_of_stack (result)`** at `0x80002e8c`: the top datum's words are
copied to the slot `q` (`0` returned, the dc state unchanged), or, on an
empty stack, the message to `stderr` and `2`. -/
theorem dc_top_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp q : Nat}
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' c g rest, G.stk = (c, g) :: rest → Keeps popClob R' R → R' 10 = 0#64 →
      DcAt S M' H F L C G hs st → DatAt M' q g → PopOut sp q M' M →
      DWO live S Q t (R 1) R' M')
    (hk0 : st.stack = [] → ∀ R' M', Keeps popClob R' R → R' 10 = 2#64 →
      DcAt S M' H F L C G hs st → PopOut sp q M' M → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80002e8c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hq1 := hq.lo
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hM1 : MemOnly (frameIn sp 32) (writeLog M [(sp - 32 + 24, 8, R 1)]) M := fun a ha => by
    simp only [frameIn] at ha; rw [imgM_store_miss _ _ (by omega)]
  have hP : ∀ n, n ≤ 336 → ∀ a, frameIn sp n a → OutHeap a ∧ ¬ DcGlob a := fun n hn a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have h1 := h.outWrite hM1 (hP 32 (by omega))
  obtain ⟨stk, regs, strs, lbuf⟩ := G
  cases stk with
  | nil =>
    have hst0 : st.stack = [] := by
      have key : ∀ (P : Blk × GV → Val → Prop) l, List.Forall₂ P [] l → l = [] := fun P l hl => by
        cases hl; rfl
      exact key _ _ h.den.stk
    have h0 : ldv .ld M dcStackAddr = 0#64 := by
      have hv := h.view.stk; cases hv with | nil h0 => exact h0
    bc_run hlive hS [h2, h0] at 0x80002ef4
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hra1 : ldv .ld (writeLog M [(sp - 32 + 24, 8, R 1)]) (sp - 32 + 24) = R 1 :=
      ldv_store_hit _ _ _
    refine top_empty hlive h1 hsf (by simp only [heapEnd]; omega) _ (by bsimp []) hra1 hal
      fun R' M' hk1 e1 e2 e10 hfr => ?_
    refine hk0 hst0 R' M' (hk1.restore2 (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2])) e10
      (h1.outWrite (P := frameIn sp 336) (fun a ha => hfr a (by simp only [frameIn] at ha; omega))
        (hP 336 (by omega))) fun a _ _ hf _ => ?_
    rw [hfr a (by simp only [frameIn] at hf; omega)]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
  | cons cg rest =>
    obtain ⟨c, g⟩ := cg
    obtain ⟨stack, sregs, ib, ob, sc, uw, ne, out⟩ := st
    cases stack with
    | nil =>
      have key : ∀ (P : Blk × GV → Val → Prop) a l, ¬ List.Forall₂ P (a :: l) [] := fun P a l hl => by
        cases hl
      exact absurd h.den.stk (key _ _ _)
    | cons v rest' =>
    have hv := h.view.stk
    cases hv with
    | cons h0 hn hl =>
    have hcG : c ∈ (⟨(c, g) :: rest, regs, strs, lbuf⟩ : DcG).blocks := by
      simp only [DcG.blocks, List.map_cons, List.cons_append, List.mem_cons, true_or]
    have fbb := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live c hcG))
    have hpl : 2147603936 ≤ c.pay ∧ c.pay < 2 ^ 64 := by
      have a1 : 2147603920 ≤ c.h := fbb.lo
      have a2 : c.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
      have e1 : c.pay = c.h + 16 := rfl
      have e2 : c.fin = c.h + 16 + c.sz := rfl
      omega
    have hc0 : BitVec.ofNat 64 c.pay ≠ 0#64 := fun hc => by
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl.2, BitVec.toNat_ofNat] at this
      omega
    bc_run hlive hS [h2, h0] at 0x80002ea0
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals try (intro hc; exact absurd hc hc0)
    intro _
    have hra1 : ldv .ld (writeLog M [(sp - 32 + 24, 8, R 1)]) (sp - 32 + 24) = R 1 :=
      ldv_store_hit _ _ _
    refine top_some (G := ⟨rest, regs, strs, lbuf⟩) (st := ⟨rest', sregs, ib, ob, sc, uw, ne, out⟩)
      hlive h1 hsf (by simp only [heapEnd]; omega) hq _ (by bsimp []) (by bsimp [h0]) (by bsimp [h10])
      hra1 hal fun R' hk1 e1 e2 e10 h' hd => ?_
    refine hk R' _ c g rest rfl (hk1.restore2 (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2])) e10
      h' hd fun a _ _ hf hqa => ?_
    simp only [topMem]
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

end Dc.Mach
