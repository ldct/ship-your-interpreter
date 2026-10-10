import Dc.Mach.DcMsg
import Dc.Mach.DcStack

/-!
# `dc_pop` (M9)

    dc_pop (dc_data *result):
      if (dc_stack == NULL || dc_stack->value.dc_type == DC_UNINITIALIZED)
        { fprintf (stderr, "%s: stack empty\n", progname); return DC_FAIL; }
      if (type is neither number nor string) dc_garbage (...);
      *result = dc_stack->value; r = dc_stack; dc_stack = r->link;
      dc_array_free (r->array); free (r); return DC_SUCCESS;

- `DatSlot`: the caller's 16-byte result slot.
- `pop_empty`: the message path.
- `dc_pop_spec`: the top datum moves to the slot, or the message and `2`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)


/-- The message path of `dc_pop` (`0x80003198`), the 32-byte frame at
`sp - 32` holding `ra` and `s0`. -/
theorem pop_empty {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) {ra s0 : BitVec 64}
    (hra : ldv .ld M (sp - 32 + 24) = ra) (hs0 : ldv .ld M (sp - 32 + 16) = s0)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M', Keeps (1 :: 2 :: 8 :: fprintfClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 10 = 2#64 → (∀ a, (a < sp - 336 ∨ sp - 32 ≤ a) → imgM M' a = imgM M a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x80003198#64 R M := by
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
  have hs01 : ldv .ld M1 (sp - 32 + 16) = s0 := by
    rw [ldv_congr .ld fun j hj => hfr1 _ (.inr (by simp only [widthOfM] at hj; omega))]; exact hs0
  bsimp []
  bc_run hlive hS [q2, hra1, hs01]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hal
  refine hk _ M1 (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (by bsimp []) (by rw [upd_same]; congr 1; omega) (by bsimp []) (by bsimp []) ?_
  intro a ha
  exact hfr1 a (hwin a ha)

/-- The caller's 16-byte `dc_data` slot at `q`, above the frame. -/
structure DatSlot (S : Nat → Prop) (sp q : Nat) : Prop where
  own : ∀ i, i < 16 → S (q + i)
  lo : sp ≤ q
  hi : q + 16 ≤ 0x88000000
  al : q % 8 = 0

/-- The memory after `dc_pop`'s stores: the node's datum words at `q`, the
link in `dc_stack`. -/
abbrev popMem (M : Mem) (q p : Nat) : Mem :=
  writeLog (writeLog (writeLog M [(q, 8, ldv .ld M p)]) [(dcStackAddr, 8, ldv .ld M (p + 24))])
    [(q + 8, 8, ldv .ld M (p + 8))]

/-- `dc_pop`'s stores and `dc_array_free (NULL)` (`0x8000313c` to
`0x80003160`): the node at `p`, the slot at `q`. -/
theorem pop_mid {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64}
    {sp p q : Nat} (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (hp1 : 2147603936 ≤ p) (hp2 : p + 32 ≤ 2273312768) (hp3 : p % 16 = 0)
    (hG : ∀ a, DcGlob a → S a)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h8 : R 8 = BitVec.ofNat 64 p)
    (h14 : R 14 = BitVec.ofNat 64 q) (harr : ldv .ld M (p + 16) = 0#64)
    (hk : ∀ R', Keeps [1, 10, 12, 13, 14, 15] R' R → DW live S Q 0x80003160#64 R' (popMem M q p)) :
    DW live S Q 0x8000313c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hq1 := hq.lo; have hq2 := hq.hi; have hq3 := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hqS : ∀ b ∈ accAddrs q 8, S b := fun b hb => by
    have := of_mem_accAddrs hb; have e := hq.own (b - q) (by omega)
    rwa [show q + (b - q) = b by omega] at e
  have hqS8 : ∀ b ∈ accAddrs (q + 8) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb; have e := hq.own (b - q) (by omega)
    rwa [show q + (b - q) = b by omega] at e
  have hp8 : ldv .ld (writeLog M [(q, 8, ldv .ld M p)]) (p + 8) = ldv .ld M (p + 8) :=
    ldv_ld_miss _ _ (by omega)
  bc_run hlive hS [h2, h8, h14, hp8, harr] at 0x80003160
  all_goals first | exact hqS | exact hqS8 | skip
  refine st_80003eb8 hlive (by bsimp []) ?_
  rw [ldv_ld_miss (a := p + 8) _ _ (by omega)]
  exact hk _ (by keeps_tac Keeps.refl _ _)

/-- `free (node)` and the epilogue of `dc_pop` (`0x80003160`). -/
theorem pop_tail {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} (hi : HeapInv S M H)
    {lpre lpost : List Blk} {c : Blk} (hl : H.live = lpre ++ c :: lpost)
    {sp : Nat} (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h8 : R 8 = BitVec.ofNat 64 c.pay)
    {ra s0 : BitVec 64} (hra : ldv .ld M (sp - 32 + 24) = ra) (hs0 : ldv .ld M (sp - 32 + 16) = s0)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M', Keeps [1, 2, 8, 10, 14, 15] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 10 = 0#64 →
      FreePost S M M' H ⟨H.braw, c :: H.free, lpre ++ lpost⟩ c lpre lpost →
      DW live S Q ra R' M') :
    DW live S Q 0x80003160#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  bc_run hlive hS [h2, h8] at 0x80000a0c
  refine free_spec hlive hi hl _ (by bsimp [h8]) (by bsimp []) fun R1 M1 hk1 hp => ?_
  have hfm : ∀ o, o + 8 ≤ 32 → ldv .ld M1 (sp - 32 + o) = ldv .ld M (sp - 32 + o) := fun o ho =>
    ldv_congr .ld fun j hj => hp.frame _ (OutHeap.not_alloc hi (outHeap_of_ge (by
      simp only [heapEnd, widthOfM] at hj ⊢; omega)))
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  have hra1 := (hfm 24 (by omega)).trans hra
  have hs01 := (hfm 16 (by omega)).trans hs0
  bsimp []
  bc_run hlive hS [q2, hra1, hs01]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hal
  exact hk _ M1 (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (by bsimp []) (by rw [upd_same]; congr 1; omega) (by bsimp []) (by bsimp []) hp

/-- Registers through a callee that restores `ra`, `sp`, `s0`. -/
theorem Keeps.restore3 {ks : List Nat} {R' R1 R : Nat → BitVec 64}
    (h1 : Keeps (1 :: 2 :: 8 :: ks) R' R1) (h0 : Keeps (2 :: 8 :: ks) R1 R)
    (e1 : R' 1 = R 1) (e2 : R' 2 = R 2) (e8 : R' 8 = R 8) : Keeps ks R' R := fun z hz => by
  by_cases z1 : z = 1
  · subst z1; exact e1
  by_cases z2 : z = 2
  · subst z2; exact e2
  by_cases z8 : z = 8
  · subst z8; exact e8
  have hz' : z ∉ 1 :: 2 :: 8 :: ks := by simp [z1, z2, z8, hz]
  rw [h1 z hz', h0 z (by simp [z2, z8, hz])]

/-- `dc_pop`'s memory frame: only the heap, `dc_stack`, the window below `sp`
and the slot at `q` change. -/
def PopOut (sp q : Nat) (M' M : Mem) : Prop :=
  ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 336 a → (a < q ∨ q + 16 ≤ a) → imgM M' a = imgM M a

/-- The registers `dc_pop` may change. -/
abbrev popClob : List Nat := fprintfClob

/-- `dc_pop` on a non-empty stack, from the type check (`0x80003124`, `s0`
the top node `c`, `a0` the slot `q`). -/
theorem pop_some {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {c : Blk} {g : GV} {hs : List GV} {st : St} {v : Val}
    (h : DcAt S M H F L C { G with stk := (c, g) :: G.stk } hs (st.push v)) {sp q : Nat}
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h8 : R 8 = BitVec.ofNat 64 c.pay)
    (h10 : R 10 = BitVec.ofNat 64 q) {ra s0 : BitVec 64}
    (hra : ldv .ld M (sp - 32 + 24) = ra) (hs0 : ldv .ld M (sp - 32 + 16) = s0)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H', Keeps (1 :: 2 :: 8 :: popClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 10 = 0#64 → DcAt S M' H' F L C G (g :: hs) st → DatAt M' q g →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 336 a → (a < q ∨ q + 16 ≤ a) →
        imgM M' a = imgM M a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x80003124#64 R M := by
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
  have hne : BitVec.ofNat 64 g.tag ≠ 0#64 := by cases g <;> simp only [GV.tag] <;> decide
  bc_run hlive hS [h8, htag, wp, wq] at 0x80003138
  all_goals try (intro hc; exact absurd hc hne)
  intro _
  bsimp []
  bc_run hlive hS [h8, htag, wp, wq] at 0x80003138
  refine st_80003138 hlive (fun hc => absurd hc ?_) fun _ => ?_
  · bsimp []; omega
  have hqo : ∀ a, (q ≤ a ∧ a < q + 16) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  -- the state through the stores
  have h2a := h.outWrite (P := fun a => q ≤ a ∧ a < q + 8)
    (M' := writeLog M [(q, 8, ldv .ld M c.pay)]) (MemOnly.store M _ 8 _)
    fun a ha => hqo a ⟨ha.1, by omega⟩
  obtain ⟨h2b, hfr, -, -⟩ := h2a.popNode
  have e24 : ldv .ld (writeLog M [(q, 8, ldv .ld M c.pay)]) (c.pay + 24) = ldv .ld M (c.pay + 24) :=
    ldv_ld_miss _ _ (by omega)
  rw [e24] at h2b
  have h2c := h2b.outWrite (P := fun a => q + 8 ≤ a ∧ a < q + 8 + 8)
    (M' := popMem M q c.pay) (MemOnly.store _ _ 8 _) fun a ha => hqo a ⟨by omega, by omega⟩
  obtain ⟨lpre, lpost, hlv⟩ := List.append_of_mem hcl
  refine pop_mid hlive hS hsf (by simp only [heapEnd]; omega) hq hpl1 hpl2 hpl3 hG (by bsimp [h2])
    (by bsimp [h8]) (by bsimp [h10]) hn.arr fun R1 hk1 => ?_
  have hpm : ∀ o, o + 8 ≤ 32 → ldv .ld (popMem M q c.pay) (sp - 32 + o) = ldv .ld M (sp - 32 + o) :=
    fun o ho => by
      simp only [popMem]
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by simp only [dc_addrs]; omega),
        ldv_ld_miss _ _ (by omega)]
  refine pop_tail hlive h2c.heap.heap hlv hsf (by simp only [heapEnd]; omega) R1
    (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8])
    ((hpm 24 (by omega)).trans hra) ((hpm 16 (by omega)).trans hs0) hal
    fun R' M' hk2 e1 e2 e8 e10 hp => ?_
  have hi2 := h2c.heap.heap
  have hpq : ∀ k, k + 8 ≤ 16 → ldv .ld M' (q + k) = ldv .ld (popMem M q c.pay) (q + k) := fun k hk =>
    ldv_congr .ld fun j hj => hp.frame _ (OutHeap.not_alloc hi2 (hqo _ ⟨by omega, by
      simp only [widthOfM] at hj; omega⟩).1)
  have hd : DatAt M' q g := by
    refine ⟨?_, ?_⟩
    · have e := hpq 0 (by omega)
      simp only [Nat.add_zero] at e
      rw [e]; simp only [popMem]
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by simp only [dc_addrs]; omega), ldv_store_hit]
      exact hn.dat.tag
    · rw [hpq 8 (by omega)]; simp only [popMem]
      rw [ldv_store_hit]; exact hn.dat.ptr
  refine hk R' M' _ ((hk2.mono (by decide)).trans ((hk1.mono (by decide)).trans
    (by keeps_tac Keeps.refl _ _))) e1 e2 e8 e10 (h2c.free hfr hlv hp) hd fun a ho hg hf hqa => ?_
  rw [hp.frame a (OutHeap.not_alloc hi2 ho)]
  simp only [popMem]
  simp only [DcGlob, dc_addrs, not_or] at hg
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by simp only [dc_addrs]; omega),
    imgM_store_miss _ _ (by omega)]

/-- **`dc_pop (result)`** at `0x8000310c`: the top datum (node `c`) moves to the
slot `q` (`0` returned), or, on an empty stack, the message to `stderr` and `2`. -/
theorem dc_pop_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp q : Nat}
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' (G' : DcG) g v st', st = st'.push v →
      (∃ c, G = { G' with stk := (c, g) :: G'.stk }) → Keeps popClob R' R → R' 10 = 0#64 →
      DcAt S M' H' F L C G' (g :: hs) st' → DatAt M' q g → PopOut sp q M' M →
      DWO live S Q t (R 1) R' M')
    (hk0 : st.stack = [] → ∀ R' M', Keeps popClob R' R → R' 10 = 2#64 →
      DcAt S M' H F L C G hs st → PopOut sp q M' M → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x8000310c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hq1 := hq.lo
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hM1 : MemOnly (frameIn sp 32) (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
      [(sp - 32 + 24, 8, R 1)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hP : ∀ n, n ≤ 336 → ∀ a, frameIn sp n a → OutHeap a ∧ ¬ DcGlob a := fun n hn a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have h1 := h.outWrite hM1 (hP 32 (by omega))
  obtain ⟨stk, regs, strs, lbuf, lk⟩ := G
  cases stk with
  | nil =>
    have hst0 : st.stack = [] := by
      have key : ∀ (P : Blk × GV → Val → Prop) l, List.Forall₂ P [] l → l = [] := fun P l hl => by
        cases hl; rfl
      exact key _ _ h.den.stk
    bc_run hlive hS [h2] at 0x80003198
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals try (intro hc; refine absurd ?_ hc; rw [ldv_ld_miss _ _ (by omega)]
                   have hv := h.view.stk; cases hv with | nil h0 => exact h0)
    intro _
    have hra1 : ldv .ld (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)])
        (sp - 32 + 24) = R 1 := ldv_store_hit _ _ _
    have hs01 : ldv .ld (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)])
        (sp - 32 + 16) = R 8 := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    refine pop_empty hlive h1 hsf (by simp only [heapEnd]; omega) _ ?_ hra1 hs01 hal
      fun R' M' hk1 e1 e2 e8 e10 hfr => ?_
    · bsimp []
    refine hk0 hst0 R' M' (hk1.restore3 (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2]) e8) e10
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
    have hcG : c ∈ (⟨(c, g) :: rest, regs, strs, lbuf, lk⟩ : DcG).blocks := by
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
    bc_run hlive hS [h2] at 0x80003124
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals try (intro hc; rw [ldv_ld_miss _ _ (by omega), h0] at hc; exact absurd hc hc0)
    intro _
    have hra1 : ldv .ld (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)])
        (sp - 32 + 24) = R 1 := ldv_store_hit _ _ _
    have hs01 : ldv .ld (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)])
        (sp - 32 + 16) = R 8 := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    refine pop_some (G := ⟨rest, regs, strs, lbuf, lk⟩) (st := ⟨rest', sregs, ib, ob, sc, uw, ne, out⟩)
      hlive h1 hsf (by simp only [heapEnd]; omega) hq _ ?_ ?_ ?_ hra1 hs01 hal
      fun R' M' H' hk1 e1 e2 e8 e10 h' hd hfr => ?_
    · bsimp []
    · bsimp []; rw [ldv_ld_miss _ _ (by omega), h0]
    · bsimp [h10]
    refine hk R' M' H' _ g v _ rfl ⟨c, rfl⟩ (hk1.restore3 (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2]) e8)
      e10 h' hd fun a ho hg hf hqa => ?_
    rw [hfr a ho hg hf hqa]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

end Dc.Mach
