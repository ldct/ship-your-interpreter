import Dc.Mach.DcArrFree

/-!
# `dc_clear_stack` (M9)

    dc_clear_stack ():
      for (n = dc_stack; n; n = t) {
        t = n->link;
        free the datum (dc_free_num / dc_free_str);
        dc_array_free (n->array); free (n); }
      dc_stack = NULL;

The machine frees the nodes while `dc_stack` still names the first, so the
state is held on the view `stkV w M`: the machine memory with `dc_stack` as
the next node `w`, a pending window over the word (`pend_stk`). Each node is
popped in the view (`DcAt.popTop`), its datum freed through
`dc_free_num_specP`/`dc_free_str_specP`, its array (`NULL` on the stack) by
`dc_array_free`'s first branch and the node by `free`. The closing store of
`NULL` makes the machine memory the view.

- `cs_tail`: `dc_array_free (NULL)`, `free (n)`, the loop test.
- `cs_num`, `cs_str`: a node by its datum's type; `cs_body` pops and
  dispatches; `cs_loop` runs the chain.
- `dc_clear_stack_spec`: the stack empty, every datum's reference released.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- A doubleword store of the word already there changes no byte. -/
theorem imgM_store_self (M : Mem) {a : Nat} {v : BitVec 64} (hv : ldv .ld M a = v) (x : Nat) :
    imgM (writeLog M [(a, 8, v)]) x = imgM M x := by
  by_cases hx : a ≤ x ∧ x < a + 8
  · have e : imgLE (imgM (writeLog M [(a, 8, v)])) a 8 = imgLE (imgM M) a 8 := by
      rw [imgLE_imgM_store, ← hv, show ldv .ld M a = ldvf .ld (imgM M) a from rfl,
        ldvf_ld_imgLE rfl, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := imgLE_lt (imgM M) a 8; omega)
    have := imgLE_inj e (x - a) (by omega)
    rwa [show a + (x - a) = x by omega] at this
  · exact imgM_store_miss _ _ (by omega)

/-- **The view of `dc_stack`**: the machine memory with the word `w` there. -/
abbrev stkV (w : BitVec 64) (M : Mem) : Mem := writeLog M [(dcStackAddr, 8, w)]

/-- The word `dc_stack` is a pending window of any ghost. -/
theorem pend_stk (G : DcG) (w : BitVec 64) : Pend G [] StkWord (stkV w) where
  out M x hx := imgM_store_miss _ _ (by simp only [StkWord] at hx; omega)
  fix M M' x hx := imgM_store_same _ _ w (.inr rfl) hx
  sub _ h := absurd h List.not_mem_nil
  win _ hx := .inr hx
  nstr _ h := absurd h List.not_mem_nil

/-- A second view word replaces the first. -/
theorem stkV_stkV (v w : BitVec 64) (M : Mem) (x : Nat) :
    imgM (writeLog (stkV w M) [(dcStackAddr, 8, v)]) x = imgM (stkV v M) x := by
  by_cases hx : StkWord x
  · exact imgM_store_same _ _ v (.inr rfl) hx
  · simp only [StkWord] at hx
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]

/-- **The top node popped** from any state whose stack starts at `c`. -/
theorem DcAt.popTop {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {c : Blk} {g : GV}
    {rest : List (Blk × GV)} (h : DcAt S M H F L C G hs st) (he : G.stk = (c, g) :: rest) :
    DcAt S (writeLog M [(dcStackAddr, 8, ldv .ld M (c.pay + 24))]) H F L C { G with stk := rest }
      (g :: hs) { st with stack := st.stack.tail } ∧
    DcFresh H F L { G with stk := rest } c ∧ SNodeAt M c g := by
  obtain ⟨stk, regs, strs, lbuf, lk⟩ := G
  simp only at he
  subst he
  obtain ⟨stack, sregs, ib, ob, sc, uw, ne, out⟩ := st
  cases stack with
  | nil =>
    have key : ∀ (P : Blk × GV → Val → Prop) a l, ¬ List.Forall₂ P (a :: l) [] := fun P a l hl => by
      cases hl
    exact absurd h.den.stk (key _ _ _)
  | cons v vs =>
    obtain ⟨h1, h2, h3, -⟩ := DcAt.popNode (G := ⟨rest, regs, strs, lbuf, lk⟩) (v := v)
      (st := ⟨vs, sregs, ib, ob, sc, uw, ne, out⟩) h
    exact ⟨h1, h2, h3⟩

/-- A word of a node, inside the node, in the heap. -/
theorem node_slot {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) (hS : HeapOwn S)
    {b : Blk} (hb : b ∈ H.live) {o : Nat} (ho : o + 8 ≤ b.sz) (ho8 : o % 8 = 0) :
    PtrSlot S (b.pay + o) ∧ (∀ a, slotBytes (b.pay + o) a → b.In a) := by
  have := blk_bounds hi hb
  simp only [heapStart, heapEnd] at this
  refine ⟨⟨fun i _ => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
    by simp only [tohostAddr]; omega, by omega⟩, fun a ha => ?_⟩
  simp only [slotBytes, Blk.In, Blk.pay, Blk.fin] at ha this ⊢; omega

/-- The registers one node of `dc_clear_stack` changes past its datum. -/
abbrev csTailClob : List Nat := [1, 10, 14, 15]

/-- After a node's datum is freed (`0x80002d24` or `0x80002d60`, `s0` the
node `b`, `s1` the next pointer `w`): `dc_array_free (NULL)`, `free (b)`,
then the loop test. -/
theorem cs_tail {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk} {w : BitVec 64}
    (h : DcAt S (stkV w M) H F L C G hs st) (hfb : DcFresh H F L G b) (hsz : 32 ≤ b.sz)
    (harr : ldv .ld M (b.pay + 16) = 0#64) {pc : BitVec 64}
    (hpc : pc = 0x80002d24#64 ∨ pc = 0x80002d60#64)
    (R : Nat → BitVec 64) (h8 : R 8 = BitVec.ofNat 64 b.pay) (h9 : R 9 = w)
    (hk : ∀ R' M' H', Keeps csTailClob R' R → DcAt S (stkV w M') H' F L C G hs st →
      (∀ a, OutHeap a → imgM M' a = imgM M a) →
      DW live S Q (if w = 0#64 then 0x80002d74#64 else 0x80002d38#64) R' M') :
    DW live S Q pc R M := by
  have hpd := pend_stk G w
  have hb := h.machHeap hpd
  have hi := hb.heap
  have hS : HeapOwn S := fun a e1 e2 => hi.own a e1 e2
  have hbb := blk_bounds hi hfb.live
  simp only [heapStart, heapEnd] at hbb
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨lpre, lpost, hl⟩ := List.append_of_mem hfb.live
  have hacc : ∀ x ∈ accAddrs (b.pay + 16) 8, S x := fun x hx => by
    have := of_mem_accAddrs hx
    exact hS x (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hrest : ∀ (R1 : Nat → BitVec 64), Keeps [1, 10] R1 R → R1 10 = BitVec.ofNat 64 b.pay →
      R1 9 = w → (R1 1 = 0x80002d34#64 ∨ R1 1 = 0x80002d70#64) → DW live S Q 0x80000a0c#64 R1 M := by
    intro R1 hk1 h10 q9 hra
    refine free_spec hlive hi hl R1 h10 (by rcases hra with e | e <;> rw [e] <;> decide)
      fun R' M' hk2 hp => ?_
    have h' := h.freeP hpd hfb hl hp
    have hk' := hk R' M' _ ((hk2.mono (by decide)).trans (hk1.mono (by decide))) h'
      fun a ho => hp.frame a (OutHeap.not_alloc hi ho)
    have p9 : R' 9 = w := by rw [hk2.get 9 (by decide)]; exact q9
    by_cases hz : w = 0#64
    · simp only [hz, ↓reduceIte] at hk'
      rcases hra with e | e <;> rw [e] <;>
        bc_run hlive hS [p9, hz] at 0x80002d74
      all_goals first | (intro hc; exact absurd (p9.symm.trans hc) hz) | (intro hc; exact absurd hc hz) | skip
      all_goals first | (intro hc; exact absurd (p9.trans hz) hc) | (intro hc; exact absurd hz hc) | skip
      all_goals try intro _
      all_goals exact hk'
    · simp only [hz, ↓reduceIte] at hk'
      rcases hra with e | e <;> rw [e] <;>
        bc_run hlive hS [p9] at 0x80002d38
      all_goals first | (intro hc; exact absurd (p9.symm.trans hc) hz) | (intro hc; exact absurd hc hz) | skip
      all_goals first | (intro hc; exact absurd (p9.trans hz) hc) | (intro hc; exact absurd hz hc) | skip
      all_goals try intro _
      all_goals exact hk'
  rcases hpc with rfl | rfl
  · bc_run hlive hS [h8, harr] at 0x80003eb8
    all_goals first | exact hacc | (intro hc; exact absurd hc (by decide)) | skip
    all_goals try intro _
    bc_run hlive hS [h8, harr] at 0x80000a0c
    exact hrest _ (by keeps_tac Keeps.refl _ _) (by bsimp [h8]) (by bsimp [h9]) (.inl (by bsimp []))
  · bc_run hlive hS [h8, harr] at 0x80003eb8
    all_goals first | exact hacc | (intro hc; exact absurd hc (by decide)) | skip
    all_goals try intro _
    bc_run hlive hS [h8, harr] at 0x80000a0c
    exact hrest _ (by keeps_tac Keeps.refl _ _) (by bsimp [h8]) (by bsimp [h9]) (.inr (by bsimp []))

/-- The registers one node of `dc_clear_stack` changes after its type test. -/
abbrev csNodeClob : List Nat := [1, 10, 13, 14, 15]

/-- A node holding a number (`0x80002d98`, `sp` lowered by 48, `s0` the
node `b`, `s1` the next pointer `w`): `dc_free_num` through the node's slot,
then `cs_tail`. -/
theorem cs_num {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk} {w : BitVec 64} {p sp : Nat}
    (h : DcAt S (stkV w M) H F L C G (.num p :: hs) st) (hfb : DcFresh H F L G b)
    (hsz : 32 ≤ b.sz) (hw : ldv .ld M (b.pay + 8) = BitVec.ofNat 64 p)
    (harr : ldv .ld M (b.pay + 16) = 0#64) (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48))
    (h8 : R 8 = BitVec.ofNat 64 b.pay) (h9 : R 9 = w)
    (hk : ∀ R' M' H' F' L' C' G', Keeps csNodeClob R' R → SameNodes G G' →
      DcAt S (stkV w M') H' F' L' C' G' hs st → StkOut (sp - 48) 32 M' M → StrPin G.strs G'.strs hs →
      DW live S Q (if w = 0#64 then 0x80002d74#64 else 0x80002d38#64) R' M') :
    DW live S Q 0x80002d98#64 R M := by
  have hpd := pend_stk G w
  have hi := (h.machHeap hpd).heap
  have hS : HeapOwn S := fun a e1 e2 => hi.own a e1 e2
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨hq, hqb⟩ := node_slot hi hS hfb.live (o := 8) (by omega) (by decide)
  have hbb := blk_bounds hi hfb.live
  simp only [heapEnd, heapStart] at hab hbb
  bc_run hlive hS [h2, h8] at 0x80002ba0
  refine dc_free_num_specP hlive hpd h (q := b.pay + 8) hq (.fresh b hfb hqb) hw
    (StackFrame.sub (m := 48) (n := 32) hsf (by decide)) (by simp only [heapEnd]; omega)
    (Or.inl (by omega)) _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    fun R1 M3 H' F' L' C' hk1 h3 _ hfr hfc _ => ?_
  have q8 : R1 8 = BitVec.ofNat 64 b.pay := by rw [hk1.get 8]; bsimp [h8]
  have q9 : R1 9 = w := by rw [hk1.get 9]; bsimp [h9]
  have harr3 : ldv .ld M3 (b.pay + 16) = 0#64 := by
    rw [ldv_congr .ld fun j hj => (hfc b hfb).2 _
      (by simp only [Blk.In, Blk.pay, Blk.fin, widthOfM] at hj hbb ⊢; omega)
      (fun hs' => by simp only [slotBytes, widthOfM] at hs' hj; omega)]
    exact harr
  show DW live S Q 0x80002da0#64 R1 M3
  bc_run hlive hS [] at 0x80002d24
  refine cs_tail hlive h3 (hfc b hfb).1 hsz harr3 (.inl rfl) R1 q8 q9 fun R2 M4 H4 hk2 h4 hfr4 => ?_
  refine hk R2 M4 H4 F' L' C' G ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
    (by keeps_tac Keeps.refl _ _)))) ⟨rfl, rfl, rfl⟩ h4 (fun a ho hg hf => (hfr4 a ho).trans
      (hfr a ho hg hf fun hs' => ho.1 (live_in_heap hi hfb.live (hqb a hs')))) (StrPin.refl _ _)

/-- A node holding a string (`0x80002d58`): `dc_free_str` through the node's
slot, then `cs_tail`. -/
theorem cs_str {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk} {w : BitVec 64} {p sp : Nat}
    (h : DcAt S (stkV w M) H F L C G (.str p :: hs) st) (hfb : DcFresh H F L G b)
    (hsz : 32 ≤ b.sz) (hw : ldv .ld M (b.pay + 8) = BitVec.ofNat 64 p)
    (harr : ldv .ld M (b.pay + 16) = 0#64) (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48))
    (h8 : R 8 = BitVec.ofNat 64 b.pay) (h9 : R 9 = w)
    (hk : ∀ R' M' H' F' L' C' G', Keeps csNodeClob R' R → SameNodes G G' →
      DcAt S (stkV w M') H' F' L' C' G' hs st → StkOut (sp - 48) 32 M' M → StrPin G.strs G'.strs hs →
      DW live S Q (if w = 0#64 then 0x80002d74#64 else 0x80002d38#64) R' M') :
    DW live S Q 0x80002d58#64 R M := by
  have hpd := pend_stk G w
  have hi := (h.machHeap hpd).heap
  have hS : HeapOwn S := fun a e1 e2 => hi.own a e1 e2
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨hq, -⟩ := node_slot hi hS hfb.live (o := 8) (by omega) (by decide)
  have hbb := blk_bounds hi hfb.live
  simp only [heapEnd, heapStart] at hab hbb
  bc_run hlive hS [h2, h8] at 0x800039a4
  refine dc_free_str_specP hlive hpd h (q := b.pay + 8) hq hw
    (StackFrame.sub (m := 48) (n := 32) hsf (by decide)) (by simp only [heapEnd]; omega)
    _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    fun R1 M3 H' G' hk1 hsn h3 hfr hfc _ hpin => ?_
  have q8 : R1 8 = BitVec.ofNat 64 b.pay := by rw [hk1.get 8]; bsimp [h8]
  have q9 : R1 9 = w := by rw [hk1.get 9]; bsimp [h9]
  have harr3 : ldv .ld M3 (b.pay + 16) = 0#64 := by
    rw [ldv_congr .ld fun j hj => (hfc b hfb).2 _
      (by simp only [Blk.In, Blk.pay, Blk.fin, widthOfM] at hj hbb ⊢; omega)]
    exact harr
  show DW live S Q 0x80002d60#64 R1 M3
  refine cs_tail hlive h3 (hfc b hfb).1 hsz harr3 (.inr rfl) R1 q8 q9 fun R2 M4 H4 hk2 h4 hfr4 => ?_
  refine hk R2 M4 H4 F L C G' ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
    (by keeps_tac Keeps.refl _ _)))) hsn h4 (fun a ho hg hf => (hfr4 a ho).trans (hfr a ho hg hf)) hpin

/-- The type test of a node (`0x80002d38`, `s1` the node `b` with type word
`tg`): `s0 = b`, `s1` the link, then the number or the string branch. -/
theorem cs_disp {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {b : Blk} {tg : Nat}
    {link : BitVec 64} (hlo : heapStart + 16 ≤ b.pay) (hhi : b.pay + 32 ≤ heapEnd)
    (htg : tg = 1 ∨ tg = 2) (hlw : ldv .lw M b.pay = BitVec.ofNat 64 tg)
    (hl : ldv .ld M (b.pay + 24) = link)
    (R : Nat → BitVec 64) (h9 : R 9 = BitVec.ofNat 64 b.pay) (h18 : R 18 = 1#64)
    (h19 : R 19 = 2#64)
    (hk : ∀ R', Keeps [8, 9, 10, 11, 15] R' R → R' 8 = BitVec.ofNat 64 b.pay → R' 9 = link →
      DW live S Q (if tg = 1 then 0x80002d98#64 else 0x80002d58#64) R' M) :
    DW live S Q 0x80002d38#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapStart, heapEnd] at hlo hhi
  rcases htg with rfl | rfl
  · bc_run hlive hS [h9, h18, h19, hlw, hl] at 0x80002d98
    all_goals first | (intro hc; exact absurd hc (by decide)) | skip
    all_goals try intro _
    exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp [h9]) (by bsimp [])
  · bc_run hlive hS [h9, h18, h19, hlw, hl] at 0x80002d58
    all_goals first | (intro hc; exact absurd hc (by decide)) | skip
    all_goals try intro _
    all_goals try (bc_run hlive hS [h9, h18, h19, hlw, hl] at 0x80002d58)
    all_goals first | (intro hc; exact absurd hc (by decide)) | skip
    all_goals try intro _
    all_goals exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp [h9]) (by bsimp [])

/-- The registers the loop of `dc_clear_stack` may change. -/
abbrev csClob : List Nat := [1, 8, 9, 10, 11, 13, 14, 15]

/-- **One node of `dc_clear_stack`** (`0x80002d38`, `sp` lowered by 48, `s1`
the top node of the view, `s2 = 1`, `s3 = 2`): the node popped in the view,
its datum freed by its type, the node freed, `s1` the next pointer. -/
theorem cs_body {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk} {g : GV}
    {rest : List (Blk × GV)} {w : BitVec 64} {sp : Nat}
    (h : DcAt S (stkV w M) H F L C G hs st) (he : G.stk = (b, g) :: rest)
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h9 : R 9 = w)
    (h18 : R 18 = 1#64) (h19 : R 19 = 2#64)
    (hk : ∀ R' M' H' F' L' C' G', Keeps csClob R' R → R' 9 = ldv .ld M (b.pay + 24) →
      SameNodes { G with stk := rest } G' →
      DcAt S (stkV (ldv .ld M (b.pay + 24)) M') H' F' L' C' G' hs { st with stack := st.stack.tail } →
      StkOut (sp - 48) 32 M' M → StrPin G.strs G'.strs hs →
      DW live S Q (if ldv .ld M (b.pay + 24) = 0#64 then 0x80002d74#64 else 0x80002d38#64) R' M') :
    DW live S Q 0x80002d38#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hv := h.view.stk
  rw [he] at hv
  cases hv with
  | cons h0 hn _ =>
  have ew : w = BitVec.ofNat 64 b.pay := by rw [← h0]; exact (ldv_store_hit _ _ _).symm
  obtain ⟨h1, hfb, hsn⟩ := h.popTop he
  have hi := (h.machHeap (pend_stk G w)).heap
  have hS : HeapOwn S := fun a e1 e2 => hi.own a e1 e2
  have hbb := blk_bounds hi hfb.live
  have hsz := hsn.sz
  simp only [heapEnd, heapStart] at hab hbb
  have hoff : ∀ x, b.pay ≤ x → x < b.pay + 32 → imgM M x = imgM (stkV w M) x := fun x e1 e2 =>
    (imgM_store_miss _ _ (by simp only [dc_addrs]; omega)).symm
  have hdat : DatAt M b.pay g := hsn.dat.congr16 fun x e1 e2 => hoff x e1 (by omega)
  have harr : ldv .ld M (b.pay + 16) = 0#64 := by
    rw [ldv_congr .ld fun j hj => hoff _ (by omega) (by simp only [widthOfM] at hj; omega)]
    exact hsn.arr
  generalize hl : ldv .ld M (b.pay + 24) = link at hk
  have hl' : ldv .ld (stkV w M) (b.pay + 24) = link := by
    rw [ldv_ld_miss _ _ (by simp only [dc_addrs]; omega)]; exact hl
  rw [hl'] at h1
  have h1' := h1.congr fun x => (stkV_stkV link w M x).symm
  have hlw := hdat.lw
  have hptr := hdat.ptr
  have q9 : R 9 = BitVec.ofNat 64 b.pay := by rw [h9, ew]
  have hh2 : R 2 = BitVec.ofNat 64 (sp - 48) := h2
  cases g with
  | num p =>
    simp only [GV.tag, GV.ptr] at hlw hptr
    refine cs_disp hlive hS (tg := 1) (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
      (.inl rfl) hlw hl R q9 h18 h19 fun R1 hk1 r8 r9 => ?_
    have r2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2 (by decide)]; exact hh2
    refine cs_num hlive h1' hfb hsz hptr harr hsf (by simp only [heapEnd]; omega) R1 r2 r8 r9
      fun R' M' H' F' L' C' G' hk2 hsn' h' hfr hpin => ?_
    exact hk R' M' H' F' L' C' G' ((hk2.mono (by decide)).trans (hk1.mono (by decide)))
      (by rw [hk2.get 9 (by decide)]; exact r9) ⟨hsn'.stk, hsn'.regs, hsn'.lbuf⟩ h' hfr hpin
  | str p =>
    simp only [GV.tag, GV.ptr] at hlw hptr
    refine cs_disp hlive hS (tg := 2) (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
      (.inr rfl) hlw hl R q9 h18 h19 fun R1 hk1 r8 r9 => ?_
    have r2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2 (by decide)]; exact hh2
    refine cs_str hlive h1' hfb hsz hptr harr hsf (by simp only [heapEnd]; omega) R1 r2 r8 r9
      fun R' M' H' F' L' C' G' hk2 hsn' h' hfr hpin => ?_
    exact hk R' M' H' F' L' C' G' ((hk2.mono (by decide)).trans (hk1.mono (by decide)))
      (by rw [hk2.get 9 (by decide)]; exact r9) ⟨hsn'.stk, hsn'.regs, hsn'.lbuf⟩ h' hfr hpin

/-- Frames compose. -/
theorem StkOut.trans {sp W : Nat} {M2 M1 M0 : Mem} (h2 : StkOut sp W M2 M1) (h1 : StkOut sp W M1 M0) :
    StkOut sp W M2 M0 := fun a ho hg hf => (h2 a ho hg hf).trans (h1 a ho hg hf)

/-- **The loop of `dc_clear_stack`** (`0x80002d38`) over a nonempty stack in
the view: every node and datum freed, `s1` `NULL` at `0x80002d74`. -/
theorem cs_loop {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {hs : List GV} {sp : Nat}
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp) :
    ∀ (rest : List (Blk × GV)) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
      {C : BcConsts} {G : DcG} {st : St} {b : Blk} {g : GV} {w : BitVec 64}
      (_ : DcAt S (stkV w M) H F L C G hs st) (_ : G.stk = (b, g) :: rest)
      (R : Nat → BitVec 64) (_ : R 2 = BitVec.ofNat 64 (sp - 48)) (_ : R 9 = w)
      (_ : R 18 = 1#64) (_ : R 19 = 2#64)
      (_ : ∀ R' M' H' F' L' C' G', Keeps csClob R' R → SameNodes { G with stk := [] } G' →
        DcAt S (stkV 0#64 M') H' F' L' C' G' hs { st with stack := [] } →
        StkOut (sp - 48) 32 M' M → StrPin G.strs G'.strs hs → DW live S Q 0x80002d74#64 R' M'),
      DW live S Q 0x80002d38#64 R M
  | rest, M, H, F, L, C, G, st, b, g, w, h, he, R, h2, h9, h18, h19, hk => by
    refine cs_body hlive h he hsf hab R h2 h9 h18 h19
      fun R' M' H' F' L' C' G' hk1 e9 hsn h' hfr hpin => ?_
    have k18 : R' 18 = 1#64 := by rw [hk1.get 18 (by decide)]; exact h18
    have k19 : R' 19 = 2#64 := by rw [hk1.get 19 (by decide)]; exact h19
    have k2 : R' 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2 (by decide)]; exact h2
    have hst : G'.stk = rest := hsn.stk
    have hv := h'.view.stk
    rw [hst] at hv
    match rest, hv, hst with
    | [], hv, hst =>
      cases hv with
      | nil h0 =>
      have hz : ldv .ld M (b.pay + 24) = 0#64 := by rw [← h0]; exact (ldv_store_hit _ _ _).symm
      simp only [hz, ↓reduceIte]
      rw [hz] at h'
      have key : ∀ (P : Blk × GV → Val → Prop) l, List.Forall₂ P [] l → l = [] := fun P l hl => by
        cases hl; rfl
      have hd := h'.den.stk
      rw [hst] at hd
      have et : st.stack.tail = [] := key _ _ hd
      rw [et] at h'
      exact hk R' M' H' F' L' C' G' hk1 ⟨hst, hsn.regs, hsn.lbuf⟩ h' hfr hpin
    | (b', g') :: rest', hv, hst =>
      cases hv with
      | cons h0 _ _ =>
      have e1 : ldv .ld M (b.pay + 24) = BitVec.ofNat 64 b'.pay := by
        rw [← h0]; exact (ldv_store_hit _ _ _).symm
      have hb' : b' ∈ G'.blocks := by
        rw [DcG.blocks, hst]; exact List.mem_append_left _ (List.mem_cons_self)
      have hnz : ldv .ld M (b.pay + 24) ≠ 0#64 :=
        e1 ▸ blk_ptr_ne h'.heap.heap (h'.heap.raw.live b' hb')
      simp only [hnz, ↓reduceIte]
      refine cs_loop hlive hsf hab rest' h' hst R' k2 e9 k18 k19
        fun R'' M'' H'' F'' L'' C'' G'' hk2 hsn2 h'' hfr2 hpin2 => ?_
      exact hk R'' M'' H'' F'' L'' C'' G'' (hk2.trans hk1)
        ⟨hsn2.stk, hsn2.regs.trans hsn.regs, hsn2.lbuf.trans hsn.lbuf⟩ h'' (hfr2.trans hfr)
        (hpin.trans hpin2)

/-- `dc_clear_stack`'s exit (`0x80002d74`, `sp` lowered by 48): the saved
registers back, `dc_stack = NULL`. -/
theorem cs_epi {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) (hG : ∀ a, DcGlob a → S a) {M : Mem}
    {sp : Nat} (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp) {s0 s1 s2 s3 ra : BitVec 64}
    (hal : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48))
    (f8 : ldv .ld M (sp - 48 + 8) = s3) (f16 : ldv .ld M (sp - 48 + 16) = s2)
    (f24 : ldv .ld M (sp - 48 + 24) = s1) (f32 : ldv .ld M (sp - 48 + 32) = s0)
    (f40 : ldv .ld M (sp - 48 + 40) = ra)
    (hk : ∀ R', Keeps [1, 2, 8, 9, 15, 18, 19] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 9 = s1 → R' 18 = s2 → R' 19 = s3 → DW live S Q ra R' (stkV 0#64 M)) :
    DW live S Q 0x80002d74#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h2, f8, f16, f24, f32, f40]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  rw [ldv_ld_miss _ _ (by omega), f24]
  exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (show BitVec.ofNat 64 (sp - 48 + 48) = _ by
    congr 1; omega) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])

/-- The registers `dc_clear_stack` changes. -/
abbrev clearClob : List Nat := [1, 10, 11, 13, 14, 15]

/-- **`dc_clear_stack ()`** at `0x80002cf0`: every node of the stack and its
datum's reference released, `dc_stack = NULL`, the model's `stack := []`. -/
theorem dc_clear_stack_spec {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat} (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps clearClob R' R → R' 2 = R 2 →
      SameNodes { G with stk := [] } G' → DcAt S M' H' F' L' C' G' hs { st with stack := [] } →
      StkOut sp 80 M' M → StrPin G.strs G'.strs hs → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80002cf0#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hG := h.glob
  have hM2 : MemOnly (frameIn sp 48) (writeLog (writeLog M [(sp - 48 + 24, 8, R 9)])
      [(sp - 48 + 40, 8, R 1)]) M := fun a ha => by
    simp only [frameIn] at ha; rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hP : ∀ n, n ≤ 80 → ∀ a, frameIn sp n a → OutHeap a ∧ ¬ DcGlob a := fun n hn a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have h1 := h.outWrite hM2 (hP 48 (by omega))
  have hv := h.view.stk
  have run0 : ∀ {P : Prop}, (P → DWO live S Q t 0x80002cf0#64 R M) → P → DWO live S Q t 0x80002cf0#64 R M :=
    fun f p => f p
  rcases hst : G.stk with _ | ⟨⟨b, g⟩, rest⟩
  · rw [hst] at hv
    cases hv with
    | nil h0 =>
    bc_run hlive hS [h2, word_sub48 (show 48 ≤ sp by omega)]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals rw [show ldv .ld (writeLog M [(sp - 48 + 24, 8, R 9)]) 2147601816 = ldv .ld M dcStackAddr
      from ldv_ld_miss _ _ (by omega)]
    all_goals first | (intro hc; exact absurd h0 hc) | skip
    intro _
    have g24 : ldv .ld (writeLog (writeLog M [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)])
        (sp - 48 + 24) = R 9 := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    have g40 : ldv .ld (writeLog (writeLog M [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)])
        (sp - 48 + 40) = R 1 := ldv_store_hit _ _ _
    have gdc : ldv .ld (writeLog (writeLog M [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)])
        dcStackAddr = 0#64 := by
      rw [ldv_ld_miss _ _ (by simp only [dc_addrs]; omega), ldv_ld_miss _ _ (by simp only [dc_addrs]; omega)]
      exact h0
    generalize writeLog (writeLog M [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)] = M2
      at h1 g24 g40 gdc hM2 ⊢
    bc_run hlive hS [g40]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
    rw [g24]
    have key : ∀ (P : Blk × GV → Val → Prop) l, List.Forall₂ P [] l → l = [] := fun P l hl => by
      cases hl; rfl
    have hd := h.den.stk
    rw [hst] at hd
    have e0 : st.stack = [] := key _ _ hd
    have est : ({ st with stack := [] } : St) = st := by rw [← e0]
    have h1' : DcAt S (writeLog M2 [(dcStackAddr, 8, 0#64)]) H F L C G hs { st with stack := [] } := by
      rw [est]; exact h1.congr fun x => imgM_store_self M2 gdc x
    refine hk _ _ H F L C G
      (Keeps.restore (by rw [h2]; congr 1; omega) (Keeps.restore rfl (by keeps_tac Keeps.refl _ _)))
      (show BitVec.ofNat 64 (sp - 48 + 48) = R 2 by rw [h2]; congr 1; omega) ⟨hst, rfl, rfl⟩ h1'
      (fun a ho hg hf => ?_) (StrPin.refl _ _)
    rw [imgM_store_miss _ _ (Classical.byContradiction fun hc => hg (by simp only [DcGlob, dc_addrs]; omega))]
    exact hM2 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
  · rw [hst] at hv
    cases hv with
    | cons h0 _ _ =>
    have hbG : b ∈ G.blocks := by rw [DcG.blocks, hst]; exact List.mem_append_left _ List.mem_cons_self
    have hnz := blk_ptr_ne h.heap.heap (h.heap.raw.live b hbG)
    bc_run hlive hS [h2, word_sub48 (show 48 ≤ sp by omega)]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals rw [show ldv .ld (writeLog M [(sp - 48 + 24, 8, R 9)]) 2147601816 = ldv .ld M dcStackAddr
      from ldv_ld_miss _ _ (by omega)]
    all_goals first | (intro hc; exact absurd (h0.symm.trans hc) hnz) | skip
    intro _
    have g24 : ldv .ld (writeLog (writeLog M [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)])
        (sp - 48 + 24) = R 9 := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    have g40 : ldv .ld (writeLog (writeLog M [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)])
        (sp - 48 + 40) = R 1 := ldv_store_hit _ _ _
    have gdc : ldv .ld (writeLog (writeLog M [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)])
        dcStackAddr = BitVec.ofNat 64 b.pay := by
      rw [ldv_ld_miss _ _ (by simp only [dc_addrs]; omega), ldv_ld_miss _ _ (by simp only [dc_addrs]; omega)]
      exact h0
    generalize writeLog (writeLog M [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)] = M2
      at h1 g24 g40 gdc hM2 ⊢
    rw [h0]
    bc_run hlive hS [] at 0x80002d38
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hM3 : MemOnly (frameIn sp 48) (writeLog (writeLog (writeLog M2 [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 19)]) [(sp - 48 + 32, 8, R 8)]) M2 := fun a ha => by
      simp only [frameIn] at ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
    have h3 := h1.outWrite hM3 (hP 48 (by omega))
    have m3dc : ldv .ld (writeLog (writeLog (writeLog M2 [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 19)]) [(sp - 48 + 32, 8, R 8)]) dcStackAddr = BitVec.ofNat 64 b.pay := by
      rw [ldv_ld_miss _ _ (by simp only [dc_addrs]; omega), ldv_ld_miss _ _ (by simp only [dc_addrs]; omega),
        ldv_ld_miss _ _ (by simp only [dc_addrs]; omega)]
      exact gdc
    have m8 : ldv .ld (writeLog (writeLog (writeLog M2 [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 19)]) [(sp - 48 + 32, 8, R 8)]) (sp - 48 + 8) = R 19 := by
      rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    have m16 : ldv .ld (writeLog (writeLog (writeLog M2 [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 19)]) [(sp - 48 + 32, 8, R 8)]) (sp - 48 + 16) = R 18 := by
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
    have m24 : ldv .ld (writeLog (writeLog (writeLog M2 [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 19)]) [(sp - 48 + 32, 8, R 8)]) (sp - 48 + 24) = R 9 := by
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact g24
    have m32 : ldv .ld (writeLog (writeLog (writeLog M2 [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 19)]) [(sp - 48 + 32, 8, R 8)]) (sp - 48 + 32) = R 8 := ldv_store_hit _ _ _
    have m40 : ldv .ld (writeLog (writeLog (writeLog M2 [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 19)]) [(sp - 48 + 32, 8, R 8)]) (sp - 48 + 40) = R 1 := by
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact g40
    generalize (writeLog (writeLog (writeLog M2 [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 19)]) [(sp - 48 + 32, 8, R 8)]) = M3 at h3 m3dc m8 m16 m24 m32 m40 hM3 ⊢
    have hV := h3.congr fun x => imgM_store_self M3 m3dc x
    refine cs_loop hlive hsf hab rest hV hst _ (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
      fun R' M' H' F' L' C' G' hk1 hsn h' hfr hpin => ?_
    have hT : ∀ a, sp - 48 ≤ a → a + 8 ≤ sp → ldv .ld M' a = ldv .ld M3 a := fun a e1 e2 =>
      ldv_congr .ld fun j hj =>
        hfr _ (hP 48 (by omega) _ (by simp only [frameIn, widthOfM] at hj ⊢; omega)).1
          (hP 48 (by omega) _ (by simp only [frameIn, widthOfM] at hj ⊢; omega)).2
          (fun hf => by simp only [frameIn, widthOfM] at hf hj; omega)
    have r2 : R' 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2 (by decide)]; bsimp []
    refine cs_epi hlive hS hG hsf hab hal R' r2 ((hT _ (by omega) (by omega)).trans m8)
      ((hT _ (by omega) (by omega)).trans m16) ((hT _ (by omega) (by omega)).trans m24)
      ((hT _ (by omega) (by omega)).trans m32) ((hT _ (by omega) (by omega)).trans m40)
      fun R'' hk2 e1 e2 e8 e9 e18 e19 => ?_
    refine hk R'' (stkV 0#64 M') H' F' L' C' G' (Keeps.restoreAll (rs := [2, 8, 9, 18, 19])
      ((hk2.mono (by decide)).trans ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) ?_)
      (e2.trans h2.symm) hsn h' (fun a ho hg hf => ?_) hpin
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact e2.trans h2.symm
      · exact e8
      · exact e9
      · exact e18
      · exact e19
    · rw [imgM_store_miss _ _ (Classical.byContradiction fun hc => hg (by
          simp only [DcGlob, dc_addrs] at hc ⊢; omega)),
        hfr a ho hg (fun h' => hf (by simp only [frameIn, Nat.sub_sub] at h' ⊢; omega)),
        hM3 a (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
      exact hM2 a fun h' => hf (by simp only [frameIn] at h' ⊢; omega)

end Dc.Mach
