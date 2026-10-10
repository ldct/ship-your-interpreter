import Dc.Mach.DcPrint
import Dc.Mach.DcRotate

/-!
# `dc_printall` (M9)

    dc_printall (obase):
      for (n = dc_stack; n; n = n->link)
        dc_print (n->value, obase, DC_WITHNL, DC_KEEP);

- `pa_loop`: the walk from a node of the stack, each value printed in place.
- `dc_printall_spec`: the console extended by every stack value's
  `Val.out 70 ob` and a newline, the state unchanged up to `SameNodes`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The value related to the element after the prefix `pre`. -/
theorem forall2_at {α β : Type} {r : α → β → Prop} :
    ∀ {pre rest : List α} {x : α} {l : List β}, List.Forall₂ r (pre ++ x :: rest) l →
      ∃ v, r x v ∧ l.drop pre.length = v :: l.drop (pre.length + 1)
  | [], _, _, _, h => by
    cases h with
    | cons hr _ => exact ⟨_, hr, rfl⟩
  | _ :: pre, _, _, _, h => by
    cases h with
    | cons _ ht =>
      obtain ⟨v, hv, e⟩ := forall2_at (pre := pre) ht
      exact ⟨v, hv, by simpa using e⟩

theorem SameNodes.trans {G G' G'' : DcG} (h1 : SameNodes G G') (h2 : SameNodes G' G'') :
    SameNodes G G'' := ⟨h2.stk.trans h1.stk, h2.regs.trans h1.regs, h2.lbuf.trans h1.lbuf⟩

/-- The text `dc_printall` sends for the values `l`. -/
def paOut (ob : Nat) (l : List Val) : List Nat := l.flatMap fun v => Dc.Val.out 70 ob v ++ [10]

/-- The link word of a stack node after the prefix `pre`. -/
theorem DcAt.stkLink {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {pre rest : List (Blk × GV)} {b : Blk} {g : GV} (hst : G.stk = pre ++ (b, g) :: rest) :
    ldv .ld M (b.pay + 24) = headPtr rest := by
  have hseg := h.view.stk.toSeg
  rw [hst] at hseg
  obtain ⟨q, -, h2⟩ := PSeg.split hseg
  exact h2.uncons.2.head

/-- `dc_printall`'s loop (`0x800038c4`, `s0` the node `b` after the nodes
`pre`, `s1` the base, `sp` lowered by 32). -/
theorem pa_loop {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {st : St} {hs : List GV} {ob sp : Nat} {M0 : Mem} {G0 : DcG}
    (hhs : hs.length ≤ 2 ^ 20) (hw : ∀ v ∈ st.stack, ∀ n, v = .num n → n.wid < 2 ^ 20)
    (hob2 : 2 ≤ ob) (hob : ob < 2 ^ 31) (herr : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a)
    (hsf : StackFrame S sp prN) (hab : heapEnd + prN ≤ sp)
    (hoom : ∀ t' R' M' sp', OomAt S sp prN M0 ocG sp' R' M' → DWO live S Q t' 0x80001e74#64 R' M') :
    ∀ (rest pre : List (Blk × GV)) {b : Blk} {g : GV} {t : String} {M : Mem} {H : Heap} {F : List Blk}
      {L : List NumObj} {C : BcConsts} {G : DcG} (R : Nat → BitVec 64),
    DcAt S M H F L C G hs st → G.stk = pre ++ (b, g) :: rest → SameNodes G0 G → StrPin G0.strs G.strs hs →
    MulBase S M →
    (∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp prN a → imgM M a = imgM M0 a) →
    R 2 = BitVec.ofNat 64 sp → R 8 = BitVec.ofNat 64 b.pay → R 9 = BitVec.ofNat 64 ob →
    (∀ R' M' H' F' L' C' G', Keeps (8 :: cClob) R' R → R' 2 = R 2 → SameNodes G0 G' →
      DcAt S M' H' F' L' C' G' hs st → StrPin G0.strs G'.strs hs →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp prN a → imgM M' a = imgM M0 a) →
      DWO live S Q (t ++ Dc.outStr (paOut ob (st.stack.drop pre.length))) 0x800038e4#64 R' M') →
    DWO live S Q t 0x800038c4#64 R M := by
  intro rest
  induction rest with
  | nil => ?_
  | cons y rest ih => ?_
  all_goals
    intro pre b g t M H F L C G R h hst hsn hpin hmb hfr h2 h8 h9 hk
    have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
    have hNW : prN = 48 + (32 + (176 + 512 + rmStack (2 ^ 30) + 48)) := rfl
    have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
    have hab' := hab
    rw [hNW] at hab'
    simp only [heapEnd] at hab'
    have htx : tohostAddr = 0x8001ad00 := rfl
    have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
    have geo := h.stkGeo
    obtain ⟨hb1, hb2, hb3⟩ := geo.bnd (b, g) (by rw [hst]; exact List.mem_append_right _ List.mem_cons_self)
    simp only [heapStart, heapEnd] at hb1 hb2
    have hnd : SNodeAt M b g := h.view.stk.forall (b, g) (by rw [hst]; exact List.mem_append_right _ List.mem_cons_self)
    have d0 := hnd.dat.tag
    have d8 := hnd.dat.ptr
    obtain ⟨v, hv, hdrop⟩ := forall2_at (hst ▸ h.den.stk)
    bc_run hlive hS [h2, h8, h9, d8] at 0x8000200c
    have hvm : v ∈ st.stack := List.mem_of_mem_drop (by rw [hdrop]; exact List.mem_cons_self)
    refine dc_print_spec hlive (keep := true) (nl := true) (ob := ob) (sp := sp) h
      (fun e => absurd e (by decide)) hv hhs (hw v hvm) hmb hob2 hob herr hsf hab _ ?q2 ?q10 ?q11 ?q12
      ?q13 ?q14 ?qal (fun R' M' H' F' L' C' G' hk' e2 hsn' hD hfr' hpin' => ?_)
      fun t' R' M' sp' ho => hoom t' R' M' sp' ⟨ho.lo, ho.hi, ho.r2, fun a e1 e2 e3 e4 =>
        (ho.out a e1 e2 e3 e4).trans (hfr a e1 e2 e4 e3)⟩
    case q2 => bsimp [h2]
    case q10 => bsimp []; exact d0
    case q11 => bsimp []
    case q12 => bsimp []
    case q13 => bsimp []
    case q14 => bsimp []
    case qal => bsimp []
    have hD' : DcAt S M' H' F' L' C' G' hs st := hD
    have hst' : G'.stk = _ := hsn'.stk.trans hst
    have hl := hD'.stkLink hst'
    have q8 : R' 8 = BitVec.ofNat 64 b.pay := by rw [hk'.get 8 (by decide)]; bsimp [h8]
    have q2 : R' 2 = BitVec.ofNat 64 sp := by rw [e2]; bsimp [h2]
    have q9 : R' 9 = BitVec.ofNat 64 ob := by rw [hk'.get 9 (by decide)]; bsimp [h9]
    have hS' : HeapOwn S := fun a e1 e2 => hD'.heap.heap.own a e1 e2
    have hmb' : MulBase S M' := hmb.transport fun a e1 e2 => by
      have ho := mulBase_off e1 e2
      refine hfr' a ho.1 ho.2.1 (fun hg => ?_) (fun hf => ?_)
      · simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr, mulBaseAddr] at hg e1 e2; omega
      · have := ho.2.2; have h' := hab; simp only [frameIn, heapStart] at hf this; simp only [heapEnd] at h'; omega
    have hfr2 : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp prN a → imgM M' a = imgM M0 a :=
      fun a e1 e2 e3 e4 => (hfr' a e1 e2 e3 e4).trans (hfr a e1 e2 e3 e4)
    have hsn2 := hsn.trans hsn'
    have hpin2 : StrPin G0.strs G'.strs hs := hpin.trans hpin'
    have hlen := hD'.den.stk.length_eq
    rw [hst'] at hlen
    rw [show nlBytes true = [10] from rfl]
    clear hfr' hmb hfr hD h hsn hsn' hpin hpin'
    bsimp []
  · -- the last node
    simp only [headPtr] at hl
    bc_run hlive hS' [q8, q2, hl] at 0x800038e4
    have ho : Dc.Val.out 70 ob v ++ [10] = paOut ob (st.stack.drop pre.length) := by
      rw [hdrop, List.drop_eq_nil_of_le (by simp at hlen; omega)]; simp [paOut]
    rw [ho]
    refine hk _ M' H' F' L' C' G' ?_ ?_ hsn2 hD' hpin2 hfr2
    · exact by keeps_tac ((hk'.mono (ks' := 8 :: cClob) (by decide)).trans
        (show Keeps (8 :: cClob) _ R by keeps_tac Keeps.refl _ _))
    · bsimp [e2]
  · -- around the loop
    obtain ⟨b', g'⟩ := y
    simp only [headPtr] at hl
    have geo' := hD'.stkGeo
    obtain ⟨hb1', hb2', -⟩ := geo'.bnd (b', g') (by
      rw [hst']; exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
    simp only [heapStart, heapEnd] at hb1' hb2'
    have hnz : BitVec.ofNat 64 b'.pay ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    bc_run hlive hS' [q8, q2, q9, hl] at 0x800038e0
    bc_run hlive hS' [q8, q2, q9, hl]
    all_goals try (intro hc; exact (hc hnz).elim)
    try intro _
    refine ih (pre ++ [(b, g)]) (b := b') (g := g') (t := t ++ Dc.outStr (Dc.Val.out 70 ob v ++ [10])) _ hD'
      (by rw [hst']; simp) hsn2 hpin2 hmb' hfr2 ?r2 ?r8 ?r9
      fun R'' M'' H'' F'' L'' C'' G'' hk'' e2' hsn'' hD'' hpin'' hfr'' => ?_
    case r2 => bsimp [q2]
    case r8 => bsimp [hl]
    case r9 => bsimp [q9]
    have ho : Dc.Val.out 70 ob v ++ [10] ++ paOut ob (st.stack.drop (pre.length + 1)) =
        paOut ob (st.stack.drop pre.length) := by
      rw [hdrop]; simp [paOut]
    rw [List.length_append, List.length_singleton, String.append_assoc, ← outStr_append, ho]
    refine hk R'' M'' H'' F'' L'' C'' G'' (hk''.trans ?_) ?_ hsn'' hD'' hpin'' hfr''
    · exact by keeps_tac ((hk'.mono (ks' := 8 :: cClob) (by decide)).trans
        (show Keeps (8 :: cClob) _ R by keeps_tac Keeps.refl _ _))
    · rw [e2']; bsimp [e2]


/-- `dc_printall`'s epilogue (`0x800038e4`): `s1`, `ra`, `s0` reloaded, the
frame popped, `ret`. -/
theorem pa_epi {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} {s0v s1v ra : BitVec 64}
    (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (f16 : ldv .ld M (sp - 32 + 16) = s0v)
    (f8 : ldv .ld M (sp - 32 + 8) = s1v) (f24 : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 8, 9] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp → R' 8 = s0v →
      R' 9 = s1v → DWO live S Q t ra R' M) :
    DWO live S Q t 0x800038e4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, f16, f8, f24]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) ?_ (by bsimp []) (by bsimp [])
  bsimp []; congr 1; omega

/-- **`dc_printall (obase)`** at `0x800038a4`: the console extended by each
stack value's `Val.out 70 ob` and a newline, top first; the state unchanged
up to `SameNodes` (`out_char`'s bytes, the heap's scratch). -/
theorem dc_printall_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {ob sp : Nat}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 20)
    (hw : ∀ v ∈ st.stack, ∀ n, v = .num n → n.wid < 2 ^ 20) (hmb : MulBase S M)
    (hob2 : 2 ≤ ob) (hob : ob < 2 ^ 31) (herr : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a)
    (hsf : StackFrame S sp (32 + prN)) (hab : heapEnd + (32 + prN) ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 ob)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps cClob R' R → R' 2 = R 2 → SameNodes G G' →
      DcAt S M' H' F' L' C' G' hs st → StrPin G.strs G'.strs hs →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp (32 + prN) a → imgM M' a = imgM M a) →
      DWO live S Q (t ++ Dc.outStr (paOut ob st.stack)) (R 1) R' M')
    (hoom : ∀ t' R' M' sp', OomAt S sp (32 + prN) M ocG sp' R' M' → DWO live S Q t' 0x80001e74#64 R' M') :
    DWO live S Q t 0x800038a4#64 R M := by
  have hNW : prN = 48 + (32 + (176 + 512 + rmStack (2 ^ 30) + 48)) := rfl
  have hsf' := hsf
  have hab0 := hab
  rw [hNW] at hsf' hab0
  have hsl := hsf'.lo; have hsh := hsf'.hi; have hsa := hsf'.al
  simp only [heapEnd] at hab0
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hG := h.glob
  have hch := h.view.stk.toP
  have geo := h.stkGeo
  have g0 : ldv .ld (writeLog M [(sp - 32 + 16, 8, R 8)]) dcStackAddr = ldv .ld M dcStackAddr :=
    ldv_ld_miss _ _ (by simp only [dcStackAddr]; omega)
  bc_run hlive hS [h2, h10, word_sub32 (show 32 ≤ sp by omega)] at 0x800038b8
  all_goals first | exact frame_acc hsf' (by omega) (by omega) | skip
  simp only [dcStackAddr] at g0
  rw [g0]
  have hab2 : heapEnd ≤ sp - 32 := by simp only [heapEnd]; omega
  have hlen := h.den.stk.length_eq
  rcases hstk : G.stk with _ | ⟨⟨b, g⟩, rest⟩
  · rw [hstk] at hch
    have hz := hch.nil_eq
    simp only [dcStackAddr] at hz
    have m16 : ldv .ld (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)])
        (sp - 32 + 16) = R 8 := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    have m24 : ldv .ld (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)])
        (sp - 32 + 24) = R 1 := ldv_store_hit _ _ _
    have hM1 : MemOnly (frameIn sp 32) (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
        [(sp - 32 + 24, 8, R 1)]) M := fun a ha => by
      simp only [frameIn] at ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
    have h1 := h.outWrite hM1 fun a ha =>
      ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
        (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
    generalize writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)] = M1
      at hM1 h1 m16 m24 ⊢
    bc_run hlive hS [hz, m16, m24]
    all_goals first | (intro hc; exact absurd rfl hc) | skip
    try intro _
    bc_run hlive hS [hz, m16, m24]
    all_goals first | exact frame_acc hsf' (by omega) (by omega) | exact hal | skip
    have hnil : st.stack = [] := List.eq_nil_of_length_eq_zero (by rw [← hlen, hstk]; rfl)
    rw [show t = t ++ Dc.outStr (paOut ob st.stack) by rw [hnil]; simp [paOut, Dc.outStr]]
    refine hk _ M1 H F L C G ?_ ?_ ⟨rfl, rfl, rfl⟩ h1 (StrPin.refl _ _) fun a _ _ _ hf =>
      hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
    · refine Keeps.restoreAll (rs := [2, 8]) (show Keeps ([2, 8] ++ cClob) _ R by
        keeps_tac Keeps.refl _ _) fun z hz => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · rw [h2]; bsimp []; congr 1; omega
      · bsimp []
    · rw [h2]; bsimp []; congr 1; omega
  · rw [hstk] at hch
    have he := hch.head_eq
    simp only [dcStackAddr] at he
    obtain ⟨hb1, hb2, -⟩ := geo.bnd (b, g) (by rw [hstk]; exact List.mem_cons_self)
    simp only [heapStart, heapEnd] at hb1 hb2
    have hnz : BitVec.ofNat 64 b.pay ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    bc_run hlive hS [he]
    all_goals first | (intro hc; exact absurd hc hnz) | skip
    try intro _
    bc_run hlive hS [he, h10, word_sub32 (show 32 ≤ sp by omega)] at 0x800038c4
    all_goals first | exact frame_acc hsf' (by omega) (by omega) | skip
    have hM1 : MemOnly (frameIn sp 32) (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
        [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, R 9)]) M := fun a ha => by
      simp only [frameIn] at ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
    have h1 := h.outWrite hM1 fun a ha =>
      ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
        (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
    have hmb1 := hmb.transport (M' := writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
        [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, R 9)]) fun a e1 e2 => hM1 a fun hp => by
      simp only [frameIn, mulBaseAddr] at e1 e2 hp; simp only [heapEnd] at hab2; omega
    have m8 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
        [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, R 9)]) (sp - 32 + 8) = R 9 := ldv_store_hit _ _ _
    have m16 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
        [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, R 9)]) (sp - 32 + 16) = R 8 := by
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
    have m24 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
        [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, R 9)]) (sp - 32 + 24) = R 1 := by
      rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    generalize writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
        [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, R 9)] = M1 at hM1 h1 hmb1 m8 m16 m24 ⊢
    refine pa_loop hlive (sp := sp - 32) (M0 := M1) (G0 := G) hhs hw hob2 hob herr
      (hsf.within (m := 32) (n := prN) (by omega) (by decide)) (by omega)
      (fun t' R' M' sp' ho => hoom t' R' M' sp' ⟨by have := ho.lo; omega, by have := ho.hi; omega, ho.r2,
        fun a e1 e2 e3 e4 => (ho.out a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)) e4).trans
          (hM1 a fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))⟩)
      rest [] (b := b) (g := g) _ h1 (by rw [hstk]; rfl) ⟨rfl, rfl, rfl⟩ (StrPin.refl _ _) hmb1 (fun _ _ _ _ _ => rfl)
      ?r2 ?r8 ?r9 fun R' M' H' F' L' C' G' hk' e2 hsn hD hpin hfr => ?_
    case r2 => bsimp []
    case r8 => bsimp []
    case r9 => bsimp []
    have kf : ∀ o, 8 ≤ o → o < 32 → imgM M' (sp - 32 + o) = imgM M1 (sp - 32 + o) := fun o h8 h32 =>
      hfr _ (above_sp hab2 (by omega)).1 (above_sp hab2 (by omega)).2.1
        (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr]; simp only [heapEnd] at hab2; omega)
        ((above_sp hab2 (by omega)).2.2 _)
    have f8 : ldv .ld M' (sp - 32 + 8) = R 9 := (ldv_congr .ld fun j hj => by
      have := kf (8 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m8
    have f16 : ldv .ld M' (sp - 32 + 16) = R 8 := (ldv_congr .ld fun j hj => by
      have := kf (16 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m16
    have f24 : ldv .ld M' (sp - 32 + 24) = R 1 := (ldv_congr .ld fun j hj => by
      have := kf (24 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m24
    have q2 : R' 2 = BitVec.ofNat 64 (sp - 32) := by rw [e2]; bsimp []
    simp only [List.length_nil, List.drop_zero]
    have hsf32 : StackFrame S sp 32 := by simpa using hsf.within (m := 0) (n := 32) (by omega) (by decide)
    refine pa_epi hlive hsf32 (by omega) _ q2 f16 f8 f24 hal fun R'' hk'' e1 e2' e8 e9 => ?_
    refine hk _ M' H' F' L' C' G' ?_ ?_ hsn hD hpin fun a e1 e2 e3 e4 =>
      (hfr a e1 e2 e3 fun hf => e4 (by simp only [frameIn] at hf ⊢; omega)).trans
        (hM1 a fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))
    · refine Keeps.restoreAll (rs := [2, 8, 9]) ((hk''.mono (ks' := [2, 8, 9] ++ cClob) (by decide)).trans
        (by keeps_tac ((hk'.mono (ks' := [2, 8, 9] ++ cClob) (by decide)).trans
          (show Keeps ([2, 8, 9] ++ cClob) _ R by keeps_tac Keeps.refl _ _)))) fun z hz => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · rw [e2', h2]
      · exact e8
      · exact e9
    · rw [e2', h2]

end Dc.Mach
