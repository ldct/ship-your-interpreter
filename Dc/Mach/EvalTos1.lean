import Dc.Mach.EvalSkip

/-!
# `DC_EVALTOS`'s machine spans (M10)

After the skip (`tos_skip`): `dc_pop (s9)` at the text's end
(`0x8000179c`, `rt_pop_end`) or before another byte (`0x800017d8`,
`rt_pop_mid`); the popped datum's type at `0x800017a8`: a number pushed
back (`rt_tos_num`), a string as the tail call (`rt_tail`) or the nested
evaluation (`rt_tos_str`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t : String} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
  {hs : List GV} {st : St} {sp : Nat}

/-- The datum `dc_pop` moved to the slot `s9 = sp + 32`. -/
def PopK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t : String) (pc : BitVec 64) (sp : Nat) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G : DcG) (hs : List GV) (st : St) (R : Nat → BitVec 64) : Prop :=
  ∀ R2 M2 H2 (G' : DcG) g v st', st = st'.push v → (∃ c, G = { G' with stk := (c, g) :: G'.stk }) →
    Keeps (1 :: 23 :: popClob) R2 R → DcAt S M2 H2 F L C G' (g :: hs) st' → DatAt M2 (sp + 32) g →
    PopOut sp (sp + 32) M2 M → DWO live S Q t pc R2 M2

/-- **`dc_pop (s9)` at the text's end** (`0x8000179c`): the popped datum's
type at `0x800017a8`, or (an empty stack) the exit. -/
theorem rt_pop_end (hlive : ∀ p ∈ dcText, live p.1) (h : DcAt S M H F L C G hs st)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp (sp + 32))
    {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp) (h25 : R 25 = BitVec.ofNat 64 (sp + 32))
    (hpop : PopK live S Q t 0x800017a8#64 sp M H F L C G hs st R)
    (hemp : st.stack = [] → ∀ R2 M2, Keeps (1 :: popClob) R2 R → DcAt S M2 H F L C G hs st →
      PopOut sp (sp + 32) M2 M → DWO live S Q t 0x8000156c#64 R2 M2) :
    DWO live S Q t 0x8000179c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, h25] at 0x8000310c
  refine dc_pop_spec hlive h hsf hab hq _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    (fun R1 M1 H1 G' g v st' hst hG k1 e10 h1 hd hpo => ?_) (fun he R1 M1 k1 e10 h1 hpo => ?_)
  · bsimp []
    bc_run hlive hlive [e10] at 0x800017a8
    all_goals first | (intro hc; exact absurd hc (by decide)) | intro _ | skip
    exact hpop _ M1 H1 G' g v st' hst hG
      (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) h1 hd hpo
  · bsimp []
    bc_run hlive hlive [e10] at 0x8000156c
    all_goals first | (intro hc; exact absurd hc (by decide)) | intro _ | skip
    exact hemp he _ M1 (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      h1 hpo

/-- **`dc_pop (s9)` before another byte** (`0x800017d8`): the type at
`0x800017a8`, or (an empty stack) the loop head with `a2 = 0`. -/
theorem rt_pop_mid (hlive : ∀ p ∈ dcText, live p.1) (h : DcAt S M H F L C G hs st)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp (sp + 32))
    {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp) (h25 : R 25 = BitVec.ofNat 64 (sp + 32))
    (hpop : PopK live S Q t 0x800017a8#64 sp M H F L C G hs st R)
    (hemp : st.stack = [] → ∀ R2 M2, Keeps (1 :: 12 :: popClob) R2 R → R2 12 = 0#64 →
      DcAt S M2 H F L C G hs st → PopOut sp (sp + 32) M2 M → DWO live S Q t 0x800014f8#64 R2 M2) :
    DWO live S Q t 0x800017d8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, h25] at 0x8000310c
  refine dc_pop_spec hlive h hsf hab hq _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    (fun R1 M1 H1 G' g v st' hst hG k1 e10 h1 hd hpo => ?_) (fun he R1 M1 k1 e10 h1 hpo => ?_)
  · bsimp []
    bc_run hlive hlive [e10] at 0x800017a8
    all_goals first | (intro hc; exact absurd hc (by decide)) | intro _ | skip
    bc_run hlive hlive [e10] at 0x800017a8
    exact hpop _ M1 H1 G' g v st' hst hG
      (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) h1 hd hpo
  · bsimp []
    bc_run hlive hlive [e10] at 0x800014f8
    all_goals first | (intro hc; exact absurd hc (by decide)) | intro _ | skip
    exact hemp he _ M1 (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (by bsimp []) h1 hpo

/-- **A number popped** (`0x800017a8`, the slot's type `1`): pushed back,
`a2 = 0`, the test at `0x800017d0`. -/
theorem rt_tos_num (hlive : ∀ p ∈ dcText, live p.1) {g : GV} {v : Val}
    (h : DcAt S M H F L C G (g :: hs) st) (hv : g.Den ⟨L, G.strs⟩ v) (hg : g.tag = 1)
    (hd : DatAt M (sp + 32) g) (hown : ∀ b, sp ≤ b → b < sp + 88 → S b)
    (hsf : StackFrame S sp 64) (hab : heapEnd + 64 ≤ sp)
    {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp)
    (hk : ∀ R2 M2 H2 c, Keeps (1 :: 12 :: 23 :: pushClob) R2 R → R2 12 = 0#64 →
      DcAt S M2 H2 F L C { G with stk := (c, g) :: G.stk } hs (st.push v) → StkOut sp 64 M2 M →
      DWO live S Q t 0x800017d0#64 R2 M2)
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 64) → StkOut sp 64 M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x800017a8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hlw := hd.lw
  rw [hg] at hlw
  have ht := hd.tag; have hpt := hd.ptr
  bc_run hlive hlive [h2, hlw] at 0x80002da4
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | (intro hc; exact absurd hc (by decide)) | intro _ | skip
  bc_run hlive hlive [h2, hlw] at 0x80002da4
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | skip
  refine dc_push_spec hlive h hv hsf hab _ ⟨by bsimp []; exact ht, by bsimp [] at hpt ⊢; exact hpt⟩
    (by bsimp [h2]) (by bsimp []) (fun R1 M1 H1 c k1 h1 hso => ?_) hoom
  bsimp []
  bc_run hlive hlive [] at 0x800017d0
  exact hk _ M1 H1 c (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (by bsimp []) h1 hso

/-- **A string popped** (`0x800017a8`, type `2`): the tail call at the
text's end (`0x800018bc`), else the nested evaluation (`0x800017fc`). -/
theorem rt_tos_str (hlive : ∀ p ∈ dcText, live p.1) {g : GV} (hg : g.tag = 2)
    (hd : DatAt M (sp + 32) g) (hown : ∀ b, sp ≤ b → b < sp + 88 → S b) (hsf : StackFrame S sp 64)
    {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp)
    (htail : ∀ R2, Keeps [15, 23] R2 R → R 8 = R 9 → DWO live S Q t 0x800018bc#64 R2 M)
    (hcall : ∀ R2, Keeps [15, 23] R2 R → R2 23 = 2#64 → R 8 ≠ R 9 → DWO live S Q t 0x800017fc#64 R2 M) :
    DWO live S Q t 0x800017a8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hlw := hd.lw
  rw [hg] at hlw
  bc_run hlive hlive [h2, hlw] at 0x800018bc 0x800017fc
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | (intro hc; exact absurd hc (by decide)) | intro _ | skip
  bc_run hlive hlive [h2, hlw] at 0x800018bc 0x800017fc
  all_goals first | (intro hc; exact absurd hc (by decide)) | intro hc | skip
  · exact htail _ (by keeps_tac Keeps.refl _ _) hc.symm
  · exact hcall _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (fun e => hc e.symm)

/-- The tail call after `dc_free_str` (`0x800018c4`): `*string` the popped
datum `.str p'`, `tail_depth + 1`, the new text and its end, `a2 = 0`. -/
theorem rt_tail2 (hlive : ∀ p ∈ dcText, live p.1) {p' q td : Nat} {hs' : List GV}
    (h : DcAt S M H F L C G hs' st) (hq : DatSlot S (sp + 176) q) (hd : DatAt M (sp + 32) (.str p'))
    (hp' : GV.str p' ∈ hs') (hown : ∀ b, sp ≤ b → b < sp + 88 → S b)
    (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (htd : td + 1 < 2 ^ 31) {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp)
    (h22 : R 22 = BitVec.ofNat 64 q) (h24 : R 24 = BitVec.ofNat 64 td)
    (hk : ∀ R2 M2 o', Keeps (1 :: 8 :: 9 :: 12 :: 24 :: cClob) R2 R → o' ∈ G.strs →
      o'.hb.pay = p' → R2 8 = BitVec.ofNat 64 o'.tb.pay →
      R2 9 = BitVec.ofNat 64 (o'.tb.pay + o'.s.length) → R2 24 = BitVec.ofNat 64 (td + 1) →
      R2 12 = 0#64 → DcAt S M2 H F L C G hs' st → DatAt M2 q (.str p') →
      (∀ a, ¬ (q ≤ a ∧ a < q + 16) → imgM M2 a = imgM M a) →
      DWO live S Q t 0x800018f0#64 R2 M2) :
    DWO live S Q t 0x800018c4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab; simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hq8w : BitVec.ofNat 64 q + 8#64 = BitVec.ofNat 64 (q + 8) := by
    rw [show (8#64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
  have hpt := hd.ptr
  rw [show sp + 32 + 8 = sp + 40 by omega] at hpt
  have hqo : ∀ b, q ≤ b → b < q + 16 → S b := fun b h1 h2 => by
    have := hq.own (b - q) (by omega); rwa [Nat.add_sub_cancel' h1] at this
  -- the popped string's object
  obtain ⟨v, hv⟩ := h.den.hsDen _ hp'
  obtain ⟨o', ho', e1⟩ : ∃ o' ∈ G.strs, o'.hb.pay = p' := by
    cases v with
    | num _ => exact absurd hv (by simp [GV.Den])
    | str x => obtain ⟨o', ho', e1, -⟩ := hv; exact ⟨o', ho', e1⟩
  have hso' := h.view.strs o' ho'
  have hmem : o'.hb ∈ G.blocks :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o', ho', by simp⟩))
  have bt := blk_bounds h.heap.heap (h.heap.raw.live o'.hb hmem)
  have hhsz := hso'.hsz
  simp only [heapStart, heapEnd] at bt
  have hpp : (GV.str p').ptr = o'.hb.pay := by rw [e1]; rfl
  rw [hpp] at hpt
  generalize hw0 : ldv .ld M (sp + 32) = w0
  have l1 : ldv .ld (writeLog (writeLog M [(q, 8, w0)]) [(q + 8, 8, BitVec.ofNat 64 o'.hb.pay)])
      o'.hb.pay = BitVec.ofNat 64 o'.tb.pay := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hso'.ptr
  have l2 : ldv .ld (writeLog (writeLog M [(q, 8, w0)]) [(q + 8, 8, BitVec.ofNat 64 o'.hb.pay)])
      (o'.hb.pay + 8) = BitVec.ofNat 64 o'.s.length := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hso'.len
  have l3 : ldv .ld (writeLog (writeLog M [(q, 8, w0)]) [(q + 8, 8, BitVec.ofNat 64 o'.hb.pay)])
      (q + 8) = BitVec.ofNat 64 o'.hb.pay := ldv_store_hit _ _ _
  bc_run hlive hS [h2, h22, h24, hpt, hw0, addiw1_ofNat (c := td) htd, l1, l2, l3, hq8w] at 0x80003c64
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | (intro b hb; have := of_mem_accAddrs hb; exact hqo b (by omega) (by omega))
    | skip
  bc_run hlive hS [l1] at 0x800018dc
  bc_run hlive hS [h22, l3, hq8w] at 0x80003c6c
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | (intro b hb; have := of_mem_accAddrs hb; exact hqo b (by omega) (by omega))
    | skip
  have hp8 : BitVec.ofNat 64 o'.hb.pay + 8#64 = BitVec.ofNat 64 (o'.hb.pay + 8) := by
    rw [show (8#64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
  simp only [ldv_store_hit]
  bc_run hlive hS [l2, hp8] at 0x800018e8
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | (intro b hb; have := of_mem_accAddrs hb; exact hqo b (by omega) (by omega))
    | skip
  bc_run hlive hS [BitVec.ofNat_add_ofNat] at 0x800018f0
  have hmo : MemOnly (fun a => q ≤ a ∧ a < q + 16)
      (writeLog (writeLog M [(q, 8, w0)]) [(q + 8, 8, BitVec.ofNat 64 o'.hb.pay)]) M := fun a ha => by
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hP : ∀ a, (q ≤ a ∧ a < q + 16) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    have := above_sp (sp := q) (a := a) (by simp only [heapEnd]; omega) ha.1
    ⟨this.1, this.2.1⟩
  have htg := hd.tag
  rw [hw0] at htg
  exact hk _ _ o' (by keeps_tac Keeps.refl _ _) ho' e1 (by bsimp []) (by bsimp [])
    (by bsimp []) (by bsimp []) (h.outWrite hmo hP)
    (slotMem_dat ⟨htg, by rw [← e1]; rfl⟩) hmo

/-- **The tail call** (`0x800018bc`, the text at its end, the popped string
`.str p'` in the slot `s9 = sp + 32`): `dc_free_str (&string->ptr)` of the
current string (`.str p`, at `q`), then `rt_tail2`. -/
theorem rt_tail (hlive : ∀ p ∈ dcText, live p.1) {p p' q td : Nat} {hs' : List GV}
    (h : DcAt S M H F L C G (.str p :: hs') st) (hq : DatSlot S (sp + 176) q)
    (hw : ldv .ld M (q + 8) = BitVec.ofNat 64 p) (hd : DatAt M (sp + 32) (.str p'))
    (hp' : GV.str p' ∈ hs') (hown : ∀ b, sp ≤ b → b < sp + 88 → S b)
    (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (htd : td + 1 < 2 ^ 31) {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp)
    (h22 : R 22 = BitVec.ofNat 64 q) (h24 : R 24 = BitVec.ofNat 64 td)
    (hk : ∀ R2 H2 (G' : DcG) M2 o', Keeps (1 :: 8 :: 9 :: 12 :: 24 :: cClob) R2 R → o' ∈ G'.strs →
      o'.hb.pay = p' → R2 8 = BitVec.ofNat 64 o'.tb.pay →
      R2 9 = BitVec.ofNat 64 (o'.tb.pay + o'.s.length) → R2 24 = BitVec.ofNat 64 (td + 1) →
      R2 12 = 0#64 → SameNodes G G' → DcAt S M2 H2 F L C G' hs' st → StrPin G.strs G'.strs hs' →
      DatAt M2 q (.str p') →
      (∀ a, OutHeap a → ¬ (DcGlob a ∧ ¬ PinWords a) → ¬ frameIn sp 32 a → ¬ (q ≤ a ∧ a < q + 16) →
        imgM M2 a = imgM M a) →
      DWO live S Q t 0x800018f0#64 R2 M2) :
    DWO live S Q t 0x800018bc#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab; simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hq8 : PtrSlot S (q + 8) := ⟨fun i hi => by
      have := hq.own (8 + i) (by omega); rwa [← Nat.add_assoc] at this, by omega,
    by simp only [tohostAddr] at hsl ⊢; omega, by omega⟩
  have hq8w : BitVec.ofNat 64 q + 8#64 = BitVec.ofNat 64 (q + 8) := by
    rw [show (8#64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
  bc_run hlive hS [h2, h22, hq8w] at 0x800039a4
  refine dc_free_str_spec hlive h hq8 hw hsf hab _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    fun R1 M1 H1 G1 k1 hsn h1 hso hpin => ?_
  bsimp []
  have hd1 : DatAt M1 (sp + 32) (.str p') := DatAt.congr16 (fun x h1 h2 =>
    hso x (outHeap_of_ge (by simp only [heapEnd]; omega)) (fun hg => by
      have := hg.1.lt; simp only [heapStart] at this; omega)
      (fun hf => by simp only [frameIn] at hf; omega)) hd
  refine rt_tail2 hlive h1 hq hd1 hp' hown hsf hab htd (by rw [k1.get 2 (by decide)]; bsimp [h2])
    (by rw [k1.get 22 (by decide)]; bsimp [h22]) (by rw [k1.get 24 (by decide)]; bsimp [h24])
    fun R2 M2 o' k2 ho' e1 e8 e9 e24 e12 h2' hd2 hm2 => ?_
  exact hk R2 H1 G1 M2 o' (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac
    ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))) ho' e1 e8 e9 e24 e12 hsn h2' hpin hd2
    fun a e1 e2 e3 e4 => (hm2 a e4).trans (hso a e1 e2 e3)

end

end Dc.Mach
