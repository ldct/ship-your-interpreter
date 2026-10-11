import Dc.Mach.EvalPieces

/-!
# `evalstr`'s entry, proved (M10)

`ev_entry_k : EvEntryCore`: from `evalstr`'s entry `0x80001448` (`*string` a string, so the
type test falls through to `0x80001488`), the prologue saves `ra`, `s6`,
`s0`, `s1`, `s8`, clears `interrupt_seen` (already `0`: `imgM_store_zero4`),
reads the text and its length (`dc_str2charp`, `dc_strlen`: `StrAt`); an
empty text restores and returns `DC_OKAY` (`0x800018f8` → `ev_epi`), else
the remaining saves and the loop constants reach the loop head with `EvAt`
over `⟨o.s, 1, false⟩` (`EvHeadK`). The spans are `en_mid` (`EnMid`, at
`dc_str2charp`'s call), `en_empty`/`en_full` (`EnPro`, after `dc_strlen`) and
`en_head` (`EnHead`, at the loop head).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- A word store of `0` over a word that reads `0` leaves its bytes. -/
theorem imgM_store_zero4 (M : Mem) {a x : Nat} (h : ldv .lw M a = 0#64) (hx : a ≤ x ∧ x < a + 4) :
    imgM (writeLog M [(a, 4, 0#64)]) x = imgM M x := by
  have h0 : imgLE (imgM M) a 4 = 0 := by
    rw [ldv_lw_img] at h
    have hl := imgLE_lt (imgM M) a 4
    have := congrArg (fun v : BitVec 64 => v.toNat % 2 ^ 32) h
    simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.toNat_ofNat] at this
    rw [BitVec.toNat_signExtend] at this
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    split at this <;> omega
  have e : imgLE (imgM (writeLog M [(a, 4, 0#64)])) a 4 = imgLE (imgM M) a 4 := by
    rw [imgLE_store4_hit, h0]; rfl
  have := imgLE_inj e (x - a) (by omega)
  rwa [Nat.add_sub_cancel' hx.1] at this

/-- A word store of `0` over a word that reads `0` leaves memory's bytes. -/
theorem imgM_store_zero (M : Mem) {a x : Nat} (h : ldv .lw M a = 0#64) :
    imgM (writeLog M [(a, 4, 0#64)]) x = imgM M x := by
  by_cases hx : a ≤ x ∧ x < a + 4
  · exact imgM_store_zero4 M h hx
  · exact imgM_store_miss _ _ (by omega)

/-- The saves before the text is read: `s8`, `s1`, `s0`, `s6`, `ra`. -/
abbrev enSaved5 : List (Nat × Nat) := [(24, 96), (9, 152), (8, 160), (22, 112), (1, 168)]

/-- **At `dc_str2charp`'s call** (`0x800014a8`): the five saves in the frame
`[sp - 176, sp)`, the only bytes changed (`interrupt_seen` was already `0`). -/
structure EnMid (sp q : Nat) (o : StrObj) (M : Mem) (R R1 : Nat → BitVec 64) (M1 : Mem) : Prop where
  r2 : R1 2 = BitVec.ofNat 64 (sp - 176)
  a0 : R1 10 = BitVec.ofNat 64 o.hb.pay
  s6 : R1 22 = BitVec.ofNat 64 q
  keep : Keeps [1, 2, 10, 14, 15, 22] R1 R
  saved : SavedWords M1 (sp - 176) enSaved5 R
  only : MemOnly (fun a => sp - 176 ≤ a ∧ a < sp) M1 M

/-- **After the text is read** (`0x800014c4`): `s0`/`s1` the text's bounds,
`s8 = 1`, `a2 = 0`, the five saves. -/
structure EnPro (sp q : Nat) (o : StrObj) (M : Mem) (R R1 : Nat → BitVec 64) (M1 : Mem) : Prop where
  r2 : R1 2 = BitVec.ofNat 64 (sp - 176)
  s0 : R1 8 = BitVec.ofNat 64 o.tb.pay
  s1 : R1 9 = BitVec.ofNat 64 (o.tb.pay + o.s.length)
  s6 : R1 22 = BitVec.ofNat 64 q
  s8 : R1 24 = 1#64
  a2 : R1 12 = 0#64
  keep : Keeps [1, 2, 8, 9, 10, 12, 14, 15, 22, 24] R1 R
  saved : SavedWords M1 (sp - 176) enSaved5 R
  only : MemOnly (fun a => sp - 176 ≤ a ∧ a < sp) M1 M

/-- The globals `evalstr` keeps, through writes to its frame. -/
theorem EvGlobs.frameOnly {S : Nat → Prop} {M M1 : Mem} {sp : Nat} (h : EvGlobs S M)
    (hm : MemOnly (fun a => sp - 176 ≤ a ∧ a < sp) M1 M) (hsp : 0x8001cd88 + 176 ≤ sp) :
    EvGlobs S M1 where
  intrOwn := h.intrOwn
  intr := by
    rw [ldv_congr .lw fun j hj => hm _ (by simp only [widthOfM] at hj; omega)]; exact h.intr
  laOwn := h.laOwn
  la := by
    rw [ldv_congr .lw fun j hj => hm _ (by simp only [widthOfM] at hj; omega)]; exact h.la
  inOwn := h.inOwn

/-- The empty text (`0x800018f8`): the saves reloaded, `DC_OKAY`, the
epilogue. -/
theorem en_empty {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {sp W d k q : Nat} {M : Mem}
    {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
    {hs xs : List GV} {st : St} {o : StrObj} (e : EvEntry S sp W d k q M R H F L C G hs xs st o)
    (hk : EvK live S Q t0 sp W k q M R G hs xs st .ok)
    {R1 : Nat → BitVec 64} {M1 : Mem} (hm : EnPro sp q o M R R1 M1) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800018f8#64 R1 M1 := by
  have hsf : StackFrame S sp 176 := e.frame.mono (by have := e.stk; omega)
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := e.room; simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hstk := e.stk
  have e2 := hm.r2
  have sv := hm.saved
  have g1 := sv.get 1 168 (by decide); have g8 := sv.get 8 160 (by decide)
  have g9 := sv.get 9 152 (by decide); have g22 := sv.get 22 112 (by decide)
  have g24 := sv.get 24 96 (by decide)
  bc_run hlive hlive [e2, g8, g9, g22, g24] at 0x80001478
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hlive [] at 0x8000147c
  have hon := hm.only
  have hq := e.slotPlace
  have hq1 := hq.lo; have hq2 := hq.hi
  refine ev_epi hlive hsf (by simp only [heapEnd]; omega) _ (by bsimp [e2]) g1 e.al
    fun R' k e1 e2' => hk R' M1 H F L C G xs o.hb.pay ?_ (e2'.trans e.r2.symm) ?_ ?_
  · refine Keeps.restoreAll (rs := [1, 2, 8, 9, 22, 24])
      ((k.mono (by decide)).trans (by keeps_tac (hm.keep.mono (by decide)))) fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact e1
    · exact e2'.trans e.r2.symm
    all_goals rw [k.get _ (by decide)]; bsimp []
  · rw [k.get 10 (by decide)]; bsimp []; rfl
  · have hh := e.held
    obtain ⟨hst, rfl⟩ : ∃ hst, hs = .str o.hb.pay :: hst := by
      cases hs with
      | nil => cases hh
      | cons g hst => simp at hh; subst hh; exact ⟨hst, rfl⟩
    have hP : ∀ a, (sp - 176 ≤ a ∧ a < sp) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
      have := above_sp (sp := sp - 176) (a := a) (by simp only [heapEnd]; omega) (by omega)
      ⟨this.1, this.2.1⟩
    exact
      { dc := e.dc.outWrite hon hP
        slot := e.slot.congr16 fun x h1 h2 => hon x (by omega)
        strIn := ⟨o, e.strIn, rfl⟩
        grow := by omega
        pin := StrPin.refl _ _
        mb := e.mb.transport fun a e1 e2 => hon a (by simp only [mulBaseAddr] at e1 e2; omega)
        globs := e.globs.frameOnly hon (by omega)
        out := fun a _ _ _ e4 _ _ => hon a (by simp only [frameIn] at e4; omega) }

/-- **At the loop head** (`0x800014f8`) after the prologue: all saves, the
loop constants. -/
structure EnHead (sp q : Nat) (o : StrObj) (M : Mem) (R R2 : Nat → BitVec 64) (M2 : Mem) : Prop where
  r2 : R2 2 = BitVec.ofNat 64 (sp - 176)
  s0 : R2 8 = BitVec.ofNat 64 o.tb.pay
  s1 : R2 9 = BitVec.ofNat 64 (o.tb.pay + o.s.length)
  s6 : R2 22 = BitVec.ofNat 64 q
  s8 : R2 24 = 1#64
  a2 : R2 12 = 0#64
  cs : EvConsts R2
  keep : Keeps evClob R2 R
  saved : SavedWords M2 (sp - 176) evSaved R
  only : MemOnly (fun a => sp - 176 ≤ a ∧ a < sp) M2 M

/-- The loop head with the invariant over `⟨o.s, 1, false⟩`. -/
theorem en_head {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t0 : String} {sp W d k q : Nat} {M : Mem}
    {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
    {hs xs : List GV} {st : St} {o : StrObj} (e : EvEntry S sp W d k q M R H F L C G hs xs st o)
    (hne : o.s ≠ []) (hhead : EvHeadK live S Q t0 sp W d k k q M R G hs xs st ⟨o.s, 1, false⟩)
    {R2 : Nat → BitVec 64} {M2 : Mem} (hm : EnHead sp q o M R R2 M2) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800014f8#64 R2 M2 := by
  have hstk := e.stk
  have hab := e.room
  have hon := hm.only
  have hq := e.slotPlace
  have hq1 := hq.lo; have hq2 := hq.hi
  have hP : ∀ a, (sp - 176 ≤ a ∧ a < sp) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    have := above_sp (sp := sp - 176) (a := a) (by simp only [heapEnd] at hab ⊢; omega) (by omega)
    ⟨this.1, this.2.1⟩
  simp only [heapEnd] at hab
  refine hhead R2 M2 H F L C G xs o
    { dc := e.dc.outWrite hon hP
      strIn := e.strIn
      strLen := e.len
      sb := e.sb
      srt := e.srt
      held := e.held
      slot := e.slot.congr16 fun x h1 h2 => hon x (by omega)
      slotPlace := hq
      pos := ⟨0, Nat.zero_le _, rfl, by rw [hm.s0]⟩
      s1 := hm.s1
      s6 := hm.s6
      s8 := hm.s8
      tdLt := by show 1 < 2 ^ 31; decide
      cs := hm.cs
      r2 := hm.r2
      saved := hm.saved
      keep := hm.keep
      al := e.al
      r20 := e.r2
      frame := e.frame
      room := by simp only [heapEnd]; omega
      stk := e.stk
      stkPr := e.stkPr
      stkDn := e.stkDn
      budget := e.budget
      mb := e.mb.transport fun a e1 e2 => hon a (by simp only [mulBaseAddr] at e1 e2; omega)
      err := e.err
      globs := e.globs.frameOnly hon (by omega)
      out := fun a _ _ _ _ e5 _ _ => hon a e5 }
    (by rw [hm.a2]; rfl) hne (Nat.le_refl _) (StrPin.refl _ _)

/-- The text nonempty (`0x800014c8`): the rest of the prologue and the
loop head. -/
theorem en_full {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {sp W d k q : Nat} {M : Mem}
    {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
    {hs xs : List GV} {st : St} {o : StrObj} (e : EvEntry S sp W d k q M R H F L C G hs xs st o)
    (hne : o.s ≠ []) (hhead : EvHeadK live S Q t0 sp W d k k q M R G hs xs st ⟨o.s, 1, false⟩)
    {R1 : Nat → BitVec 64} {M1 : Mem} (hm : EnPro sp q o M R R1 M1) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800014c8#64 R1 M1 := by
  have hsf : StackFrame S sp 176 := e.frame.mono (by have := e.stk; omega)
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := e.room; simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hstk := e.stk
  have e2 := hm.r2
  bc_run hlive hlive [e2] at 0x800014f8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have kp := hm.keep
  refine en_head e hne hhead ⟨by bsimp [e2], by bsimp [hm.s0], by bsimp [hm.s1], by bsimp [hm.s6],
    by bsimp [hm.s8], by bsimp [hm.a2], ⟨by bsimp [], by bsimp [], by bsimp [], by bsimp []⟩,
    by keeps_tac (kp.mono (by decide)), fun p hp => ?_, fun a ha => ?_⟩
  · simp only [evSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    have sv := hm.saved
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
      simp (disch := omega) only [ldv_ld_miss, ldv_store_hit, kp.get 18 (by decide), kp.get 19 (by decide),
        kp.get 20 (by decide), kp.get 21 (by decide), kp.get 23 (by decide), kp.get 25 (by decide)] <;>
      first | exact sv.get _ _ (by decide) | skip
  · simp (disch := omega) only [imgM_store_miss]
    exact hm.only a ha

/-- From `dc_str2charp`'s call. -/
theorem en_mid {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {sp W d k q : Nat} {M : Mem}
    {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
    {hs xs : List GV} {st : St} {o : StrObj} (e : EvEntry S sp W d k q M R H F L C G hs xs st o)
    (hhead : o.s ≠ [] → EvHeadK live S Q t0 sp W d k k q M R G hs xs st ⟨o.s, 1, false⟩)
    (hk : o.s = [] → EvK live S Q t0 sp W k q M R G hs xs st .ok)
    {R1 : Nat → BitVec 64} {M1 : Mem} (hm : EnMid sp q o M R R1 M1) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800014a8#64 R1 M1 := by
  have hsf : StackFrame S sp 176 := e.frame.mono (by have := e.stk; omega)
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := e.room; simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => e.dc.heap.heap.own a e1 e2
  have hso := e.dc.view.strs o e.strIn
  have hq := e.slotPlace
  have hq1 := hq.lo; have hq2 := hq.hi; have hq3 := hq.al
  have hstk := e.stk
  have bh := blk_bounds e.dc.heap.heap (e.dc.heap.raw.live o.hb
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, e.strIn, by simp⟩))))
  have hhz := hso.hsz
  simp only [heapStart, heapEnd] at bh
  have hon := hm.only
  have hp0 : ldv .ld M1 o.hb.pay = BitVec.ofNat 64 o.tb.pay := by
    rw [ldv_congr .ld fun j hj => hon _ (by simp only [widthOfM] at hj; omega)]; exact hso.ptr
  have hl0 : ldv .ld M1 (o.hb.pay + 8) = BitVec.ofNat 64 o.s.length := by
    rw [ldv_congr .ld fun j hj => hon _ (by simp only [widthOfM] at hj; omega)]; exact hso.len
  have hpt : ldv .ld M1 (q + 8) = BitVec.ofNat 64 o.hb.pay := by
    rw [ldv_congr .ld fun j hj => hon _ (by simp only [widthOfM] at hj; omega)]; exact e.slot.ptr
  have hqS : ∀ b, q ≤ b → b < q + 16 → S b := fun b h1 h2 => by
    have := hq.own (b - q) (by omega); rwa [Nat.add_sub_cancel' h1] at this
  have r2 := hm.r2; have r10 := hm.a0; have r22 := hm.s6
  have bt := blk_bounds e.dc.heap.heap (e.dc.heap.raw.live o.tb
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, e.strIn, by simp⟩))))
  have htz := hso.tsz
  simp only [heapStart, heapEnd] at bt
  bc_run hlive hS [r2, r10, r22, hp0, hl0, hpt, GV.ptr] at 0x800018f8 0x800014c8
  all_goals try (intro b hb; have := of_mem_accAddrs hb; exact hqS b (by omega) (by omega))
  all_goals intro hc
  · have he : o.s = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact en_empty hlive e (hk he) ⟨by bsimp [r2], by bsimp [], by bsimp [], by bsimp [r22], by bsimp [],
      by bsimp [], by keeps_tac (hm.keep.mono (by decide)), hm.saved, hon⟩
  · have hne : o.s ≠ [] := fun he => hc (by rw [he]; simp)
    exact en_full hlive e hne (hhead hne) ⟨by bsimp [r2], by bsimp [], by bsimp [], by bsimp [r22],
      by bsimp [], by bsimp [], by keeps_tac (hm.keep.mono (by decide)), hm.saved, hon⟩

/-- **`evalstr`'s entry**, continuation-generic (`EvEntryCore`). -/
theorem ev_entry_k {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) : EvEntryCore live S Q := by
  intro t0 sp W d k q M R H F L C G hs xs st o e hhead hk
  have hsf : StackFrame S sp 176 := e.frame.mono (by have := e.stk; omega)
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := e.room; simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => e.dc.heap.heap.own a e1 e2
  have hq := e.slotPlace
  have htg : ldv .lw M q = 2#64 := by rw [e.slot.lw]; rfl
  have hpt := e.slot.ptr
  have e2 := e.r2
  have e10 := e.r10
  have hstk := e.stk
  have hqS : ∀ b, q ≤ b → b < q + 16 → S b := fun b h1 h2 => by
    have := hq.own (b - q) (by omega); rwa [Nat.add_sub_cancel' h1] at this
  have hq1 := hq.lo; have hq2 := hq.hi; have hq3 := hq.al
  bc_run hlive hS [e2, e10, htg, word_sub176] at 0x800014a8
  all_goals try bc_run hlive hS [e2, e10, htg, word_sub176, hpt, GV.ptr, ldv_ld_miss] at 0x800014a8
  all_goals try (simp only [LdOK, StOK, StOKb]; omega)
  all_goals try exact frame_acc hsf (by omega) (by omega)
  all_goals try (intro b hb; have := of_mem_accAddrs hb; exact hqS b (by omega) (by omega))
  all_goals try (intro b hb; have := of_mem_accAddrs hb; exact e.globs.intrOwn b (by omega) (by omega))
  have hz : ∀ M' : Mem, (∀ x, 0x8001cd84 ≤ x → x < 0x8001cd88 → imgM M' x = imgM M x) →
      ldv .lw M' 0x8001cd84 = 0#64 := fun M' h => by
    rw [ldv_congr .lw fun j hj => h _ (by omega) (by simp only [widthOfM] at hj; omega)]
    exact e.globs.intr
  refine en_mid hlive e hhead hk ⟨by bsimp [], by bsimp [], by bsimp [], by keeps_tac Keeps.refl _ _,
    fun p hp => ?_, fun a ha => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
      simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]
  · rw [imgM_store_zero _ (hz _ fun x h1 h2 => by simp (disch := omega) only [imgM_store_miss])]
    simp (disch := omega) only [imgM_store_miss]

end Dc.Mach
