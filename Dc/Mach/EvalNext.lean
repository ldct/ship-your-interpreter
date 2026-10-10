import Dc.Mach.EvalHead

/-!
# `evalstr`: the loop invariant after `dc_func` returns (M10)

`EvAt.next`: from the invariant before the call, `dc_func`'s post
(`FnPost` over the memory at the call), and the registers a status route
sets (`s0` at a new position `j` of the same string, `s1`, `s6`, `s8`, the
constants, `sp` as before), the invariant holds again for the new state, the
lost strings `ex ++ xs`, and the leak budget less the command's allowance;
the evaluated string survives with its blocks and text (`StrPin`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **What changed since the loop head** (memory `M`, ghost `G`): the
state `st'` over the handles `ex ++ xs ++ hs`, the lost references within
the allowance `al`, the pinned strings, and the bytes outside the frames
below `evalstr`'s and its scratch words below the saved registers (`sp`
to `sp + 88`: the lookahead word, the slot `s9`, the spills) unchanged. -/
structure EvStep (S : Nat → Prop) (sp W al : Nat) (M : Mem) (G : DcG) (hs xs : List GV) (M' : Mem)
    (H' : Heap) (F' : List Blk) (L' : List NumObj) (C' : BcConsts) (G' : DcG) (st' : St)
    (ex : List GV) : Prop where
  dc : DcAt S M' H' F' L' C' G' (ex ++ (xs ++ hs)) st'
  lk : G'.lk.length + ex.length ≤ G.lk.length + al
  ex : ex.length ≤ 2
  pin : StrPin G.strs G'.strs (xs ++ hs)
  out : ∀ a, OutHeap a → ¬ (DcGlob a ∧ ¬ PinWords a) → ¬ ocG a → ¬ frameIn (sp - 176) (W - 176) a →
    ¬ (sp - 176 ≤ a ∧ a < sp - 176 + 88) → ¬ InP a → imgM M' a = imgM M a

/-- `dc_func`'s post after the lookahead store. -/
theorem EvStep.ofPost {S : Nat → Prop} {sp W al : Nat} {M Mc : Mem} {G : DcG} {hs xs : List GV}
    {M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG} {st' : St}
    {ex : List GV} (hmc : MemOnly (fun a => sp - 176 + 28 ≤ a ∧ a < sp - 176 + 32) Mc M)
    (hp : FnPost S al (sp - 176) (W - 176) Mc G (xs ++ hs) M' H' F' L' C' G' st' ex) :
    EvStep S sp W al M G hs xs M' H' F' L' C' G' st' ex :=
  ⟨hp.dc, hp.lk, hp.ex, hp.pin, fun a e1 e2 e3 e4 e5 _ => by
    rw [hp.out a e1 e2 e3 e4]; exact hmc a (fun hw => e5 (by omega))⟩

/-- No step since the loop head. -/
theorem EvStep.refl {S : Nat → Prop} {sp W : Nat} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV} {st : St}
    (h : DcAt S M H F L C G (xs ++ hs) st) : EvStep S sp W 0 M G hs xs M H F L C G st [] :=
  ⟨by simpa using h, by simp, by simp, StrPin.refl _ _, fun _ _ _ _ _ _ _ => rfl⟩

/-- **Steps compose**: a later step (state `st''` over the same handles,
no new lost references, the pinned strings kept) whose writes are confined
like `EvStep`'s. -/
theorem EvStep.then {S : Nat → Prop} {sp W al : Nat} {M : Mem} {G : DcG} {hs xs : List GV}
    {M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG} {st' : St}
    {ex : List GV} (hp : EvStep S sp W al M G hs xs M' H' F' L' C' G' st' ex)
    {M'' : Mem} {H'' : Heap} {F'' : List Blk} {L'' : List NumObj} {C'' : BcConsts} {G'' : DcG}
    {st'' : St} (hdc : DcAt S M'' H'' F'' L'' C'' G'' (ex ++ (xs ++ hs)) st'')
    (hlk : G''.lk.length ≤ G'.lk.length) (hpin : StrPin G'.strs G''.strs (ex ++ (xs ++ hs)))
    (hout : ∀ a, OutHeap a → ¬ (DcGlob a ∧ ¬ PinWords a) → ¬ frameIn (sp - 176) (W - 176) a →
      ¬ (sp - 176 ≤ a ∧ a < sp - 176 + 88) → ¬ InP a → imgM M'' a = imgM M' a) :
    EvStep S sp W al M G hs xs M'' H'' F'' L'' C'' G'' st'' ex :=
  ⟨hdc, by have := hp.lk; omega, hp.ex,
    hp.pin.trans (hpin.mono fun g hg => List.mem_append_right _ hg),
    fun a e1 e2 e3 e4 e5 e6 => (hout a e1 e2 e4 e5 e6).trans (hp.out a e1 e2 e3 e4 e5 e6)⟩

/-- **The invariant again** after the steps `EvStep` (the scratch words
excepted). -/
theorem EvAt.step {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV} {st : St}
    {f : Frame} {o : StrObj} (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o)
    {M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG}
    {st' : St} {ex : List GV} {al k' : Nat}
    (hp : EvStep S sp W al M G hs xs M' H' F' L' C' G' st' ex)
    (hal : al + 4 * k' ≤ 4 * k)
    {f' : Frame} {R2 : Nat → BitVec 64} {j : Nat} (hj : j ≤ o.s.length) (hdrop : o.s.drop j = f'.s)
    (h8 : R2 8 = BitVec.ofNat 64 (o.tb.pay + j)) (h9 : R2 9 = R 9) (h22 : R2 22 = R 22)
    (h24 : R2 24 = BitVec.ofNat 64 f'.td) (htd : f'.td < 2 ^ 31) (hcs : EvConsts R2)
    (h2 : R2 2 = R 2) (hkeep : Keeps evClob R2 R) (hsb : StrBound (2 ^ 24) st')
    (hsrt : ArrSorted st') :
    ∃ o', o'.hb = o.hb ∧ o'.tb = o.tb ∧ o'.s = o.s ∧
      EvAt S sp W d k' q M0 R0 R2 M' H' F' L' C' G' hs (ex ++ xs) st' f' o' := by
  have hab := ev.room; have hstk := ev.stk; have hfl := ev.frame.lo
  have hW1 : 176 ≤ W := by omega
  -- the bytes at or above `sp - 176`
  have hup : ∀ a, sp - 176 ≤ a → ¬ (sp - 176 ≤ a ∧ a < sp - 176 + 88) → imgM M' a = imgM M a :=
    fun a ha hw => by
      have := above_sp (sp := sp - 176) (a := a) (by simp only [heapEnd] at hab ⊢; omega) ha
      rw [hp.out a this.1 (nglob_pin this.2.1) (not_ocG_of_ge (by simp only [heapEnd] at hab ⊢; omega) ha)
        (this.2.2 _) hw (fun h => by simp only [InP, inPtrAddr] at h; simp only [heapEnd] at hab; omega)]
  obtain ⟨o', ho', e1, e2, e3⟩ := hp.pin o ev.strIn (by
    have := ev.held; cases e : hs with
    | nil => rw [e] at this; cases this
    | cons g hs' => rw [e] at this; simp at this; subst this; simp)
  have hlk := hp.lk
  have hex := hp.ex
  refine ⟨o', e1, e2, e3, ?_⟩
  exact
    { dc := by rw [List.append_assoc]; exact hp.dc
      strIn := ho'
      strLen := e3 ▸ ev.strLen
      sb := hsb
      srt := hsrt
      held := by rw [e1]; exact ev.held
      slot := by
        have hq := ev.slotPlace
        rw [show o'.hb.pay = o.hb.pay by rw [e1]]
        exact ⟨by rw [ldv_congr .ld fun i hi => hup _ (by have := hq.lo; omega)
                  (by have := hq.lo; omega)]; exact ev.slot.tag,
               by rw [ldv_congr .ld fun i hi => hup _ (by have := hq.lo; omega)
                  (by have := hq.lo; omega)]; exact ev.slot.ptr⟩
      slotPlace := ev.slotPlace
      pos := ⟨j, e3 ▸ hj, e3 ▸ hdrop, e2 ▸ h8⟩
      s1 := by rw [h9, ev.s1, e2, e3]
      s6 := h22.trans ev.s6
      s8 := h24
      tdLt := htd
      cs := hcs
      r2 := h2.trans ev.r2
      saved := ev.saved.transport (lo := 88) (top := 176) (hag := fun a h1 h2 => hup a (by omega) (by omega))
      keep := hkeep.trans ev.keep
      al := ev.al
      r20 := ev.r20
      frame := ev.frame
      room := ev.room
      stk := ev.stk
      stkPr := ev.stkPr
      stkDn := ev.stkDn
      budget := by have := ev.budget; simp only [List.length_append]; omega
      mb := ev.mb.transport fun a e1 e2 => by
        have ho := mulBase_off e1 e2
        exact hp.out a ho.1 (nglob_pin ho.2.1) (fun hg => by
            simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr, mulBaseAddr] at hg e1 e2; omega)
          (fun hf => by have := ho.2.2; simp only [frameIn, heapStart, heapEnd] at hf this hab; omega)
          (by simp only [mulBaseAddr, heapEnd] at e1 e2 hab; omega)
          (fun h => by simp only [InP, inPtrAddr, mulBaseAddr] at h e1 e2; omega)
      err := ev.err
      globs := by
        have g := ev.globs
        have hlow : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → a < heapStart → ¬ InP a →
            imgM M' a = imgM M a := fun a e1 e2 e3 e4 e5 => by
          exact hp.out a e1 (nglob_pin e2) e3 (fun hf => by simp only [frameIn, heapStart, heapEnd] at hf e4 hab; omega)
            (by simp only [heapStart, heapEnd] at e4 hab; omega) e5
        have hw : ∀ b, 0x8001cd30 ≤ b → b < 0x8001cd34 ∨ (0x8001cd84 ≤ b ∧ b < 0x8001cd88) →
            imgM M' b = imgM M b := fun b h1 h2 => hlow b
          (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [DcGlob, dc_addrs]; omega)
          (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr]; omega)
          (by simp only [heapStart]; omega) (by simp only [InP, inPtrAddr]; omega)
        exact ⟨g.intrOwn,
          by rw [ldv_congr .lw fun i hi => hw _ (by simp only [widthOfM] at hi; omega)
            (.inr (by simp only [widthOfM] at hi; omega))]; exact g.intr,
          g.laOwn,
          by rw [ldv_congr .lw fun i hi => hw _ (by simp only [widthOfM] at hi; omega)
            (.inl (by simp only [widthOfM] at hi; omega))]; exact g.la, g.inOwn⟩
      out := fun a e1 e2 e3 e4 e5 e6 e7 => by
        rw [hp.out a e1 e2 e3 e4 (fun hw => e5 (by omega)) e7]
        exact ev.out a e1 e2 e3 e4 e5 e6 e7 }

/-- **The invariant after `dc_func` returns** (`EvAt.step` from its post). -/
theorem EvAt.next {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV} {st : St}
    {f : Frame} {o : StrObj} (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o)
    {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG}
    {st' : St} {ex : List GV} {al k' : Nat}
    (hmc : MemOnly (fun a => sp - 176 + 28 ≤ a ∧ a < sp - 176 + 32) Mc M)
    (hp : FnPost S al (sp - 176) (W - 176) Mc G (xs ++ hs) M' H' F' L' C' G' st' ex)
    (hal : al + 4 * k' ≤ 4 * k)
    {f' : Frame} {R2 : Nat → BitVec 64} {j : Nat} (hj : j ≤ o.s.length) (hdrop : o.s.drop j = f'.s)
    (h8 : R2 8 = BitVec.ofNat 64 (o.tb.pay + j)) (h9 : R2 9 = R 9) (h22 : R2 22 = R 22)
    (h24 : R2 24 = BitVec.ofNat 64 f'.td) (htd : f'.td < 2 ^ 31) (hcs : EvConsts R2)
    (h2 : R2 2 = R 2) (hkeep : Keeps evClob R2 R) (hsb : StrBound (2 ^ 24) st')
    (hsrt : ArrSorted st') :
    ∃ o', o'.hb = o.hb ∧ o'.tb = o.tb ∧ o'.s = o.s ∧
      EvAt S sp W d k' q M0 R0 R2 M' H' F' L' C' G' hs (ex ++ xs) st' f' o' :=
  ev.step (EvStep.ofPost hmc hp) hal hj hdrop h8 h9 h22 h24 htd hcs h2 hkeep hsb hsrt

end Dc.Mach
