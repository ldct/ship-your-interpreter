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

/-- The bytes at or above `sp - 176` other than the lookahead word are none
of the call's. -/
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
    (h2 : R2 2 = R 2) (hkeep : Keeps evClob R2 R) :
    ∃ o', o'.hb = o.hb ∧ o'.tb = o.tb ∧ o'.s = o.s ∧
      EvAt S sp W d k' q M0 R0 R2 M' H' F' L' C' G' hs (ex ++ xs) st' f' o' := by
  have hab := ev.room; have hstk := ev.stk; have hfl := ev.frame.lo
  have hW1 : 176 ≤ W := by omega
  -- the bytes at or above `sp - 176`
  have hup : ∀ a, sp - 176 ≤ a → ¬ (sp - 176 + 28 ≤ a ∧ a < sp - 176 + 32) → imgM M' a = imgM M a :=
    fun a ha hw => by
      have := above_sp (sp := sp - 176) (a := a) (by simp only [heapEnd] at hab ⊢; omega) ha
      rw [hp.out a this.1 this.2.1 (not_ocG_of_ge (by simp only [heapEnd] at hab ⊢; omega) ha)
        (this.2.2 _), hmc a hw]
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
        rw [hp.out a ho.1 ho.2.1 (fun hg => by
            simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr, mulBaseAddr] at hg e1 e2; omega)
          (fun hf => by have := ho.2.2; simp only [frameIn, heapStart, heapEnd] at hf this hab; omega)]
        exact hmc a (by simp only [mulBaseAddr, heapEnd] at e1 e2 hab; omega)
      err := ev.err
      globs := by
        have g := ev.globs
        have hlow : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → a < heapStart →
            imgM M' a = imgM M a := fun a e1 e2 e3 e4 => by
          rw [hp.out a e1 e2 e3 (fun hf => by simp only [frameIn, heapStart, heapEnd] at hf e4 hab; omega)]
          exact hmc a (by simp only [heapStart, heapEnd] at e4 hab; omega)
        have hw : ∀ b, 0x8001cd30 ≤ b → b < 0x8001cd34 ∨ (0x8001cd84 ≤ b ∧ b < 0x8001cd88) →
            imgM M' b = imgM M b := fun b h1 h2 => hlow b
          (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
          (by simp only [DcGlob, dc_addrs]; omega)
          (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr]; omega)
          (by simp only [heapStart]; omega)
        exact ⟨g.intrOwn,
          by rw [ldv_congr .lw fun i hi => hw _ (by simp only [widthOfM] at hi; omega)
            (.inr (by simp only [widthOfM] at hi; omega))]; exact g.intr,
          g.laOwn,
          by rw [ldv_congr .lw fun i hi => hw _ (by simp only [widthOfM] at hi; omega)
            (.inl (by simp only [widthOfM] at hi; omega))]; exact g.la⟩
      out := fun a e1 e2 e3 e4 e5 e6 => by
        rw [hp.out a e1 e2 e3 e4, hmc a (fun hw => e5 (by omega))]
        exact ev.out a e1 e2 e3 e4 e5 e6 }

end Dc.Mach
