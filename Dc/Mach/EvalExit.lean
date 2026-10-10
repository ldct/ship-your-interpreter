import Dc.Mach.EvalNext

/-!
# `evalstr`'s returns (M10)

`ev_exit`: at `0x8000156c` (the loop's exit: `s0`–`s9` reloaded, `a0 = 0`,
the frame popped, `ret`) the activation returns `DC_OKAY` with the current
state to the caller's `EvK`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `evalstr`'s epilogue at `0x8000147c` (`ra` reloaded, the frame popped, `ret`). -/
theorem ev_epi {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} {ra : BitVec 64}
    (hsf : StackFrame S sp 176) (hab : heapEnd + 176 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 176)) (f : ldv .ld M (sp - 176 + 168) = ra)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp → DWO live S Q t ra R' M) :
    DWO live S Q t 0x8000147c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, f]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) ?_
  bsimp []; rw [Nat.sub_add_cancel (by omega)]

/-- **The loop's exit** (`0x8000156c`): `DC_OKAY` with the current state. -/
theorem ev_exit {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {sp W d k q : Nat} {M0 : Mem}
    {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
    {G : DcG} {hs xs : List GV} {st : St} {f : Frame} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o)
    {Ge : DcG} {hse xse : List GV} {ke : Nat} (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail)
    (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st .ok) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x8000156c#64 R M := by
  have hsf : StackFrame S sp 176 := ev.frame.mono (by have := ev.stk; omega)
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := ev.room; simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := ev.r2
  have sv := ev.saved
  have g1 := sv.get 1 168 (by decide); have g8 := sv.get 8 160 (by decide)
  have g9 := sv.get 9 152 (by decide); have g18 := sv.get 18 144 (by decide)
  have g19 := sv.get 19 136 (by decide); have g20 := sv.get 20 128 (by decide)
  have g21 := sv.get 21 120 (by decide); have g22 := sv.get 22 112 (by decide)
  have g23 := sv.get 23 104 (by decide); have g24 := sv.get 24 96 (by decide)
  have g25 := sv.get 25 88 (by decide)
  have hal := ev.al
  bc_run hlive hlive [e2, g8, g9, g18, g19, g20, g21, g22, g23, g24, g25] at 0x80001478
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  bc_run hlive hlive [] at 0x8000147c
  have hstk := ev.stk
  refine ev_epi hlive hsf (by simp only [heapEnd]; omega) _ (by bsimp [e2]) g1 hal
    fun R' k e1 e2' => hk R' M H F L C G xs o.hb.pay ?_ (e2'.trans ev.r20.symm) ?_ ?_
  · refine Keeps.restoreAll (rs := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25])
      ((k.mono (by decide)).trans (by keeps_tac (ev.keep.mono (by decide)))) fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact e1
    · exact e2'.trans ev.r20.symm
    all_goals rw [k.get _ (by decide)]; bsimp []
  · rw [k.get 10 (by decide)]; bsimp []; rfl
  · have hh := ev.held
    obtain ⟨hst, rfl⟩ : ∃ hst, hs = .str o.hb.pay :: hst := by
      cases hs with
      | nil => cases hh
      | cons g hst => simp at hh; subst hh; exact ⟨hst, rfl⟩
    simp only [List.tail_cons] at htl hpin
    exact
      { dc := htl ▸ ev.dc
        slot := ev.slot
        strIn := ⟨o, ev.strIn, rfl⟩
        grow := by omega
        pin := htl ▸ hpin
        mb := ev.mb
        globs := ev.globs
        out := fun a e1 e2 e3 e4 e5 => ev.out a e1 e2 e3
          (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))
          (fun hf => e4 (by simp only [frameIn]; omega)) e5 }

end Dc.Mach
