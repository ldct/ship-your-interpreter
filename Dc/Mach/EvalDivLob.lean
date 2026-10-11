import Dc.Mach.HaltsP
import VsaIris.LocalRunOLater

/-!
# Diverging runs by Löb induction (M10, stuck direction)

A run that never finishes is cut into segments between *positions* (`At p`):
from every position a printing run (`LRO`) reaches another position or
`_exit`'s store with a nonzero exit code, and the segment takes at least one
step (its end condition fails at its start). `DivSupply` collects that;
`div_lob` proves, by Löb induction over the partial WP (`wpW`), the
`EvalstrDivSpec`-shaped conclusion at every position: the run diverges or
halts with a nonzero code. Each segment's step pays the Löb hypothesis's
later (`wp_lroW_later`); the exit is `exitKont`.
-/

namespace Dc.Mach

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Inst VsaIris.MallocFast

/-- **Segments between positions** of a run that diverges or exits nonzero. -/
structure DivSupply (live S : Nat → Prop) (Pos : Type)
    (At : Pos → String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) : Prop where
  step : ∀ p t rv mv, At p t rv mv →
    ∃ Qp : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop,
      LRO (vsaModel live) roR dcText dcRegs S Qp t rv mv ∧ ¬ Qp t rv mv ∧
      ∀ t' rv' mv', Qp t' rv' mv' →
        (∃ p', At p' t' rv' mv') ∨ ∃ e, ExitW (fun v => v.1 ≠ 0) t' rv' e

section

variable {GF : BundledGFunctors} [G : MachGS .hasLC GF]

/-- **Löb over the positions**: from any position, the partial WP with a
nonzero exit code. -/
theorem div_lob {live S : Nat → Prop} (hlive : ∀ p ∈ dcText, live p.1) {Pos : Type}
    {At : Pos → String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (D : DivSupply live S Pos At) :
    ⊢ ∀ (p : Pos) (t : String) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8), ⌜At p t rv mv⌝ -∗
      roOwn (GF := GF) roR dcText -∗ RunRes S t rv mv -∗
      (wpW (GF := GF) (vsaModel live)).W (fun v => iprop(⌜v.1 ≠ 0⌝)) := by
  iapply loeb_wand
  imodintro
  iintro Hlob %p %t %rv %mv %hat #Hro ⟨Hr, HS, Hc⟩
  obtain ⟨Qp, hl, hne, hq⟩ := D.step p t rv mv hat
  iapply wp_lroW_later (X := iprop(∀ (p : Pos) (t : String) (rv : Nat → BitVec 64)
      (mv : Nat → BitVec 8), ⌜At p t rv mv⌝ -∗ roOwn (GF := GF) roR dcText -∗ RunRes S t rv mv -∗
      (wpW (GF := GF) (vsaModel live)).W (fun v => iprop(⌜v.1 ≠ 0⌝)))) hl hne
  isplitl []
  · iexact Hro
  isplitl [Hr]
  · iexact Hr
  isplitl [HS]
  · iexact HS
  isplitl [Hc]
  · iexact Hc
  isplitl [Hlob]
  · iexact Hlob
  iintro HIH %t' %rv' %mv' %hq' Hr' HS' Hc'
  rcases hq t' rv' mv' hq' with ⟨p', hat'⟩ | ⟨e, hw⟩
  · iapply HIH $$ %p' %t' %rv' %mv' %hat' Hro
    isplitl [Hr']
    · iexact Hr'
    isplitl [HS']
    · iexact HS'
    iexact Hc'
  · ihave #Htx := roOwn_text roR dcText $$ Hro
    iapply exitKont (S := S) (wpW (vsaModel live)) hlive (fun v => v.1 ≠ 0) $$ Htx %t' %rv' %mv'
      %⟨e, hw⟩ Hr' HS' Hc'

end

end Dc.Mach
