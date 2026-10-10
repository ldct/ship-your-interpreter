import VsaIris.LocalRunO

/-!
# A printing run that pays a later

`wp_localRunW_later` (`VsaIris/Interp/SymLater.lean`) for printing runs:
an `LRO` that does not end where it starts (`¬ Q` at its start) takes a
segment, whose step strips the `▷` of a Löb hypothesis in the partial WP
(`wpW`). `LRO.inv`: a printing run is done or takes a segment.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}
  {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)} {rs : List Nat}
  {S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **A printing run is done or takes a segment.** -/
theorem LRO.inv {t : String} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : LRO M ro text rs S Q t rv mv) :
    Q t rv mv ∨ ∃ k, SegFromO M ro text rs S k rv mv (fun o => LRO M ro text rs S Q (t ++ o)) :=
  (LRO.ind (X := fun t rv mv => LRO M ro text rs S Q t rv mv ∧
      (Q t rv mv ∨ ∃ k, SegFromO M ro text rs S k rv mv (fun o => LRO M ro text rs S Q (t ++ o))))
    (fun _ _ _ hq => ⟨LRO.done hq, .inl hq⟩)
    (fun _ _ _ k hs => ⟨LRO.seg k (hs.mono fun _ _ _ h => h.1), .inr ⟨k, hs.mono fun _ _ _ h => h.1⟩⟩)
    h).2

/-- **A printing run that takes a step pays a later** (partial WP): a `▷ X`
in the context is available, without the later, to the run's continuation. -/
theorem wp_lroW_later {Φ : Nat × String → IProp GF} {X : IProp GF} {t : String}
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : LRO M ro text rs S Q t rv mv) (hne : ¬ Q t rv mv) :
    roOwn (GF := GF) ro text ∗ sepL rs (fun r => r ↦ᵣ rv r) ∗ ownSet S (fun a => a ↦ₘ mv a) ∗
      consoleOwn t ∗ ▷ X ∗ (X -∗ runKontO (wpW M) Φ rs S Q) ⊢ (wpW M).W Φ := by
  rcases h.inv with hq | ⟨K, hseg⟩
  · exact absurd hq hne
  unfold roOwn ownSet
  iintro ⟨⟨#Hro, #Htx⟩, Hrs, ⟨%l, %⟨hnd, hmem⟩, Hl⟩, Hc, HX, Hk⟩
  iapply (wpW M).lagRun (hseg.lagFoot (t := t) hmem)
  unfold runFoot
  isplitl [Hrs Hl Hc]
  · iframe Hro Htx Hrs Hl Hc
  iintro %σ %σf %⟨ht, o, hout, hP, _, _⟩ ⟨⟨_, _, Hrs, Hl⟩, Hc⟩
  simp only [wpW_lat]
  inext
  ihave Hk := Hk $$ HX
  rw [hout, ht]
  iapply wp_lroW (wpW M) hP
  unfold roOwn ownSet
  iframe Hro Htx Hrs Hk Hc
  iexists l
  iframe Hl
  ipureintro; exact ⟨hnd, hmem⟩

end

end VsaIris
