import Dc.Adequacy
import Vsa.Machine

/-!
# Refinement: the dc binary against the dc semantics

The machine is the RISC-V ISA relation of `Vsa.Machine` (`Halts`,
`Diverges`), the specification is `Dc.Runs 70` (line length 70: the
bare-metal build has no environment, so `DC_LINE_LENGTH` is unset).

`DcSim L` packages the two forward-simulation obligations for the binary
at the configurations `L.boot prog` (the ELF loaded with `prog` in its script
buffer); `refinement` derives the full correspondence from them by machine
determinism, as `Vsa.Refine.refinement` does for WHILE:

* the terminating runs of `prog` are exactly the clean halts of the machine,
  with the same output;
* a diverging machine means `prog` has no terminating run.
-/

namespace Dc

open Vsa.Machine

/-- The console text of an output byte list (the HTIF console appends
`Char.ofNat b` for each byte `b`). -/
def outStr (out : List Nat) : String := String.ofList (out.map Char.ofNat)

/-- The boot configurations of a dc binary and the programs it accepts. -/
structure DcLayout where
  /-- the machine configuration with `prog` loaded -/
  boot : List Nat → Config
  /-- the programs the layout can hold -/
  admissible : List Nat → Prop

/-- Forward simulation for dc. -/
structure DcSim (L : DcLayout) : Prop where
  term_sim : ∀ prog out, L.admissible prog → Runs 70 prog out → Halts (L.boot prog) (outStr out) 0
  stuck_sim : ∀ prog, L.admissible prog → (¬ ∃ out, Runs 70 prog out) →
    Diverges (L.boot prog) ∨ ∃ out e, Halts (L.boot prog) out e ∧ e ≠ 0

/-- **The refinement theorem.** For every admissible dc program: every
terminating run is a clean halt of the machine with the same output, every
clean halt is such a run, and machine divergence means no run
terminates. -/
theorem refinement {L : DcLayout} (H : DcSim L) (prog : List Nat) (hp : L.admissible prog) :
    (∀ out, Runs 70 prog out → Halts (L.boot prog) (outStr out) 0) ∧
    (∀ s, Halts (L.boot prog) s 0 → ∃ out, Runs 70 prog out ∧ s = outStr out) ∧
    (Diverges (L.boot prog) → ¬ ∃ out, Runs 70 prog out) := by
  refine ⟨fun out h => H.term_sim prog out hp h, fun s hs => ?_, ?_⟩
  · by_cases hex : ∃ out, Runs 70 prog out
    · obtain ⟨out, h⟩ := hex
      obtain ⟨ho, -⟩ := hs.deterministic (H.term_sim prog out hp h)
      exact ⟨out, h, ho⟩
    · rcases H.stuck_sim prog hp hex with hd | ⟨s', e, h', he⟩
      · exact (hd.not_halts hs).elim
      · obtain ⟨-, hee⟩ := hs.deterministic h'
        exact (he hee.symm).elim
  · rintro hd ⟨out, h⟩
    exact hd.not_halts (H.term_sim prog out hp h)

end Dc
