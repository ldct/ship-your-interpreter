import Dc.Adequacy
import Dc.Depth
import Vsa.Machine

/-!
# Refinement: the dc binary against the dc semantics

The machine is the RISC-V ISA relation of `Vsa.Machine` (`Halts`,
`Diverges`), the specification is `Dc.Runs 70` (line length 70: the
bare-metal build has no environment, so `DC_LINE_LENGTH` is unset).

Heap exhaustion is a possible outcome of any run: dc's allocator returns
`NULL` and dc exits with status 1 (`dc_memfail`). `DcSim L` states forward
simulation with that outcome allowed; `refinement` derives the full
correspondence from it by machine determinism, as `Vsa.Refine.refinement`
does for WHILE:

* a terminating run of `prog` is realised by the machine: a clean halt with
  the same output, or an exit with status 1;
* every clean halt of the machine is a terminating run with that output;
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

/-- Forward simulation for dc, with heap exhaustion (exit status 1) allowed. -/
structure DcSim (L : DcLayout) : Prop where
  term_sim : ∀ prog out, L.admissible prog → Runs 70 prog out →
    Halts (L.boot prog) (outStr out) 0 ∨ ∃ s, Halts (L.boot prog) s 1
  stuck_sim : ∀ prog, L.admissible prog → (¬ ∃ out, Runs 70 prog out) →
    Diverges (L.boot prog) ∨ ∃ out e, Halts (L.boot prog) out e ∧ e ≠ 0

/-- **The refinement theorem.** For every admissible dc program: a
terminating run is a clean halt of the machine with the same output or a
heap-exhaustion exit (status 1); every clean halt is a terminating run with
that output; machine divergence means no run terminates. -/
theorem refinement {L : DcLayout} (H : DcSim L) (prog : List Nat) (hp : L.admissible prog) :
    (∀ out, Runs 70 prog out →
      Halts (L.boot prog) (outStr out) 0 ∨ ∃ s, Halts (L.boot prog) s 1) ∧
    (∀ s, Halts (L.boot prog) s 0 → ∃ out, Runs 70 prog out ∧ s = outStr out) ∧
    (Diverges (L.boot prog) → ¬ ∃ out, Runs 70 prog out) := by
  refine ⟨fun out h => H.term_sim prog out hp h, fun s hs => ?_, ?_⟩
  · by_cases hex : ∃ out, Runs 70 prog out
    · obtain ⟨out, h⟩ := hex
      rcases H.term_sim prog out hp h with h0 | ⟨s', h1⟩
      · obtain ⟨ho, -⟩ := hs.deterministic h0
        exact ⟨out, h, ho⟩
      · obtain ⟨-, he⟩ := hs.deterministic h1
        exact absurd he (by decide)
    · rcases H.stuck_sim prog hp hex with hd | ⟨s', e, h', he⟩
      · exact (hd.not_halts hs).elim
      · obtain ⟨-, hee⟩ := hs.deterministic h'
        exact (he hee.symm).elim
  · rintro hd ⟨out, h⟩
    rcases H.term_sim prog out hp h with h0 | ⟨s', h1⟩
    · exact hd.not_halts h0
    · exact hd.not_halts h1

end Dc
