import Dc.Mach.EvalInv
import Dc.Mach.EvalEntryB

/-!
# `DC_EVALTOS` in the term direction (M10)

`tos_step`: `TosIH` at fuel `n + 1` from the loop at fuel `n` (`LoopIH n`)
through `ev_tos_k`, the nested evaluation by the entry at fuel `n`
(`ev_entry_of_core` over `ev_entry_k`).
-/

namespace Dc.Mach

open Dc

/-- A nested evaluation needs a level of nesting. -/
theorem TosFuel.call0 {lm n k : Nat} {st st'' : St} {rest : List Nat} {td : Nat} {r : Status}
    (h : TosFuel lm (n + 1) 0 k st rest td st'' r) {x : List Nat} {more : List Val}
    (hs : st.stack = .str x :: more) (he : skipWs rest ≠ []) : False := by
  have hn := h.nest
  unfold tosDepth at hn
  simp only [hs, he, ite_false] at hn
  split at hn <;> omega

/-- **`DC_EVALTOS` at fuel `n + 1`**. -/
theorem tos_step {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {n : Nat} (IH : LoopIH live S Q n) :
    TosIH live S Q (n + 1) := by
  intro t0 sp W d k q M0 R0 R M H F L C G hs xs st st'' rest td o r Ge hse xse ke hfu ev h25 hoom
    htl hgrow hpin hk
  have hen := ev_entry_of_core (ev_entry_k (Q := Q) hlive) IH
  refine ev_tos_k hlive ev h25 hoom (fun hns => ?_) (fun x more p' hs he => ?_)
    (fun x more hs he => ?_)
  · -- an empty stack or a number
    have hfu' : EvFuel 70 n d k st ⟨skipWs rest, td, false⟩ st'' r := by
      cases hs : st.stack with
      | nil => exact hfu.empty hs
      | cons v more =>
        cases v with
        | num x => exact hfu.num hs
        | str x => exact absurd hs (hns x more)
    exact ⟨EvHeadK.ofIH IH hfu' hoom htl hgrow hpin hk, EvEndK.ofFuel hlive hfu' htl hgrow hpin hk⟩
  · -- the tail call
    have hfu' := hfu.tailCall hs he
    have htd : td + 1 < 2 ^ 31 := by
      have := tailMax_ge (lm := 70) n { st with stack := more } ⟨x, td + 1, false⟩
      have := hfu'.tail; simp only at *; omega
    exact ⟨htd, EvHeadK.ofIH IH hfu' hoom htl hgrow hpin hk,
      EvEndK.ofFuel hlive hfu' htl hgrow hpin hk⟩
  · -- the nested evaluation
    cases d with
    | zero => exact absurd (hfu.call0 hs he) id
    | succ d1 =>
      obtain ⟨st1, r1, k1, hfu1, hk1, hcases⟩ := hfu.call hs he
      have hsb' := ev.sb.pop hs
      have hsrt' := ev.srt.stack more
      have hx : x.length < 2 ^ 24 := ev.sb.top hs x (by simp [Val.strs])
      have hinv := (inv_step n).1 _ _ _ _ hfu1.run ⟨hsb', hsrt', hx⟩
      refine ⟨d1, k1, fun st' r' => st' = st1 ∧ r' = r1, rfl, hk1, fun R1 M1 H1 G1 p' o1 en hox hoom1 hret => ?_,
        fun st' r' hP => ?_⟩
      · rw [← hox] at hfu1
        exact hen t0 _ _ _ _ _ M1 R1 H1 F L C G1 _ _ _ st1 o1 r1 hfu1 en hoom1 (hret st1 r1 ⟨rfl, rfl⟩)
      · obtain ⟨rfl, rfl⟩ := hP
        refine ⟨hinv.1, hinv.2, fun hr => ?_, fun hr hu => ?_, fun hr hu => ?_⟩
        · rcases hcases with ⟨-, hfu2⟩ | ⟨hq, -⟩ | ⟨hq, -⟩
          · exact ⟨EvHeadK.ofIH IH hfu2 hoom htl hgrow hpin hk,
              EvEndK.ofFuel hlive hfu2 htl hgrow hpin hk⟩
          · rw [hr] at hq; cases hq
          · rw [hr] at hq; cases hq
        · rcases hcases with ⟨hq, -⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, hu0, -, -⟩
          · rw [hr] at hq; cases hq
          · exact EvRetK.ofK hlive htl hgrow hpin hk
          · omega
        · rcases hcases with ⟨hq, -⟩ | ⟨-, hu0, -, -⟩ | ⟨-, -, rfl, rfl⟩
          · rw [hr] at hq; cases hq
          · omega
          · exact EvExitK.ofK hlive htl hgrow hpin hk

end Dc.Mach
