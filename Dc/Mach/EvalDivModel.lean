import Dc.Adequacy

/-!
# Diverging evaluations, step by step (M10, stuck direction)

`RunDiv lm st f`: the evaluation of `f` from `st` completes at no fuel;
`TosDiv` likewise for `tos`. `runDiv_of_not`: a string with no derivation
diverges. One lemma per `dcFunc` outcome, read off `run`'s equations: the
evaluation the outcome continues with diverges too (`runDiv_ok`, …), the
outcomes that end the evaluation are impossible (`runDiv_eof`,
`runDiv_quit_le`), and `DC_EVALTOS`/`DC_EVALREG` hand the divergence to
`tos` (`tosDiv_*`), where a nested evaluation either diverges or completes
with `.ok` and the outer one then diverges (`tosDiv_nested`).
-/

namespace Dc

/-- The evaluation of `f` from `st` completes at no fuel. -/
def RunDiv (lm : Nat) (st : St) (f : Frame) : Prop := ∀ n, run lm n st f = none

/-- `tos` completes at no fuel. -/
def TosDiv (lm : Nat) (st : St) (rest : List Nat) (td : Nat) : Prop :=
  ∀ n, tos lm n st rest td = none

/-- **No derivation, no completion.** -/
theorem runDiv_of_not {lm : Nat} {st : St} {f : Frame} (h : ¬ ∃ st' r, Loop lm st f st' r) :
    RunDiv lm st f := fun n => by
  cases hr : run lm n st f with
  | none => rfl
  | some x => exact absurd ⟨x.1, x.2, run_iff.2 ⟨n, hr⟩⟩ h

theorem RunDiv.not_nil {lm : Nat} {st : St} {td : Nat} {neg : Bool} :
    ¬ RunDiv lm st ⟨[], td, neg⟩ := fun h => by
  have := h 1; simp [run] at this

section

variable {lm : Nat} {st s : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool}

theorem runDiv_ok (h : RunDiv lm st ⟨c :: rest, td, neg⟩) (hres : dcFunc lm st c rest.head? neg = .ok s) :
    RunDiv lm s ⟨rest, td, false⟩ := fun n => by
  have := h (n + 1); simp only [run, hres] at this; exact this

theorem runDiv_eat (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .eatOne s) : RunDiv lm s ⟨rest.tail, td, false⟩ :=
  fun n => by have := h (n + 1); simp only [run, hres] at this; exact this

theorem runDiv_comment (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .comment) : RunDiv lm st ⟨skipEol rest, td, false⟩ :=
  fun n => by have := h (n + 1); simp only [run, hres] at this; exact this

theorem runDiv_negcmp (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .negcmp) : RunDiv lm st ⟨rest, td, true⟩ :=
  fun n => by have := h (n + 1); simp only [run, hres] at this; exact this

theorem runDiv_system (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .system) : RunDiv lm st ⟨skipSys rest, td, false⟩ :=
  fun n => by have := h (n + 1); simp only [run, hres] at this; exact this

theorem runDiv_int (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .int) :
    RunDiv lm (st.push (.num (readNum st.ibase (c :: rest)).1))
      ⟨(readNum st.ibase (c :: rest)).2, td, false⟩ :=
  fun n => by have := h (n + 1); simp only [run, hres] at this; exact this

theorem runDiv_str (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .str) :
    RunDiv lm (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩ :=
  fun n => by have := h (n + 1); simp only [run, hres] at this; exact this

theorem runDiv_reg_none {reg : Nat} (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .evalReg s reg) (hg : regGet s reg = none) :
    RunDiv lm s ⟨rest.tail, td, false⟩ :=
  fun n => by have := h (n + 1); simp only [run, hres, hg] at this; exact this

theorem tosDiv_reg {reg : Nat} {v : Val} (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .evalReg s reg) (hg : regGet s reg = some v) :
    TosDiv lm (s.push v) rest.tail td :=
  fun n => by have := h (n + 1); simp only [run, hres, hg] at this; exact this

theorem tosDiv_tos (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .evalTos s) : TosDiv lm s rest td :=
  fun n => by have := h (n + 1); simp only [run, hres] at this; exact this

/-- `DC_QUIT` from a diverging evaluation stays (`td > unwind`) and the rest diverges. -/
theorem runDiv_quit (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .quit s) :
    ¬ td ≤ s.unwind ∧ RunDiv lm s ⟨rest, td - s.unwind, false⟩ := by
  have h1 := h 1
  by_cases hle : td ≤ s.unwind
  · simp [run, hres, hle] at h1
  · exact ⟨hle, fun n => by have := h (n + 1); simp only [run, hres, hle, ↓reduceIte] at this; exact this⟩

/-- `DC_EOF_ERROR` ends the evaluation: impossible when it diverges. -/
theorem runDiv_eof (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .eofError) : False := by
  have := h 1; simp [run, hres] at this

/-- `v` with the root found (`SqrtLoop`): the rest diverges. -/
theorem runDiv_sqrt {x y : Num} (h : RunDiv lm st ⟨c :: rest, td, neg⟩)
    (hres : dcFunc lm st c rest.head? neg = .sqrt s x)
    (hy : SqrtLoop x (max s.scale x.scale) (Num.sqrtInit x).1 (Num.sqrtInit x).2 y) :
    RunDiv lm (s.push (.num y)) ⟨rest, td, false⟩ := fun n => by
  obtain ⟨m, hm⟩ := hy.complete
  cases hr : run lm n (s.push (.num y)) ⟨rest, td, false⟩ with
  | none => rfl
  | some z =>
    exfalso
    have hz := run_mono hr (Nat.le_max_left n m)
    have hs := sqrtLoopFuel_mono hm (Nat.le_max_right n m)
    have := h (max n m + 1)
    simp only [run, hres, hs, hz] at this
    exact absurd this (by simp)

end

section

variable {lm : Nat} {st : St} {rest : List Nat} {td : Nat}

/-- An empty stack or a number on top: on to the rest. -/
theorem tosDiv_plain (h : TosDiv lm st rest td) (hs : ∀ x more, st.stack ≠ .str x :: more) :
    RunDiv lm st ⟨skipWs rest, td, false⟩ := fun n => by
  have := h (n + 1)
  simp only [tos] at this
  split at this
  · exact this
  · exact this
  · exact absurd ‹_› (hs _ _)

/-- A string on top with nothing after it: the tail call. -/
theorem tosDiv_tail {x : List Nat} {more : List Val} (h : TosDiv lm st rest td)
    (hs : st.stack = .str x :: more) (hw : skipWs rest = []) :
    RunDiv lm { st with stack := more } ⟨x, td + 1, false⟩ := fun n => by
  have := h (n + 1); simp only [tos, hs, hw, ↓reduceIte] at this; exact this

/-- **A nested evaluation**: it diverges, or completes with `.ok` and the
outer evaluation's rest diverges. -/
theorem tosDiv_nested {x : List Nat} {more : List Val} (h : TosDiv lm st rest td)
    (hs : st.stack = .str x :: more) (hw : skipWs rest ≠ []) :
    RunDiv lm { st with stack := more } ⟨x, 1, false⟩ ∨
      ∃ st', Loop lm { st with stack := more } ⟨x, 1, false⟩ st' .ok ∧
        RunDiv lm st' ⟨skipWs rest, td, false⟩ := by
  by_cases hin : RunDiv lm { st with stack := more } ⟨x, 1, false⟩
  · exact .inl hin
  · right
    obtain ⟨m, hm⟩ := Classical.not_forall.mp hin
    obtain ⟨⟨st', r⟩, hr⟩ := Option.ne_none_iff_exists'.mp hm
    refine ⟨st', ?_⟩
    have hq : r = .ok := by
      cases r with
      | ok => rfl
      | quit =>
        exfalso
        have := h (m + 1)
        simp only [tos, hs, hw, ↓reduceIte, hr] at this
        split at this <;> simp at this
    subst hq
    refine ⟨run_iff.2 ⟨m, hr⟩, fun n => ?_⟩
    cases hz : run lm n st' ⟨skipWs rest, td, false⟩ with
    | none => rfl
    | some z =>
      exfalso
      have h1 := run_mono hr (Nat.le_max_right n m)
      have h2 := run_mono hz (Nat.le_max_left n m)
      have := h (max n m + 1)
      simp only [tos, hs, hw, ↓reduceIte, h1, h2] at this
      exact absurd this (by simp)

end

end Dc
