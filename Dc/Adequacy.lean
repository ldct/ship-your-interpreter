import Dc.Interp

/-!
# Adequacy: the interpreter computes exactly the semantics

* `run_mono`: more fuel never changes a result.
* `Loop.complete`: every derivation is found by `run` with enough fuel.
* `run_iff`: `Loop` holds iff `run` returns it for some fuel.
* `Loop.det`, `Runs.det`: the semantics is deterministic — a dc program has
  at most one output.
-/

namespace Dc

theorem sqrtLoopFuel_succ {x : Num} {rs : Nat} :
    ∀ {n g cs y}, Num.sqrtLoopFuel x rs n g cs = some y →
      Num.sqrtLoopFuel x rs (n + 1) g cs = some y := by
  intro n
  induction n with
  | zero => intro g cs y h; simp [Num.sqrtLoopFuel] at h
  | succ n ih =>
    intro g cs y h
    rw [Num.sqrtLoopFuel] at h ⊢
    by_cases hn : (Num.sqrtStep x g cs).2.isNearZero cs = true
    · by_cases hc : cs < rs + 1
      · simp only [hn, hc, ite_true] at h ⊢; exact ih h
      · simp only [hn, hc, ite_true, ite_false] at h ⊢; exact h
    · simp only [hn, ite_false] at h ⊢; exact ih h

theorem sqrtLoopFuel_mono {x : Num} {rs n m g cs y}
    (h : Num.sqrtLoopFuel x rs n g cs = some y) (hle : n ≤ m) :
    Num.sqrtLoopFuel x rs m g cs = some y := by
  induction hle with
  | refl => exact h
  | step _ ih => exact sqrtLoopFuel_succ ih

theorem run_tos_succ (lm : Nat) : ∀ n,
    (∀ st f x, run lm n st f = some x → run lm (n + 1) st f = some x) ∧
    (∀ st rest td x, tos lm n st rest td = some x → tos lm (n + 1) st rest td = some x) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ h => by simp [run] at h, fun _ _ _ _ h => by simp [tos] at h⟩
  | succ n ih =>
    obtain ⟨ihr, iht⟩ := ih
    constructor
    · rintro st ⟨s, td, neg⟩ x h
      cases s with
      | nil => simpa [run] using h
      | cons c rest =>
        rw [run] at h ⊢
        generalize dcFunc lm st c rest.head? neg = d at h ⊢
        cases d with
        | evalReg st' reg =>
          simp only at h ⊢
          cases hg : regGet st' reg <;> simp only [hg] at h ⊢
          · exact ihr _ _ _ h
          · exact iht _ _ _ _ h
        | quit st' =>
          simp only at h ⊢
          by_cases hq : td ≤ st'.unwind
          · simp only [hq, ite_true] at h ⊢; exact h
          · simp only [hq, ite_false] at h ⊢; exact ihr _ _ _ h
        | sqrt st' y =>
          simp only at h ⊢
          cases hv : Num.sqrtLoopFuel y (max st'.scale y.scale) n (Num.sqrtInit y).1
              (Num.sqrtInit y).2 with
          | none => simp only [hv] at h; cases h
          | some v =>
            simp only [hv] at h
            rw [sqrtLoopFuel_succ hv]; exact ihr _ _ _ h
        | eofError => exact h
        | evalTos st' => exact iht _ _ _ _ h
        | _ => exact ihr _ _ _ h
    · intro st rest td x h
      rw [tos] at h ⊢
      cases hs : st.stack with
      | nil => simp only [hs] at h; exact ihr _ _ _ h
      | cons v more =>
        simp only [hs] at h
        cases v with
        | num _ => exact ihr _ _ _ h
        | str x =>
          simp only at h ⊢
          by_cases he : skipWs rest = []
          · simp only [he, ite_true] at h ⊢; exact ihr _ _ _ h
          · simp only [he, ite_false] at h ⊢
            cases hc : run lm n { st with stack := more } ⟨x, 1, false⟩ with
            | none => simp only [hc] at h; cases h
            | some p =>
              rw [ihr _ _ _ hc]
              simp only [hc] at h
              obtain ⟨st', r⟩ := p
              cases r with
              | ok => exact ihr _ _ _ h
              | quit => exact h

theorem run_mono {lm n m st f x} (h : run lm n st f = some x) (hle : n ≤ m) :
    run lm m st f = some x := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (run_tos_succ lm _).1 _ _ _ ih

theorem tos_mono {lm n m st rest td x} (h : tos lm n st rest td = some x) (hle : n ≤ m) :
    tos lm m st rest td = some x := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (run_tos_succ lm _).2 _ _ _ _ ih

theorem SqrtLoop.complete {x rs g cs y} (h : SqrtLoop x rs g cs y) :
    ∃ n, Num.sqrtLoopFuel x rs n g cs = some y := by
  induction h with
  | finish hn hc => exact ⟨1, by simp [Num.sqrtLoopFuel, hn, hc]⟩
  | refine hn hc _ ih =>
    obtain ⟨n, h⟩ := ih
    exact ⟨n + 1, by simp [Num.sqrtLoopFuel, hn, hc, h]⟩
  | iterate hn _ ih =>
    obtain ⟨n, h⟩ := ih
    exact ⟨n + 1, by simp [Num.sqrtLoopFuel, hn, h]⟩

mutual

theorem Loop.complete {lm st f st' r} : Loop lm st f st' r → ∃ n, run lm n st f = some (st', r)
  | .done => ⟨1, rfl⟩
  | .ok hf hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [run, hf, h]⟩
  | .eatOne hf hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [run, hf, h]⟩
  | .evalReg hf hg hk => by
    obtain ⟨n, h⟩ := Tos.complete hk; exact ⟨n + 1, by simp [run, hf, hg, h]⟩
  | .evalRegNone hf hg hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [run, hf, hg, h]⟩
  | .evalTos hf hk => by
    obtain ⟨n, h⟩ := Tos.complete hk; exact ⟨n + 1, by simp [run, hf, h]⟩
  | .quitOut hf hle => ⟨1, by simp [run, hf, hle]⟩
  | .quitStay hf hlt hk => by
    obtain ⟨n, h⟩ := Loop.complete hk
    exact ⟨n + 1, by simp [run, hf, Nat.not_le.mpr hlt, h]⟩
  | .int hf hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [run, hf, h]⟩
  | .str hf hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [run, hf, h]⟩
  | .comment hf hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [run, hf, h]⟩
  | .system hf hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [run, hf, h]⟩
  | .negcmp hf hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [run, hf, h]⟩
  | .eofError hf => ⟨1, by simp [run, hf]⟩
  | .sqrt hf hs hk => by
    obtain ⟨n₁, h₁⟩ := SqrtLoop.complete hs
    obtain ⟨n₂, h₂⟩ := Loop.complete hk
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [run, hf]
    rw [sqrtLoopFuel_mono h₁ (Nat.le_max_left _ _)]
    exact run_mono h₂ (Nat.le_max_right _ _)

theorem Tos.complete {lm st rest td st' r} :
    Tos lm st rest td st' r → ∃ n, tos lm n st rest td = some (st', r)
  | .empty hs hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [tos, hs, h]⟩
  | .num hs hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [tos, hs, h]⟩
  | .tail hs he hk => by
    obtain ⟨n, h⟩ := Loop.complete hk; exact ⟨n + 1, by simp [tos, hs, he, h]⟩
  | .callOk hs hne hc hk => by
    obtain ⟨n₁, h₁⟩ := Loop.complete hc
    obtain ⟨n₂, h₂⟩ := Loop.complete hk
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [tos, hs, hne, if_false]
    rw [run_mono h₁ (Nat.le_max_left _ _)]
    exact run_mono h₂ (Nat.le_max_right _ _)
  | .callQuitUp hs hne hc hu => by
    obtain ⟨n, h⟩ := Loop.complete hc
    exact ⟨n + 1, by simp [tos, hs, hne, h, hu]⟩
  | .callQuitStop hs hne hc hu => by
    obtain ⟨n, h⟩ := Loop.complete hc
    exact ⟨n + 1, by simp [tos, hs, hne, h, hu]⟩

end

theorem run_iff {lm st f st' r} : Loop lm st f st' r ↔ ∃ n, run lm n st f = some (st', r) :=
  ⟨Loop.complete, fun ⟨_, h⟩ => run_sound h⟩

/-- The semantics is deterministic. -/
theorem Loop.det {lm st f st₁ r₁ st₂ r₂} (h₁ : Loop lm st f st₁ r₁) (h₂ : Loop lm st f st₂ r₂) :
    st₁ = st₂ ∧ r₁ = r₂ := by
  obtain ⟨n₁, e₁⟩ := h₁.complete
  obtain ⟨n₂, e₂⟩ := h₂.complete
  have := (run_mono e₁ (Nat.le_max_left n₁ n₂)).symm.trans (run_mono e₂ (Nat.le_max_right n₁ n₂))
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

/-- A dc program has at most one output. -/
theorem Runs.det {lm prog o₁ o₂} (h₁ : Runs lm prog o₁) (h₂ : Runs lm prog o₂) : o₁ = o₂ := by
  obtain ⟨s₁, r₁, d₁, rfl⟩ := h₁
  obtain ⟨s₂, r₂, d₂, rfl⟩ := h₂
  rw [(Loop.det d₁ d₂).1]

/-- `runOut` decides the semantics: its answer is the unique output. -/
theorem runOut_spec {lm fuel prog out} (h : runOut lm fuel prog = some out) :
    Runs lm prog out ∧ ∀ out', Runs lm prog out' → out' = out :=
  ⟨runOut_sound h, fun _ h' => Runs.det h' (runOut_sound h)⟩

end Dc
