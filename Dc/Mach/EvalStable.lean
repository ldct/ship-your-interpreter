import Dc.Mach.EvalDivBudget

/-!
# The evaluation budgets of a terminating run

Once `run lm n st f` returns, more fuel changes none of the budgets
`nestDepth`, `leakCount`, `tailMax`, `AllCalls` (`stable_succ`), so the
`∀ n` bounds of `DcAdmissible` follow from their values at that fuel
(`nestBound_of_run`, `leakBound_of_run`, `tailBound_of_run`,
`allCalls_of_run`).
-/

namespace Dc.Mach

open Dc

/-- Close one budget of a step from the budgets of its continuation `e`. -/
macro "stab_close " e:term : tactic =>
  `(tactic| first
    | exact ($e).nest
    | exact Nat.add_le_add_left ($e).leak _
    | exact Nat.add_le_add_left (Nat.add_le_add_right ($e).leak _) _
    | (have := ($e).leak; omega)
    | (have := ($e).tail; omega)
    | exact ($e).calls
    | exact fun hh => ⟨hh.1, ($e).calls hh.2⟩)

/-- The budgets at fuel `n + 1` within those at `n`. -/
structure Stab (lm : Nat) (P : St → Nat → Option Nat → Prop) (n : Nat) (st : St) (f : Frame) :
    Prop where
  nest : nestDepth lm (n + 1) st f ≤ nestDepth lm n st f
  leak : leakCount lm (n + 1) st f ≤ leakCount lm n st f
  tail : tailMax lm (n + 1) st f ≤ tailMax lm n st f
  calls : AllCalls lm P n st f → AllCalls lm P (n + 1) st f

/-- `Stab` for `tos`. -/
structure TStab (lm : Nat) (P : St → Nat → Option Nat → Prop) (n : Nat) (st : St) (rest : List Nat)
    (td : Nat) : Prop where
  nest : tosDepth lm (n + 1) st rest td ≤ tosDepth lm n st rest td
  leak : tosLeak lm (n + 1) st rest td ≤ tosLeak lm n st rest td
  tail : tosTail lm (n + 1) st rest td ≤ tosTail lm n st rest td
  calls : TosCalls lm P n st rest td → TosCalls lm P (n + 1) st rest td

theorem stable_succ (lm : Nat) (P : St → Nat → Option Nat → Prop) : ∀ n,
    (∀ st f x, run lm n st f = some x → Stab lm P n st f) ∧
    (∀ st rest td x, tos lm n st rest td = some x → TStab lm P n st rest td) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ h => by simp [run] at h, fun _ _ _ _ h => by simp [tos] at h⟩
  | succ n ih =>
    obtain ⟨ihr, iht⟩ := ih
    constructor
    · rintro st ⟨s, td, neg⟩ x h
      cases s with
      | nil => exact ⟨by simp [nestDepth], by simp [leakCount], by simp [tailMax], fun _ => by simp [AllCalls]⟩
      | cons c rest =>
        rw [run] at h
        cases hd : dcFunc lm st c rest.head? neg with
        | evalReg st' reg =>
          cases hg : regGet st' reg with
          | none =>
            simp only [hd, hg] at h
            have e := ihr _ _ _ h
            refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [nestDepth, leakCount, tailMax, AllCalls, hd, hg] <;>
              stab_close e
          | some v =>
            simp only [hd, hg] at h
            have e := iht _ _ _ _ h
            refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [nestDepth, leakCount, tailMax, AllCalls, hd, hg] <;>
              stab_close e
        | quit st' =>
          by_cases hq : td ≤ st'.unwind
          · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [nestDepth, leakCount, tailMax, AllCalls, hd, hq]
          · simp only [hd, hq, ite_false] at h
            have e := ihr _ _ _ h
            refine ⟨?_, ?_, ?_, ?_⟩ <;>
              simp only [nestDepth, leakCount, tailMax, AllCalls, hd, hq, ite_false] <;> stab_close e
        | sqrt st' y =>
          cases hv : Num.sqrtLoopFuel y (max st'.scale y.scale) n (Num.sqrtInit y).1 (Num.sqrtInit y).2 with
          | none => simp [hd, hv] at h
          | some v =>
            simp only [hd, hv] at h
            have e := ihr _ _ _ h
            refine ⟨?_, ?_, ?_, ?_⟩ <;>
              simp only [nestDepth, leakCount, tailMax, AllCalls, hd, hv, sqrtLoopFuel_succ hv] <;>
              stab_close e
        | eofError =>
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [nestDepth, leakCount, tailMax, AllCalls, hd]
        | evalTos st' =>
          simp only [hd] at h
          have e := iht _ _ _ _ h
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [nestDepth, leakCount, tailMax, AllCalls, hd] <;>
            stab_close e
        | _ =>
          simp only [hd] at h
          have e := ihr _ _ _ h
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [nestDepth, leakCount, tailMax, AllCalls, hd] <;>
            stab_close e
    · intro st rest td x h
      rw [tos] at h
      cases hs : st.stack with
      | nil =>
        simp only [hs] at h
        have e := ihr _ _ _ h
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tosDepth, tosLeak, tosTail, TosCalls, hs] <;> stab_close e
      | cons v more =>
        cases v with
        | num _ =>
          simp only [hs] at h
          have e := ihr _ _ _ h
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tosDepth, tosLeak, tosTail, TosCalls, hs] <;> stab_close e
        | str y =>
          by_cases he : skipWs rest = []
          · simp only [hs, he, ite_true] at h
            have e := ihr _ _ _ h
            refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tosDepth, tosLeak, tosTail, TosCalls, hs, he, ite_true] <;>
              stab_close e
          · simp only [hs, he, ite_false] at h
            cases hc : run lm n { st with stack := more } ⟨y, 1, false⟩ with
            | none => simp [hc] at h
            | some p =>
              have ei := ihr _ _ _ hc
              have hc1 := (run_tos_succ lm n).1 _ _ _ hc
              obtain ⟨st', r⟩ := p
              cases r with
              | ok =>
                simp only [hc] at h
                have ek := ihr _ _ _ h
                have i1 := ei.nest; have i2 := ei.leak; have i3 := ei.tail
                have k1 := ek.nest; have k2 := ek.leak; have k3 := ek.tail
                refine ⟨?_, ?_, ?_, ?_⟩ <;>
                  simp only [tosDepth, tosLeak, tosTail, TosCalls, hs, he, ite_false, hc, hc1]
                · omega
                · omega
                · omega
                · exact fun hh => ⟨ei.calls hh.1, ek.calls hh.2⟩
              | quit =>
                have i1 := ei.nest; have i2 := ei.leak; have i3 := ei.tail
                refine ⟨?_, ?_, ?_, ?_⟩ <;>
                  simp only [tosDepth, tosLeak, tosTail, TosCalls, hs, he, ite_false, hc, hc1]
                · omega
                · omega
                · omega
                · exact fun hh => ⟨ei.calls hh.1, hh.2⟩

/-- The budgets at fuel `m` within those at `N`. -/
structure Below (lm : Nat) (P : St → Nat → Option Nat → Prop) (N m : Nat) (st : St) (f : Frame) :
    Prop where
  nest : nestDepth lm m st f ≤ nestDepth lm N st f
  leak : leakCount lm m st f ≤ leakCount lm N st f
  tail : tailMax lm m st f ≤ tailMax lm N st f
  calls : AllCalls lm P N st f → AllCalls lm P m st f

/-- The budgets at any fuel beyond a returning run's. -/
theorem stable_ge {lm : Nat} {P : St → Nat → Option Nat → Prop} {N : Nat} {st : St} {f : Frame}
    {x : St × Status} (h : run lm N st f = some x) : ∀ m, N ≤ m → Below lm P N m st f := by
  intro m hm
  induction hm with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, id⟩
  | step hle ih =>
    have e := (stable_succ lm P _).1 _ _ _ (run_mono h hle)
    exact ⟨Nat.le_trans e.nest ih.nest, Nat.le_trans e.leak ih.leak, Nat.le_trans e.tail ih.tail,
      fun hc => e.calls (ih.calls hc)⟩

variable {lm : Nat} {prog : List Nat} {N : Nat} {x : St × Status}

theorem nestBound_of_run (h : run lm N St.init ⟨prog, 1, false⟩ = some x) {d : Nat}
    (hb : nestDepth lm N St.init ⟨prog, 1, false⟩ ≤ d) : NestBound lm prog d := fun n => by
  rcases Nat.le_total n N with hn | hn
  · exact Nat.le_trans (nestDepth_mono hn) hb
  · exact Nat.le_trans (stable_ge (P := fun _ _ _ => True) h n hn).nest hb

theorem leakBound_of_run (h : run lm N St.init ⟨prog, 1, false⟩ = some x) {k : Nat}
    (hb : leakCount lm N St.init ⟨prog, 1, false⟩ ≤ k) : LeakBound lm prog k := fun n => by
  rcases Nat.le_total n N with hn | hn
  · exact Nat.le_trans (leakCount_mono hn) hb
  · exact Nat.le_trans (stable_ge (P := fun _ _ _ => True) h n hn).leak hb

theorem tailBound_of_run (h : run lm N St.init ⟨prog, 1, false⟩ = some x)
    (hb : tailMax lm N St.init ⟨prog, 1, false⟩ < 2 ^ 31) : TailBound lm prog := fun n => by
  rcases Nat.le_total n N with hn | hn
  · exact Nat.lt_of_le_of_lt (tailMax_mono hn) hb
  · exact Nat.lt_of_le_of_lt (stable_ge (P := fun _ _ _ => True) h n hn).tail hb

theorem allCalls_of_run {P : St → Nat → Option Nat → Prop} (h : run lm N St.init ⟨prog, 1, false⟩ = some x)
    (hb : AllCalls lm P N St.init ⟨prog, 1, false⟩) : ∀ n, AllCalls lm P n St.init ⟨prog, 1, false⟩ :=
  fun n => by
    rcases Nat.le_total n N with hn | hn
    · exact allCalls_anti hn hb
    · exact (stable_ge h n hn).calls hb

end Dc.Mach
