import Dc.Mach.EvalBase
import Dc.Mach.EvalModel

/-!
# The fuel-indexed budgets step by step (M10)

For a frame `c :: rest` completing at fuel `n + 1`, the continuation the
command's result selects completes at fuel `n` within the remaining budgets
(the leak budget less `leakOne c`), and the command's own call meets the
per-call premises (`CallOK`). One lemma per `run` case, read off the
equations of `run`, `nestDepth`, `leakCount` and `AllCalls`.
-/

namespace Dc.Mach

open Dc

/-- The per-call premises of `dc_func` (`FnSize`) and the string bound. -/
abbrev CallOK (st : St) : Prop := FnSize st ∧ StrBound (2 ^ 24) st

/-- One leaking command. -/
abbrev leakOne (c : Nat) : Nat := if leakCmd c then 1 else 0

section

variable {lm n d k : Nat} {st st'' : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool}
  {r : Status}

set_option hygiene false in
/-- Unfold one step of the four fuel-indexed functions under `hr`. -/
macro "fuel_step" : tactic => `(tactic| (
    have hrun := h.run; have hn := h.nest; have hl := h.leak; have hsz := h.size
    unfold Dc.run at hrun; unfold nestDepth at hn; unfold leakCount at hl; unfold AllCalls at hsz
    simp only [hr] at hrun hn hl hsz
    simp only [leakOne]
    cases hlc : leakCmd c <;> simp only [hlc, Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.sub_zero] at hl ⊢))

theorem EvFuel.ok (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) {st' : St}
    (hr : dcFunc lm st c rest.head? neg = .ok st') :
    EvFuel lm n d (k - leakOne c) st' ⟨rest, td, false⟩ st'' r ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.eatOne (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) {st' : St}
    (hr : dcFunc lm st c rest.head? neg = .eatOne st') :
    EvFuel lm n d (k - leakOne c) st' ⟨rest.tail, td, false⟩ st'' r ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.evalRegNone (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) {st' : St}
    {reg : Nat} (hr : dcFunc lm st c rest.head? neg = .evalReg st' reg) (hg : regGet st' reg = none) :
    EvFuel lm n d (k - leakOne c) st' ⟨rest.tail, td, false⟩ st'' r ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals simp only [hg] at hrun hn hl hsz
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.evalReg (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) {st' : St}
    {reg : Nat} {v : Val} (hr : dcFunc lm st c rest.head? neg = .evalReg st' reg)
    (hg : regGet st' reg = some v) :
    TosFuel lm n d (k - leakOne c) (st'.push v) rest.tail td st'' r ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals simp only [hg] at hrun hn hl hsz
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.evalTos (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) {st' : St}
    (hr : dcFunc lm st c rest.head? neg = .evalTos st') :
    TosFuel lm n d (k - leakOne c) st' rest td st'' r ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.quitStay (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) {st' : St}
    (hr : dcFunc lm st c rest.head? neg = .quit st') (hlt : st'.unwind < td) :
    EvFuel lm n d (k - leakOne c) st' ⟨rest, td - st'.unwind, false⟩ st'' r ∧ CallOK st ∧
      leakOne c ≤ k := by
  fuel_step
  all_goals simp only [show ¬ td ≤ st'.unwind by omega, if_false] at hrun hn hl hsz
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.quitOut (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) {st' : St}
    (hr : dcFunc lm st c rest.head? neg = .quit st') (hle : td ≤ st'.unwind) :
    st'' = { st' with unwind := st'.unwind - td } ∧ r = .quit ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals simp only [hle, if_true, Option.some.injEq, Prod.mk.injEq] at hrun hn hl hsz
  all_goals exact ⟨hrun.1.symm, hrun.2.symm, hsz.1, by omega⟩

theorem EvFuel.int (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r)
    (hr : dcFunc lm st c rest.head? neg = .int) :
    EvFuel lm n d (k - leakOne c) (st.push (.num (readNum st.ibase (c :: rest)).1))
      ⟨(readNum st.ibase (c :: rest)).2, td, false⟩ st'' r ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.str (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r)
    (hr : dcFunc lm st c rest.head? neg = .str) :
    EvFuel lm n d (k - leakOne c) (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩
      st'' r ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.comment (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r)
    (hr : dcFunc lm st c rest.head? neg = .comment) :
    EvFuel lm n d (k - leakOne c) st ⟨skipEol rest, td, false⟩ st'' r ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.system (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r)
    (hr : dcFunc lm st c rest.head? neg = .system) :
    EvFuel lm n d (k - leakOne c) st ⟨skipSys rest, td, false⟩ st'' r ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.negcmp (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r)
    (hr : dcFunc lm st c rest.head? neg = .negcmp) :
    EvFuel lm n d (k - leakOne c) st ⟨rest, td, true⟩ st'' r ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals exact ⟨⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.eofError (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r)
    (hr : dcFunc lm st c rest.head? neg = .eofError) :
    st'' = st ∧ r = .ok ∧ CallOK st ∧ leakOne c ≤ k := by
  fuel_step
  all_goals simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  all_goals exact ⟨hrun.1.symm, hrun.2.symm, hsz.1, by omega⟩

theorem EvFuel.sqrt (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) {st' : St} {x : Num}
    (hr : dcFunc lm st c rest.head? neg = .sqrt st' x) :
    ∃ y, Num.sqrtLoopFuel x (max st'.scale x.scale) n (Num.sqrtInit x).1 (Num.sqrtInit x).2 = some y ∧
      EvFuel lm n d (k - leakOne c) (st'.push (.num y)) ⟨rest, td, false⟩ st'' r ∧ CallOK st ∧
      leakOne c ≤ k := by
  fuel_step
  all_goals
    cases hy : Num.sqrtLoopFuel x (max st'.scale x.scale) n (Num.sqrtInit x).1 (Num.sqrtInit x).2 with
    | none => simp only [hy] at hrun; cases hrun
    | some y =>
      simp only [hy] at hrun hn hl hsz
      exact ⟨y, rfl, ⟨hrun, hn, by omega, hsz.2⟩, hsz.1, by omega⟩

theorem EvFuel.nil (h : EvFuel lm n d k st ⟨[], td, neg⟩ st'' r) : st'' = st ∧ r = .ok := by
  have hrun := h.run
  cases n with
  | zero => simp [Dc.run] at hrun
  | succ n =>
    unfold Dc.run at hrun
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
    exact ⟨hrun.1.symm, hrun.2.symm⟩

theorem EvFuel.pos (h : EvFuel lm n d k st f st'' r) : ∃ m, n = m + 1 := by
  have hrun := h.run
  cases n with
  | zero => simp [Dc.run] at hrun
  | succ m => exact ⟨m, rfl⟩

theorem TosFuel.pos {rest : List Nat} (h : TosFuel lm n d k st rest td st'' r) : ∃ m, n = m + 1 := by
  have hrun := h.run
  cases n with
  | zero => simp [Dc.tos] at hrun
  | succ m => exact ⟨m, rfl⟩

set_option hygiene false in
/-- Unfold one step of the `tos` functions. -/
macro "tos_step" : tactic => `(tactic| (
    have hrun := h.run; have hn := h.nest; have hl := h.leak; have hsz := h.size
    unfold Dc.tos at hrun; unfold tosDepth at hn; unfold tosLeak at hl; unfold TosCalls at hsz
    simp only [hs] at hrun hn hl hsz))

theorem TosFuel.empty (h : TosFuel lm (n + 1) d k st rest td st'' r) (hs : st.stack = []) :
    EvFuel lm n d k st ⟨skipWs rest, td, false⟩ st'' r := by
  tos_step
  exact ⟨hrun, hn, hl, hsz⟩

theorem TosFuel.num (h : TosFuel lm (n + 1) d k st rest td st'' r) {x : Num} {more : List Val}
    (hs : st.stack = .num x :: more) :
    EvFuel lm n d k st ⟨skipWs rest, td, false⟩ st'' r := by
  tos_step
  exact ⟨hrun, hn, hl, hsz⟩

theorem TosFuel.tail (h : TosFuel lm (n + 1) d k st rest td st'' r) {x : List Nat} {more : List Val}
    (hs : st.stack = .str x :: more) (he : skipWs rest = []) :
    EvFuel lm n d k { st with stack := more } ⟨x, td + 1, false⟩ st'' r := by
  tos_step
  simp only [he, if_true] at hrun hn hl hsz
  exact ⟨hrun, hn, hl, hsz⟩

/-- A string not in tail position: the nested evaluation completes at fuel
`n` within one level less of nesting, and the continuation (on `.ok`) or
the result (on `.quit`) follows. -/
theorem TosFuel.call (h : TosFuel lm (n + 1) (d + 1) k st rest td st'' r) {x : List Nat}
    {more : List Val} (hs : st.stack = .str x :: more) (he : skipWs rest ≠ []) :
    ∃ st' r' k1, EvFuel lm n d k1 { st with stack := more } ⟨x, 1, false⟩ st' r' ∧ k1 ≤ k ∧
      ((r' = .ok ∧ EvFuel lm n (d + 1) (k - k1) st' ⟨skipWs rest, td, false⟩ st'' r) ∨
       (r' = .quit ∧ 0 < st'.unwind ∧ st'' = { st' with unwind := st'.unwind - 1 } ∧ r = .quit) ∨
       (r' = .quit ∧ st'.unwind = 0 ∧ st'' = st' ∧ r = .ok)) := by
  tos_step
  simp only [he, if_false] at hrun hn hl hsz
  cases hrr : Dc.run lm n { st with stack := more } ⟨x, 1, false⟩ with
  | none => simp only [hrr] at hrun; cases hrun
  | some p =>
    obtain ⟨st', r'⟩ := p
    cases r' with
    | ok =>
      simp only [hrr] at hrun hn hl hsz
      exact ⟨st', .ok, _, ⟨hrr, by omega, Nat.le_refl _, hsz.1⟩, by omega,
        .inl ⟨rfl, hrun, by omega, by omega, hsz.2⟩⟩
    | quit =>
      simp only [hrr] at hrun hn hl hsz
      by_cases hu : 0 < st'.unwind
      · simp only [hu, if_true, Option.some.injEq, Prod.mk.injEq] at hrun
        exact ⟨st', .quit, _, ⟨hrr, by omega, Nat.le_refl _, hsz.1⟩, by omega,
          .inr (.inl ⟨rfl, hu, hrun.1.symm, hrun.2.symm⟩)⟩
      · simp only [hu, if_false, Option.some.injEq, Prod.mk.injEq] at hrun
        exact ⟨st', .quit, _, ⟨hrr, by omega, Nat.le_refl _, hsz.1⟩, by omega,
          .inr (.inr ⟨rfl, by omega, hrun.1.symm, hrun.2.symm⟩)⟩

end

end Dc.Mach
