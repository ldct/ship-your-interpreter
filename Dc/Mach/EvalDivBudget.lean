import Dc.Mach.EvalFuel
import Dc.Mach.EvalDivModel

/-!
# The budgets of a diverging evaluation, step by step (M10, stuck direction)

`DivBud lm d k st f`: the evaluation of `f` from `st` diverges (`RunDiv`)
and at every fuel stays within the budgets `EvBudget` asks for (nesting `d`,
leaking commands `k`, the per-call premises, the tail depth); `TosDivBud`
for `tos`. `DivBud.step` reads one command off the four fuel-indexed
functions' equations; one lemma per `dcFunc` outcome instantiates it, the
twins of `EvFuel.ok` … (`EvalFuel.lean`) without a completing fuel.
-/

namespace Dc.Mach

open Dc


/-! ## The budgets grow with the fuel -/

theorem nest_tos_succ (lm : Nat) : ∀ n,
    (∀ st f, nestDepth lm n st f ≤ nestDepth lm (n + 1) st f) ∧
    (∀ st rest td, tosDepth lm n st rest td ≤ tosDepth lm (n + 1) st rest td) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ => by simp [nestDepth], fun _ _ _ => by simp [tosDepth]⟩
  | succ n ih =>
    obtain ⟨ihr, iht⟩ := ih
    constructor
    · rintro st ⟨s, td, neg⟩
      cases s with
      | nil => simp [nestDepth]
      | cons c rest =>
        rw [nestDepth, nestDepth]
        generalize dcFunc lm st c rest.head? neg = d
        cases d with
        | evalReg st' reg =>
          simp only
          cases hg : regGet st' reg
          · exact ihr _ _
          · exact iht _ _ _
        | quit st' =>
          simp only
          split
          · exact Nat.le_refl _
          · exact ihr _ _
        | sqrt st' y =>
          simp only
          cases hv : Num.sqrtLoopFuel y (max st'.scale y.scale) n (Num.sqrtInit y).1
              (Num.sqrtInit y).2 with
          | none => exact Nat.zero_le _
          | some v => rw [sqrtLoopFuel_succ hv]; exact ihr _ _
        | eofError => exact Nat.le_refl _
        | evalTos st' => exact iht _ _ _
        | _ => exact ihr _ _
    · intro st rest td
      rw [tosDepth, tosDepth]
      cases hs : st.stack with
      | nil => exact ihr _ _
      | cons v more =>
        cases v with
        | num _ => exact ihr _ _
        | str x =>
          simp only
          split
          · exact ihr _ _
          · have hi := ihr { st with stack := more } ⟨x, 1, false⟩
            cases hc : run lm n { st with stack := more } ⟨x, 1, false⟩ with
            | none =>
              simp only
              split <;> omega
            | some p =>
              rw [(run_tos_succ lm n).1 _ _ _ hc]
              obtain ⟨st', r⟩ := p
              cases r with
              | ok => have := ihr st' ⟨skipWs rest, td, false⟩; simp only; omega
              | quit => simp only; omega

theorem leak_tos_succ (lm : Nat) : ∀ n,
    (∀ st f, leakCount lm n st f ≤ leakCount lm (n + 1) st f) ∧
    (∀ st rest td, tosLeak lm n st rest td ≤ tosLeak lm (n + 1) st rest td) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ => by simp [leakCount], fun _ _ _ => by simp [tosLeak]⟩
  | succ n ih =>
    obtain ⟨ihr, iht⟩ := ih
    constructor
    · rintro st ⟨s, td, neg⟩
      cases s with
      | nil => simp [leakCount]
      | cons c rest =>
        rw [leakCount, leakCount]
        refine Nat.add_le_add_left ?_ _
        generalize dcFunc lm st c rest.head? neg = d
        cases d with
        | evalReg st' reg =>
          simp only
          cases hg : regGet st' reg
          · exact ihr _ _
          · exact iht _ _ _
        | quit st' =>
          simp only
          split
          · exact Nat.le_refl _
          · exact ihr _ _
        | sqrt st' y =>
          simp only
          cases hv : Num.sqrtLoopFuel y (max st'.scale y.scale) n (Num.sqrtInit y).1
              (Num.sqrtInit y).2 with
          | none => exact Nat.zero_le _
          | some v => rw [sqrtLoopFuel_succ hv]; exact ihr _ _
        | eofError => exact Nat.le_refl _
        | evalTos st' => exact iht _ _ _
        | int => exact Nat.add_le_add_right (ihr _ _) _
        | _ => exact ihr _ _
    · intro st rest td
      rw [tosLeak, tosLeak]
      cases hs : st.stack with
      | nil => exact ihr _ _
      | cons v more =>
        cases v with
        | num _ => exact ihr _ _
        | str x =>
          simp only
          split
          · exact ihr _ _
          · have hi := ihr { st with stack := more } ⟨x, 1, false⟩
            cases hc : run lm n { st with stack := more } ⟨x, 1, false⟩ with
            | none =>
              simp only
              split <;> omega
            | some p =>
              rw [(run_tos_succ lm n).1 _ _ _ hc]
              obtain ⟨st', r⟩ := p
              cases r with
              | ok => have := ihr st' ⟨skipWs rest, td, false⟩; simp only; omega
              | quit => simp only; omega

theorem tail_tos_succ (lm : Nat) : ∀ n,
    (∀ st f, tailMax lm n st f ≤ tailMax lm (n + 1) st f) ∧
    (∀ st rest td, tosTail lm n st rest td ≤ tosTail lm (n + 1) st rest td) := by
  intro n
  induction n with
  | zero => exact ⟨fun st f => tailMax_ge 1 st f, fun st rest td => tosTail_ge 1 st rest td⟩
  | succ n ih =>
    obtain ⟨ihr, iht⟩ := ih
    constructor
    · rintro st ⟨s, td, neg⟩
      cases s with
      | nil => simp [tailMax]
      | cons c rest =>
        rw [tailMax, tailMax]
        refine Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.le_trans ?_ (Nat.le_max_right _ _)⟩
        generalize dcFunc lm st c rest.head? neg = d
        cases d with
        | evalReg st' reg =>
          simp only
          cases hg : regGet st' reg
          · exact ihr _ _
          · exact iht _ _ _
        | quit st' =>
          simp only
          split
          · exact Nat.le_refl _
          · exact ihr _ _
        | sqrt st' y =>
          simp only
          cases hv : Num.sqrtLoopFuel y (max st'.scale y.scale) n (Num.sqrtInit y).1
              (Num.sqrtInit y).2 with
          | none => exact Nat.zero_le _
          | some v => rw [sqrtLoopFuel_succ hv]; exact ihr _ _
        | eofError => exact Nat.le_refl _
        | evalTos st' => exact iht _ _ _
        | _ => exact ihr _ _
    · intro st rest td
      rw [tosTail, tosTail]
      refine Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.le_trans ?_ (Nat.le_max_right _ _)⟩
      cases hs : st.stack with
      | nil => exact ihr _ _
      | cons v more =>
        cases v with
        | num _ => exact ihr _ _
        | str x =>
          simp only
          split
          · exact ihr _ _
          · have hi := ihr { st with stack := more } ⟨x, 1, false⟩
            cases hc : run lm n { st with stack := more } ⟨x, 1, false⟩ with
            | none =>
              simp only
              split <;> omega
            | some p =>
              rw [(run_tos_succ lm n).1 _ _ _ hc]
              obtain ⟨st', r⟩ := p
              cases r with
              | ok => have := ihr st' ⟨skipWs rest, td, false⟩; simp only; omega
              | quit => simp only; omega

theorem calls_tos_pred (lm : Nat) (P : St → Nat → Option Nat → Prop) : ∀ n,
    (∀ st f, AllCalls lm P (n + 1) st f → AllCalls lm P n st f) ∧
    (∀ st rest td, TosCalls lm P (n + 1) st rest td → TosCalls lm P n st rest td) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ => by simp [AllCalls], fun _ _ _ _ => by simp [TosCalls]⟩
  | succ n ih =>
    obtain ⟨ihr, iht⟩ := ih
    constructor
    · rintro st ⟨s, td, neg⟩ h
      cases s with
      | nil => simp [AllCalls]
      | cons c rest =>
        rw [AllCalls] at h ⊢
        refine ⟨h.1, ?_⟩
        have h2 := h.2
        revert h2
        generalize dcFunc lm st c rest.head? neg = d
        cases d with
        | evalReg st' reg =>
          simp only
          cases hg : regGet st' reg
          · exact ihr _ _
          · exact iht _ _ _
        | quit st' =>
          simp only
          split
          · exact id
          · exact ihr _ _
        | sqrt st' y =>
          simp only
          cases hv : Num.sqrtLoopFuel y (max st'.scale y.scale) n (Num.sqrtInit y).1
              (Num.sqrtInit y).2 with
          | none => exact fun _ => trivial
          | some v => rw [sqrtLoopFuel_succ hv]; exact ihr _ _
        | eofError => exact id
        | evalTos st' => exact iht _ _ _
        | _ => exact ihr _ _
    · intro st rest td h
      rw [TosCalls] at h ⊢
      revert h
      cases hs : st.stack with
      | nil => exact ihr _ _
      | cons v more =>
        cases v with
        | num _ => exact ihr _ _
        | str x =>
          simp only
          split
          · exact ihr _ _
          · rintro ⟨hi, ho⟩
            refine ⟨ihr _ _ hi, ?_⟩
            cases hc : run lm n { st with stack := more } ⟨x, 1, false⟩ with
            | none => simp
            | some p =>
              rw [(run_tos_succ lm n).1 _ _ _ hc] at ho
              obtain ⟨st', r⟩ := p
              cases r with
              | ok => exact ihr _ _ ho
              | quit => trivial

/-- The budgets at more fuel bound those at less. -/
theorem nestDepth_mono {lm n m : Nat} {st : St} {f : Frame} (h : n ≤ m) :
    nestDepth lm n st f ≤ nestDepth lm m st f := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih ((nest_tos_succ lm _).1 _ _)

theorem leakCount_mono {lm n m : Nat} {st : St} {f : Frame} (h : n ≤ m) :
    leakCount lm n st f ≤ leakCount lm m st f := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih ((leak_tos_succ lm _).1 _ _)

theorem tailMax_mono {lm n m : Nat} {st : St} {f : Frame} (h : n ≤ m) :
    tailMax lm n st f ≤ tailMax lm m st f := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih ((tail_tos_succ lm _).1 _ _)

theorem allCalls_anti {lm n m : Nat} {P : St → Nat → Option Nat → Prop} {st : St} {f : Frame}
    (h : n ≤ m) (hm : AllCalls lm P m st f) : AllCalls lm P n st f := by
  induction h with
  | refl => exact hm
  | step _ ih => exact ih ((calls_tos_pred lm P _).1 _ _ hm)

/-- **A diverging evaluation within its budgets.** -/
structure DivBud (lm d k : Nat) (st : St) (f : Frame) : Prop where
  nest : ∀ n, nestDepth lm n st f ≤ d
  leak : ∀ n, leakCount lm n st f ≤ k
  size : ∀ n, AllCalls lm (fun st c' _ => CallP st c') n st f
  tail : ∀ n, tailMax lm n st f < 2 ^ 31
  run : RunDiv lm st f

/-- **A diverging `tos` within its budgets.** -/
structure TosDivBud (lm d k : Nat) (st : St) (rest : List Nat) (td : Nat) : Prop where
  nest : ∀ n, tosDepth lm n st rest td ≤ d
  leak : ∀ n, tosLeak lm n st rest td ≤ k
  size : ∀ n, TosCalls lm (fun st c' _ => CallP st c') n st rest td
  tail : ∀ n, tosTail lm n st rest td < 2 ^ 31
  run : TosDiv lm st rest td

section

variable {lm d k : Nat} {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool}

/-- **One command to a further evaluation** `s'`/`f'`, given the four
functions' equations at that command. -/
theorem DivBud.step {s' : St} {f' : Frame} (h : DivBud lm d k st ⟨c :: rest, td, neg⟩)
    (en : ∀ n, nestDepth lm (n + 1) st ⟨c :: rest, td, neg⟩ = nestDepth lm n s' f')
    (el : ∀ n, leakCount lm (n + 1) st ⟨c :: rest, td, neg⟩ = leakOne c + leakCount lm n s' f')
    (es : ∀ n, AllCalls lm (fun st c' _ => CallP st c') (n + 1) st ⟨c :: rest, td, neg⟩ ↔
      CallP st c ∧ AllCalls lm (fun st c' _ => CallP st c') n s' f')
    (et : ∀ n, tailMax lm (n + 1) st ⟨c :: rest, td, neg⟩ = max td (tailMax lm n s' f'))
    (hr : RunDiv lm s' f') :
    DivBud lm d (k - leakOne c) s' f' ∧ CallOK st c ∧ leakOne c ≤ k := by
  have hl0 := h.leak 1
  rw [el] at hl0
  refine ⟨⟨fun n => (en n).symm ▸ h.nest (n + 1), fun n => ?_, fun n => ((es n).1 (h.size (n + 1))).2,
    fun n => Nat.lt_of_le_of_lt (Nat.le_max_right td _) ((et n).symm ▸ h.tail (n + 1)), hr⟩,
    ((es 0).1 (h.size 1)).1, by omega⟩
  have := h.leak (n + 1); rw [el] at this; omega

set_option hygiene false in
/-- The four equations of a command whose outcome continues with `run`. -/
macro "div_eqs" hr:term : tactic => `(tactic| (
    refine DivBud.step h (fun n => by simp only [nestDepth, $hr:term])
      (fun n => by simp only [leakCount, leakOne, $hr:term])
      (fun n => by simp only [AllCalls, $hr:term]) (fun n => by simp only [tailMax, $hr:term]) ?_))

theorem DivBud.ok (h : DivBud lm d k st ⟨c :: rest, td, neg⟩) {s : St}
    (hr : dcFunc lm st c rest.head? neg = .ok s) :
    DivBud lm d (k - leakOne c) s ⟨rest, td, false⟩ ∧ CallOK st c ∧ leakOne c ≤ k := by
  div_eqs hr; exact runDiv_ok h.run hr

theorem DivBud.eatOne (h : DivBud lm d k st ⟨c :: rest, td, neg⟩) {s : St}
    (hr : dcFunc lm st c rest.head? neg = .eatOne s) :
    DivBud lm d (k - leakOne c) s ⟨rest.tail, td, false⟩ ∧ CallOK st c ∧ leakOne c ≤ k := by
  div_eqs hr; exact runDiv_eat h.run hr

theorem DivBud.comment (h : DivBud lm d k st ⟨c :: rest, td, neg⟩)
    (hr : dcFunc lm st c rest.head? neg = .comment) :
    DivBud lm d (k - leakOne c) st ⟨skipEol rest, td, false⟩ ∧ CallOK st c ∧ leakOne c ≤ k := by
  div_eqs hr; exact runDiv_comment h.run hr

theorem DivBud.negcmp (h : DivBud lm d k st ⟨c :: rest, td, neg⟩)
    (hr : dcFunc lm st c rest.head? neg = .negcmp) :
    DivBud lm d (k - leakOne c) st ⟨rest, td, true⟩ ∧ CallOK st c ∧ leakOne c ≤ k := by
  div_eqs hr; exact runDiv_negcmp h.run hr

theorem DivBud.system (h : DivBud lm d k st ⟨c :: rest, td, neg⟩)
    (hr : dcFunc lm st c rest.head? neg = .system) :
    DivBud lm d (k - leakOne c) st ⟨skipSys rest, td, false⟩ ∧ CallOK st c ∧ leakOne c ≤ k := by
  div_eqs hr; exact runDiv_system h.run hr

theorem DivBud.int (h : DivBud lm d k st ⟨c :: rest, td, neg⟩)
    (hr : dcFunc lm st c rest.head? neg = .int) :
    DivBud lm d (k - leakOne c - numLeak (c :: rest)) (st.push (.num (readNum st.ibase (c :: rest)).1))
      ⟨(readNum st.ibase (c :: rest)).2, td, false⟩ ∧ CallOK st c ∧
      leakOne c + numLeak (c :: rest) ≤ k := by
  have el : ∀ n, leakCount lm (n + 1) st ⟨c :: rest, td, neg⟩ = leakOne c +
      (leakCount lm n (st.push (.num (readNum st.ibase (c :: rest)).1))
        ⟨(readNum st.ibase (c :: rest)).2, td, false⟩ + numLeak (c :: rest)) :=
    fun n => by simp only [leakCount, leakOne, hr]
  have hl1 := h.leak 1
  rw [el] at hl1
  refine ⟨⟨fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, runDiv_int h.run hr⟩,
    (by have := h.size 1; simp only [AllCalls, hr] at this; exact this.1), by omega⟩
  · have := h.nest (n + 1); simp only [nestDepth, hr] at this; exact this
  · have := h.leak (n + 1); rw [el] at this; omega
  · have := h.size (n + 1); simp only [AllCalls, hr] at this; exact this.2
  · have := h.tail (n + 1); simp only [tailMax, hr] at this
    exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) this

theorem DivBud.str (h : DivBud lm d k st ⟨c :: rest, td, neg⟩)
    (hr : dcFunc lm st c rest.head? neg = .str) :
    DivBud lm d (k - leakOne c) (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩ ∧
      CallOK st c ∧ leakOne c ≤ k := by
  div_eqs hr; exact runDiv_str h.run hr

theorem DivBud.evalRegNone (h : DivBud lm d k st ⟨c :: rest, td, neg⟩) {s : St} {reg : Nat}
    (hr : dcFunc lm st c rest.head? neg = .evalReg s reg) (hg : regGet s reg = none) :
    DivBud lm d (k - leakOne c) s ⟨rest.tail, td, false⟩ ∧ CallOK st c ∧ leakOne c ≤ k := by
  refine DivBud.step h (fun n => by simp only [nestDepth, hr, hg])
    (fun n => by simp only [leakCount, leakOne, hr, hg]) (fun n => by simp only [AllCalls, hr, hg])
    (fun n => by simp only [tailMax, hr, hg]) (runDiv_reg_none h.run hr hg)

/-- `DC_QUIT` staying in the activation (`unwind < td`). -/
theorem DivBud.quitStay (h : DivBud lm d k st ⟨c :: rest, td, neg⟩) {s : St}
    (hr : dcFunc lm st c rest.head? neg = .quit s) :
    s.unwind < td ∧ DivBud lm d (k - leakOne c) s ⟨rest, td - s.unwind, false⟩ ∧ CallOK st c ∧
      leakOne c ≤ k := by
  obtain ⟨hle, hd⟩ := runDiv_quit h.run hr
  refine ⟨by omega, DivBud.step h (fun n => by simp only [nestDepth, hr, hle, ↓reduceIte])
    (fun n => by simp only [leakCount, leakOne, hr, hle, ↓reduceIte])
    (fun n => by simp only [AllCalls, hr, hle, ↓reduceIte])
    (fun n => by simp only [tailMax, hr, hle, ↓reduceIte]) hd⟩

/-- `v` with its root `y` (`SqrtLoop`). -/
theorem DivBud.sqrt (h : DivBud lm d k st ⟨c :: rest, td, neg⟩) {s : St} {x y : Num}
    (hr : dcFunc lm st c rest.head? neg = .sqrt s x)
    (hy : SqrtLoop x (max s.scale x.scale) (Num.sqrtInit x).1 (Num.sqrtInit x).2 y) :
    DivBud lm d (k - leakOne c) (s.push (.num y)) ⟨rest, td, false⟩ ∧ CallOK st c ∧ leakOne c ≤ k := by
  have hd := runDiv_sqrt h.run hr hy
  obtain ⟨m, hm⟩ := hy.complete
  have hc := h.size 1
  simp only [AllCalls] at hc
  -- the root is found at every fuel from `m` on
  have hfuel : ∀ n, m ≤ n →
      Num.sqrtLoopFuel x (max s.scale x.scale) n (Num.sqrtInit x).1 (Num.sqrtInit x).2 = some y :=
    fun n hn => sqrtLoopFuel_mono hm hn
  have hl1 := h.leak (m + 1)
  simp only [leakCount, hr, hfuel m (Nat.le_refl _)] at hl1
  refine ⟨⟨fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, hd⟩, hc.1, by
    simp only [leakOne]; split at hl1 <;> simp_all <;> omega⟩
  · have := h.nest (max n m + 1)
    simp only [nestDepth, hr, hfuel _ (Nat.le_max_right n m)] at this
    exact Nat.le_trans (nestDepth_mono (Nat.le_max_left n m)) this
  · have := h.leak (max n m + 1)
    simp only [leakCount, leakOne, hr, hfuel _ (Nat.le_max_right n m)] at this ⊢
    have := leakCount_mono (lm := lm) (st := s.push (.num y)) (f := ⟨rest, td, false⟩)
      (Nat.le_max_left n m)
    split at * <;> omega
  · have := h.size (max n m + 1)
    simp only [AllCalls, hr, hfuel _ (Nat.le_max_right n m)] at this
    exact allCalls_anti (Nat.le_max_left n m) this.2
  · have := h.tail (max n m + 1)
    simp only [tailMax, hr, hfuel _ (Nat.le_max_right n m)] at this
    exact Nat.lt_of_le_of_lt (tailMax_mono (Nat.le_max_left n m))
      (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) this)


/-- `DC_EVALTOS`: on to `tos`. -/
theorem DivBud.evalTos (h : DivBud lm d k st ⟨c :: rest, td, neg⟩) {s : St}
    (hr : dcFunc lm st c rest.head? neg = .evalTos s) :
    TosDivBud lm d (k - leakOne c) s rest td ∧ CallOK st c ∧ leakOne c ≤ k := by
  have hl1 := h.leak 1
  simp only [leakCount, hr, tosLeak, Nat.add_zero] at hl1
  refine ⟨⟨fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, tosDiv_tos h.run hr⟩,
    (by have := h.size 1; simp only [AllCalls, hr] at this; exact this.1), by omega⟩
  · have := h.nest (n + 1); simp only [nestDepth, hr] at this; exact this
  · have := h.leak (n + 1); simp only [leakCount, hr] at this; simp only [leakOne]; omega
  · have := h.size (n + 1); simp only [AllCalls, hr] at this; exact this.2
  · have := h.tail (n + 1); simp only [tailMax, hr] at this
    exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) this

/-- `DC_EVALREG` with a value: on to `tos`. -/
theorem DivBud.evalReg (h : DivBud lm d k st ⟨c :: rest, td, neg⟩) {s : St} {reg : Nat} {v : Val}
    (hr : dcFunc lm st c rest.head? neg = .evalReg s reg) (hg : regGet s reg = some v) :
    TosDivBud lm d (k - leakOne c) (s.push v) rest.tail td ∧ CallOK st c ∧ leakOne c ≤ k := by
  have hl1 := h.leak 1
  simp only [leakCount, hr, hg, tosLeak, Nat.add_zero] at hl1
  refine ⟨⟨fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, tosDiv_reg h.run hr hg⟩,
    (by have := h.size 1; simp only [AllCalls, hr, hg] at this; exact this.1), by omega⟩
  · have := h.nest (n + 1); simp only [nestDepth, hr, hg] at this; exact this
  · have := h.leak (n + 1); simp only [leakCount, hr, hg] at this; simp only [leakOne]; omega
  · have := h.size (n + 1); simp only [AllCalls, hr, hg] at this; exact this.2
  · have := h.tail (n + 1); simp only [tailMax, hr, hg] at this
    exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) this

end

section

variable {lm d k : Nat} {st : St} {rest : List Nat} {td : Nat}

/-- An empty stack or a number on top: on to the rest. -/
theorem TosDivBud.plain (h : TosDivBud lm d k st rest td) (hs : ∀ x more, st.stack ≠ .str x :: more) :
    DivBud lm d k st ⟨skipWs rest, td, false⟩ := by
  have key : ∀ n, tosDepth lm (n + 1) st rest td = nestDepth lm n st ⟨skipWs rest, td, false⟩ ∧
      tosLeak lm (n + 1) st rest td = leakCount lm n st ⟨skipWs rest, td, false⟩ ∧
      (TosCalls lm (fun st c' _ => CallP st c') (n + 1) st rest td ↔
        AllCalls lm (fun st c' _ => CallP st c') n st ⟨skipWs rest, td, false⟩) ∧
      tosTail lm (n + 1) st rest td = max td (tailMax lm n st ⟨skipWs rest, td, false⟩) := by
    intro n
    simp only [tosDepth, tosLeak, TosCalls, tosTail]
    cases hst : st.stack with
    | nil => exact ⟨rfl, rfl, Iff.rfl, rfl⟩
    | cons v more =>
      cases v with
      | num _ => exact ⟨rfl, rfl, Iff.rfl, rfl⟩
      | str x => exact absurd hst (hs x more)
  refine ⟨fun n => (key n).1 ▸ h.nest (n + 1), fun n => (key n).2.1 ▸ h.leak (n + 1),
    fun n => (key n).2.2.1.1 (h.size (n + 1)),
    fun n => Nat.lt_of_le_of_lt (Nat.le_max_right _ _) ((key n).2.2.2 ▸ h.tail (n + 1)),
    tosDiv_plain h.run hs⟩

/-- A string on top with nothing after it: the tail call. -/
theorem TosDivBud.tailCall {x : List Nat} {more : List Val} (h : TosDivBud lm d k st rest td)
    (hs : st.stack = .str x :: more) (hw : skipWs rest = []) :
    DivBud lm d k { st with stack := more } ⟨x, td + 1, false⟩ := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, tosDiv_tail h.run hs hw⟩
  · have := h.nest (n + 1); simp only [tosDepth, hs, hw, ↓reduceIte] at this; exact this
  · have := h.leak (n + 1); simp only [tosLeak, hs, hw, ↓reduceIte] at this; exact this
  · have := h.size (n + 1); simp only [TosCalls, hs, hw, ↓reduceIte] at this; exact this
  · have := h.tail (n + 1); simp only [tosTail, hs, hw, ↓reduceIte] at this
    exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) this

/-- **A nested evaluation**: it diverges within one level less, or completes
with `.ok` at a fuel `n` with its budgets (`EvFuel`) and the outer rest
diverges within the rest of the leak budget. -/
theorem TosDivBud.nested {x : List Nat} {more : List Val} (h : TosDivBud lm d k st rest td)
    (hs : st.stack = .str x :: more) (hw : skipWs rest ≠ []) :
    1 ≤ d ∧ (DivBud lm (d - 1) k { st with stack := more } ⟨x, 1, false⟩ ∨
      ∃ n k1 st', EvFuel lm n (d - 1) k1 { st with stack := more } ⟨x, 1, false⟩ st' .ok ∧ k1 ≤ k ∧
        DivBud lm d (k - k1) st' ⟨skipWs rest, td, false⟩) := by
  have hin : ∀ n, nestDepth lm n { st with stack := more } ⟨x, 1, false⟩ + 1 ≤ d := fun n => by
    have := h.nest (n + 1); simp only [tosDepth, hs, hw, ↓reduceIte] at this
    split at this <;> omega
  have hd : 1 ≤ d := by have := hin 0; omega
  refine ⟨hd, ?_⟩
  have hlin : ∀ n, leakCount lm n { st with stack := more } ⟨x, 1, false⟩ ≤ k := fun n => by
    have := h.leak (n + 1)
    simp only [tosLeak, hs, hw, ↓reduceIte] at this
    split at this <;> omega
  have hcin : ∀ n, AllCalls lm (fun st c' _ => CallP st c') n { st with stack := more } ⟨x, 1, false⟩ :=
    fun n => by
      have := h.size (n + 1); simp only [TosCalls, hs, hw, ↓reduceIte] at this; exact this.1
  have htin : ∀ n, tailMax lm n { st with stack := more } ⟨x, 1, false⟩ < 2 ^ 31 := fun n => by
    have := h.tail (n + 1)
    simp only [tosTail, hs, hw, ↓reduceIte] at this
    have := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) this
    split at this <;> omega
  rcases tosDiv_nested h.run hs hw with hdv | ⟨st', hl, hdv⟩
  · exact .inl ⟨fun n => by have := hin n; omega, hlin, hcin, htin, hdv⟩
  · obtain ⟨n, hn⟩ := Loop.complete hl
    refine .inr ⟨n, leakCount lm n { st with stack := more } ⟨x, 1, false⟩, st',
      ⟨hn, by have := hin n; omega, Nat.le_refl _, hcin n, htin n⟩, hlin n, ?_⟩
    -- the outer rest at any fuel `m`, read at `N = max n m`
    have hrN : ∀ N, n ≤ N → Dc.run lm N { st with stack := more } ⟨x, 1, false⟩ = some (st', Status.ok) :=
      fun N hN => run_mono hn hN
    refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, hdv⟩
    · have := h.nest (max n m + 1)
      simp only [tosDepth, hs, hw, ↓reduceIte, hrN _ (Nat.le_max_left n m)] at this
      exact Nat.le_trans (nestDepth_mono (Nat.le_max_right n m))
        (Nat.le_trans (Nat.le_max_right _ _) this)
    · have := h.leak (max n m + 1)
      simp only [tosLeak, hs, hw, ↓reduceIte, hrN _ (Nat.le_max_left n m)] at this
      have h1 := leakCount_mono (lm := lm) (st := { st with stack := more }) (f := ⟨x, 1, false⟩)
        (Nat.le_max_left n m)
      have h2 := leakCount_mono (lm := lm) (st := st') (f := ⟨skipWs rest, td, false⟩)
        (Nat.le_max_right n m)
      omega
    · have := h.size (max n m + 1)
      simp only [TosCalls, hs, hw, ↓reduceIte, hrN _ (Nat.le_max_left n m)] at this
      exact allCalls_anti (Nat.le_max_right n m) this.2
    · have := h.tail (max n m + 1)
      simp only [tosTail, hs, hw, ↓reduceIte, hrN _ (Nat.le_max_left n m)] at this
      have := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) this
      exact Nat.lt_of_le_of_lt (tailMax_mono (Nat.le_max_right n m))
        (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) this)

end

end Dc.Mach
