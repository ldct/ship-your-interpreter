import Dc.Semantics

/-!
# An executable dc interpreter, sound for the semantics

`run lm fuel st f` follows the rules of `Dc.Loop` / `Dc.Tos` one step per
unit of fuel; `none` means the fuel ran out. `run_sound` shows that every result is derivable, so
`runOut_sound` turns an evaluation into a proof of `Runs`.
-/

namespace Dc

mutual

/-- The executable counterpart of `Loop`. -/
def run (lm : Nat) : Nat → St → Frame → Option (St × Status)
  | 0, _, _ => none
  | _ + 1, st, ⟨[], _, _⟩ => some (st, .ok)
  | fuel + 1, st, ⟨c :: rest, td, neg⟩ =>
    match dcFunc lm st c rest.head? neg with
    | .ok st' => run lm fuel st' ⟨rest, td, false⟩
    | .eatOne st' => run lm fuel st' ⟨rest.tail, td, false⟩
    | .evalReg st' reg =>
      match regGet st' reg with
      | some v => tos lm fuel (st'.push v) rest.tail td
      | none => run lm fuel st' ⟨rest.tail, td, false⟩
    | .evalTos st' => tos lm fuel st' rest td
    | .quit st' =>
      if td ≤ st'.unwind then some ({ st' with unwind := st'.unwind - td }, .quit)
      else run lm fuel st' ⟨rest, td - st'.unwind, false⟩
    | .int =>
      run lm fuel (st.push (.num (readNum st.ibase (c :: rest)).1))
        ⟨(readNum st.ibase (c :: rest)).2, td, false⟩
    | .str => run lm fuel (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩
    | .comment => run lm fuel st ⟨skipEol rest, td, false⟩
    | .negcmp => run lm fuel st ⟨rest, td, true⟩
    | .eofError => some (st, .ok)
    | .sqrt st' x =>
      match Num.sqrtLoopFuel x (max st'.scale x.scale) fuel (Num.sqrtInit x).1 (Num.sqrtInit x).2 with
      | some y => run lm fuel (st'.push (.num y)) ⟨rest, td, false⟩
      | none => none
    | .system => run lm fuel st ⟨skipSys rest, td, false⟩

/-- The executable counterpart of `Tos`. -/
def tos (lm : Nat) : Nat → St → List Nat → Nat → Option (St × Status)
  | 0, _, _, _ => none
  | fuel + 1, st, rest, td =>
    match st.stack with
    | [] => run lm fuel st ⟨skipWs rest, td, false⟩
    | .num _ :: _ => run lm fuel st ⟨skipWs rest, td, false⟩
    | .str x :: more =>
      if skipWs rest = [] then run lm fuel { st with stack := more } ⟨x, td + 1, false⟩
      else
        match run lm fuel { st with stack := more } ⟨x, 1, false⟩ with
        | some (st', .ok) => run lm fuel st' ⟨skipWs rest, td, false⟩
        | some (st', .quit) =>
          if 0 < st'.unwind then some ({ st' with unwind := st'.unwind - 1 }, .quit)
          else some (st', .ok)
        | none => none

end

theorem sqrtLoopFuel_sound (x : Num) (rs : Nat) :
    ∀ n g cs y, Num.sqrtLoopFuel x rs n g cs = some y → SqrtLoop x rs g cs y := by
  intro n
  induction n with
  | zero => intro g cs y h; simp [Num.sqrtLoopFuel] at h
  | succ n ih =>
    intro g cs y h
    simp only [Num.sqrtLoopFuel] at h
    split at h
    · split at h
      · exact .refine (by assumption) (by assumption) (ih _ _ _ h)
      · cases h; exact .finish (by assumption) (by assumption)
    · rename_i hn; exact .iterate (by simpa using hn) (ih _ _ _ h)

theorem run_tos_sound (lm : Nat) : ∀ n,
    (∀ st f st' r, run lm n st f = some (st', r) → Loop lm st f st' r) ∧
    (∀ st rest td st' r, tos lm n st rest td = some (st', r) → Tos lm st rest td st' r) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ _ h => by simp [run] at h, fun _ _ _ _ _ h => by simp [tos] at h⟩
  | succ n ih =>
    obtain ⟨ihr, iht⟩ := ih
    constructor
    · rintro st ⟨s, td, neg⟩ st' r h
      cases s with
      | nil => simp [run] at h; obtain ⟨rfl, rfl⟩ := h; exact .done
      | cons c rest =>
        simp only [run] at h
        split at h
        · exact .ok (by assumption) (ihr _ _ _ _ h)
        · exact .eatOne (by assumption) (ihr _ _ _ _ h)
        · split at h
          · exact .evalReg (by assumption) (by assumption) (iht _ _ _ _ _ h)
          · exact .evalRegNone (by assumption) (by assumption) (ihr _ _ _ _ h)
        · exact .evalTos (by assumption) (iht _ _ _ _ _ h)
        · split at h
          · cases h; exact .quitOut (by assumption) (by assumption)
          · exact .quitStay (by assumption) (by omega) (ihr _ _ _ _ h)
        · exact .int (by assumption) (ihr _ _ _ _ h)
        · exact .str (by assumption) (ihr _ _ _ _ h)
        · exact .comment (by assumption) (ihr _ _ _ _ h)
        · exact .negcmp (by assumption) (ihr _ _ _ _ h)
        · cases h; exact .eofError (by assumption)
        · split at h
          · exact .sqrt (by assumption) (sqrtLoopFuel_sound _ _ _ _ _ _ (by assumption))
              (ihr _ _ _ _ h)
          · cases h
        · exact .system (by assumption) (ihr _ _ _ _ h)
    · intro st rest td st' r h
      simp only [tos] at h
      split at h
      · exact .empty (by assumption) (ihr _ _ _ _ h)
      · exact .num (by assumption) (ihr _ _ _ _ h)
      · split at h
        · exact .tail (by assumption) (by assumption) (ihr _ _ _ _ h)
        · split at h
          · exact .callOk (by assumption) (by assumption) (ihr _ _ _ _ (by assumption))
              (ihr _ _ _ _ h)
          · split at h
            · cases h
              exact .callQuitUp (by assumption) (by assumption)
                (ihr _ _ _ _ (by assumption)) (by assumption)
            · cases h
              exact .callQuitStop (by assumption) (by assumption)
                (ihr _ _ _ _ (by assumption)) (by omega)
          · cases h

theorem run_sound {lm n st f st' r} (h : run lm n st f = some (st', r)) :
    Loop lm st f st' r :=
  (run_tos_sound lm n).1 _ _ _ _ h

/-- The output of `dc -e prog` computed with `fuel` steps. -/
def runOut (lm fuel : Nat) (prog : List Nat) : Option (List Nat) :=
  (run lm fuel St.init ⟨prog, 1, false⟩).map (·.1.out)

theorem runOut_sound {lm fuel prog out} (h : runOut lm fuel prog = some out) :
    Runs lm prog out := by
  unfold runOut at h
  match hr : run lm fuel St.init ⟨prog, 1, false⟩, h with
  | some (st, r), h => exact ⟨st, r, run_sound hr, by simpa using h⟩

end Dc
