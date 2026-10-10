import Dc.Interp

/-!
# Macro nesting depth

`evalstr` evaluates a string that is not in tail position by a recursive C
call, so the machine's stack grows with the nesting of such evaluations. The
stack hypothesis of the refinement theorem bounds it: `nestDepth lm n st f`
is the deepest non-tail nesting that the first `n` steps of the evaluation
of frame `f` reach (`0`: the frame's own `evalstr`). It follows `Dc.run`
step for step and is defined for every fuel, so it also measures evaluations
that do not terminate.
-/

namespace Dc

mutual

/-- Deepest nesting reached by `run lm n st f`. -/
def nestDepth (lm : Nat) : Nat → St → Frame → Nat
  | 0, _, _ => 0
  | _ + 1, _, ⟨[], _, _⟩ => 0
  | fuel + 1, st, ⟨c :: rest, td, neg⟩ =>
    match dcFunc lm st c rest.head? neg with
    | .ok st' => nestDepth lm fuel st' ⟨rest, td, false⟩
    | .eatOne st' => nestDepth lm fuel st' ⟨rest.tail, td, false⟩
    | .evalReg st' reg =>
      match regGet st' reg with
      | some v => tosDepth lm fuel (st'.push v) rest.tail td
      | none => nestDepth lm fuel st' ⟨rest.tail, td, false⟩
    | .evalTos st' => tosDepth lm fuel st' rest td
    | .quit st' =>
      if td ≤ st'.unwind then 0 else nestDepth lm fuel st' ⟨rest, td - st'.unwind, false⟩
    | .int =>
      nestDepth lm fuel (st.push (.num (readNum st.ibase (c :: rest)).1))
        ⟨(readNum st.ibase (c :: rest)).2, td, false⟩
    | .str => nestDepth lm fuel (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩
    | .comment => nestDepth lm fuel st ⟨skipEol rest, td, false⟩
    | .negcmp => nestDepth lm fuel st ⟨rest, td, true⟩
    | .eofError => 0
    | .sqrt st' x =>
      match Num.sqrtLoopFuel x (max st'.scale x.scale) fuel (Num.sqrtInit x).1 (Num.sqrtInit x).2 with
      | some y => nestDepth lm fuel (st'.push (.num y)) ⟨rest, td, false⟩
      | none => 0
    | .system => nestDepth lm fuel st ⟨skipSys rest, td, false⟩

/-- Deepest nesting reached by `tos lm n st rest td`. -/
def tosDepth (lm : Nat) : Nat → St → List Nat → Nat → Nat
  | 0, _, _, _ => 0
  | fuel + 1, st, rest, td =>
    match st.stack with
    | [] => nestDepth lm fuel st ⟨skipWs rest, td, false⟩
    | .num _ :: _ => nestDepth lm fuel st ⟨skipWs rest, td, false⟩
    | .str x :: more =>
      if skipWs rest = [] then nestDepth lm fuel { st with stack := more } ⟨x, td + 1, false⟩
      else
        let inner := nestDepth lm fuel { st with stack := more } ⟨x, 1, false⟩ + 1
        match run lm fuel { st with stack := more } ⟨x, 1, false⟩ with
        | some (st', .ok) => max inner (nestDepth lm fuel st' ⟨skipWs rest, td, false⟩)
        | _ => inner

end

/-- The deepest nesting any evaluation of `dc -e prog` reaches, at any fuel,
is at most `d`. -/
def NestBound (lm : Nat) (prog : List Nat) (d : Nat) : Prop :=
  ∀ n, nestDepth lm n St.init ⟨prog, 1, false⟩ ≤ d

end Dc
