import Dc.Depth

/-!
# Lost references and string sizes along an evaluation (M10)

`leakCount lm n st f` counts the commands, within the first `n` steps of the
evaluation of `f` (following `Dc.run` like `nestDepth`), whose `dc_func` arm
may lose references (`leakCmd`): each such call may add at most two lost
number references (`DcG.lk`) and two lost string handles (`FnPost.ex`).
`LeakBound lm prog k` bounds it for `dc -e prog` at every fuel.

`StrBound N st`: every string the state holds is shorter than `N`
(`dc_getnum` reads the evaluated string under `|w| < 2^24`).
-/

namespace Dc

/-- The commands whose `dc_func` arm may lose a reference: `/ % ~ |` (a
failed operation's result slot), `v` (a negative operand, a string), `X` (a
string). -/
def leakCmd (c : Nat) : Bool := c == 47 || c == 37 || c == 126 || c == 124 || c == 118 || c == 88

mutual

/-- Leaking commands run by `run lm n st f`. -/
def leakCount (lm : Nat) : Nat → St → Frame → Nat
  | 0, _, _ => 0
  | _ + 1, _, ⟨[], _, _⟩ => 0
  | fuel + 1, st, ⟨c :: rest, td, neg⟩ =>
    (if leakCmd c then 1 else 0) +
    match dcFunc lm st c rest.head? neg with
    | .ok st' => leakCount lm fuel st' ⟨rest, td, false⟩
    | .eatOne st' => leakCount lm fuel st' ⟨rest.tail, td, false⟩
    | .evalReg st' reg =>
      match regGet st' reg with
      | some v => tosLeak lm fuel (st'.push v) rest.tail td
      | none => leakCount lm fuel st' ⟨rest.tail, td, false⟩
    | .evalTos st' => tosLeak lm fuel st' rest td
    | .quit st' =>
      if td ≤ st'.unwind then 0 else leakCount lm fuel st' ⟨rest, td - st'.unwind, false⟩
    | .int =>
      leakCount lm fuel (st.push (.num (readNum st.ibase (c :: rest)).1))
        ⟨(readNum st.ibase (c :: rest)).2, td, false⟩
    | .str => leakCount lm fuel (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩
    | .comment => leakCount lm fuel st ⟨skipEol rest, td, false⟩
    | .negcmp => leakCount lm fuel st ⟨rest, td, true⟩
    | .eofError => 0
    | .sqrt st' x =>
      match Num.sqrtLoopFuel x (max st'.scale x.scale) fuel (Num.sqrtInit x).1 (Num.sqrtInit x).2 with
      | some y => leakCount lm fuel (st'.push (.num y)) ⟨rest, td, false⟩
      | none => 0
    | .system => leakCount lm fuel st ⟨skipSys rest, td, false⟩

/-- Leaking commands run by `tos lm n st rest td`. -/
def tosLeak (lm : Nat) : Nat → St → List Nat → Nat → Nat
  | 0, _, _, _ => 0
  | fuel + 1, st, rest, td =>
    match st.stack with
    | [] => leakCount lm fuel st ⟨skipWs rest, td, false⟩
    | .num _ :: _ => leakCount lm fuel st ⟨skipWs rest, td, false⟩
    | .str x :: more =>
      if skipWs rest = [] then leakCount lm fuel { st with stack := more } ⟨x, td + 1, false⟩
      else
        let inner := leakCount lm fuel { st with stack := more } ⟨x, 1, false⟩
        match run lm fuel { st with stack := more } ⟨x, 1, false⟩ with
        | some (st', .ok) => inner + leakCount lm fuel st' ⟨skipWs rest, td, false⟩
        | _ => inner

end

/-- At most `k` leaking commands run in any prefix of `dc -e prog`. -/
def LeakBound (lm : Nat) (prog : List Nat) (k : Nat) : Prop :=
  ∀ n, leakCount lm n St.init ⟨prog, 1, false⟩ ≤ k

/-- The strings of a value. -/
def Val.strs : Val → List (List Nat)
  | .num _ => []
  | .str s => [s]

/-- Every string the state holds (stack, register values and arrays) is
shorter than `N`. -/
structure StrBound (N : Nat) (st : St) : Prop where
  stack : ∀ v ∈ st.stack, ∀ s ∈ v.strs, s.length < N
  regs : ∀ r, ∀ e ∈ st.regs r, (∀ v, e.val = some v → ∀ s ∈ v.strs, s.length < N) ∧
    ∀ iv ∈ e.arr, ∀ s ∈ iv.2.strs, s.length < N

end Dc
