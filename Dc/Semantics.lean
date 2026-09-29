import Dc.Machine

/-!
# Big-step semantics of GNU dc

The evaluation of a dc program given with `dc -e PROGRAM`: `main` calls
`dc_evalstr`, i.e. `evalstr` (`dc/eval.c`) on the program text. `evalstr`
scans its string one command at a time, dispatches through `dc_func`
(`Dc.dcFunc`), and handles the returned status: reading numbers and strings,
skipping comments, negated comparisons, and evaluating strings, which
recurses into `evalstr` except in tail position, where the current string is
replaced and `tail_depth` incremented. `q` and `Q` unwind through
`unwind_depth` and `tail_depth` exactly as the C code does.

`Loop lm st f st' r` says: evaluating the frame `f` (the unread rest of the
string, its `tail_depth`, and the pending `!` flag) from state `st`
terminates in state `st'` with status `r`. `lm` is the output line length.
Programs that do not terminate, and programs that reach `!` (shell escape)
or `?` (read a line from stdin), have no derivation.
-/

namespace Dc

/-- The status `evalstr` returns. -/
inductive Status where
  | ok
  | quit
  deriving DecidableEq, Repr

/-- The local state of one `evalstr` activation. -/
structure Frame where
  /-- the unread characters (`s` up to `end`) -/
  s : List Nat
  /-- `tail_depth` -/
  td : Nat
  /-- `next_negcmp` -/
  neg : Bool

/-- The Newton iteration of `bc_sqrt` for `x` at result scale `rs`, from a
guess and working scale to the returned square root. -/
inductive SqrtLoop (x : Num) (rs : Nat) : Num → Nat → Num → Prop
  | finish {guess cs} :
      (Num.sqrtStep x guess cs).2.isNearZero cs = true → ¬ cs < rs + 1 →
      SqrtLoop x rs guess cs (Num.sqrtFinish (Num.sqrtStep x guess cs).1 rs)
  | refine {guess cs r} :
      (Num.sqrtStep x guess cs).2.isNearZero cs = true → cs < rs + 1 →
      SqrtLoop x rs (Num.sqrtStep x guess cs).1 (min (cs * 3) (rs + 1)) r →
      SqrtLoop x rs guess cs r
  | iterate {guess cs r} :
      (Num.sqrtStep x guess cs).2.isNearZero cs = false →
      SqrtLoop x rs (Num.sqrtStep x guess cs).1 cs r →
      SqrtLoop x rs guess cs r

/-- `bc_sqrt x k` for `x > 0`, `x ≠ 1`. -/
def Sqrt (x : Num) (k : Nat) (r : Num) : Prop :=
  SqrtLoop x (max k x.scale) (Num.sqrtInit x).1 (Num.sqrtInit x).2 r

mutual

/-- One `evalstr` activation, from its current frame to its return. -/
inductive Loop (lm : Nat) : St → Frame → St → Status → Prop
  /-- `s == end`: the loop exits. -/
  | done {st td neg} : Loop lm st ⟨[], td, neg⟩ st .ok
  /-- `DC_OKAY` -/
  | ok {st st' st'' c rest td neg r} :
      dcFunc lm st c rest.head? neg = .ok st' →
      Loop lm st' ⟨rest, td, false⟩ st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r
  /-- `DC_EATONE`: also skip the lookahead character. -/
  | eatOne {st st' st'' c rest td neg r} :
      dcFunc lm st c rest.head? neg = .eatOne st' →
      Loop lm st' ⟨rest.tail, td, false⟩ st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r
  /-- `DC_EVALREG` with a register holding a value (`0` if empty): push it
  and evaluate the top of stack. -/
  | evalReg {st st' st'' c rest td neg reg v r} :
      dcFunc lm st c rest.head? neg = .evalReg st' reg →
      regGet st' reg = some v →
      Tos lm (st'.push v) rest.tail td st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r
  /-- `DC_EVALREG` on a register level without value: nothing happens. -/
  | evalRegNone {st st' st'' c rest td neg reg r} :
      dcFunc lm st c rest.head? neg = .evalReg st' reg →
      regGet st' reg = none →
      Loop lm st' ⟨rest.tail, td, false⟩ st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r
  /-- `DC_EVALTOS` (command `x`). -/
  | evalTos {st st' st'' c rest td neg r} :
      dcFunc lm st c rest.head? neg = .evalTos st' →
      Tos lm st' rest td st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r
  /-- `DC_QUIT` reaching past this activation. -/
  | quitOut {st st' c rest td neg} :
      dcFunc lm st c rest.head? neg = .quit st' →
      td ≤ st'.unwind →
      Loop lm st ⟨c :: rest, td, neg⟩ { st' with unwind := st'.unwind - td } .quit
  /-- `DC_QUIT` absorbed by tail-recursion levels: continue. -/
  | quitStay {st st' st'' c rest td neg r} :
      dcFunc lm st c rest.head? neg = .quit st' →
      st'.unwind < td →
      Loop lm st' ⟨rest, td - st'.unwind, false⟩ st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r
  /-- `DC_INT`: read a number in the current input base. -/
  | int {st st'' c rest td neg r} :
      dcFunc lm st c rest.head? neg = .int →
      Loop lm (st.push (.num (readNum st.ibase (c :: rest)).1))
        ⟨(readNum st.ibase (c :: rest)).2, td, false⟩ st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r
  /-- `DC_STR`: read a bracketed string. -/
  | str {st st'' c rest td neg r} :
      dcFunc lm st c rest.head? neg = .str →
      Loop lm (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩ st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r
  /-- `DC_COMMENT` -/
  | comment {st st'' c rest td neg r} :
      dcFunc lm st c rest.head? neg = .comment →
      Loop lm st ⟨skipEol rest, td, false⟩ st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r
  /-- `DC_NEGCMP`: the next command's comparison is negated. -/
  | negcmp {st st'' c rest td neg r} :
      dcFunc lm st c rest.head? neg = .negcmp →
      Loop lm st ⟨rest, td, true⟩ st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r
  /-- `DC_EOF_ERROR` ("unexpected EOS"): this activation returns. -/
  | eofError {st c rest td neg} :
      dcFunc lm st c rest.head? neg = .eofError →
      Loop lm st ⟨c :: rest, td, neg⟩ st .ok
  /-- `v`: the square root by `bc_sqrt`'s Newton iteration. -/
  | sqrt {st st' st'' c rest td neg x y r} :
      dcFunc lm st c rest.head? neg = .sqrt st' x →
      Sqrt x st'.scale y →
      Loop lm (st'.push (.num y)) ⟨rest, td, false⟩ st'' r →
      Loop lm st ⟨c :: rest, td, neg⟩ st'' r

/-- The `DC_EVALTOS` code of `evalstr`: skip whitespace and comments, pop
the top of stack and evaluate it. `Tos lm st rest td st' r`: `rest` is the
input after the command, `td` the activation's `tail_depth`. -/
inductive Tos (lm : Nat) : St → List Nat → Nat → St → Status → Prop
  /-- Empty stack: continue. -/
  | empty {st st'' rest td r} :
      st.stack = [] →
      Loop lm st ⟨skipWs rest, td, false⟩ st'' r →
      Tos lm st rest td st'' r
  /-- A number is pushed back: continue. -/
  | num {st st'' rest td n more r} :
      st.stack = .num n :: more →
      Loop lm st ⟨skipWs rest, td, false⟩ st'' r →
      Tos lm st rest td st'' r
  /-- A string in tail position replaces the current one. -/
  | tail {st st'' rest td x more r} :
      st.stack = .str x :: more →
      skipWs rest = [] →
      Loop lm { st with stack := more } ⟨x, td + 1, false⟩ st'' r →
      Tos lm st rest td st'' r
  /-- A string elsewhere is evaluated by a nested `evalstr`, which returns
  normally: continue. -/
  | callOk {st st' st'' rest td x more r} :
      st.stack = .str x :: more →
      skipWs rest ≠ [] →
      Loop lm { st with stack := more } ⟨x, 1, false⟩ st' .ok →
      Loop lm st' ⟨skipWs rest, td, false⟩ st'' r →
      Tos lm st rest td st'' r
  /-- The nested evaluation quit with levels left to unwind: return `quit`
  with one level fewer. -/
  | callQuitUp {st st' rest td x more} :
      st.stack = .str x :: more →
      skipWs rest ≠ [] →
      Loop lm { st with stack := more } ⟨x, 1, false⟩ st' .quit →
      0 < st'.unwind →
      Tos lm st rest td { st' with unwind := st'.unwind - 1 } .quit
  /-- The nested evaluation quit with no level left: this activation
  returns normally. -/
  | callQuitStop {st st' rest td x more} :
      st.stack = .str x :: more →
      skipWs rest ≠ [] →
      Loop lm { st with stack := more } ⟨x, 1, false⟩ st' .quit →
      st'.unwind = 0 →
      Tos lm st rest td st' .ok

end

/-- `dc -e prog` terminates, having written `out` to standard output. -/
def Runs (lm : Nat) (prog : List Nat) (out : List Nat) : Prop :=
  ∃ st r, Loop lm St.init ⟨prog, 1, false⟩ st r ∧ st.out = out

end Dc
