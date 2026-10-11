import Dc.Num

/-!
# The dc machine and its primitive commands

The state of GNU dc 1.4.1 (`dc/stack.c`, `dc/array.c`, `dc/eval.c` globals)
and `dcFunc`, a transcription of `dc_func` (`dc/eval.c`): the effect of one
command character given the lookahead character, returning the `dc_status`
that tells the evaluation loop what to do next.

The environment is the bare-metal build (`dc-port/`): standard input is
at end of file and there is no command processor (`system` fails).
Only standard output is modelled. Messages written to standard error
(stack empty, divide by zero, ...) leave no trace except their effect on the
state. The `unimplemented` diagnostic is split by dc itself: `dc: ` goes to
stderr and `'y' (0171) unimplemented` to stdout, so the latter is output here.

Bytes are natural numbers below 256.
-/

namespace Dc

/-- A dc datum (`dc_data`): a number or a byte string. -/
inductive Val where
  | num (n : Num)
  | str (s : List Nat)
  deriving DecidableEq, Repr

/-- One level of a register stack (`dc_list`): its value (absent when the
level was created by storing into the array of an empty register) and its
array, a list of index/value pairs sorted by index (`dc_array`). -/
structure Entry where
  val : Option Val
  arr : List (Nat × Val)
  deriving DecidableEq, Repr

/-- The machine state. `regs r` is register `r`'s stack, top first. -/
structure St where
  stack : List Val
  regs : Nat → List Entry
  ibase : Nat
  obase : Nat
  scale : Nat
  /-- `unwind_depth` -/
  unwind : Nat
  /-- `unwind_noexit` -/
  noexit : Bool
  /-- bytes written to standard output -/
  out : List Nat

/-- The state at program start. -/
def St.init : St :=
  ⟨[], fun _ => [], 10, 10, 0, 0, false, []⟩

namespace St

def push (st : St) (v : Val) : St := { st with stack := v :: st.stack }

def emit (st : St) (bs : List Nat) : St := { st with out := st.out ++ bs }

def setReg (st : St) (r : Nat) (l : List Entry) : St :=
  { st with regs := fun q => if q = r then l else st.regs q }

end St

/-- `dc_print` of a datum without newline. -/
def Val.out (lm obase : Nat) : Val → List Nat
  | .num n => n.out lm obase
  | .str s => s

/-- The result of `dc_func`. -/
inductive Res where
  /-- `DC_OKAY` -/
  | ok (st : St)
  /-- `DC_EATONE`: skip the lookahead character -/
  | eatOne (st : St)
  /-- `DC_EVALREG`: evaluate register `r` (the lookahead character) -/
  | evalReg (st : St) (r : Nat)
  /-- `DC_EVALTOS` -/
  | evalTos (st : St)
  /-- `DC_QUIT` -/
  | quit (st : St)
  /-- `DC_INT`: read a number starting at this character -/
  | int
  /-- `DC_STR`: read a bracketed string -/
  | str
  /-- `DC_COMMENT` -/
  | comment
  /-- `DC_NEGCMP` -/
  | negcmp
  /-- `DC_EOF_ERROR`: the command needs a lookahead character -/
  | eofError
  /-- `v` on a positive number other than one: run the Newton iteration of
  `bc_sqrt` (the number has been popped) -/
  | sqrt (st : St) (x : Num)
  /-- `DC_SYSTEM`: `!` not followed by a comparison: run the rest of the
  line as a shell command -/
  | system

/-! ## Stack and register primitives -/

/-- `dc_stack_rotate n`. The machine takes `|n|` in 32 bits, so
`n = -2^31` stays negative and leaves the stack unchanged. -/
def rotate (n : Int) (s : List Val) : List Val :=
  let absn := n.natAbs
  if s.isEmpty || absn < 2 || n == -2147483648 then s
  else
    let i := min (absn - 1) (s.length - 1)
    if i == 0 then s
    else if n > 0 then
      match s[i]? with
      | some p => p :: s.eraseIdx i
      | none => s
    else
      match s with
      | top :: rest => rest.take i ++ top :: rest.drop i
      | [] => s

/-- `dc_register_get`: `some (num 0)` for an empty register, `none` for a
level without value (dc reports a bug and pushes nothing). -/
def regGet (st : St) (r : Nat) : Option Val :=
  match st.regs r with
  | [] => some (.num (Num.zero 0))
  | e :: _ => e.val

/-- `dc_register_set`: replace the top level's value, keeping its array. -/
def regSet (st : St) (r : Nat) (v : Val) : St :=
  match st.regs r with
  | [] => st.setReg r [⟨some v, []⟩]
  | e :: es => st.setReg r ({ e with val := some v } :: es)

/-- Insert into a sorted array (`dc_array_set`). -/
def arrSet (i : Nat) (v : Val) : List (Nat × Val) → List (Nat × Val)
  | [] => [(i, v)]
  | (j, w) :: rest =>
    if j < i then (j, w) :: arrSet i v rest
    else if j == i then (i, v) :: rest
    else (i, v) :: (j, w) :: rest

/-- `dc_array_set` on register `r`'s top level (created without value when
the register is empty). -/
def arraySet (st : St) (r i : Nat) (v : Val) : St :=
  match st.regs r with
  | [] => st.setReg r [⟨none, [(i, v)]⟩]
  | e :: es => st.setReg r ({ e with arr := arrSet i v e.arr } :: es)

/-- `dc_array_get`: the stored value, or `0`. -/
def arrayGet (st : St) (r i : Nat) : Val :=
  let arr := match st.regs r with
    | [] => []
    | e :: _ => e.arr
  match arr.find? (·.1 == i) with
  | some (_, v) => v
  | none => .num (Num.zero 0)

/-- `dc_binop`: pop two numbers, push `f a b`; leave the stack unchanged if
there are fewer than two numbers on top or `f` fails. -/
def binop (st : St) (f : Num → Num → Option Num) : St :=
  match st.stack with
  | .num b :: .num a :: rest =>
    match f a b with
    | some r => { st with stack := .num r :: rest }
    | none => st
  | _ => st

/-- `dc_binop2`: push both results, first then second. -/
def binop2 (st : St) (f : Num → Num → Option (Num × Num)) : St :=
  match st.stack with
  | .num b :: .num a :: rest =>
    match f a b with
    | some (q, r) => { st with stack := .num r :: .num q :: rest }
    | none => st
  | _ => st

/-- `dc_triop`. -/
def triop (st : St) (f : Num → Num → Num → Option Num) : St :=
  match st.stack with
  | .num c :: .num b :: .num a :: rest =>
    match f a b c with
    | some r => { st with stack := .num r :: rest }
    | none => st
  | _ => st

/-- `dc_cmpop`: compare top with second and pop both; with fewer than two
numbers on top, pop nothing and report equality. -/
def cmpop (st : St) : Ordering × St :=
  match st.stack with
  | .num b :: .num a :: rest => (Num.cmp b a, { st with stack := rest })
  | _ => (.eq, st)

/-- `dc_num2int` of a datum, with the default used for a string. -/
def valInt (dflt : Int) : Val → Int
  | .num n => n.toInt.1
  | .str _ => dflt

/-- `isgraph` in the C locale. -/
def isGraph (c : Nat) : Bool := 33 ≤ c && c ≤ 126

/-- `printf("%#o", c)`. -/
def octAlt (c : Nat) : List Nat :=
  if c == 0 then [48] else 48 :: (Num.digits 8 c).map Num.decChar

/-- The part of the `unimplemented` diagnostic written to stdout
(`dc_show_id (stdout, c, " unimplemented\n")`). -/
def unimplemented (c : Nat) : List Nat :=
  -- " unimplemented\n"
  let msg := [32, 117, 110, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 10]
  if isGraph c then [39, c, 39, 32, 40] ++ octAlt c ++ [41] ++ msg
  else octAlt c ++ msg

/-- `dc_func c peekc negcmp` (`dc/eval.c`). `lm` is the line length
(`DC_LINE_LENGTH`; `0` disables wrapping). -/
def dcFunc (lm : Nat) (st : St) (c : Nat) (peek : Option Nat) (neg : Bool) : Res :=
  let k := st.scale
  let pop : Option (Val × St) := match st.stack with
    | v :: rest => some (v, { st with stack := rest })
    | [] => none
  -- a comparison command: evaluate register `peek` when the test holds
  let cmpCmd (test : Ordering → Bool) : Res :=
    match peek with
    | none => .eofError
    | some r =>
      let (o, st') := cmpop st
      if test o == !neg then .evalReg st' r else .eatOne st'
  match c with
  -- digits, `_`, `.`, `A`-`F`: a number
  | 95 | 46 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57
  | 65 | 66 | 67 | 68 | 69 | 70 => .int
  | 32 | 9 | 10 => .ok st
  | 43 => .ok (binop st fun a b => some (Num.add a b 0))          -- +
  | 45 => .ok (binop st fun a b => some (Num.sub a b 0))          -- -
  | 42 => .ok (binop st fun a b => some (Num.mul a b k))          -- *
  | 47 => .ok (binop st fun a b => Num.div a b k)                 -- /
  | 37 => .ok (binop st fun a b => Num.modulo a b k)              -- %
  | 126 => .ok (binop2 st fun a b => Num.divmod a b k)            -- ~
  | 124 => .ok (triop st fun a b m => Num.raisemod a b m k)       -- |
  | 94 => .ok (binop st fun a b => some (Num.raise a b k).1)      -- ^
  | 60 => cmpCmd (· == .lt)                                       -- <
  | 61 => cmpCmd (· == .eq)                                       -- =
  | 62 => cmpCmd (· == .gt)                                       -- >
  -- ?: `dc_readstring (stdin, '\n', '\n')` reads the empty line at end of
  -- file (the bare-metal build has no console input), and evaluates it
  | 63 => .evalTos (st.push (.str []))
  | 91 => .str                                                    -- [
  | 33 =>                                                         -- !
    if peek == some 60 || peek == some 61 || peek == some 62 then .negcmp
    else .system
  | 35 => .comment                                                -- #
  | 97 =>                                                         -- a
    match pop with
    | some (v, st') =>
      let b := match v with
        | .num n => (n.toInt.1 % 256).toNat
        | .str s => s.headD 0
      .ok (st'.push (.str [b]))
    | none => .ok st
  | 99 => .ok { st with stack := [] }                             -- c
  | 100 =>                                                        -- d
    match st.stack with
    | v :: _ => .ok (st.push v)
    | [] => .ok st
  | 102 =>                                                        -- f
    .ok (st.emit (st.stack.flatMap fun v => v.out lm st.obase ++ [10]))
  | 105 =>                                                        -- i
    match pop with
    | some (v, st') =>
      let t := valInt 0 v
      .ok (if 2 ≤ t && t ≤ 16 then { st' with ibase := t.toNat } else st')
    | none => .ok st
  | 107 =>                                                        -- k
    match pop with
    | some (v, st') =>
      let t := valInt (-1) v
      .ok (if 0 ≤ t then { st' with scale := t.toNat } else st')
    | none => .ok st
  | 108 =>                                                        -- l
    match peek with
    | none => .eofError
    | some r =>
      match regGet st r with
      | some v => .eatOne (st.push v)
      | none => .eatOne st
  | 110 =>                                                        -- n
    match pop with
    | some (v, st') => .ok (st'.emit (v.out lm st.obase))
    | none => .ok st
  | 111 =>                                                        -- o
    match pop with
    | some (v, st') =>
      let t := valInt 0 v
      .ok (if 1 < t then { st' with obase := t.toNat } else st')
    | none => .ok st
  | 112 =>                                                        -- p
    match st.stack with
    | v :: _ => .ok (st.emit (v.out lm st.obase ++ [10]))
    | [] => .ok st
  | 113 => .quit { st with unwind := 1, noexit := false }         -- q
  | 114 => .ok { st with stack := rotate 2 st.stack }             -- r
  | 115 =>                                                        -- s
    match peek with
    | none => .eofError
    | some r =>
      match pop with
      | some (v, st') => .eatOne (regSet st' r v)
      | none => .eatOne st
  | 118 =>                                                        -- v
    match pop with
    | some (.num x, st') =>
      match Num.cmp x (Num.zero 0) with
      | .lt => .ok st'                     -- square root of negative number
      | .eq => .ok (st'.push (.num (Num.zero 0)))
      | .gt =>
        if Num.cmp x Num.one == .eq then .ok (st'.push (.num Num.one))
        else .sqrt st' x
    | some (.str _, st') => .ok st'        -- square root of nonnumeric
    | none => .ok st
  | 120 => .evalTos st                                            -- x
  | 122 => .ok (st.push (.num (Num.ofInt st.stack.length)))       -- z
  | 73 => .ok (st.push (.num (Num.ofInt st.ibase)))               -- I
  | 75 => .ok (st.push (.num (Num.ofInt st.scale)))               -- K
  | 76 =>                                                         -- L
    match peek with
    | none => .eofError
    | some r =>
      match st.regs r with
      | ⟨some v, _⟩ :: es => .eatOne ((st.setReg r es).push v)
      | _ => .eatOne st
  | 79 => .ok (st.push (.num (Num.ofInt st.obase)))               -- O
  | 80 =>                                                         -- P
    match pop with
    | some (.num n, st') => .ok (st'.emit n.dump)
    | some (.str s, st') => .ok (st'.emit s)
    | none => .ok st
  | 81 =>                                                         -- Q
    match pop with
    | some (v, st') =>
      let ud := valInt 0 v
      if 0 < ud then .quit { st' with unwind := (ud - 1).toNat, noexit := true }
      else .ok { st' with unwind := 0, noexit := true }
    | none => .ok st
  | 82 =>                                                         -- R
    match pop with
    | some (v, st') => .ok { st' with stack := rotate (valInt 0 v) st'.stack }
    | none => .ok st
  | 83 =>                                                         -- S
    match peek with
    | none => .eofError
    | some r =>
      match pop with
      | some (v, st') => .eatOne (st'.setReg r (⟨some v, []⟩ :: st'.regs r))
      | none => .eatOne st
  | 88 =>                                                         -- X
    match pop with
    | some (.num n, st') => .ok (st'.push (.num (Num.ofInt n.scale)))
    | some (.str _, st') => .ok (st'.push (.num (Num.zero 0)))
    | none => .ok st
  | 90 =>                                                         -- Z
    match pop with
    | some (.num n, st') => .ok (st'.push (.num (Num.ofInt n.numLen)))
    | some (.str s, st') => .ok (st'.push (.num (Num.ofInt s.length)))
    | none => .ok st
  | 58 =>                                                         -- :
    match peek with
    | none => .eofError
    | some r =>
      match pop with
      | some (iv, st') =>
        let t := valInt (-1) iv
        match st'.stack with
        | v :: rest =>
          let st'' := { st' with stack := rest }
          .eatOne (if t < 0 then st'' else arraySet st'' r t.toNat v)
        | [] => .eatOne st'
      | none => .eatOne st
  | 59 =>                                                         -- ;
    match peek with
    | none => .eofError
    | some r =>
      match pop with
      | some (iv, st') =>
        let t := valInt (-1) iv
        .eatOne (if t < 0 then st' else st'.push (arrayGet st' r t.toNat))
      | none => .eatOne st
  | _ => .ok (st.emit (unimplemented c))

/-! ## Reading numbers and strings (`dc_getnum`, the `DC_STR` scan) -/

/-- `isspace` in the C locale. -/
def isSpace (c : Nat) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

/-- The digit value of `0`-`9`, `A`-`F` (accepted in every input base). -/
def digitVal (c : Nat) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else none

/-- The maximal prefix of digits: their values and the rest. -/
def takeDigits : List Nat → List Nat × List Nat
  | [] => ([], [])
  | c :: cs =>
    match digitVal c with
    | some d => let (ds, r) := takeDigits cs; (d :: ds, r)
    | none => ([], c :: cs)

/-- The value of a digit string in base `b`. -/
def ofDigits (b : Nat) (ds : List Nat) : Nat := ds.foldl (fun r d => r * b + d) 0

/-- `dc_getnum` in input base `ib`, reading from `s` (which starts with a
digit, `_` or `.`); returns the number and the input left at the first
character not consumed. -/
def readNum (ib : Nat) (s : List Nat) : Num × List Nat :=
  let (neg, s) := match s with
    | 95 :: rest => (true, rest.dropWhile isSpace)
    | _ => (false, s)
  let (ids, s) := takeDigits s
  let ip : Num := ⟨false, ofDigits ib ids, 0⟩
  let (n, s) := match s with
    | 46 :: rest =>
      let (fds, s') := takeDigits rest
      let dec := fds.length
      let build : Num := ⟨false, ofDigits ib fds, 0⟩
      let frac := (Num.div build ⟨false, ib ^ dec, 0⟩ dec).getD (Num.zero dec)
      (Num.add ip frac 0, s')
    | _ => (ip, s)
  ((if neg then Num.sub (Num.zero 0) n 0 else n), s)

/-- The `DC_STR` scan from just after `[`: the bracket-balanced contents and
the rest (an unbalanced string takes everything). -/
def scanStr : Nat → List Nat → List Nat × List Nat
  | _, [] => ([], [])
  | depth, c :: cs =>
    if c == 93 then
      if depth == 1 then ([], cs)
      else let (b, r) := scanStr (depth - 1) cs; (c :: b, r)
    else if c == 91 then let (b, r) := scanStr (depth + 1) cs; (c :: b, r)
    else let (b, r) := scanStr depth cs; (c :: b, r)

/-- `dc_system`: the command runs to the first newline, which is consumed,
or to the first NUL byte (`strchr` stops there), which is not. -/
def skipSys : List Nat → List Nat
  | [] => []
  | c :: cs => if c == 10 then cs else if c == 0 then c :: cs else skipSys cs

/-- `skip_past_eol`. -/
def skipEol : List Nat → List Nat
  | [] => []
  | c :: cs => if c == 10 then cs else skipEol cs

/-- The whitespace and comment skip before `DC_EVALTOS` evaluates; `fuel`
bounds the characters examined. -/
def skipWsF : Nat → List Nat → List Nat
  | 0, s => s
  | _, [] => []
  | fuel + 1, c :: cs =>
    if c == 32 || c == 9 || c == 10 then skipWsF fuel cs
    else if c == 35 then skipWsF fuel (skipEol cs)
    else c :: cs

/-- The whitespace and comment skip, with the input length as fuel (each
step consumes at least one character). -/
def skipWs (s : List Nat) : List Nat := skipWsF s.length s

end Dc
