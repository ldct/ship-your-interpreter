/-!
# GNU dc numbers

A model of the `bc_num` values of GNU bc 1.07.1 (`lib/number.c`) as used by
GNU dc 1.4.1: a sign flag, a magnitude and a scale, denoting
`(-1)^neg * mag / 10^scale`.

The sign is a separate flag, as in `bc_num`: every operation reproduces the
library's sign rule, including the cases where it leaves a negative zero
(`bc_raise` truncates by lowering `n_scale` without normalising the sign, so
`_.1 3^p` prints `-0`). Magnitudes are exact; every operation truncates
exactly where the C code truncates.

Everything here is structurally recursive so that the kernel can evaluate it.
-/

namespace Dc

/-- A `bc_num`: `(-1)^neg * mag / 10^scale`. -/
structure Num where
  neg : Bool
  mag : Nat
  scale : Nat
  deriving DecidableEq, Repr

namespace Num

/-- `_zero_` at a given scale. -/
def zero (s : Nat := 0) : Num := ⟨false, 0, s⟩

/-- `_one_`. -/
def one : Num := ⟨false, 1, 0⟩

/-- `bc_int2num`. -/
def ofInt (v : Int) : Num := ⟨decide (v < 0), v.natAbs, 0⟩

/-- `bc_is_zero`. -/
def isZero (n : Num) : Bool := n.mag == 0

/-- The magnitude rescaled to scale `s ≥ n.scale`. -/
def align (n : Num) (s : Nat) : Nat := n.mag * 10 ^ (s - n.scale)

/-- `_bc_do_compare` without signs: compares magnitudes as values. -/
def cmpMag (a b : Num) : Ordering :=
  let s := max a.scale b.scale
  compare (a.align s) (b.align s)

/-- `bc_compare`: signs first (a negative zero is below a positive zero),
then magnitudes. -/
def cmp (a b : Num) : Ordering :=
  if a.neg != b.neg then (if a.neg then .lt else .gt)
  else if a.neg then (cmpMag a b).swap else cmpMag a b

/-- `bc_add a b scale_min`. -/
def add (a b : Num) (smin : Nat) : Num :=
  let s := max smin (max a.scale b.scale)
  let A := a.align s
  let B := b.align s
  if a.neg == b.neg then ⟨a.neg, A + B, s⟩
  else match compare A B with
    | .lt => ⟨b.neg, B - A, s⟩
    | .eq => zero s
    | .gt => ⟨a.neg, A - B, s⟩

/-- `bc_sub a b scale_min`. -/
def sub (a b : Num) (smin : Nat) : Num :=
  let s := max smin (max a.scale b.scale)
  let A := a.align s
  let B := b.align s
  if a.neg != b.neg then ⟨a.neg, A + B, s⟩
  else match compare A B with
    | .lt => ⟨!b.neg, B - A, s⟩
    | .eq => zero s
    | .gt => ⟨a.neg, A - B, s⟩

/-- `bc_multiply a b scale`: the full product truncated to
`min (sa + sb) (max scale (max sa sb))` digits; a zero result is positive. -/
def mul (a b : Num) (k : Nat) : Num :=
  let full := a.scale + b.scale
  let ps := min full (max k (max a.scale b.scale))
  let m := a.mag * b.mag / 10 ^ (full - ps)
  ⟨if m == 0 then false else a.neg != b.neg, m, ps⟩

/-- `bc_divide a b scale`: the quotient truncated toward zero to `scale`
digits; `none` on division by zero. -/
def div (a b : Num) (k : Nat) : Option Num :=
  if b.mag == 0 then none
  else
    let q := a.mag * 10 ^ (b.scale + k) / (b.mag * 10 ^ a.scale)
    some ⟨if q == 0 then false else a.neg != b.neg, q, k⟩

/-- `bc_divmod a b scale`: quotient and remainder. -/
def divmod (a b : Num) (k : Nat) : Option (Num × Num) :=
  match div a b k with
  | none => none
  | some q =>
    let rs := max a.scale (b.scale + k)
    some (q, sub a (mul q b rs) rs)

/-- `bc_modulo`. -/
def modulo (a b : Num) (k : Nat) : Option Num := (divmod a b k).map (·.2)

/-- The integer part of the magnitude. -/
def intPart (n : Num) : Nat := n.mag / 10 ^ n.scale

/-- `LONG_MAX` as `lib/number.c` sees it: `h/number.h` defines it as
`0x7fffffff` when `<limits.h>` has not been included, which is the case in
`lib/number.c` (the arithmetic itself is done in a 64-bit `long`). -/
def longMax : Nat := 0x7fffffff

/-- `bc_num2long`: the truncated integer part, or `0` when the digit loop
(`while val <= LONG_MAX/BASE`) stops before the last digit, i.e. when the
integer part exceeds `10 * (LONG_MAX / 10) + 9 = 2147483649`. -/
def toLong (n : Num) : Int :=
  let i := n.intPart
  let v : Int := if i / 10 ≤ longMax / 10 then i else 0
  if n.neg then -v else v

/-- The C conversion `(int) l` of a `long` (two's complement, 32 bits). -/
def toInt32 (l : Int) : Int :=
  let m := l % 2 ^ 32
  if m < 2 ^ 31 then m else m - 2 ^ 32

/-- `dc_num2int`: `bc_num2long`, with `-1` when it returns `0` for a
nonzero value (overflow, and also every value strictly between -1 and 1),
narrowed to `int`. The flag reports the "overflows simple integer" message
(written to stderr). -/
def toInt (n : Num) : Int × Bool :=
  let r := n.toLong
  if r == 0 && !n.isZero then (-1, true) else (toInt32 r, false)

/-- `n ^ u` computed exactly (the repeated squaring of `bc_raise` never
truncates: every intermediate scale is the full scale). -/
def powExact (n : Num) (u : Nat) : Num :=
  let m := n.mag ^ u
  ⟨if m == 0 then false else n.neg && u % 2 == 1, m, n.scale * u⟩

/-- `n ^ u` as `bc_raise` holds it before the final truncation: `num1`
itself for `u = 1` (no product recomputes the sign, so a negative zero stays
negative), otherwise `powExact`. -/
def powRaise (n : Num) (u : Nat) : Num := if u = 1 then n else powExact n u

/-- `bc_raise a b scale`. Returns the result and whether the
"exponent too large" runtime error was reported. -/
def raise (a b : Num) (k : Nat) : Num × Bool :=
  let e := b.toLong
  if e == 0 then (one, b.intPart != 0)
  else if e < 0 then
    let t := powRaise a e.natAbs
    -- `bc_divide (_one_, temp, result, rscale)` leaves `result` (= `_zero_`)
    -- untouched when `temp` is zero.
    ((div one t k).getD (zero 0), false)
  else
    let u := e.natAbs
    let t := powRaise a u
    let rs := min (a.scale * u) (max k a.scale)
    (⟨t.neg, t.mag / 10 ^ (t.scale - rs), rs⟩, false)

/-- The loop of `bc_raisemod`: `fuel` bounds the iterations (the exponent
halves each time, so its value is enough). -/
def raisemodLoop (md : Num) (k rs : Nat) : Nat → Num → Num → Num → Num
  | 0, _, _, temp => temp
  | fuel + 1, ex, power, temp =>
    if ex.isZero then temp
    else
      let two : Num := ⟨false, 2, 0⟩
      let (ex', parity) := (divmod ex two 0).getD (ex, zero)
      let temp :=
        if parity.isZero then temp
        else ((modulo (mul temp power rs) md k).getD temp)
      let power := (modulo (mul power power rs) md k).getD power
      raisemodLoop md k rs fuel ex' power temp

/-- `bc_raisemod base expo mod scale`; `none` for a zero modulus or a
negative exponent. -/
def raisemod (base ex md : Num) (k : Nat) : Option Num :=
  if md.isZero then none
  else if ex.neg then none
  else
    let ex := if ex.scale != 0 then (div ex one 0).getD ex else ex
    let rs := max k base.scale
    some (raisemodLoop md k rs (ex.intPart + 1) ex base one)

/-- Digits of `n` in base `b ≥ 2`, most significant first (`[]` for `0`);
`fuel` bounds the number of digits. -/
def digitsIn (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n => if n == 0 then [] else digitsIn b fuel (n / b) ++ [n % b]

/-- Digits of `n` in base `b`, with `n + 1` as fuel. -/
def digits (b n : Nat) : List Nat := digitsIn b (n + 1) n

/-! ## Square root (`bc_sqrt`)

The Newton iteration is not structurally terminating; the semantics
(`Dc.Semantics`) describes it by the relation `SqrtLoop`, and the executable
interpreter runs `sqrtLoopFuel`. Both share the step functions below. -/

/-- `bc_is_near_zero n scale`: the magnitude truncated to
`min scale n.scale` fraction digits is `0` or `1` (one unit in the last
place). -/
def isNearZero (n : Num) (s : Nat) : Bool :=
  let s := min s n.scale
  n.mag / 10 ^ (n.scale - s) ≤ 1

/-- `0.5`. -/
def half : Num := ⟨false, 5, 1⟩

/-- One Newton step: `(num / guess + guess) * 0.5` at `cscale`, and the
difference with the previous guess at `cscale + 1`. -/
def sqrtStep (x guess : Num) (cscale : Nat) : Num × Num :=
  let g := (div x guess cscale).getD guess
  let g := add g guess 0
  let g := mul g half cscale
  (g, sub g guess (cscale + 1))

/-- The number of integer digits `n_len` of a normalised `bc_num`. -/
def intLen (n : Num) : Nat := max 1 (digits 10 n.intPart).length

/-- The initial guess and working scale of `bc_sqrt` for `x > 1`
(`10 ^ (n_len / 2)`, scale 3) or `0 < x < 1` (`1`, `x.scale`). -/
def sqrtInit (x : Num) : Num × Nat :=
  if cmp x one == .lt then (one, x.scale)
  else ((raise ⟨false, 10, 0⟩ ⟨false, x.intLen / 2, 0⟩ 0).1, 3)

/-- The final truncation `bc_divide (guess, _one_, num, rscale)`. -/
def sqrtFinish (guess : Num) (rs : Nat) : Num := (div guess one rs).getD guess

/-- The executable Newton loop (`none` when the fuel runs out). -/
def sqrtLoopFuel (x : Num) (rs : Nat) : Nat → Num → Nat → Option Num
  | 0, _, _ => none
  | fuel + 1, guess, cscale =>
    if (sqrtStep x guess cscale).2.isNearZero cscale then
      if cscale < rs + 1 then
        sqrtLoopFuel x rs fuel (sqrtStep x guess cscale).1 (min (cscale * 3) (rs + 1))
      else some (sqrtFinish (sqrtStep x guess cscale).1 rs)
    else sqrtLoopFuel x rs fuel (sqrtStep x guess cscale).1 cscale

/-! ## Output (`bc_out_num`, `dc_dump_num`) -/

/-- ASCII of a decimal digit. -/
def decChar (d : Nat) : Nat := 48 + d

/-- `ref_str[d]` = `"0123456789ABCDEF"[d]`. -/
def hexChar (d : Nat) : Nat := if d < 10 then 48 + d else 55 + d

/-- Decimal text of a natural number (`%ld` of a nonnegative value). -/
def decText (n : Nat) : List Nat :=
  match digits 10 n with
  | [] => [48]
  | ds => ds.map decChar

/-- `bc_out_long val size space`: an optional space, then `val` zero-padded
to `size` digits. -/
def outLong (v size : Nat) (space : Bool) : List Nat :=
  let t := decText v
  (if space then [32] else []) ++ List.replicate (size - t.length) 48 ++ t

/-- The fraction digits of the non-decimal branch: while `t = base^i` has at
most `scale` decimal digits, multiply the fraction by the base and emit its
integer part. `fuel` bounds the iterations. -/
def fracDigits (base scale : Nat) : Nat → Num → Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, frac, t =>
    if (decText t).length ≤ scale then
      let f := mul frac ⟨false, base, 0⟩ scale
      let d := f.toLong.natAbs
      d :: fracDigits base scale fuel (sub f (ofInt d) 0) (t * base)
    else []

/-- The characters `bc_out_num` writes for `n` in base `obase`, before line
wrapping (`leading_zero` is `0` in dc). -/
def outChars (n : Num) (obase : Nat) : List Nat :=
  let sign := if n.neg then [45] else []
  if n.isZero then sign ++ [48]
  else if obase == 10 then
    let ip := n.intPart
    let fp := n.mag % 10 ^ n.scale
    let intDs := if ip == 0 then [] else (digits 10 ip).map decChar
    let fracDs :=
      if n.scale == 0 then []
      else 46 :: (List.replicate (n.scale - (digits 10 fp).length) 0 ++ digits 10 fp).map decChar
    sign ++ intDs ++ fracDs
  else
    let ipN := (div n one 0).getD n
    let fpN := sub n ipN 0
    let width := (decText (obase - 1)).length
    let digit (d : Nat) (space : Bool) : List Nat :=
      if obase ≤ 16 then [hexChar d] else outLong d width space
    let intDs := (digits obase ipN.mag).flatMap (digit · true)
    let fracDs :=
      if n.scale == 0 then []
      else
        let ds := fracDigits obase n.scale (4 * n.scale + 4) { fpN with neg := false } 1
        46 :: (ds.zipIdx.flatMap fun (d, i) => digit d (i != 0))
    sign ++ intDs ++ fracDs

/-- `out_char` line wrapping: the column restarts at each number; when the
incremented column reaches `lm` (and `lm ≠ 0`), emit `\` newline first. -/
def wrap (lm : Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | col, c :: cs =>
    if lm != 0 && col + 1 ≥ lm then 92 :: 10 :: c :: wrap lm 1 cs
    else c :: wrap lm (col + 1) cs

/-- `dc_out_num`: the bytes written for a number. -/
def out (lm obase : Nat) (n : Num) : List Nat := wrap lm 0 (outChars n obase)

/-- `dc_dump_num` (command `P` on a number): the absolute integer part as
base-256 bytes, most significant first, at least one byte. -/
def dump (n : Num) : List Nat :=
  match digits 256 n.intPart with
  | [] => [0]
  | ds => ds

/-- `dc_numlen` (command `Z` on a number): the number of significant digits,
at least one. -/
def numLen (n : Num) : Nat := max 1 (digits 10 n.mag).length

end Num

end Dc
