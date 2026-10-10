import Dc.Mach.DcFuncSpec
import Dc.Mach.EvalLeak
import Dc.Adequacy

/-!
# `evalstr`: the loop invariant and the statements (M10)

`evalstr (dc_data *string)` (`0x80001448`, 176-byte frame) evaluates the
string `*string` one command at a time. Its loop head is `0x800014f8`, with
`s` in `s0`, `end` in `s1`, `next_negcmp` in `a2`, `tail_depth` in `s8`,
`string` in `s6`, the two status jump tables in `s2`/`s3` and the
constants `10`/`-1` in `s4`/`s5` (`EvConsts`); `ra` and `s0`–`s9` are saved
at `sp - 176 + 168 … 88` (`evSaved`).

`EvAt … f o`: the machine at the loop head represents the frame
`f = ⟨s, td, neg⟩` over the string object `o` held by the caller's handle
(`hs.head? = some (.str o.hb.pay)`, the datum at `q = s6`), `s` being the
rest of `o.s` from `s0`. The state is `DcAt` over the handles `xs ++ hs`,
`xs` the strings lost by the commands run so far; the lost references and
strings and the leak budget fit the handle and reference bounds together
(`budget`). The model-side budgets
are carried with it: the nesting depth `d` (each nested `evalstr` takes 176
more bytes, `nestDepth`), the leaking commands `k` (`leakCount`), and the
per-call premises of `dc_func` (`FnSize`, the SizeBound) for every call the
evaluation makes (`AllCalls`).

`EvPost`/`EvK`: an activation returns to its caller's `ra` with `a0` the
status (`DC_OKAY = 0`, `DC_QUIT = 4`), `s0`–`s9`, `sp` restored, and the
state `st'` over `xs' ++ .str p' :: hs.tail`, where `p'` is the string in
`*string` now (a tail call replaces it), `G'.lk` and `xs'` grown by at most
four per leaking command.

The statements (`EvLoopSpec` at the loop head, `EvTosSpec` at the
`DC_EVALTOS` code, `EvalstrSpec` at the entry) are given as
propositions here, for review; their proofs (by induction on `Loop`/`Tos`)
follow in `Eval*.lean`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Model-side budgets -/

mutual

/-- Every `dc_func` call within the first `n` steps of `run lm n st f`
meets `P st c peek` (the state, the command, the lookahead). -/
def AllCalls (lm : Nat) (P : St → Nat → Option Nat → Prop) : Nat → St → Frame → Prop
  | 0, _, _ => True
  | _ + 1, _, ⟨[], _, _⟩ => True
  | fuel + 1, st, ⟨c :: rest, td, neg⟩ =>
    P st c rest.head? ∧
    match dcFunc lm st c rest.head? neg with
    | .ok st' => AllCalls lm P fuel st' ⟨rest, td, false⟩
    | .eatOne st' => AllCalls lm P fuel st' ⟨rest.tail, td, false⟩
    | .evalReg st' reg =>
      match regGet st' reg with
      | some v => TosCalls lm P fuel (st'.push v) rest.tail td
      | none => AllCalls lm P fuel st' ⟨rest.tail, td, false⟩
    | .evalTos st' => TosCalls lm P fuel st' rest td
    | .quit st' =>
      if td ≤ st'.unwind then True else AllCalls lm P fuel st' ⟨rest, td - st'.unwind, false⟩
    | .int =>
      AllCalls lm P fuel (st.push (.num (readNum st.ibase (c :: rest)).1))
        ⟨(readNum st.ibase (c :: rest)).2, td, false⟩
    | .str => AllCalls lm P fuel (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩
    | .comment => AllCalls lm P fuel st ⟨skipEol rest, td, false⟩
    | .negcmp => AllCalls lm P fuel st ⟨rest, td, true⟩
    | .eofError => True
    | .sqrt st' x =>
      match Num.sqrtLoopFuel x (max st'.scale x.scale) fuel (Num.sqrtInit x).1 (Num.sqrtInit x).2 with
      | some y => AllCalls lm P fuel (st'.push (.num y)) ⟨rest, td, false⟩
      | none => True
    | .system => AllCalls lm P fuel st ⟨skipSys rest, td, false⟩

/-- `AllCalls` for `tos lm n st rest td`. -/
def TosCalls (lm : Nat) (P : St → Nat → Option Nat → Prop) : Nat → St → List Nat → Nat → Prop
  | 0, _, _, _ => True
  | fuel + 1, st, rest, td =>
    match st.stack with
    | [] => AllCalls lm P fuel st ⟨skipWs rest, td, false⟩
    | .num _ :: _ => AllCalls lm P fuel st ⟨skipWs rest, td, false⟩
    | .str x :: more =>
      if skipWs rest = [] then AllCalls lm P fuel { st with stack := more } ⟨x, td + 1, false⟩
      else
        AllCalls lm P fuel { st with stack := more } ⟨x, 1, false⟩ ∧
        match run lm fuel { st with stack := more } ⟨x, 1, false⟩ with
        | some (st', .ok) => AllCalls lm P fuel st' ⟨skipWs rest, td, false⟩
        | _ => True

end

/-- **The model-side budgets of an evaluation** from `st` and frame `f`:
nesting at most `d`, at most `k` leaking commands, every `dc_func` call
within SizeBound (`FnSize`), every string held shorter than `2^24`. -/
structure EvBudget (lm d k : Nat) (st : St) (f : Frame) : Prop where
  nest : ∀ n, nestDepth lm n st f ≤ d
  leak : ∀ n, leakCount lm n st f ≤ k
  size : ∀ n, AllCalls lm (fun st _ _ => FnSize st ∧ StrBound (2 ^ 24) st) n st f
  frameLen : f.s.length < 2 ^ 24

/-- `EvBudget` for the `DC_EVALTOS` code. -/
structure TosBudget (lm d k : Nat) (st : St) (rest : List Nat) (td : Nat) : Prop where
  nest : ∀ n, tosDepth lm n st rest td ≤ d
  leak : ∀ n, tosLeak lm n st rest td ≤ k
  size : ∀ n, TosCalls lm (fun st _ _ => FnSize st ∧ StrBound (2 ^ 24) st) n st rest td
  restLen : rest.length < 2 ^ 24

/-- **The budgets at a fuel `n`** where the evaluation completes
(`run lm n st f = some (st', r)`): the loop proof inducts on `n`, every
sub-evaluation completing at a smaller fuel with its budgets read off the
same equations (`EvBudget.fuel` gives it from a derivation). -/
structure EvFuel (lm n d k : Nat) (st : St) (f : Frame) (st' : St) (r : Status) : Prop where
  run : run lm n st f = some (st', r)
  nest : nestDepth lm n st f ≤ d
  leak : leakCount lm n st f ≤ k
  size : AllCalls lm (fun st _ _ => FnSize st ∧ StrBound (2 ^ 24) st) n st f

/-- `EvFuel` for the `DC_EVALTOS` code. -/
structure TosFuel (lm n d k : Nat) (st : St) (rest : List Nat) (td : Nat) (st' : St) (r : Status) :
    Prop where
  run : tos lm n st rest td = some (st', r)
  nest : tosDepth lm n st rest td ≤ d
  leak : tosLeak lm n st rest td ≤ k
  size : TosCalls lm (fun st _ _ => FnSize st ∧ StrBound (2 ^ 24) st) n st rest td

/-- A derivation with its budgets completes at some fuel. -/
theorem EvBudget.fuel {lm d k : Nat} {st st' : St} {f : Frame} {r : Status}
    (hl : Loop lm st f st' r) (hb : EvBudget lm d k st f) : ∃ n, EvFuel lm n d k st f st' r := by
  obtain ⟨n, hn⟩ := hl.complete
  exact ⟨n, hn, hb.nest n, hb.leak n, hb.size n⟩

/-! ## The machine side -/

/-- `evalstr`'s saved registers (`ra`, `s0`–`s9`) and their frame offsets. -/
abbrev evSaved : List (Nat × Nat) :=
  [(1, 168), (8, 160), (9, 152), (18, 144), (19, 136), (20, 128), (21, 120), (22, 112), (23, 104),
    (24, 96), (25, 88)]

/-- `evalstr`'s loop constants: the status tables and `10`, `-1`. -/
structure EvConsts (R : Nat → BitVec 64) : Prop where
  s2 : R 18 = 0x80008134#64
  s3 : R 19 = 0x80008160#64
  s4 : R 20 = 10#64
  s5 : R 21 = 0xFFFFFFFFFFFFFFFF#64

/-- `interrupt_seen` (`0x8001cd84`, outside `DcGlob`): owned and `0`;
`stdin_lookahead` (`0x8001cd30`): owned and `EOF`. -/
structure EvGlobs (S : Nat → Prop) (M : Mem) : Prop where
  intrOwn : ∀ a, 0x8001cd84 ≤ a → a < 0x8001cd88 → S a
  intr : ldv .lw M 0x8001cd84 = 0#64
  laOwn : ∀ a, 0x8001cd30 ≤ a → a < 0x8001cd34 → S a
  la : ldv .lw M 0x8001cd30 = 0xFFFFFFFFFFFFFFFF#64

/-- **An `evalstr` activation at its loop head** (`0x800014f8`): its frame
`W` bytes below `sp` (entry registers `R0`, memory `M0`), the string datum
`*string` at `q`, the budgets `d` (nesting), `k` (leaks). -/
structure EvAt (S : Nat → Prop) (sp W d k q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64)
    (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj) (C : BcConsts)
    (G : DcG) (hs xs : List GV) (st : St) (f : Frame) (o : StrObj) : Prop where
  dc : DcAt S M H F L C G (xs ++ hs) st
  strIn : o ∈ G.strs
  strLen : o.s.length < 2 ^ 24
  held : hs.head? = some (.str o.hb.pay)
  slot : DatAt M q (.str o.hb.pay)
  slotPlace : DatSlot S sp q
  pos : ∃ i, i ≤ o.s.length ∧ o.s.drop i = f.s ∧ R 8 = BitVec.ofNat 64 (o.tb.pay + i)
  s1 : R 9 = BitVec.ofNat 64 (o.tb.pay + o.s.length)
  s6 : R 22 = BitVec.ofNat 64 q
  s8 : R 24 = BitVec.ofNat 64 f.td
  tdLt : f.td < 2 ^ 31
  cs : EvConsts R
  r2 : R 2 = BitVec.ofNat 64 (sp - 176)
  saved : SavedWords M (sp - 176) evSaved R0
  al : (R0 1).toNat % 4 = 0
  r20 : R0 2 = BitVec.ofNat 64 sp
  frame : StackFrame S sp W
  room : heapEnd + W ≤ sp
  stk : 176 * (d + 1) + 1216 + rmStack (2 ^ 30) ≤ W
  stkPr : 176 * (d + 1) + 192 + 336 + prN ≤ W
  stkDn : 176 * (d + 1) + 192 + 336 + dnN ≤ W
  budget : G.lk.length + xs.length + hs.length + 4 * k + 8 ≤ 2 ^ 20
  mb : MulBase S M
  err : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a
  globs : EvGlobs S M
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn (sp - 176) (W - 176) a →
    ¬ (sp - 176 ≤ a ∧ a < sp) → ¬ (q ≤ a ∧ a < q + 16) → imgM M a = imgM M0 a

/-- `evalstr`'s status word. -/
def statusWord : Status → BitVec 64
  | .ok => 0#64
  | .quit => 4#64

/-- **What an `evalstr` activation leaves its caller**: the state `st'` over
the lost strings `xs'` and the caller's handles with the string `*string`
now `p'`; at most four more lost references or strings per leaking command
of the budget `k`; the caller's other strings pinned; the bytes outside the
heap, the globals, `out_char`'s words, the activation's stack and `*string`
as at the activation's entry; the globals `EvGlobs` and `MulBase` kept. -/
structure EvPost (S : Nat → Prop) (sp W k q : Nat) (M0 : Mem) (G : DcG) (hs xs : List GV)
    (M' : Mem) (H' : Heap) (F' : List Blk) (L' : List NumObj) (C' : BcConsts) (G' : DcG)
    (xs' : List GV) (p' : Nat) (st' : St) : Prop where
  dc : DcAt S M' H' F' L' C' G' (xs' ++ .str p' :: hs.tail) st'
  slot : DatAt M' q (.str p')
  strIn : ∃ o' ∈ G'.strs, o'.hb.pay = p'
  grow : G'.lk.length + xs'.length ≤ G.lk.length + xs.length + 4 * k
  pin : StrPin G.strs G'.strs hs.tail
  mb : MulBase S M'
  globs : EvGlobs S M'
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp W a → ¬ (q ≤ a ∧ a < q + 16) →
    imgM M' a = imgM M0 a

/-- **The caller's continuation** after an activation returning `r` in
state `st'`. -/
def EvK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W k q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (G : DcG) (hs xs : List GV)
    (st' : St) (r : Status) : Prop :=
  ∀ R' M' H' F' L' C' G' xs' p', Keeps cClob R' R0 → R' 2 = R0 2 → R' 10 = statusWord r →
    EvPost S sp W k q M0 G hs xs M' H' F' L' C' G' xs' p' st' →
    DWO live S Q (t0 ++ Dc.outStr st'.out) (R0 1) R' M'

/-- **Out of memory inside an activation** (frame `W` below `sp`, entry
memory `M0`): `dc_memfail` from any `sp'` in the frame, the bytes off the
heap, the globals, the frame, `out_char`'s words and `*string` as at entry. -/
def EvOom (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (sp W q : Nat) (M0 : Mem) : Prop :=
  ∀ t' R' M' sp', OomAt S sp W M0 (fun a => ocG a ∨ (q ≤ a ∧ a < q + 16)) sp' R' M' →
    DWO live S Q t' 0x80001e74#64 R' M'

/-- **`dc_func`'s contract** as a hypothesis (`dc_func_spec`, once every arm
is in; `dc_func_spec_done` for the characters done). -/
def FnSpecH (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    Prop :=
  ∀ (t0 : String) (sp W : Nat) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj) (C : BcConsts)
    (G : DcG) (hs : List GV) (st : St) (c : Nat) (peek : Option Nat) (neg : Bool)
    (R : Nat → BitVec 64),
    FnPre S sp W M H F L C G hs st c peek → FnRegs R sp c peek neg → FnOom live S Q sp W M →
    FnK live S Q (leakAllow c) t0 st (dcFunc 70 st c peek neg) G hs sp W M R →
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000b9c#64 R M

/-! ## The statements -/

/-- **The loop** (term direction): an evaluation completing at fuel `n`
(`EvFuel`, from a derivation `Loop 70 st f st' r`) and the machine at the
loop head representing `st` and `f` (nonempty) run to the caller's
continuation for `st'` and `r`. -/
def EvLoopSpec (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st st' : St)
    (f : Frame) (o : StrObj) (r : Status) (Ge : DcG) (hse xse : List GV) (ke : Nat),
    ∀ n, EvFuel 70 n d k st f st' r → f.s ≠ [] →
    EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o → R 12 = boolWord f.neg →
    EvOom live S Q sp W q M0 →
    hs.tail = hse.tail → G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke →
    StrPin Ge.strs G.strs hs.tail →
    EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st' r →
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800014f8#64 R M

/-- **The `DC_EVALTOS` code** (term direction) at `0x80001748` (the
whitespace and comment skip, then `dc_pop (&evalstr)` into `s9 = sp - 176 +
32`): an evaluation `tos 70 n st rest td = some (st', r)` with its budgets, the machine representing `st`
and the frame `⟨rest, td, false⟩` (`rest` possibly empty), runs to the
continuation. -/
def EvTosSpec (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st st' : St)
    (rest : List Nat) (td : Nat) (o : StrObj) (r : Status) (Ge : DcG) (hse xse : List GV) (ke : Nat),
    ∀ n, TosFuel 70 n d k st rest td st' r →
    EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o →
    R 25 = BitVec.ofNat 64 (sp - 176 + 32) →
    EvOom live S Q sp W q M0 →
    hs.tail = hse.tail → G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke →
    StrPin Ge.strs G.strs hs.tail →
    EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st' r →
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001748#64 R M

/-- **`evalstr (string)`** at `0x80001448`: a derivation
`Loop 70 st ⟨o.s, 1, false⟩ st' r` for the string datum `*string = .str
o.hb.pay` at `q`, held by the caller's handle, runs to the continuation. -/
def EvalstrSpec (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M : Mem) (R : Nat → BitVec 64) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st st' : St)
    (o : StrObj) (r : Status),
    Loop 70 st ⟨o.s, 1, false⟩ st' r → EvBudget 70 d k st ⟨o.s, 1, false⟩ →
    DcAt S M H F L C G (xs ++ hs) st → o ∈ G.strs → hs.head? = some (.str o.hb.pay) →
    DatAt M q (.str o.hb.pay) → DatSlot S sp q →
    R 2 = BitVec.ofNat 64 sp → R 10 = BitVec.ofNat 64 q → (R 1).toNat % 4 = 0 →
    StackFrame S sp W → heapEnd + W ≤ sp →
    176 * (d + 1) + 1216 + rmStack (2 ^ 30) ≤ W → 176 * (d + 1) + 192 + 336 + prN ≤ W →
    176 * (d + 1) + 192 + 336 + dnN ≤ W →
    G.lk.length + xs.length + hs.length + 4 * k + 8 ≤ 2 ^ 20 →
    MulBase S M → (∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a) → EvGlobs S M →
    EvOom live S Q sp W q M →
    EvK live S Q t0 sp W k q M R G hs xs st' r →
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001448#64 R M

end Dc.Mach
