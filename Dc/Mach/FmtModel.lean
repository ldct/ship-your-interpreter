import Dc.Mach.Realloc

/-!
# The formatter's model: `Dc.Mach.fmt` and the sink

`dc-port/libc/libc.c` formats through `format(k, fmt, ap)` into a sink
`struct sink { FILE *f; char *buf; size_t size; size_t len; }` (32 bytes at
`k`). This file holds what the machine proofs (`EmitUnsigned.lean`,
`Format.lean`, `Printf.lean`) are stated against:

- The format as pieces (`Piece`): literal bytes and conversions `%[#][l]k`
  for `k ∈ {s, c, d, u, o, %}`, the conversions dc uses; `fmtBytes` is the
  format string they spell.
- The arguments (`FArg`): the `va_list` word and, for `%s`, the bytes of the
  string it points to.
- `fmt ps as`: the bytes `format` produces (`udigits b v`: `v` in base `b`,
  most significant digit first, as `emit_unsigned` writes it).
- The sink (`SinkAt`): a stream (on `stdout` the run prints the output, on
  any other descriptor nothing), or a buffer of `size` bytes whose first
  `size - 1` bytes receive the output; `len` counts every byte produced.
  `SinkAt.bump`/`SinkAt.put` are the two memory effects of one emitted byte.
- The console (`SinkDst.shown`, `DWS`): the formatter's runs are printing
  runs (`DWO`) whose console is the text at entry followed by what the sink
  has shown of the output so far.
- Strings the formatter reads (the format and the `%s` arguments) are in
  `.rodata` (`RoStr`): dc passes only string literals.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## The format and its output -/

/-- A conversion of `format`. -/
inductive Conv
  | s | c | d | u | o | pct
  deriving DecidableEq

/-- The conversion character. -/
def Conv.char : Conv → BitVec 8
  | .s => 115#8
  | .c => 99#8
  | .d => 100#8
  | .u => 117#8
  | .o => 111#8
  | .pct => 37#8

/-- A piece of a format string: a literal byte (neither NUL nor `%`), or a
conversion with the `#` and `l` flags. -/
inductive Piece
  | lit (c : BitVec 8)
  | conv (alt lng : Bool) (k : Conv)

/-- The bytes of a piece. -/
def Piece.bytes : Piece → List (BitVec 8)
  | .lit c => [c]
  | .conv alt lng k => 37#8 :: ((if alt then [35#8] else []) ++ (if lng then [108#8] else []) ++ [k.char])

/-- A literal piece is neither NUL nor `%`. -/
def Piece.ok : Piece → Prop
  | .lit c => c ≠ 0#8 ∧ c ≠ 37#8
  | .conv .. => True

/-- The format string of the pieces (without the NUL). -/
def fmtBytes (ps : List Piece) : List (BitVec 8) := ps.flatMap Piece.bytes

/-- A formatting argument: its `va_list` word and, for `%s`, the bytes of its
string. -/
structure FArg where
  w : BitVec 64
  s : List (BitVec 8)

/-- A digit: `"0123456789abcdef"[i]`. -/
def digitChar (i : Nat) : BitVec 8 := BitVec.ofNat 8 (if i < 10 then 48 + i else 87 + i)

/-- The number of base-`b` digits of `v` (at least one). -/
def ndig (b v : Nat) : Nat :=
  if h : 2 ≤ b ∧ b ≤ v then ndig b (v / b) + 1 else 1
termination_by v
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The `j`-th base-`b` digit of `v` (from the least significant). -/
def dg (b v j : Nat) : BitVec 8 := digitChar (v / b ^ j % b)

/-- `v` in base `b`, most significant digit first (`emit_unsigned`). -/
def udigits (b v : Nat) : List (BitVec 8) := ((List.range (ndig b v)).map (dg b v)).reverse

/-- The value of a `%u`/`%o` argument: the word, or its low 32 bits. -/
def uval (lng : Bool) (w : BitVec 64) : Nat := if lng then w.toNat else w.toNat % 2 ^ 32

/-- The value of a `%d` argument: the word, or its low 32 bits sign-extended. -/
def dval (lng : Bool) (w : BitVec 64) : BitVec 64 :=
  if lng then w else (w.setWidth 32).signExtend 64

/-- What a conversion that takes an argument produces. -/
def convOut (alt lng : Bool) : Conv → FArg → List (BitVec 8)
  | .s, a => a.s
  | .c, a => [a.w.setWidth 8]
  | .d, a => if (dval lng a.w).msb then 45#8 :: udigits 10 (-(dval lng a.w)).toNat
      else udigits 10 (dval lng a.w).toNat
  | .u, a => udigits 10 (uval lng a.w)
  | .o, a => (if alt && uval lng a.w ≠ 0 then [48#8] else []) ++ udigits 8 (uval lng a.w)
  | .pct, _ => [37#8]

/-- **The formatter's output** for the pieces `ps` over the arguments `args`. -/
def fmt : List Piece → List FArg → List (BitVec 8)
  | [], _ => []
  | .lit c :: ps, args => c :: fmt ps args
  | .conv _ _ .pct :: ps, args => 37#8 :: fmt ps args
  | .conv alt lng k :: ps, a :: args => convOut alt lng k a ++ fmt ps args
  | .conv _ _ _ :: _, [] => []

/-- The number of arguments the pieces take. -/
def nargs : List Piece → Nat
  | [] => 0
  | .lit _ :: ps => nargs ps
  | .conv _ _ .pct :: ps => nargs ps
  | .conv _ _ _ :: ps => nargs ps + 1

/-! ## Digits -/

theorem digitChar_lt10 {i : Nat} (h : i < 10) : digitChar i = BitVec.ofNat 8 (48 + i) := by
  simp [digitChar, h]

theorem ndig_of_lt {b v : Nat} (h : v < b) : ndig b v = 1 := by
  rw [ndig]; simp only [dite_eq_right_iff]; intro h'; omega

theorem ndig_of_ge {b v : Nat} (hb : 2 ≤ b) (h : b ≤ v) : ndig b v = ndig b (v / b) + 1 := by
  rw [ndig]; simp only [hb, h, and_self, dite_true]

theorem ndig_pos (b v : Nat) : 1 ≤ ndig b v := by
  rw [ndig]; split <;> omega

theorem div_pow_succ (v b n : Nat) : v / b ^ (n + 1) = v / b ^ n / b := by
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- Before the last digit the quotient is at least the base. -/
theorem ndig_ge {b : Nat} (hb : 2 ≤ b) : ∀ v n, n + 1 < ndig b v → b ≤ v / b ^ n := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
  intro n hn
  by_cases h : b ≤ v
  · rw [ndig_of_ge hb h] at hn
    cases n with
    | zero => simpa using h
    | succ n =>
      have := ih (v / b) (Nat.div_lt_self (by omega) (by omega)) n (by omega)
      rwa [div_pow_succ, Nat.div_div_eq_div_mul, ← Nat.pow_succ', Nat.pow_succ,
        ← Nat.div_div_eq_div_mul] at *
  · rw [ndig_of_lt (by omega)] at hn; omega

/-- At the last digit the quotient is below the base. -/
theorem ndig_lt {b : Nat} (hb : 2 ≤ b) : ∀ v, v / b ^ (ndig b v - 1) < b := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
  by_cases h : b ≤ v
  · rw [ndig_of_ge hb h, Nat.add_sub_cancel]
    have := ih (v / b) (Nat.div_lt_self (by omega) (by omega))
    have h1 := ndig_pos b (v / b)
    obtain ⟨m, hm⟩ : ∃ m, ndig b (v / b) = m + 1 := ⟨_, (Nat.sub_add_cancel h1).symm⟩
    rw [hm, Nat.add_sub_cancel] at this
    rw [hm, div_pow_succ]
    rwa [show v / b / b ^ m = v / b ^ m / b by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]] at this
  · rw [ndig_of_lt (by omega)]; simpa using (by omega : v < b)

/-! ## Strings in `.rodata` -/

/-- The bytes `l` at `p` in `.rodata`: image bytes of the ELF's read-only
data below `tohost`. -/
def RoBytes (p : Nat) : List (BitVec 8) → Prop
  | [] => True
  | b :: l => dcROImg p = b ∧ (p, b) ∈ dcRO ∧ 0x80000000 ≤ p ∧ p + 1 ≤ tohostAddr ∧ RoBytes (p + 1) l

theorem RoBytes.append {p : Nat} : ∀ {l1 l2 : List (BitVec 8)},
    RoBytes p (l1 ++ l2) ↔ RoBytes p l1 ∧ RoBytes (p + l1.length) l2
  | [], _ => by simp [RoBytes]
  | b :: l1, l2 => by
    simp only [List.cons_append, RoBytes, List.length_cons]
    rw [RoBytes.append (p := p + 1), show p + 1 + l1.length = p + (l1.length + 1) by omega]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
    · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The C string `s` at `p` in `.rodata`: its bytes, none NUL, then the NUL. -/
structure RoStr (p : Nat) (s : List (BitVec 8)) : Prop where
  bytes : RoBytes p (s ++ [0#8])
  nz : ∀ b ∈ s, b ≠ 0#8

/-! ## The sink -/

/-- Where a sink sends its bytes: a stream, or a buffer. -/
inductive SinkDst
  | stream (f fd : Nat)
  | buffer (buf size : Nat)

/-- The sink's first word: the stream, or `NULL` for a buffer. -/
def SinkDst.fw : SinkDst → Nat
  | .stream f _ => f
  | .buffer _ _ => 0

/-- The bytes an emit may change: the count word, and a buffer. -/
def SinkDst.Byte (k : Nat) : SinkDst → Nat → Prop
  | .stream _ _, a => k + 24 ≤ a ∧ a < k + 32
  | .buffer buf size, a => (k + 24 ≤ a ∧ a < k + 32) ∨ (buf ≤ a ∧ a < buf + size)

/-- The destination's facts after the output `out`. -/
inductive DstAt (S : Nat → Prop) (Mt : Mem) (k : Nat) : SinkDst → List (BitVec 8) → Prop
  | stream {f fd : Nat} {out : List (BitVec 8)} : FdAt S Mt f fd →
      (f + 4 ≤ k ∨ k + 32 ≤ f) → DstAt S Mt k (.stream f fd) out
  | buffer {buf size : Nat} {out : List (BitVec 8)} : OwnedBytes S buf size →
      (buf + size ≤ k ∨ k + 32 ≤ buf) → size < 2 ^ 62 →
      ldv .ld Mt (k + 8) = BitVec.ofNat 64 buf → ldv .ld Mt (k + 16) = BitVec.ofNat 64 size →
      (∀ j (h : j < out.length), j + 1 < size → imgM Mt (buf + j) = out[j]) →
      DstAt S Mt k (.buffer buf size) out

/-- **The sink** at `k` sending to `dst`, after the output `out` from an empty
sink: its words and the destination. -/
structure SinkAt (S : Nat → Prop) (Mt : Mem) (k : Nat) (dst : SinkDst)
    (out : List (BitVec 8)) : Prop where
  own : ∀ i, i < 32 → S (k + i)
  al : k % 8 = 0
  lo : tohostAddr + 16 ≤ k
  hi : k + 32 ≤ 0x88000000
  fw : ldv .ld Mt k = BitVec.ofNat 64 dst.fw
  len : ldv .ld Mt (k + 24) = BitVec.ofNat 64 out.length
  short : out.length < 2 ^ 62
  dstAt : DstAt S Mt k dst out

/-- One or more emits from `Mt` to `Mt'`: the sink after the output `out`,
and only the sink's count word and buffer changed. -/
structure Emitted (S : Nat → Prop) (Mt Mt' : Mem) (k : Nat) (dst : SinkDst)
    (out : List (BitVec 8)) : Prop where
  sink : SinkAt S Mt' k dst out
  frame : ∀ a, ¬ dst.Byte k a → imgM Mt' a = imgM Mt a

/-- The console text of the bytes `l`. -/
def bytesStr : List (BitVec 8) → String
  | [] => ""
  | c :: l => putcStr c ++ bytesStr l

theorem bytesStr_append : ∀ (l1 l2 : List (BitVec 8)), bytesStr (l1 ++ l2) = bytesStr l1 ++ bytesStr l2
  | [], l2 => by simp [bytesStr]
  | c :: l1, l2 => by simp only [List.cons_append, bytesStr, bytesStr_append l1 l2, String.append_assoc]

/-- What the destination shows on the console of the output `out`: all of it
on `stdout`, nothing elsewhere. -/
def SinkDst.shown : SinkDst → List (BitVec 8) → String
  | .stream _ fd, out => fdOut fd (bytesStr out)
  | .buffer _ _, _ => ""

/-- One more byte shown on `stdout`. -/
theorem SinkDst.shown_print {f : Nat} (out : List (BitVec 8)) (c : BitVec 8) :
    (SinkDst.stream f 1).shown (out ++ [c]) = (SinkDst.stream f 1).shown out ++ putcStr c := by
  simp [SinkDst.shown, fdOut_one, bytesStr_append, bytesStr]

/-- One more byte on another stream or a buffer shows nothing. -/
theorem SinkDst.shown_silent {dst : SinkDst} (h : ∀ f, dst ≠ .stream f 1)
    (out l : List (BitVec 8)) : dst.shown (out ++ l) = dst.shown out := by
  cases dst with
  | stream f fd =>
    have hne : fd ≠ 1 := fun e => h f (by rw [e])
    simp [SinkDst.shown, fdOut_ne hne]
  | buffer => rfl

/-- **A formatter run**: a printing run (`DWO`) whose console is `t0` followed
by what the sink `dst` has shown of the output `out`. -/
abbrev DWS (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (dst : SinkDst) (out : List (BitVec 8)) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  DWO live S Q (t0 ++ dst.shown out)

/-- The bytes a sink reads: its four words, and the stream's descriptor word
or the buffer. -/
def SinkDst.Read (k : Nat) : SinkDst → Nat → Prop
  | .stream f _, a => (k ≤ a ∧ a < k + 32) ∨ (f ≤ a ∧ a < f + 4)
  | .buffer buf size, a => (k ≤ a ∧ a < k + 32) ∨ (buf ≤ a ∧ a < buf + size)

/-- A load depends only on its bytes. -/
theorem ldv_congr (kd : MKind) {Mt Mt' : Mem} {a : Nat}
    (h : ∀ j, j < widthOfM kd → imgM Mt' (a + j) = imgM Mt (a + j)) : ldv kd Mt' a = ldv kd Mt a := by
  unfold ldv bytesAt
  congr 1
  exact List.map_congr_left fun j hj => h j (List.mem_range.mp hj)

/-- **Transport**: a sink survives any memory that agrees on its bytes. -/
theorem SinkAt.transport {S : Nat → Prop} {Mt Mt' : Mem} {k : Nat} {dst : SinkDst}
    {out : List (BitVec 8)} (h : SinkAt S Mt k dst out)
    (hag : ∀ a, dst.Read k a → imgM Mt' a = imgM Mt a) : SinkAt S Mt' k dst out := by
  have hw : ∀ o, o + 8 ≤ 32 → ldv .ld Mt' (k + o) = ldv .ld Mt (k + o) := fun o ho =>
    ldv_congr .ld fun j hj => hag _ (by
      have : j < 8 := hj
      cases dst with
      | stream => exact .inl ⟨by omega, by omega⟩
      | buffer => exact .inl ⟨by omega, by omega⟩)
  refine { h with fw := ?_, len := ?_, dstAt := ?_ }
  · have := hw 0 (by omega); rw [Nat.add_zero] at this; rw [this]; exact h.fw
  · rw [hw 24 (by omega)]; exact h.len
  · cases hd : h.dstAt with
    | stream hfd hoff =>
      refine .stream ⟨hfd.own, ?_, hfd.lo, hfd.hi, hfd.small⟩ hoff
      rw [ldv_congr .lw fun j hj => hag _ (.inr ⟨by omega, by have : j < 4 := hj; omega⟩)]
      exact hfd.val
    | buffer hb hoff hsz h8 h16 hc =>
      refine .buffer hb hoff hsz ?_ ?_ fun j hj hjs => ?_
      · rw [hw 8 (by omega)]; exact h8
      · rw [hw 16 (by omega)]; exact h16
      · rw [hag _ (.inr ⟨by omega, by omega⟩)]; exact hc j hj hjs

theorem SinkDst.byte_count {k : Nat} {dst : SinkDst} {a : Nat} (h1 : k + 24 ≤ a) (h2 : a < k + 32) :
    dst.Byte k a := by
  cases dst with
  | stream => exact ⟨h1, h2⟩
  | buffer => exact .inl ⟨h1, h2⟩

/-- A stream's word and a buffer's words lie outside the count word. -/
theorem SinkAt.fw_ld {S : Nat → Prop} {Mt : Mem} {k : Nat} {dst : SinkDst}
    {out : List (BitVec 8)} (h : SinkAt S Mt k dst out) {Mt' : Mem}
    (hag : ∀ a, a < k + 24 → imgM Mt' a = imgM Mt a) :
    ldv .ld Mt' k = BitVec.ofNat 64 dst.fw :=
  (ldv_ld_congr fun j hj => hag _ (by omega)).trans h.fw

/-- **One byte `c` counted** without a buffer store (a stream, or a full
buffer): the count word takes `len + 1`. -/
theorem SinkAt.bump {S : Nat → Prop} {Mt : Mem} {k : Nat} {dst : SinkDst}
    {out : List (BitVec 8)} (h : SinkAt S Mt k dst out) (c : BitVec 8)
    (hfull : ∀ buf size, dst = .buffer buf size → size ≤ out.length + 1)
    (hsh' : (out ++ [c]).length < 2 ^ 62) :
    SinkAt S (writeLog Mt [(k + 24, 8, BitVec.ofNat 64 (out.length + 1))]) k dst (out ++ [c]) := by
  have hal := h.al
  have hsh := h.short
  have hmiss : ∀ a, a < k + 24 ∨ k + 32 ≤ a →
      imgM (writeLog Mt [(k + 24, 8, BitVec.ofNat 64 (out.length + 1))]) a = imgM Mt a :=
    fun a ha => imgM_store_miss _ _ (by omega)
  refine { h with fw := ?_, len := ?_, short := hsh', dstAt := ?_ }
  · rw [ldv_ld_miss _ _ (by omega)]; exact h.fw
  · rw [ldv_store_hit, List.length_append, List.length_singleton]
  · cases h.dstAt with
    | stream hfd hoff =>
      refine .stream ⟨hfd.own, ?_, hfd.lo, hfd.hi, hfd.small⟩ hoff
      rw [ldv_lw_miss _ _ (by omega)]; exact hfd.val
    | @buffer buf size _ hb hoff hsz h8 h16 hc =>
      have hs := hfull buf size rfl
      refine .buffer hb hoff hsz ?_ ?_ fun j hj hjs => ?_
      · rw [ldv_ld_miss _ _ (by omega)]; exact h8
      · rw [ldv_ld_miss _ _ (by omega)]; exact h16
      · simp only [List.length_append, List.length_singleton] at hj
        have hj' : j < out.length := by omega
        rw [hmiss _ (by omega), List.getElem_append_left hj']
        exact hc j hj' hjs

/-- **One byte `c` stored** in a buffer with room, then counted. -/
theorem SinkAt.put {S : Nat → Prop} {Mt : Mem} {k buf size : Nat}
    {out : List (BitVec 8)} (h : SinkAt S Mt k (.buffer buf size) out) (c : BitVec 8)
    (hroom : out.length + 1 < size) {v : BitVec 64} (hv : sbData v = c)
    (hsh' : (out ++ [c]).length < 2 ^ 62) :
    SinkAt S (writeLog (writeLog Mt [(buf + out.length, 1, v)])
      [(k + 24, 8, BitVec.ofNat 64 (out.length + 1))]) k (.buffer buf size) (out ++ [c]) := by
  have hal := h.al
  have hsh := h.short
  cases hd : h.dstAt with
  | buffer hb hoff hsz h8 h16 hc =>
  have hmiss : ∀ a, a < k + 24 ∨ k + 32 ≤ a →
      imgM (writeLog (writeLog Mt [(buf + out.length, 1, v)])
        [(k + 24, 8, BitVec.ofNat 64 (out.length + 1))]) a =
        imgM (writeLog Mt [(buf + out.length, 1, v)]) a :=
    fun a ha => imgM_store_miss _ _ (by omega)
  have hbw : ∀ x, x + 8 ≤ buf + out.length ∨ buf + out.length + 1 ≤ x →
      ldv .ld (writeLog Mt [(buf + out.length, 1, v)]) x = ldv .ld Mt x :=
    fun x hx => ldv_ld_miss _ _ hx
  refine { h with fw := ?_, len := ?_, short := hsh', dstAt := ?_ }
  · rw [ldv_ld_miss _ _ (by omega), hbw _ (by omega)]; exact h.fw
  · rw [ldv_store_hit, List.length_append, List.length_singleton]
  · refine .buffer hb hoff hsz ?_ ?_ fun j hj hjs => ?_
    · rw [ldv_ld_miss _ _ (by omega), hbw _ (by omega)]; exact h8
    · rw [ldv_ld_miss _ _ (by omega), hbw _ (by omega)]; exact h16
    · simp only [List.length_append, List.length_singleton] at hj
      rw [hmiss _ (by omega)]
      by_cases e : j = out.length
      · subst e; rw [imgM_sb, hv]; simp
      · have hj' : j < out.length := by omega
        rw [imgM_store_miss _ _ (by omega), List.getElem_append_left hj']
        exact hc j hj' hjs

end Dc.Mach
