import Dc.Mach.FmtModel

/-!
# The inlined `emit` of the formatter

`emit(k, c)` (`libc.c`) is inlined at every place `format` and
`emit_unsigned` produce a byte:

```
if (k->f) fputc(c, k->f);                        // prints only on stdout
else if (k->len + 1 < k->size) k->buf[k->len] = c;
k->len++;
```

Each copy starts at the `beqz` on the sink's first word, with the count and
the count plus one already in registers, and ends after the store of the new
count (the join). `emit_<pc>` runs one copy for a `SinkAt` sink: the byte is
counted (`SinkAt.bump`) or stored and counted (`SinkAt.put`), and only the
sink's count word and buffer change (`Emitted`); the register that held the
new count still holds it. The run is a formatter run (`DWS`): on `stdout`
the copy's `tohost` store prints the byte (`stP_<pc>`, the console gains
`putcStr c`), on any other destination the console is unchanged. The copies differ only in their
registers and PCs; the proofs share the tactics below.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

theorem SinkAt.own' {S : Nat → Prop} {Mt : Mem} {k : Nat} {dst : SinkDst}
    {out : List (BitVec 8)} (h : SinkAt S Mt k dst out) {x : Nat} (h1 : k ≤ x)
    (h2 : x < k + 32) : S x := by
  have := h.own (x - k) (by omega); rwa [Nat.add_sub_cancel' h1] at this

theorem FdAt.own' {S : Nat → Prop} {Mt : Mem} {f fd : Nat} (h : FdAt S Mt f fd) {x : Nat}
    (h1 : f ≤ x) (h2 : x < f + 4) : S x := by
  have := h.own (x - f) (by omega); rwa [Nat.add_sub_cancel' h1] at this

/-- An access owned by `h` (`SinkAt.own'`, `FdAt.own'`, `OwnedBytes.own'`),
its address bounds by `sx_addr`. -/
macro "own_by " h:term : tactic =>
  `(tactic| (gnorm; intro x hx; have hx' := of_mem_accAddrs hx; clear hx
             refine ($h).own' ?_ ?_ <;> (revert hx'; sx_addr)))

/-- `bump` at the machine's address and value. -/
theorem SinkAt.bump_at {S : Nat → Prop} {Mt : Mem} {k : Nat} {dst : SinkDst}
    {out : List (BitVec 8)} (h : SinkAt S Mt k dst out) (c : BitVec 8)
    (hfull : ∀ buf size, dst = .buffer buf size → size ≤ out.length + 1)
    (hsh : out.length + 1 < 2 ^ 62) {A : Nat} {v : BitVec 64} (hA : A = k + 24)
    (hv : v.toNat = out.length + 1) :
    Emitted S Mt (writeLog Mt [(A, 8, v)]) k dst (out ++ [c]) := by
  have hv' : v = BitVec.ofNat 64 (out.length + 1) :=
    BitVec.eq_of_toNat_eq (by rw [hv, BitVec.toNat_ofNat]; omega)
  subst hA hv'
  refine ⟨h.bump c hfull (by simpa using hsh), fun a ha => imgM_store_miss _ _ ?_⟩
  exact Classical.byContradiction fun hn => ha (SinkDst.byte_count (by omega) (by omega))

/-- `put` at the machine's addresses and values. -/
theorem SinkAt.put_at {S : Nat → Prop} {Mt : Mem} {k buf size : Nat}
    {out : List (BitVec 8)} (h : SinkAt S Mt k (.buffer buf size) out) (c : BitVec 8)
    (hroom : out.length + 1 < size) (hsh : out.length + 1 < 2 ^ 62) {A B : Nat}
    {v w : BitVec 64} (hA : A = buf + out.length) (hv : sbData v = c) (hB : B = k + 24)
    (hw : w.toNat = out.length + 1) :
    Emitted S Mt (writeLog (writeLog Mt [(A, 1, v)]) [(B, 8, w)]) k (.buffer buf size)
      (out ++ [c]) := by
  have hw' : w = BitVec.ofNat 64 (out.length + 1) :=
    BitVec.eq_of_toNat_eq (by rw [hw, BitVec.toNat_ofNat]; omega)
  subst hA hB hw'
  refine ⟨h.put c hroom hv (by simpa using hsh), fun a ha => ?_⟩
  have ha' : ¬ ((k + 24 ≤ a ∧ a < k + 32) ∨ (buf ≤ a ∧ a < buf + size)) := ha
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]

/-- The words of a buffer sink. -/
theorem SinkAt.bufWords {S : Nat → Prop} {Mt : Mem} {k buf size : Nat}
    {out : List (BitVec 8)} (h : SinkAt S Mt k (.buffer buf size) out) :
    OwnedBytes S buf size ∧ (buf + size ≤ k ∨ k + 32 ≤ buf) ∧ size < 2 ^ 62 ∧
      ldv .ld Mt (k + 8) = BitVec.ofNat 64 buf ∧ ldv .ld Mt (k + 16) = BitVec.ofNat 64 size := by
  cases h.dstAt with
  | buffer hb hoff hsz h8 h16 _ => exact ⟨hb, hoff, hsz, h8, h16⟩

/-- The stream of a stream sink. -/
theorem SinkAt.streamFd {S : Nat → Prop} {Mt : Mem} {k f fd : Nat}
    {out : List (BitVec 8)} (h : SinkAt S Mt k (.stream f fd) out) :
    FdAt S Mt f fd ∧ (f + 4 ≤ k ∨ k + 32 ≤ f) := by
  cases h.dstAt with
  | stream hfd hoff => exact ⟨hfd, hoff⟩

set_option hygiene false in
/-- The new count in the stored register: the count plus one in a register,
or the count reloaded (`hlen`) and incremented. -/
macro "len1_tac" : tactic =>
  `(tactic| first
    | (gnorm; exact hl1)
    | (gnorm; (try simp (disch := sx_addr) only [ldv_ld_miss])
       rw [hlen, ofNat_add_ofNat, ofNat_toNat_lt (by omega)]))

set_option hygiene false in
/-- The byte stored: the register byte `hc`, or a literal. -/
macro "byte_tac" : tactic =>
  `(tactic| first
    | (rw [sbData_eq]; exact hc)
    | exact hc
    | (rw [hc]; exact sbData_zext _)
    | (gnorm; rw [hc]; exact sbData_zext _)
    | decide
    | (gnorm; decide))

set_option hygiene false in
/-- **One inlined `emit`**, from the `beqz` on the sink's first word to the
join `j`; the sink is in register `kr`, its first word in `fr`, the byte is
`ch`. The site
theorem names its hypotheses `hlive`, `hs` (the sink), `hsh`, `hfr` (the
first word), `hl1` (the count plus one), `hc` (the byte, unless literal) and
`hk` (the continuation); the register holding `1` for a `beq`, if any, is in
the context. -/
macro "emit_tac " j:num kr:num fr:num ch:term:max pr:ident : tactic =>
  `(tactic| (
    have hkal := hs.al
    have hklo := hs.lo
    have hkhi := hs.hi
    have htx : tohostAddr = 0x8001ad00 := rfl
    have hlen : ldv .ld Mt (R $kr + 24#64).toNat = BitVec.ofNat 64 out.length := by
      rw [show (R $kr + 24#64).toNat = k + 24 by sx_addr]; exact hs.len
    cases dst with
    | stream f fd =>
      obtain ⟨hfd, hoff⟩ := hs.streamFd
      have hflo := hfd.lo
      have hfhi := hfd.hi
      have hfsm := hfd.small
      try simp only [SinkDst.fw] at hfr
      have hval : ldv .lw Mt (R $fr).toNat = BitVec.ofNat 64 fd := by rw [hfr]; exact hfd.val
      by_cases hfd1 : fd = 1
      · -- `stdout`: the byte is printed
        subst hfd1
        simp only [DWS, SinkDst.shown_print, ← String.append_assoc] at hk
        dx_run hlive at $j
        all_goals (try own_by hfd)
        all_goals (try own_by hs)
        all_goals (try (intro hc'; exfalso; gnorm_at hc'
                        try simp only [ne_eq] at hc'
                        rw [hval] at hc'
                        apply hc'
                        first
                          | rfl
                          | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega)))
        intro _
        dx_run hlive at $j
        all_goals (try own_by hs)
        refine $pr hlive $ch ?pb ?pw ?_
        case pb => gnorm
        case pw =>
          gnorm
          first
            | decide
            | rfl
            | (rw [hc, hpw]; exact putcWord_zext _)
            | (rw [hc]; exact putcWord_zext _)
            | (rw [← hc]; exact putcWord_and _)
        dx_run hlive at $j
        all_goals (try own_by hs)
        refine hk _ _ ?kp ?kl (hs.bump_at $ch (fun _ _ h => nomatch h) hsh ?ka ?kv)
        case kp => keeps_tac (Keeps.refl _ _)
        case kl => len1_tac
        case ka => sx_addr
        case kv => len1_tac
      · -- another stream: nothing is printed
        simp only [DWS, SinkDst.shown_silent (dst := .stream f fd) (fun f' e => hfd1 (by cases e; rfl))]
          at hk
        dx_run hlive at $j
        all_goals (try own_by hfd)
        all_goals (try own_by hs)
        all_goals (try (intro hc'; exfalso; gnorm_at hc'
                        try simp only [ne_eq, Classical.not_not] at hc'
                        rw [hval] at hc'
                        have := congrArg BitVec.toNat hc'; gnorm_at this
                        rw [ofNat_toNat_lt (by omega)] at this; omega))
        intro _
        dx_run hlive at $j
        all_goals (try own_by hs)
        refine hk _ _ ?kp ?kl (hs.bump_at $ch (fun _ _ h => nomatch h) hsh ?ka ?kv)
        case kp => keeps_tac (Keeps.refl _ _)
        case kl => len1_tac
        case ka => sx_addr
        case kv => len1_tac
    | buffer buf size =>
      simp only [DWS, SinkDst.shown_silent (dst := .buffer buf size) (fun f' e => nomatch e)] at hk
      obtain ⟨hb, hoff, hsz, h8, h16⟩ := hs.bufWords
      have hblo := hb.lo
      have hbhi := hb.hi
      try simp only [SinkDst.fw] at hfr
      have hsize : ldv .ld Mt (R $kr + 16#64).toNat = BitVec.ofNat 64 size := by
        rw [show (R $kr + 16#64).toNat = k + 16 by sx_addr]; exact h16
      have hbuf : ldv .ld Mt (R $kr + 8#64).toNat = BitVec.ofNat 64 buf := by
        rw [show (R $kr + 8#64).toNat = k + 8 by sx_addr]; exact h8
      dx_run hlive at $j
      all_goals (try own_by hs)
      · intro hge
        gnorm_at hge
        rw [hsize] at hge
        rw [ofNat_toNat_lt (by omega), hl1] at hge
        dx_run hlive at $j
        all_goals (try own_by hs)
        refine hk _ _ ?kp ?kl (hs.bump_at $ch (fun _ _ h => by cases h; omega) hsh ?ka ?kv)
        case kp => keeps_tac (Keeps.refl _ _)
        case kl => len1_tac
        case ka => sx_addr
        case kv => len1_tac
      · intro hlt
        gnorm_at hlt
        rw [hsize] at hlt
        rw [ofNat_toNat_lt (by omega), hl1] at hlt
        dx_run hlive at $j
        all_goals (try (gnorm; rw [hbuf]))
        all_goals (try own_by hs)
        all_goals (try own_by hb)
        all_goals (try (simp only [StOKb]; sx_addr))
        refine hk _ _ ?kp ?kl (hs.put_at $ch (by omega) hsh ?ka ?kc ?kb ?kv)
        case kp => keeps_tac (Keeps.refl _ _)
        case kl => len1_tac
        case ka => sx_addr
        case kc => byte_tac
        case kb => sx_addr
        case kv => len1_tac))

/-! ## `emit_unsigned`'s copy (`0x800000f4`)

```
800000f4 beqz a3,80000148 ; 800000f8 lw a4,0(a3) ; 800000fc beq a4,a6,80000138
80000100 mv a4,a1 ; 80000104 sd a4,24(s4)          → 80000108
80000148 ld a3,16(s4) ; 8000014c bgeu a1,a3,80000100 ; 80000150 ld a3,8(s4)
80000154 add a4,a3,a4 ; 80000158 sb a2,0(a4) ; 8000015c ld a4,24(s4)
80000160 addi a4,a4,1 ; 80000164 j 80000104
```
`s4` the sink, `a3` its first word, `a4` the count, `a1` the count plus one,
`a2` the byte, `a6 = 1`.
-/

theorem emit_800000f4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {k : Nat} {dst : SinkDst} {out : List (BitVec 8)}
    (hs : SinkAt S Mt k dst out) (c : BitVec 8) (hsh : out.length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hkr : (R 20).toNat = k) (hfr : (R 13).toNat = dst.fw)
    (hlr : (R 14).toNat = out.length) (hl1 : (R 11).toNat = out.length + 1)
    (hc : R 12 = zero_extend (m := 64) c) (h1 : (R 16).toNat = 1)
    (hpw : R 17 = 72339069014638592#64)
    (hk : ∀ R' Mt', Keeps [12, 13, 14] R' R → (R' 14).toNat = out.length + 1 →
      Emitted S Mt Mt' k dst (out ++ [c]) →
      DWS live S Q t0 dst (out ++ [c]) 0x80000108#64 R' Mt') :
    DWS live S Q t0 dst out 0x800000f4#64 R Mt := by
  emit_tac 0x80000108 20 13 c stP_80000140

/-! ## A literal byte (`0x80000310`)

```
80000310 beqz a3,800003bc ; 80000314 lw a3,0(a3) ; 80000318 beq a3,s3,800003e0
8000031c sd a4,24(s1)                                → 80000320
800003bc ld a3,16(s1) ; 800003c0 bgeu a4,a3,8000031c ; 800003c4 ld a4,8(s1)
800003c8 add a4,a4,a2 ; 800003cc sb a5,0(a4) ; 800003d0 ld a4,24(s1)
800003d4 addi a4,a4,1 ; 800003d8 sd a4,24(s1) ; 800003dc j 80000320
```
`s1` the sink, `a3` its first word, `a2` the count, `a4` the count plus
one, `a5` the byte, `s3 = 1`.
-/

theorem emit_80000310 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {k : Nat} {dst : SinkDst} {out : List (BitVec 8)}
    (hs : SinkAt S Mt k dst out) (c : BitVec 8) (hsh : out.length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hkr : (R 9).toNat = k) (hfr : (R 13).toNat = dst.fw)
    (hlr : (R 12).toNat = out.length) (hl1 : (R 14).toNat = out.length + 1)
    (hc : R 15 = zero_extend (m := 64) c) (h1 : (R 19).toNat = 1)
    (hk : ∀ R' Mt', Keeps [13, 14, 15] R' R → (R' 14).toNat = out.length + 1 →
      Emitted S Mt Mt' k dst (out ++ [c]) →
      DWS live S Q t0 dst (out ++ [c]) 0x80000320#64 R' Mt') :
    DWS live S Q t0 dst out 0x80000310#64 R Mt := by
  emit_tac 0x80000320 9 13 c stP_800003f0

/-! ## `%%` (`0x80000398`)

```
80000398 beqz a4,800004e4 ; 8000039c lw a3,0(a4) ; 800003a0 li a4,1
800003a4 beq a3,a4,8000052c ; 800003a8 sd a5,24(s1)   → 800003ac
800004e4 ld a4,16(s1) ; 800004e8 bgeu a5,a4,800003a8 ; 800004ec ld a5,8(s1)
800004f0 li a4,37 ; 800004f4 add a5,a5,a3 ; 800004f8 sb a4,0(a5)
800004fc ld a5,24(s1) ; 80000500 addi a5,a5,1 ; 80000504 sd a5,24(s1) ; 80000508 j 800003ac
```
`s1` the sink, `a4` its first word, `a3` the count, `a5` the count plus
one; the byte `%`.
-/

theorem emit_80000398 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {k : Nat} {dst : SinkDst} {out : List (BitVec 8)}
    (hs : SinkAt S Mt k dst out) (hsh : out.length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hkr : (R 9).toNat = k) (hfr : (R 14).toNat = dst.fw)
    (hlr : (R 13).toNat = out.length) (hl1 : (R 15).toNat = out.length + 1)
    (hk : ∀ R' Mt', Keeps [13, 14, 15] R' R → (R' 15).toNat = out.length + 1 →
      Emitted S Mt Mt' k dst (out ++ [37#8]) →
      DWS live S Q t0 dst (out ++ [37#8]) 0x800003ac#64 R' Mt') :
    DWS live S Q t0 dst out 0x80000398#64 R Mt := by
  emit_tac 0x800003ac 9 14 (37#8) stP_8000053c

/-! ## `%c` (`0x800002c4`)

```
800002c4 beqz a4,8000050c ; 800002c8 lw a2,0(a4) ; 800002cc li a4,1
800002d0 bne a2,a4,800002ec ; … ; 800002ec sd a5,24(s1)  → 800002f0
8000050c ld a4,16(s1) ; 80000510 bgeu a5,a4,800002ec ; 80000514 ld a5,8(s1)
80000518 add a5,a5,a2 ; 8000051c sb a3,0(a5) ; 80000520 ld a5,24(s1)
80000524 addi a5,a5,1 ; 80000528 j 800002ec
```
`s1` the sink, `a4` its first word, `a2` the count, `a5` the count plus
one, `a3` the argument word.
-/

theorem emit_800002c4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {k : Nat} {dst : SinkDst} {out : List (BitVec 8)}
    (hs : SinkAt S Mt k dst out) (c : BitVec 8) (hsh : out.length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hkr : (R 9).toNat = k) (hfr : (R 14).toNat = dst.fw)
    (hlr : (R 12).toNat = out.length) (hl1 : (R 15).toNat = out.length + 1)
    (hc : lo8 (R 13) = c)
    (hk : ∀ R' Mt', Keeps [12, 13, 14, 15] R' R → (R' 15).toNat = out.length + 1 →
      Emitted S Mt Mt' k dst (out ++ [c]) →
      DWS live S Q t0 dst (out ++ [c]) 0x800002f0#64 R' Mt') :
    DWS live S Q t0 dst out 0x800002c4#64 R Mt := by
  emit_tac 0x800002f0 9 14 c stP_800002e8

/-! ## The `0` of `%#o` (`0x80000450`)

```
80000450 beqz a4,80000548 ; 80000454 lw a3,0(a4) ; 80000458 li a4,1
8000045c beq a3,a4,80000578 ; 80000460 sd a5,24(s1)   → 80000464
80000548 ld a4,16(s1) ; 8000054c bgeu a5,a4,80000460 ; 80000550 ld a5,8(s1)
80000554 li a4,48 ; 80000558 add a5,a5,a3 ; 8000055c sb a4,0(a5)
80000560 ld a5,24(s1) ; 80000564 addi a5,a5,1 ; 80000568 sd a5,24(s1) ; 8000056c j 80000464
```
`s1` the sink, `a4` its first word, `a3` the count, `a5` the count plus
one; the byte `0`.
-/

theorem emit_80000450 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {k : Nat} {dst : SinkDst} {out : List (BitVec 8)}
    (hs : SinkAt S Mt k dst out) (hsh : out.length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hkr : (R 9).toNat = k) (hfr : (R 14).toNat = dst.fw)
    (hlr : (R 13).toNat = out.length) (hl1 : (R 15).toNat = out.length + 1)
    (hk : ∀ R' Mt', Keeps [13, 14, 15] R' R → (R' 15).toNat = out.length + 1 →
      Emitted S Mt Mt' k dst (out ++ [48#8]) →
      DWS live S Q t0 dst (out ++ [48#8]) 0x80000464#64 R' Mt') :
    DWS live S Q t0 dst out 0x80000450#64 R Mt := by
  emit_tac 0x80000464 9 14 (48#8) stP_80000588

/-! ## The `-` of `%d` (`0x800004a8`)

```
800004a8 beqz a3,80000594 ; 800004ac lw a2,0(a3) ; 800004b0 li a3,1
800004b4 bne a2,a3,800004cc ; … ; 800004cc sd a4,24(s1)  → 800004d0
80000594 ld a3,16(s1) ; 80000598 bgeu a4,a3,800004cc ; 8000059c ld a4,8(s1)
800005a0 li a3,45 ; 800005a4 add a4,a4,a2 ; 800005a8 sb a3,0(a4)
800005ac ld a4,24(s1) ; 800005b0 addi a4,a4,1 ; 800005b4 j 800004cc
```
`s1` the sink, `a3` its first word, `a2` the count, `a4` the count plus
one; the byte `-`.
-/

theorem emit_800004a8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {k : Nat} {dst : SinkDst} {out : List (BitVec 8)}
    (hs : SinkAt S Mt k dst out) (hsh : out.length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hkr : (R 9).toNat = k) (hfr : (R 13).toNat = dst.fw)
    (hlr : (R 12).toNat = out.length) (hl1 : (R 14).toNat = out.length + 1)
    (hk : ∀ R' Mt', Keeps [12, 13, 14] R' R → (R' 14).toNat = out.length + 1 →
      Emitted S Mt Mt' k dst (out ++ [45#8]) →
      DWS live S Q t0 dst (out ++ [45#8]) 0x800004d0#64 R' Mt') :
    DWS live S Q t0 dst out 0x800004a8#64 R Mt := by
  emit_tac 0x800004d0 9 13 (45#8) stP_800004c8

/-! ## A byte of `%s` (`0x80000270`)

```
80000270 beqz a1,80000330 ; 80000274 lw a3,0(a1) ; 80000278 beq a3,a0,800002a0
8000027c mv a3,a2 ; 80000280 sd a3,24(s1)            → 80000284
80000330 ld a1,16(s1) ; 80000334 bgeu a2,a1,8000027c ; 80000338 ld a2,8(s1)
8000033c add a3,a2,a3 ; 80000340 sb a4,0(a3) ; 80000344 ld a3,24(s1)
80000348 addi a3,a3,1 ; 8000034c j 80000280
```
`s1` the sink, `a1` its first word, `a3` the count, `a2` the count plus
one, `a4` the byte, `a0 = 1`.
-/

theorem emit_80000270 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {k : Nat} {dst : SinkDst} {out : List (BitVec 8)}
    (hs : SinkAt S Mt k dst out) (c : BitVec 8) (hsh : out.length + 1 < 2 ^ 62)
    (R : Nat → BitVec 64) (hkr : (R 9).toNat = k) (hfr : (R 11).toNat = dst.fw)
    (hlr : (R 13).toNat = out.length) (hl1 : (R 12).toNat = out.length + 1)
    (hc : R 14 = zero_extend (m := 64) c) (h1 : (R 10).toNat = 1)
    (hpw : R 16 = 72339069014638592#64)
    (hk : ∀ R' Mt', Keeps [11, 12, 13, 14] R' R → (R' 13).toNat = out.length + 1 →
      Emitted S Mt Mt' k dst (out ++ [c]) →
      DWS live S Q t0 dst (out ++ [c]) 0x80000284#64 R' Mt') :
    DWS live S Q t0 dst out 0x80000270#64 R Mt := by
  emit_tac 0x80000284 9 11 c stP_800002a8

end Dc.Mach
