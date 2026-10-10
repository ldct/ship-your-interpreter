import Dc.Mach.Libgcc

/-!
# Output: `fputc`, `putchar`, `fwrite` (`dc-port/libc/libc.c`)

Printing runs are `DWO` (`Htif.lean`): the console string `t` grows by
`putcStr c` at each `tohost` store (`stP_<pc>`, `Tohost.lean`).

A stream is a `FILE` whose first word is the descriptor (`FdAt`): `stdout`
(`files + 4`, descriptor 1) prints, any other descriptor prints nothing.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The stream at `f` has descriptor `fd`: its first word, owned and loadable. -/
structure FdAt (S : Nat → Prop) (Mt : Mem) (f fd : Nat) : Prop where
  own : ∀ i, i < 4 → S (f + i)
  val : ldv .lw Mt f = BitVec.ofNat 64 fd
  lo : tohostAddr + 8 ≤ f
  hi : f + 4 ≤ 0x88000000
  small : fd < 2 ^ 31

/-- What a stream with descriptor `fd` shows of `s`: all of it on `stdout`. -/
def fdOut (fd : Nat) (s : String) : String := if fd = 1 then s else ""

theorem fdOut_one (s : String) : fdOut 1 s = s := rfl

theorem fdOut_ne {fd : Nat} (h : fd ≠ 1) (s : String) : fdOut fd s = "" := by
  simp [fdOut, h]

/-- `stdout`'s `FILE` (`files + 4`, in `.data`). -/
abbrev stdoutFile : Nat := 0x8001ad14

/-- An owned access of width `w`. -/
theorem accOwn {S : Nat → Prop} {a w : Nat} (h : ∀ i, i < w → S (a + i)) :
    ∀ b ∈ accAddrs a w, S b := by
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  exact h j (List.mem_range.mp hj)

/-- The console word `fputc` builds from a masked byte. -/
theorem and255_eq (x : BitVec 64) : x &&& 255#64 = BitVec.zeroExtend 64 (lo8 x) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and255]
  simp [BitVec.toNat_setWidth]
  omega

theorem putcWord_and (x : BitVec 64) :
    (x &&& 255#64) ||| 72339069014638592#64 = putcWord (lo8 x) := by
  rw [and255_eq, BitVec.or_comm]

/-! ## `putchar` (`0x80000628`)

```
80000628 auipc a4,0x1a ; 8000062c lw a4,1772(a4) ; 80000630 li a5,1
80000634 zext.b a0,a0 ; 80000638 beq a4,a5,80000640 ; 8000063c ret
80000640 li a5,257 ; 80000644 slli a5,a5,0x30 ; 80000648 or a5,a0,a5
8000064c auipc a4,0x1a ; 80000650 sd a5,1716(a4) ; 80000654 ret
```
-/

theorem putchar_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hfd : FdAt S Mt stdoutFile 1)
    (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 14, 15] R' R → R' 10 = R 10 &&& 255#64 →
      DWO live S Q (t ++ putcStr (lo8 (R 10))) (R 1) R' Mt) :
    DWO live S Q t 0x80000628#64 R Mt := by
  have hv : ldv .lw Mt 2147593492 = 1#64 := hfd.val
  dx_run hlive
  · dc_simp []; exact accOwn hfd.own
  · intro _
    dx_run hlive
    refine stP_80000650 hlive (lo8 (R 10)) (by dc_simp []) (by dc_simp []; exact putcWord_and _) ?_
    dx_run hlive
    refine hk _ (by keeps_tac Keeps.refl _ _) (by dc_simp [])
  · intro hne; dc_simp [hv] at hne; exact absurd trivial hne


/-! ## `fputc` (`0x800005fc`)

```
800005fc lw a4,0(a1) ; 80000600 li a5,1 ; 80000604 zext.b a0,a0
80000608 beq a4,a5,80000610 ; 8000060c ret
80000610 li a5,257 ; 80000614 slli a5,a5,0x30 ; 80000618 or a5,a0,a5
8000061c auipc a4,0x1a ; 80000620 sd a5,1764(a4) ; 80000624 ret
```
-/

/-- **`fputc(c, f)`** at `0x800005fc`: prints the low byte of `c` when `f` is
`stdout` (`fdOut`), returns it; clobbers `a4`, `a5`. -/
theorem fputc_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {f fd : Nat} (hfd : FdAt S Mt f fd)
    (R : Nat → BitVec 64) (h11 : R 11 = BitVec.ofNat 64 f) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 14, 15] R' R → R' 10 = R 10 &&& 255#64 →
      DWO live S Q (t ++ fdOut fd (putcStr (lo8 (R 10)))) (R 1) R' Mt) :
    DWO live S Q t 0x800005fc#64 R Mt := by
  have hlo := hfd.lo
  have hhi := hfd.hi
  have hsm := hfd.small
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive
  all_goals (try dc_simp [h11])
  · simp only [LdOK]; omega
  · exact accOwn hfd.own
  · intro heq
    rw [hfd.val] at heq
    have h1 : fd = 1 := by
      have := congrArg BitVec.toNat heq
      rwa [ofNat_toNat_lt (by omega)] at this
    subst h1
    dx_run hlive
    refine stP_80000620 hlive (lo8 (R 10)) (by dc_simp []) (by dc_simp []; exact putcWord_and _) ?_
    dx_run hlive
    exact hk _ (by keeps_tac Keeps.refl _ _) (by dc_simp [])
  · intro hne
    rw [hfd.val] at hne
    have h1 : fd ≠ 1 := fun e => hne (by rw [e])
    dx_run hlive
    have e : t = t ++ fdOut fd (putcStr (lo8 (R 10))) := by rw [fdOut_ne h1, String.append_empty]
    rw [e]
    exact hk _ (by keeps_tac Keeps.refl _ _) (by dc_simp [])


/-! ## `fwrite` (`0x80000658`)

```
80000658 addi sp,sp,-32 ; 8000065c sd s0,16(sp) ; 80000660 mv s0,a0 ; 80000664 mv a0,a1
80000668 mv a1,a2 ; 8000066c sd a2,0(sp) ; 80000670 sd ra,24(sp) ; 80000674 sd a3,8(sp)
80000678 jal __muldi3 ; 8000067c ld a2,0(sp) ; 80000680 beqz a0,800006ac
80000684 ld a3,8(sp) ; 80000688 li a4,1 ; 8000068c mv a5,s0 ; 80000690 lw a3,0(a3)
80000694 add a0,s0,a0 ; 80000698 beq a3,a4,800006c0
8000069c addi a4,a5,1 ; 800006a0 addi a5,a5,2 ; 800006a4 beq a4,a0,800006ac
800006a8 bne a5,a0,8000069c
800006ac ld ra,24(sp) ; 800006b0 ld s0,16(sp) ; 800006b4 mv a0,a2 ; 800006b8 addi sp,sp,32
800006bc ret
800006c0 lbu a4,0(s0) ; 800006c4 li a3,257 ; 800006c8 slli a3,a3,0x30
800006cc or a4,a4,a3 ; 800006d0 auipc a1,0x1a ; 800006d4 sd a4,1584(a1)
800006d8 addi a4,a5,1 ; 800006dc beq a0,a4,800006ac ; 800006e0 lbu a4,1(a5)
800006e4 addi a5,a5,2 ; 800006e8 or a4,a4,a3 ; 800006ec auipc a1,0x1a
800006f0 sd a4,1556(a1) ; 800006f4 beq a0,a5,800006ac ; 800006f8 lbu a4,0(a5)
800006fc j 800006cc
```
-/

/-- The console text of the `n` bytes at `p`. -/
def outBytes (f : Nat → BitVec 8) (p : Nat) : Nat → String
  | 0 => ""
  | k + 1 => outBytes f p k ++ putcStr (f (p + k))

theorem outBytes_succ (f : Nat → BitVec 8) (p k : Nat) :
    outBytes f p (k + 1) = outBytes f p k ++ putcStr (f (p + k)) := rfl

theorem outBytes_congr {f g : Nat → BitVec 8} {p : Nat} :
    ∀ n, (∀ i, i < n → f (p + i) = g (p + i)) → outBytes f p n = outBytes g p n
  | 0, _ => rfl
  | n + 1, h => by
    rw [outBytes_succ, outBytes_succ, outBytes_congr n (fun i hi => h i (by omega)), h n (by omega)]

theorem fdOut_empty (fd : Nat) : fdOut fd "" = "" := by
  unfold fdOut; split <;> rfl

/-- A register restored to its entry value (a callee-saved register, `sp`). -/
theorem Keeps.restore {ks : List Nat} {R' R : Nat → BitVec 64} {k : Nat} {v : BitVec 64}
    (hv : v = R k) (h : Keeps (k :: ks) R' R) : Keeps ks (VsaIris.Sym.upd R' k v) R := by
  intro z hz
  by_cases e : z = k
  · subst e; rw [upd_same, hv]
  · rw [upd_other _ _ e]; exact h z (by simp [e, hz])

/-- A frame's `sp` restored: `x - a + b = x` for literals with `a + b ≡ 0`. -/
theorem add_lits_cancel (x : BitVec 64) (a b : Nat) (h : (a + b) % 2 ^ 64 = 0) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]
  rw [show BitVec.ofNat 64 (a + b) = 0#64 from BitVec.eq_of_toNat_eq (by simp [h]), BitVec.add_zero]

theorem putcWord_zext (b : BitVec 8) :
    zero_extend (m := 64) b ||| 72339069014638592#64 = putcWord b := by
  rw [BitVec.or_comm]; rfl

/-- The printing loop of `fwrite` at `0x800006cc`: `a5 = p + i`, `a4` the byte
there, `a3` the console command, `a0 = p + len`. -/
theorem fwrite_print {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {p len : Nat} (hb : OwnedBytes S p len)
    (R0 : Nat → BitVec 64)
    (hx : ∀ R', Keeps [11, 13, 14, 15] R' R0 →
      DWO live S Q (t ++ outBytes (imgM Mt) p len) 0x800006ac#64 R' Mt) :
    ∀ k i (R : Nat → BitVec 64), len - i = k → i < len →
      R 15 = BitVec.ofNat 64 (p + i) → R 14 = zero_extend (m := 64) (imgM Mt (p + i)) →
      R 13 = 72339069014638592#64 → R 10 = BitVec.ofNat 64 (p + len) →
      Keeps [11, 13, 14, 15] R R0 →
      DWO live S Q (t ++ outBytes (imgM Mt) p i) 0x800006cc#64 R Mt := by
  have hlo := hb.lo
  have hhi := hb.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i R hn hi h15 h14 h13 h10 hkeep
    dx_run hlive
    refine stP_800006d4 hlive (imgM Mt (p + i)) (by dc_simp []) (by dc_simp [h14, h13]; exact putcWord_zext _) ?_
    rw [String.append_assoc, ← outBytes_succ]
    dx_run hlive
    all_goals (try dc_simp [h10, h15])
    · -- the last byte
      intro heq
      have hn' : i + 1 = len := by
        have := congrArg BitVec.toNat heq
        rw [ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)] at this; omega
      rw [hn']
      exact hx _ (by keeps_tac hkeep)
    · intro hne
      have hlt : i + 1 < len := by
        refine Classical.byContradiction fun hge => hne ?_
        congr 1; omega
      dx_run hlive
      dc_sides [h10, h15, h13] hb
      refine stP_800006f0 hlive (imgM Mt (p + i + 1)) (by dc_simp [])
        (by dc_simp [h13]; exact putcWord_zext _) ?_
      rw [String.append_assoc, show p + i + 1 = p + (i + 1) by omega, ← outBytes_succ]
      dx_run hlive
      all_goals (try dc_simp [h10, h15])
      · intro heq
        have hn' : i + 1 + 1 = len := by
          have := congrArg BitVec.toNat heq
          rw [ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)] at this; omega
        rw [hn']
        exact hx _ (by keeps_tac hkeep)
      · intro hne2
        have hlt2 : i + 2 < len := by
          refine Classical.byContradiction fun hge => hne2 ?_
          congr 1; omega
        dx_run hlive at 0x800006cc
        dc_sides [h10, h15, h13] hb
        rw [show i + 1 + 1 = i + 2 by omega]
        refine ih (len - (i + 2)) (by omega) (i + 2) _ rfl hlt2 ?_ ?_ ?_ ?_ (by keeps_tac hkeep)
        · dc_simp [Nat.add_assoc]
        · dc_simp [Nat.add_assoc]
        · dc_simp [h13]
        · dc_simp [h10]


/-- The silent loop of `fwrite` at `0x8000069c` (descriptor other than 1):
`a5 = p + i`, `a0 = p + len`. -/
theorem fwrite_silent {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {p len : Nat} (hb : OwnedBytes S p len)
    (R0 : Nat → BitVec 64)
    (hx : ∀ R', Keeps [14, 15] R' R0 → DWO live S Q t 0x800006ac#64 R' Mt) :
    ∀ k i (R : Nat → BitVec 64), len - i = k → i < len →
      R 15 = BitVec.ofNat 64 (p + i) → R 10 = BitVec.ofNat 64 (p + len) →
      Keeps [14, 15] R R0 → DWO live S Q t 0x8000069c#64 R Mt := by
  have hlo := hb.lo
  have hhi := hb.hi
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i R hn hi h15 h10 hkeep
    dx_run hlive
    all_goals (try dc_simp [h10, h15])
    · intro _; exact hx _ (by keeps_tac hkeep)
    · intro hne
      dx_run hlive
      all_goals (try dc_simp [h10, h15])
      · intro hne2
        refine ih (len - (i + 2)) (by omega) (i + 2) _ rfl ?_ ?_ ?_ (by keeps_tac hkeep)
        · refine Classical.byContradiction fun hge => ?_
          by_cases h1 : i + 1 = len
          · exact hne (by congr 1; omega)
          · exact hne2 (by congr 1; omega)
        · dc_simp [h15, Nat.add_assoc]
        · dc_simp [h10]
      · intro _; exact hx _ (by keeps_tac hkeep)

/-- A callee's stack frame: the `n` bytes below `sp`, owned, in RAM. -/
structure StackFrame (S : Nat → Prop) (sp n : Nat) : Prop where
  own : ∀ a, sp - n ≤ a → a < sp → S a
  lo : tohostAddr + 16 + n ≤ sp
  hi : sp ≤ 0x88000000
  al : sp % 16 = 0

/-- An access inside the stack frame `h` is owned. -/
macro "dc_frame " h:term : tactic =>
  `(tactic| (intro b hb; have hb' := of_mem_accAddrs hb; clear hb
             apply ($h).own <;> (revert hb'; sx_addr)))

/-- Only the `n` bytes at `lo` may differ between `Mt'` and `Mt`. -/
structure SameOutside (Mt' Mt : Mem) (lo n : Nat) : Prop where
  rest : ∀ a, a < lo ∨ lo + n ≤ a → imgM Mt' a = imgM Mt a

/-- A load at an address equal to one with a known value (for `simp` with
`sx_addr` discharging the address). -/
theorem ldv_eq_at {k : MKind} {M : Mem} {a : Nat} {v : BitVec 64} (h : ldv k M a = v) :
    ∀ a', a' = a → ldv k M a' = v := by
  rintro a' rfl; exact h

/-- `fwrite`'s epilogue at `0x800006ac`: reload `ra`, `s0`, return `n`. -/
theorem fwrite_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {u : String} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp : Nat} (hfr : StackFrame S sp 32)
    (R0 R2 : Nat → BitVec 64) (h2 : (R2 2).toNat = sp - 32) (h2' : R2 2 + 32#64 = R0 2)
    (hra : ldv .ld M (sp - 8) = R0 1) (hs0 : ldv .ld M (sp - 16) = R0 8)
    (h12 : R2 12 = R0 12) (hkeep : Keeps [1, 2, 8, 10, 11, 12, 13, 14, 15] R2 R0)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 12, 13, 14, 15] R' R0 → R' 10 = R0 12 → DWO live S Q u (R0 1) R' M) :
    DWO live S Q u 0x800006ac#64 R2 M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive
  all_goals (try dc_frame hfr)
  all_goals simp (disch := sx_addr) only [ldv_eq_at hra, ldv_eq_at hs0]
  all_goals (try (dc_simp [hal]; done))
  refine hk _ ?_ (by dc_simp [h12])
  refine Keeps.restore (by dc_simp [h2']) ?_
  refine Keeps.upd _ (by decide) ?_
  refine Keeps.restore rfl ?_
  refine Keeps.restore rfl ?_
  exact hkeep.mono (by decide)

/-- `fwrite` after `__muldi3` (`0x8000067c`), over a memory `M` whose frame
holds the saved words. -/
theorem fwrite_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {M Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp p len f fd : Nat} (hfr : StackFrame S sp 32)
    (hb : OwnedBytes S p len) (hdj : p + len ≤ sp - 32 ∨ sp ≤ p) (hfd : FdAt S M f fd)
    (hso : SameOutside M Mt (sp - 32) 32)
    (R0 R1 : Nat → BitVec 64) (h2 : (R1 2).toNat = sp - 32) (h2' : R1 2 + 32#64 = R0 2)
    (hra : ldv .ld M (sp - 8) = R0 1) (hs0 : ldv .ld M (sp - 16) = R0 8)
    (hn : ldv .ld M (sp - 32) = R0 12) (hf : ldv .ld M (sp - 24) = R0 13)
    (h13 : (R0 13).toNat = f) (e8 : R1 8 = BitVec.ofNat 64 p) (hl : (R1 10).toNat = len)
    (hkeep : Keeps [1, 2, 8, 10, 11, 12, 13] R1 R0) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 12, 13, 14, 15] R' R0 → R' 10 = R0 12 →
      DWO live S Q (t ++ fdOut fd (outBytes (imgM Mt) p len)) (R0 1) R' M) :
    DWO live S Q t 0x8000067c#64 R1 M := by
  have hflo := hfd.lo
  have hfhi := hfd.hi
  have hblo := hb.lo
  have hbhi := hb.hi
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hbytes : ∀ i, i < len → imgM M (p + i) = imgM Mt (p + i) :=
    fun i hi => hso.rest _ (by omega)
  have hex : ∀ (u : String) (R2 : Nat → BitVec 64), R2 2 = R1 2 → R2 12 = R0 12 →
      Keeps [1, 2, 8, 10, 11, 12, 13, 14, 15] R2 R0 →
      (∀ R', Keeps [10, 11, 12, 13, 14, 15] R' R0 → R' 10 = R0 12 → DWO live S Q u (R0 1) R' M) →
      DWO live S Q u 0x800006ac#64 R2 M := fun u R2 e2 e12 hk2 hku =>
    fwrite_exit hlive hfr R0 R2 (by rw [e2, h2]) (by rw [e2, h2']) hra hs0 e12 hk2 hal hku
  have hend : R1 8 + R1 10 = BitVec.ofNat 64 (p + len) := by
    rw [e8, show R1 10 = BitVec.ofNat 64 len from BitVec.eq_of_toNat_eq (by rw [hl]; dc_simp [])]
    dc_simp []
  dx_run hlive
  all_goals (try dc_frame hfr)
  all_goals (try simp (disch := sx_addr) only [ldv_eq_at hn])
  · -- `size * n = 0`
    intro hz
    dc_simp [] at hz
    have hl0 : len = 0 := by rw [← hl, hz]; rfl
    subst hl0
    refine hex t _ (by dc_simp []) (by dc_simp []) (by keeps_tac (hkeep.mono (by decide))) ?_
    intro R' h1 h2
    have := hk R' h1 h2
    rwa [outBytes, fdOut_empty, String.append_empty] at this
  · intro hnz
    dc_simp [] at hnz
    have hlpos : 0 < len :=
      Nat.pos_of_ne_zero fun h0 => hnz (BitVec.eq_of_toNat_eq (by rw [hl, h0]; rfl))
    have hbase : Keeps [1, 2, 8, 10, 11, 12, 13, 14, 15] R1 R0 := hkeep.mono (by decide)
    dx_run hlive
    all_goals (try dc_frame hfr)
    all_goals (try simp (disch := sx_addr) only [ldv_eq_at hf, ldv_eq_at hfd.val])
    all_goals (try (dc_simp [h13]; simp only [LdOK]; omega))
    all_goals (try (dc_simp [h13]; exact accOwn hfd.own))
    · -- `stdout`: print the bytes
      intro heq
      dc_simp [] at heq
      have h1 : fd = 1 := by
        have := congrArg BitVec.toNat heq
        rwa [ofNat_toNat_lt (by have := hfd.small; omega)] at this
      subst h1
      dx_run hlive at 0x800006cc
      all_goals (try (dc_simp [e8]; simp only [LdOK]; omega))
      all_goals (try (dc_simp [e8]; exact acc1 (hb.own' (by omega) (by omega))))
      rw [show t = t ++ outBytes (imgM M) p 0 by simp [outBytes]]
      refine fwrite_print hlive hb _ (fun R' hk' => ?_) (len - 0) 0 _ rfl hlpos ?_ ?_ ?_ ?_
        (by keeps_tac Keeps.refl _ _)
      · refine hex _ R' (by rw [hk'.get 2]; dc_simp []) (by rw [hk'.get 12]; dc_simp []) ?_ ?_
        · exact (hk'.mono (by decide)).trans (by keeps_tac hbase)
        · intro R'' h1 h2
          have := hk R'' h1 h2
          rwa [fdOut_one, outBytes_congr len (fun i hi => (hbytes i hi).symm)] at this
      · dc_simp [e8]
      · dc_simp [e8]
      · dc_simp []
      · dc_simp [hend]
    · -- another stream: the silent loop
      intro hne
      dc_simp [] at hne
      have h1 : fd ≠ 1 := fun e => hne (by rw [e])
      refine fwrite_silent hlive hb _ (fun R' hk' => ?_) (len - 0) 0 _ rfl hlpos ?_ ?_
        (by keeps_tac Keeps.refl _ _)
      · refine hex _ R' (by rw [hk'.get 2]; dc_simp []) (by rw [hk'.get 12]; dc_simp []) ?_ ?_
        · exact (hk'.mono (by decide)).trans (by keeps_tac hbase)
        · intro R'' h1' h2
          have := hk R'' h1' h2
          rwa [fdOut_ne h1, String.append_empty] at this
      · dc_simp [e8]
      · dc_simp [hend]


/-- `fwrite`'s arguments: its frame, the `len` bytes at `p` and the stream,
disjoint from the frame. -/
structure FwriteArgs (S : Nat → Prop) (Mt : Mem) (sp p len f fd : Nat) : Prop where
  frame : StackFrame S sp 32
  buf : OwnedBytes S p len
  bufOff : p + len ≤ sp - 32 ∨ sp ≤ p
  file : FdAt S Mt f fd
  fileOff : f + 4 ≤ sp - 32 ∨ sp ≤ f

/-- **`fwrite(p, size, n, f)`** at `0x80000658`: prints the `size * n` bytes at
`p` when `f` is `stdout` (`fdOut`), returns `n`; clobbers `a0`–`a5` and only
its 32-byte frame. -/
theorem fwrite_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp p len f fd : Nat} (ha : FwriteArgs S Mt sp p len f fd)
    (R : Nat → BitVec 64) (hsp : (R 2).toNat = sp) (h10 : R 10 = BitVec.ofNat 64 p)
    (hlen : (R 11 * R 12).toNat = len) (h13 : (R 13).toNat = f) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [10, 11, 12, 13, 14, 15] R' R → R' 10 = R 12 →
      SameOutside Mt' Mt (sp - 32) 32 →
      DWO live S Q (t ++ fdOut fd (outBytes (imgM Mt) p len)) (R 1) R' Mt') :
    DWO live S Q t 0x80000658#64 R Mt := by
  have hfr := ha.frame
  have hfdj := ha.fileOff
  have hflo := ha.file.lo
  have hfhi := ha.file.hi
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive at 0x800078a4
  all_goals (try dc_frame hfr)
  refine muldi3_spec hlive _ (by dc_simp []; try decide) fun R1 hk1 hmul => ?_
  refine fwrite_body (fd := fd) (Mt := Mt) hlive hfr ha.buf ha.bufOff ?fd ?so R R1 ?h2 ?h2' ?ra ?s0 ?n ?f h13 ?e8 ?hl
    ?keep hal ?hk
  case fd =>
    refine ⟨ha.file.own, ?_, ha.file.lo, ha.file.hi, ha.file.small⟩
    simp (disch := sx_addr) only [ldv_lw_miss]; exact ha.file.val
  case so =>
    constructor
    intro a ha
    simp (disch := sx_addr) only [imgM_store_miss]
  case h2 => rw [hk1.get 2]; sx_addr
  case h2' => rw [hk1.get 2]; dc_simp []; exact add_lits_cancel _ _ _ (by decide)
  case ra => simp (disch := sx_addr) only [ldv_ld_hit_eq, ldv_ld_miss]
  case s0 => simp (disch := sx_addr) only [ldv_ld_hit_eq, ldv_ld_miss]
  case n => simp (disch := sx_addr) only [ldv_ld_hit_eq, ldv_ld_miss]
  case f => simp (disch := sx_addr) only [ldv_ld_hit_eq, ldv_ld_miss]
  case e8 => rw [hk1.get 8]; dc_simp [h10]
  case hl => rw [hmul]; dc_simp [hlen]
  case keep => exact (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  case hk =>
    intro R' h1 h2
    exact hk R' _ h1 h2 ⟨fun a ha => by simp (disch := sx_addr) only [imgM_store_miss]⟩

end Dc.Mach
