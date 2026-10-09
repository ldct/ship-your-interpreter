import Dc.Mach.Printf

/-!
# `rt_error` and `rt_warn` (`lib/number.c`'s messages, dc's `main.c`)

    rt_error (mesg, ...)  /  rt_warn (mesg, ...):
      fprintf (stderr, "Runtime error: ");   /  "Runtime warning: "
      vfprintf (stderr, mesg, args);
      fprintf (stderr, "\n");

Every call site passes a `.rodata` message without conversions (`RtMsg`):
the three writes go to `stderr` (`FdAt … 2`), so the console is unchanged and
only the frames below `sp` change.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The pieces of a literal message. -/
def lits (bs : List (BitVec 8)) : List Piece := bs.map Piece.lit

theorem fmtBytes_lits : ∀ bs : List (BitVec 8), fmtBytes (lits bs) = bs
  | [] => rfl
  | b :: bs => by
    simp only [lits, List.map_cons, fmtBytes, List.flatMap_cons, Piece.bytes] at *
    rw [show List.flatMap Piece.bytes (List.map Piece.lit bs) = bs from fmtBytes_lits bs]; rfl

theorem fmt_lits : ∀ (bs : List (BitVec 8)) (args : List FArg), fmt (lits bs) args = bs
  | [], _ => rfl
  | b :: bs, args => by
    simp only [lits, List.map_cons, fmt]; rw [show fmt (List.map Piece.lit bs) args = bs from
      fmt_lits bs args]

theorem argStrs_lits : ∀ (bs : List (BitVec 8)) (args : List FArg), ArgStrs (lits bs) args
  | [], _ => trivial
  | b :: bs, args => by simp only [lits, List.map_cons, ArgStrs]; exact argStrs_lits bs args

/-- `stderr`'s `FILE` (`0x8001ad18`, the word at `0x80008200` of `.rodata`). -/
abbrev stderrAddr : Nat := 0x8001ad18

/-- A message of `n` bytes at `p` in `.rodata`: no `NUL`, no `%`, then `NUL`. -/
structure RtMsg (p n : Nat) : Prop where
  ro : ∀ i, i < n + 1 → (p + i, dcROImg (p + i)) ∈ dcRO
  lit : ∀ i, i < n → dcROImg (p + i) ≠ 0#8 ∧ dcROImg (p + i) ≠ 37#8
  nul : dcROImg (p + n) = 0#8
  lo : 0x80000000 ≤ p
  hi : p + n + 1 ≤ tohostAddr

/-- The bytes of the message. -/
def msgBytes (p n : Nat) : List (BitVec 8) := (List.range n).map fun i => dcROImg (p + i)

theorem msgBytes_succ (p n : Nat) : msgBytes p (n + 1) = dcROImg p :: msgBytes (p + 1) n := by
  simp only [msgBytes, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]; congr 1; omega

theorem msgBytes_length (p n : Nat) : (msgBytes p n).length = n := by simp [msgBytes]

theorem roBytes_msg : ∀ (n p : Nat), (∀ i, i < n + 1 → (p + i, dcROImg (p + i)) ∈ dcRO) →
    dcROImg (p + n) = 0#8 → 0x80000000 ≤ p → p + n + 1 ≤ tohostAddr →
    RoBytes p (msgBytes p n ++ [0#8])
  | 0, p, hro, hz, hlo, hhi => by
    simp only [Nat.add_zero] at hz
    have h0 := hro 0 (by omega)
    simp only [Nat.add_zero, hz] at h0
    exact ⟨hz, h0, hlo, by omega, trivial⟩
  | n + 1, p, hro, hz, hlo, hhi => by
    rw [msgBytes_succ, List.cons_append]
    have h0 := hro 0 (by omega)
    simp only [Nat.add_zero] at h0
    exact ⟨rfl, h0, hlo, by omega, roBytes_msg n (p + 1)
      (fun i hi => by rw [show p + 1 + i = p + (i + 1) by omega]; exact hro (i + 1) (by omega))
      (by rw [show p + 1 + n = p + (n + 1) by omega]; exact hz) (by omega) (by omega)⟩

theorem RtMsg.ro_bytes {p n : Nat} (h : RtMsg p n) : RoBytes p (msgBytes p n ++ [0#8]) :=
  roBytes_msg n p h.ro h.nul h.lo h.hi

theorem RtMsg.ok {p n : Nat} (h : RtMsg p n) : ∀ pc ∈ lits (msgBytes p n), pc.ok := by
  intro pc hpc
  simp only [lits, msgBytes, List.map_map, List.mem_map, List.mem_range] at hpc
  obtain ⟨i, hi, rfl⟩ := hpc
  exact h.lit i hi

theorem StackFrame.shrink {S : Nat → Prop} {sp n m : Nat} (h : StackFrame S sp n) (hm : m ≤ n) :
    StackFrame S sp m :=
  ⟨fun a h1 h2 => h.own a (by omega) h2, by have := h.lo; omega, h.hi, h.al⟩

set_option maxRecDepth 100000 in
theorem stderr_word : ldvf .ld dcROImg 2147516928 = BitVec.ofNat 64 stderrAddr := by decide

set_option maxRecDepth 100000 in
theorem rtWarnPre : RtMsg 0x80007d50 17 := ⟨by decide, by decide, by decide, by decide, by decide⟩
set_option maxRecDepth 100000 in
theorem rtErrPre : RtMsg 0x80007d40 15 := ⟨by decide, by decide, by decide, by decide, by decide⟩
set_option maxRecDepth 100000 in
theorem rtNewline : RtMsg 0x80007b60 1 := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem Keeps.symm {ks : List Nat} {R' R : Nat → BitVec 64} (h : Keeps ks R' R) : Keeps ks R R' :=
  fun z hz => (h z hz).symm

/-- The registers `rt_error`/`rt_warn` may change, with `ra`, `sp`, `s0`,
`s1` (restored at the end). -/
abbrev rtKeep : List Nat := 1 :: 2 :: 8 :: 9 :: fprintfClob

/-- `rt_error`/`rt_warn` between its calls: `stderr` intact, `ra`, `s0`, `s1`
saved in the 112-byte frame at `sp - 112`, the memory changed only in
`[sp - 416, sp)`, `s0 = stderr`. -/
structure RtAt (S : Nat → Prop) (M0 M : Mem) (sp : Nat) (R0 R : Nat → BitVec 64) : Prop where
  sp2 : (R 2).toNat = sp - 112
  fd : FdAt S M stderrAddr 2
  ra : ldv .ld M (sp - 112 + 40) = R0 1
  s0 : ldv .ld M (sp - 112 + 32) = R0 8
  s1 : ldv .ld M (sp - 112 + 24) = R0 9
  out : ∀ a, (a < sp - 416 ∨ sp ≤ a) → imgM M a = imgM M0 a
  keep : Keeps rtKeep R R0
  w8 : R 8 = BitVec.ofNat 64 stderrAddr

/-- Through a callee that changes registers in `fprintfClob` and memory below
`sp - 112`. -/
theorem RtAt.call {S : Nat → Prop} {M0 M M' : Mem} {sp : Nat} {R0 R R' : Nat → BitVec 64}
    {cl : List Nat} (h : RtAt S M0 M sp R0 R) (hcl : ∀ z ∈ cl, z ∈ 1 :: fprintfClob)
    (hkp : Keeps cl R' R) (hfar : stderrAddr + 4 ≤ sp - 416)
    (hag : ∀ a, (a < sp - 416 ∨ sp - 112 ≤ a) → imgM M' a = imgM M a) :
    RtAt S M0 M' sp R0 R' := by
  have hsf := h.sp2
  have k2 : R' 2 = R 2 := hkp 2 fun hm => absurd (hcl 2 hm) (by decide)
  have k8 : R' 8 = R 8 := hkp 8 fun hm => absurd (hcl 8 hm) (by decide)
  have hsp : 416 ≤ sp := by simp only [stderrAddr] at hfar; omega
  exact
    { sp2 := by rw [k2]; exact hsf
      fd := h.fd.transport fun j hj => hag _ (.inl (by simp only [stderrAddr] at hfar ⊢; omega))
      ra := by rw [ldv_ld_congr fun j hj => hag _ (.inr (by omega))]; exact h.ra
      s0 := by rw [ldv_ld_congr fun j hj => hag _ (.inr (by omega))]; exact h.s0
      s1 := by rw [ldv_ld_congr fun j hj => hag _ (.inr (by omega))]; exact h.s1
      out := fun a ha => by
        rw [hag a (by omega)]; exact h.out a ha
      keep := (hkp.mono fun z hz => by
        have := hcl z hz
        simp only [rtKeep, fprintfClob, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
        omega).trans h.keep
      w8 := by rw [k8]; exact h.w8 }

/-- Through the store of `ap` at `sp - 112 + 8`. -/
theorem RtAt.store8 {S : Nat → Prop} {M0 M : Mem} {sp : Nat} {R0 R : Nat → BitVec 64}
    (h : RtAt S M0 M sp R0 R) (v : BitVec 64) (hfar : stderrAddr + 4 ≤ sp - 416) :
    RtAt S M0 (writeLog M [(sp - 112 + 8, 8, v)]) sp R0 R := by
  have hsp : 416 ≤ sp := by simp only [stderrAddr] at hfar; omega
  exact
    { h with
      fd := h.fd.transport fun j hj => imgM_store_miss _ _ (by simp only [stderrAddr] at hfar ⊢; omega)
      ra := by rw [ldv_ld_miss _ _ (by omega)]; exact h.ra
      s0 := by rw [ldv_ld_miss _ _ (by omega)]; exact h.s0
      s1 := by rw [ldv_ld_miss _ _ (by omega)]; exact h.s1
      out := fun a ha => by rw [imgM_store_miss _ _ (by omega)]; exact h.out a ha }

end Dc.Mach
