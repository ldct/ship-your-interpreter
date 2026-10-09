import Dc.Mach.RtMsg
import Dc.Mach.StateOps

/-!
# dc's own error messages (M9)

    fprintf (stderr, "%s: <message>\n", progname);

`ProgMsg p n`: the format at `p` is `%s` and `n` literal bytes. `progname` is
`"dc"` (`dcNameAddr`). `fprintf_prog_spec` prints to `stderr`, so the console
is unchanged; only the 304 bytes below `sp` change. `DcAt.errFile` supplies the
stream.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A format `"%s<msg>"` at `p` in `.rodata`, the message `n` bytes. -/
structure ProgMsg (p n : Nat) : Prop where
  pct : dcROImg p = 37#8 ∧ (p, 37#8) ∈ dcRO
  s : dcROImg (p + 1) = 115#8 ∧ (p + 1, 115#8) ∈ dcRO
  msg : RtMsg (p + 2) n
  lo : 0x80000000 ≤ p

/-- The pieces of a `ProgMsg`. -/
def progPieces (p n : Nat) : List Piece := .conv false false .s :: lits (msgBytes (p + 2) n)

/-- `"dc"` in `.rodata`. -/
theorem dcName_str : RoStr dcNameAddr [100#8, 99#8] :=
  ⟨by simp only [RoBytes, List.cons_append, List.nil_append]; decide +kernel, by decide⟩

/-- `progname`'s argument. -/
def progArg : FArg := ⟨BitVec.ofNat 64 dcNameAddr, [100#8, 99#8]⟩

theorem ProgMsg.ro {p n : Nat} (h : ProgMsg p n) :
    RoBytes p (fmtBytes (progPieces p n) ++ [0#8]) := by
  have hm := h.msg.ro_bytes
  have hlo := h.msg.lo
  have hhi := h.msg.hi
  have hlo' := h.lo
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [progPieces, fmtBytes, List.flatMap_cons, Piece.bytes] at *
  rw [show List.flatMap Piece.bytes (lits (msgBytes (p + 2) n)) = msgBytes (p + 2) n from
    fmtBytes_lits _]
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, Conv.char, List.cons_append,
    RoBytes]
  exact ⟨h.pct.1, h.pct.2, by omega, by omega, h.s.1, h.s.2, by omega, by omega, hm⟩

theorem ProgMsg.ok {p n : Nat} (h : ProgMsg p n) : ∀ pc ∈ progPieces p n, pc.ok := by
  intro pc hpc
  rcases List.mem_cons.mp hpc with rfl | hpc
  · trivial
  · exact h.msg.ok pc hpc

theorem progPieces_args (p n : Nat) : ArgStrs (progPieces p n) [progArg] :=
  ⟨dcName_str, argStrs_lits _ _⟩

theorem progPieces_len (p n : Nat) : (fmt (progPieces p n) [progArg]).length = n + 2 := by
  simp only [progPieces, fmt, convOut, progArg, fmt_lits, msgBytes_length, List.cons_append,
    List.nil_append, List.length_cons]

/-- `stderr`'s stream of a dc state. -/
theorem DcAt.errFile {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S Mt H F L C G hs st) :
    FdAt S Mt stderrAddr 2 :=
  { own := fun i hi => h.glob _ (by simp only [DcGlob, dc_addrs, stderrAddr]; omega)
    val := h.view.errFd
    lo := by simp only [stderrAddr, tohostAddr]; omega
    hi := by simp only [stderrAddr]; omega
    small := by decide }

/-- **`fprintf (stderr, "%s<msg>", progname)`** at `0x80000774`. -/
theorem fprintf_prog_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp p n : Nat} (hm : ProgMsg p n) (hn : n < 2 ^ 60)
    (hfr : StackFrame S sp 304) (hfar : stderrAddr + 4 ≤ sp - 304)
    (hfd : FdAt S M stderrAddr 2) (R : Nat → BitVec 64) (hsp : (R 2).toNat = sp)
    (h10 : (R 10).toNat = stderrAddr) (h11 : (R 11).toNat = p)
    (h12 : R 12 = BitVec.ofNat 64 dcNameAddr) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps fprintfClob R' R →
      (∀ a, (a < sp - 304 ∨ sp ≤ a) → imgM M' a = imgM M a) →
      DWO live S Q t0 (R 1) R' M') :
    DWO live S Q t0 0x80000774#64 R M := by
  refine fprintf_spec (ps := progPieces p n) (args := [progArg]) hlive hfr hfd (.inl hfar) hm.ok
    hm.ro (progPieces_args p n) (by rw [progPieces_len]; omega) R (by decide)
    (fun i hi => by
      simp only [List.length_cons, List.length_nil] at hi
      have : i = 0 := by omega
      subst this; simp only [progArg]; exact h12.symm)
    hsp h10 h11 hal fun R' M' hk1 _ hfr' => ?_
  have e : t0 ++ fdOut 2 (bytesStr (fmt (progPieces p n) [progArg])) = t0 := by simp [fdOut]
  rw [e]; exact hk R' M' hk1 hfr'

theorem stackEmptyMsg : ProgMsg 0x80007d90 14 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

end Dc.Mach
