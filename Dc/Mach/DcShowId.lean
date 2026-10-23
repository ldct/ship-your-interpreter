import Dc.Mach.DcMsg

/-!
# `dc_show_id` (M9)

    if (isgraph (id)) fprintf (f, "'%c' (%#o)%s", id, id, suffix);
    else fprintf (f, "%#o%s", id, suffix);

`dc_show_id_spec`: to any stream, with a suffix in `.rodata`; the bytes sent
are `showIdBytes id m sfx` (the formatter's output for the route taken).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `"'%c' (%#o)%s"` at `0x80007c28`. -/
def showIdPs : List Piece :=
  [.lit 39#8, .conv false false .c, .lit 39#8, .lit 32#8, .lit 40#8, .conv true false .o,
    .lit 41#8, .conv false false .s]

/-- `"%#o%s"` at `0x80007c38`. -/
def showOctPs : List Piece := [.conv true false .o, .conv false false .s]

theorem showIdPs_ro : RoBytes 0x80007c28 (fmtBytes showIdPs ++ [0#8]) := by
  show RoBytes _ [39#8, 37#8, 99#8, 39#8, 32#8, 40#8, 37#8, 35#8, 111#8, 41#8, 37#8, 115#8, 0#8]
  simp only [RoBytes]
  repeat' apply And.intro
  all_goals first | decide +kernel | trivial

theorem showOctPs_ro : RoBytes 0x80007c38 (fmtBytes showOctPs ++ [0#8]) := by
  show RoBytes _ [37#8, 35#8, 111#8, 37#8, 115#8, 0#8]
  simp only [RoBytes]
  repeat' apply And.intro
  all_goals first | decide +kernel | trivial

theorem uval_lt (lng : Bool) (w : BitVec 64) : uval lng w < 2 ^ 64 := by
  unfold uval; have := w.isLt; split <;> omega

theorem oct_len (w : BitVec 64) :
    (convOut true false .o ⟨w, []⟩).length ≤ 23 := by
  have := ndig_le22 (b := 8) (v := uval false w) (by omega) (uval_lt _ _)
  simp only [convOut, List.length_append, udigits_length]
  split <;> simp only [List.length_cons, List.length_nil] <;> omega

theorem showOct_len (w m : BitVec 64) (sfx : List (BitVec 8)) :
    (fmt showOctPs [⟨w, []⟩, ⟨m, sfx⟩]).length ≤ 23 + sfx.length := by
  have := oct_len w
  simp only [showOctPs, fmt, List.length_append, List.length_nil,
    show convOut false false .s ⟨m, sfx⟩ = sfx from rfl]; omega

theorem showId_len (w m : BitVec 64) (sfx : List (BitVec 8)) :
    (fmt showIdPs [⟨w, []⟩, ⟨w, []⟩, ⟨m, sfx⟩]).length ≤ 29 + sfx.length := by
  have := oct_len w
  simp only [showIdPs, fmt, List.length_append, List.length_cons, List.length_nil,
    show convOut false false .s ⟨m, sfx⟩ = sfx from rfl,
    show convOut false false .c ⟨w, []⟩ = [w.setWidth 8] from rfl]; omega

/-- The bytes `dc_show_id` sends: the `isgraph` route or the octal-only one. -/
def showIdBytes (id m : Nat) (sfx : List (BitVec 8)) : List (BitVec 8) :=
  if 33 ≤ id ∧ id ≤ 126 then
    fmt showIdPs [⟨BitVec.ofNat 64 id, []⟩, ⟨BitVec.ofNat 64 id, []⟩, ⟨BitVec.ofNat 64 m, sfx⟩]
  else fmt showOctPs [⟨BitVec.ofNat 64 id, []⟩, ⟨BitVec.ofNat 64 m, sfx⟩]

/-- `addiw a4, a1, -33; bltu 93, a4`: `id` is not in `'!'..'~'`. -/
theorem show_br {id : Nat} (hid : id < 2 ^ 31) :
    93 < (BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (BitVec.ofNat 64 id + 18446744073709551583#64))).toNat ↔ ¬ (33 ≤ id ∧ id ≤ 126) := by
  by_cases h : 33 ≤ id
  · have e : BitVec.ofNat 64 id + 18446744073709551583#64 = BitVec.ofNat 64 (id - 33) := by
      change BitVec.ofNat 64 id + -(33#64) = _
      rw [BitVec.add_neg_eq_sub]
      exact BitVec.ofNat_sub_ofNat_of_le id 33 (by decide) h
    rw [e, sxw_ofNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hs : ∀ k, k < 33 → 93 < (BitVec.signExtend 64 (BitVec.extractLsb 31 0
        (BitVec.ofNat 64 k + 18446744073709551583#64))).toNat := by decide +kernel
    simp only [hs id (by omega), true_iff]; omega

/-- **`dc_show_id(f, id, suffix)`** at `0x80001ec0`: `id` as a character and
in octal, or in octal only, then the suffix, to the stream `f`. -/
theorem dc_show_id_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t0 : String} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp f fd id m : Nat} {sfx : List (BitVec 8)}
    (hfr : StackFrame S sp 304) (hfd : FdAt S M f fd) (hfoff : f + 4 ≤ sp - 304 ∨ sp ≤ f)
    (hsfx : RoStr m sfx) (hlen : sfx.length < 2 ^ 40)
    (R : Nat → BitVec 64) (h10 : (R 10).toNat = f) (h11 : R 11 = BitVec.ofNat 64 id)
    (hid : id < 2 ^ 31) (h12 : R 12 = BitVec.ofNat 64 m) (hsp : (R 2).toNat = sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps fprintfClob R' R →
      (∀ a, (a < sp - 304 ∨ sp ≤ a) → imgM M' a = imgM M a) →
      DWO live S Q (t0 ++ fdOut fd (bytesStr (showIdBytes id m sfx))) (R 1) R' M') :
    DWO live S Q t0 0x80001ec0#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hb := show_br hid
  have hm : m + 1 ≤ tohostAddr := by
    have := hsfx.bytes
    cases sfx <;> simp only [List.cons_append, List.nil_append, RoBytes] at this <;> exact this.2.2.2.1
  dx_run hlive
  · intro hc
    have hn : ¬(33 ≤ id ∧ id ≤ 126) := hb.mp (by simpa [upd, h11] using hc)
    rw [showIdBytes, if_neg hn] at hk
    dx_run hlive at 0x80001ef4
    refine st_80001ef4 hlive ?_
    refine fprintf_spec hlive (ps := showOctPs)
      (args := [⟨BitVec.ofNat 64 id, []⟩, ⟨BitVec.ofNat 64 m, sfx⟩]) hfr hfd hfoff
      (by intro pc hpc; simp only [showOctPs, List.mem_cons, List.not_mem_nil, or_false] at hpc
          rcases hpc with rfl | rfl <;> trivial)
      showOctPs_ro ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsfx, trivial⟩
      (by have := showOct_len (BitVec.ofNat 64 id) (BitVec.ofNat 64 m) sfx; omega) _ (by simp)
      (fun i hi => ?_) (by bsimp [hsp]) (by bsimp [h10]) (by bsimp []) (by bsimp [hal])
      fun R' M' hk1 _ hfr' => hk R' M' (fun z hz => ?_) hfr'
    · simp only [List.length_cons, List.length_nil] at hi
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl <;> bsimp [h11, h12] <;>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    · rw [hk1 z hz]
      simp only [fprintfClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp only [upd, show z ≠ 11 by omega, show z ≠ 12 by omega, show z ≠ 13 by omega,
        show z ≠ 14 by omega, show z ≠ 15 by omega, ite_false]
  · intro hc
    have hn : 33 ≤ id ∧ id ≤ 126 := Classical.byContradiction fun e =>
      hc (by simpa [upd, h11] using hb.mpr e)
    rw [showIdBytes, if_pos hn] at hk
    dx_run hlive at 0x80001ee0
    refine st_80001ee0 hlive ?_
    refine fprintf_spec hlive (ps := showIdPs)
      (args := [⟨BitVec.ofNat 64 id, []⟩, ⟨BitVec.ofNat 64 id, []⟩, ⟨BitVec.ofNat 64 m, sfx⟩])
      hfr hfd hfoff
      (by intro pc hpc; simp only [showIdPs, List.mem_cons, List.not_mem_nil, or_false] at hpc
          rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | trivial | exact ⟨by decide, by decide⟩)
      showIdPs_ro ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsfx, trivial⟩
      (by have := showId_len (BitVec.ofNat 64 id) (BitVec.ofNat 64 m) sfx; omega) _ (by simp)
      (fun i hi => ?_) (by bsimp [hsp]) (by bsimp [h10]) (by bsimp []) (by bsimp [hal])
      fun R' M' hk1 _ hfr' => hk R' M' (fun z hz => ?_) hfr'
    · simp only [List.length_cons, List.length_nil] at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl | rfl
      · show BitVec.ofNat 64 id = _
        simp only [upd, h11, h12, Nat.add_zero]; rfl
      · show BitVec.ofNat 64 id = _
        simp only [upd, h11, h12, Nat.add_zero]; rfl
      · show BitVec.ofNat 64 m = _
        simp only [upd, h11, h12, Nat.add_zero]; rfl
    · rw [hk1 z hz]
      simp only [fprintfClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp only [upd, show z ≠ 11 by omega, show z ≠ 12 by omega, show z ≠ 13 by omega,
        show z ≠ 14 by omega, show z ≠ 15 by omega, ite_false]

end Dc.Mach
