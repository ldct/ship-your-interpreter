import Dc.Mach.EvalQuit

/-!
# `evalstr`'s `DC_COMMENT` route (M10)

`DC_COMMENT` (`0x800015a8`): `memchr (s7, '\n', end - s7)`; a newline at
`p` continues at `p + 1` (`skipEol`), none ends the string's evaluation.
`skipEol_find` ties `findFrom` to `skipEol`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `skipEol` drops a prefix. -/
theorem skipEol_drop : ∀ (s : List Nat), skipEol s = s.drop (s.length - (skipEol s).length)
  | [] => rfl
  | c :: cs => by
    unfold skipEol
    split
    · simp
    · rw [skipEol_drop cs]
      have : (cs.drop (cs.length - (skipEol cs).length)).length ≤ cs.length := by simp
      rw [← skipEol_drop cs]
      have hle : (skipEol cs).length ≤ cs.length := by rw [skipEol_drop cs]; simp
      rw [List.length_cons, show cs.length + 1 - (skipEol cs).length =
        (cs.length - (skipEol cs).length) + 1 by omega, List.drop_succ_cons, ← skipEol_drop cs]

/-- **`memchr (s, '\n', |s|)` against `skipEol`**: a newline at `p` leaves
the input after it; none leaves nothing. -/
theorem skipEol_find (f : Nat → BitVec 8) : ∀ (s : List Nat) (a : Nat),
    (∀ i, i < s.length → f (a + i) = BitVec.ofNat 8 (s.getD i 0)) → (∀ c ∈ s, c < 256) →
      (∀ p, findFrom f 10#8 a s.length = some p →
        a + (s.length - (skipEol s).length) = p + 1) ∧
      (findFrom f 10#8 a s.length = none → skipEol s = [])
  | [], _, _, _ => ⟨fun p h => by simp [findFrom] at h, fun _ => rfl⟩
  | c :: cs, a, hv, hb => by
    have hcb := hb c List.mem_cons_self
    have h0 := hv 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    have ih := skipEol_find f cs (a + 1) (fun i hi => by
      have := hv (i + 1) (by simp; omega)
      rw [show a + (i + 1) = a + 1 + i by omega] at this
      simpa using this) (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    by_cases c10 : c = 10
    · subst c10
      rw [List.length_cons, findFrom_hit _ h0]
      refine ⟨fun p hp => ?_, fun hp => by cases hp⟩
      simp only [Option.some.injEq] at hp
      subst hp
      simp [skipEol]
    · have hne : f a ≠ 10#8 := by
        rw [h0]; intro e
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt hcb] at this; exact c10 this
      rw [List.length_cons, findFrom_miss _ hne]
      have hs : skipEol (c :: cs) = skipEol cs := by simp [skipEol, c10]
      rw [hs]
      have hle : (skipEol cs).length ≤ cs.length := by rw [skipEol_drop cs]; simp
      exact ⟨fun p hp => by have := ih.1 p hp; omega, ih.2⟩

theorem findFrom_bounds {f : Nat → BitVec 8} {c : BitVec 8} :
    ∀ {a n p : Nat}, findFrom f c a n = some p → a ≤ p ∧ p < a + n
  | _, 0, _, h => by simp [findFrom] at h
  | a, n + 1, p, h => by
    unfold findFrom at h
    split at h
    · cases h; omega
    · have := findFrom_bounds h; omega

/-- **`DC_COMMENT`** (`0x800015a8`, `s7` the position after the command,
`OwnedBytes` of the rest): `memchr` then `s0 = p + 1`, `a2 = 0` and the
test at `0x800015c4`, or the exit. -/
theorem rt_comment {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t : String} {R : Nat → BitVec 64} {M : Mem} {a n : Nat}
    (hs : OwnedBytes S a n) (h23 : R 23 = BitVec.ofNat 64 a) (h9 : R 9 = BitVec.ofNat 64 (a + n))
    (hnone : findFrom (imgM M) 10#8 a n = none → ∀ R2, Keeps [1, 10, 11, 12, 15] R2 R →
      DWO live S Q t 0x8000156c#64 R2 M)
    (hsome : ∀ p, findFrom (imgM M) 10#8 a n = some p → ∀ R2, Keeps [1, 8, 10, 11, 12, 15] R2 R →
      R2 8 = BitVec.ofNat 64 (p + 1) → R2 12 = 0#64 → DWO live S Q t 0x800015c4#64 R2 M) :
    DWO live S Q t 0x800015a8#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hhi := hs.hi
  have hsub : BitVec.ofNat 64 (a + n) - BitVec.ofNat 64 a = BitVec.ofNat 64 n := by
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]; congr 1; omega
  bc_run hlive hlive [h23, h9, hsub] at 0x800008ac
  refine memchr_spec hlive hs _ (by bsimp []) (by bsimp []) (by bsimp []) fun R1 k1 e10 => ?_
  bsimp []
  have hlo := hs.lo
  have e10' : R1 10 = ptrOr0 (findFrom (imgM M) 10#8 a n) := by rw [e10]; bsimp []; rfl
  cases hf : findFrom (imgM M) 10#8 a n with
  | none =>
    rw [hf] at e10'
    have e0 : R1 10 = 0#64 := e10'
    bc_run hlive hlive [e0] at 0x8000156c
    exact hnone hf _ (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  | some p =>
    rw [hf] at e10'
    have ep : R1 10 = BitVec.ofNat 64 p := e10'
    have hpa : a ≤ p ∧ p < a + n := findFrom_bounds hf
    have hnz : BitVec.ofNat 64 p ≠ 0#64 := by
      intro h; have := congrArg BitVec.toNat h; simp at this; omega
    bc_run hlive hlive [ep] at 0x800015c4
    all_goals first | (intro hc; exact absurd hc hnz) | intro _
    bc_run hlive hlive [ep] at 0x800015c4
    exact hsome p hf _ (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (by bsimp []) (by bsimp [])

end Dc.Mach
