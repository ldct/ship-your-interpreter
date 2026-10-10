import Dc.Mach.EvalScan

/-!
# `DC_EVALTOS`'s whitespace and comment skip (M10)

`skipWs` as a suffix of its input (`skipWs_cons`, `skipWs_drop`); the
machine's skip at `0x8000175c` (`skip_loop`, the `#` case `skip_hash` over
`memchr`) ends at the text's end (`0x8000179c`) when `skipWs` leaves
nothing, else at the first other byte (`0x800017d8`).
-/

namespace Dc
theorem skipEol_length_le : ∀ s : List Nat, (skipEol s).length ≤ s.length
  | [] => by simp [skipEol]
  | c :: cs => by
    unfold skipEol
    split
    · simp
    · have := skipEol_length_le cs; simp; omega

theorem skipWsF_eq : ∀ (f g : Nat) (s : List Nat), s.length ≤ f → s.length ≤ g →
    skipWsF f s = skipWsF g s
  | 0, g, s, hf, _ => by
    cases s with
    | nil => cases g <;> rfl
    | cons c cs => simp at hf
  | f + 1, 0, s, _, hg => by
    cases s with
    | nil => rfl
    | cons c cs => simp at hg
  | f + 1, g + 1, [], _, _ => rfl
  | f + 1, g + 1, c :: cs, hf, hg => by
    simp only [skipWsF]
    have h1 := skipEol_length_le cs
    simp only [List.length_cons] at hf hg
    split
    · exact skipWsF_eq f g cs (by omega) (by omega)
    · split
      · exact skipWsF_eq f g _ (by omega) (by omega)
      · rfl

theorem skipWs_nil : skipWs [] = [] := rfl

theorem skipWs_cons (c : Nat) (cs : List Nat) :
    skipWs (c :: cs) = if c == 32 || c == 9 || c == 10 then skipWs cs
      else if c == 35 then skipWs (skipEol cs) else c :: cs := by
  have h1 := skipEol_length_le cs
  unfold skipWs
  simp only [List.length_cons, skipWsF]
  split
  · rfl
  · split
    · exact skipWsF_eq _ _ _ (by omega) (Nat.le_refl _)
    · rfl

theorem skipWs_length_le : ∀ (n : Nat) (s : List Nat), s.length ≤ n → (skipWs s).length ≤ s.length
  | _, [], _ => by simp [skipWs_nil]
  | 0, _ :: _, h => by simp at h
  | n + 1, c :: cs, h => by
    have h1 := skipEol_length_le cs
    simp only [List.length_cons] at h
    rw [skipWs_cons]
    split
    · have := skipWs_length_le n cs (by omega); simp; omega
    · split
      · have := skipWs_length_le n (skipEol cs) (by omega); simp; omega
      · simp

theorem skipWs_drop : ∀ (n : Nat) (s : List Nat), s.length ≤ n →
    skipWs s = s.drop (s.length - (skipWs s).length)
  | _, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, c :: cs, h => by
    have h1 := skipEol_length_le cs
    simp only [List.length_cons] at h
    rw [skipWs_cons]
    split
    · have hl := skipWs_length_le n cs (by omega)
      rw [List.length_cons, show cs.length + 1 - (skipWs cs).length =
        (cs.length - (skipWs cs).length) + 1 by omega, List.drop_succ_cons, ← skipWs_drop n cs (by omega)]
    · split
      · have hl := skipWs_length_le n (skipEol cs) (by omega)
        have e := skipWs_drop n (skipEol cs) (by omega)
        have hE := Mach.skipEol_drop cs
        rw [List.length_cons, show cs.length + 1 - (skipWs (skipEol cs)).length =
          (cs.length - (skipWs (skipEol cs)).length) + 1 by omega, List.drop_succ_cons]
        refine e.trans ?_
        have e2 : (skipEol cs).drop ((skipEol cs).length - (skipWs (skipEol cs)).length) =
            (cs.drop (cs.length - (skipEol cs).length)).drop
              ((skipEol cs).length - (skipWs (skipEol cs)).length) := by rw [← hE]
        rw [e2, List.drop_drop]
        congr 1
        omega
      · rw [Nat.sub_self, List.drop_zero]
end Dc

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

theorem wsBit_all : ∀ c, c < 36 →
    ((38654707200#64 >>> (BitVec.extractLsb 5 0 (BitVec.ofNat 64 c)).toNat &&& 1#64 = 0#64) ↔
      ¬ (c = 9 ∨ c = 10 ∨ c = 32 ∨ c = 35)) := by decide

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t : String} {M : Mem}

/-- The registers the skip loop writes. -/
abbrev skipClob : List Nat := [1, 8, 10, 11, 12, 13, 14, 15]

/-- **A `#` in the skip** (`0x8000175c`, byte `i` the `#`): `memchr` for
the newline; on after it, or the end. -/
theorem skip_hash (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {pay N i : Nat} {s : List Nat}
    (hsN : s.length = N) (hi : i < N) (hlo : 2147603920 ≤ pay) (hhi : pay + N ≤ 2273312768)
    (himg : ∀ k, k < N → imgM M (pay + k) = BitVec.ofNat 8 (s.getD k 0))
    (hbyte : ∀ c ∈ s, c < 256) {R : Nat → BitVec 64}
    (hb : ldv .lbu M (pay + i) = BitVec.ofNat 64 35)
    (h8 : R 8 = BitVec.ofNat 64 (pay + i)) (h9 : R 9 = BitVec.ofNat 64 (pay + N))
    (h13 : R 13 = BitVec.ofNat 64 35) (h23 : R 23 = 0x900000600#64)
    (hgo : ∀ i', i < i' → i' < N → skipWs (35 :: s.drop (i + 1)) = skipWs (s.drop i') →
      ∀ R2, Keeps skipClob R2 R → R2 8 = BitVec.ofNat 64 (pay + i') → R2 9 = R 9 → R2 13 = R 13 →
      R2 23 = R 23 → DWO live S Q t 0x8000175c#64 R2 M)
    (hnext : ∀ i', i < i' → i' ≤ N → skipWs (35 :: s.drop (i + 1)) = skipWs (s.drop i') →
      ∀ R2, Keeps skipClob R2 R → R2 8 = BitVec.ofNat 64 (pay + i') → R2 9 = R 9 → R2 13 = R 13 →
      R2 23 = R 23 → DWO live S Q t 0x80001758#64 R2 M)
    (hfin : skipWs (35 :: s.drop (i + 1)) = [] → ∀ R2, Keeps skipClob R2 R →
      R2 8 = BitVec.ofNat 64 (pay + N) → DWO live S Q t 0x8000179c#64 R2 M) :
    DWO live S Q t 0x8000175c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hdl : (s.drop (i + 1)).length = N - (i + 1) := by rw [List.length_drop, hsN]
  have hcn : (BitVec.ofNat 64 35).toNat = 35 := rfl
  have hb1 : ¬ (38654707200#64 >>> (BitVec.extractLsb 5 0 (BitVec.ofNat 64 35)).toNat &&& 1#64 = 0#64) := by
    decide
  have hsub : BitVec.ofNat 64 (pay + N) - BitVec.ofNat 64 (pay + i + 1) =
      BitVec.ofNat 64 (N - (i + 1)) := by
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]; congr 1; omega
  have hadd : BitVec.ofNat 64 (pay + i) + 1#64 = BitVec.ofNat 64 (pay + i + 1) := by
    rw [show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
  bc_run hlive hS [h8, h9, h13, h23, hb, hcn, hb1, hadd, hsub] at 0x800008ac
  all_goals first | (intro hc'; exact absurd hc' (by omega)) | (intro hc'; exact absurd hc' (by decide)) | intro _ | skip
  bc_run hlive hS [h8, h9, h13, h23, hb, hcn, hb1, hadd, hsub] at 0x800008ac
  all_goals first | (intro hc'; exact absurd hc' (by omega)) | (intro hc'; exact absurd hc' (by decide)) | intro _ | skip
  bc_run hlive hS [h8, h9, h13, h23, hb, hcn, hb1, hadd, hsub] at 0x800008ac
  all_goals first | (intro hc'; exact absurd hc' (by omega)) | (intro hc'; exact absurd hc' (by decide)) | intro _ | skip
  bc_run hlive hS [h8, h9, h13, h23, hb, hcn, hb1, hadd, hsub] at 0x800008ac
  have hown : OwnedBytes S (pay + i + 1) (N - (i + 1)) :=
    ⟨fun k hk => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega),
      by rw [htx]; omega, by omega⟩
  refine memchr_spec hlive hown _ (by bsimp []) (by bsimp []) (by bsimp [])
    fun R1 k1 e10 => ?_
  bsimp []
  have hv : ∀ k, k < (s.drop (i + 1)).length →
      imgM M (pay + i + 1 + k) = BitVec.ofNat 8 ((s.drop (i + 1)).getD k 0) := fun k hk => by
    rw [hdl] at hk
    rw [show pay + i + 1 + k = pay + (i + 1 + k) by omega, himg _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hbd : ∀ x ∈ s.drop (i + 1), x < 256 := fun x hx => hbyte x (List.mem_of_mem_drop hx)
  have hf := skipEol_find (imgM M) (s.drop (i + 1)) (pay + i + 1) hv hbd
  rw [hdl] at hf
  have hw35 : skipWs (35 :: s.drop (i + 1)) = skipWs (skipEol (s.drop (i + 1))) := by
    rw [skipWs_cons]; rfl
  have e10' : R1 10 = ptrOr0 (findFrom (imgM M) 10#8 (pay + i + 1) (N - (i + 1))) := by
    rw [e10]; bsimp []; rfl
  have e9 : R1 9 = BitVec.ofNat 64 (pay + N) := by rw [k1.get 9 (by decide)]; bsimp [h9]
  cases hfd : findFrom (imgM M) 10#8 (pay + i + 1) (N - (i + 1)) with
  | none =>
    rw [hfd] at e10'
    have e0 : R1 10 = 0#64 := e10'
    bc_run hlive hS [e0, e9] at 0x80001758
    exact hnext N (by omega) (Nat.le_refl _)
      (by rw [hw35, hf.2 hfd, List.drop_eq_nil_of_le (by omega)]) _
      (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (by bsimp []) (by bsimp [e9, h9]) (by bsimp [h13]) (by bsimp [k1.get 23 (by decide)])
  | some p =>
    rw [hfd] at e10'
    have ep : R1 10 = BitVec.ofNat 64 p := e10'
    have hpa := findFrom_bounds hfd
    have hm := hf.1 p hfd
    have hnz : BitVec.ofNat 64 p ≠ 0#64 := by
      intro h; have := congrArg BitVec.toNat h; simp at this; omega
    have hp1 : BitVec.ofNat 64 p + 1#64 = BitVec.ofNat 64 (pay + (p + 1 - pay)) := by
      rw [show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]; congr 1; omega
    have e := skipEol_drop (s.drop (i + 1))
    have hle : (skipEol (s.drop (i + 1))).length ≤ N - (i + 1) := by
      rw [← hdl]; exact skipEol_length_le _
    rw [hdl] at e
    generalize hk : N - (i + 1) - (skipEol (s.drop (i + 1))).length = k at e hm
    have hws' : skipWs (35 :: s.drop (i + 1)) = skipWs (s.drop (p + 1 - pay)) := by
      rw [hw35, e, List.drop_drop]; congr 2; omega
    bc_run hlive hS [ep, e9, hp1] at 0x80001798
    all_goals first | (intro hc'; exact absurd hc' hnz) | intro _ | skip
    by_cases hpn : p + 1 - pay < N
    · bc_run hlive hS [ep, e9, hp1] at 0x8000175c
      all_goals first | (intro hc'; exact absurd hc' (by omega)) | intro _ | skip
      exact hgo (p + 1 - pay) (by omega) hpn hws' _ (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) (by bsimp [])
        (by bsimp [e9, h9]) (by bsimp [h13]) (by bsimp [k1.get 23 (by decide)])
    · bc_run hlive hS [ep, e9, hp1] at 0x8000179c
      all_goals first | (intro hc'; exact absurd hc' (by omega)) | intro _ | skip
      exact hfin (by rw [hws', List.drop_eq_nil_of_le (by omega)]; rfl) _ (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
        (by bsimp []; congr 1; omega)

/-- **The whitespace and comment skip** of `DC_EVALTOS` from `0x8000175c`
(`s0` at byte `i` of the text `s` at `pay`, `s1` its end): the end of the
text (`0x8000179c`) when `skipWs` leaves nothing, else the first other
byte (`0x800017d8`). -/
theorem skip_loop (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {pay N : Nat} {s : List Nat}
    (hsN : s.length = N) (hlo : heapStart ≤ pay) (hhi : pay + N ≤ heapEnd)
    (hlbu : ∀ k, k < N → ldv .lbu M (pay + k) = BitVec.ofNat 64 (s.getD k 0))
    (himg : ∀ k, k < N → imgM M (pay + k) = BitVec.ofNat 8 (s.getD k 0))
    (hbyte : ∀ c ∈ s, c < 256) :
    ∀ m i (R : Nat → BitVec 64), N - i ≤ m → i < N →
      R 8 = BitVec.ofNat 64 (pay + i) → R 9 = BitVec.ofNat 64 (pay + N) →
      R 13 = BitVec.ofNat 64 35 → R 23 = 0x900000600#64 →
      (∀ R2, Keeps skipClob R2 R → skipWs (s.drop i) = [] → R2 8 = BitVec.ofNat 64 (pay + N) →
        DWO live S Q t 0x8000179c#64 R2 M) →
      (∀ R2, Keeps skipClob R2 R → skipWs (s.drop i) ≠ [] →
        R2 8 = BitVec.ofNat 64 (pay + N - (skipWs (s.drop i)).length) →
        DWO live S Q t 0x800017d8#64 R2 M) →
      DWO live S Q t 0x8000175c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapStart, heapEnd] at hlo hhi
  intro m
  induction m with
  | zero => intro i R hm hi; omega
  | succ m ih =>
  intro i R hm hi h8 h9 h13 h23 hend hch
  have hb := hlbu i hi
  have hdi := drop_getD (l := s) (j := i) (by omega)
  have hc : s.getD i 0 < 256 := hbyte _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _)
  have hcn : (BitVec.ofNat 64 (s.getD i 0)).toNat = s.getD i 0 := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [hdi] at hend hch
  generalize s.getD i 0 = c at hb hc hcn hend hch
  have hdl : (s.drop (i + 1)).length = N - (i + 1) := by rw [List.length_drop, hsN]
  -- on at a later position `i'`, at `0x8000175c` or `0x80001758`
  have hgo : ∀ i', i < i' → i' < N → skipWs (c :: s.drop (i + 1)) = skipWs (s.drop i') →
      ∀ R2, Keeps skipClob R2 R → R2 8 = BitVec.ofNat 64 (pay + i') → R2 9 = R 9 → R2 13 = R 13 →
      R2 23 = R 23 → DWO live S Q t 0x8000175c#64 R2 M := fun i' hi' hi1 hw R2 k2 e8 e9 e13 e23 =>
    ih i' R2 (by omega) hi1 e8 (by rw [e9, h9]) (by rw [e13, h13]) (by rw [e23, h23])
      (fun R3 k3 hw3 f8 => hend R3 (k3.trans k2) (by rw [hw]; exact hw3) f8)
      (fun R3 k3 hw3 f8 => hch R3 (k3.trans k2) (by rw [hw]; exact hw3) (by rw [hw]; exact f8))
  have hfin : skipWs (c :: s.drop (i + 1)) = [] → ∀ R2, Keeps skipClob R2 R →
      R2 8 = BitVec.ofNat 64 (pay + N) → DWO live S Q t 0x8000179c#64 R2 M := fun hw R2 k2 e8 =>
    hend R2 k2 hw e8
  have hnext : ∀ i', i < i' → i' ≤ N → skipWs (c :: s.drop (i + 1)) = skipWs (s.drop i') →
      ∀ R2, Keeps skipClob R2 R → R2 8 = BitVec.ofNat 64 (pay + i') → R2 9 = R 9 → R2 13 = R 13 →
      R2 23 = R 23 → DWO live S Q t 0x80001758#64 R2 M := fun i' hi' hi1 hw R2 k2 e8 e9 e13 e23 => by
    by_cases hi2 : i' < N
    · bc_run hlive hS [e8, e9, h9] at 0x8000175c
      all_goals first | (intro hc'; exact absurd hc' (by omega)) | intro _ | skip
      exact hgo i' hi' hi2 hw _ (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
        (by bsimp []; exact e8) (by bsimp []; exact e9) (by bsimp []; exact e13) (by bsimp []; exact e23)
    · have hnil : s.drop i' = [] := List.drop_eq_nil_of_le (by omega)
      bc_run hlive hS [e8, e9, h9] at 0x8000179c
      all_goals first | (intro hc'; exact absurd hc' (by omega)) | intro _ | skip
      exact hfin (by rw [hw, hnil]; rfl) _ (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
        (by bsimp []; rw [e8]; congr 1; omega)
  -- a byte that ends the skip
  have hstop : skipWs (c :: s.drop (i + 1)) = c :: s.drop (i + 1) → ∀ R2, Keeps skipClob R2 R →
      R2 8 = R 8 → DWO live S Q t 0x800017d8#64 R2 M := fun hw R2 k2 e8 =>
    hch R2 k2 (by rw [hw]; simp) (by rw [e8, h8, hw, List.length_cons, hdl]; congr 1; omega)
  by_cases hbig : 35 < c
  · bc_run hlive hS [h8, h9, h13, h23, hb, hcn] at 0x800017d8
    all_goals first | (intro hc'; exact absurd hc' (by omega)) | intro _ | skip
    exact hstop (by rw [skipWs_cons]; simp only [show (c == 32 || c == 9 || c == 10) = false by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega,
      show (c == 35) = false by simp only [beq_eq_false_iff_ne]; omega]; rfl)
      _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
  have hbit := wsBit_all c (by omega)
  by_cases hws : c = 9 ∨ c = 10 ∨ c = 32 ∨ c = 35
  · have hb1 := mt hbit.1 (fun h => h hws)
    by_cases h35 : c = 35
    · subst h35
      exact skip_hash hlive hS hsN hi hlo hhi himg hbyte hb h8 h9 h13 h23 hgo hnext hfin
    · have h35' : BitVec.ofNat 64 c ≠ 35#64 := fun e => h35 (by
        have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega)
      bc_run hlive hS [h8, h9, h13, h23, hb, hcn, hb1, h35'] at 0x80001758
      all_goals first | (intro hc'; exact absurd hc' (by omega)) | intro _ | skip
      bc_run hlive hS [h8, h9, h13, h23, hb, hcn, hb1, h35'] at 0x80001758
      all_goals first | (intro hc'; exact absurd h35' hc') | intro _ | skip
      bc_run hlive hS [h8, h9, h13, h23, hb, hcn, hb1, h35'] at 0x80001758
      all_goals first | (intro hc'; exact absurd h35' hc') | intro _ | skip
      refine hnext (i + 1) (by omega) (by omega) (by rw [skipWs_cons]; simp only [show (c == 32 || c == 9 || c == 10) = true by
          simp only [Bool.or_eq_true, beq_iff_eq]; omega, ite_true]) _
        (by keeps_tac Keeps.refl _ _) (by bsimp []; rfl) (by bsimp []) (by bsimp []) (by bsimp [])
  · have hb0 := hbit.2 hws
    bc_run hlive hS [h8, h9, h13, h23, hb, hcn, hb0] at 0x800017d8
    all_goals first | (intro hc'; exact absurd hc' (by omega)) | intro _ | skip
    bc_run hlive hS [h8, h9, h13, h23, hb, hcn, hb0] at 0x800017d8
    all_goals first | (intro hc'; exact absurd hc' (by omega)) | intro _ | skip
    exact hstop (by rw [skipWs_cons]; simp only [show (c == 32 || c == 9 || c == 10) = false by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega,
      show (c == 35) = false by simp only [beq_eq_false_iff_ne]; omega]; rfl)
      _ (by keeps_tac Keeps.refl _ _) (by bsimp [])

/-- **`DC_EVALTOS`'s skip from its start** `0x80001748` (`s7` the
whitespace mask, `a3 = '#'`), at byte `i ≤ N`. -/
theorem tos_skip (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {pay N i : Nat} {s : List Nat}
    (hsN : s.length = N) (hi : i ≤ N) (hlo : heapStart ≤ pay) (hhi : pay + N ≤ heapEnd)
    (hlbu : ∀ k, k < N → ldv .lbu M (pay + k) = BitVec.ofNat 64 (s.getD k 0))
    (himg : ∀ k, k < N → imgM M (pay + k) = BitVec.ofNat 8 (s.getD k 0))
    (hbyte : ∀ c ∈ s, c < 256) {R : Nat → BitVec 64}
    (h8 : R 8 = BitVec.ofNat 64 (pay + i)) (h9 : R 9 = BitVec.ofNat 64 (pay + N))
    (hend : ∀ R2, Keeps (23 :: skipClob) R2 R → skipWs (s.drop i) = [] →
      R2 8 = BitVec.ofNat 64 (pay + N) → DWO live S Q t 0x8000179c#64 R2 M)
    (hch : ∀ R2, Keeps (23 :: skipClob) R2 R → skipWs (s.drop i) ≠ [] →
      R2 8 = BitVec.ofNat 64 (pay + N - (skipWs (s.drop i)).length) →
      DWO live S Q t 0x800017d8#64 R2 M) :
    DWO live S Q t 0x80001748#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hlo' := hlo; have hhi' := hhi
  simp only [heapStart, heapEnd] at hlo' hhi'
  bc_run hlive hS [h8, h9] at 0x80001758
  by_cases hiN : i < N
  · bc_run hlive hS [h8, h9] at 0x8000175c
    all_goals first | (intro hc'; exact absurd hc' (by omega)) | intro _ | skip
    refine skip_loop hlive hS hsN hlo hhi hlbu himg hbyte (N - i) i _ (Nat.le_refl _) hiN
      (by bsimp []; exact h8) (by bsimp []; exact h9) (by bsimp []) (by bsimp [])
      (fun R2 k2 hw e8 => hend R2 (by keeps_tac ((k2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _))) hw e8)
      (fun R2 k2 hw e8 => hch R2 (by keeps_tac ((k2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _))) hw e8)
  · have hnil : s.drop i = [] := List.drop_eq_nil_of_le (by omega)
    bc_run hlive hS [h8, h9] at 0x8000179c
    all_goals first | (intro hc'; exact absurd hc' (by omega)) | intro _ | skip
    exact hend _ (by keeps_tac Keeps.refl _ _) (by rw [hnil]; rfl)
      (by bsimp []; rw [h8]; congr 1; omega)

end

end Dc.Mach
