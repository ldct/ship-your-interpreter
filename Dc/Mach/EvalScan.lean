import Dc.Mach.EvalCases7

/-!
# `evalstr`'s `DC_STR` scan (M10)

The loop at `0x80001618` (`a1` the byte, `a3` the bracket depth) finds the
`]` closing the string (`scanStr`): `scan_body` one byte, `scan_loop` the
whole scan to `0x80001640` with `a1` the contents' length and `a5` the
position after the scan.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)


theorem sltu0 (x : BitVec 64) : zopz0zI_u 0#64 x = decide (x.toNat ≠ 0) := by
  unfold zopz0zI_u
  simp [BitVec.toNatInt]
  rcases Nat.eq_zero_or_pos x.toNat with h | h <;> simp [h, Nat.ne_of_gt]

/-- The depth after a byte. -/
def scanDepth (b dd : Nat) : Nat := if b = 93 then dd - 1 else if b = 91 then dd + 1 else dd

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t : String} {M : Mem}

/-- **One byte of the scan** at `0x80001618` (`a1 = a + j`, `a3 = dd`, the
end `s1 = a + n`, `s0 = a - 1`): the next byte, or the end of the scan. -/
theorem scan_body (hlive : ∀ p ∈ dcText, live p.1) {R : Nat → BitVec 64} {a n j dd b : Nat}
    (hS : HeapOwn S) (hlo : heapStart ≤ a) (hhi : a + n ≤ heapEnd)
    (hj : j < n) (hn : a + n < 2 ^ 60) (h1a : 1 ≤ a) (hdd : 1 ≤ dd) (hdd2 : dd + 1 < 2 ^ 31)
    (hb : ldv .lbu M (a + j) = BitVec.ofNat 64 b) (hb256 : b < 256)
    (h8 : R 8 = BitVec.ofNat 64 (a - 1)) (h9 : R 9 = BitVec.ofNat 64 (a + n))
    (h10 : R 10 = BitVec.ofNat 64 91) (h11 : R 11 = BitVec.ofNat 64 (a + j))
    (h12 : R 12 = BitVec.ofNat 64 93) (h13 : R 13 = BitVec.ofNat 64 dd)
    (hnext : j + 1 < n → ¬ (b = 93 ∧ dd = 1) → ∀ R2, Keeps [11, 13, 14, 15] R2 R →
      R2 11 = BitVec.ofNat 64 (a + (j + 1)) → R2 13 = BitVec.ofNat 64 (scanDepth b dd) →
      DWO live S Q t 0x80001618#64 R2 M)
    (hexit : ∀ R2, Keeps [11, 13, 14, 15] R2 R →
      (b = 93 ∧ dd = 1 → R2 11 = BitVec.ofNat 64 j ∧ R2 15 = BitVec.ofNat 64 (a + j + 1)) →
      (¬ (b = 93 ∧ dd = 1) →
        j + 1 = n ∧ R2 11 = BitVec.ofNat 64 (j + 1) ∧ R2 15 = BitVec.ofNat 64 (a + n)) →
      DWO live S Q t 0x80001640#64 R2 M) :
    DWO live S Q t 0x80001618#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hne : ∀ x y : Nat, x < 2 ^ 64 → y < 2 ^ 64 → x ≠ y → BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y :=
    fun x y hx hy hxy e => hxy (by
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this)
  have hsub : ∀ x : Nat, a - 1 ≤ x → x < 2 ^ 60 →
      BitVec.ofNat 64 x - BitVec.ofNat 64 (a - 1) = BitVec.ofNat 64 (x - (a - 1)) := fun x h1 h2 => by
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  have hadd1 : BitVec.ofNat 64 (a + j) + 1#64 = BitVec.ofNat 64 (a + (j + 1)) := by
    rw [show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]; congr 1
  have hd0 : dd ≠ 0 := by omega
  by_cases h93 : b = 93
  · subst h93
    by_cases hd1 : dd = 1
    · subst hd1
      simp only [heapStart, heapEnd] at hlo hhi
      bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1] at 0x80001640
      bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1] at 0x80001640
      all_goals intro _
      all_goals bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1] at 0x80001640
      all_goals refine hexit _ (by keeps_tac Keeps.refl _ _) (fun _ => ⟨?_, ?_⟩) (fun h => (h (by decide)).elim)
      all_goals bsimp [hsub (a + j) (by omega) (by omega)]
      all_goals first
        | (rw [show zero_extend (bool_to_bit (zopz0zI_u 0#64 1#64)) = (1#64 : BitVec 64) by decide]
           apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega)
        | (congr 1 <;> omega)
    · simp only [heapStart, heapEnd] at hlo hhi
      have hd' : dd - 1 ≠ 0 := by omega
      bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb, hd'] at 0x80001614 0x80001640
      bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb, hd'] at 0x80001614 0x80001640
      all_goals intro _
      all_goals bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb, hd'] at 0x80001614 0x80001640
      all_goals first | (intro hc; exfalso; revert hc; simp [hd']; done) | intro _ | skip
      · bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb, hd'] at 0x80001618
        exact hnext (by omega) (fun h => hd1 h.2) _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
          (by bsimp []; simp only [scanDepth, ite_true])
      · refine hexit _ (by keeps_tac Keeps.refl _ _) (fun h => absurd h.2 hd1) (fun _ => ⟨by omega, ?_, ?_⟩)
        all_goals bsimp [hsub (a + j) (by omega) (by omega)]
        all_goals first
          | (congr 1 <;> omega)
          | (simp only [decide_false, decide_true, Bool.toNat_false, Bool.toNat_true]
             apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega)
  · simp only [heapStart, heapEnd] at hlo hhi
    have h93' : BitVec.ofNat 64 b ≠ 93#64 := hne b 93 (by omega) (by omega) h93
    by_cases h91 : b = 91
    · subst h91
      bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb] at 0x80001614 0x80001640
      all_goals first | (intro hc; exfalso; revert hc; simp; done) | intro _ | skip
      bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb] at 0x80001614 0x80001640
      all_goals first | (intro hc; exfalso; revert hc; simp; done) | intro _ | skip
      bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb] at 0x80001614 0x80001640
      all_goals first | (intro hc; exfalso; revert hc; simp; done) | intro _ | skip
      all_goals bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb] at 0x80001614 0x80001640
      all_goals first | (intro hc; exfalso; revert hc; simp; done) | intro _ | skip
      · refine hexit _ (by keeps_tac Keeps.refl _ _) (fun h => absurd h.1 (by decide))
          (fun _ => ⟨by omega, ?_, ?_⟩)
        all_goals bsimp [hsub (a + j) (by omega) (by omega)]
        all_goals first
          | (congr 1 <;> omega)
          | ((try simp only [decide_false, decide_true, Bool.toNat_false, Bool.toNat_true, ne_eq, hd0, decide_false])
             apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega)
      · bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1] at 0x80001618
        exact hnext (by omega) (fun h => absurd h.1 (by decide)) _ (by keeps_tac Keeps.refl _ _)
          (by bsimp []) (by bsimp []; simp only [scanDepth]; rfl)
    · have h91' : BitVec.ofNat 64 b ≠ 91#64 := hne b 91 (by omega) (by omega) h91
      bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb, h93', h91'] at 0x80001614 0x80001640
      all_goals first | (intro hc; exact (hc h93').elim) | (intro hc; exact (hc h91').elim) | intro _ | skip
      all_goals bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb, h93', h91'] at 0x80001614 0x80001640
      all_goals first | (intro hc; exact (hc h93').elim) | (intro hc; exact (hc h91').elim) | intro _ | skip
      all_goals bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb, h93', h91'] at 0x80001614 0x80001640
      all_goals first | (intro hc; exact (hc h93').elim) | (intro hc; exact (hc h91').elim) | intro _ | skip
      all_goals bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, sltu0, sltiu1, ze_bb, h93', h91'] at 0x80001614 0x80001640
      all_goals first | (intro hc; exact (hc h93').elim) | (intro hc; exact (hc h91').elim) | intro _ | skip
      · refine hexit _ (by keeps_tac Keeps.refl _ _) (fun h => absurd h.1 h93)
          (fun _ => ⟨by omega, ?_, ?_⟩)
        all_goals bsimp [hsub (a + j) (by omega) (by omega)]
        all_goals first
          | (congr 1 <;> omega)
          | ((try simp only [decide_false, decide_true, Bool.toNat_false, Bool.toNat_true, ne_eq, hd0])
             apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega)
      · bc_run hlive hS [h8, h9, h10, h11, h12, h13, hb, hadd1, h93', h91'] at 0x80001618
        exact hnext (by omega) (fun h => absurd h.1 h93) _ (by keeps_tac Keeps.refl _ _)
          (by bsimp []) (by bsimp []; simp only [scanDepth, h93, h91, ite_false]; exact h13)

end

theorem scanStr_close (cs : List Nat) : scanStr 1 (93 :: cs) = ([], cs) := by
  simp [scanStr]

theorem scanStr_cons {dd b : Nat} (cs : List Nat) (h : ¬ (b = 93 ∧ dd = 1)) :
    scanStr dd (b :: cs) = (b :: (scanStr (scanDepth b dd) cs).1, (scanStr (scanDepth b dd) cs).2) := by
  rw [scanStr.eq_2]; unfold scanDepth
  by_cases h93 : b = 93
  · subst h93
    have : dd ≠ 1 := fun e => h ⟨rfl, e⟩
    simp [this]
  · by_cases h91 : b = 91
    · subst h91; simp
    · simp [h93, h91]

theorem drop_getD {l : List Nat} {j : Nat} (hj : j < l.length) :
    l.drop j = l.getD j 0 :: l.drop (j + 1) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.drop_eq_getElem_cons hj

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t : String} {M : Mem}

/-- **The `DC_STR` scan** from `0x80001618` to `0x80001640`: `a1` the
contents' length, `a5` the position after the scan (`scanStr`). -/
theorem scan_loop (hlive : ∀ p ∈ dcText, live p.1) {a n : Nat} {rest : List Nat}
    (hS : HeapOwn S) (hlo : heapStart ≤ a) (hhi : a + n ≤ heapEnd) (hn : a + n < 2 ^ 60)
    (h1a : 1 ≤ a) (hlen : rest.length = n)
    (hval : ∀ i, i < n → ldv .lbu M (a + i) = BitVec.ofNat 64 (rest.getD i 0))
    (hbyte : ∀ x ∈ rest, x < 256) :
    ∀ m j dd (R : Nat → BitVec 64), n - j = m → j < n → 1 ≤ dd → dd + (n - j) < 2 ^ 31 →
      R 8 = BitVec.ofNat 64 (a - 1) → R 9 = BitVec.ofNat 64 (a + n) →
      R 10 = BitVec.ofNat 64 91 → R 11 = BitVec.ofNat 64 (a + j) →
      R 12 = BitVec.ofNat 64 93 → R 13 = BitVec.ofNat 64 dd →
      (∀ R2, Keeps [11, 13, 14, 15] R2 R →
        R2 11 = BitVec.ofNat 64 (j + (scanStr dd (rest.drop j)).1.length) →
        R2 15 = BitVec.ofNat 64 (a + n - (scanStr dd (rest.drop j)).2.length) →
        DWO live S Q t 0x80001640#64 R2 M) →
      DWO live S Q t 0x80001618#64 R M := by
  intro m
  induction m with
  | zero => intro j dd R hm hj; omega
  | succ m ih =>
    intro j dd R hm hj hdd hdd2 h8 h9 h10 h11 h12 h13 hk
    have hjl : j < rest.length := by omega
    have hdj := drop_getD hjl
    have hb256 : rest.getD j 0 < 256 := hbyte _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
      exact List.getElem_mem hjl)
    refine scan_body hlive hS hlo hhi hj hn h1a hdd (by omega) (hval j hj) hb256 h8 h9 h10 h11 h12 h13
      (fun hj1 hnc R2 k2 e11 e13 => ?_) (fun R2 k2 hc hl => ?_)
    · have hsd : 1 ≤ scanDepth (rest.getD j 0) dd ∧ scanDepth (rest.getD j 0) dd + (n - (j + 1)) < 2 ^ 31 := by
        unfold scanDepth; split
        · rename_i h; exact ⟨by have := fun e => hnc ⟨h, e⟩; omega, by omega⟩
        · split <;> omega
      refine ih (j + 1) _ R2 (by omega) hj1 hsd.1 hsd.2 (by rw [k2.get 8 (by decide)]; exact h8)
        (by rw [k2.get 9 (by decide)]; exact h9) (by rw [k2.get 10 (by decide)]; exact h10) e11
        (by rw [k2.get 12 (by decide)]; exact h12) e13 fun R3 k3 f11 f15 => hk R3 (k3.trans k2) ?_ ?_
      · rw [f11, hdj, scanStr_cons _ hnc]; congr 1; simp; omega
      · rw [f15, hdj, scanStr_cons _ hnc]
    · by_cases hcl : rest.getD j 0 = 93 ∧ dd = 1
      · obtain ⟨e11, e15⟩ := hc hcl
        refine hk R2 k2 ?_ ?_
        · rw [e11, hdj, hcl.1, hcl.2, scanStr_close]; simp
        · rw [e15, hdj, hcl.1, hcl.2, scanStr_close, List.length_drop]; congr 1; omega
      · obtain ⟨hjn, e11, e15⟩ := hl hcl
        have hd1 : rest.drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
        refine hk R2 k2 ?_ ?_
        · rw [e11, hdj, scanStr_cons _ hcl, hd1]; simp [scanStr]
        · rw [e15, hdj, scanStr_cons _ hcl, hd1]; simp [scanStr]

end

end Dc.Mach
