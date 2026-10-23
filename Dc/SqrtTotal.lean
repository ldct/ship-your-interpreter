import Dc.Semantics

/-!
# `bc_sqrt`'s Newton loop terminates

`sqrtLoop_total`: for every `x > 0` and result scale, the relation
`SqrtLoop` (`Dc/Semantics.lean`) has a result. At a fixed working scale
`cs` the guess is the integer `G` (the guess times `10^cs`) and a step is
integer Newton for `N = ⌊x · 10^(2 cs)⌋` (`newton_ge`, `newton_lt`,
`newton_at`); a step that does not settle moves `G` strictly towards
`⌊√N⌋`, and a settled step at a scale below the target raises the scale.
-/

set_option linter.unusedSimpArgs false

namespace Dc

/-! ## Integer Newton -/

theorem amgm (r G : Nat) : 2 * (r * G) ≤ r * r + G * G := by
  rcases Nat.le_total r G with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.add_mul, Nat.mul_add]; rw [Nat.mul_comm d r]; omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.add_mul, Nat.mul_add]; rw [Nat.mul_comm d G]; omega

/-- An integer square root. -/
theorem exists_isqrt : ∀ N : Nat, ∃ r, r * r ≤ N ∧ N < (r + 1) * (r + 1)
  | 0 => ⟨0, by simp⟩
  | N + 1 => by
    obtain ⟨r, h1, h2⟩ := exists_isqrt N
    by_cases h : (r + 1) * (r + 1) ≤ N + 1
    · refine ⟨r + 1, h, ?_⟩
      have : (r + 1 + 1) * (r + 1 + 1) = (r + 1) * (r + 1) + 2 * r + 3 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
      omega
    · exact ⟨r, by omega, by omega⟩

variable {N r : Nat}

/-- A Newton step from any positive guess lands at or above `⌊√N⌋`. -/
theorem newton_ge (h1 : r * r ≤ N) {G : Nat} (hG : 0 < G) : r ≤ (N / G + G) / 2 := by
  suffices 2 * r ≤ N / G + G by omega
  have hq := Nat.lt_mul_div_succ N hG
  generalize N / G = q at hq ⊢
  apply Classical.byContradiction
  intro hc
  have hc' : q + 1 ≤ 2 * r - G := by omega
  have e1 : G * (q + 1) ≤ G * (2 * r - G) := Nat.mul_le_mul_left _ hc'
  have e2 : G * (2 * r - G) + G * G = 2 * (r * G) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (by omega), Nat.mul_comm G, Nat.mul_assoc]
  have := amgm r G
  omega

/-- Above `⌊√N⌋` a step strictly decreases the guess. -/
theorem newton_lt (h2 : N < (r + 1) * (r + 1)) {G : Nat} (hG : r + 1 ≤ G) : (N / G + G) / 2 < G := by
  have : (r + 1) * (r + 1) ≤ G * G := Nat.mul_le_mul hG hG
  have : N / G < G := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  omega

/-- At `⌊√N⌋` a step moves by at most one. -/
theorem newton_at (h2 : N < (r + 1) * (r + 1)) :
    (N / r + r) / 2 ≤ r + 1 := by
  have e : (r + 1) * (r + 1) = r * (r + 2) + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
  have : N / r ≤ r + 2 := Nat.div_le_of_le_mul (by omega)
  omega

/-! ## The step at a fixed scale -/

namespace Num

/-- The integer `⌊x · 10^(2 cs)⌋` Newton approximates the root of. -/
def sqN (x : Num) (cs : Nat) : Nat := x.mag * 10 ^ (2 * cs) / 10 ^ x.scale

/-- A guess as an integer at scale `cs`. -/
def sqG (g : Num) (cs : Nat) : Nat := g.mag * 10 ^ (cs - g.scale)

variable {x g : Num} {cs : Nat}

theorem div_sqG (hgs : g.scale ≤ cs) (hgm : 0 < g.mag) :
    x.mag * 10 ^ (g.scale + cs) / (g.mag * 10 ^ x.scale) = sqN x cs / sqG g cs := by
  unfold sqN sqG
  rw [Nat.div_div_eq_div_mul]
  have e1 : x.mag * 10 ^ (2 * cs) = x.mag * 10 ^ (g.scale + cs) * 10 ^ (cs - g.scale) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  have e2 : 10 ^ x.scale * (g.mag * 10 ^ (cs - g.scale)) = g.mag * 10 ^ x.scale * 10 ^ (cs - g.scale) := by
    rw [Nat.mul_comm (10 ^ x.scale), Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (10 ^ (cs - g.scale))]
  rw [e1, e2, Nat.mul_div_mul_right _ _ (Nat.pow_pos (by decide : 0 < 10))]

/-- **One step** from a positive guess at scale at most `cs`: integer Newton. -/
theorem sqrtStep_fst (hx : x.neg = false) (hg : g.neg = false) (hgm : 0 < g.mag)
    (hgs : g.scale ≤ cs) (hcs : 1 ≤ cs) :
    (sqrtStep x g cs).1 = ⟨false, (sqN x cs / sqG g cs + sqG g cs) / 2, cs⟩ := by
  have hne : (g.mag == 0) = false := by simp; omega
  have e1 : max 0 (max cs g.scale) = cs := by omega
  simp only [sqrtStep, div, hne, Bool.false_eq_true, ite_false, Option.getD_some, add, mul, half,
    hx, hg, bne_self_eq_false, ite_self, beq_self_eq_true, ite_true, e1, align, Nat.sub_self,
    Nat.pow_zero, Nat.mul_one, Nat.max_self]
  rw [div_sqG hgs hgm]
  have e3 : min (cs + 1) (max cs (max cs 1)) = cs := by omega
  simp only [e3, Nat.max_self, show ¬ (cs + 1 ≤ cs) by omega, ite_false, show cs + 1 - cs = 1 by omega,
    Nat.pow_one, sqG]
  congr 1
  generalize x.sqN cs / (g.mag * 10 ^ (cs - g.scale)) + g.mag * 10 ^ (cs - g.scale) = A
  omega

/-- **The settling test** of a step: the guess moved by at most one unit. -/
theorem sqrtStep_near (hx : x.neg = false) (hg : g.neg = false) (hgm : 0 < g.mag)
    (hgs : g.scale ≤ cs) (hcs : 1 ≤ cs) :
    (sqrtStep x g cs).2.isNearZero cs = true ↔
      ((sqN x cs / sqG g cs + sqG g cs) / 2 ≤ sqG g cs + 1 ∧
        sqG g cs ≤ (sqN x cs / sqG g cs + sqG g cs) / 2 + 1) := by
  have e : (sqrtStep x g cs).2 = sub (sqrtStep x g cs).1 g (cs + 1) := rfl
  rw [e, sqrtStep_fst hx hg hgm hgs hcs]
  generalize (sqN x cs / sqG g cs + sqG g cs) / 2 = G'
  have eB : g.align (cs + 1) = sqG g cs * 10 := by
    unfold align sqG; rw [show cs + 1 - g.scale = (cs - g.scale) + 1 by omega, Nat.pow_succ, Nat.mul_assoc]
  have e1 : max (cs + 1) (max cs g.scale) = cs + 1 := by omega
  have eA : (⟨false, G', cs⟩ : Num).align (cs + 1) = G' * 10 := by
    simp only [align, show cs + 1 - cs = 1 by omega, Nat.pow_one]
  simp only [sub, hg, e1, bne_self_eq_false, Bool.false_eq_true, ite_false]
  rw [eA, eB]
  generalize sqG g cs = G
  split <;> rename_i h <;> simp only [isNearZero, zero, decide_eq_true_eq] <;>
    simp only [Nat.compare_eq_lt, Nat.compare_eq_eq, Nat.compare_eq_gt] at h <;>
    simp only [Nat.min_def, show cs ≤ cs + 1 by omega, ite_true, show cs + 1 - cs = 1 by omega,
      Nat.pow_one] <;> omega

end Num

/-! ## The loop -/

open Num in
/-- **`bc_sqrt`'s loop terminates** from a positive guess at a positive
working scale. -/
theorem sqrtLoop_total {x : Num} (hx : x.neg = false) (rs : Nat) :
    ∀ D cs (g : Num), rs + 1 - cs = D → 1 ≤ cs → g.neg = false → 0 < g.mag → g.scale ≤ cs →
      10 ^ x.scale ≤ x.mag * 10 ^ (2 * cs) → ∃ r, SqrtLoop x rs g cs r := by
  intro D
  induction D using Nat.strongRecOn with
  | _ D ihD =>
  intro cs g hD hcs hg hgm hgs hxN
  have hN : 1 ≤ sqN x cs := (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mpr (by omega)
  obtain ⟨r, h1, h2⟩ := exists_isqrt (sqN x cs)
  have hr : 1 ≤ r := by
    apply Classical.byContradiction; intro h0
    have : r = 0 := by omega
    subst this; simp at h2; omega
  have hrN : r ≤ sqN x cs := Nat.le_trans (Nat.le_mul_self r) h1
  let μ : Nat → Nat := fun G => if r ≤ G then G - r else sqN x cs + 1
  suffices H : ∀ M (g : Num), μ (sqG g cs) ≤ M → g.neg = false → 0 < g.mag → g.scale ≤ cs →
      ∃ r', SqrtLoop x rs g cs r' from H _ g (Nat.le_refl _) hg hgm hgs
  intro M
  induction M using Nat.strongRecOn with
  | _ M ihM =>
  intro g hμ hg hgm hgs
  have hG : 0 < sqG g cs := Nat.mul_pos hgm (Nat.pow_pos (by decide))
  have hge := newton_ge h1 hG
  have hst := sqrtStep_fst hx hg hgm hgs hcs
  have hnz := sqrtStep_near hx hg hgm hgs hcs (x := x)
  generalize hGd : sqG g cs = G at hG hge hst hnz hμ
  generalize hG'd : (sqN x cs / G + G) / 2 = G' at hge hst hnz
  cases hz : (sqrtStep x g cs).2.isNearZero cs
  · -- not settled: iterate
    have hn : ¬ (G' ≤ G + 1 ∧ G ≤ G' + 1) := fun h => by rw [hnz.mpr h] at hz; cases hz
    have hlt : μ G' < μ G := by
      simp only [μ]
      rcases Nat.lt_trichotomy G r with hl | he | hgt
      · have : G' ≤ sqN x cs := by
          rw [← hG'd]
          have := Nat.div_le_self (sqN x cs) G
          omega
        simp only [show ¬ r ≤ G by omega, hge, ite_true, ite_false]; omega
      · have hna := newton_at h2
        rw [← he, hG'd] at hna
        exact absurd ⟨hna, by omega⟩ hn
      · have := newton_lt h2 (G := G) (by omega); rw [hG'd] at this
        simp only [show r ≤ G by omega, hge, ite_true]; omega
    obtain ⟨r', hr'⟩ := ihM (μ G') (Nat.lt_of_lt_of_le hlt hμ) ⟨false, G', cs⟩
      (by simp only [sqG, Nat.sub_self, Nat.pow_zero, Nat.mul_one]; exact Nat.le_refl _)
      rfl (show 0 < G' by omega) (Nat.le_refl _)
    exact ⟨r', SqrtLoop.iterate hz (by rw [hst]; exact hr')⟩
  · by_cases hc : cs < rs + 1
    · -- settled below the target scale: refine
      have hcs' : cs < min (cs * 3) (rs + 1) := by omega
      have hxN' : 10 ^ x.scale ≤ x.mag * 10 ^ (2 * min (cs * 3) (rs + 1)) :=
        Nat.le_trans hxN (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
      obtain ⟨r', hr'⟩ := ihD (rs + 1 - min (cs * 3) (rs + 1)) (by omega) _ ⟨false, G', cs⟩ rfl
        (by omega) rfl (show 0 < G' by omega) (show cs ≤ min (cs * 3) (rs + 1) by omega) hxN'
      exact ⟨r', SqrtLoop.refine hz hc (by rw [hst]; exact hr')⟩
    · exact ⟨_, SqrtLoop.finish hz hc⟩

namespace Num

/-- `bc_sqrt`'s first guess for `x ≥ 1`: a positive integer. -/
theorem raise10_pos (n : Nat) :
    (raise ⟨false, 10, 0⟩ ⟨false, n, 0⟩ 0).1.neg = false ∧
      0 < (raise ⟨false, 10, 0⟩ ⟨false, n, 0⟩ 0).1.mag ∧
      (raise ⟨false, 10, 0⟩ ⟨false, n, 0⟩ 0).1.scale = 0 := by
  unfold raise
  generalize he : toLong ⟨false, n, 0⟩ = e
  have hen : 0 ≤ e := by
    rw [← he]; unfold toLong; simp only [Bool.false_eq_true, ite_false]; split <;> omega
  by_cases h0 : e = 0
  · subst h0; simp [one]
  · have h0' : (e == 0) = false := by simp [h0]
    have hlt : ¬ e < 0 := by omega
    simp only [h0', Bool.false_eq_true, ite_false, hlt, decide_false]
    unfold powRaise powExact
    split
    · simp
    · simp only [Nat.zero_mul, Nat.min_self, Nat.max_self, Nat.sub_zero, Nat.pow_zero, Nat.div_one]
      refine ⟨?_, Nat.pow_pos (by decide), by simp⟩
      split <;> simp

end Num

/-- **`bc_sqrt` has a result** for every `x > 0`. -/
theorem sqrt_total {x : Num} (hx : x.neg = false) (hm : 0 < x.mag) (k : Nat) : ∃ r, Sqrt x k r := by
  unfold Sqrt Num.sqrtInit
  have hc : Num.cmp x Num.one = compare x.mag (10 ^ x.scale) := by
    simp [Num.cmp, Num.one, hx, Num.cmpMag, Num.align]
  split
  · rename_i h
    rw [hc] at h
    have hl : x.mag < 10 ^ x.scale := by simpa [Nat.compare_eq_lt] using h
    have hs : 1 ≤ x.scale := by
      apply Classical.byContradiction; intro h0
      have : x.scale = 0 := by omega
      rw [this] at hl; simp at hl; omega
    refine sqrtLoop_total hx _ _ x.scale Num.one rfl hs rfl (by decide) (by simp [Num.one]) ?_
    have := Nat.pow_le_pow_right (show 0 < 10 by decide) (show x.scale ≤ 2 * x.scale by omega)
    exact Nat.le_trans this (Nat.le_mul_of_pos_left _ hm)
  · rename_i h
    rw [hc] at h
    have hl : 10 ^ x.scale ≤ x.mag := by
      simp [Nat.compare_eq_lt] at h; omega
    obtain ⟨p1, p2, p3⟩ := Num.raise10_pos (x.intLen / 2)
    refine sqrtLoop_total hx _ _ 3 _ rfl (by decide) p1 p2 (by dsimp only; rw [p3]; omega) ?_
    exact Nat.le_trans hl (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide)))

end Dc
