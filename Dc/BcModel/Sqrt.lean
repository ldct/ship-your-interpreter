import Dc.Num

/-!
# The Newton loop of `bc_sqrt`

Every guess of `bc_sqrt` is non-negative, has scale at most the current
working scale `cs`, and its magnitude at the scale ceiling `c` stays below
`sqU x c = (x·10^c + 10^c)·10^c` (all at scale `c`): the quotient `x / g` of
a nonzero guess is at most `x·10^c` at scale `c` (a nonzero guess is at least
`10^-c`), and the new guess is half the sum (`SqInv`, `sqInv_step`). A guess
stays nonzero while `x ≥ 10^-2cs` (`SqG`, `sqG_step`), so no division is by
zero. The step's quotient, sum, half and difference stay below `10^E` for
`E = n + 2c + 3`, `x < 10^n` (`SqStepB`, `sqStepB`), which bounds every
digit count the machine sees.
-/

namespace Dc.BcModel

open Dc

/-- The scale ceiling of the Newton loop for `x` at result scale `k`. -/
def sqC (x : Num) (k : Nat) : Nat := max 3 (max k x.scale + 1)

/-- The magnitude bound at scale `c`. -/
def sqU (x : Num) (c : Nat) : Nat := (x.align c + 10 ^ c) * 10 ^ c

/-- A guess of the loop at working scale `cs` under the ceiling `c`. -/
structure SqInv (x : Num) (c : Nat) (g : Num) (cs : Nat) : Prop where
  pos : 1 ≤ cs
  le : cs ≤ c
  neg : g.neg = false
  scale : g.scale ≤ cs
  bound : g.align c ≤ sqU x c

/-- A larger working scale under the ceiling. -/
theorem SqInv.mono {x g : Num} {c cs cs' : Nat} (h : SqInv x c g cs) (h1 : cs ≤ cs')
    (h2 : cs' ≤ c) : SqInv x c g cs' :=
  ⟨by have := h.pos; omega, h2, h.neg, by have := h.scale; omega, h.bound⟩

theorem div_mul_le' (a b c : Nat) : a / b * c ≤ a * c / b := by
  rw [Nat.mul_comm (a / b), Nat.mul_comm a]; exact Nat.mul_div_le_mul_div_assoc c a b

theorem pow_mul_pow_sub {a b : Nat} (h : a ≤ b) : 10 ^ a * 10 ^ (b - a) = 10 ^ b := by
  rw [← Nat.pow_add, Nat.add_sub_cancel' h]

/-- The quotient of a nonzero guess at scale `c`: at most `x·10^c`. -/
theorem quot_align_le (x g : Num) {c cs : Nat} (hg : g.mag ≠ 0) (hgs : g.scale ≤ cs)
    (hcs : cs ≤ c) (hxs : x.scale ≤ c) :
    x.mag * 10 ^ (g.scale + cs) / (g.mag * 10 ^ x.scale) * 10 ^ (c - cs) ≤
      x.align c * 10 ^ c := by
  have h1 : x.mag * 10 ^ (g.scale + cs) / (g.mag * 10 ^ x.scale) ≤
      x.mag * 10 ^ (g.scale + cs) / 10 ^ x.scale :=
    Nat.div_le_div_left (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hg)) (Nat.pow_pos (by decide))
  have h2 : x.mag * 10 ^ (g.scale + cs) / 10 ^ x.scale * 10 ^ (c - cs) ≤
      x.mag * 10 ^ (g.scale + cs) * 10 ^ (c - cs) / 10 ^ x.scale :=
    div_mul_le' _ _ _
  have h3 : x.mag * 10 ^ (g.scale + cs) * 10 ^ (c - cs) = x.mag * 10 ^ (g.scale + c) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  have h4 : x.mag * 10 ^ (g.scale + c) / 10 ^ x.scale ≤ x.align c * 10 ^ c := by
    unfold Num.align
    apply Nat.div_le_of_le_mul
    calc x.mag * 10 ^ (g.scale + c) ≤ x.mag * 10 ^ (c - x.scale + c + x.scale) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
      _ = 10 ^ x.scale * (x.mag * 10 ^ (c - x.scale) * 10 ^ c) := by
          rw [Nat.pow_add, Nat.pow_add]; ac_rfl
  calc _ ≤ x.mag * 10 ^ (g.scale + cs) / 10 ^ x.scale * 10 ^ (c - cs) := Nat.mul_le_mul_right _ h1
    _ ≤ _ := h2
    _ = _ := by rw [h3]
    _ ≤ _ := h4

/-- One Newton step on a nonzero guess: the new guess is half the sum of the
quotient and the guess, at the working scale. -/
theorem sqrtStep_fst_pos (x g : Num) (cs : Nat) (hx : x.neg = false) (hg : g.neg = false)
    (hm : g.mag ≠ 0) (hgs : g.scale ≤ cs) (hcs : 1 ≤ cs) :
    (Num.sqrtStep x g cs).1 =
      ⟨false, (x.mag * 10 ^ (g.scale + cs) / (g.mag * 10 ^ x.scale) +
        g.mag * 10 ^ (cs - g.scale)) * 5 / 10 ^ 1, cs⟩ := by
  simp only [Num.sqrtStep, Num.div, Num.add, Num.mul, Num.align, Num.half, hm, hx, hg,
    beq_iff_eq, if_false, Option.getD_some, Nat.sub_self, Nat.pow_zero, Nat.mul_one,
    Nat.max_eq_right (Nat.zero_le _)]
  have e1 : max cs g.scale = cs := Nat.max_eq_left hgs
  have e2 : min (cs + 1) (max cs (max cs 1)) = cs := by omega
  have e3 : cs + 1 - cs = 1 := by omega
  split <;> simp_all

/-- One Newton step keeps the invariant. -/
theorem sqInv_step {x g : Num} {c cs : Nat} (hx : x.neg = false) (hxs : x.scale ≤ c)
    (h : SqInv x c g cs) : SqInv x c (Num.sqrtStep x g cs).1 cs := by
  have hp := h.pos; have hl := h.le; have hg := h.neg; have hgs := h.scale; have hb := h.bound
  by_cases hm : g.mag = 0
  · have e : (Num.sqrtStep x g cs).1 = ⟨false, 0, min (g.scale + 1) cs⟩ := by
      simp only [Num.sqrtStep, Num.div, Num.add, Num.mul, Num.align, Num.half, hm, hg,
        beq_self_eq_true, if_true, Option.getD_none, Nat.zero_mul, Nat.zero_add, Nat.zero_div,
        Nat.max_self, Nat.max_eq_right (Nat.zero_le _)]
      congr 1; omega
    rw [e]
    exact ⟨hp, hl, rfl, by simp; omega, by simp [Num.align]⟩
  · rw [sqrtStep_fst_pos x g cs hx hg hm hgs hp]
    refine ⟨hp, hl, rfl, Nat.le_refl _, ?_⟩
    have hq := quot_align_le x g hm hgs hl hxs
    have hG : g.mag * 10 ^ (cs - g.scale) * 10 ^ (c - cs) = g.align c := by
      unfold Num.align; rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
    have hU : x.align c * 10 ^ c ≤ sqU x c := by
      unfold sqU; exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    show (_ + _) * 5 / 10 ^ 1 * 10 ^ (c - cs) ≤ sqU x c
    have hb' := hb
    generalize x.mag * 10 ^ (g.scale + cs) / (g.mag * 10 ^ x.scale) = Q at hq ⊢
    generalize g.mag * 10 ^ (cs - g.scale) = B at hG ⊢
    generalize 10 ^ (c - cs) = P at hq hG ⊢
    have e5 : (Q + B) * 5 / 10 ^ 1 = (Q + B) / 2 := by
      rw [show (10 : Nat) ^ 1 = 10 from rfl]; omega
    rw [e5]
    have hd := div_mul_le' (Q + B) 2 P
    rw [Nat.add_mul] at hd
    generalize Q * P = QP at hq hd
    generalize B * P = BP at hG hd
    generalize (Q + B) / 2 * P = L at hd ⊢
    generalize x.align c * 10 ^ c = XC at hq hU
    omega

/-- The refined working scale. -/
theorem sqInv_refine {x g : Num} {k cs : Nat} (h : SqInv x (sqC x k) g cs)
    (hc : cs < max k x.scale + 1) :
    SqInv x (sqC x k) g (min (cs * 3) (max k x.scale + 1)) :=
  h.mono (by have := h.pos; omega) (by unfold sqC; omega)

/-- `10^u` as `bc_raise (10, u, 0)` computes it. -/
theorem raise_ten (u : Nat) (hu : u / 10 ≤ Num.longMax / 10) :
    (Num.raise ⟨false, 10, 0⟩ ⟨false, u, 0⟩ 0).1 = ⟨false, 10 ^ u, 0⟩ := by
  have hl : Num.toLong ⟨false, u, 0⟩ = u := by
    simp only [Num.toLong, Num.intPart, Nat.pow_zero, Nat.div_one, hu, if_true, Bool.false_eq_true,
      if_false]
  rcases Nat.eq_zero_or_pos u with rfl | hp
  · simp [Num.raise, hl, Num.one]
  · have h1 : ¬ ((u : Int) == 0) = true := by simp; omega
    have h2 : ¬ (u : Int) < 0 := by omega
    simp only [Num.raise, hl, h1, h2, if_false, Int.natAbs_natCast, Nat.zero_mul,
      Nat.min_eq_left (Nat.zero_le _), Nat.sub_zero, Nat.pow_zero, Nat.div_one]
    by_cases h1 : u = 1
    · subst h1; simp [Num.powRaise]
    · simp only [Num.powRaise, h1, if_false, Num.powExact, Nat.zero_mul]
      have : 10 ^ u ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
      simp [this]

/-- The first guess above one: `10^u ≤` the integer part. -/
theorem sqInv_initHi {x : Num} {k u : Nat} (hx : 10 ^ (u + x.scale) ≤ x.mag) :
    SqInv x (sqC x k) ⟨false, 10 ^ u, 0⟩ 3 := by
  refine ⟨by decide, by unfold sqC; omega, rfl, Nat.zero_le _, ?_⟩
  unfold sqU Num.align
  simp only [Nat.sub_zero]
  have hxs : x.scale ≤ sqC x k := by unfold sqC; omega
  have : 10 ^ u * 10 ^ sqC x k ≤ x.mag * 10 ^ (sqC x k - x.scale) := by
    calc 10 ^ u * 10 ^ sqC x k = 10 ^ (u + x.scale) * 10 ^ (sqC x k - x.scale) := by
          rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hx
  exact Nat.le_trans this (Nat.le_trans (Nat.le_add_right _ _)
    (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))))

/-- The first guess below one: `1` at the number's scale. -/
theorem sqInv_initLo {x : Num} {k : Nat} (hs : 1 ≤ x.scale) :
    SqInv x (sqC x k) Num.one x.scale := by
  refine ⟨hs, by unfold sqC; omega, rfl, Nat.zero_le _, ?_⟩
  unfold sqU Num.align Num.one
  simp only [Nat.one_mul, Nat.sub_zero]
  exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide)))

/-- The bound in digits: below `10^(n + 2c + 1)` for `x < 10^n`. -/
theorem sqU_lt {x : Num} {c n : Nat} (hx : x.mag < 10 ^ (n + x.scale)) (hxs : x.scale ≤ c) :
    sqU x c < 10 ^ (n + 2 * c + 1) := by
  unfold sqU Num.align
  have h1 : x.mag * 10 ^ (c - x.scale) < 10 ^ (n + c) := by
    calc x.mag * 10 ^ (c - x.scale) < 10 ^ (n + x.scale) * 10 ^ (c - x.scale) :=
          Nat.mul_lt_mul_of_pos_right hx (Nat.pow_pos (by decide))
      _ = 10 ^ (n + c) := by rw [← Nat.pow_add]; congr 1; omega
  have h2 : 10 ^ c ≤ 10 ^ (n + c) := Nat.pow_le_pow_right (by decide) (by omega)
  calc (x.mag * 10 ^ (c - x.scale) + 10 ^ c) * 10 ^ c < 2 * 10 ^ (n + c) * 10 ^ c :=
        Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by decide))
    _ ≤ 10 * 10 ^ (n + c) * 10 ^ c := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
    _ = 10 ^ (n + 2 * c + 1) := by
        rw [show n + 2 * c + 1 = n + c + c + 1 by omega]
        simp only [Nat.pow_succ, Nat.pow_add]; ac_rfl

/-! ## Nonzero guesses and the step's bounds -/

/-- A nonzero guess: `SqInv`, and `x ≥ 10^-2cs`, so the half sum of the
quotient and the smallest guess is nonzero. -/
structure SqG (x : Num) (c : Nat) (g : Num) (cs : Nat) : Prop extends SqInv x c g cs where
  nz : g.mag ≠ 0
  low : 10 ^ x.scale ≤ x.mag * 10 ^ (2 * cs)

theorem SqG.mono {x g : Num} {c cs cs' : Nat} (h : SqG x c g cs) (h1 : cs ≤ cs') (h2 : cs' ≤ c) :
    SqG x c g cs' :=
  { h.toSqInv.mono h1 h2 with
    nz := h.nz
    low := Nat.le_trans h.low (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))) }

/-- One Newton step keeps a guess nonzero. -/
theorem sqG_step {x g : Num} {c cs : Nat} (hx : x.neg = false) (hxs : x.scale ≤ c)
    (h : SqG x c g cs) : SqG x c (Num.sqrtStep x g cs).1 cs := by
  refine { sqInv_step hx hxs h.toSqInv with nz := ?_, low := h.low }
  have hp := h.pos; have hgs := h.scale; have hm := h.nz; have hlow := h.low
  rw [sqrtStep_fst_pos x g cs hx h.neg hm hgs hp]
  show (_ + _) * 5 / 10 ^ 1 ≠ 0
  have hB : 1 ≤ g.mag * 10 ^ (cs - g.scale) :=
    Nat.mul_le_mul (Nat.pos_of_ne_zero hm) (Nat.pow_pos (by decide))
  rcases Nat.lt_or_ge 1 (g.mag * 10 ^ (cs - g.scale)) with h2 | h2
  · rw [show (10 : Nat) ^ 1 = 10 from rfl]
    generalize x.mag * 10 ^ (g.scale + cs) / (g.mag * 10 ^ x.scale) = Q
    generalize g.mag * 10 ^ (cs - g.scale) = B at h2
    omega
  · have hg1 : g.mag = 1 ∧ 10 ^ (cs - g.scale) = 1 := by
      constructor
      · exact Nat.le_antisymm (Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))) h2)
          (Nat.pos_of_ne_zero hm)
      · exact Nat.le_antisymm (Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm)) h2)
          (Nat.pow_pos (by decide))
    have hsc : g.scale = cs := by
      have := (Nat.pow_eq_one.mp hg1.2)
      omega
    have hQ : 1 ≤ x.mag * 10 ^ (g.scale + cs) / (g.mag * 10 ^ x.scale) := by
      rw [hg1.1, Nat.one_mul, hsc, show cs + cs = 2 * cs by omega]
      exact (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mpr (by rw [Nat.one_mul]; exact hlow)
    rw [show (10 : Nat) ^ 1 = 10 from rfl]; omega

/-- The refined working scale keeps a guess nonzero. -/
theorem sqG_refine {x g : Num} {k cs : Nat} (h : SqG x (sqC x k) g cs)
    (hc : cs < max k x.scale + 1) :
    SqG x (sqC x k) g (min (cs * 3) (max k x.scale + 1)) :=
  h.mono (by have := h.pos; omega) (by unfold sqC; omega)

/-- The quotient, the sum, the half and the difference of one step at `cs`,
each of magnitude below `10^E` and scale `cs` (the difference `cs + 1`). -/
structure SqStepB (g q : Num) (cs E : Nat) : Prop where
  qmag : q.mag < 10 ^ E
  qscale : q.scale = cs
  amag : (Num.add q g 0).mag < 10 ^ E
  ascale : (Num.add q g 0).scale = cs
  mmag : (Num.mul (Num.add q g 0) Num.half cs).mag < 10 ^ E
  mscale : (Num.mul (Num.add q g 0) Num.half cs).scale = cs
  dmag : (Num.sub (Num.mul (Num.add q g 0) Num.half cs) g (cs + 1)).mag < 10 ^ E
  dscale : (Num.sub (Num.mul (Num.add q g 0) Num.half cs) g (cs + 1)).scale = cs + 1

/-- A nonzero guess's quotient. -/
theorem sqG_div {x g : Num} {c cs : Nat} (h : SqG x c g cs) :
    Num.div x g cs = some ⟨if x.mag * 10 ^ (g.scale + cs) / (g.mag * 10 ^ x.scale) == 0 then false
      else x.neg != g.neg, x.mag * 10 ^ (g.scale + cs) / (g.mag * 10 ^ x.scale), cs⟩ := by
  simp only [Num.div, h.nz, beq_iff_eq, if_false]

/-- **The step's numbers are bounded** for `x < 10^n`. -/
theorem sqStepB {x g q : Num} {c cs n : Nat} (hx : x.neg = false) (hxs : x.scale ≤ c)
    (hxn : x.mag < 10 ^ (n + x.scale)) (h : SqG x c g cs) (hq : Num.div x g cs = some q) :
    SqStepB g q cs (n + 2 * c + 3) := by
  have hp := h.pos; have hl := h.le; have hgs := h.scale; have hm := h.nz; have hgn := h.neg
  have hb := h.bound
  rw [sqG_div h] at hq
  generalize hQ : x.mag * 10 ^ (g.scale + cs) / (g.mag * 10 ^ x.scale) = Q at hq
  have hq' : q = ⟨false, Q, cs⟩ := by
    have := (Option.some.inj hq).symm; rw [this, hx, hgn]; split <;> rfl
  subst hq'
  have hqa := quot_align_le x g hm hgs hl hxs
  rw [hQ] at hqa
  have hU : x.align c * 10 ^ c ≤ sqU x c := by
    unfold sqU; exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hUl := sqU_lt hxn hxs
  have hP : 1 ≤ 10 ^ (c - cs) := Nat.pow_pos (by decide)
  have hQU : Q ≤ sqU x c := Nat.le_trans (Nat.le_mul_of_pos_right _ hP) (Nat.le_trans hqa hU)
  have hG : g.mag * 10 ^ (cs - g.scale) * 10 ^ (c - cs) = g.align c := by
    unfold Num.align; rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  have hBU : g.mag * 10 ^ (cs - g.scale) ≤ sqU x c :=
    Nat.le_trans (Nat.le_mul_of_pos_right _ hP) (by rw [hG]; exact hb)
  have hE : 10 * (2 * sqU x c) < 10 ^ (n + 2 * c + 3) := by
    rw [show n + 2 * c + 3 = (n + 2 * c + 1) + 2 by omega, Nat.pow_add]
    have : (10 : Nat) ^ 2 = 100 := rfl
    omega
  generalize hB : g.mag * 10 ^ (cs - g.scale) = B at hBU
  have ea : Num.add ⟨false, Q, cs⟩ g 0 = ⟨false, Q + B, cs⟩ := by
    have e1 : max 0 (max cs g.scale) = cs := by omega
    simp only [Num.add, Num.align, e1, Nat.sub_self, Nat.pow_zero, Nat.mul_one, hx, hgn, hB]
    split <;> simp_all
  have em : Num.mul ⟨false, Q + B, cs⟩ Num.half cs = ⟨false, (Q + B) * 5 / 10 ^ 1, cs⟩ := by
    have e2 : min (cs + 1) (max cs (max cs 1)) = cs := by omega
    have e3 : cs + 1 - cs = 1 := by omega
    simp only [Num.mul, Num.half, e2, e3]
    split <;> simp_all
  have hdm : (Num.sub ⟨false, (Q + B) * 5 / 10 ^ 1, cs⟩ g (cs + 1)).mag ≤
      (Q + B) * 5 / 10 ^ 1 * 10 + B * 10 := by
    have e1 : max (cs + 1) (max cs g.scale) = cs + 1 := by omega
    have e4 : g.mag * 10 ^ (cs + 1 - g.scale) = B * 10 := by
      rw [← hB, show cs + 1 - g.scale = (cs - g.scale) + 1 by omega, Nat.pow_succ, Nat.mul_assoc]
    simp only [Num.sub, Num.align, e1, e4, show cs + 1 - cs = 1 by omega, Nat.pow_one, hgn]
    split
    · simp only; omega
    · split <;> simp only [Num.zero] <;> omega
  have hds : (Num.sub ⟨false, (Q + B) * 5 / 10 ^ 1, cs⟩ g (cs + 1)).scale = cs + 1 := by
    have e1 : max (cs + 1) (max cs g.scale) = cs + 1 := by omega
    simp only [Num.sub, e1]
    split
    · rfl
    · split <;> rfl
  have h5 : (Q + B) * 5 / 10 ^ 1 ≤ Q + B := by rw [show (10 : Nat) ^ 1 = 10 from rfl]; omega
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ea, em]
  all_goals first | exact hds | omega

/-- A guess's own magnitude bound. -/
theorem SqInv.mag_lt {x g : Num} {c cs n : Nat} (h : SqInv x c g cs) (hxs : x.scale ≤ c)
    (hxn : x.mag < 10 ^ (n + x.scale)) : g.mag < 10 ^ (n + 2 * c + 3) := by
  have hb := h.bound
  have hUl := sqU_lt hxn hxs
  have hle : g.mag ≤ g.align c := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
  have : 10 ^ (n + 2 * c + 1) ≤ 10 ^ (n + 2 * c + 3) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The first guess above one is nonzero. -/
theorem sqG_initHi {x : Num} {k u : Nat} (hx : 10 ^ (u + x.scale) ≤ x.mag) :
    SqG x (sqC x k) ⟨false, 10 ^ u, 0⟩ 3 :=
  { sqInv_initHi hx with
    nz := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
    low := Nat.le_trans (Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ u)) hx)
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))) }

/-- The first guess below one is nonzero. -/
theorem sqG_initLo {x : Num} {k : Nat} (hs : 1 ≤ x.scale) (hm : x.mag ≠ 0) :
    SqG x (sqC x k) Num.one x.scale :=
  { sqInv_initLo hs with
    nz := by decide
    low := by
      calc 10 ^ x.scale ≤ 1 * 10 ^ (2 * x.scale) := by
            rw [Nat.one_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero hm) }

end Dc.BcModel
