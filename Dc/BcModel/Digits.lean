import Dc.Num

/-!
# Digit-array arithmetic of `lib/number.c`

The value-level model of the digit loops of `_bc_do_add` and `_bc_do_sub`.
A machine digit array is big-endian (`n_value[0]` is the most significant
digit); the loops run from the last digit to the first, so the models work on
little-endian lists (`dvalLE`).

- `dvalBE` is `Dc.Mach.dval` (the value of a big-endian list); `dvalLE` its
  little-endian counterpart, `dvalLE_reverse` relates them.
- `addLE xs ys c`: digit-wise sum with carry of two lists of equal length,
  ending with the final carry digit (`_bc_do_add`'s loops and its
  `*sumptr += carry`).
- `subLE xs ys b`: digit-wise difference with borrow (`_bc_do_sub`'s loops);
  with `ys ≤ xs` in value the final borrow is zero.
- `padLE ds sc s m`: a number's digits aligned to `s` fraction digits and `m`
  integer-plus-fraction positions (zeros below its own scale and above its
  integer part).
-/

namespace Dc.BcModel

/-- The value of a big-endian decimal digit list (`Dc.Mach.dval`). -/
def dvalBE (ds : List Nat) : Nat := ds.foldl (fun a d => 10 * a + d) 0

/-- The value of a little-endian digit list. -/
def dvalLE : List Nat → Nat
  | [] => 0
  | d :: ds => d + 10 * dvalLE ds

/-- Every entry is a decimal digit. -/
abbrev IsDigits (ds : List Nat) : Prop := ∀ d ∈ ds, d < 10

theorem foldl_dvalBE (a : Nat) : ∀ ds : List Nat,
    ds.foldl (fun a d => 10 * a + d) a = a * 10 ^ ds.length + dvalBE ds
  | [] => by simp [dvalBE]
  | d :: ds => by
    simp only [List.foldl_cons, List.length_cons, dvalBE]
    rw [foldl_dvalBE (10 * a + d) ds, foldl_dvalBE (10 * 0 + d) ds, Nat.pow_succ]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_mul, Nat.add_assoc]
    rw [Nat.mul_comm (10 ^ ds.length) 10, ← Nat.mul_assoc, Nat.mul_comm a 10]

theorem dvalBE_nil : dvalBE [] = 0 := rfl

theorem dvalBE_append (xs ys : List Nat) :
    dvalBE (xs ++ ys) = dvalBE xs * 10 ^ ys.length + dvalBE ys := by
  unfold dvalBE
  rw [List.foldl_append, foldl_dvalBE]
  rfl

theorem dvalBE_cons (d : Nat) (ds : List Nat) :
    dvalBE (d :: ds) = d * 10 ^ ds.length + dvalBE ds := by
  have := dvalBE_append [d] ds
  rw [List.singleton_append] at this
  rw [this]; simp [dvalBE]

theorem dvalLE_append (xs ys : List Nat) :
    dvalLE (xs ++ ys) = dvalLE xs + 10 ^ xs.length * dvalLE ys := by
  induction xs with
  | nil => simp [dvalLE]
  | cons x xs ih =>
    simp only [List.cons_append, dvalLE, ih, List.length_cons, Nat.pow_succ, Nat.mul_add]
    rw [Nat.mul_comm (10 ^ xs.length) 10, Nat.mul_assoc]
    omega

theorem dvalLE_reverse (ds : List Nat) : dvalLE ds.reverse = dvalBE ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.reverse_cons, dvalLE_append, ih, dvalBE_cons, List.length_reverse]
    simp only [dvalLE, Nat.mul_zero, Nat.add_zero]
    rw [Nat.mul_comm, Nat.add_comm]

theorem dvalBE_reverse (ds : List Nat) : dvalBE ds.reverse = dvalLE ds := by
  rw [← dvalLE_reverse, List.reverse_reverse]

theorem dvalLE_replicate_zero (n : Nat) : dvalLE (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, dvalLE, ih]

theorem dvalBE_replicate_zero (n : Nat) : dvalBE (List.replicate n 0) = 0 := by
  rw [← dvalLE_reverse, List.reverse_replicate, dvalLE_replicate_zero]

theorem dvalLE_lt : ∀ {ds : List Nat}, IsDigits ds → dvalLE ds < 10 ^ ds.length
  | [], _ => by simp [dvalLE]
  | d :: ds, h => by
    have hd := h d List.mem_cons_self
    have ih := dvalLE_lt (ds := ds) fun e he => h e (List.mem_cons_of_mem _ he)
    simp only [dvalLE, List.length_cons, Nat.pow_succ]
    have : 10 * dvalLE ds + 10 ≤ 10 * 10 ^ ds.length := by omega
    rw [Nat.mul_comm (10 ^ ds.length) 10]
    omega

/-! ## Addition with carry -/

/-- Digit-wise sum with carry of two lists of equal length, with the final
carry as the last (most significant) digit. -/
def addLE : List Nat → List Nat → Nat → List Nat
  | x :: xs, y :: ys, c => (x + y + c) % 10 :: addLE xs ys ((x + y + c) / 10)
  | _, _, c => [c]

theorem addLE_val : ∀ (xs ys : List Nat) (c : Nat), xs.length = ys.length →
    dvalLE (addLE xs ys c) = dvalLE xs + dvalLE ys + c
  | [], [], c, _ => by simp [addLE, dvalLE]
  | x :: xs, y :: ys, c, h => by
    simp only [addLE, dvalLE]
    rw [addLE_val xs ys _ (by simpa using h)]
    have := Nat.mod_add_div (x + y + c) 10
    omega
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem addLE_length : ∀ (xs ys : List Nat) (c : Nat), xs.length = ys.length →
    (addLE xs ys c).length = xs.length + 1
  | [], [], c, _ => rfl
  | x :: xs, y :: ys, c, h => by
    simp only [addLE, List.length_cons]
    rw [addLE_length xs ys _ (by simpa using h)]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- The carry stays a bit on digits. -/
theorem addLE_digits : ∀ (xs ys : List Nat) (c : Nat), IsDigits xs → IsDigits ys → c ≤ 1 →
    xs.length = ys.length → IsDigits (addLE xs ys c)
  | [], [], c, _, _, hc, _ => by
    intro d hd; simp only [addLE, List.mem_cons, List.not_mem_nil, or_false] at hd; omega
  | x :: xs, y :: ys, c, hx, hy, hc, h => by
    have h1 := hx x List.mem_cons_self
    have h2 := hy y List.mem_cons_self
    intro d hd
    simp only [addLE, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ (by decide)
    · exact addLE_digits xs ys _ (fun e he => hx e (List.mem_cons_of_mem _ he))
        (fun e he => hy e (List.mem_cons_of_mem _ he)) (by omega) (by simpa using h) d hd
  | [], _ :: _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h

/-! ## Subtraction with borrow -/

/-- Digit-wise difference with borrow (`val = x - y - borrow`, plus `BASE`
when negative). -/
def subLE : List Nat → List Nat → Nat → List Nat
  | x :: xs, y :: ys, b =>
    if x < y + b then (x + 10 - y - b) :: subLE xs ys 1 else (x - y - b) :: subLE xs ys 0
  | _, _, _ => []

/-- The final borrow of `subLE`. -/
def subBorrow : List Nat → List Nat → Nat → Nat
  | x :: xs, y :: ys, b => if x < y + b then subBorrow xs ys 1 else subBorrow xs ys 0
  | _, _, b => b

theorem subLE_val : ∀ (xs ys : List Nat) (b : Nat), xs.length = ys.length → IsDigits ys → b ≤ 1 →
    dvalLE (subLE xs ys b) + dvalLE ys + b = dvalLE xs + 10 ^ xs.length * subBorrow xs ys b
  | [], [], b, _, _, _ => by simp [subLE, subBorrow, dvalLE]
  | x :: xs, y :: ys, b, h, hy, hb => by
    have h2 := hy y List.mem_cons_self
    have hy' : IsDigits ys := fun e he => hy e (List.mem_cons_of_mem _ he)
    have hl : xs.length = ys.length := by simpa using h
    simp only [subLE, subBorrow]
    split
    · have ih := subLE_val xs ys 1 hl hy' (by decide)
      simp only [dvalLE, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (10 ^ xs.length) 10, Nat.mul_assoc]
      omega
    · have ih := subLE_val xs ys 0 hl hy' (by decide)
      simp only [dvalLE, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (10 ^ xs.length) 10, Nat.mul_assoc]
      omega
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h

theorem subLE_length : ∀ (xs ys : List Nat) (b : Nat), xs.length = ys.length →
    (subLE xs ys b).length = xs.length
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, b, h => by
    simp only [subLE]
    split <;> simp only [List.length_cons] <;> rw [subLE_length xs ys _ (by simpa using h)]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem subLE_digits : ∀ (xs ys : List Nat) (b : Nat), IsDigits xs → IsDigits ys → b ≤ 1 →
    IsDigits (subLE xs ys b)
  | [], _, _, _, _, _ => by intro d hd; simp [subLE] at hd
  | _ :: _, [], _, _, _, _ => by intro d hd; simp [subLE] at hd
  | x :: xs, y :: ys, b, hx, hy, hb => by
    have h1 := hx x List.mem_cons_self
    have h2 := hy y List.mem_cons_self
    have hx' : IsDigits xs := fun e he => hx e (List.mem_cons_of_mem _ he)
    have hy' : IsDigits ys := fun e he => hy e (List.mem_cons_of_mem _ he)
    simp only [subLE]
    split
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · exact subLE_digits xs ys 1 hx' hy' (by decide) d hd
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · exact subLE_digits xs ys 0 hx' hy' (by decide) d hd

theorem subBorrow_le : ∀ (xs ys : List Nat) (b : Nat), b ≤ 1 → subBorrow xs ys b ≤ 1
  | x :: xs, y :: ys, b, hb => by
    simp only [subBorrow]; split
    · exact subBorrow_le xs ys 1 (by decide)
    · exact subBorrow_le xs ys 0 (by decide)
  | [], _, _, hb => hb
  | _ :: _, [], _, hb => hb

/-- With the subtrahend's value at most the minuend's, no borrow is left and
the difference is exact. -/
theorem subLE_exact (xs ys : List Nat) (h : xs.length = ys.length) (hx : IsDigits xs)
    (hy : IsDigits ys) (hle : dvalLE ys ≤ dvalLE xs) :
    subBorrow xs ys 0 = 0 ∧ dvalLE (subLE xs ys 0) = dvalLE xs - dvalLE ys := by
  have hv := subLE_val xs ys 0 h hy (by decide)
  have hb := subBorrow_le xs ys 0 (by decide)
  have hd := dvalLE_lt (subLE_digits xs ys 0 hx hy (by decide))
  rw [subLE_length xs ys 0 h] at hd
  rcases Nat.lt_or_ge (subBorrow xs ys 0) 1 with h0 | h1
  · refine ⟨by omega, ?_⟩
    have : subBorrow xs ys 0 = 0 := by omega
    rw [this, Nat.mul_zero] at hv
    omega
  · exfalso
    have : subBorrow xs ys 0 = 1 := by omega
    rw [this, Nat.mul_one] at hv
    omega

/-! ## Alignment -/

/-- The digits `ds` (big-endian, `sc` fraction digits) as a little-endian list
aligned to `s ≥ sc` fraction digits and padded with zeros to `m` positions. -/
def padLE (ds : List Nat) (sc s m : Nat) : List Nat :=
  let core := List.replicate (s - sc) 0 ++ ds.reverse
  core ++ List.replicate (m - core.length) 0

theorem padLE_val (ds : List Nat) (sc s m : Nat) :
    dvalLE (padLE ds sc s m) = dvalBE ds * 10 ^ (s - sc) := by
  simp only [padLE, dvalLE_append, dvalLE_replicate_zero, dvalLE_reverse, List.length_replicate,
    Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  rw [Nat.mul_comm]

theorem padLE_length (ds : List Nat) (sc s m : Nat) (h : s - sc + ds.length ≤ m) :
    (padLE ds sc s m).length = m := by
  simp only [padLE, List.length_append, List.length_replicate, List.length_reverse]
  omega

theorem padLE_digits {ds : List Nat} (h : IsDigits ds) (sc s m : Nat) : IsDigits (padLE ds sc s m) := by
  intro d hd
  simp only [padLE, List.mem_append, List.mem_replicate, List.mem_reverse] at hd
  rcases hd with (⟨_, rfl⟩ | hd) | ⟨_, rfl⟩
  · decide
  · exact h d hd
  · decide

end Dc.BcModel
