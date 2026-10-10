import Dc.BcModel.Digits

/-!
# One position at a time

The machine loops of `_bc_do_add` and `_bc_do_sub` produce one result digit
per iteration, from the last array position down, carrying a bit. This file
states the models of `Digits.lean` position by position:

- `carryAt xs ys c k`: the carry into position `k` of `addLE xs ys c`;
  `addLE_getD`, `carryAt_succ`, `addLE_getD_last` give digit `k`, the next
  carry and the final carry digit.
- `padLE_getD`: digit `k` of an aligned operand.
- `sumDs N k r Z`: a big-endian array of `N` positions whose last `k` hold
  the first `k` little-endian digits of `r`, the rest zero, followed by `Z`;
  `sumDs_step` writes position `N - 1 - k`.
-/

namespace Dc.BcModel

/-- The carry into position `k` of `addLE xs ys c`. -/
def carryAt : List Nat → List Nat → Nat → Nat → Nat
  | x :: xs, y :: ys, c, k + 1 => carryAt xs ys ((x + y + c) / 10) k
  | _, _, c, _ => c

theorem carryAt_zero (xs ys : List Nat) (c : Nat) : carryAt xs ys c 0 = c := by
  cases xs <;> cases ys <;> rfl

theorem addLE_getD : ∀ (xs ys : List Nat) (c k : Nat), xs.length = ys.length → k < xs.length →
    (addLE xs ys c).getD k 0 = (xs.getD k 0 + ys.getD k 0 + carryAt xs ys c k) % 10
  | _ :: _, _ :: _, c, 0, _, _ => by simp [addLE, carryAt_zero]
  | _ :: xs, _ :: ys, c, k + 1, h, hk => by
    simp only [addLE, List.getD_cons_succ, carryAt]
    exact addLE_getD xs ys _ k (by simpa using h) (by simpa using hk)
  | [], _, _, _, _, hk => by simp at hk
  | _ :: _, [], _, _, h, _ => by simp at h

theorem carryAt_succ : ∀ (xs ys : List Nat) (c k : Nat), xs.length = ys.length → k < xs.length →
    carryAt xs ys c (k + 1) = (xs.getD k 0 + ys.getD k 0 + carryAt xs ys c k) / 10
  | _ :: _, _ :: _, c, 0, _, _ => by simp [carryAt, carryAt_zero]
  | _ :: xs, _ :: ys, c, k + 1, h, hk => by
    simp only [carryAt, List.getD_cons_succ]
    exact carryAt_succ xs ys _ k (by simpa using h) (by simpa using hk)
  | [], _, _, _, _, hk => by simp at hk
  | _ :: _, [], _, _, h, _ => by simp at h

theorem addLE_getD_last : ∀ (xs ys : List Nat) (c : Nat), xs.length = ys.length →
    (addLE xs ys c).getD xs.length 0 = carryAt xs ys c xs.length
  | [], [], c, _ => by simp [addLE, carryAt_zero]
  | _ :: xs, _ :: ys, c, h => by
    simp only [addLE, List.length_cons, List.getD_cons_succ, carryAt]
    exact addLE_getD_last xs ys _ (by simpa using h)
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem carryAt_le : ∀ (xs ys : List Nat) (c k : Nat), IsDigits xs → IsDigits ys → c ≤ 1 →
    carryAt xs ys c k ≤ 1
  | x :: xs, y :: ys, c, k + 1, hx, hy, hc => by
    have h1 := hx x List.mem_cons_self
    have h2 := hy y List.mem_cons_self
    exact carryAt_le xs ys _ k (fun e he => hx e (List.mem_cons_of_mem _ he))
      (fun e he => hy e (List.mem_cons_of_mem _ he)) (by omega)
  | [], _, c, _, _, _, hc => by cases ‹List Nat› <;> exact hc
  | _ :: _, [], c, _, _, _, hc => hc
  | _ :: _, _ :: _, c, 0, _, _, hc => hc

/-- One position of a sum: the digit and the carry out. -/
theorem digit_add {x y c : Nat} (hx : x < 10) (hy : y < 10) (hc : c ≤ 1) :
    (if 9 < x + y + c then x + y + c - 10 else x + y + c) = (x + y + c) % 10 ∧
      (if 9 < x + y + c then 1 else 0) = (x + y + c) / 10 := by
  constructor <;> split <;> omega

/-! ## Aligned operands -/

theorem padLE_getD (ds : List Nat) (sc s m k : Nat) :
    (padLE ds sc s m).getD k 0 = if k < s - sc then 0 else ds.reverse.getD (k - (s - sc)) 0 := by
  simp only [padLE, List.getD_eq_getElem?_getD]
  split
  · rename_i hk
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_replicate]
    simp [hk]
  · rename_i hk
    by_cases h2 : k < s - sc + ds.length
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp
    · rw [List.getElem?_append_right (by simp; omega)]
      rw [List.getElem?_eq_none (show ds.reverse.length ≤ k - (s - sc) by simp; omega)]
      simp only [List.getElem?_replicate]
      split <;> simp

/-! ## Writing the result from the end -/

/-- `N` positions: zeros, then the first `k` little-endian digits of `r`
reversed; then `Z`. -/
def sumDs (N k : Nat) (r Z : List Nat) : List Nat :=
  List.replicate (N - k) 0 ++ (r.take k).reverse ++ Z

theorem sumDs_length {N k : Nat} {r Z : List Nat} (hk : k ≤ N) (hr : k ≤ r.length) :
    (sumDs N k r Z).length = N + Z.length := by
  simp only [sumDs, List.length_append, List.length_replicate, List.length_reverse,
    List.length_take]
  omega

theorem sumDs_zero (N : Nat) (r Z : List Nat) : sumDs N 0 r Z = List.replicate N 0 ++ Z := by
  simp [sumDs]

theorem sumDs_full {N : Nat} {r Z : List Nat} (hr : r.length = N) :
    sumDs N N r Z = r.reverse ++ Z := by
  simp [sumDs, ← hr]

/-- Position `N - 1 - k` written with digit `k` of `r`. -/
theorem sumDs_step {N k : Nat} {r Z : List Nat} (hk : k < N) (hr : k < r.length) :
    (sumDs N k r Z).set (N - 1 - k) (r.getD k 0) = sumDs N (k + 1) r Z := by
  have e1 : List.replicate (N - k) 0 = List.replicate (N - (k + 1)) 0 ++ [0] := by
    rw [show N - k = N - (k + 1) + 1 by omega, List.replicate_succ']
  have e2 : (r.take (k + 1)).reverse = r.getD k 0 :: (r.take k).reverse := by
    rw [List.take_add_one, List.getElem?_eq_getElem hr, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hr]
    simp
  simp only [sumDs, e1, e2, List.append_assoc, List.cons_append]
  rw [List.set_append_right _ _ (by simp; omega)]
  simp only [List.length_replicate, show N - 1 - k - (N - (k + 1)) = 0 by omega, List.set_cons_zero,
    List.nil_append]

/-! ## Subtraction, position by position -/

/-- The borrow into position `k` of `subLE xs ys b`. -/
def borrowAt : List Nat → List Nat → Nat → Nat → Nat
  | x :: xs, y :: ys, b, k + 1 => borrowAt xs ys (if x < y + b then 1 else 0) k
  | _, _, b, _ => b

theorem borrowAt_zero (xs ys : List Nat) (b : Nat) : borrowAt xs ys b 0 = b := by
  cases xs <;> cases ys <;> rfl

theorem subLE_getD : ∀ (xs ys : List Nat) (b k : Nat), xs.length = ys.length → k < xs.length →
    (subLE xs ys b).getD k 0 =
      if xs.getD k 0 < ys.getD k 0 + borrowAt xs ys b k then
        xs.getD k 0 + 10 - ys.getD k 0 - borrowAt xs ys b k
      else xs.getD k 0 - ys.getD k 0 - borrowAt xs ys b k
  | _ :: _, _ :: _, b, 0, _, _ => by
    simp only [subLE, borrowAt_zero, List.getD_cons_zero]; split <;> rfl
  | x :: xs, y :: ys, b, k + 1, h, hk => by
    simp only [subLE, List.getD_cons_succ, borrowAt]
    split
    · rw [List.getD_cons_succ, subLE_getD xs ys 1 k (by simpa using h) (by simpa using hk)]
    · rw [List.getD_cons_succ, subLE_getD xs ys 0 k (by simpa using h) (by simpa using hk)]
  | [], _, _, _, _, hk => by simp at hk
  | _ :: _, [], _, _, h, _ => by simp at h

theorem borrowAt_succ : ∀ (xs ys : List Nat) (b k : Nat), xs.length = ys.length → k < xs.length →
    borrowAt xs ys b (k + 1) =
      if xs.getD k 0 < ys.getD k 0 + borrowAt xs ys b k then 1 else 0
  | _ :: _, _ :: _, b, 0, _, _ => by simp only [borrowAt, borrowAt_zero, List.getD_cons_zero]
  | x :: xs, y :: ys, b, k + 1, h, hk => by
    simp only [borrowAt, List.getD_cons_succ]
    exact borrowAt_succ xs ys _ k (by simpa using h) (by simpa using hk)
  | [], _, _, _, _, hk => by simp at hk
  | _ :: _, [], _, _, h, _ => by simp at h

theorem borrowAt_le : ∀ (xs ys : List Nat) (b k : Nat), b ≤ 1 → borrowAt xs ys b k ≤ 1
  | x :: xs, y :: ys, b, k + 1, hb => borrowAt_le xs ys _ k (by split <;> decide)
  | [], _, b, _, hb => by cases ‹List Nat› <;> exact hb
  | _ :: _, [], b, _, hb => hb
  | _ :: _, _ :: _, b, 0, hb => hb

/-- One position of a difference: the digit and the borrow out. -/
theorem digit_sub {x y b : Nat} (hx : x < 10) (hy : y < 10) (hb : b ≤ 1) :
    (if x < y + b then x + 10 - y - b else x - y - b) < 10 := by
  split <;> omega

end Dc.BcModel
