import Dc.BcModel.Digits

/-!
# The column product of `_bc_simp_mul`

`_bc_simp_mul` computes the product column by column from the least
significant end: column `k` sums `a i * b (k - i)` (little-endian digit
functions, zero outside the operands), the running `sum` keeps the carry,
and each column writes `sum % 10`; the last position gets the final carry.

- `sumR f n`: `f 0 + … + f (n - 1)`.
- `conv a b k`: the column sum `Σ_{i ≤ k} a i * b (k - i)`.
- `dotLoop a la b i j`: what the inner loop adds from `n1ptr` at
  little-endian index `i` and `n2ptr` at `j` (stopping at `i = la` or after
  `j = 0`); `dotLoop_eq_conv` identifies it with the column sum.
- `propLE cs c`: the outer loop's digits from column sums `cs` and carry `c`;
  `dvalLE (propLE cs c) = dvalLE cs + c`.
- `dvalLE_convs`: the columns of two digit lists have the product's value.
-/

namespace Dc.BcModel

/-- `f 0 + … + f (n - 1)`. -/
def sumR (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumR f n + f n

theorem sumR_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ i, i < n → f i = g i) → sumR f n = sumR g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sumR]
    rw [sumR_congr fun i hi => h i (by omega), h n (by omega)]

theorem sumR_zero {f : Nat → Nat} : ∀ {n : Nat}, (∀ i, i < n → f i = 0) → sumR f n = 0
  | 0, _ => rfl
  | n + 1, h => by simp only [sumR]; rw [sumR_zero fun i hi => h i (by omega), h n (by omega)]

theorem sumR_add (f g : Nat → Nat) : ∀ n, sumR (fun i => f i + g i) n = sumR f n + sumR g n
  | 0 => rfl
  | n + 1 => by simp only [sumR]; rw [sumR_add f g n]; omega

theorem sumR_mul (c : Nat) (f : Nat → Nat) : ∀ n, sumR (fun i => c * f i) n = c * sumR f n
  | 0 => rfl
  | n + 1 => by simp only [sumR]; rw [sumR_mul c f n, Nat.mul_add]

/-- Peel the first term. -/
theorem sumR_succ' (f : Nat → Nat) : ∀ n, sumR f (n + 1) = f 0 + sumR (fun i => f (i + 1)) n
  | 0 => by simp [sumR]
  | n + 1 => by
    rw [sumR, sumR_succ' f n, sumR]
    omega

/-- Extend a sum by terms that vanish. -/
theorem sumR_extend {f : Nat → Nat} {m n : Nat} (hmn : m ≤ n) (h : ∀ i, m ≤ i → i < n → f i = 0) :
    sumR f n = sumR f m := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; rfl
  | succ n ih =>
    rcases Nat.lt_or_ge n m with h1 | h1
    · have : m = n + 1 := by omega
      subst this; rfl
    · simp only [sumR]
      rw [ih (by omega) fun i h2 h3 => h i h2 (by omega), h n h1 (by omega), Nat.add_zero]

/-- The column sum `Σ_{i ≤ k} a i * b (k - i)`. -/
def conv (a b : Nat → Nat) (k : Nat) : Nat := sumR (fun i => a i * b (k - i)) (k + 1)

/-- The value of a function's first `n` entries, little-endian. -/
def fval (f : Nat → Nat) (n : Nat) : Nat := sumR (fun i => f i * 10 ^ i) n

theorem fval_succ' (f : Nat → Nat) (n : Nat) :
    fval f (n + 1) = f 0 + 10 * fval (fun i => f (i + 1)) n := by
  simp only [fval]
  rw [sumR_succ', ← sumR_mul]
  simp only [Nat.pow_zero, Nat.mul_one, Nat.pow_succ]
  congr 1
  refine sumR_congr fun i _ => ?_
  rw [Nat.mul_comm (10 ^ i) 10, Nat.mul_left_comm]

/-- The digit function of a little-endian list. -/
abbrev dig (ds : List Nat) (i : Nat) : Nat := ds.getD i 0

theorem fval_dig : ∀ (ds : List Nat), fval (dig ds) ds.length = dvalLE ds
  | [] => rfl
  | d :: ds => by
    rw [List.length_cons, fval_succ', dvalLE]
    simp only [dig, List.getD_cons_zero, List.getD_cons_succ]
    rw [fval_dig ds]

/-- Entries beyond the list are zero. -/
theorem dig_ge {ds : List Nat} {i : Nat} (h : ds.length ≤ i) : dig ds i = 0 := by
  simp only [dig, List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem fval_extend {f : Nat → Nat} {m n : Nat} (hmn : m ≤ n) (h : ∀ i, m ≤ i → f i = 0) :
    fval f n = fval f m := by
  unfold fval
  exact sumR_extend hmn fun i h1 _ => by rw [h i h1, Nat.zero_mul]

theorem conv_succ_shift (a b : Nat → Nat) (k : Nat) :
    conv a b (k + 1) = a 0 * b (k + 1) + conv (fun j => a (j + 1)) b k := by
  unfold conv
  rw [sumR_succ']
  simp only [Nat.sub_zero]
  congr 1
  refine sumR_congr fun i _ => ?_
  congr 2; omega

theorem conv_zero (a b : Nat → Nat) : conv a b 0 = a 0 * b 0 := by
  simp [conv, sumR]

/-- **The columns have the product's value**: for `a`, `b` zero from `la`,
`lb` on, the first `n ≥ la + lb` columns sum to `fval a la * fval b lb`. -/
theorem fval_conv : ∀ (la : Nat) (a b : Nat → Nat) (lb n : Nat), (∀ i, la ≤ i → a i = 0) →
    (∀ i, lb ≤ i → b i = 0) → la + lb ≤ n → fval (conv a b) n = fval a la * fval b lb
  | 0, a, b, lb, n, ha, hb, hn => by
    rw [show fval a 0 = 0 from rfl, Nat.zero_mul]
    unfold fval
    refine sumR_zero fun k _ => ?_
    rw [show conv a b k = 0 from sumR_zero fun i _ => by rw [ha i (Nat.zero_le _), Nat.zero_mul],
      Nat.zero_mul]
  | la + 1, a, b, lb, n, ha, hb, hn => by
    have ih := fval_conv la (fun j => a (j + 1)) b lb (n - 1) (fun i hi => ha (i + 1) (by omega)) hb
      (by omega)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel] at ih
    rw [fval_succ', fval_succ' a, conv_zero]
    simp only [conv_succ_shift]
    -- columns `x * b (k+1) + conv a' b k`
    have hsplit : fval (fun i => a 0 * b (i + 1) + conv (fun j => a (j + 1)) b i) n' =
        a 0 * fval (fun i => b (i + 1)) n' + fval (conv (fun j => a (j + 1)) b) n' := by
      unfold fval
      rw [← sumR_mul, ← sumR_add]
      exact sumR_congr fun i _ => by rw [Nat.add_mul, Nat.mul_assoc]
    rw [hsplit, ih]
    -- `fval b` peeled
    have hb' : fval b (n' + 1) = b 0 + 10 * fval (fun i => b (i + 1)) n' := fval_succ' b n'
    have hbl : fval b (n' + 1) = fval b lb := fval_extend (by omega) hb
    generalize fval (fun i => b (i + 1)) n' = F at hb'
    generalize fval (fun j => a (j + 1)) la = A
    rw [← hbl, hb']
    generalize a 0 = x
    generalize b 0 = y
    rw [Nat.add_mul, Nat.mul_add x, Nat.mul_left_comm x 10 F, Nat.mul_assoc 10 A]
    omega

/-! ## The inner loop -/

/-- The inner loop's sum from `n1ptr` at index `i` (of `la` digits) and
`n2ptr` at index `j`: it adds `a i * b j` and moves to `(i + 1, j - 1)`,
stopping after `j = 0` or at `i = la`. -/
def dotLoop (a : Nat → Nat) (la : Nat) (b : Nat → Nat) : Nat → Nat → Nat
  | i, 0 => if i < la then a i * b 0 else 0
  | i, j + 1 => if i < la then a i * b (j + 1) + dotLoop a la b (i + 1) j else 0

/-- The loop's sum is the column sum over the remaining pairs. -/
theorem dotLoop_eq (a : Nat → Nat) (la : Nat) (b : Nat → Nat) (ha : ∀ i, la ≤ i → a i = 0) :
    ∀ j i, dotLoop a la b i j = sumR (fun t => a (i + t) * b (j - t)) (j + 1)
  | 0, i => by
    simp only [dotLoop, sumR, Nat.zero_add, Nat.add_zero, Nat.sub_zero]
    split
    · rfl
    · rw [ha i (by omega), Nat.zero_mul]
  | j + 1, i => by
    rw [sumR_succ']
    simp only [dotLoop, Nat.add_zero, Nat.sub_zero]
    split
    · rw [dotLoop_eq a la b ha j (i + 1)]
      congr 1
      exact sumR_congr fun t _ => by rw [Nat.add_assoc, Nat.add_comm 1 t]; congr 2; omega
    · rw [ha i (by omega), Nat.zero_mul, Nat.zero_add]
      exact (sumR_zero fun t _ => by rw [ha (i + (t + 1)) (by omega), Nat.zero_mul]).symm

/-- **The inner loop computes column `k`**: started at `i0 = k - j0`,
`j0 = min k (lb - 1)` (as `_bc_simp_mul` does), with `b` zero from `lb`. -/
theorem dotLoop_eq_conv (a : Nat → Nat) (la : Nat) (b : Nat → Nat) (lb k : Nat) (hlb : 1 ≤ lb)
    (ha : ∀ i, la ≤ i → a i = 0) (hb : ∀ j, lb ≤ j → b j = 0) :
    dotLoop a la b (k - min k (lb - 1)) (min k (lb - 1)) = conv a b k := by
  rw [dotLoop_eq a la b ha]
  unfold conv
  -- the column's terms below `i0` vanish (`b` beyond `lb`)
  have hi0 : ∀ m, m ≤ k + 1 → sumR (fun i => a i * b (k - i)) (k + 1) =
      sumR (fun i => a i * b (k - i)) m +
      sumR (fun t => a (m + t) * b (k - (m + t))) (k + 1 - m) := by
    intro m hm
    induction m with
    | zero => simp [sumR]
    | succ m ih =>
      rw [ih (by omega), sumR]
      obtain ⟨r, hr⟩ : ∃ r, k + 1 - m = r + 1 := ⟨k - m, by omega⟩
      rw [hr, sumR_succ', show k + 1 - (m + 1) = r by omega]
      simp only [Nat.add_zero]
      rw [Nat.add_assoc]
      congr 2
      exact sumR_congr fun t _ => by rw [Nat.add_assoc, Nat.add_comm 1 t]
  rw [hi0 (k - min k (lb - 1)) (by omega)]
  rw [sumR_zero (n := k - min k (lb - 1)) fun i hi => by rw [hb (k - i) (by omega), Nat.mul_zero],
    Nat.zero_add, show k + 1 - (k - min k (lb - 1)) = min k (lb - 1) + 1 by omega]
  exact sumR_congr fun t _ => by congr 2; omega

/-! ## Carry propagation -/

/-- The outer loop's digits from column sums `cs` (little-endian) and the
running carry `c`; the last digit is the final carry. -/
def propLE : List Nat → Nat → List Nat
  | [], c => [c]
  | x :: xs, c => (c + x) % 10 :: propLE xs ((c + x) / 10)

theorem propLE_val : ∀ (cs : List Nat) (c : Nat), dvalLE (propLE cs c) = dvalLE cs + c
  | [], c => by simp [propLE, dvalLE]
  | x :: xs, c => by
    simp only [propLE, dvalLE]
    rw [propLE_val xs]
    have := Nat.mod_add_div (c + x) 10
    omega

theorem propLE_length : ∀ (cs : List Nat) (c : Nat), (propLE cs c).length = cs.length + 1
  | [], _ => rfl
  | _ :: xs, c => by simp only [propLE, List.length_cons]; rw [propLE_length xs]

theorem dvalLE_map_range (f : Nat → Nat) : ∀ n, dvalLE ((List.range n).map f) = fval f n := by
  intro n
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, dvalLE, fval_succ']
    congr 2
    exact ih (fun i => f (i + 1))

/-- **`_bc_simp_mul`'s digits** (little-endian) for operands of `la`, `lb`
digits: the column sums `conv` of the first `la + lb - 1` columns,
propagated from carry `0`. Their value is the product. -/
def simpMulLE (a : Nat → Nat) (la : Nat) (b : Nat → Nat) (lb : Nat) : List Nat :=
  propLE ((List.range (la + lb - 1)).map (conv a b)) 0

theorem simpMulLE_val (a : Nat → Nat) (la : Nat) (b : Nat → Nat) (lb : Nat) (hla : 1 ≤ la)
    (hlb : 1 ≤ lb) (ha : ∀ i, la ≤ i → a i = 0) (hb : ∀ j, lb ≤ j → b j = 0) :
    dvalLE (simpMulLE a la b lb) = fval a la * fval b lb := by
  unfold simpMulLE
  rw [propLE_val, dvalLE_map_range, Nat.add_zero]
  rw [← fval_conv la a b lb (la + lb) ha hb (Nat.le_refl _)]
  refine (fval_extend (by omega) fun k hk => ?_).symm
  unfold conv
  exact sumR_zero fun i hi => by
    rcases Nat.lt_or_ge i la with h1 | h1
    · rw [hb (k - i) (by omega), Nat.mul_zero]
    · rw [ha i h1, Nat.zero_mul]

theorem simpMulLE_length (a : Nat → Nat) (la : Nat) (b : Nat → Nat) (lb : Nat) :
    (simpMulLE a la b lb).length = la + lb - 1 + 1 := by
  simp [simpMulLE, propLE_length]

end Dc.BcModel
