import Dc.BcModel.Result

/-!
# Decimal output of `bc_out_num`

The base-10 branch of `bc_out_num` writes the integer digits of a
normalised number (none when the integer part is the single digit `0`),
then `.` and every fraction digit. `out10_chars` equates that byte list
with `Num.outChars n 10`.
-/

namespace Dc.BcModel

open Dc

theorem digitsIn_fuel (b : Nat) (hb : 2 ≤ b) :
    ∀ (f g n : Nat), n < f → n < g → Num.digitsIn b f n = Num.digitsIn b g n
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, g + 1, n, hf, hg => by
    simp only [Num.digitsIn]
    split
    · rfl
    · rename_i hn
      have hlt : n / b < n := Nat.div_lt_self (by simp at hn; omega) (by omega)
      rw [digitsIn_fuel b hb f g (n / b) (by omega) (by omega)]

/-- Peeling the last digit. -/
theorem digits_snoc (b : Nat) (hb : 2 ≤ b) (m d : Nat) (hd : d < b) (hne : b * m + d ≠ 0) :
    Num.digits b (b * m + d) = Num.digits b m ++ [d] := by
  have hq : (b * m + d) / b = m := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hd, Nat.zero_add]
  have hr : (b * m + d) % b = d := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  have h2 : 2 * m ≤ b * m := Nat.mul_le_mul_right _ hb
  show Num.digitsIn b (b * m + d + 1) (b * m + d) = Num.digitsIn b (m + 1) m ++ [d]
  rw [Num.digitsIn]
  simp only [beq_iff_eq, hne, ite_false]
  rw [hq, hr, digitsIn_fuel b hb (b * m + d) (m + 1) m (by omega) (by omega)]

/-- One step of `bc_out_num`'s integer-digit loop (`bc_modulo` pushes
`n % b`, `bc_divide` leaves `n / b`): the digits of `n` are the digits of
`n / b` followed by `n % b`. -/
theorem digits_step (b : Nat) (hb : 2 ≤ b) (n : Nat) (hn : n ≠ 0) :
    Num.digits b n = Num.digits b (n / b) ++ [n % b] := by
  have h := digits_snoc b hb (n / b) (n % b) (Nat.mod_lt _ (by omega)) (by rw [Nat.div_add_mod]; exact hn)
  rwa [Nat.div_add_mod] at h

/-- The invariant of that loop: the digits still to compute, then the
pushed stack (top first). -/
theorem digits_stack (b : Nat) (hb : 2 ≤ b) (n0 cur : Nat) (stk : List Nat)
    (h : Num.digits b n0 = Num.digits b cur ++ stk) (hc : cur ≠ 0) :
    Num.digits b n0 = Num.digits b (cur / b) ++ (cur % b :: stk) := by
  rw [h, digits_step b hb cur hc]; simp

/-- The decimal digits of a digit list without a leading zero are the list. -/
theorem digits_dvalBE_len : ∀ (n : Nat) (ds : List Nat), ds.length = n → IsDigits ds →
    (∀ d ∈ ds.head?, d ≠ 0) → Num.digits 10 (dvalBE ds) = ds
  | 0, ds, hl, _, _ => by rw [List.length_eq_zero_iff.mp hl]; rfl
  | n + 1, ds, hl, hds, hhead => by
    rcases List.eq_nil_or_concat ds with rfl | ⟨xs, d, rfl⟩
    · rfl
    simp only [List.concat_eq_append] at hl hds hhead ⊢
    have hd : d < 10 := hds d (List.mem_append_right _ (List.mem_singleton_self d))
    have hxs : IsDigits xs := fun e he => hds e (List.mem_append_left _ he)
    have hxl : xs.length = n := by simp at hl; omega
    have hval : dvalBE (xs ++ [d]) = 10 * dvalBE xs + d := by
      rw [dvalBE_append]; simp [dvalBE, Nat.mul_comm]
    rw [hval]
    cases xs with
    | nil =>
      have : d ≠ 0 := hhead d (by simp)
      have h := digits_snoc 10 (by decide) 0 d hd (by omega)
      have h0 : Num.digits 10 0 = [] := rfl
      simpa [dvalBE, h0] using h
    | cons x xs' =>
      have hx : x ≠ 0 := hhead x (by simp)
      have hpos : 10 ^ xs'.length ≤ dvalBE (x :: xs') := dvalBE_ge_top (Nat.pos_of_ne_zero hx)
      have hv : dvalBE (x :: xs') ≠ 0 := by
        have := Nat.pow_pos (n := xs'.length) (show 0 < 10 by decide); omega
      rw [digits_snoc 10 (by decide) _ d hd (by omega),
        digits_dvalBE_len n (x :: xs') hxl hxs (fun e he => hhead e (by simpa using he))]

/-- The decimal digits of a digit list without a leading zero are the list. -/
theorem digits_dvalBE (ds : List Nat) (h : IsDigits ds) (hh : ∀ d ∈ ds.head?, d ≠ 0) :
    Num.digits 10 (dvalBE ds) = ds :=
  digits_dvalBE_len _ ds rfl h hh

/-- A fraction of `s` digits: its significant digits after `s - k` zero
padding reproduce the list. -/
theorem frac_digits (fs : List Nat) (h : IsDigits fs) :
    List.replicate (fs.length - (Num.digits 10 (dvalBE fs)).length) 0 ++
      Num.digits 10 (dvalBE fs) = fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have hf : IsDigits fs := fun e he => h e (List.mem_cons_of_mem _ he)
    by_cases h0 : f = 0
    · subst h0
      have hv : dvalBE (0 :: fs) = dvalBE fs := by rw [dvalBE_cons]; simp
      rw [hv, List.length_cons]
      have hle : (Num.digits 10 (dvalBE fs)).length ≤ fs.length := by
        have := congrArg List.length (ih hf); simp at this; omega
      rw [show fs.length + 1 - (Num.digits 10 (dvalBE fs)).length =
        (fs.length - (Num.digits 10 (dvalBE fs)).length) + 1 by omega, List.replicate_succ,
        List.cons_append, ih hf]
    · rw [digits_dvalBE (f :: fs) h (by simpa using h0)]
      simp

/-- The bytes of `bc_out_num`'s base-10 branch for a nonzero normalised
number with integer digits `is` and fraction digits `fs`. -/
def out10 (neg : Bool) (is fs : List Nat) : List Nat :=
  (if neg then [45] else []) ++
    (if 1 < is.length ∨ is.head? ≠ some 0 then is.map Num.decChar else []) ++
    (if fs.length = 0 then [] else 46 :: fs.map Num.decChar)

theorem out10_chars (neg : Bool) (is fs : List Nat) (his : IsDigits is) (hfs : IsDigits fs)
    (hlen : 1 ≤ is.length) (hnorm : 1 < is.length → ∀ d ∈ is.head?, d ≠ 0)
    (hnz : dvalBE (is ++ fs) ≠ 0) :
    Num.outChars ⟨neg, dvalBE (is ++ fs), fs.length⟩ 10 = out10 neg is fs := by
  have hsplit : dvalBE (is ++ fs) = dvalBE is * 10 ^ fs.length + dvalBE fs := dvalBE_append _ _
  have hflt : dvalBE fs < 10 ^ fs.length := dvalBE_lt hfs
  have hp : 0 < 10 ^ fs.length := Nat.pow_pos (by decide)
  have hip : dvalBE (is ++ fs) / 10 ^ fs.length = dvalBE is := by
    rw [hsplit, Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hflt, Nat.zero_add]
  have hfp : dvalBE (is ++ fs) % 10 ^ fs.length = dvalBE fs := by
    rw [hsplit, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hflt]
  simp only [Num.outChars, Num.isZero, Num.intPart, beq_iff_eq, hnz, ite_false, hip, hfp,
    ite_true, out10]
  congr 1
  · congr 1
    -- integer digits
    cases is with
    | nil => simp at hlen
    | cons x xs =>
      cases xs with
      | nil =>
        have hx : x < 10 := his x (by simp)
        by_cases hx0 : x = 0
        · subst hx0; simp [dvalBE]
        · have : dvalBE [x] = x := by simp [dvalBE]
          rw [this]
          have hd := digits_dvalBE [x] his (by simpa using hx0)
          rw [this] at hd
          simp [hx0, hd]
      | cons y ys =>
        have hx0 : x ≠ 0 := hnorm (by simp) x (by simp)
        have hd := digits_dvalBE (x :: y :: ys) his (by simpa using hx0)
        have hv : dvalBE (x :: y :: ys) ≠ 0 := by
          have := dvalBE_ge_top (ds := y :: ys) (Nat.pos_of_ne_zero hx0)
          have := Nat.pow_pos (n := (y :: ys).length) (show 0 < 10 by decide); omega
        simp [hv, hd]
  · -- fraction digits
    by_cases hs : fs.length = 0
    · simp [hs]
    · simp only [hs, ite_false]
      rw [frac_digits fs hfs]

end Dc.BcModel
