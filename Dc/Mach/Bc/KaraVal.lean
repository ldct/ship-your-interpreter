import Dc.Mach.Bc.ShiftAddSub

/-!
# The values of `_bc_shift_addsub`'s result

`shiftDs y w s sub` (the accumulator's digits after the call) holds
`y ± w·10^s` when no carry (borrow) leaves the accumulator; `noCarry_add` and
`noCarry_sub` supply `ShiftArgs.noCarry` from the values.
-/

namespace Dc.Mach

open Dc.BcModel

/-- `val`'s little-endian digits read `val`'s first `len` digits. -/
theorem dvalLE_valLE {w : NumRep} (hl : w.len ≤ w.ds.length) (h1 : 1 ≤ w.len) :
    dvalLE (valLE w) = dvalBE (w.ds.take w.len) := by
  obtain ⟨d, rest, he⟩ : ∃ d rest, w.ds.take w.len = d :: rest := by
    cases h : w.ds.take w.len with
    | nil =>
      have := congrArg List.length h
      simp only [List.length_take, List.length_nil] at this; omega
    | cons d rest => exact ⟨d, rest, rfl⟩
  have hlen : rest.length = w.len - 1 := by
    have := congrArg List.length he; simp at this; omega
  have hd : w.ds.getD 0 0 = d := by
    have : (w.ds.take w.len).getD 0 0 = w.ds.getD 0 0 := by
      simp [List.getD_eq_getElem?_getD, show 0 < w.len by omega]
    rw [← this, he]; rfl
  unfold valLE valCount
  rw [he, hd, List.reverse_cons]
  split
  · rename_i h0
    rw [List.take_left' (by simp [hlen]), dvalLE_reverse, dvalBE_cons, h0]; simp
  · rw [List.take_of_length_le (by simp; omega), ← List.reverse_cons, dvalLE_reverse]

/-- A digit list split at `k`. -/
theorem dvalBE_take_drop (ds : List Nat) (k : Nat) :
    dvalBE ds = dvalBE (ds.take k) * 10 ^ (ds.drop k).length + dvalBE (ds.drop k) := by
  conv => lhs; rw [← List.take_append_drop k ds]
  rw [dvalBE_append]

/-- **The shifted add**: the accumulator gains `val·10^s`. -/
theorem shiftDs_add {y w : NumRep} {s : Nat} (hyl : y.ds.length = y.len + y.scale)
    (hyd : IsDigits y.ds) (hfit : s + valCount w ≤ y.len + y.scale) (hwl : w.len ≤ w.ds.length)
    (hw1 : 1 ≤ w.len) (hwd : IsDigits w.ds) (hc : ripOut false (accLE y s) (valLE w) 0 = 0) :
    dvalBE (shiftDs y w s false) = dvalBE y.ds + dvalBE (w.ds.take w.len) * 10 ^ s := by
  have hvl := valLE_length hwl
  have ha : IsDigits (accLE y s) := fun d hd => hyd d (List.mem_of_mem_take (List.mem_reverse.mp hd))
  have hv : IsDigits (valLE w) := fun d hd =>
    hwd d (List.mem_of_mem_take (List.mem_reverse.mp (List.mem_of_mem_take hd)))
  have hal : (accLE y s).length = y.len + y.scale - s := by
    simp only [accLE, List.length_reverse, List.length_take]; omega
  have h := addRip_val (accLE y s) (valLE w) 0 ha hv (Nat.zero_le _) (by omega)
  simp only [ripOut, Bool.false_eq_true, ↓reduceIte] at hc
  rw [hc, Nat.mul_zero, Nat.add_zero, Nat.add_zero] at h
  have hdl : (y.ds.drop (y.len + y.scale - s)).length = s := by simp; omega
  unfold shiftDs ripOp
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [dvalBE_append, dvalBE_reverse, h, hdl, dvalLE_valLE hwl hw1,
    dvalBE_take_drop y.ds (y.len + y.scale - s), hdl]
  simp only [accLE, dvalLE_reverse]
  rw [Nat.add_mul]; omega

/-- **The shifted subtract**: the accumulator loses `val·10^s`. -/
theorem shiftDs_sub {y w : NumRep} {s : Nat} (hyl : y.ds.length = y.len + y.scale)
    (hyd : IsDigits y.ds) (hfit : s + valCount w ≤ y.len + y.scale) (hwl : w.len ≤ w.ds.length)
    (hw1 : 1 ≤ w.len) (hwd : IsDigits w.ds) (hc : ripOut true (accLE y s) (valLE w) 0 = 0) :
    dvalBE (shiftDs y w s true) + dvalBE (w.ds.take w.len) * 10 ^ s = dvalBE y.ds := by
  have hvl := valLE_length hwl
  have ha : IsDigits (accLE y s) := fun d hd => hyd d (List.mem_of_mem_take (List.mem_reverse.mp hd))
  have hv : IsDigits (valLE w) := fun d hd =>
    hwd d (List.mem_of_mem_take (List.mem_reverse.mp (List.mem_of_mem_take hd)))
  have hal : (accLE y s).length = y.len + y.scale - s := by
    simp only [accLE, List.length_reverse, List.length_take]; omega
  have h := subRip_val (accLE y s) (valLE w) 0 ha hv (Nat.zero_le _) (by omega)
  simp only [ripOut, ↓reduceIte] at hc
  rw [hc, Nat.mul_zero, Nat.add_zero, Nat.add_zero] at h
  have hdl : (y.ds.drop (y.len + y.scale - s)).length = s := by simp; omega
  unfold shiftDs ripOp
  simp only [↓reduceIte]
  have hacc : dvalLE (accLE y s) = dvalBE (y.ds.take (y.len + y.scale - s)) := by
    simp only [accLE, dvalLE_reverse]
  rw [dvalBE_append, dvalBE_reverse, hdl, dvalBE_take_drop y.ds (y.len + y.scale - s), hdl,
    ← dvalLE_valLE hwl hw1, ← hacc, ← h, Nat.add_mul]
  omega

/-- No carry leaves the accumulator when the sum fits. -/
theorem noCarry_add {y w : NumRep} {s : Nat} (hyl : y.ds.length = y.len + y.scale)
    (hyd : IsDigits y.ds) (hfit : s + valCount w ≤ y.len + y.scale) (hwl : w.len ≤ w.ds.length)
    (hw1 : 1 ≤ w.len) (hwd : IsDigits w.ds)
    (hlt : dvalBE y.ds + dvalBE (w.ds.take w.len) * 10 ^ s < 10 ^ (y.len + y.scale)) :
    ripOut false (accLE y s) (valLE w) 0 = 0 := by
  have hvl := valLE_length hwl
  have ha : IsDigits (accLE y s) := fun d hd => hyd d (List.mem_of_mem_take (List.mem_reverse.mp hd))
  have hv : IsDigits (valLE w) := fun d hd =>
    hwd d (List.mem_of_mem_take (List.mem_reverse.mp (List.mem_of_mem_take hd)))
  have hal : (accLE y s).length = y.len + y.scale - s := by
    simp only [accLE, List.length_reverse, List.length_take]; omega
  have h := addRip_val (accLE y s) (valLE w) 0 ha hv (Nat.zero_le _) (by omega)
  have hdl : (y.ds.drop (y.len + y.scale - s)).length = s := by simp; omega
  have hsp := dvalBE_take_drop y.ds (y.len + y.scale - s)
  rw [hdl] at hsp
  have hacc : dvalLE (accLE y s) = dvalBE (y.ds.take (y.len + y.scale - s)) := by
    simp only [accLE, dvalLE_reverse]
  rw [dvalLE_valLE hwl hw1, hal, hacc] at h
  have hpw : 10 ^ (y.len + y.scale) = 10 ^ (y.len + y.scale - s) * 10 ^ s := by
    rw [← Nat.pow_add]; congr 1; omega
  have hlt' : (dvalBE (y.ds.take (y.len + y.scale - s)) + dvalBE (w.ds.take w.len)) * 10 ^ s <
      10 ^ (y.len + y.scale - s) * 10 ^ s := by rw [Nat.add_mul, ← hpw]; omega
  have hlt'' := Nat.lt_of_mul_lt_mul_right hlt'
  simp only [ripOut, Bool.false_eq_true, ↓reduceIte]
  refine Nat.eq_zero_of_not_pos fun hp => ?_
  have : 10 ^ (y.len + y.scale - s) ≤ 10 ^ (y.len + y.scale - s) *
      addRipC (accLE y s) (valLE w) 0 := Nat.le_mul_of_pos_right _ hp
  omega

/-- No borrow leaves the accumulator when the subtrahend is at most it. -/
theorem noCarry_sub {y w : NumRep} {s : Nat} (hyl : y.ds.length = y.len + y.scale)
    (hyd : IsDigits y.ds) (hfit : s + valCount w ≤ y.len + y.scale) (hwl : w.len ≤ w.ds.length)
    (hw1 : 1 ≤ w.len) (hwd : IsDigits w.ds)
    (hle : dvalBE (w.ds.take w.len) * 10 ^ s ≤ dvalBE y.ds) :
    ripOut true (accLE y s) (valLE w) 0 = 0 := by
  have hvl := valLE_length hwl
  have ha : IsDigits (accLE y s) := fun d hd => hyd d (List.mem_of_mem_take (List.mem_reverse.mp hd))
  have hv : IsDigits (valLE w) := fun d hd =>
    hwd d (List.mem_of_mem_take (List.mem_reverse.mp (List.mem_of_mem_take hd)))
  have hal : (accLE y s).length = y.len + y.scale - s := by
    simp only [accLE, List.length_reverse, List.length_take]; omega
  have h := subRip_val (accLE y s) (valLE w) 0 ha hv (Nat.zero_le _) (by omega)
  have hd := dvalLE_lt (subRip_digits (accLE y s) (valLE w) 0 ha hv (Nat.zero_le _))
  rw [subRip_length, hal] at hd
  have hdl : (y.ds.drop (y.len + y.scale - s)).length = s := by simp; omega
  have hsp := dvalBE_take_drop y.ds (y.len + y.scale - s)
  rw [hdl] at hsp
  have hdlt := dvalLE_lt (ds := (y.ds.drop (y.len + y.scale - s)).reverse)
    (fun d hd => hyd d (List.mem_of_mem_drop (List.mem_reverse.mp hd)))
  rw [dvalLE_reverse, List.length_reverse, hdl] at hdlt
  have hacc : dvalLE (accLE y s) = dvalBE (y.ds.take (y.len + y.scale - s)) := by
    simp only [accLE, dvalLE_reverse]
  rw [dvalLE_valLE hwl hw1, hal, hacc] at h
  have hW : dvalBE (w.ds.take w.len) ≤ dvalBE (y.ds.take (y.len + y.scale - s)) := by
    have : dvalBE (w.ds.take w.len) * 10 ^ s < (dvalBE (y.ds.take (y.len + y.scale - s)) + 1) * 10 ^ s := by
      rw [Nat.add_mul]; omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  simp only [ripOut, ↓reduceIte]
  refine Nat.eq_zero_of_not_pos fun hp => ?_
  have : 10 ^ (y.len + y.scale - s) ≤ 10 ^ (y.len + y.scale - s) *
      subRipB (accLE y s) (valLE w) 0 := Nat.le_mul_of_pos_right _ hp
  omega

/-- The accumulator's digits after the call: as many, all digits. -/
theorem shiftDs_shape {y w : NumRep} {s : Nat} {sub : Bool} (hyl : y.ds.length = y.len + y.scale)
    (hyd : IsDigits y.ds) (hfit : s + valCount w ≤ y.len + y.scale) (hwd : IsDigits w.ds) :
    (shiftDs y w s sub).length = y.len + y.scale ∧ IsDigits (shiftDs y w s sub) := by
  have ha : IsDigits (accLE y s) := fun d hd => hyd d (List.mem_of_mem_take (List.mem_reverse.mp hd))
  have hv : IsDigits (valLE w) := fun d hd =>
    hwd d (List.mem_of_mem_take (List.mem_reverse.mp (List.mem_of_mem_take hd)))
  have hal : (accLE y s).length = y.len + y.scale - s := by
    simp only [accLE, List.length_reverse, List.length_take]; omega
  unfold shiftDs ripOp
  cases sub
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨by simp [addRip_length, hal]; omega, fun d hd => ?_⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact addRip_digits _ _ 0 ha hv (Nat.zero_le _) d (List.mem_reverse.mp hd)
    · exact hyd d (List.mem_of_mem_drop hd)
  · simp only [↓reduceIte]
    refine ⟨by simp [subRip_length, hal]; omega, fun d hd => ?_⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact subRip_digits _ _ 0 ha hv (Nat.zero_le _) d (List.mem_reverse.mp hd)
    · exact hyd d (List.mem_of_mem_drop hd)

end Dc.Mach
