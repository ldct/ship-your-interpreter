import Dc.BcModel.Mul

/-!
# `_one_mult`, `_bc_shift_addsub` and the Karatsuba step of `_bc_rec_mul`

- `oneMultLE d xs`: `_one_mult`'s product of the little-endian digits `xs`
  by the digit `d`; the last entry is the carry the C code writes in front.
- `addRip acc val c` / `subRip acc val b`: `_bc_shift_addsub`'s in-place
  loops from the shifted position (little-endian `acc` from there): the
  digit loop over `val`, then the carry (borrow) ripple, which stops at the
  first digit that absorbs it. `addRipC`/`subRipB` are the carry (borrow)
  left over past the end of `acc`; with a bound on the result they are zero.
- `karatsuba_add`/`karatsuba_sub`: the identity `_bc_rec_mul` assembles its
  product from (`u = u1 B + u0`, `v = v1 B + v0`, `m1 = u1 v1`,
  `m3 = u0 v0`, `m2 = |u1 - u0| |v0 - v1|`, added when `u1 - u0` and
  `v0 - v1` have the same sign, subtracted otherwise).
-/

namespace Dc.BcModel

/-! ## `_one_mult` -/

/-- `_one_mult`'s digits (little-endian), carry last. -/
def oneMultLE (d : Nat) (xs : List Nat) : List Nat := propLE (xs.map (d * ·)) 0

theorem dvalLE_map_mul (d : Nat) : ∀ xs : List Nat, dvalLE (xs.map (d * ·)) = d * dvalLE xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, dvalLE]
    rw [dvalLE_map_mul d xs, Nat.mul_add, Nat.mul_left_comm]

theorem oneMultLE_val (d : Nat) (xs : List Nat) : dvalLE (oneMultLE d xs) = d * dvalLE xs := by
  rw [oneMultLE, propLE_val, dvalLE_map_mul, Nat.add_zero]

theorem oneMultLE_length (d : Nat) (xs : List Nat) : (oneMultLE d xs).length = xs.length + 1 := by
  rw [oneMultLE, propLE_length, List.length_map]

/-! ## `_bc_shift_addsub` -/

/-- The addition loops: digits `acc + val + c` with carry, then the carry
ripple until it is absorbed. -/
def addRip : List Nat → List Nat → Nat → List Nat
  | a :: as, v :: vs, c => if 9 < a + v + c then (a + v + c - 10) :: addRip as vs 1
                           else (a + v + c) :: addRip as vs 0
  | a :: as, [], c => if c = 0 then a :: as
                      else if 9 < a + c then (a + c - 10) :: addRip as [] 1 else (a + c) :: as
  | [], _, _ => []

/-- The carry left past the end of `acc`. -/
def addRipC : List Nat → List Nat → Nat → Nat
  | a :: as, v :: vs, c => if 9 < a + v + c then addRipC as vs 1 else addRipC as vs 0
  | a :: as, [], c => if c = 0 then 0 else if 9 < a + c then addRipC as [] 1 else 0
  | [], _, c => c

theorem addRip_val : ∀ (acc val : List Nat) (c : Nat), IsDigits acc → IsDigits val → c ≤ 1 →
    val.length ≤ acc.length →
    dvalLE (addRip acc val c) + 10 ^ acc.length * addRipC acc val c = dvalLE acc + dvalLE val + c
  | [], [], c, _, _, _, _ => by simp [addRip, addRipC, dvalLE]
  | [], _ :: _, _, _, _, _, h => by simp at h
  | a :: as, v :: vs, c, ha, hv, hc, hl => by
    have h1 := ha a List.mem_cons_self
    have h2 := hv v List.mem_cons_self
    have ha' : IsDigits as := fun e he => ha e (List.mem_cons_of_mem _ he)
    have hv' : IsDigits vs := fun e he => hv e (List.mem_cons_of_mem _ he)
    have hl' : vs.length ≤ as.length := by simpa using hl
    simp only [addRip, addRipC]
    split
    · have ih := addRip_val as vs 1 ha' hv' (by decide) hl'
      simp only [dvalLE, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (10 ^ as.length) 10, Nat.mul_assoc]
      omega
    · have ih := addRip_val as vs 0 ha' hv' (by decide) hl'
      simp only [dvalLE, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (10 ^ as.length) 10, Nat.mul_assoc]
      omega
  | a :: as, [], c, ha, hv, hc, hl => by
    have h1 := ha a List.mem_cons_self
    have ha' : IsDigits as := fun e he => ha e (List.mem_cons_of_mem _ he)
    simp only [addRip, addRipC]
    split
    · subst c; simp [dvalLE]
    · split
      · have ih := addRip_val as [] 1 ha' hv (by decide) (Nat.zero_le _)
        simp only [dvalLE, List.length_cons, Nat.pow_succ] at ih ⊢
        rw [Nat.mul_comm (10 ^ as.length) 10, Nat.mul_assoc]
        omega
      · simp only [dvalLE]; omega

theorem addRip_length : ∀ (acc val : List Nat) (c : Nat), (addRip acc val c).length = acc.length
  | [], _, _ => by simp [addRip]
  | a :: as, v :: vs, c => by
    simp only [addRip]; split <;> simp only [List.length_cons] <;> rw [addRip_length as vs]
  | a :: as, [], c => by
    simp only [addRip]; split
    · rfl
    · split
      · simp only [List.length_cons]; rw [addRip_length as []]
      · rfl

theorem addRip_digits : ∀ (acc val : List Nat) (c : Nat), IsDigits acc → IsDigits val → c ≤ 1 →
    IsDigits (addRip acc val c)
  | [], _, _, _, _, _ => by intro d hd; simp [addRip] at hd
  | a :: as, v :: vs, c, ha, hv, hc => by
    have h1 := ha a List.mem_cons_self
    have h2 := hv v List.mem_cons_self
    have ha' : IsDigits as := fun e he => ha e (List.mem_cons_of_mem _ he)
    have hv' : IsDigits vs := fun e he => hv e (List.mem_cons_of_mem _ he)
    simp only [addRip]
    split
    · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · exact addRip_digits as vs 1 ha' hv' (by decide) d hd
    · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · exact addRip_digits as vs 0 ha' hv' (by decide) d hd
  | a :: as, [], c, ha, hv, hc => by
    have h1 := ha a List.mem_cons_self
    have ha' : IsDigits as := fun e he => ha e (List.mem_cons_of_mem _ he)
    simp only [addRip]
    split
    · exact ha
    · split
      · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
        · omega
        · exact addRip_digits as [] 1 ha' hv (by decide) d hd
      · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
        · omega
        · exact ha' d hd

/-- With the sum below `10 ^ acc.length`, no carry is lost. -/
theorem addRip_exact {acc val : List Nat} {c : Nat} (ha : IsDigits acc) (hv : IsDigits val)
    (hc : c ≤ 1) (hl : val.length ≤ acc.length)
    (hb : dvalLE acc + dvalLE val + c < 10 ^ acc.length) :
    dvalLE (addRip acc val c) = dvalLE acc + dvalLE val + c := by
  have h := addRip_val acc val c ha hv hc hl
  have : addRipC acc val c = 0 := by
    refine Nat.eq_zero_of_not_pos fun hp => ?_
    have : 10 ^ acc.length ≤ 10 ^ acc.length * addRipC acc val c := Nat.le_mul_of_pos_right _ hp
    omega
  rw [this, Nat.mul_zero, Nat.add_zero] at h
  exact h

/-- The subtraction loops: digits `acc - val - b` with borrow, then the borrow
ripple until it is absorbed. -/
def subRip : List Nat → List Nat → Nat → List Nat
  | a :: as, v :: vs, b => if a < v + b then (a + 10 - v - b) :: subRip as vs 1
                           else (a - v - b) :: subRip as vs 0
  | a :: as, [], b => if b = 0 then a :: as
                      else if a < b then (a + 10 - b) :: subRip as [] 1 else (a - b) :: as
  | [], _, _ => []

/-- The borrow left past the end of `acc`. -/
def subRipB : List Nat → List Nat → Nat → Nat
  | a :: as, v :: vs, b => if a < v + b then subRipB as vs 1 else subRipB as vs 0
  | a :: as, [], b => if b = 0 then 0 else if a < b then subRipB as [] 1 else 0
  | [], _, b => b

theorem subRip_val : ∀ (acc val : List Nat) (b : Nat), IsDigits acc → IsDigits val → b ≤ 1 →
    val.length ≤ acc.length →
    dvalLE (subRip acc val b) + dvalLE val + b = dvalLE acc + 10 ^ acc.length * subRipB acc val b
  | [], [], b, _, _, _, _ => by simp [subRip, subRipB, dvalLE]
  | [], _ :: _, _, _, _, _, h => by simp at h
  | a :: as, v :: vs, b, ha, hv, hb, hl => by
    have h1 := ha a List.mem_cons_self
    have h2 := hv v List.mem_cons_self
    have ha' : IsDigits as := fun e he => ha e (List.mem_cons_of_mem _ he)
    have hv' : IsDigits vs := fun e he => hv e (List.mem_cons_of_mem _ he)
    have hl' : vs.length ≤ as.length := by simpa using hl
    simp only [subRip, subRipB]
    split
    · have ih := subRip_val as vs 1 ha' hv' (by decide) hl'
      simp only [dvalLE, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (10 ^ as.length) 10, Nat.mul_assoc]
      omega
    · have ih := subRip_val as vs 0 ha' hv' (by decide) hl'
      simp only [dvalLE, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (10 ^ as.length) 10, Nat.mul_assoc]
      omega
  | a :: as, [], b, ha, hv, hb, hl => by
    have h1 := ha a List.mem_cons_self
    have ha' : IsDigits as := fun e he => ha e (List.mem_cons_of_mem _ he)
    simp only [subRip, subRipB]
    split
    · subst b; simp [dvalLE]
    · split
      · have ih := subRip_val as [] 1 ha' hv (by decide) (Nat.zero_le _)
        simp only [dvalLE, List.length_cons, Nat.pow_succ] at ih ⊢
        rw [Nat.mul_comm (10 ^ as.length) 10, Nat.mul_assoc]
        omega
      · simp only [dvalLE]; omega

theorem subRip_length : ∀ (acc val : List Nat) (b : Nat), (subRip acc val b).length = acc.length
  | [], _, _ => by simp [subRip]
  | a :: as, v :: vs, b => by
    simp only [subRip]; split <;> simp only [List.length_cons] <;> rw [subRip_length as vs]
  | a :: as, [], b => by
    simp only [subRip]; split
    · rfl
    · split
      · simp only [List.length_cons]; rw [subRip_length as []]
      · rfl

theorem subRip_digits : ∀ (acc val : List Nat) (b : Nat), IsDigits acc → IsDigits val → b ≤ 1 →
    IsDigits (subRip acc val b)
  | [], _, _, _, _, _ => by intro d hd; simp [subRip] at hd
  | a :: as, v :: vs, b, ha, hv, hb => by
    have h1 := ha a List.mem_cons_self
    have h2 := hv v List.mem_cons_self
    have ha' : IsDigits as := fun e he => ha e (List.mem_cons_of_mem _ he)
    have hv' : IsDigits vs := fun e he => hv e (List.mem_cons_of_mem _ he)
    simp only [subRip]
    split
    · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · exact subRip_digits as vs 1 ha' hv' (by decide) d hd
    · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · exact subRip_digits as vs 0 ha' hv' (by decide) d hd
  | a :: as, [], b, ha, hv, hb => by
    have h1 := ha a List.mem_cons_self
    have ha' : IsDigits as := fun e he => ha e (List.mem_cons_of_mem _ he)
    simp only [subRip]
    split
    · exact ha
    · split
      · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
        · omega
        · exact subRip_digits as [] 1 ha' hv (by decide) d hd
      · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
        · omega
        · exact ha' d hd

/-- With the subtrahend at most the accumulator, no borrow is lost. -/
theorem subRip_exact {acc val : List Nat} {b : Nat} (ha : IsDigits acc) (hv : IsDigits val)
    (hb : b ≤ 1) (hl : val.length ≤ acc.length) (hle : dvalLE val + b ≤ dvalLE acc) :
    dvalLE (subRip acc val b) = dvalLE acc - dvalLE val - b := by
  have h := subRip_val acc val b ha hv hb hl
  have hd := dvalLE_lt (subRip_digits acc val b ha hv hb)
  rw [subRip_length] at hd
  have : subRipB acc val b = 0 := by
    refine Nat.eq_zero_of_not_pos fun hp => ?_
    have : 10 ^ acc.length ≤ 10 ^ acc.length * subRipB acc val b := Nat.le_mul_of_pos_right _ hp
    omega
  rw [this, Nat.mul_zero, Nat.add_zero] at h
  omega

/-! ## The Karatsuba identity -/

/-- `u1 - u0` and `v0 - v1` have the same sign (`m2` is added). -/
abbrev kSame (u1 u0 v1 v0 : Nat) : Prop := (u1 < u0 ↔ v0 < v1)

/-- `|x - y|`. -/
abbrev dist (x y : Nat) : Nat := if x < y then y - x else x - y

theorem karatsuba_add {u1 u0 v1 v0 B : Nat} (h : kSame u1 u0 v1 v0) :
    (u1 * B + u0) * (v1 * B + v0) =
      u1 * v1 * B * B + u1 * v1 * B + u0 * v0 * B + u0 * v0 + dist u1 u0 * dist v0 v1 * B := by
  simp only [dist]
  by_cases h1 : u1 < u0
  · have h2 := h.mp h1
    obtain ⟨a, rfl⟩ : ∃ a, u0 = u1 + a := ⟨u0 - u1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v1 = v0 + b := ⟨v1 - v0, by omega⟩
    simp only [h1, h2, ite_true, Nat.add_sub_cancel_left]
    grind
  · have h2 : ¬ v0 < v1 := fun h' => h1 (h.mpr h')
    obtain ⟨a, rfl⟩ : ∃ a, u1 = u0 + a := ⟨u1 - u0, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v0 = v1 + b := ⟨v0 - v1, by omega⟩
    simp only [h1, h2, ite_false, Nat.add_sub_cancel_left]
    grind

theorem karatsuba_sub {u1 u0 v1 v0 B : Nat} (h : ¬ kSame u1 u0 v1 v0) :
    (u1 * B + u0) * (v1 * B + v0) + dist u1 u0 * dist v0 v1 * B =
      u1 * v1 * B * B + u1 * v1 * B + u0 * v0 * B + u0 * v0 := by
  simp only [dist]
  by_cases h1 : u1 < u0
  · have h2 : ¬ v0 < v1 := fun h' => h ⟨fun _ => h', fun _ => h1⟩
    obtain ⟨a, rfl⟩ : ∃ a, u0 = u1 + a := ⟨u0 - u1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v0 = v1 + b := ⟨v0 - v1, by omega⟩
    simp only [h1, h2, ite_true, ite_false, Nat.add_sub_cancel_left]
    grind
  · have h2 : v0 < v1 := Classical.byContradiction fun h' =>
      h ⟨fun h'' => absurd h'' h1, fun h'' => absurd h'' h'⟩
    obtain ⟨a, rfl⟩ : ∃ a, u1 = u0 + a := ⟨u1 - u0, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v1 = v0 + b := ⟨v1 - v0, by omega⟩
    simp only [h1, h2, ite_true, ite_false, Nat.add_sub_cancel_left]
    grind

end Dc.BcModel
