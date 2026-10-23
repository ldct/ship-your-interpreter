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

/-! ## The accumulator never overflows

`_bc_rec_mul` adds `m1·B²`, `m1·B`, `m3·B`, `m3` into a product array of
`ulen + vlen + 1` digits before it adds or subtracts `m2·B`
(`B = 10^n`, `n = (max ulen vlen + 1) / 2`). `kara_bound` bounds that
partial sum by the array's capacity, so no `_bc_shift_addsub` carries out of
the array. -/

theorem sq_mul_lt {B x y : Nat} (hx : x < B) (hy : 0 < y) : x * y * B + x * y < B * B * y := by
  obtain ⟨c, rfl⟩ : ∃ c, B = x + 1 + c := ⟨B - x - 1, by omega⟩
  grind

theorem cube_lt {B x y : Nat} (hx : x < B) (hy : y < B) : x * y * B + x * y < B * B * B := by
  rcases Nat.eq_zero_or_pos y with rfl | hy0
  · simp; exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  exact Nat.lt_of_lt_of_le (sq_mul_lt hx hy0) (Nat.mul_le_mul_left _ (Nat.le_of_lt hy))

theorem pow_ul_pos {x ul : Nat} (hx0 : 0 < x) (hx : x < 10 ^ ul) : 1 ≤ ul := by
  rcases ul with _ | ul
  · simp at hx; omega
  · omega

/-- The two products of the low (or only) halves. -/
theorem half_bound {n ul vl x y : Nat} (hx : x < 10 ^ ul) (hxB : x < 10 ^ n) (hy : y < 10 ^ vl)
    (hyB : y < 10 ^ n) (hmax : 2 * n ≤ max ul vl + 1) :
    x * y * 10 ^ n + x * y < 10 ^ (ul + vl + 1) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · simp; exact Nat.pow_pos (by decide)
  rcases Nat.eq_zero_or_pos y with rfl | hy0
  · simp; exact Nat.pow_pos (by decide)
  have hul := pow_ul_pos hx0 hx
  have hvl := pow_ul_pos hy0 hy
  have hBB : 10 ^ n * 10 ^ n = 10 ^ (2 * n) := by rw [← Nat.pow_add]; congr 1; omega
  by_cases hv : vl ≤ n
  · have h1 := sq_mul_lt hxB hy0
    rw [hBB] at h1
    have h2 : 10 ^ n * 10 ^ n * y < 10 ^ n * 10 ^ n * 10 ^ vl :=
      Nat.mul_lt_mul_of_pos_left hy (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))
    rw [hBB, ← Nat.pow_add] at h2
    have h3 : 10 ^ (2 * n + vl) ≤ 10 ^ (ul + vl + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  by_cases hu : ul ≤ n
  · have h1 := sq_mul_lt hyB hx0
    rw [Nat.mul_comm y x, hBB] at h1
    have h2 : 10 ^ n * 10 ^ n * x < 10 ^ n * 10 ^ n * 10 ^ ul :=
      Nat.mul_lt_mul_of_pos_left hx (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))
    rw [hBB, ← Nat.pow_add] at h2
    have h3 : 10 ^ (2 * n + ul) ≤ 10 ^ (ul + vl + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h1 := cube_lt hxB hyB
  rw [hBB, ← Nat.pow_add] at h1
  have h3 : 10 ^ (2 * n + n) ≤ 10 ^ (ul + vl + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The partial sum `m1·B² + m1·B + m3·B + m3` fits in `ulen + vlen + 1`
digits. -/
theorem kara_bound {n ul vl u1 u0 v1 v0 : Nat} (hu : u1 * 10 ^ n + u0 < 10 ^ ul)
    (hv : v1 * 10 ^ n + v0 < 10 ^ vl) (hu0 : u0 < 10 ^ n) (hv0 : v0 < 10 ^ n)
    (hul : ul ≤ 2 * n) (hvl : vl ≤ 2 * n) (hmax : 2 * n ≤ max ul vl + 1) :
    u1 * v1 * 10 ^ n * 10 ^ n + u1 * v1 * 10 ^ n + u0 * v0 * 10 ^ n + u0 * v0 <
      10 ^ (ul + vl + 1) := by
  have hBpos : 0 < 10 ^ n := Nat.pow_pos (by decide)
  have hBB : 10 ^ n * 10 ^ n = 10 ^ (2 * n) := by rw [← Nat.pow_add]; congr 1; omega
  by_cases hu1 : u1 = 0
  · subst hu1; simp only [Nat.zero_mul, Nat.zero_add] at hu ⊢
    exact half_bound hu hu0 (by omega) hv0 hmax
  by_cases hv1 : v1 = 0
  · subst hv1; simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add] at hv ⊢
    exact half_bound (by omega) hu0 hv hv0 hmax
  -- both high halves are nonzero: both lengths exceed `n`
  have hB1 : 10 ^ n ≤ u1 * 10 ^ n := Nat.le_mul_of_pos_left _ (by omega)
  have hB2 : 10 ^ n ≤ v1 * 10 ^ n := Nat.le_mul_of_pos_left _ (by omega)
  have hnu : n < ul := Nat.lt_of_not_le fun h => by
    have : 10 ^ ul ≤ 10 ^ n := Nat.pow_le_pow_right (by decide) h
    omega
  have hnv : n < vl := Nat.lt_of_not_le fun h => by
    have : 10 ^ vl ≤ 10 ^ n := Nat.pow_le_pow_right (by decide) h
    omega
  -- `u1 < B`
  have hu1B : u1 < 10 ^ n := by
    have h1 : u1 * 10 ^ n < 10 ^ n * 10 ^ n := by
      rw [hBB]; exact Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) hul)
    exact Nat.lt_of_mul_lt_mul_right h1
  have hv1B : v1 < 10 ^ n := by
    have h1 : v1 * 10 ^ n < 10 ^ n * 10 ^ n := by
      rw [hBB]; exact Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) hvl)
    exact Nat.lt_of_mul_lt_mul_right h1
  have hd1 : dist u1 u0 < 10 ^ n := by simp only [dist]; split <;> omega
  have hd2 : dist v0 v1 < 10 ^ n := by simp only [dist]; split <;> omega
  -- `uv < 10^(ul+vl)` and `|d1||d2|B < B³ ≤ 10^(ul+vl)`
  have huv : (u1 * 10 ^ n + u0) * (v1 * 10 ^ n + v0) < 10 ^ ul * 10 ^ vl :=
    Nat.mul_lt_mul_of_lt_of_le hu (Nat.le_of_lt hv) (Nat.pow_pos (by decide))
  have hdd : dist u1 u0 * dist v0 v1 * 10 ^ n < 10 ^ n * 10 ^ n * 10 ^ n :=
    Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_lt_of_le hd1 (Nat.le_of_lt hd2) hBpos) hBpos
  rw [hBB, ← Nat.pow_add] at hdd
  rw [← Nat.pow_add] at huv
  have h3 : 10 ^ (2 * n + n) ≤ 10 ^ (ul + vl) := Nat.pow_le_pow_right (by decide) (by omega)
  have h4 : 10 ^ (ul + vl + 1) = 10 * 10 ^ (ul + vl) := by rw [Nat.pow_succ, Nat.mul_comm]
  by_cases hk : kSame u1 u0 v1 v0
  · have := karatsuba_add (B := 10 ^ n) hk
    omega
  · have := karatsuba_sub (B := 10 ^ n) hk
    omega

end Dc.BcModel
