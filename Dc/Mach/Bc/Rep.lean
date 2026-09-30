import Dc.Mach.Malloc
import VsaIris.Vsa.Stdout.Mem
import Dc.Num

/-!
# `bc_num` in memory (M3)

`lib/number.c`'s `bc_struct`, as `bc_new_num` lays it out (40 bytes):

| offset | field | load |
| --- | --- | --- |
| 0 | `n_sign` (`PLUS` 0, `MINUS` 1) | `lw` |
| 4 | `n_len` (integer digits) | `lw` |
| 8 | `n_scale` (fraction digits) | `lw` |
| 12 | `n_refs` | `lw` |
| 16 | `n_next` (free-list link) | `ld` |
| 24 | `n_ptr` (the `malloc`ed digit buffer) | `ld` |
| 32 | `n_value` (the first digit, inside `n_ptr`'s buffer) | `ld` |

The `n_len + n_scale` digits `0..9` at `n_value`, most significant first.

- `NumRep`: the machine-level description of one number object (struct
  address, buffer, value pointer, sign, lengths, reference count, digits);
  `NumRep.num` the `Dc.Num` it denotes.
- `NumAt Mt o`: memory `Mt` holds `o`. `NumAt.frame`: it survives any memory
  agreeing on the footprint `NumRep.Foot` (the struct and the digits).
- `NumRep.Norm`: no leading zero (`n_len = 1` or a nonzero first digit), the
  form every `bc_num` result has after `_bc_rm_leading_zeros`;
  `NumRep.rmLeadingZeros` is that function on representations.
- Digit arithmetic: `dval` (the value of a digit list), `dval_append`,
  `dval_lt`, `compare_dval_first_diff` (equal-length digit lists compare as
  their first differing digit).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Globals of `lib/number.c` (`.bss`) -/

/-- `_bc_Free_list`. -/
abbrev bcFreeAddr : Nat := 0x8001cdb0
/-- `_two_`. -/
abbrev twoAddr : Nat := 0x8001cdb8
/-- `_one_`. -/
abbrev oneAddr : Nat := 0x8001cdc0
/-- `_zero_`. -/
abbrev zeroAddr : Nat := 0x8001cdc8

/-! ## Digit lists -/

/-- The value of a big-endian decimal digit list. -/
def dval (ds : List Nat) : Nat := ds.foldl (fun a d => 10 * a + d) 0

theorem foldl_dval (a : Nat) : ∀ ds : List Nat,
    ds.foldl (fun a d => 10 * a + d) a = a * 10 ^ ds.length + dval ds
  | [] => by simp [dval]
  | d :: ds => by
    simp only [List.foldl_cons, List.length_cons, dval]
    rw [foldl_dval, foldl_dval (10 * 0 + d)]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.pow_succ]
    have : 10 * a * 10 ^ ds.length = a * (10 ^ ds.length * 10) := by
      rw [Nat.mul_comm 10 a, Nat.mul_assoc, Nat.mul_comm 10]
    rw [Nat.add_mul]; omega

@[simp] theorem dval_nil : dval [] = 0 := rfl

theorem dval_cons (d : Nat) (ds : List Nat) : dval (d :: ds) = d * 10 ^ ds.length + dval ds := by
  simp only [dval, List.foldl_cons, Nat.mul_zero, Nat.zero_add]
  exact foldl_dval d ds

theorem dval_append (xs ys : List Nat) : dval (xs ++ ys) = dval xs * 10 ^ ys.length + dval ys := by
  simp only [dval, List.foldl_append]
  exact foldl_dval _ ys

theorem dval_snoc (xs : List Nat) (d : Nat) : dval (xs ++ [d]) = 10 * dval xs + d := by
  rw [dval_append]; simp [dval, Nat.mul_comm]

theorem dval_replicate_zero : ∀ k : Nat, dval (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, dval_cons, dval_replicate_zero k]; simp

/-- Digits are below ten. -/
abbrev Digits (ds : List Nat) : Prop := ∀ d ∈ ds, d < 10

theorem dval_lt : ∀ {ds : List Nat}, Digits ds → dval ds < 10 ^ ds.length
  | [], _ => by simp
  | d :: ds, h => by
    rw [dval_cons, List.length_cons, Nat.pow_succ]
    have h1 := h d List.mem_cons_self
    have h2 := dval_lt (fun e he => h e (List.mem_cons_of_mem _ he))
    have : d * 10 ^ ds.length + dval ds < (d + 1) * 10 ^ ds.length := by rw [Nat.add_mul]; omega
    have : (d + 1) * 10 ^ ds.length ≤ 10 ^ ds.length * 10 := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    omega

theorem dval_ge_head {d : Nat} {ds : List Nat} : d * 10 ^ ds.length ≤ dval (d :: ds) := by
  rw [dval_cons]; omega

theorem compare_add_left' (c a b : Nat) : compare (c + a) (c + b) = compare a b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (by omega)]
  · subst h; rw [Nat.compare_eq_eq.2 rfl, Nat.compare_eq_eq.2 rfl]
  · rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (by omega)]

/-- Equal-length digit lists compare as their first differing digit. -/
theorem compare_dval_first_diff : ∀ (i : Nat) {xs ys : List Nat},
    Digits xs → Digits ys → xs.length = ys.length → i < xs.length →
    (∀ j, j < i → xs.getD j 0 = ys.getD j 0) → xs.getD i 0 ≠ ys.getD i 0 →
    compare (dval xs) (dval ys) = compare (xs.getD i 0) (ys.getD i 0)
  | _, [], _, _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _, _ :: _, [], _, _, hl, _, _, _ => by simp at hl
  | 0, x :: xs, y :: ys, hx, hy, hl, _, _, hne => by
    simp only [List.getD_cons_zero] at hne ⊢
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [dval_cons, dval_cons, ← hl]
    have r1 := dval_lt (fun e he => hx e (List.mem_cons_of_mem _ he))
    have r2 := dval_lt (fun e he => hy e (List.mem_cons_of_mem _ he))
    rw [← hl] at r2
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : x * 10 ^ xs.length + dval xs < y * 10 ^ xs.length + dval ys := by
        have : (x + 1) * 10 ^ xs.length ≤ y * 10 ^ xs.length := Nat.mul_le_mul_right _ h
        rw [Nat.add_mul] at this; omega
      rw [Nat.compare_eq_lt.2 this, Nat.compare_eq_lt.2 h]
    · have : y * 10 ^ xs.length + dval ys < x * 10 ^ xs.length + dval xs := by
        have : (y + 1) * 10 ^ xs.length ≤ x * 10 ^ xs.length := Nat.mul_le_mul_right _ h
        rw [Nat.add_mul] at this; omega
      rw [Nat.compare_eq_gt.2 this, Nat.compare_eq_gt.2 h]
  | i + 1, x :: xs, y :: ys, hx, hy, hl, hi, heq, hne => by
    simp only [List.getD_cons_succ] at hne ⊢
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl hi
    have h0 : x = y := by simpa using heq 0 (by omega)
    subst h0
    rw [dval_cons, dval_cons, ← hl, compare_add_left',
      compare_dval_first_diff i (fun e he => hx e (List.mem_cons_of_mem _ he))
        (fun e he => hy e (List.mem_cons_of_mem _ he)) hl (by omega)
        (fun j hj => by simpa using heq (j + 1) (by omega)) hne]

/-- Lists agreeing at every index up to their common length are equal. -/
theorem list_ext_getD {xs ys : List Nat} (hl : xs.length = ys.length)
    (h : ∀ j, j < xs.length → xs.getD j 0 = ys.getD j 0) : xs = ys := by
  apply List.ext_getElem hl
  intro j h1 h2
  have := h j h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

/-- A digit list padded with zeros reads the same digits (`getD` defaults to 0). -/
theorem getD_pad (ds : List Nat) (k j : Nat) :
    (ds ++ List.replicate k 0).getD j 0 = ds.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : j < ds.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := ds) (by omega),
      List.getElem?_replicate]
    split <;> rfl

theorem digits_pad {ds : List Nat} (h : Digits ds) (k : Nat) : Digits (ds ++ List.replicate k 0) := by
  intro d hd
  rcases List.mem_append.1 hd with hd | hd
  · exact h d hd
  · rw [List.eq_of_mem_replicate hd]; omega

/-- A digit read with `getD` is a digit. -/
theorem getD_digit {ds : List Nat} (h : Digits ds) (j : Nat) : ds.getD j 0 < 10 := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : ds[j]? with
  | none => simp
  | some d => simpa using h d (List.mem_of_getElem? hj)

/-- A digit list is zero exactly when every digit is. -/
theorem dval_eq_zero_iff : ∀ ds : List Nat,
    dval ds = 0 ↔ ∀ j, j < ds.length → ds.getD j 0 = 0
  | [] => by simp
  | d :: ds => by
    rw [dval_cons]
    have hp : 0 < 10 ^ ds.length := Nat.pow_pos (by decide)
    constructor
    · intro h j hj
      have hd : d = 0 := by
        rcases Nat.eq_zero_or_pos d with e | e
        · exact e
        · have : 10 ^ ds.length ≤ d * 10 ^ ds.length := Nat.le_mul_of_pos_left _ e
          omega
      cases j with
      | zero => simpa using hd
      | succ j =>
        simp only [List.getD_cons_succ]
        exact (dval_eq_zero_iff ds).1 (by rw [hd] at h; simpa using h) j (by simp at hj; omega)
    · intro h
      have hd : d = 0 := by simpa using h 0 (by simp)
      have := (dval_eq_zero_iff ds).2 fun j hj => by simpa using h (j + 1) (by simp; omega)
      rw [hd, this]; simp

/-- A digit list is at most one exactly when every digit but the last is zero
and the last is at most one. -/
theorem dval_le_one_iff : ∀ ds : List Nat, ds ≠ [] →
    (dval ds ≤ 1 ↔ (∀ j, j + 1 < ds.length → ds.getD j 0 = 0) ∧ ds.getD (ds.length - 1) 0 ≤ 1)
  | [], h => absurd rfl h
  | [d], _ => by simp [dval_cons]
  | d :: e :: ds, _ => by
    rw [dval_cons]
    have ih := dval_le_one_iff (e :: ds) (by simp)
    have hp : 10 ≤ 10 ^ (e :: ds).length := by
      simp only [List.length_cons]
      exact Nat.le_self_pow (by omega) _
    constructor
    · intro h
      have hd : d = 0 := by
        rcases Nat.eq_zero_or_pos d with hz | hz
        · exact hz
        · have : 10 ^ (e :: ds).length ≤ d * 10 ^ (e :: ds).length := Nat.le_mul_of_pos_left _ hz
          omega
      rw [hd] at h
      have := ih.1 (by simpa using h)
      refine ⟨fun j hj => ?_, ?_⟩
      · cases j with
        | zero => simpa using hd
        | succ j => simpa using this.1 j (by simp at hj ⊢; omega)
      · simpa using this.2
    · rintro ⟨h1, h2⟩
      have hd : d = 0 := by simpa using h1 0 (by simp)
      have := ih.2 ⟨fun j hj => by simpa using h1 (j + 1) (by simp at hj ⊢; omega),
        by simpa using h2⟩
      rw [hd]; simpa using this

/-- Truncating the last `L - m` digits: the value of the first `m`. -/
theorem dval_div_take (ds : List Nat) (hd : Digits ds) (m : Nat) :
    dval ds / 10 ^ (ds.length - m) = dval (ds.take m) := by
  have e : ds = ds.take m ++ ds.drop m := (List.take_append_drop m ds).symm
  have hl : (ds.drop m).length = ds.length - m := List.length_drop ..
  have hlt : dval (ds.drop m) < 10 ^ (ds.length - m) := by
    rw [← hl]; exact dval_lt fun d h => hd d (List.mem_of_mem_drop h)
  rw [show dval ds = dval (ds.take m) * 10 ^ (ds.length - m) + dval (ds.drop m) by
    conv => lhs; rw [e]
    rw [dval_append, hl]]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- The value of a prefix grows with the prefix. -/
theorem dval_take_mono (ds : List Nat) {m m' : Nat} (h : m ≤ m') :
    dval (ds.take m) ≤ dval (ds.take m') := by
  have e : ds.take m' = ds.take m ++ (ds.take m').drop m :=
    (List.take_append_drop m (ds.take m')).symm.trans (by rw [List.take_take, Nat.min_eq_left h])
  rw [e, dval_append]
  have : 1 ≤ 10 ^ ((ds.take m').drop m).length := Nat.one_le_pow _ _ (by decide)
  have := Nat.le_mul_of_pos_right (dval (ds.take m)) this
  omega

/-- One more digit of a prefix. -/
theorem dval_take_succ (ds : List Nat) {m : Nat} (h : m < ds.length) :
    dval (ds.take (m + 1)) = 10 * dval (ds.take m) + ds.getD m 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, dval_snoc,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-! ## Number objects -/

/-- One `bc_num` object at the machine level. -/
structure NumRep where
  /-- the struct (40 bytes) -/
  p : Nat
  /-- `n_ptr`: the digit buffer `malloc` returned -/
  ptr : Nat
  /-- `n_value`: the first digit -/
  val : Nat
  neg : Bool
  len : Nat
  scale : Nat
  refs : Nat
  /-- the `len + scale` digits at `val` -/
  ds : List Nat

/-- The number an object denotes. -/
def NumRep.num (o : NumRep) : Dc.Num := ⟨o.neg, dval o.ds, o.scale⟩

/-- The `n_sign` word of a sign. -/
abbrev signWord (neg : Bool) : BitVec 64 := BitVec.ofNat 64 (if neg then 1 else 0)

/-- The address-independent shape of an object. -/
structure NumShape (o : NumRep) : Prop where
  dsLen : o.ds.length = o.len + o.scale
  dig : Digits o.ds
  lenPos : 1 ≤ o.len
  size : o.len + o.scale < 2 ^ 31
  refsLt : o.refs < 2 ^ 31
  pAl : o.p % 8 = 0
  pLo : heapStart ≤ o.p
  pHi : o.p + 40 ≤ heapEnd
  ptrLe : o.ptr ≤ o.val
  vLo : heapStart ≤ o.ptr
  vHi : o.val + o.len + o.scale ≤ heapEnd
  /-- the digit buffer is apart from the struct -/
  sep : o.val + o.len + o.scale ≤ o.p ∨ o.p + 40 ≤ o.ptr

/-- **Memory `Mt` holds the object `o`.** -/
structure NumAt (Mt : Mem) (o : NumRep) : Prop where
  shape : NumShape o
  sign : ldv .lw Mt o.p = signWord o.neg
  len : ldv .lw Mt (o.p + 4) = BitVec.ofNat 64 o.len
  scale : ldv .lw Mt (o.p + 8) = BitVec.ofNat 64 o.scale
  refs : ldv .lw Mt (o.p + 12) = BitVec.ofNat 64 o.refs
  ptr : ldv .ld Mt (o.p + 24) = BitVec.ofNat 64 o.ptr
  value : ldv .ld Mt (o.p + 32) = BitVec.ofNat 64 o.val
  digit : ∀ i, i < o.len + o.scale → imgM Mt (o.val + i) = BitVec.ofNat 8 (o.ds.getD i 0)

/-- No leading zero: `n_len = 1` or the first digit is nonzero. -/
def NumRep.Norm (o : NumRep) : Prop := o.len = 1 ∨ o.ds.getD 0 0 ≠ 0

/-- The bytes `NumAt` reads: the struct's fields and the digits. -/
def NumRep.Foot (o : NumRep) (a : Nat) : Prop :=
  (o.p ≤ a ∧ a < o.p + 40) ∨ (o.val ≤ a ∧ a < o.val + o.len + o.scale)

/-- A load depends only on its bytes. -/
theorem ldv_congr (k : MKind) {Mt Mt' : Mem} {a : Nat}
    (h : ∀ j, j < widthOfM k → imgM Mt' (a + j) = imgM Mt (a + j)) : ldv k Mt' a = ldv k Mt a := by
  unfold ldv bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  exact h j (List.mem_range.mp hj)

/-- **Frame**: an object survives any memory agreeing on its footprint. -/
theorem NumAt.frame {Mt Mt' : Mem} {o : NumRep} (h : NumAt Mt o)
    (hag : ∀ a, o.Foot a → imgM Mt' a = imgM Mt a) : NumAt Mt' o := by
  have hs := fun (off : Nat) (k : MKind) (hk : off + widthOfM k ≤ 40) =>
    ldv_congr (a := o.p + off) k (Mt := Mt) (Mt' := Mt') fun j hj =>
      hag _ (.inl ⟨by omega, by omega⟩)
  refine ⟨h.shape, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [← h.sign]; simpa using hs 0 .lw (by decide)
  · rw [← h.len]; exact hs 4 .lw (by decide)
  · rw [← h.scale]; exact hs 8 .lw (by decide)
  · rw [← h.refs]; exact hs 12 .lw (by decide)
  · rw [← h.ptr]; exact hs 24 .ld (by decide)
  · rw [← h.value]; exact hs 32 .ld (by decide)
  · rw [hag _ (.inr ⟨by omega, by omega⟩)]; exact h.digit i hi

/-- The footprint lies in the heap. -/
theorem NumAt.foot_heap {Mt : Mem} {o : NumRep} (h : NumAt Mt o) {a : Nat} (ha : o.Foot a) :
    heapStart ≤ a ∧ a < heapEnd := by
  have := h.shape.pLo; have := h.shape.pHi; have := h.shape.vLo; have := h.shape.vHi
  have := h.shape.ptrLe
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> omega

/-! ## Values of an object -/

theorem NumRep.num_mag (o : NumRep) : o.num.mag = dval o.ds := rfl
theorem NumRep.num_neg (o : NumRep) : o.num.neg = o.neg := rfl
theorem NumRep.num_scale (o : NumRep) : o.num.scale = o.scale := rfl

/-- The magnitude of a normalised object with `n_len > 1` has `n_len` integer
digits. -/
theorem NumRep.mag_ge {o : NumRep} (hs : NumShape o) (hn : o.Norm) (h1 : 1 < o.len) :
    10 ^ (o.len - 1 + o.scale) ≤ dval o.ds := by
  rcases hn with hn | hn
  · omega
  · match hds : o.ds, hs.dsLen with
    | [], hl => simp at hl; omega
    | d :: ds, hl =>
      rw [hds] at hn
      simp only [List.getD_cons_zero] at hn
      simp only [List.length_cons] at hl
      have : 10 ^ ds.length ≤ d * 10 ^ ds.length := Nat.le_mul_of_pos_left _ (by omega)
      have := dval_ge_head (d := d) (ds := ds)
      rw [show o.len - 1 + o.scale = ds.length by omega]; omega

theorem NumRep.mag_lt {o : NumRep} (hs : NumShape o) : dval o.ds < 10 ^ (o.len + o.scale) := by
  have := dval_lt hs.dig; rwa [hs.dsLen] at this

/-- The aligned magnitude is the value of the zero-padded digits. -/
theorem NumRep.align_eq (o : NumRep) (s : Nat) :
    o.num.align s = dval (o.ds ++ List.replicate (s - o.scale) 0) := by
  simp only [Dc.Num.align, NumRep.num, dval_append, dval_replicate_zero, List.length_replicate,
    Nat.add_zero]

/-! ## `_bc_rm_leading_zeros` on representations -/

/-- Dropping `k` leading zeros: `n_value` advances, `n_len` shrinks. -/
def NumRep.drop (o : NumRep) (k : Nat) : NumRep :=
  { o with val := o.val + k, len := o.len - k, ds := o.ds.drop k }

/-- The number of leading zeros `_bc_rm_leading_zeros` removes (it keeps at
least one integer digit). -/
def lzCount : Nat → List Nat → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, d :: ds => if d = 0 then lzCount n ds + 1 else 0

/-- `_bc_rm_leading_zeros`. -/
def NumRep.rmLeadingZeros (o : NumRep) : NumRep := o.drop (lzCount (o.len - 1) o.ds)

theorem dval_drop_zeros : ∀ (k : Nat) (ds : List Nat), (∀ j, j < k → ds.getD j 0 = 0) →
    dval (ds.drop k) = dval ds
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | k + 1, d :: ds, h => by
    have h0 : d = 0 := by simpa using h 0 (by omega)
    subst h0
    rw [List.drop_succ_cons, dval_drop_zeros k ds (fun j hj => by simpa using h (j + 1) (by omega)),
      dval_cons]
    simp

theorem lzCount_le : ∀ (n : Nat) (ds : List Nat), lzCount n ds ≤ n
  | 0, _ => Nat.le_refl _
  | _ + 1, [] => Nat.zero_le _
  | n + 1, d :: ds => by
    simp only [lzCount]; split
    · have := lzCount_le n ds; omega
    · omega

theorem lzCount_zeros : ∀ (n : Nat) (ds : List Nat) (j : Nat), j < lzCount n ds → ds.getD j 0 = 0
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d :: ds, j, h => by
    simp only [lzCount] at h; split at h
    · rename_i hd
      cases j with
      | zero => simpa using hd
      | succ j => simpa using lzCount_zeros n ds j (by omega)
    · exact absurd h (Nat.not_lt_zero _)

theorem lzCount_stop : ∀ (n : Nat) (ds : List Nat), n < ds.length →
    lzCount n ds = n ∨ ds.getD (lzCount n ds) 0 ≠ 0
  | 0, _, _ => .inl rfl
  | _ + 1, [], h => absurd h (Nat.not_lt_zero _)
  | n + 1, d :: ds, h => by
    simp only [lzCount]; split
    · simp only [List.length_cons] at h
      rcases lzCount_stop n ds (by omega) with e | e
      · exact .inl (by omega)
      · exact .inr (by simpa using e)
    · rename_i hd; exact .inr (by simpa using hd)

/-- `_bc_rm_leading_zeros` keeps the number and normalises. -/
theorem NumRep.rmLeadingZeros_spec {o : NumRep} (hs : o.ds.length = o.len + o.scale)
    (hl : 1 ≤ o.len) :
    o.rmLeadingZeros.num = o.num ∧ o.rmLeadingZeros.Norm ∧
      o.rmLeadingZeros.ds.length = o.rmLeadingZeros.len + o.rmLeadingZeros.scale ∧
      1 ≤ o.rmLeadingZeros.len := by
  have hle := lzCount_le (o.len - 1) o.ds
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [NumRep.rmLeadingZeros, NumRep.drop, NumRep.num]
    rw [dval_drop_zeros _ _ (lzCount_zeros _ _)]
  · simp only [NumRep.Norm, NumRep.rmLeadingZeros, NumRep.drop]
    rcases lzCount_stop (o.len - 1) o.ds (by omega) with e | e
    · exact .inl (by omega)
    · exact .inr (by rw [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero,
        ← List.getD_eq_getElem?_getD]; exact e)
  · simp only [NumRep.rmLeadingZeros, NumRep.drop, List.length_drop]; omega
  · simp only [NumRep.rmLeadingZeros, NumRep.drop]; omega

/-! ## Word encodings -/

theorem msb32_small {k : Nat} (hk : k < 2 ^ 31) : (BitVec.ofNat 32 k).msb = false := by
  rw [BitVec.msb_eq_decide]; simp; omega

/-- A small word, sign-extended. -/
theorem sext32_small {k : Nat} (hk : k < 2 ^ 31) :
    sign_extend (m := 64) (BitVec.ofNat 32 k) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  unfold sign_extend Sail.BitVec.signExtend
  rw [BitVec.toNat_signExtend]
  simp [msb32_small hk]
  omega

/-- A word load of a small value just stored. -/
theorem ldv_lw_hitN (Mt : Mem) {a b : Nat} {v : BitVec 64} {k : Nat} (h : a = b)
    (hv : v.toNat % 2 ^ 32 = k) (hk : k < 2 ^ 31) :
    ldv .lw (writeLog Mt [(b, 4, v)]) a = BitVec.ofNat 64 k := by
  rw [ldv_lw_hit Mt v h, hv]; exact sext32_small hk

/-- A small word's low 32 bits. -/
theorem toNat_ofNat_mod32 {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 64 k).toNat % 2 ^ 32 = k := by
  rw [BitVec.toNat_ofNat]; omega

/-- `sx32` of a small word. -/
theorem sx32_small {k : Nat} (hk : k < 2 ^ 31) : sx32 (BitVec.ofNat 64 k) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have : (BitVec.truncate 32 (BitVec.ofNat 64 k)) = BitVec.ofNat 32 k := by
    apply BitVec.eq_of_toNat_eq; simp
  simp only [sx32, this]
  rw [BitVec.toNat_signExtend]
  simp [msb32_small hk]
  omega

/-- A word load reads the value of its signed 32-bit word. -/
theorem sx32_toNat_mod (v : BitVec 64) : (sx32 v).toNat % 2 ^ 32 = v.toNat % 2 ^ 32 := by
  simp only [sx32, BitVec.toNat_signExtend, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  split <;> omega

end Dc.Mach
