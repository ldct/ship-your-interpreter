import Dc.Mach.Strlen

/-!
# Byte-level vocabulary for the libc specs

The shared shapes of the `dc-port/libc/libc.c` specs:

- `Keeps ks R' R`: every register outside `ks` is unchanged (the callee's
  clobber set); `Keeps.upd` extends it through a register write in `ks`.
- `OwnedBytes S a n`: `n` owned bytes at `a` in writable RAM above `tohost`.
- `Filled Mt Mt0 d n g`: `Mt` is `Mt0` with the `n` bytes at `d` replaced by
  `g 0, …, g (n - 1)` — the memory post of `memset`, `memcpy`, `strncpy`;
  `Filled.snoc` extends it by one byte store.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The registers outside `ks` are unchanged from `R` to `R'`. -/
def Keeps (ks : List Nat) (R' R : Nat → BitVec 64) : Prop :=
  ∀ z, z ∉ ks → R' z = R z

theorem Keeps.refl (ks : List Nat) (R : Nat → BitVec 64) : Keeps ks R R := fun _ _ => rfl

theorem Keeps.upd {ks : List Nat} {R R0 : Nat → BitVec 64} {k : Nat} (v : BitVec 64)
    (hk : k ∈ ks) (h : Keeps ks R R0) : Keeps ks (upd R k v) R0 := by
  intro z hz
  rw [upd_other _ _ (fun e => hz (by rw [e]; exact hk))]; exact h z hz

theorem Keeps.trans {ks : List Nat} {R2 R1 R0 : Nat → BitVec 64} (h2 : Keeps ks R2 R1)
    (h1 : Keeps ks R1 R0) : Keeps ks R2 R0 := fun z hz => (h2 z hz).trans (h1 z hz)

theorem Keeps.mono {ks ks' : List Nat} {R' R : Nat → BitVec 64} (h : Keeps ks R' R)
    (hs : ∀ z ∈ ks, z ∈ ks') : Keeps ks' R' R := fun z hz => h z fun hm => hz (hs z hm)

/-- A kept register reads its old value (`z ∉ ks` by `decide`). -/
theorem Keeps.get {ks : List Nat} {R' R : Nat → BitVec 64} (h : Keeps ks R' R) (z : Nat)
    (hz : z ∉ ks := by decide) : R' z = R z := h z hz

/-- Close `Keeps ks (upd … (upd R k v) …) R0` from `h : Keeps ks R R0`. -/
macro "keeps_tac " h:term : tactic =>
  `(tactic| ((repeat (refine Keeps.upd _ (by decide) ?_)); exact $h))

/-- `n` owned bytes at `a`, in writable RAM above the HTIF words. -/
structure OwnedBytes (S : Nat → Prop) (a n : Nat) : Prop where
  own : ∀ i, i < n → S (a + i)
  lo : tohostAddr + 16 ≤ a
  hi : a + n ≤ 0x88000000

theorem OwnedBytes.own' {S : Nat → Prop} {a n x : Nat} (h : OwnedBytes S a n) (h1 : a ≤ x)
    (h2 : x < a + n) : S x := by
  have := h.own (x - a) (by omega); rwa [Nat.add_sub_cancel' h1] at this

theorem OwnedCStr.own' {S : Nat → Prop} {Mt : Mem} {a len x : Nat} (h : OwnedCStr S Mt a len)
    (h1 : a ≤ x) (h2 : x ≤ a + len) : S x := by
  have := h.own (x - a) (by omega); rwa [Nat.add_sub_cancel' h1] at this

/-- `Mt` is `Mt0` with the `n` bytes at `d` replaced by `g 0, …, g (n-1)`. -/
structure Filled (Mt Mt0 : Mem) (d n : Nat) (g : Nat → BitVec 8) : Prop where
  fill : ∀ i, i < n → imgM Mt (d + i) = g i
  rest : ∀ a, a < d ∨ d + n ≤ a → imgM Mt a = imgM Mt0 a

theorem Filled.zero (Mt : Mem) (d : Nat) (g : Nat → BitVec 8) : Filled Mt Mt d 0 g :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

/-- A byte store's image at its address. -/
theorem imgM_sb (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgM (writeLog Mt [(a, 1, v)]) a = sbData v := by
  unfold imgM writeLog
  simp only [List.foldl, applyW, Std.ExtHashMap.getElem?_insert]
  simp

/-- A byte store of a zero-extended byte stores that byte. -/
theorem sbData_zext (b : BitVec 8) : sbData (zero_extend (m := 64) b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [sbData, Sail.BitVec.extractLsb]
  simp [zero_extend, Sail.BitVec.zeroExtend]
  omega

/-- A byte load's value. -/
theorem ldv_lbu (Mt : Mem) (a : Nat) : ldv .lbu Mt a = zero_extend (m := 64) (imgM Mt a) := by
  simp [ldv, bytesAt, bytesVal, widthOfM]

/-- A byte store of a loaded byte stores that byte. -/
theorem sbData_lbu (Mt : Mem) (a : Nat) : sbData (ldv .lbu Mt a) = imgM Mt a := by
  rw [ldv_lbu]; exact sbData_zext _

/-- One more byte stored at the end of a fill. -/
theorem Filled.snoc {Mt Mt0 : Mem} {d i : Nat} {g : Nat → BitVec 8} (h : Filled Mt Mt0 d i g)
    {A : Nat} (hA : A = d + i) {v : BitVec 64} (hv : sbData v = g i) :
    Filled (writeLog Mt [(A, 1, v)]) Mt0 d (i + 1) g where
  fill j hj := by
    by_cases hji : j = i
    · subst hji hA; rw [imgM_sb]; exact hv
    · rw [imgM_store_miss _ _ (by omega)]; exact h.fill j (by omega)
  rest a ha := by rw [imgM_store_miss _ _ (by omega)]; exact h.rest a (by omega)

/-- A one-byte access owns its byte. -/
theorem acc1 {S : Nat → Prop} {x : Nat} (h : S x) : ∀ b ∈ accAddrs x 1, S b := by
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  rw [List.mem_range.mp hj |> Nat.lt_one_iff.mp, Nat.add_zero]; exact h

theorem se12_fff : sign_extend (m := 64) (0xfff#12) = 0xffffffffffffffff#64 := by decide

theorem ofNat_toNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_ne_iff {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y ↔ x ≠ y := by
  constructor
  · intro h e; exact h (e ▸ rfl)
  · intro h e; apply h
    have := congrArg BitVec.toNat e
    rwa [ofNat_toNat_lt hx, ofNat_toNat_lt hy] at this

theorem ofNat_eq_zero_iff {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x = 0#64 ↔ x = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rwa [ofNat_toNat_lt hx] at this
  · rintro rfl; rfl

theorem ofNat_add_ofNat (x y : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]

theorem ofNat_sub_one {x : Nat} (hx : 1 ≤ x) :
    BitVec.ofNat 64 x + 0xffffffffffffffff#64 = BitVec.ofNat 64 (x - 1) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [← ofNat_add_ofNat, BitVec.add_assoc,
    show (BitVec.ofNat 64 1 + 0xffffffffffffffff#64 : BitVec 64) = 0#64 by decide,
    BitVec.add_zero, Nat.add_sub_cancel]

theorem toNat_ofNat_m1 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 64) :
    (BitVec.ofNat 64 (x + 18446744073709551615)).toNat = x - 1 := by
  rw [BitVec.toNat_ofNat]; omega

theorem se12_ff : sign_extend (m := 64) (0x0ff#12) = 255#64 := by decide

theorem toNat_zext8 (b : BitVec 8) : (zero_extend (m := 64) b).toNat = b.toNat := by
  have := b.isLt
  simp [zero_extend, Sail.BitVec.zeroExtend]
  omega

theorem toNat_and255 (x : BitVec 64) : (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

theorem toNat_setWidth8 (x : BitVec 64) : (x.setWidth 8).toNat = x.toNat % 256 := by
  simp [BitVec.toNat_setWidth]

/-- The low byte of a register. -/
abbrev lo8 (x : BitVec 64) : BitVec 8 := x.setWidth 8

theorem sbData_eq (x : BitVec 64) : sbData x = lo8 x := by
  apply BitVec.eq_of_toNat_eq
  simp [sbData, Sail.BitVec.extractLsb, BitVec.toNat_setWidth]

/-- A loaded byte against a masked register (`zext.b` then `beq`/`bne`). -/
theorem zext_eq_and255 (b : BitVec 8) (x : BitVec 64) :
    zero_extend (m := 64) b = x &&& 255#64 ↔ b = lo8 x := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    rw [toNat_zext8, toNat_and255] at this
    rw [toNat_setWidth8]; exact this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [toNat_zext8, toNat_and255, h, toNat_setWidth8]

theorem zext8_eq_zero (b : BitVec 8) : zero_extend (m := 64) b = 0#64 ↔ b = 0#8 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    rw [toNat_zext8] at this; exact this
  · rintro rfl; rfl

/-- `dc_simp [hs…]`: register lookups at literal registers, the register
hypotheses `hs`, literal immediates, and `BitVec.ofNat` address arithmetic
(bounds by `omega`). -/
macro "dc_simp" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := omega) only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
    se12_zero, se12_one, se12_fff, se12_ff, BitVec.add_zero, ofNat_add_ofNat, ofNat_toNat_lt,
    toNat_ofNat_m1, Nat.add_sub_cancel, Nat.add_zero, ldv_lbu, $ts,*] $(loc)?)

/-- A load's or store's address side condition (`LdOK`, `StOKb`, `StOK`) by `omega`. -/
macro "dc_addr" : tactic => `(tactic| (simp only [LdOK, StOKb, StOK]; omega))

/-- A one-byte access to an owned byte of `h` (`OwnedBytes`/`OwnedCStr`). -/
macro "dc_own " h:term : tactic => `(tactic| (refine acc1 (($h).own' ?_ ?_) <;> omega))

/-- The side conditions after `dx_run`: register facts `hs`, then addresses,
then ownership in `h`. -/
macro "dc_sides " "[" ts:Lean.Parser.Tactic.simpLemma,* "] " h:term : tactic =>
  `(tactic| (all_goals (try dc_simp [$ts,*])
             all_goals (try dc_addr)
             all_goals (try dc_own $h)))

/-- The first address in `[a, a + k)` whose byte is `c`. -/
def findFrom (f : Nat → BitVec 8) (c : BitVec 8) : Nat → Nat → Option Nat
  | _, 0 => none
  | a, k + 1 => if f a = c then some a else findFrom f c (a + 1) k

theorem findFrom_hit {f : Nat → BitVec 8} {c : BitVec 8} {a : Nat} (k : Nat) (h : f a = c) :
    findFrom f c a (k + 1) = some a := by
  simp [findFrom, h]

theorem findFrom_miss {f : Nat → BitVec 8} {c : BitVec 8} {a : Nat} (k : Nat) (h : f a ≠ c) :
    findFrom f c a (k + 1) = findFrom f c (a + 1) k := by
  simp [findFrom, h]

/-- The C value of a search result: the address, or `NULL`. -/
abbrev ptrOr0 (o : Option Nat) : BitVec 64 := BitVec.ofNat 64 (o.getD 0)

/-! ## `memset` (`0x80000890`)

```
80000890 add a4,a0,a2 ; 80000894 mv a5,a0 ; 80000898 beqz a2,800008a8
8000089c addi a5,a5,1 ; 800008a0 sb a1,-1(a5) ; 800008a4 bne a4,a5,8000089c
800008a8 ret
```
-/

/-- The store loop of `memset` at `0x8000089c`, `a5 = d + i`, `a4 = d + n`. -/
theorem memset_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {d n : Nat} (hs : OwnedBytes S d n) (Mt0 : Mem)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [14, 15] R' R0 → Filled Mt' Mt0 d n (fun _ => lo8 (R0 11)) →
      DW live S Q (R0 1) R' Mt') :
    ∀ k i (R : Nat → BitVec 64) (Mt : Mem), n - i = k → i < n →
      R 15 = BitVec.ofNat 64 (d + i) → R 14 = BitVec.ofNat 64 (d + n) → Keeps [14, 15] R R0 →
      Filled Mt Mt0 d i (fun _ => lo8 (R0 11)) →
      DW live S Q 0x8000089c#64 R Mt := by
  have hlo := hs.lo
  have hhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k with
  | zero => intro i R Mt h1 h2; omega
  | succ k ih =>
    intro i R Mt hn hi h15 h14 hkeep hf
    have h11 : R 11 = R0 11 := hkeep.get 11
    dx_run hlive
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, se12_fff,
      h15, h14, h11, ofNat_add_ofNat]
    · simp only [BitVec.toNat_ofNat, StOKb]; omega
    · refine acc1 ?_; rw [BitVec.toNat_ofNat]
      rw [show (d + i + 1 + 18446744073709551615) % 2 ^ 64 = d + i by omega]
      exact hs.own i hi
    · intro hne
      refine ih (i + 1) _ _ (by omega) ?_ ?_ ?_ ?_ ?_
      · refine Classical.byContradiction fun hge => hne ?_
        congr 1; omega
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h15, ofNat_add_ofNat,
          Nat.add_assoc]
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h14]
      · keeps_tac hkeep
      · exact hf.snoc (by rw [BitVec.toNat_ofNat]; omega) (sbData_eq _)
    · intro heq
      have hn' : i + 1 = n := by
        refine Classical.byContradiction fun hne => heq ?_
        rw [ofNat_ne_iff (by omega) (by omega)]; omega
      dx_run hlive
      · simp only [upd_apply, Nat.reduceEqDiff, ite_false, hkeep.get 1, hal]
      · rw [hkeep.get 1]
        refine hk _ _ (by keeps_tac hkeep) ?_
        have := hf.snoc (A := (BitVec.ofNat 64 (d + i + 1 + 18446744073709551615)).toNat)
          (v := R0 11) (by rw [BitVec.toNat_ofNat]; omega) (sbData_eq _)
        rwa [hn'] at this

/-- **`memset(d, c, n)`** at `0x80000890` on `n` owned bytes: fills them with
the low byte of `c`, returns `d`, clobbers `a4`/`a5` only. -/
theorem memset_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {d n : Nat} (hs : OwnedBytes S d n)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 d) (h12 : R 12 = BitVec.ofNat 64 n)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [14, 15] R' R → Filled Mt' Mt d n (fun _ => lo8 (R 11)) →
      DW live S Q (R 1) R' Mt') :
    DW live S Q 0x80000890#64 R Mt := by
  have hlo := hs.lo
  have hhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h10, h12, ofNat_add_ofNat,
    ofNat_eq_zero_iff (show n < 2 ^ 64 by omega)]
  · rintro rfl
    dx_run hlive
    exact hk _ _ (by keeps_tac Keeps.refl _ _) (Filled.zero Mt d _)
  · intro hnz
    refine memset_loop hlive hs Mt R hal hk (n - 0) 0 _ _ rfl (by omega) ?_ ?_
      (by keeps_tac Keeps.refl _ _) (Filled.zero Mt d _)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h10, Nat.add_zero]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h10, h12, ofNat_add_ofNat]


/-! ## `memcpy` (`0x8000086c`)

```
8000086c beqz a2,8000088c ; 80000870 add a2,a0,a2 ; 80000874 mv a5,a0
80000878 lbu a4,0(a1) ; 8000087c addi a5,a5,1 ; 80000880 addi a1,a1,1
80000884 sb a4,-1(a5) ; 80000888 bne a2,a5,80000878 ; 8000088c ret
```
-/

/-- `memcpy`'s source and destination: `n` owned bytes each, disjoint. -/
structure CopyArgs (S : Nat → Prop) (d s n : Nat) : Prop where
  dst : OwnedBytes S d n
  src : OwnedBytes S s n
  disj : s + n ≤ d ∨ d + n ≤ s

/-- The copy loop of `memcpy` at `0x80000878`: `a1 = s + i`, `a5 = d + i`, `a2 = d + n`. -/
theorem memcpy_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {d s n : Nat} (hc : CopyArgs S d s n) (Mt0 : Mem)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [11, 12, 14, 15] R' R0 → Filled Mt' Mt0 d n (fun j => imgM Mt0 (s + j)) →
      DW live S Q (R0 1) R' Mt') :
    ∀ k i (R : Nat → BitVec 64) (Mt : Mem), n - i = k → i < n →
      R 11 = BitVec.ofNat 64 (s + i) → R 15 = BitVec.ofNat 64 (d + i) →
      R 12 = BitVec.ofNat 64 (d + n) → Keeps [11, 12, 14, 15] R R0 →
      Filled Mt Mt0 d i (fun j => imgM Mt0 (s + j)) →
      DW live S Q 0x80000878#64 R Mt := by
  have hlo := hc.dst.lo
  have hhi := hc.dst.hi
  have hlo' := hc.src.lo
  have hhi' := hc.src.hi
  have hdj := hc.disj
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k with
  | zero => intro i R Mt h1 h2; omega
  | succ k ih =>
    intro i R Mt hn hi h11 h15 h12 hkeep hf
    have hsrc : imgM Mt (s + i) = imgM Mt0 (s + i) := hf.rest _ (by omega)
    dx_run hlive
    dc_sides [h11, h15, h12] hc.src
    all_goals (try dc_own hc.dst)
    · intro hne
      refine ih (i + 1) _ _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_
      · refine Classical.byContradiction fun hge => hne ?_
        congr 1; omega
      · dc_simp [h11, Nat.add_assoc]
      · dc_simp [h15, Nat.add_assoc]
      · dc_simp [h12]
      · keeps_tac hkeep
      · exact hf.snoc rfl (by rw [sbData_zext, hsrc])
    · intro heq
      have hn' : i + 1 = n := by
        refine Classical.byContradiction fun hne => heq ?_
        rw [ofNat_ne_iff (by omega) (by omega)]; omega
      dx_run hlive
      · dc_simp [hkeep.get 1, hal]
      · rw [hkeep.get 1]
        refine hk _ _ (by keeps_tac hkeep) ?_
        have := hf.snoc (A := d + i) rfl (v := zero_extend (m := 64) (imgM Mt (s + i)))
          (by rw [sbData_zext, hsrc])
        rwa [hn'] at this

/-- **`memcpy(d, s, n)`** at `0x8000086c`, disjoint owned buffers: the `n`
bytes at `s` copied to `d`, `a0 = d`, clobbers `a1`, `a2`, `a4`, `a5`. -/
theorem memcpy_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {d s n : Nat} (hc : CopyArgs S d s n)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 d) (h11 : R 11 = BitVec.ofNat 64 s)
    (h12 : R 12 = BitVec.ofNat 64 n) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [11, 12, 14, 15] R' R → Filled Mt' Mt d n (fun j => imgM Mt (s + j)) →
      DW live S Q (R 1) R' Mt') :
    DW live S Q 0x8000086c#64 R Mt := by
  have hhi := hc.dst.hi
  dx_run hlive
  all_goals (try dc_simp [h10, h12, ofNat_eq_zero_iff (show n < 2 ^ 64 by omega)])
  · rintro rfl
    dx_run hlive
    exact hk _ _ (Keeps.refl _ _) (Filled.zero Mt d _)
  · intro hnz
    dx_run hlive at 0x80000878
    refine memcpy_loop hlive hc Mt R hal hk (n - 0) 0 _ _ rfl (by omega) ?_ ?_ ?_
      (by keeps_tac Keeps.refl _ _) (Filled.zero Mt d _)
    · dc_simp [h11]
    · dc_simp [h10]
    · dc_simp [h10, h12]

/-! ## `memchr` (`0x800008ac`)

```
800008ac beqz a2,800008d0 ; 800008b0 zext.b a1,a1 ; 800008b4 add a2,a0,a2
800008b8 j 800008c4 ; 800008bc addi a0,a0,1 ; 800008c0 beq a0,a2,800008d0
800008c4 lbu a5,0(a0) ; 800008c8 bne a5,a1,800008bc ; 800008cc ret
800008d0 li a0,0 ; 800008d4 ret
```
-/

/-- The search loop of `memchr` at `0x800008c4`: `a0 = s + i`, `a2 = s + n`,
`a1 = c & 0xff`. -/
theorem memchr_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {s n : Nat} (hs : OwnedBytes S s n)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 12, 15] R' R0 →
      R' 10 = ptrOr0 (findFrom (imgM Mt) (lo8 (R0 11)) s n) → DW live S Q (R0 1) R' Mt) :
    ∀ k i (R : Nat → BitVec 64), n - i = k → i < n →
      R 10 = BitVec.ofNat 64 (s + i) → R 12 = BitVec.ofNat 64 (s + n) →
      R 11 = R0 11 &&& 255#64 → Keeps [10, 11, 12, 15] R R0 →
      findFrom (imgM Mt) (lo8 (R0 11)) s n = findFrom (imgM Mt) (lo8 (R0 11)) (s + i) (n - i) →
      DW live S Q 0x800008c4#64 R Mt := by
  have hlo := hs.lo
  have hhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k with
  | zero => intro i R h1 h2; omega
  | succ k ih =>
    intro i R hn hi h10 h12 h11 hkeep hf
    have hsplit : n - i = (n - (i + 1)) + 1 := by omega
    dx_run hlive
    dc_sides [h10, h12, h11] hs
    · -- a mismatch: step on
      intro hne
      have hne' : imgM Mt (s + i) ≠ lo8 (R0 11) := fun e => hne ((zext_eq_and255 _ _).2 e)
      rw [hsplit, findFrom_miss _ hne'] at hf
      dx_run hlive
      all_goals (try dc_simp [h10, h12, h11])
      · intro heq
        have hn' : i + 1 = n := by
          refine Classical.byContradiction fun hne2 => ?_
          have := congrArg BitVec.toNat heq
          rw [ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)] at this; omega
        dx_run hlive
        · dc_simp [hkeep.get 1, hal]
        · rw [hkeep.get 1]
          refine hk _ (by keeps_tac hkeep) ?_
          dc_simp []
          rw [hf, ← hn', Nat.sub_self]; rfl
      · intro hne2
        refine ih (i + 1) _ (by omega) ?_ ?_ ?_ ?_ (by keeps_tac hkeep) ?_
        · refine Classical.byContradiction fun hge => hne2 ?_
          congr 1; omega
        · dc_simp [h10, Nat.add_assoc]
        · dc_simp [h12]
        · dc_simp [h11]
        · rw [hf, Nat.add_assoc]
    · -- a match: return `s + i`
      intro heq
      have heq' : imgM Mt (s + i) = lo8 (R0 11) :=
        (zext_eq_and255 _ _).1 (Classical.byContradiction fun h => heq h)
      dx_run hlive
      · dc_simp [hkeep.get 1, hal]
      · rw [hkeep.get 1]
        refine hk _ (by keeps_tac hkeep) ?_
        dc_simp [h10]
        rw [hf, hsplit, findFrom_hit _ heq']; rfl

/-- **`memchr(s, c, n)`** at `0x800008ac` on `n` owned bytes: `a0` is the
address of the first byte equal to the low byte of `c`, or `NULL`; clobbers
`a1`, `a2`, `a5`. -/
theorem memchr_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {s n : Nat} (hs : OwnedBytes S s n)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 s) (h12 : R 12 = BitVec.ofNat 64 n)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 12, 15] R' R →
      R' 10 = ptrOr0 (findFrom (imgM Mt) (lo8 (R 11)) s n) → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x800008ac#64 R Mt := by
  have hhi := hs.hi
  dx_run hlive
  all_goals (try dc_simp [h10, h12, ofNat_eq_zero_iff (show n < 2 ^ 64 by omega)])
  · rintro rfl
    dx_run hlive
    exact hk _ (by keeps_tac Keeps.refl _ _) rfl
  · intro hnz
    dx_run hlive at 0x800008c4
    refine memchr_loop hlive hs R hal hk (n - 0) 0 _ rfl (by omega) ?_ ?_ ?_
      (by keeps_tac Keeps.refl _ _) (by rw [Nat.add_zero, Nat.sub_zero])
    · dc_simp [h10]
    · dc_simp [h10, h12]
    · dc_simp []

/-! ## `strchr` (`0x800008d8`)

```
800008d8 lbu a5,0(a0) ; 800008dc zext.b a1,a1 ; 800008e0 bne a5,a1,800008f0
800008e4 ret ; 800008e8 lbu a5,0(a0) ; 800008ec beq a5,a1,80000900
800008f0 addi a0,a0,1 ; 800008f4 bnez a5,800008e8 ; 800008f8 li a0,0
800008fc ret ; 80000900 ret
```
-/

/-- The step of `strchr` at `0x800008f0`, past a byte at `s + i ≠ c`:
`a0 = s + i`, `a5` that byte, `a1 = c & 0xff`. -/
theorem strchr_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {s len : Nat} (hs : OwnedCStr S Mt s len)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 15] R' R0 →
      R' 10 = ptrOr0 (findFrom (imgM Mt) (lo8 (R0 11)) s (len + 1)) → DW live S Q (R0 1) R' Mt) :
    ∀ k i (R : Nat → BitVec 64), len - i = k → i ≤ len →
      R 10 = BitVec.ofNat 64 (s + i) → R 15 = zero_extend (m := 64) (imgM Mt (s + i)) →
      imgM Mt (s + i) ≠ lo8 (R0 11) →
      R 11 = R0 11 &&& 255#64 → Keeps [10, 11, 15] R R0 →
      findFrom (imgM Mt) (lo8 (R0 11)) s (len + 1) =
        findFrom (imgM Mt) (lo8 (R0 11)) (s + i) (len + 1 - i) →
      DW live S Q 0x800008f0#64 R Mt := by
  have hlo := hs.lo
  have hhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k with
  | zero =>
    intro i R hn hi h10 h15 hne h11 hkeep hf
    have hil : len = i := by omega
    subst hil
    dx_run hlive
    all_goals (try dc_simp [h10, h15, h11])
    · intro hnz
      exact absurd ((zext8_eq_zero _).2 hs.nul) hnz
    · intro hz
      dx_run hlive
      · dc_simp [hkeep.get 1, hal]
      · rw [hkeep.get 1]
        refine hk _ (by keeps_tac hkeep) ?_
        dc_simp []
        rw [hf, show len + 1 - len = 0 + 1 by omega, findFrom_miss _ hne]; rfl
  | succ k ih =>
    intro i R hn hi h10 h15 hne h11 hkeep hf
    have hnz : imgM Mt (s + i) ≠ 0 := hs.nz i (by omega)
    rw [show len + 1 - i = (len + 1 - (i + 1)) + 1 by omega, findFrom_miss _ hne] at hf
    dx_run hlive
    all_goals (try dc_simp [h10, h15, h11])
    · intro _
      dx_run hlive
      dc_sides [h10, h15, h11] hs
      · intro heq
        have heq' : imgM Mt (s + i + 1) = lo8 (R0 11) := (zext_eq_and255 _ _).1 heq
        dx_run hlive
        · dc_simp [hkeep.get 1, hal]
        · rw [hkeep.get 1]
          refine hk _ (by keeps_tac hkeep) ?_
          dc_simp []
          rw [hf, show len + 1 - (i + 1) = (len - (i + 1)) + 1 by omega, findFrom_hit _ heq']; rfl
      · intro hne2
        have hne' : imgM Mt (s + (i + 1)) ≠ lo8 (R0 11) :=
          fun e => hne2 (by rw [Nat.add_assoc]; exact (zext_eq_and255 _ _).2 e)
        refine ih (i + 1) _ (by omega) (by omega) ?_ ?_ hne' ?_ (by keeps_tac hkeep) ?_
        · dc_simp [Nat.add_assoc]
        · dc_simp [Nat.add_assoc]
        · dc_simp [h11]
        · rw [hf, Nat.add_assoc]
    · intro hz
      exact absurd ((zext8_eq_zero _).1 (Classical.byContradiction hz)) hnz

/-- **`strchr(s, c)`** at `0x800008d8` on an owned C string of length `len`:
`a0` is the address of the first byte equal to the low byte of `c` among the
`len + 1` bytes (the NUL included), or `NULL`; clobbers `a1`, `a5`. -/
theorem strchr_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {s len : Nat} (hs : OwnedCStr S Mt s len)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 s) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 11, 15] R' R →
      R' 10 = ptrOr0 (findFrom (imgM Mt) (lo8 (R 11)) s (len + 1)) → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x800008d8#64 R Mt := by
  have hlo := hs.lo
  have hhi := hs.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive
  dc_sides [h10] hs
  · intro hne
    have hne' : imgM Mt (s + 0) ≠ lo8 (R 11) :=
      fun e => hne (by rw [Nat.add_zero] at e; exact (zext_eq_and255 _ _).2 e)
    refine strchr_loop hlive hs R hal hk (len - 0) 0 _ rfl (by omega) ?_ ?_ hne' ?_
      (by keeps_tac Keeps.refl _ _) (by simp only [Nat.add_zero, Nat.sub_zero])
    · dc_simp [h10]
    · dc_simp [h10]
    · dc_simp []
  · intro heq
    have heq' : imgM Mt s = lo8 (R 11) :=
      (zext_eq_and255 _ _).1 (Classical.byContradiction heq)
    dx_run hlive
    refine hk _ (by keeps_tac Keeps.refl _ _) ?_
    dc_simp [h10]
    rw [findFrom_hit _ heq']; rfl


/-! ## `strncpy` (`0x80000928`)

```
80000928 li a5,0 ; 8000092c bnez a2,80000940 ; 80000930 ret
80000934 sb a4,0(a3) ; 80000938 addi a5,a5,1 ; 8000093c beq a2,a5,80000968
80000940 add a4,a1,a5 ; 80000944 lbu a4,0(a4) ; 80000948 add a3,a0,a5
8000094c bnez a4,80000934 ; 80000950 bgeu a5,a2,80000968 ; 80000954 mv a5,a3
80000958 add a2,a0,a2 ; 8000095c sb zero,0(a5) ; 80000960 addi a5,a5,1
80000964 bne a2,a5,8000095c ; 80000968 ret
```
-/

/-- `strncpy`'s arguments: `n` owned destination bytes, an owned source C
string of length `len`, disjoint. -/
structure StrncpyArgs (S : Nat → Prop) (Mt : Mem) (d s n len : Nat) : Prop where
  dst : OwnedBytes S d n
  src : OwnedCStr S Mt s len
  disj : s + len + 1 ≤ d ∨ d + n ≤ s

/-- The bytes `strncpy` writes: the source string, then NULs. -/
def ncpyByte (f : Nat → BitVec 8) (s len j : Nat) : BitVec 8 :=
  if j < len then f (s + j) else 0

theorem ncpyByte_lt {f : Nat → BitVec 8} {s len j : Nat} (h : j < len) :
    ncpyByte f s len j = f (s + j) := by simp [ncpyByte, h]

theorem ncpyByte_ge {f : Nat → BitVec 8} {s len j : Nat} (h : len ≤ j) :
    ncpyByte f s len j = 0 := by simp [ncpyByte, show ¬ j < len by omega]

/-- The NUL fill of `strncpy` at `0x8000095c`: `a5 = d + j`, `a2 = d + n`, `len ≤ j < n`. -/
theorem strncpy_zero {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {d s n len : Nat} {Mt0 : Mem}
    (hc : StrncpyArgs S Mt0 d s n len)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [12, 13, 14, 15] R' R0 → Filled Mt' Mt0 d n (ncpyByte (imgM Mt0) s len) →
      DW live S Q (R0 1) R' Mt') :
    ∀ k j (R : Nat → BitVec 64) (Mt : Mem), n - j = k → j < n → len ≤ j →
      R 15 = BitVec.ofNat 64 (d + j) → R 12 = BitVec.ofNat 64 (d + n) →
      Keeps [12, 13, 14, 15] R R0 → Filled Mt Mt0 d j (ncpyByte (imgM Mt0) s len) →
      DW live S Q 0x8000095c#64 R Mt := by
  have hlo := hc.dst.lo
  have hhi := hc.dst.hi
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hzero : ∀ j, len ≤ j → sbData 0#64 = ncpyByte (imgM Mt0) s len j := fun j hj => by
    rw [ncpyByte_ge hj]; rfl
  intro k
  induction k with
  | zero => intro j R Mt h1 h2; omega
  | succ k ih =>
    intro j R Mt hn hj hl h15 h12 hkeep hf
    dx_run hlive
    dc_sides [h15, h12] hc.dst
    · intro hne
      refine ih (j + 1) _ _ (by omega) ?_ (by omega) ?_ ?_ (by keeps_tac hkeep) ?_
      · refine Classical.byContradiction fun hge => hne ?_
        congr 1; omega
      · dc_simp [h15, Nat.add_assoc]
      · dc_simp [h12]
      · exact hf.snoc rfl (hzero j hl)
    · intro heq
      have hn' : j + 1 = n := by
        refine Classical.byContradiction fun hne => heq ?_
        rw [ofNat_ne_iff (by omega) (by omega)]; omega
      dx_run hlive
      · dc_simp [hkeep.get 1, hal]
      · rw [hkeep.get 1]
        refine hk _ _ (by keeps_tac hkeep) ?_
        have := hf.snoc (A := d + j) rfl (hzero j hl)
        rwa [hn'] at this

/-- The copy loop of `strncpy` at `0x80000940`: `a5 = i`, `i < n`, `i ≤ len`. -/
theorem strncpy_copy {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {d s n len : Nat} {Mt0 : Mem}
    (hc : StrncpyArgs S Mt0 d s n len)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0)
    (h10 : R0 10 = BitVec.ofNat 64 d) (h11 : R0 11 = BitVec.ofNat 64 s)
    (h12 : R0 12 = BitVec.ofNat 64 n)
    (hk : ∀ R' Mt', Keeps [12, 13, 14, 15] R' R0 → Filled Mt' Mt0 d n (ncpyByte (imgM Mt0) s len) →
      DW live S Q (R0 1) R' Mt') :
    ∀ k i (R : Nat → BitVec 64) (Mt : Mem), n - i = k → i < n → i ≤ len →
      R 15 = BitVec.ofNat 64 i → Keeps [12, 13, 14, 15] R R0 → R 12 = R0 12 →
      Filled Mt Mt0 d i (ncpyByte (imgM Mt0) s len) →
      DW live S Q 0x80000940#64 R Mt := by
  have hlo := hc.dst.lo
  have hhi := hc.dst.hi
  have hlo' := hc.src.lo
  have hhi' := hc.src.hi
  have hdj := hc.disj
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k with
  | zero => intro i R Mt h1 h2; omega
  | succ k ih =>
    intro i R Mt hn hi hil h15 hkeep h12' hf
    have hr10 : R 10 = BitVec.ofNat 64 d := (hkeep.get 10).trans h10
    have hr11 : R 11 = BitVec.ofNat 64 s := (hkeep.get 11).trans h11
    have hr12 : R 12 = BitVec.ofNat 64 n := h12'.trans h12
    have hsrc : imgM Mt (s + i) = imgM Mt0 (s + i) := hf.rest _ (by omega)
    dx_run hlive
    dc_sides [h15, hr10, hr11, hr12] hc.src
    · -- a nonzero byte: copy it
      intro hnz
      have hlt : i < len := by
        refine Classical.byContradiction fun hge => hnz ?_
        rw [zext8_eq_zero, hsrc, show i = len by omega]; exact hc.src.nul
      dx_run hlive
      dc_sides [h15, hr10, hr11, hr12] hc.dst
      · intro heq
        have hn' : i + 1 = n := by
          have := congrArg BitVec.toNat heq
          rw [ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)] at this; omega
        dx_run hlive
        · dc_simp [hkeep.get 1, hal]
        · rw [hkeep.get 1]
          refine hk _ _ (by keeps_tac hkeep) ?_
          have := hf.snoc (A := d + i) rfl (v := zero_extend (m := 64) (imgM Mt (s + i)))
            (by rw [sbData_zext, hsrc, ncpyByte_lt hlt])
          rwa [hn'] at this
      · intro hne
        refine ih (i + 1) _ _ (by omega) ?_ (by omega) ?_ (by keeps_tac hkeep) ?_ ?_
        · refine Classical.byContradiction fun hge => hne ?_
          congr 1; omega
        · dc_simp [h15]
        · dc_simp [h12']
        · exact hf.snoc rfl (by rw [sbData_zext, hsrc, ncpyByte_lt hlt])
    · -- the NUL: fill the rest
      intro hz
      have hz' : imgM Mt0 (s + i) = 0 :=
        hsrc ▸ (zext8_eq_zero _).1 (Classical.byContradiction hz)
      have hle : len ≤ i := Classical.byContradiction fun hlt => hc.src.nz i (by omega) hz'
      dx_run hlive
      dc_sides [h15, hr10, hr11, hr12] hc.dst
      · intro hge; omega
      · intro _
        dx_run hlive at 0x8000095c
        refine strncpy_zero hlive hc R0 hal hk (n - i) i _ _ rfl hi hle ?_ ?_
          (by keeps_tac hkeep) hf
        · dc_simp [h15, hr10]
        · dc_simp [hr10, hr12]

/-- **`strncpy(d, s, n)`** at `0x80000928`: the first `n` bytes of the
source string padded with NULs (`ncpyByte`) written to `d`, `a0 = d`,
clobbers `a2`–`a5`. -/
theorem strncpy_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {d s n len : Nat} (hc : StrncpyArgs S Mt d s n len)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 d) (h11 : R 11 = BitVec.ofNat 64 s)
    (h12 : R 12 = BitVec.ofNat 64 n) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [12, 13, 14, 15] R' R → Filled Mt' Mt d n (ncpyByte (imgM Mt) s len) →
      DW live S Q (R 1) R' Mt') :
    DW live S Q 0x80000928#64 R Mt := by
  have hhi := hc.dst.hi
  dx_run hlive
  all_goals (try dc_simp [h12])
  · intro hnz
    have hpos : 0 < n := Nat.pos_of_ne_zero fun h0 => hnz (by rw [h0])
    refine strncpy_copy hlive hc R hal h10 h11 h12 hk (n - 0) 0 _ _ rfl hpos (Nat.zero_le _) ?_
      (by keeps_tac Keeps.refl _ _) ?_ (Filled.zero Mt d _)
    all_goals dc_simp []
  · intro hz
    have h0 : n = 0 := by
      have := Classical.byContradiction hz
      rwa [ofNat_eq_zero_iff (by omega)] at this
    subst h0
    dx_run hlive
    exact hk _ _ (by keeps_tac Keeps.refl _ _) (Filled.zero Mt d _)

end Dc.Mach
