import Dc.Mach.Bc.Rep

/-!
# Shared vocabulary of the `lib/number.c` specs

- `HeapOwn S`: the run owns the heap (`HeapInv.own` gives it); `acc_heap`
  discharges an access's ownership side condition inside the heap.
- `PtrSlot S q`: eight owned, aligned bytes at `q` (a `bc_num *` argument).
- `MemOnly P Mt' Mt`: only bytes in `P` differ.
- `boolWord`, `ordWord`: the C values of a `char` flag and of a comparison.
- `bsimp [hs…]`: register lookups, literal immediates and `BitVec.ofNat`
  address arithmetic (bounds by `omega`); `num_facts h` puts the bounds of
  `h : NumAt Mt o` in the context as literals.
- Field updates of an object (`NumAt.setRefs`, `NumAt.setSign`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The run owns the heap. -/
abbrev HeapOwn (S : Nat → Prop) : Prop := ∀ a, heapStart ≤ a → a < heapEnd → S a

/-- An access inside the heap owns its bytes. -/
theorem acc_heap {S : Nat → Prop} (hS : HeapOwn S) {a w : Nat} (h1 : 2147603920 ≤ a)
    (h2 : a + w ≤ 2273312768) : ∀ b ∈ accAddrs a w, S b := fun b hb => by
  have := of_mem_accAddrs hb; exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)

/-- Eight owned, aligned bytes in writable RAM: a pointer slot. -/
structure PtrSlot (S : Nat → Prop) (q : Nat) : Prop where
  own : ∀ i, i < 8 → S (q + i)
  al : q % 8 = 0
  lo : tohostAddr + 16 ≤ q
  hi : q + 8 ≤ 0x88000000

theorem PtrSlot.acc {S : Nat → Prop} {q : Nat} (h : PtrSlot S q) : ∀ b ∈ accAddrs q 8, S b :=
  fun b hb => by
    have := of_mem_accAddrs hb
    have := h.own (b - q) (by omega); rwa [Nat.add_sub_cancel' (by omega)] at this

/-- Only the bytes in `P` differ between `Mt'` and `Mt`. -/
def MemOnly (P : Nat → Prop) (Mt' Mt : Mem) : Prop := ∀ a, ¬ P a → imgM Mt' a = imgM Mt a

theorem MemOnly.refl (P : Nat → Prop) (Mt : Mem) : MemOnly P Mt Mt := fun _ _ => rfl

theorem MemOnly.trans {P : Nat → Prop} {M2 M1 M0 : Mem} (h2 : MemOnly P M2 M1)
    (h1 : MemOnly P M1 M0) : MemOnly P M2 M0 := fun a ha => (h2 a ha).trans (h1 a ha)

theorem MemOnly.mono {P P' : Nat → Prop} {Mt' Mt : Mem} (h : MemOnly P Mt' Mt)
    (hp : ∀ a, P a → P' a) : MemOnly P' Mt' Mt := fun a ha => h a fun hp' => ha (hp a hp')

/-- One store changes only its bytes. -/
theorem MemOnly.store (Mt : Mem) (x w : Nat) (v : BitVec 64) :
    MemOnly (fun a => x ≤ a ∧ a < x + w) (writeLog Mt [(x, w, v)]) Mt := fun a ha =>
  imgM_store_miss _ _ (by omega)

/-- The C value of a `char` flag. -/
abbrev boolWord (b : Bool) : BitVec 64 := BitVec.ofNat 64 b.toNat

/-- The C value of a three-way comparison (`-1`, `0`, `1`). -/
def ordWord : Ordering → BitVec 64
  | .lt => 0xffffffffffffffff#64
  | .eq => 0#64
  | .gt => 1#64

@[simp] theorem signWord_false : signWord false = 0#64 := rfl
@[simp] theorem signWord_true : signWord true = 1#64 := rfl

theorem signWord_eq (b : Bool) : signWord b = boolWord b := by cases b <;> rfl

/-- `addiw`'s result on a small word. -/
theorem sxw_ofNat {k : Nat} (hk : k < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 k)) = BitVec.ofNat 64 k := by
  have := sx32_small hk
  simpa [sx32, BitVec.truncate_eq_setWidth, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)] using this

theorem ofNat_eq_iff {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro e; exact Classical.byContradiction fun hne => (ofNat_ne_iff hx hy).2 hne e
  · rintro rfl; rfl

theorem ze_bb (b : Bool) : zero_extend (m := 64) (bool_to_bit b) = boolWord b := by
  cases b <;> decide

/-- `sltiu r, x, 1` (`seqz`): `x` is zero. -/
theorem sltiu1 (x : BitVec 64) : zopz0zI_u x 1#64 = decide (x.toNat = 0) := by
  unfold zopz0zI_u
  simp [BitVec.toNatInt]
  omega

/-- `slli` of a word. -/
theorem shl_ofNat (v k : Nat) : BitVec.ofNat 64 v <<< k = BitVec.ofNat 64 (v * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mul_mod]

/-- `not`, `srai 63`, `and` (`max (v, 0)`) on a nonnegative word. -/
theorem max0_ofNat {v : Nat} (hv : v < 2 ^ 63) :
    BitVec.ofNat 64 v &&& shift_bits_right_arith (BitVec.ofNat 64 v ^^^ 18446744073709551615#64) (63#6) =
      BitVec.ofNat 64 v := by
  have hx : BitVec.ofNat 64 v ^^^ 18446744073709551615#64 = ~~~(BitVec.ofNat 64 v) := by
    rw [show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]
  have hmsb : (~~~(BitVec.ofNat 64 v)).msb = true := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_not]; omega
  have hsh : (BitVec.ofNat 64 v) >>> 63 = 0#64 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  unfold shift_bits_right_arith
  rw [hx, show BitVec.toNatInt (63#6) = 63 from rfl]
  rw [BitVec.sshiftRight_eq_of_msb_true hmsb, BitVec.not_not, show Int.toNat 63 = 63 from rfl, hsh]
  rw [show (~~~(0#64) : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.and_allOnes]

theorem ofNat_congr {x y : Nat} (h : x = y) : BitVec.ofNat 64 x = BitVec.ofNat 64 y := h ▸ rfl

/-- Stack addresses below `sp` (frames of 16, 32, 48, 96 bytes): `sp + (2^64 - c) + k`
is `sp - c + k`. -/
theorem ofNat_wrap {x m k : Nat} (c : Nat) (hc : m + c = 2 ^ 64) (h : c ≤ x) :
    BitVec.ofNat 64 (x + m + k) = BitVec.ofNat 64 (x - c + k) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem frame16 {x k : Nat} (h : 16 ≤ x) :
    BitVec.ofNat 64 (x + 18446744073709551600 + k) = BitVec.ofNat 64 (x - 16 + k) :=
  ofNat_wrap 16 (by decide) h
theorem frame32 {x k : Nat} (h : 32 ≤ x) :
    BitVec.ofNat 64 (x + 18446744073709551584 + k) = BitVec.ofNat 64 (x - 32 + k) :=
  ofNat_wrap 32 (by decide) h
theorem frame96 {x k : Nat} (h : 96 ≤ x) :
    BitVec.ofNat 64 (x + 18446744073709551520 + k) = BitVec.ofNat 64 (x - 96 + k) :=
  ofNat_wrap 96 (by decide) h
theorem frame16' {x : Nat} (h : 16 ≤ x) :
    BitVec.ofNat 64 (x + 18446744073709551600) = BitVec.ofNat 64 (x - 16) := by
  simpa using frame16 (k := 0) h
theorem frame32' {x : Nat} (h : 32 ≤ x) :
    BitVec.ofNat 64 (x + 18446744073709551584) = BitVec.ofNat 64 (x - 32) := by
  simpa using frame32 (k := 0) h
theorem frame96' {x : Nat} (h : 96 ≤ x) :
    BitVec.ofNat 64 (x + 18446744073709551520) = BitVec.ofNat 64 (x - 96) := by
  simpa using frame96 (k := 0) h

/-- `srli` of a word. -/
theorem shr_ofNat (v k : Nat) : BitVec.ofNat 64 v >>> k = BitVec.ofNat 64 (v % 2 ^ 64 / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide)))).symm

/-- `subw` of two small words. -/
theorem subw_ofNat {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) -
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 b)) = BitVec.ofNat 64 (a - b) := by
  have e : BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) - BitVec.extractLsb 31 0 (BitVec.ofNat 64 b) =
      BitVec.ofNat 32 (a - b) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub]
    omega
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp [msb32_small (show a - b < 2 ^ 31 by omega)]
  omega

/-- `addw` of two small words. -/
theorem addw_ofNat {a b : Nat} (h : a + b < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) +
      BitVec.extractLsb 31 0 (BitVec.ofNat 64 b)) = BitVec.ofNat 64 (a + b) := by
  have e : BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) + BitVec.extractLsb 31 0 (BitVec.ofNat 64 b) =
      BitVec.ofNat 32 (a + b) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp [msb32_small h]
  omega

/-- A small word as a signed integer. -/
theorem toInt_ofNat_small {k : Nat} (hk : k < 2 ^ 63) : (BitVec.ofNat 64 k).toInt = k := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 2 * k < 2 ^ 64 by omega, ite_true]

/-- `blez` on a positive small word is not taken. -/
theorem not_blez {k : Nat} (h1 : 1 ≤ k) (h2 : k < 2 ^ 63) :
    ¬ (BitVec.ofNat 64 k).toInt ≤ (0#64).toInt := by
  rw [toInt_ofNat_small h2]; simp; omega

/-- Normalize a decrement before converting word addition to naturals.
This avoids the deeply nested modulo proof from the generic addition normalizer. -/
theorem word_pred {k : Nat} (h1 : 1 ≤ k) :
    BitVec.ofNat 64 k + 18446744073709551615#64 = BitVec.ofNat 64 (k - 1) := by
  change BitVec.ofNat 64 k + -(1#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le k 1 (by decide) h1

/-- Register lookups, literal immediates and `BitVec.ofNat` address arithmetic
(bounds by `omega`), with the facts `hs`. -/
macro "bsimp" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| ((try simp (disch := omega) only [$ts,*, word_pred, sxw_ofNat] $(loc)?) <;>
    (try simp (disch := omega) only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, reduceIte,
    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
    BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat, ofNat_add_ofNat, ofNat_toNat_lt,
    Nat.reduceAdd, Nat.reduceSub, Nat.add_zero, Nat.sub_zero, ldv_lbu, boolWord, Bool.toNat_false, Bool.toNat_true,
    frame16, frame32, frame96, frame16', frame32', frame96',
    $ts,*] $(loc)?)))

/-- The bounds of `h : NumAt Mt o`, with the heap's limits as literals. -/
macro "num_facts " h:term : tactic =>
  `(tactic| (have _n1 := ($h).shape.pLo; have _n2 := ($h).shape.pHi; have _n3 := ($h).shape.pAl
             have _n4 := ($h).shape.vLo; have _n5 := ($h).shape.vHi; have _n6 := ($h).shape.ptrLe
             have _n7 := ($h).shape.size; have _n8 := ($h).shape.lenPos
             have _n9 := ($h).shape.refsLt; have _n10 := ($h).shape.dsLen
             simp only [heapStart, heapEnd] at _n1 _n2 _n4 _n5
             have _htx : tohostAddr = 0x8001ad00 := rfl))

/-- A word (in)equality of `BitVec.ofNat`s and literals as one of naturals
(`%`-reduced; `omega` closes it with the bounds). -/
macro "bv_nat" " at " h:ident : tactic =>
  `(tactic| simp only [ne_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat] at $h:ident)

open Lean Elab Tactic Meta in
/-- A goal `P → G` whose `P` holds by `decide`: introduce it. -/
elab "bc_intro_true" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let .forallE _ P _ _ := ty | throwError "bc_intro_true: not an implication"
  unless (← isProp P) do throwError "bc_intro_true: not a proposition"
  let pg ← mkFreshExprMVar P
  let gs ← evalTacticAt (← `(tactic| decide)) pg.mvarId!
  unless gs.isEmpty do throwError "bc_intro_true: decide left goals"
  let (_, g') ← g.intro1
  replaceMainGoal [g']

open Lean Elab Tactic Meta in
/-- Fails when the goal is a symbolic run at one of the given PCs (so a
repeated `bc_run` leaves goals at its stops alone). -/
elab "bc_not_at" stops:(num)* : tactic => do
  let g ← getMainGoal
  let pcs := stops.toList.map (·.getNat)
  if let some pc ← g.withContext (do VsaIris.Sym.swpPC? (← instantiateMVars (← g.getType))) then
    if pcs.contains pc then throwError "bc_not_at: at a stop"

/-- One round of symbolic execution: `dx_run` (not from a stop), then
`bsimp [hs]` on every goal, address and heap-ownership side conditions, and
branch hypotheses decided by `decide` (a false one closes its branch, a true
one is introduced). -/
syntax "bc_run " term:max term:max " [" Lean.Parser.Tactic.simpLemma,* "]" (" at " num+)? : tactic

macro_rules
  | `(tactic| bc_run $hl $hs [$ts,*] at $stops*) =>
    `(tactic| (bc_not_at $stops*
               dx_run $hl at $stops*
               all_goals (try bsimp [$ts,*])
               all_goals (try (first | (simp only [LdOK, StOK, StOKb]; omega) |
                 exact acc_heap $hs (by omega) (by omega)))
               all_goals (try (intro hc; exact absurd hc (by decide)))
               all_goals (try bc_intro_true)))
  | `(tactic| bc_run $hl $hs [$ts,*]) =>
    `(tactic| (dx_run $hl
               all_goals (try bsimp [$ts,*])
               all_goals (try (first | (simp only [LdOK, StOK, StOKb]; omega) |
                 exact acc_heap $hs (by omega) (by omega)))
               all_goals (try (intro hc; exact absurd hc (by decide)))
               all_goals (try bc_intro_true)))

/-- Address side conditions (`LdOK`, `StOK`, `StOKb`) by `omega`. -/
macro "bc_addr" : tactic => `(tactic| (simp only [LdOK, StOK, StOKb]; omega))

/-! ## Field updates -/

/-- A store of `w` bytes at `o.p + off` inside the struct, and the new object
`o'` agreeing with `o` except in the field it writes: the other fields and
the digits read the same. -/
theorem NumAt.store_other {Mt : Mem} {o : NumRep} (h : NumAt Mt o) {off w : Nat} (v : BitVec 64)
    (hoff : off + w ≤ 40) {a : Nat} (hd : a < o.len + o.scale) :
    imgM (writeLog Mt [(o.p + off, w, v)]) (o.val + a) = imgM Mt (o.val + a) := by
  have := h.shape.sep; have := h.shape.ptrLe
  exact imgM_store_miss _ _ (by omega)

/-- `n_refs` rewritten. -/
theorem NumAt.setRefs {Mt : Mem} {o : NumRep} (h : NumAt Mt o) {v : BitVec 64} {k : Nat}
    (hv : v.toNat % 2 ^ 32 = k) (hk : k < 2 ^ 31) :
    NumAt (writeLog Mt [(o.p + 12, 4, v)]) { o with refs := k } := by
  have hs := h.shape
  refine ⟨{ hs with refsLt := hk }, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.sign
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.len
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.scale
  · exact ldv_lw_hitN _ rfl hv hk
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.ptr
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.value
  · rw [h.store_other v (by omega) hi]; exact h.digit i hi

/-- `n_sign` rewritten. -/
theorem NumAt.setSign {Mt : Mem} {o : NumRep} (h : NumAt Mt o) {v : BitVec 64} (b : Bool)
    (hv : v.toNat % 2 ^ 32 = b.toNat) :
    NumAt (writeLog Mt [(o.p, 4, v)]) { o with neg := b } := by
  have hs := h.shape
  refine ⟨{ hs with }, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [signWord, ldv_lw_hitN _ rfl hv (by cases b <;> decide)]; cases b <;> rfl
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.len
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.scale
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM]; omega)]; exact h.refs
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.ptr
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact h.value
  · rw [← Nat.add_zero o.p, h.store_other v (by omega) hi]; exact h.digit i hi

end Dc.Mach
