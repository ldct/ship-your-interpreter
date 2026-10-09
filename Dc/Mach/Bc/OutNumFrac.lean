import Dc.Mach.Bc.OutNumExit

/-! # `bc_out_num` in a base other than 10: the fraction digits

-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel (FracInv FracFuel)

set_option linter.unusedSimpArgs false

/-- The characters of the fraction digit `d` at index `i`: a space before
every long digit but the first. -/
abbrev ogDigF (ob d i : Nat) : List Nat :=
  if ob ≤ 16 then [Num.hexChar d] else Num.outLong d (Num.decText (ob - 1)).length (i != 0)

/-- The fraction digits' characters from the index `i`. -/
def ogFracOut (ob s fuel : Nat) (f : Num) (t i : Nat) : List Nat :=
  ((Num.fracDigits ob s fuel f t).zipIdx i).flatMap fun p => ogDigF ob p.1 p.2

/-- The fraction part: the magnitude below one, positive. -/
theorem frac_part (n : Num) : ogFrac n = ⟨false, n.mag % 10 ^ n.scale, n.scale⟩ := by
  obtain ⟨neg, m, s⟩ := n
  have hp : 0 < 10 ^ s := Nat.pow_pos (by decide)
  have hdm := Nat.div_add_mod m (10 ^ s)
  simp only [ogFrac, ogIp, Num.div, Num.one, Nat.one_ne_zero, beq_iff_eq, ite_false, Option.getD_some,
    Nat.zero_add, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Num.sub, Num.align, Nat.max_zero,
    Nat.zero_max, Nat.max_self, Nat.sub_zero, Nat.sub_self]
  have hr : m % 10 ^ s < 10 ^ s := Nat.mod_lt _ hp
  generalize m / 10 ^ s = q at hdm ⊢
  generalize m % 10 ^ s = r at hdm hr ⊢
  generalize 10 ^ s = P at hdm hp hr ⊢
  have hcmp : ∀ (A B : Nat), B ≤ A → (compare A B = .gt ∧ B < A) ∨ (compare A B = .eq ∧ A = B) :=
    fun A B h => by
      rcases Nat.lt_or_ge B A with h' | h'
      · exact .inl ⟨Nat.compare_eq_gt.mpr h', h'⟩
      · exact .inr ⟨Nat.compare_eq_eq.mpr (by omega), by omega⟩
  have hqP : q * P ≤ m := by rw [Nat.mul_comm]; omega
  by_cases hq : q = 0
  · subst hq
    cases neg
    · rcases hcmp m 0 (Nat.zero_le _) with ⟨e, h⟩ | ⟨e, h⟩ <;> simp [e, Num.zero] <;> omega
    · simp; omega
  · cases neg <;>
    · rcases hcmp m (q * P) hqP with ⟨e, h⟩ | ⟨e, h⟩ <;> simp [hq, e, Num.zero] <;>
        rw [Nat.mul_comm] at hdm <;> omega

/-- The whole target split at the fraction loop. -/
theorem og_target {x : NumObj} {ob : Nat} {cs : List Nat} (hm : x.rep.num.mag ≠ 0) (hb : ob ≠ 10) :
    cs ++ Num.outChars x.rep.num ob =
      ogIntOut x ob cs ++ (if x.rep.num.scale == 0 then []
        else 46 :: ogFracOut ob x.rep.num.scale (4 * x.rep.num.scale + 4) (ogFrac x.rep.num) 1 0) := by
  have hz : x.rep.num.isZero = false := by simp [Num.isZero, hm]
  rw [Dc.BcModel.outChars_base hz hb]
  simp only [ogIntOut, ogFracOut, ogDigI, ogDigF, signOut, ogFrac, ogIp, List.append_assoc]

/-- One fraction digit. -/
theorem ogFracOut_step {ob s fuel t i : Nat} {f : Num} (h : FracInv f s) (ht0 : t ≠ 0)
    (ht : t < 10 ^ s) (hb0 : 0 < ob) (hb : ob < 2 ^ 31) :
    ogFracOut ob s (fuel + 1) f t i =
      ogDigF ob (f.mag * ob / 10 ^ s) i ++
        ogFracOut ob s fuel ⟨false, f.mag * ob % 10 ^ s, s⟩ (t * ob) (i + 1) := by
  unfold ogFracOut
  rw [Dc.BcModel.fracDigits_unfold ht0 ht, Dc.BcModel.fracStep_mul h,
    (Dc.BcModel.fracStep_digit h hb0 hb).1, Int.natAbs_natCast, Dc.BcModel.fracStep_sub]
  simp [List.zipIdx_cons]

/-- No more fraction digits. -/
theorem ogFracOut_stop {ob s fuel t i : Nat} {f : Num} (ht0 : t ≠ 0) (ht : 10 ^ s ≤ t) :
    ogFracOut ob s fuel f t i = [] := by
  unfold ogFracOut; rw [Dc.BcModel.fracDigits_stop ht0 ht]; rfl

end Dc.Mach
