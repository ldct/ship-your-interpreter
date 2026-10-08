import Dc.Mach.Bc.KaraEntry

/-!
# `_bc_rec_mul`'s Karatsuba step: the `_zero_` references

A half with no digits is a reference to `_zero_` instead of a view, so the
step loads `_zero_`'s struct and increments its reference count: once at
`0x80005378` (`u1`, with `la < n`) and once at `0x80004e68` (`v1`, with
`lb < n`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- **`_zero_`'s count raised at `0x80005378`** (`u1` is a reference to
`_zero_`), its struct left in `s8`. -/
theorem kzeroref_80005378 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {A B : List NumObj} {z : NumObj}
    (hb : BcHeap S M H F (A ++ z :: B))
    (hz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p) (hzo : ∀ a, constBytes a → S a)
    (hr : z.rep.refs + 1 < 2 ^ 31)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [15, 24] R' R →
      BcHeap S M' H F (A ++ z.withRefs (z.rep.refs + 1) :: B) →
      R' 24 = BitVec.ofNat 64 z.rep.p →
      (∀ a, a < z.rep.p + 12 ∨ z.rep.p + 16 ≤ a → imgM M' a = imgM M a) →
      DW live S Q 0x8000538c#64 R' M') :
    DW live S Q 0x80005378#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hzn := hb.nums _ (List.mem_append_right _ List.mem_cons_self)
  num_facts hzn
  have hrf := hzn.refs
  have hcst : ∀ b ∈ accAddrs 2147601864 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact hzo b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  have hsx := sxw_ofNat (show z.rep.refs < 2 ^ 31 by omega)
  have hsx1 := sxw_ofNat (show z.rep.refs + 1 < 2 ^ 31 by omega)
  simp only [zeroAddr] at hz
  bc_run hlive hS [hz, hrf, hsx, hsx1] at 0x8000538c
  all_goals try (exact hcst)
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr, zeroAddr] at *; omega)
  refine hnext _ _ (by keeps_tac Keeps.refl _ _)
    (hb.setRefs (toNat_ofNat_mod32 (by omega)) (by omega)) (by bsimp [hz]) ?_
  exact fun a ha => imgM_store_miss _ _ (by omega)

/-- **`_zero_`'s count raised at `0x80004e68`** (`v1` is a reference to
`_zero_`), its struct left in `s11` and its address in `s2`. -/
theorem kzeroref_80004e68 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {A B : List NumObj} {z : NumObj}
    (hb : BcHeap S M H F (A ++ z :: B))
    (hz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p) (hzo : ∀ a, constBytes a → S a)
    (hr : z.rep.refs + 1 < 2 ^ 31)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [14, 18, 27] R' R →
      BcHeap S M' H F (A ++ z.withRefs (z.rep.refs + 1) :: B) →
      R' 27 = BitVec.ofNat 64 z.rep.p → R' 18 = BitVec.ofNat 64 zeroAddr →
      (∀ a, a < z.rep.p + 12 ∨ z.rep.p + 16 ≤ a → imgM M' a = imgM M a) →
      DW live S Q 0x80004e80#64 R' M') :
    DW live S Q 0x80004e68#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hzn := hb.nums _ (List.mem_append_right _ List.mem_cons_self)
  num_facts hzn
  have hrf := hzn.refs
  have hcst : ∀ b ∈ accAddrs 2147601864 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact hzo b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  have hsx := sxw_ofNat (show z.rep.refs < 2 ^ 31 by omega)
  have hsx1 := sxw_ofNat (show z.rep.refs + 1 < 2 ^ 31 by omega)
  simp only [zeroAddr] at hz
  bc_run hlive hS [hz, hrf, hsx, hsx1] at 0x80004e80
  all_goals try (exact hcst)
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr, zeroAddr] at *; omega)
  refine hnext _ _ (by keeps_tac Keeps.refl _ _)
    (hb.setRefs (toNat_ofNat_mod32 (by omega)) (by omega)) (by bsimp [hz])
    (by bsimp [zeroAddr]) ?_
  exact fun a ha => imgM_store_miss _ _ (by omega)

end Dc.Mach
