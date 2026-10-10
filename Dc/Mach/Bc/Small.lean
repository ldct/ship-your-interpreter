import Dc.Mach.Bc.Base

/-!
# `bc_copy_num`, `bc_init_num`, `bc_is_neg` (`lib/number.c`)

```
800049ac lw a5,12(a0) ; 800049b0 addiw a5,a5,1 ; 800049b4 sw a5,12(a0) ; 800049b8 ret
800049bc auipc a5,0x18 ; 800049c0 ld a5,1036(a5) (_zero_) ; 800049c4 lw a4,12(a5)
800049c8 addiw a4,a4,1 ; 800049cc sw a4,12(a5) ; 800049d0 sd a5,0(a0) ; 800049d4 ret
80004a00 lw a0,0(a0) ; 80004a04 addi a0,a0,-1 ; 80004a08 seqz a0,a0 ; 80004a0c ret
```

`bc_copy_num` and `bc_init_num` share a number by raising its reference
count (the object is otherwise unchanged); `bc_is_neg` reads the sign.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The bytes of `n_refs`. -/
abbrev refsBytes (o : NumRep) (a : Nat) : Prop := o.p + 12 ≤ a ∧ a < o.p + 16

/-- **`bc_copy_num(num)`** at `0x800049ac`: the reference count of the object
at `num` goes up by one; returns `num`; clobbers `a5`. -/
theorem bc_copy_num_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o)
    (hr : o.refs + 1 < 2 ^ 31)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 o.p) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [15] R' R → NumAt Mt' { o with refs := o.refs + 1 } →
      MemOnly (refsBytes o) Mt' Mt → DW live S Q (R 1) R' Mt') :
    DW live S Q 0x800049ac#64 R Mt := by
  num_facts h
  have hrf := h.refs
  dx_run hlive
  all_goals bsimp [h10, hrf, sxw_ofNat]
  all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
  exact hk _ _ (by keeps_tac Keeps.refl _ _) (h.setRefs (toNat_ofNat_mod32 (by omega)) hr)
    fun a ha => imgM_store_miss _ _ (by simp only [refsBytes] at ha; omega)

/-- **`bc_is_neg(num)`** at `0x80004a00`: `a0` is `1` for a negative sign,
else `0`. -/
theorem bc_is_neg_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {o : NumRep} (h : NumAt Mt o)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 o.p) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10] R' R → R' 10 = boolWord o.neg → DW live S Q (R 1) R' Mt) :
    DW live S Q 0x80004a00#64 R Mt := by
  num_facts h
  have hsg := h.sign
  dx_run hlive
  all_goals bsimp [h10, hsg]
  all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) ?_
  bsimp []
  cases o.neg <;> decide

/-- `_zero_` holds the object `z`: the word at `zeroAddr` and its ownership. -/
structure ZeroGlob (S : Nat → Prop) (Mt : Mem) (z : NumRep) : Prop where
  own : ∀ b, 0x8001cdc8 ≤ b → b < 0x8001cdd0 → S b
  word : ldv .ld Mt zeroAddr = BitVec.ofNat 64 z.p

/-- **`bc_init_num(num)`** at `0x800049bc` for a slot `q` off `_zero_`'s
object `z`: `*q = _zero_` and `z`'s reference count goes up by one; clobbers
`a4`, `a5`. -/
theorem bc_init_num_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {z : NumRep} (h : NumAt Mt z)
    (hzg : ZeroGlob S Mt z) (hr : z.refs + 1 < 2 ^ 31) {q : Nat} (hq : PtrSlot S q)
    (hqz : ∀ i, i < 8 → ¬ z.Foot (q + i))
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [14, 15] R' R → NumAt Mt' { z with refs := z.refs + 1 } →
      ldv .ld Mt' q = BitVec.ofNat 64 z.p →
      MemOnly (fun a => refsBytes z a ∨ (q ≤ a ∧ a < q + 8)) Mt' Mt → DW live S Q (R 1) R' Mt') :
    DW live S Q 0x800049bc#64 R Mt := by
  num_facts h
  have hrf := h.refs
  have hzw := hzg.word
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hzq : q + 8 ≤ z.p + 12 ∨ z.p + 16 ≤ q := by
    rcases Nat.lt_or_ge q (z.p + 12) with h1 | h1
    · refine .inl (Classical.byContradiction fun h2 => hqz (z.p + 12 - q) (by omega) (.inl ?_))
      omega
    · refine .inr (Classical.byContradiction fun h2 => hqz 0 (by omega) (.inl ?_))
      omega
  -- the `ld` of `_zero_` by `st_` (its `.rodata` variant is not decidable here)
  dx_run hlive at 0x800049c0
  apply st_800049c0 hlive
  · bsimp []; bc_addr
  · bsimp []; intro b hb; have := of_mem_accAddrs hb; exact hzg.own b (by omega) (by omega)
  dx_run hlive
  all_goals bsimp [h10, hrf, hzw, sxw_ofNat]
  all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | exact hq.acc | skip
  · refine hk _ _ (by keeps_tac Keeps.refl _ _) ?_ (ldv_store_hit _ _ _) ?_
    · refine (h.setRefs (toNat_ofNat_mod32 (by omega)) hr).frame fun a ha => ?_
      refine imgM_store_miss _ _ ?_
      rcases Classical.em (q ≤ a ∧ a < q + 8) with h1 | h1
      · exact absurd (show z.Foot (q + (a - q)) by rw [Nat.add_sub_cancel' h1.1]; exact ha)
          (hqz _ (by omega))
      · omega
    · intro a ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]

end Dc.Mach
