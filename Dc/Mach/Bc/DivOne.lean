import Dc.Mach.Bc.DivLink

/-!
# `bc_divide`'s divide-by-one detour (`0x80005e54`)

GNU bc 1.07's `bc_divide` builds `n1` truncated to `scale` as the quotient
when `n2` is `1`, stores it in the slot, and then falls through into the
general division (no `return`), which frees that quotient and stores its own.

- `FreedRest.keep`: an operand survives freeing the slot's old number.
- `DivKW.rebase`: the continuations with the detour's quotient in the slot.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

/-- **An operand survives** freeing `x` when it is not `x` or `x` keeps a
reference: the same representation up to the reference count. -/
theorem FreedRest.keep {L1 L2 L : List NumObj} {x y : NumObj} (h : FreedRest L1 L2 x L)
    (hy : y ∈ L1 ++ x :: L2) (hok : x.rep.refs = 1 → y ≠ x) :
    ∃ y' ∈ L, ∃ r, y'.rep = { y.rep with refs := r } := by
  have hy' : y = x ∨ y ∈ L1 ++ L2 := by
    rcases List.mem_append.mp hy with h1 | h1
    · exact .inr (List.mem_append_left _ h1)
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact .inl h2
      · exact .inr (List.mem_append_right _ h2)
  cases h with
  | dec h2 =>
    rcases hy' with rfl | h1
    · exact ⟨y.decRef, List.mem_append_right _ List.mem_cons_self, _, rfl⟩
    · refine ⟨y, ?_, y.rep.refs, rfl⟩
      rcases List.mem_append.mp h1 with h3 | h3
      · exact List.mem_append_left _ h3
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h3)
  | rel h1 =>
    rcases hy' with rfl | h3
    · exact absurd rfl (hok h1)
    · exact ⟨y, h3, y.rep.refs, rfl⟩

/-- **The continuations after the detour**: the slot holds `y` (one
reference), the old number's rest `L` is what freeing it left, and off the
heap, the slot and the window the memory is the entry's. -/
theorem DivKW.rebase {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {R0 : Nat → BitVec 64} {Mt0 Mt1 : Mem} {L1 L2 L : List NumObj} {x y : NumObj} {q sp W : Nat}
    {n : Option Num} (hk : DivKW live S Q R0 Mt0 L1 L2 x q sp W n) (hfr : FreedRest L1 L2 x L)
    (hy : y.rep.refs = 1) (hnn : n ≠ none)
    (hM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM Mt1 a = imgM Mt0 a) :
    DivKW live S Q R0 Mt1 [] L y q sp W n where
  ret m hm R' Mt' H F L' y' hkp h10 hp := hk.ret m hm R' Mt' H F L' y' hkp h10
    { heap := hp.heap
      rest := by
        cases hp.rest with
        | dec h2 => omega
        | rel _ => exact hfr
      num := hp.num
      norm := hp.norm
      pos := hp.pos
      refs := hp.refs
      owns := hp.owns
      slot := hp.slot
      out := fun a ho hs hf => (hp.out a ho hs hf).trans (hM a ho hs hf) }
  zero h := absurd h hnn
  oomW R' Mt' sp' h1 h2 h3 h4 := hk.oomW R' Mt' sp' h1 h2 h3 fun a ho hs hf =>
    (h4 a ho hs hf).trans (hM a ho hs hf)

end Dc.Mach
