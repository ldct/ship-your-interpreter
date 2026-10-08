import Dc.Mach.Bc.KaraNew

/-!
# `_bc_rec_mul`'s Karatsuba step: the recursive calls

- `rmDepth`/`rmStack`: the recursion depth for `ulen + vlen = N` (each
  Karatsuba level at most `3N/4 + 1`), and the stack window it needs.
- `KZero`: `_zero_` (one digit `0`, its pointer at `zeroAddr`) with room for
  more references.
- `RmIH N`: `_bc_rec_mul`'s contract for operands of `N` digits together or
  fewer — the induction hypothesis.
- `kara_child`: a call of `_bc_rec_mul` from the step's frame into one of its
  slots, by `RmIH`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- The Karatsuba levels below operands of `N` digits together. -/
def rmDepth (N : Nat) : Nat := if N < 80 then 0 else 1 + rmDepth (3 * N / 4 + 1)
termination_by N
decreasing_by omega

theorem rmDepth_step {N : Nat} (h : ¬ N < 80) : rmDepth N = 1 + rmDepth (3 * N / 4 + 1) := by
  rw [rmDepth]; simp only [h, if_false]

theorem rmDepth_mono : ∀ {a b : Nat}, a ≤ b → rmDepth a ≤ rmDepth b := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | _ b ih =>
    intro hab
    by_cases ha : a < 80
    · have : rmDepth a = 0 := by rw [rmDepth]; simp only [ha, if_true]
      omega
    · rw [rmDepth_step ha, rmDepth_step (show ¬ b < 80 by omega)]
      exact Nat.add_le_add_left (ih (3 * b / 4 + 1) (by omega) (a := 3 * a / 4 + 1) (by omega)) 1

/-- The stack window `_bc_rec_mul` needs below its `sp`. -/
def rmStack (N : Nat) : Nat := 224 + 192 * rmDepth N

/-- A child of a Karatsuba level of `N` digits needs `192` bytes less. -/
theorem rmStack_child {N N' : Nat} (h80 : ¬ N < 80) (hN : N' ≤ 3 * N / 4 + 1) :
    rmStack N' + 192 ≤ rmStack N := by
  have := rmDepth_mono hN
  have := rmDepth_step h80
  simp only [rmStack]; omega

/-- `_zero_`: one digit `0`, owner, pointer at `zeroAddr`, room for `k` more
references. -/
structure KZero (M : Mem) (z : NumObj) (k : Nat) : Prop where
  glob : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p
  len : z.rep.len = 1
  scale : z.rep.scale = 0
  ds : z.rep.ds = [0]
  refs : 1 ≤ z.rep.refs
  room : z.rep.refs + k < 2 ^ 31

/-- **`_bc_rec_mul`'s contract** for operands of `N` digits together or
fewer: the induction hypothesis. -/
def RmIH (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (N : Nat) :
    Prop :=
  ∀ (R0 : Nat → BitVec 64) (M : Mem) (sp q W la lb : Nat) (A B : List NumObj)
    (z uo vo : NumObj) (H : Heap) (F : List Blk),
    la + lb ≤ N → rmStack (la + lb) ≤ W → KZero M z (4 * (la + lb) + 8) →
    RmCtx S R0 sp q W → RmK live S Q R0 M (A ++ z :: B) uo.rep vo.rep la lb q sp W →
    RmArgs M (A ++ z :: B) uo vo la lb → BcHeap S M H F (A ++ z :: B) →
    R0 10 = BitVec.ofNat 64 uo.rep.p → R0 11 = BitVec.ofNat 64 la →
    R0 12 = BitVec.ofNat 64 vo.rep.p → R0 13 = BitVec.ofNat 64 lb →
    R0 14 = BitVec.ofNat 64 q → DW live S Q 0x80004bd0#64 R0 M

/-- **A recursive call** from the step's frame (`sp - 192`) into the slot
`sp - 192 + o`: the child's window is the rest of the step's. -/
theorem kara_child {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {N : Nat} (ih : RmIH live S Q N)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb la' lb' : Nat} {L : List NumObj}
    {u v : NumRep} {A B : List NumObj} {z uo vo : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L u v la lb q sp W)
    (st : RmAt S M0 M R0 R sp q W) (o : Nat) (ho : o + 8 ≤ 88) (hoa : o % 8 = 0)
    (hN : la' + lb' ≤ N) (hW : rmStack (la' + lb') + 192 ≤ W)
    (hz : KZero M z (4 * (la' + lb') + 8))
    (ha : RmArgs M (A ++ z :: B) uo vo la' lb') (hb : BcHeap S M H F (A ++ z :: B))
    (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 uo.rep.p) (h11 : R 11 = BitVec.ofNat 64 la')
    (h12 : R 12 = BitVec.ofNat 64 vo.rep.p) (h13 : R 13 = BitVec.ofNat 64 lb')
    (h14 : R 14 = BitVec.ofNat 64 (sp - 192 + o))
    (hret : ∀ R' M' H' F' y, Keeps binClob R' R →
      RmPost S M M' H' F' (A ++ z :: B) uo.rep vo.rep la' lb' (sp - 192 + o) (sp - 192) (W - 192) y →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80004bd0#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hWb := cx.big
  simp only [heapEnd] at hab
  have hst : 224 ≤ rmStack (la' + lb') := by simp only [rmStack]; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have ks := cx.kslot o (by omega) hoa
  refine ih R M (sp - 192) (sp - 192 + o) (W - 192) la' lb' A B z uo vo H F hN (by omega) hz
    ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
      by simp only [heapEnd]; omega, by omega,
      ⟨fun i hi => ks.own _ (mem_accAddrs (by omega)), by omega, by omega, by omega⟩,
      fun a ha => ks.out a ha.1 ha.2, .inr (by omega), cx.mulBase, cx.consts, st.r2, hal⟩
    ⟨hret, fun R' M' sp' h1 h2 hr2 hout => hk.oom R' M' sp' (by omega) (by omega) hr2
      fun a ha hs hf => by
        rw [hout a ha (fun h => hf (by simp only [slotBytes, frameIn] at h ⊢; omega))
          (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
        exact st.out a ha hs hf⟩
    ha hb h10 h11 h12 h13 h14

end Dc.Mach
