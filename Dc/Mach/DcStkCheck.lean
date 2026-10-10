import Dc.Mach.DcPop

/-!
# The two-node stack check (M9)

`dc_binop`, `dc_binop2` and `dc_cmpop` open with the same check:

    if (dc_stack == NULL || dc_stack->link == NULL) → "stack empty"
    if (top two types are not both DC_NUMBER)       → "non-numeric value"

- `DcAt.top2`: the state's stack read as the check reads it, in three cases
  (no node, one node, two nodes with their type words).
- The machine runs of the check are generated per site
  (`scripts/dc/gen_stk_check.py` → `DcStkCheckSites.lean`) over `DcAt.top2`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A stack node's payload in the heap, as the check's word loads need it. -/
abbrev NodePay (c : Blk) : Prop := 2147603936 ≤ c.pay ∧ c.pay + 32 ≤ 2273312768 ∧ c.pay % 16 = 0

/-- The stack does not hold two numbers on top. -/
def No2 (st : St) : Prop := ∀ b a rest, st.stack ≠ .num b :: .num a :: rest

/-- A stack node's payload in the heap. -/
theorem DcAt.stkPay {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {c : Blk} {g : GV} (hc : (c, g) ∈ G.stk) : NodePay c := by
  have hn := h.view.stk.forall _ hc
  have fbb := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live c (DcG.stk_mem hc)))
  have hblo : 2147603920 ≤ c.h := fbb.lo
  have hbhi : c.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : c.h % 16 = 0 := fbb.al
  have hbsz := hn.sz
  simp only [NodePay, Blk.pay, Blk.fin] at *; omega

theorem ofNat_pos_ne {p : Nat} (h1 : 0 < p) (h2 : p < 2 ^ 64) : BitVec.ofNat 64 p ≠ 0#64 :=
  fun hc => by
    have := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod] at this
    rw [Nat.mod_eq_of_lt h2] at this; omega

theorem NodePay.ne0 {c : Blk} (h : NodePay c) : BitVec.ofNat 64 c.pay ≠ 0#64 :=
  ofNat_pos_ne (by omega) (by omega)

theorem GV.tag_cases (g : GV) : g.tag = 1 ∨ g.tag = 2 := by cases g <;> simp [GV.tag]

/-- **The stack as the two-node check reads it.** -/
theorem DcAt.top2 {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) {P : Prop}
    (hnil : ldv .ld M dcStackAddr = 0#64 → No2 st → P)
    (hone : ∀ c1 : Blk, ldv .ld M dcStackAddr = BitVec.ofNat 64 c1.pay →
      ldv .ld M (c1.pay + 24) = 0#64 → NodePay c1 → No2 st → P)
    (htwo : ∀ (c1 c2 : Blk) (g1 g2 : GV) rest, G.stk = (c1, g1) :: (c2, g2) :: rest →
      ldv .ld M dcStackAddr = BitVec.ofNat 64 c1.pay →
      ldv .ld M (c1.pay + 24) = BitVec.ofNat 64 c2.pay →
      ldv .lw M c1.pay = BitVec.ofNat 64 g1.tag → ldv .lw M c2.pay = BitVec.ofNat 64 g2.tag →
      NodePay c1 → NodePay c2 → ((g1.tag ≠ 1 ∨ g2.tag ≠ 1) → No2 st) → P) : P := by
  have hden := h.den.stk
  have hv := h.view.stk
  cases hstk : G.stk with
  | nil =>
    rw [hstk] at hv hden
    cases hv with
    | nil h0 => exact hnil h0 fun b a rest e => by rw [e] at hden; cases hden
  | cons n1 rest1 =>
    obtain ⟨c1, g1⟩ := n1
    have hc1 := h.stkPay (c := c1) (g := g1) (by rw [hstk]; exact List.mem_cons_self)
    rw [hstk] at hv hden
    cases hv with
    | cons h0 hn1 hl1 =>
    cases rest1 with
    | nil =>
      cases hl1 with
      | nil hl0 =>
      exact hone c1 h0 hl0 hc1 fun b a rest e => by
        rw [e] at hden; cases hden with | cons _ hr => cases hr
    | cons n2 rest2 =>
      obtain ⟨c2, g2⟩ := n2
      have hc2 := h.stkPay (c := c2) (g := g2) (by rw [hstk]; simp)
      cases hl1 with
      | cons h0' hn2 hl2 =>
      refine htwo c1 c2 g1 g2 rest2 hstk h0 h0' hn1.dat.lw hn2.dat.lw hc1 hc2 fun hn b a rest e => ?_
      rw [e] at hden
      cases hden with
      | cons hh hr =>
      cases hr with
      | cons hh2 _ =>
      rcases hn with hn | hn
      · cases g1 with
        | num _ => exact hn rfl
        | str _ => exact hh
      · cases g2 with
        | num _ => exact hn rfl
        | str _ => exact hh2

end Dc.Mach
