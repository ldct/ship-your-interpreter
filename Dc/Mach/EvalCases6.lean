import Dc.Mach.EvalCases5

/-!
# `evalstr`'s loop: `DC_EVALREG`'s span (M10)

`DC_EVALREG` (`0x800016d8`, frame `sp`, the register name the lookahead
word at `sp + 28`): `dc_register_get (peekc, sp + 32)`, `s0` two on; with a
value, `dc_push` of it and the `DC_EVALTOS` code (`0x80001748`); without,
the test at `0x800015a0`. `RegOut`: the bytes the span changes are in the
callees' frames and the slot `sp + 32`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The bytes `DC_EVALREG`'s span leaves as they were: all but the 336
bytes below `sp` and the slot `sp + 32`. -/
def RegOut (sp : Nat) (M' M : Mem) : Prop :=
  ∀ a, OutHeap a → ¬ (DcGlob a ∧ ¬ PinWords a) → ¬ frameIn sp 336 a → (a < sp + 32 ∨ sp + 32 + 16 ≤ a) →
    imgM M' a = imgM M a

/-- **`DC_EVALREG`'s span** at `0x800016d8`. -/
theorem rt_reg {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t : String} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {sp p : Nat}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) (hp : p < 256)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp (sp + 32))
    (hown : ∀ b, sp ≤ b → b < sp + 88 → S b) {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp)
    (hpk : ldv .lw M (sp + 28) = BitVec.ofNat 64 p)
    (hsome : ∀ R2 M2 H2 F2 L2 C2 Gp c g v, regGet st p = some v →
      Keeps (8 :: 12 :: 25 :: cClob) R2 R → R2 8 = R 8 + 2#64 →
      R2 25 = BitVec.ofNat 64 (sp + 32) → SameNodes G Gp →
      DcAt S M2 H2 F2 L2 C2 { Gp with stk := (c, g) :: Gp.stk } hs (st.push v) →
      StrPin G.strs Gp.strs hs → RegOut sp M2 M → DWO live S Q t 0x80001748#64 R2 M2)
    (hnone : regGet st p = none → ∀ R2 M2 H2, Keeps (8 :: 12 :: 25 :: cClob) R2 R →
      R2 8 = R 8 + 2#64 → R2 12 = 0#64 → DcAt S M2 H2 F L C G hs st → RegOut sp M2 M →
      DWO live S Q t 0x800015a0#64 R2 M2)
    (hoom : ∀ R' M' sp', sp - 336 ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' → sp' % 16 = 0 →
      RegOut sp M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x800016d8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hq32 : BitVec.ofNat 64 sp + 32#64 = BitVec.ofNat 64 (sp + 32) := by
    rw [show (32#64) = BitVec.ofNat 64 32 from rfl, BitVec.ofNat_add_ofNat]
  bc_run hlive hS [h2, hpk, hq32] at 0x80002f18
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | skip
  refine dc_register_get_spec hlive h hhs hp hsf hab hq _ (by bsimp []) (by bsimp [])
    (by bsimp [h2]) (by bsimp [])
    (fun R3 M3 H3 F3 L3 C3 G3 g v hg k3 e3 hsn h3 hgv hd3 hgo hpin3 => ?_)
    (fun hg R3 M3 k3 e3 h3 hgo => ?_) (fun R3 M3 sp3 l1 l2 e2 hal3 hgo => ?_)
  · -- a value: `dc_push` of the slot's datum
    have e32 : R3 2 = BitVec.ofNat 64 sp := by rw [k3.get 2 (by decide)]; bsimp [h2]
    have ht := hd3.tag; have hpt := hd3.ptr
    bsimp []
    bc_run hlive hS [e3, e32, hq32] at 0x80002da4
    all_goals first
      | exact frame_acc hsf (by omega) (by omega)
      | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
      | skip
    all_goals first | (intro hc; exact absurd hc (by decide)) | intro _ | skip
    bc_run hlive hS [e3, e32, hq32] at 0x80002da4
    all_goals first
      | exact frame_acc hsf (by omega) (by omega)
      | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
      | skip
    refine dc_push_spec hlive h3 hgv (hsf.mono (by omega)) (by omega) _
      ⟨by bsimp []; exact ht, by bsimp [show sp + 32 + 8 = sp + 40 by omega] at hpt ⊢; exact hpt⟩
      (by bsimp [e32]) (by bsimp []) (fun R4 M4 H4 c k4 h4 hso4 => ?_)
      (fun R4 M4 e4 hso4 => hoom R4 M4 (sp - 64) (by omega) (by omega) e4 (by omega)
        fun a e1 e2 e3 e5 => (hso4 a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))).trans
          (hgo a e1 e2 e3 e5))
    bsimp []
    bc_run hlive hS [] at 0x80001748
    exact hsome _ M4 H4 F3 L3 C3 G3 c g v hg
      (by keeps_tac ((k4.mono (by decide)).trans (by keeps_tac ((k3.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))))
      (by bsimp []; rw [k4.get 8 (by decide)]; bsimp []; rw [k3.get 8 (by decide)]; bsimp [])
      (by bsimp []; rw [k4.get 25 (by decide)]; bsimp []; rw [k3.get 25 (by decide)]; bsimp [hq32])
      hsn h4 hpin3
      fun a e1 e2 e3 e5 => (hso4 a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))).trans
        (hgo a e1 e2 e3 e5)
  · -- none: the test at `0x800015a0`
    bsimp []
    bc_run hlive hS [e3] at 0x800015a0
    all_goals first | (intro _; skip) | skip
    exact hnone hg _ M3 H (by keeps_tac ((k3.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (by bsimp []; rw [k3.get 8 (by decide)]; bsimp []) (by bsimp []) h3 hgo
  · -- out of memory: `out_of_memory` jumps to `dc_memfail`
    bc_run hlive hS [] at 0x80001e74
    exact hoom _ M3 sp3 l1 l2 (by bsimp [e2]) hal3 hgo

end Dc.Mach
