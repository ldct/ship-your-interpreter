import Dc.Mach.DcFuncArm0
import Dc.Mach.DcInt
import Dc.Mach.DcStack

/-!
# `dc_func`'s arms that push an integer (M10)

`I`, `K`, `O` and `z` load an integer (a global, or `dc_tell_stackdepth`'s
count), then `dc_int2data` and `dc_push` it: `fn_i2d_push` from the call of
`dc_int2data`, the two call sites given as steps (`JalAt`, `JAt`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **`dc_push (dc_int2data (v))`** as `fn_i2d_push`, over handles `ex ++ hs`
whose front `ex` (strings the arm lost) is left to the caller's post. -/
theorem fn_i2d_pushE {al : Nat} {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {st : St} {M0 M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {sp W : Nat}
    {R0 R : Nat → BitVec 64} {ex : List GV} {p : Nat}
    {v : Int} (h : DcAt S M H F L C G (ex ++ hs) st) (hex : ex.length ≤ 2) (hxl : ex.length ≤ al)
    (hc : FnAt S sp W M0 R0 R M) (hW : 384 ≤ W) (ho : FnOom live S Q sp W M0)
    (hhs : (ex ++ hs).length ≤ 2 ^ 30) (hvlo : -2 ^ 31 < v) (hvhi : v < 2 ^ 31)
    (h10 : R 10 = BitVec.ofInt 64 v) (h1 : R 1 = BitVec.ofNat 64 (p + 4))
    (hp : (p + 4) % 4 = 0 ∧ p + 8 < 2 ^ 64)
    (hj1 : JalAt live S Q (p + 4) 0x80002da4) (hj2 : JAt live S Q (p + 8) 0x80000c10)
    (hk : FnK live S Q al t0 st (.ok (st.push (.num (Num.ofInt v)))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800026d8#64 R M := by
  obtain ⟨hp1, hp2⟩ := hp
  refine dc_int2data_spec hlive h hhs (hc.cf (Wc := 192) (by omega)) (hc.cab (by omega)) R h10 hc.r2
    (by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p + 4) (by omega)]; exact hp1)
    hvlo hvhi (fun R1 M1 H1 F1 L1 C1 g k1 hd hv h1' hout1 => ?_)
    (fun R1 M1 e2 hout1 => ?_)
  · have hc1 := hc.callS (Wc := 192) (by omega) ((k1.mono (by decide)).trans (Keeps.refl _ _))
      (k1.get 2 (by decide)) hout1
    rw [h1]
    refine hj1 _ R1 M1 fun R2 k2 e1 => ?_
    have hc2 := hc1.mod (R' := R2) (k2.mono (by decide))
    refine dc_push_spec hlive h1' hv (hc2.cf (Wc := 64) (by omega)) (hc2.cab (by omega)) R2
      ⟨by rw [k2.get 10 (by decide)]; exact hd.tag, by rw [k2.get 11 (by decide)]; exact hd.ptr⟩
      hc2.r2 (by rw [e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p + 4 + 4) (by omega)]; omega)
      (fun R3 M3 H3 c k3 h3 hout3 => ?_) (fun R3 M3 e3 hout3 => ?_)
    · have hc3 := hc2.callS (Wc := 64) (by omega) ((k3.mono (by decide)).trans (Keeps.refl _ _))
        (k3.get 2 (by decide)) hout3
      rw [e1]
      exact hj2 _ R3 M3 (fa_ok (st' := st.push (.num (Num.ofInt v))) hlive h3 hc3 hk (.ok _) hex
        (by simp; exact hxl) (StrPin.refl _ _))
    · exact hc2.oom ho (Wc := 64) (by omega) (by omega) (by omega) e3 fun a e1 e2 _ e4 => hout3 a e1 e2 e4
  · have hj : JAt live S Q 0x80002bcc 0x80001e74 := fun t R M k => by
      have htx : tohostAddr = 0x8001ad00 := rfl
      bc_run hlive hlive [] at 0x80001e74
      exact k
    exact hj _ R1 M1 (hc.oom ho (Wc := 192) (by omega) (by omega) (by omega) e2
      fun a e1 e2 _ e4 => hout1 a e1 e2 e4)

/-- **`dc_push (dc_int2data (v))`** from the call of `dc_int2data` (return
address `p + 4`, where `dc_push` is called; `p + 8` jumps to `DC_OKAY`). -/
theorem fn_i2d_push {al : Nat} {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {st : St} {M0 M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {sp W p : Nat}
    {R0 R : Nat → BitVec 64} {v : Int} (h : DcAt S M H F L C G hs st)
    (hc : FnAt S sp W M0 R0 R M) (hW : 384 ≤ W) (ho : FnOom live S Q sp W M0)
    (hhs : hs.length ≤ 2 ^ 30) (hvlo : -2 ^ 31 < v) (hvhi : v < 2 ^ 31)
    (h10 : R 10 = BitVec.ofInt 64 v) (h1 : R 1 = BitVec.ofNat 64 (p + 4))
    (hp : (p + 4) % 4 = 0 ∧ p + 8 < 2 ^ 64)
    (hj1 : JalAt live S Q (p + 4) 0x80002da4) (hj2 : JAt live S Q (p + 8) 0x80000c10)
    (hk : FnK live S Q al t0 st (.ok (st.push (.num (Num.ofInt v)))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800026d8#64 R M :=
  fn_i2d_pushE (ex := []) hlive h (by simp) (by simp) hc hW ho hhs hvlo hvhi h10 h1 hp hj1 hj2 hk

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {st : St} {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {G : DcG} {hs : List GV} {sp W : Nat} {R0 R : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

set_option hygiene false in
/-- The `jal dc_push` / `j DC_OKAY` pair after a `jal dc_int2data` at `p`. -/
macro "fn_i2d_sites" : tactic =>
  `(tactic| (
    · intro t R M k
      simp only [Nat.reduceAdd] at k ⊢
      have htx : tohostAddr = 0x8001ad00 := rfl
      bc_run hlive hlive [] at 0x80002da4
      exact k _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
    · intro t R M k
      simp only [Nat.reduceAdd]
      have htx : tohostAddr = 0x8001ad00 := rfl
      bc_run hlive hlive [] at 0x80000c10
      exact k))

/-- A small natural `n` pushed as a number. -/
theorem fa_global {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {p n : Nat}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 384 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length ≤ 2 ^ 30) (hn : n < 2 ^ 31)
    (h10 : R 10 = BitVec.ofNat 64 n) (h1 : R 1 = BitVec.ofNat 64 (p + 4))
    (hp : (p + 4) % 4 = 0 ∧ p + 8 < 2 ^ 64)
    (hj1 : JalAt live S Q (p + 4) 0x80002da4) (hj2 : JAt live S Q (p + 8) 0x80000c10)
    (hk : FnK live S Q al t0 st (.ok (st.push (.num (Num.ofInt n)))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800026d8#64 R M :=
  fn_i2d_push hlive h hc hW ho hhs (by omega) (by omega) (by rw [h10, BitVec.ofInt_natCast]) h1 hp
    hj1 hj2 hk

/-- `K` (`0x80000ca4`): push `dc_scale`. -/
theorem fa_K {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 384 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length ≤ 2 ^ 30)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 75 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000ca4#64 R M := by
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hg := h.glob
  have hv : ldv .lw M 0x8001cd8c = BitVec.ofNat 64 st.scale := h.view.scale
  bc_run hlive hS [hv] at 0x800026d8
  refine fa_global (p := 0x80000cac) hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hW ho hhs
    h.den.scale (by bsimp []) (by bsimp []) (by decide) ?_ ?_ hk
  fn_i2d_sites

/-- `I` (`0x80000cb8`): push `dc_ibase`. -/
theorem fa_I {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 384 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length ≤ 2 ^ 30)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 73 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000cb8#64 R M := by
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hg := h.glob
  have hv : ldv .lw M 0x8001cd38 = BitVec.ofNat 64 st.ibase := h.view.ibase
  bc_run hlive hS [hv] at 0x800026d8
  refine fa_global (p := 0x80000cc0) hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hW ho hhs
    (by have := h.den.ibase; omega) (by bsimp []) (by bsimp []) (by decide) ?_ ?_ hk
  fn_i2d_sites

/-- `O` (`0x80000f1c`): push `dc_obase`. -/
theorem fa_O {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 384 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length ≤ 2 ^ 30)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 79 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000f1c#64 R M := by
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hg := h.glob
  have hv : ldv .lw M 0x8001cd34 = BitVec.ofNat 64 st.obase := h.view.obase
  bc_run hlive hS [hv] at 0x800026d8
  refine fa_global (p := 0x80000f24) hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hW ho hhs
    h.den.obase.2 (by bsimp []) (by bsimp []) (by decide) ?_ ?_ hk
  fn_i2d_sites

/-- `z` (`0x800011c0`): push the stack depth. -/
theorem fa_z {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 384 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length ≤ 2 ^ 30)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 122 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800011c0#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hlen : st.stack.length < 2 ^ 31 := by
    have := h.stk_len; have := h.den.stk.length_eq; omega
  bc_run hlive hlive [] at 0x800037e0
  refine dc_tell_stackdepth_spec hlive h _ (by bsimp []) fun R1 k1 e10 => ?_
  bsimp []
  bc_run hlive hlive [] at 0x800026d8
  refine fa_global (p := 0x800011c4) hlive h
    (hc.mod (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))) hW ho hhs
    hlen (by bsimp [e10]) (by bsimp []) (by decide) ?_ ?_ hk
  fn_i2d_sites

end

end Dc.Mach
