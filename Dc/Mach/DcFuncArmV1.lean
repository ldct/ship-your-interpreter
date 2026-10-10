import Dc.Mach.DcFuncPop
import Dc.Mach.DcFuncArm1
import Dc.Mach.DcRotate
import Dc.Mach.DcTell

/-!
# `dc_func`'s stack-shape arms (M10)

`r` (`dc_stack_rotate (2)`) and `X` (`dc_tell_scale` of a popped number, `0`
for a string, then `dc_int2data` and `dc_push`). Generic pieces: `FnK.okIdx`
(an `.ok` continuation moved to another start state and ghost with the same
lost references and strings) and `StkLinks.off`; `X` on a string never frees
it, so its handle goes to the post's `ex` (`fn_i2d_pushE`, `DcFuncArm1.lean`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The bytes a stack relink changes are none of `FnPost`'s. -/
theorem StkLinks.off {G : DcG} (g : StkGeo G) {a : Nat} (hl : StkLinks G a) (e1 : OutHeap a)
    (e2 : ¬ DcGlob a) : False := by
  rcases hl with hw | ⟨bg, hm, h1, h2⟩
  · exact e2 (by simp only [StkWord, DcGlob, dc_addrs] at hw ⊢; omega)
  · obtain ⟨b1, b2, -⟩ := g.bnd bg hm
    exact e1.1 ⟨by omega, by omega⟩


/-- `FnK` for `.ok s` depends neither on the state it started from nor on the
ghost beyond its lost references and strings. -/
theorem FnK.okIdx {al : Nat} {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t0 : String} {st1 st2 s : St} {G G2 : DcG} {hs : List GV} {sp W : Nat} {M0 : Mem}
    {R0 : Nat → BitVec 64} (hk : FnK live S Q al t0 st1 (.ok s) G hs sp W M0 R0)
    (hl : G2.lk = G.lk) (hst : G2.strs = G.strs) :
    FnK live S Q al t0 st2 (.ok s) G2 hs sp W M0 R0 :=
  fun R' M' H' F' L' C' G' code st' ex k e2 e10 hf hp =>
    hk R' M' H' F' L' C' G' code st' ex k e2 e10 (by cases hf; exact .ok _)
      ⟨hp.dc, hl ▸ hp.lk, hp.ex, hst ▸ hp.pin, hp.out⟩

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {st : St} {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {G : DcG} {hs : List GV} {sp W : Nat} {R0 R : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- `r` (`0x80000ef4`): `dc_stack_rotate (2)`, `DC_OKAY`. -/
theorem fa_r {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 114 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000ef4#64 R M := by
  have hr : dcFunc 70 st 114 peek neg = .ok { st with stack := rotate 2 st.stack } := rfl
  rw [hr] at hk
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hg := h.stkGeo
  bc_run hlive hlive [] at 0x80003768
  refine dc_stack_rotate_spec hlive h (n := 2) (by decide) (by decide) _ (by bsimp []; rfl)
    (by bsimp []) fun R1 M1 l' k1 _ hm h1 => ?_
  bsimp []
  bc_run hlive hlive [] at 0x80000c10
  have hc1 := (hc.mod (R' := R1) (by keeps_tac ((k1.mono (by decide)).trans
    (by keeps_tac Keeps.refl _ _)))).call (Wc := 0) (M' := M1) (by have := hc.big; omega)
    (Keeps.refl _ _) rfl fun a e1 e2 _ _ => hm a fun hl => StkLinks.off hg hl e1 e2
  exact fa_ok (st' := { st with stack := rotate 2 st.stack }) hlive (ex := []) h1 hc1 hk (.ok _) (by simp) (by simp) (StrPin.refl _ _)

set_option hygiene false in
/-- The `jal dc_pop` / `bnez a0` pair at `p`, `p + 4` from the generated steps. -/
macro "fn_pop_sites " p:ident b:ident : tactic =>
  `(tactic| (
    · exact JalAt.of_step fun t R M k => $p hlive k
    · exact BnezAt.of_step fun t R M k1 k2 => $b hlive k1 k2))

/-- `X` (`0x80000fe0`): a popped number's scale, `0` for a string (its
reference lost), pushed. -/
theorem fa_X {al : Nat} (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length + 1 ≤ 2 ^ 30) (hal : 1 ≤ al)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 88 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000fe0#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := hc.r2
  bc_run hlive hlive [e2] at 0x80000fe4
  refine fn_pop0 (p := 0x80000fe4) (tgt0 := 0x80000c10) hlive h (hc.mod (by keeps_tac Keeps.refl _ _))
    (by omega) (by bsimp []) (by decide) ?_ ?_ ?_ ?_
  fn_pop_sites st_80000fe4 st_80000fe8
  · intro he R1 M1 hc1 h1
    have hr : dcFunc 70 st 88 peek neg = .ok st := by
      cases st with | mk stk => simp only at he; subst he; rfl
    rw [hr] at hk
    exact fa_ok hlive (ex := []) h1 hc1 hk (.ok _) (by simp) (by simp) (StrPin.refl _ _)
  · intro R1 M1 H1 G1 g v st1 est eG hc1 h1 hv hd e10
    subst est
    obtain ⟨c, rfl⟩ := eG
    simp only [Nat.reduceAdd]
    have hsf : StackFrame S sp 192 := hc1.frame.mono hc1.big
    have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
    have hab := hc1.room; simp only [heapEnd] at hab
    have e21 := hc1.r2
    have htg := hd.lw
    have hpt := hd.ptr
    simp only [fnSlot] at htg hpt
    rw [show sp - 192 + 16 + 8 = sp - 192 + 24 by omega] at hpt
    cases g with
    | num xp =>
      cases v with
      | str _ => exact hv.elim
      | num n =>
      obtain ⟨x, hx, rfl, rfl⟩ := hv
      have hr : dcFunc 70 (st1.push (.num x.rep.num)) 88 peek neg =
          .ok (st1.push (.num (Num.ofInt (x.rep.scale : Int)))) := rfl
      rw [hr] at hk
      simp only [GV.tag, GV.ptr] at htg hpt
      bc_run hlive hlive [e21, htg, hpt] at 0x80002a04
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      bc_run hlive hlive [e21, htg, hpt] at 0x80002a04
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      refine dc_tell_scale_spec hlive h1 hx (hc1.cf (Wc := 64) (by omega)) (hc1.cab (by omega)) _
        (by bsimp [e21]) (by bsimp []) (by bsimp []) (by bsimp []) fun R2 M2 H2 F2 L2 C2 k2 e22 e102 h2 hout2 => ?_
      have hc3 := hc1.callS (R' := R2) (Wc := 64) (by omega)
        (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
        (e22.trans (by bsimp [e21])) hout2
      bsimp []
      bc_run hlive hlive [] at 0x800026d8
      have hsz := (h1.heap.nums x hx).shape.size
      refine fn_i2d_pushE (ex := []) (p := 0x80000fd4) (hs := hs) (st := st1) (v := (x.rep.scale : Int)) hlive h2 (by simp) (by simp)
        (hc3.mod (by keeps_tac Keeps.refl _ _)) (by omega) ho (by simp; omega) (by omega) (by omega)
        (by bsimp [e102]; rw [BitVec.ofInt_natCast]) (by bsimp []) (by decide) ?_ ?_ (hk.okIdx rfl rfl)
      fn_i2d_sites
    | str q =>
      cases v with
      | num _ => exact hv.elim
      | str s =>
      have hr : dcFunc 70 (st1.push (.str s)) 88 peek neg =
          .ok (st1.push (.num (Num.ofInt 0))) := rfl
      rw [hr] at hk
      simp only [GV.tag, GV.ptr] at htg hpt
      bc_run hlive hlive [e21, htg] at 0x800026d8
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      bc_run hlive hlive [e21, htg] at 0x800026d8
      refine fn_i2d_pushE (ex := [.str q]) (p := 0x80000fd4) (hs := hs) (st := st1) (v := 0) hlive h1 (by simp) (by simp; omega)
        (hc1.mod (by keeps_tac Keeps.refl _ _)) (by omega) ho (by simp; omega) (by omega) (by omega)
        (by bsimp [e10]; rfl) (by bsimp []) (by decide) ?_ ?_ (hk.okIdx rfl rfl)
      fn_i2d_sites

end

end Dc.Mach
