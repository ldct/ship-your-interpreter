import Dc.Mach.DcFuncPop
import Dc.Mach.DcFuncArm1
import Dc.Mach.DcRotate
import Dc.Mach.DcTell

/-!
# `dc_func`'s stack-shape arms (M10)

`r` (`dc_stack_rotate (2)`) and `X` (`dc_tell_scale` of a popped number, `0`
for a string, then `dc_int2data` and `dc_push`). Generic pieces: `FnK.okIdx`
(an `.ok` continuation moved to another start state and ghost with the same
lost references and strings), `fn_pop0` (`fn_pop` with `a0 = 0` on the popped
route), `fn_i2d_pushE` (`fn_i2d_push` over handles `ex ++ hs`, the front lost
to the caller's post: `X` on a string never frees it), and `StkLinks.off`.
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
theorem FnK.okIdx {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t0 : String} {st1 st2 s : St} {G G2 : DcG} {hs : List GV} {sp W : Nat} {M0 : Mem}
    {R0 : Nat → BitVec 64} (hk : FnK live S Q t0 st1 (.ok s) G hs sp W M0 R0)
    (hl : G2.lk = G.lk) (hst : G2.strs = G.strs) :
    FnK live S Q t0 st2 (.ok s) G2 hs sp W M0 R0 :=
  fun R' M' H' F' L' C' G' code st' ex k e2 e10 hf hp =>
    hk R' M' H' F' L' C' G' code st' ex k e2 e10 (by cases hf; exact .ok _)
      ⟨hp.dc, hp.ex, hl ▸ hp.lk, hst ▸ hp.pin, hp.out⟩

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t : String} {st : St} {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {G : DcG} {hs : List GV} {sp W : Nat} {R0 R : Nat → BitVec 64}

/-- **`dc_pop (&datum)`** as `fn_pop`, the popped route also given `a0 = 0`
(`DC_SUCCESS`, which `X` passes on to `dc_int2data`). -/
theorem fn_pop0 (hlive : ∀ p ∈ dcText, live p.1) {p tgt0 : Nat}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (h10 : R 10 = BitVec.ofNat 64 (fnSlot sp)) (hp : (p + 4) % 4 = 0 ∧ p + 4 < 2 ^ 64)
    (hj : JalAt live S Q p 0x8000310c) (hb : BnezAt live S Q (p + 4) tgt0)
    (hempty : st.stack = [] → ∀ R' M', FnAt S sp W M0 R0 R' M' → DcAt S M' H F L C G hs st →
      DWO live S Q t (BitVec.ofNat 64 tgt0) R' M')
    (hne : ∀ R' M' H' (G' : DcG) g v st', st = st'.push v →
      (∃ c, G = { G' with stk := (c, g) :: G'.stk }) → FnAt S sp W M0 R0 R' M' →
      DcAt S M' H' F L C G' (g :: hs) st' → g.Den ⟨L, G'.strs⟩ v → DatAt M' (fnSlot sp) g →
      R' 10 = 0#64 → DWO live S Q t (BitVec.ofNat 64 (p + 8)) R' M') :
    DWO live S Q t (BitVec.ofNat 64 p) R M := by
  refine hj t R M fun R1 k1 e1 => ?_
  have hc1 := hc.mod (k1.mono (by decide))
  refine dc_pop_spec hlive h (hc1.cf (Wc := 336) hW) (hc1.cab hW) hc1.slot R1
    (by rw [k1.get 10 (by decide)]; exact h10) hc1.r2
    (by rw [e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp.2]; exact hp.1)
    (fun R' M' H' G' g v st' est eG k2 e10 h' hd hout => ?_)
    (fun he R' M' k2 e10 h' hout => ?_)
  · rw [e1]
    have hc2 := hc1.popped hW k2 hout
    have hv : g.Den ⟨L, G'.strs⟩ v := by
      obtain ⟨c, rfl⟩ := eG
      have hden := h.den.stk
      subst est
      cases hden with | cons hh _ => exact hh
    refine hb t R' M' (fun hne' => absurd e10 hne') fun _ => ?_
    exact hne R' M' H' G' g v st' est eG hc2 h' hv hd e10
  · rw [e1]
    exact hb t R' M' (fun _ => hempty he R' M' (hc1.popped hW k2 hout) h')
      fun e => absurd (e10.symm.trans e) (by decide)

/-- **`dc_push (dc_int2data (v))`** as `fn_i2d_push`, over handles `ex ++ hs`
whose front `ex` (strings the arm lost) is left to the caller's post. -/
theorem fn_i2d_pushE (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {ex : List GV} {p : Nat}
    {v : Int} (h : DcAt S M H F L C G (ex ++ hs) st) (hex : ex.length ≤ 2)
    (hc : FnAt S sp W M0 R0 R M) (hW : 384 ≤ W) (ho : FnOom live S Q sp W M0)
    (hhs : (ex ++ hs).length ≤ 2 ^ 30) (hvlo : -2 ^ 31 < v) (hvhi : v < 2 ^ 31)
    (h10 : R 10 = BitVec.ofInt 64 v) (h1 : R 1 = BitVec.ofNat 64 (p + 4))
    (hp : (p + 4) % 4 = 0 ∧ p + 8 < 2 ^ 64)
    (hj1 : JalAt live S Q (p + 4) 0x80002da4) (hj2 : JAt live S Q (p + 8) 0x80000c10)
    (hk : FnK live S Q t0 st (.ok (st.push (.num (Num.ofInt v)))) G hs sp W M0 R0) :
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
        (by simp) (StrPin.refl _ _))
    · exact hc2.oom ho (Wc := 64) (by omega) (by omega) (by omega) e3 fun a e1 e2 _ e4 => hout3 a e1 e2 e4
  · have hj : JAt live S Q 0x80002bcc 0x80001e74 := fun t R M k => by
      have htx : tohostAddr = 0x8001ad00 := rfl
      bc_run hlive hlive [] at 0x80001e74
      exact k
    exact hj _ R1 M1 (hc.oom ho (Wc := 192) (by omega) (by omega) (by omega) e2
      fun a e1 e2 _ e4 => hout1 a e1 e2 e4)

end

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {st : St} {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {G : DcG} {hs : List GV} {sp W : Nat} {R0 R : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- `r` (`0x80000ef4`): `dc_stack_rotate (2)`, `DC_OKAY`. -/
theorem fa_r (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q t0 st (dcFunc 70 st 114 peek neg) G hs sp W M0 R0) :
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
theorem fa_X (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length + 1 ≤ 2 ^ 30)
    (hk : FnK live S Q t0 st (dcFunc 70 st 88 peek neg) G hs sp W M0 R0) :
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
      refine fn_i2d_pushE (ex := []) (p := 0x80000fd4) (hs := hs) (st := st1) (v := (x.rep.scale : Int)) hlive h2 (by simp)
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
      refine fn_i2d_pushE (ex := [.str q]) (p := 0x80000fd4) (hs := hs) (st := st1) (v := 0) hlive h1 (by simp)
        (hc1.mod (by keeps_tac Keeps.refl _ _)) (by omega) ho (by simp; omega) (by omega) (by omega)
        (by bsimp [e10]; rfl) (by bsimp []) (by decide) ?_ ?_ (hk.okIdx rfl rfl)
      fn_i2d_sites

end

end Dc.Mach
