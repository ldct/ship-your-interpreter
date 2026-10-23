import Dc.Mach.DcFuncArmV6
import Dc.Mach.DcDumpOut
import Dc.Mach.DcOutStr

/-!
# `dc_func`'s arms `Z` and `P` (M10)

`Z` pops a datum, `dc_tell_length (datum, DC_TOSS)` (a number's `numLen`, a
string's length), then `dc_int2data` and `dc_push`. `P` pops a datum and
prints a number's bytes (`dc_dump_num`) or a string (`dc_out_str`), both
releasing it, then `fflush (stdout)` and `DC_OKAY` (`fa_okF`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `FnK` for `.ok s` moved to another start state and to a ghost with no
more lost references whose strings keep the held ones (`StrPin`). -/
theorem FnK.okPin {al : Nat} {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t0 : String} {st1 st2 s : St} {G G2 : DcG} {hs : List GV} {sp W : Nat} {M0 : Mem}
    {R0 : Nat → BitVec 64} (hk : FnK live S Q al t0 st1 (.ok s) G hs sp W M0 R0)
    (hl : G2.lk.length ≤ G.lk.length) (hst : StrPin G.strs G2.strs hs) :
    FnK live S Q al t0 st2 (.ok s) G2 hs sp W M0 R0 :=
  fun R' M' H' F' L' C' G' code st' ex k e2 e10 hf hp =>
    hk R' M' H' F' L' C' G' code st' ex k e2 e10 (by cases hf; exact .ok _)
      ⟨hp.dc, by have := hp.lk; omega, hp.ex, hst.trans hp.pin, hp.out⟩

/-- `fflush (stdout)` then `DC_OKAY` (`0x80000c04`). -/
theorem fa_okF {al : Nat} {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {st st' : St} {r : Res} {M0 M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G G' : DcG} {hs ex : List GV} {sp W : Nat}
    {R0 R : Nat → BitVec 64} (h : DcAt S M H F L C G' (ex ++ hs) st') (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q al t0 st r G hs sp W M0 R0) (hf : FnOut st r 0 st') (hex : ex.length ≤ 2)
    (hlk : G'.lk.length + ex.length ≤ G.lk.length + al) (hpin : StrPin G.strs G'.strs hs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000c04#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hro : ∀ b ∈ accAddrs 2147516936 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hlive [stdout_word] at 0x8000070c
  refine fflush_spec hlive _ (by bsimp []) fun R1 k1 _ => ?_
  bsimp []
  exact fa_ok hlive h (hc.mod (by keeps_tac ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))
    hk hf hex hlk hpin

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {M0 : Mem} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {hs : List GV} {sp W : Nat} {R0 : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- A value's `Z` length fits an `int`. -/
theorem DcAt.zLen_lt {M : Mem} {H : Heap} {G : DcG} {g : GV} {v : Val} {st : St}
    (h : DcAt S M H F L C G hs st) (hv : g.Den ⟨L, G.strs⟩ v) : v.zLen < 2 ^ 31 := by
  cases g with
  | num p =>
    cases v with
    | str _ => exact hv.elim
    | num n =>
      obtain ⟨x, hx, -, rfl⟩ := hv
      have hn := h.heap.nums x hx
      have hp := h.den.pos x hx
      have hsz := hn.shape.size
      have e : x.rep.num.numLen = x.rep.len + x.rep.scale - lzCount (x.rep.len + x.rep.scale - 1) x.rep.ds :=
        numLen_rep hn.shape.dig hn.shape.dsLen (by omega) x.rep.neg x.rep.scale
      show x.rep.num.numLen < 2 ^ 31
      omega
  | str p =>
    cases v with
    | num _ => exact hv.elim
    | str s =>
      obtain ⟨o, ho, -, rfl⟩ := hv
      exact h.str_len ho

/-- `Z` (`0x80000fb8`): the popped datum's length pushed. -/
theorem fa_Z {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {G : DcG}
    {R : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length + 1 ≤ 2 ^ 30)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 90 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000fb8#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := hc.r2
  bc_run hlive hlive [e2] at 0x80000fbc
  refine fn_pop (p := 0x80000fbc) (tgt0 := 0x80000c10) hlive h (hc.mod (by keeps_tac Keeps.refl _ _))
    (by omega) (by bsimp []) (by decide) ?_ ?_ ?_ ?_
  fn_pop_sites st_80000fbc st_80000fc0
  · intro he R1 M1 hc1 h1
    have hr : dcFunc 70 st 90 peek neg = .ok st := by
      cases st with | mk stk => simp only at he; subst he; rfl
    rw [hr] at hk
    exact fa_ok hlive (ex := []) h1 hc1 hk (.ok _) (by simp) (by simp) (StrPin.refl _ _)
  · intro R1 M1 H1 G1 g v st1 est eG hc1 h1 hv hd
    subst est
    obtain ⟨c, rfl⟩ := eG
    have hr : dcFunc 70 (st1.push v) 90 peek neg = .ok (st1.push (.num (Num.ofInt v.zLen))) := by
      cases v <;> rfl
    rw [hr] at hk
    have hzl := h1.zLen_lt hv
    simp only [Nat.reduceAdd]
    fv_frame hc1
    have e21 := hc1.r2
    have htg := hd.tag
    have hpt := hd.ptr
    simp only [fnSlot] at htg hpt
    rw [show sp - 192 + 16 + 8 = sp - 192 + 24 by omega] at hpt
    bc_run hlive hlive [e21, hpt] at 0x80003804
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine dc_tell_length_spec hlive h1 hv (hc1.cf (Wc := 80) (by omega)) (hc1.cab (by omega)) _
      (by bsimp [e21]) (by bsimp []; exact htg) (by bsimp []) (by bsimp []) (by bsimp [])
      fun R2 M2 H2 F2 L2 C2 G2 k2 e22 e102 hsn h2 hout2 hpin2 => ?_
    have hc2 := hc1.callS (R' := R2) (Wc := 80) (by omega)
      (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (e22.trans (by bsimp [])) hout2
    bsimp []
    bc_run hlive hlive [] at 0x800026d8
    refine fn_i2d_pushE (ex := []) (p := 0x80000fd4) (hs := hs) (st := st1) (v := (v.zLen : Int))
      hlive h2 (by simp) (by simp) (hc2.mod (by keeps_tac Keeps.refl _ _)) (by omega) ho (by simp; omega)
      (by omega) (by omega) (by bsimp [e102]; rw [BitVec.ofInt_natCast]) (by bsimp []) (by decide)
      ?_ ?_ (hk.okPin (by rw [hsn.lk]; exact Nat.le_refl _) hpin2)
    fn_i2d_sites

/-- `P` on a popped number (`0x80001394`): `dc_dump_num (value, DC_TOSS)`. -/
theorem fP_num {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {st1 : St} {x : NumObj} {M1 : Mem} {H1 : Heap}
    {G G1 : DcG} {R1 : Nat → BitVec 64}
    (h1 : DcAt S M1 H1 F L C G1 (.num x.rep.p :: hs) st1) (hx : x ∈ L)
    (hpt : ldv .ld M1 (sp - 192 + 24) = BitVec.ofNat 64 x.rep.p)
    (hc1 : FnAt S sp W M0 R0 R1 M1) (hW : 192 + dnN ≤ W) (ho : FnOom live S Q sp W M0)
    (hmb : MulBase S M0) (hhs : hs.length + 3 ≤ 2 ^ 20) (hwid : x.rep.num.wid < 2 ^ 20)
    (hlk : G1.lk = G.lk) (hstr : G1.strs = G.strs)
    (hk : FnK live S Q al t0 st1 (.ok (st1.emit x.rep.num.dump)) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st1.out) 0x80001394#64 R1 M1 := by
  fv_frame hc1
  have e21 := hc1.r2
  bc_run hlive hlive [e21, hpt] at 0x80002aa4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_dump_num_spec hlive h1 ⟨x, hx, rfl, rfl⟩ hwid hhs (hc1.mulBase hmb)
    (hc1.cf (Wc := dnN) (by omega)) (hc1.cab (by omega)) _ (by bsimp [e21]) (by bsimp [])
    (by bsimp []) (by bsimp []) (fun R2 M2 H2 F2 L2 C2 k2 e22 h2 hout2 => ?_)
    (fun R' M' sp' o => fn_opOom hc1 ho (Wc := dnN) (by omega) o)
  have hc2 := hc1.call (R' := R2) (Wc := dnN) (by omega)
    (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (e22.trans (by bsimp [])) fun a e1 e2 _ e4 => hout2 a e1 e2 e4
  bsimp []
  bc_run hlive hlive [] at 0x80000c04
  rw [String.append_assoc, ← outStr_append]
  exact fa_okF (st' := st1.emit x.rep.num.dump) hlive (ex := []) (h2.emit _) hc2 hk (.ok _)
    (by simp) (by rw [hlk]; exact Nat.le_add_right _ _) (StrPin.of_eq hstr _)

/-- `P` on a popped string (`0x80001374`): `dc_out_str (value, DC_TOSS)`. -/
theorem fP_str {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {st1 : St} {o : StrObj} {M1 : Mem} {H1 : Heap}
    {G G1 : DcG} {R1 : Nat → BitVec 64}
    (h1 : DcAt S M1 H1 F L C G1 (.str o.hb.pay :: hs) st1) (ho' : o ∈ G1.strs)
    (hpt : ldv .ld M1 (sp - 192 + 24) = BitVec.ofNat 64 o.hb.pay)
    (hc1 : FnAt S sp W M0 R0 R1 M1) (hW : 192 + 64 ≤ W)
    (hlk : G1.lk = G.lk) (hstr : G1.strs = G.strs)
    (hk : FnK live S Q al t0 st1 (.ok (st1.emit o.s)) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st1.out) 0x80001374#64 R1 M1 := by
  fv_frame hc1
  have e21 := hc1.r2
  bc_run hlive hlive [e21, hpt] at 0x800039e0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_out_str_spec hlive h1 (keep := false) (fun _ => rfl) ho'
    (hc1.cf (Wc := 64) (by omega)) (hc1.cab (by omega)) _ (by bsimp [e21]) (by bsimp [])
    (by bsimp []) (by bsimp []) fun R2 M2 H2 G2 k2 e22 hsn h2 hout2 hpin2 => ?_
  have hc2 := hc1.callS (R' := R2) (Wc := 64) (by omega)
    (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (e22.trans (by bsimp [])) hout2
  bsimp []
  bc_run hlive hlive [] at 0x80000c04
  rw [String.append_assoc, ← outStr_append]
  exact fa_okF (st' := st1.emit o.s) hlive (ex := []) (h2.emit _) hc2 hk (.ok _)
    (by simp) (by rw [hsn.lk, hlk]; exact Nat.le_add_right _ _) (hstr ▸ hpin2)

/-- `P` (`0x80000bd4`): the popped datum printed as bytes (a number) or text
(a string) and released. -/
theorem fa_P {al : Nat} (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {G : DcG}
    {R : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 + dnN ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0) (hhs : hs.length + 3 ≤ 2 ^ 20)
    (hw : ∀ n rest, st.stack = .num n :: rest → n.wid < 2 ^ 20)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 80 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000bd4#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := hc.r2
  bc_run hlive hlive [e2] at 0x80000bd8
  refine fn_pop (p := 0x80000bd8) (tgt0 := 0x80000c04) hlive h (hc.mod (by keeps_tac Keeps.refl _ _))
    (by omega) (by bsimp []) (by decide) ?_ ?_ ?_ ?_
  fn_pop_sites st_80000bd8 st_80000bdc
  · intro he R1 M1 hc1 h1
    have hr : dcFunc 70 st 80 peek neg = .ok st := by
      cases st with | mk stk => simp only at he; subst he; rfl
    rw [hr] at hk
    exact fa_okF hlive (ex := []) h1 hc1 hk (.ok _) (by simp) (by simp) (StrPin.refl _ _)
  · intro R1 M1 H1 G1 g v st1 est eG hc1 h1 hv hd
    subst est
    obtain ⟨c, rfl⟩ := eG
    simp only [Nat.reduceAdd]
    fv_frame hc1
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
      have hr : dcFunc 70 (st1.push (.num x.rep.num)) 80 peek neg =
          .ok (st1.emit x.rep.num.dump) := rfl
      rw [hr] at hk
      simp only [GV.tag, GV.ptr] at htg hpt
      bc_run hlive hlive [e21, htg] at 0x80001394
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      exact fP_num (st1 := st1) (G1 := G1) hlive h1 hx hpt (hc1.mod (by keeps_tac Keeps.refl _ _)) (by omega) ho
        hmb hhs (hw _ st1.stack rfl) rfl rfl (hk.okIdx rfl rfl)
    | str q =>
      cases v with
      | num _ => exact hv.elim
      | str s =>
      obtain ⟨o, ho', rfl, rfl⟩ := hv
      have hr : dcFunc 70 (st1.push (.str o.s)) 80 peek neg = .ok (st1.emit o.s) := rfl
      rw [hr] at hk
      simp only [GV.tag, GV.ptr] at htg hpt
      bc_run hlive hlive [e21, htg] at 0x80001374
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      bc_run hlive hlive [e21, htg] at 0x80001374
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      exact fP_str (st1 := st1) (G1 := G1) hlive h1 ho' hpt (hc1.mod (by keeps_tac Keeps.refl _ _)) (by omega)
        rfl rfl (hk.okIdx rfl rfl)

end

end Dc.Mach
