import Dc.Mach.DcFuncArmR3
import Dc.Mach.DcArrSet

/-!
# `dc_func`'s array arms (M10)

`;` and `:` (with `peekc` the array's register) spill the register at
`sp + 0`, pop the index (`fn_popW`) and `dc_num2int` it; a string or
negative index prints `"array index must be a nonnegative integer"`
(`fsc_msg`, `0x80000de4`) and returns `DC_EATONE`. `;` reads the element
(`dc_array_get`, its result pushed), `:` pops the value and stores it
(`dc_array_set`). `dc_array_get`'s search needs register `peekc`'s top array
strictly sorted by index (`hsrt`, the open premise of `dc_array_get_spec`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

theorem idxMsg : ProgMsg 0x80007af0 44 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

section

variable {al : Nat} {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 t : String} {st : St} {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {G : DcG} {hs : List GV} {sp W : Nat} {R0 R : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- **The index message, then `DC_EATONE`** (`0x80000de4`). -/
theorem fsc_msg (hlive : ∀ p ∈ dcText, live p.1) {s : St} {G' : DcG} {ex : List GV} {H' : Heap}
    {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {r : Res}
    (h : DcAt S M H' F' L' C' G' (ex ++ hs) s) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (hk : FnK live S Q al t0 st r G hs sp W M0 R0) (hr : r = .eatOne s) (hex : ex.length ≤ 2)
    (hlk : G'.lk.length + ex.length ≤ G.lk.length + al) (hpin : StrPin G.strs G'.strs hs) :
    DWO live S Q (t0 ++ Dc.outStr s.out) 0x80000de4#64 R M := by
  subst hr
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hpn := h.view.prog
  have hG := h.glob
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hS [hpn, stderr_word] at 0x80000774
  refine fn_msg hlive idxMsg (by decide) h (hc.mod (by keeps_tac Keeps.refl _ _)) (by omega)
    (by bsimp []; decide) (by bsimp []) (by bsimp []) (by bsimp []) fun R' M' _ hc' h' => ?_
  bsimp []
  bc_run hlive hlive [] at 0x80000c14
  exact (hc'.mod (by keeps_tac Keeps.refl _ _)).close hlive hk (.eatOne _) h' hex hlk hpin
    (by bsimp [])

theorem ofInt_eq_ofNat_toNat {t : Int} (h : 0 ≤ t) : BitVec.ofInt 64 t = BitVec.ofNat 64 t.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem dcFunc_semi_nil {r : Nat} (he : st.stack = []) :
    dcFunc 70 st 59 (some r) neg = .eatOne st := by
  obtain ⟨stk⟩ := st; simp only at he; subst he; rfl

theorem dcFunc_semi_cons (st : St) (v : Val) (r : Nat) :
    dcFunc 70 (st.push v) 59 (some r) neg = .eatOne (if valInt (-1) v < 0 then st
      else st.push (arrayGet st r (valInt (-1) v).toNat)) := by
  cases st; rfl

/-- `;` with the index `t ≥ 0` (`0x80001354`): `dc_array_get (r, t)`, the
element pushed, `DC_EATONE`. -/
theorem fsemi_get (hlive : ∀ p ∈ dcText, live p.1) {r : Nat} (hr : r < 256) {t : Int}
    (ht0 : 0 ≤ t) (ht1 : t < 2 ^ 31) {R' : Nat → BitVec 64} {M' : Mem} {H' : Heap}
    {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG} {st' : St}
    (h' : DcAt S M' H' F' L' C' G' hs st') (hc' : FnAt S sp W M0 R0 R' M') (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length ≤ 2 ^ 30)
    (hsrt : (topArrSt st' r).Pairwise (fun a b => a.1 < b.1))
    (h10 : R' 10 = BitVec.ofInt 64 t) (hw : ldv .ld M' (sp - 192) = BitVec.ofNat 64 r)
    (hk : FnK live S Q al t0 st (.eatOne (st'.push (arrayGet st' r t.toNat))) G hs sp W M0 R0)
    (elk : G'.lk = G.lk) (hpin : StrPin G.strs G'.strs hs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80001354#64 R' M' := by
  fr_ctx
  bc_run hlive hS [e2', hw, h10, ofInt_eq_ofNat_toNat ht0] at 0x80003dc8
  all_goals try exact frame_acc hsf (by omega) (by omega)
  refine dc_array_get_spec hlive h' hhs hr (i := t.toNat) (by omega) hsrt (hc'.cf (Wc := 336) hW)
    (hc'.cab hW) _ (by bsimp []) (by bsimp []) (by bsimp [e2']) (by bsimp [])
    (fun R2 M2 H2 F2 L2 C2 G2 g k2 hd h2 hden hout hpin2 hlk => ?_)
    fun R2 M2 sp' e1 e2 e3 hout => ?_
  · have hc2 := (hc'.mod (by keeps_tac Keeps.refl _ _)).callS (Wc := 336) hW
      (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (by bsimp []; rw [k2.get 2 (by decide)]; bsimp []) hout
    bsimp []
    have hd10 := hd.tag
    have hd11 := hd.ptr
    bc_run hlive hS [hc2.r2] at 0x80002da4
    all_goals try exact frame_acc hsf (by omega) (by omega)
    have hc3 := ((hc2.store (a := sp - 192 + 160) (by omega) (by omega) (R2 10)).store
      (a := sp - 192 + 168) (by omega) (by omega) (R2 11))
    show DWO live S Q (t0 ++ Dc.outStr (st'.push (arrayGet st' r t.toNat)).out) _ _ _
    refine dc_push_spec hlive (((h2.fnStore hc2 (a := sp - 192 + 160) (by omega) (R2 10)).fnStore
      (hc2.store (a := sp - 192 + 160) (by omega) (by omega) (R2 10)) (a := sp - 192 + 168) (by omega)
      (R2 11))) hden (hc3.cf (Wc := 64) (by omega)) (hc3.cab (by omega)) _
      ⟨by bsimp []; exact hd10, by bsimp []; exact hd11⟩ (by bsimp [hc2.r2]) (by bsimp [])
      (fun R3 M3 H3 c k3 h3 hout3 => ?_)
      fun R3 M3 e3' hout3 => hc3.oom ho (Wc := 64) (by omega) (by omega) (by omega) e3'
        fun a a1 a2 _ a4 => hout3 a a1 a2 a4
    bsimp []
    bc_run hlive hlive [] at 0x80000c14
    exact ((hc3.mod (by keeps_tac Keeps.refl _ _)).callS (Wc := 64) (by omega)
      (by keeps_tac ((k3.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (by bsimp []; rw [k3.get 2 (by decide)]; bsimp []) hout3).close hlive hk (.eatOne _) (ex := []) h3
      (by simp) (by simp [hlk, elk]) (hpin.trans hpin2) (by bsimp [])
  · have hj : JAt live S Q 0x80002bcc 0x80001e74 := fun t R M k => by
      have htx : tohostAddr = 0x8001ad00 := rfl
      bc_run hlive hlive [] at 0x80001e74
      exact k
    exact hj _ R2 M2 ((hc'.mod (by keeps_tac Keeps.refl _ _)).oom ho (Wc := 336) hW e1 e2 e3
      fun a a1 a2 _ a4 => hout a a1 a2 a4)

/-- `;` on a numeric index (`0x80000dd8`): `dc_num2int`, then the message
for a negative index or `fsemi_get`. -/
theorem fsemi_num (hlive : ∀ p ∈ dcText, live p.1) {r : Nat} (hr : r < 256) {R' : Nat → BitVec 64}
    {M' : Mem} {H' : Heap} {G' : DcG} {x : NumObj} {st' : St}
    (h' : DcAt S M' H' F L C G' (.num x.rep.p :: hs) st') (hx : x ∈ L)
    (hc' : FnAt S sp W M0 R0 R' M') (hW : 192 + 336 ≤ W) (ho : FnOom live S Q sp W M0)
    (hhs : hs.length ≤ 2 ^ 30) (hsrt : (topArrSt st' r).Pairwise (fun a b => a.1 < b.1))
    (htg : ldv .lw M' (sp - 192 + 16) = BitVec.ofNat 64 1)
    (hpt : ldv .ld M' (sp - 192 + 24) = BitVec.ofNat 64 x.rep.p)
    (hw : ldv .ld M' (sp - 192) = BitVec.ofNat 64 r)
    (hk : FnK live S Q al t0 st (.eatOne (if x.rep.num.toInt.1 < 0 then st'
      else st'.push (arrayGet st' r x.rep.num.toInt.1.toNat))) G hs sp W M0 R0)
    (elk : G.lk = G'.lk) (estr : G.strs = G'.strs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000dd8#64 R' M' := by
  fr_ctx
  bc_run hlive hS [e2', htg, hpt] at 0x80002648
  all_goals try exact frame_acc hsf (by omega) (by omega)
  bc_run hlive hS [e2', htg, hpt] at 0x80002648
  all_goals try exact frame_acc hsf (by omega) (by omega)
  refine fn_n2i hlive h' hx (hc'.mod (by keeps_tac Keeps.refl _ _)) hW (by bsimp [])
    (by bsimp []) (by bsimp []) fun R2 M2 H2 F2 L2 C2 k2 hc2 e10 h2 hout2 => ?_
  have hw2 : ldv .ld M2 (sp - 192) = BitVec.ofNat 64 r := by
    have e := hc'.ldKeep (o := 0) hout2
    simp only [Nat.add_zero] at e
    rw [e, hw]
  bsimp []
  have hti := toInt_n2i x.rep.num
  have hrg := Num.toInt_range x.rep.num
  bc_run hlive hS [e10, hti, BitVec.toInt_zero] at 0x80000de4 0x80001354
  · intro hlt
    rw [ite_T hlt] at hk
    exact fsc_msg hlive (ex := []) h2 (hc2.mod (by keeps_tac Keeps.refl _ _)) hW hk rfl (by simp)
      (by simp [elk]) (StrPin.of_eq estr.symm _)
  · intro hge
    rw [ite_F hge] at hk
    show DWO live S Q (t0 ++ Dc.outStr st'.out) _ _ _
    exact fsemi_get hlive hr (by omega) hrg.2 h2 (hc2.mod (by keeps_tac Keeps.refl _ _)) hW ho hhs
      hsrt (by bsimp [e10]) hw2 hk (by simp [elk]) (StrPin.of_eq estr.symm _)

/-- `;` (`0x80000dc0`): pop the index; a number `t ≥ 0` pushes element `t`
of register `peekc`'s array; a string or negative index prints the message;
`DC_EATONE`. -/
theorem fa_semi (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (hhs : hs.length ≤ 2 ^ 30) (hal1 : 1 ≤ al)
    (h11 : R 11 = chW peek) (hpk : ∀ r, peek = some r → r < 256)
    (hsrt : ∀ r e es, st.regs r = e :: es → e.arr.Pairwise (fun a b => a.1 < b.1))
    (hk : FnK live S Q al t0 st (dcFunc 70 st 59 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000dc0#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hsl := hc.frame.lo; have hsh := hc.frame.hi; have hbig := hc.big; have hroom := hc.room
  have hsf : StackFrame S sp 192 := hc.frame.mono hc.big
  have hsa := hc.frame.al
  have e2 := hc.r2
  cases peek with
  | none =>
    bc_run hlive hlive [h11, chW] at 0x80001264
    exact fa_eof hlive rfl h (hc.mod (by keeps_tac Keeps.refl _ _)) hk
  | some r =>
    have hr := hpk r rfl
    have hsr : (topArrSt st r).Pairwise (fun a b => a.1 < b.1) := by
      unfold topArrSt; split
      · exact List.Pairwise.nil
      · next e es he => exact hsrt r e es he
    bc_run hlive hlive [h11, chW, chW_ne hr, e2] at 0x80000dd0
    bc_run hlive hlive [h11, e2] at 0x80000dd0
    all_goals try exact frame_acc hsf (by omega) (by omega)
    refine fn_popW (p := 0x80000dd0) (tE := 0x80000d5c) (tN := 0x80000dd8) hlive
      (h.fnStore hc (a := sp - 192) (by omega) _)
      ((hc.store (a := sp - 192) (by omega) (by omega) _).mod (by keeps_tac Keeps.refl _ _)) hW
      (by bsimp []) (by decide) ?_ ?_ ?_ ?_
    fr_pop_sites_eat 0x80000dd8
    · intro he R' M' hc' h'
      rw [dcFunc_semi_nil he] at hk
      exact fa_eat hlive (ex := []) h' hc' hk (.eatOne _) (by simp) (by simp) (StrPin.refl _ _)
    · intro R' M' H' G' g v st' est eG hc' h' hv hd hkeep
      have hw := hkeep 0 (by omega)
      subst est
      rw [dcFunc_semi_cons] at hk
      obtain ⟨c, rfl⟩ := eG
      simp only [Nat.add_zero] at hw
      have hw' := hw.trans (ldv_store_hit _ _ _)
      have htg := hd.lw
      have hpt := hd.ptr
      simp only [fnSlot] at htg hpt
      rcases GV.den_cases hv with ⟨x, hx, rfl, rfl⟩ | ⟨o, ho', rfl, rfl⟩
      · exact fsemi_num (st' := st') (G' := G') hlive hr h' hx hc' hW ho hhs hsr htg hpt hw' hk rfl rfl
      · have hs2 := hc'.r2
        have hS : HeapOwn S := fun a e1 e2 => h'.heap.heap.own a e1 e2
        rw [ite_T (by simp [valInt])] at hk
        bc_run hlive hS [hs2, htg, GV.tag] at 0x80000de4
        all_goals try exact frame_acc hsf (by omega) (by omega)
        exact fsc_msg (s := st') hlive (ex := [_]) h' (hc'.mod (by keeps_tac Keeps.refl _ _)) hW hk rfl (by simp)
          (by simp; omega) (StrPin.refl _ _)

theorem dcFunc_colon_nil {r : Nat} (he : st.stack = []) :
    dcFunc 70 st 58 (some r) neg = .eatOne st := by
  obtain ⟨stk⟩ := st; simp only at he; subst he; rfl

theorem dcFunc_colon_one (st : St) (iv : Val) {r : Nat} (he : st.stack = []) :
    dcFunc 70 (st.push iv) 58 (some r) neg = .eatOne st := by
  obtain ⟨stk⟩ := st; simp only at he; subst he; rfl

theorem dcFunc_colon_two (st : St) (v iv : Val) (r : Nat) :
    dcFunc 70 ((st.push v).push iv) 58 (some r) neg = .eatOne (if valInt (-1) iv < 0 then st
      else arraySet st r (valInt (-1) iv).toNat v) := by
  cases st; rfl

/-- `:` with the index `t` at `sp + 8` and the value `g` popped
(`0x800013d4`): the message for `t < 0` (the value's handle lost), else
`dc_array_set (r, t, value)`; `DC_EATONE`. -/
theorem fcol_set (hlive : ∀ p ∈ dcText, live p.1) {r : Nat} (hr : r < 256) {t : Int}
    (ht : -2 ^ 31 ≤ t ∧ t < 2 ^ 31) {R' : Nat → BitVec 64} {M' : Mem} {H' : Heap}
    {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG} {g : GV} {v : Val} {st' : St}
    (h' : DcAt S M' H' F' L' C' G' (g :: hs) st') (hv : g.Den ⟨L', G'.strs⟩ v)
    (hc' : FnAt S sp W M0 R0 R' M') (hW : 192 + 336 ≤ W) (ho : FnOom live S Q sp W M0)
    (hal1 : 1 ≤ al) (hd : DatAt M' (fnSlot sp) g)
    (hw : ldv .ld M' (sp - 192) = BitVec.ofNat 64 r) (hw8 : ldv .ld M' (sp - 192 + 8) = BitVec.ofInt 64 t)
    (hk : FnK live S Q al t0 st (.eatOne (if t < 0 then st' else arraySet st' r t.toNat v)) G hs
      sp W M0 R0)
    (elk : G'.lk = G.lk) (hpin : StrPin G.strs G'.strs hs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x800013d4#64 R' M' := by
  fr_ctx
  have hti : (BitVec.ofInt 64 t).toInt = t :=
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
  have htg : ldv .ld M' (sp - 192 + 16) = ldv .ld M' (fnSlot sp) := rfl
  have hpt : ldv .ld M' (sp - 192 + 24) = BitVec.ofNat 64 g.ptr := hd.ptr
  bc_run hlive hS [e2', hw8, hti, BitVec.toInt_zero] at 0x80000de4 0x800013dc
  all_goals try exact frame_acc hsf (by omega) (by omega)
  · intro hlt
    rw [ite_T hlt] at hk
    exact fsc_msg hlive (ex := [g]) h' (hc'.mod (by keeps_tac Keeps.refl _ _)) hW hk rfl (by simp)
      (by simp [elk]; omega) hpin
  · intro hge
    rw [ite_F hge] at hk
    bc_run hlive hS [e2', hw, hpt, htg] at 0x80003c7c
    all_goals try exact frame_acc hsf (by omega) (by omega)
    have harr : (arraySet st' r t.toNat v).out = st'.out := by
      unfold arraySet; split <;> rfl
    rw [← harr]
    refine dc_array_set_spec hlive h' hv hr (i := t.toNat) (by omega) (hc'.cf (Wc := 112) (by omega))
      (hc'.cab (by omega)) _ (by bsimp []) (by bsimp [ofInt_eq_ofNat_toNat (show 0 ≤ t by omega)])
      ⟨by bsimp []; exact hd.tag, by bsimp []⟩ (by bsimp [e2']) (by bsimp [])
      (fun R2 M2 H2 F2 L2 C2 G2 k2 h2 hout hpin2 hlk => ?_)
      fun R2 M2 sp' e1 e2 e3 hout => hc'.oom ho (Wc := 112) (by omega) e1 e2 e3
        fun a a1 a2 _ a4 => hout a a1 a2 a4
    bsimp []
    bc_run hlive hlive [] at 0x80000c14
    exact ((hc'.mod (by keeps_tac Keeps.refl _ _)).callS (Wc := 112) (by omega)
      (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (by bsimp []; rw [k2.get 2 (by decide)]; bsimp []) hout).close hlive hk (.eatOne _) (ex := []) h2
      (by simp) (by simp [hlk, elk]) (hpin.trans hpin2) (by bsimp [])

/-- `:` on a numeric index (`0x80000e20`): `dc_num2int` (kept at `sp + 8`),
then the value popped (`fcol_set`); an empty stack returns `DC_EATONE`. -/
theorem fcol_num (hlive : ∀ p ∈ dcText, live p.1) {r : Nat} (hr : r < 256) {R' : Nat → BitVec 64}
    {M' : Mem} {H' : Heap} {G' : DcG} {x : NumObj} {st' : St}
    (h' : DcAt S M' H' F L C G' (.num x.rep.p :: hs) st') (hx : x ∈ L)
    (hc' : FnAt S sp W M0 R0 R' M') (hW : 192 + 336 ≤ W) (ho : FnOom live S Q sp W M0)
    (hal1 : 1 ≤ al)
    (htg : ldv .lw M' (sp - 192 + 16) = BitVec.ofNat 64 1)
    (hpt : ldv .ld M' (sp - 192 + 24) = BitVec.ofNat 64 x.rep.p)
    (hw : ldv .ld M' (sp - 192) = BitVec.ofNat 64 r)
    (hk : FnK live S Q al t0 st (dcFunc 70 (st'.push (.num x.rep.num)) 58 (some r) neg) G hs
      sp W M0 R0)
    (elk : G.lk = G'.lk) (estr : G.strs = G'.strs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000e20#64 R' M' := by
  fr_ctx
  bc_run hlive hS [e2', htg, hpt] at 0x80002648
  all_goals try exact frame_acc hsf (by omega) (by omega)
  bc_run hlive hS [e2', htg, hpt] at 0x80002648
  all_goals try exact frame_acc hsf (by omega) (by omega)
  refine fn_n2i hlive h' hx (hc'.mod (by keeps_tac Keeps.refl _ _)) hW (by bsimp [])
    (by bsimp []) (by bsimp []) fun R2 M2 H2 F2 L2 C2 k2 hc2 e10 h2 hout2 => ?_
  have hw2 : ldv .ld M2 (sp - 192) = BitVec.ofNat 64 r := by
    have e := hc'.ldKeep (o := 0) hout2
    simp only [Nat.add_zero] at e
    rw [e, hw]
  have hrg := Num.toInt_range x.rep.num
  bsimp []
  bc_run hlive hS [e10, hc2.r2] at 0x800013cc
  all_goals try exact frame_acc hsf (by omega) (by omega)
  have hc3 := hc2.store (a := sp - 192 + 8) (by omega) (by omega) (BitVec.ofInt 64 x.rep.num.toInt.1)
  refine fn_popW (p := 0x800013cc) (tE := 0x80000d5c) (tN := 0x800013d4) hlive
    (h2.fnStore hc2 (a := sp - 192 + 8) (by omega) _) (hc3.mod (by keeps_tac Keeps.refl _ _)) hW
    (by bsimp []) (by decide) ?_ ?_ ?_ ?_
  fr_pop_sites_eat 0x800013d4
  · intro he R3 M3 hc4 h4
    rw [dcFunc_colon_one st' _ he] at hk
    exact fa_eat hlive (ex := []) h4 hc4 hk (.eatOne _) (by simp) (by simp [elk])
      (StrPin.of_eq estr.symm _)
  · intro R3 M3 H3 G3 g v st2 est eG hc4 h4 hv hd hkeep
    subst est
    rw [dcFunc_colon_two] at hk
    obtain ⟨c, rfl⟩ := eG
    have hw3 := hkeep 0 (by omega)
    have hw8 := hkeep 8 (by omega)
    simp only [Nat.add_zero] at hw3
    rw [ldv_ld_miss _ _ (by omega), hw2] at hw3
    rw [ldv_store_hit] at hw8
    exact fcol_set (t := x.rep.num.toInt.1) (st' := st2) (st := st) (G := G) hlive hr hrg h4 hv hc4 hW ho hal1 hd hw3 hw8 hk
      elk.symm (StrPin.of_eq estr.symm _)

/-- `:` on a string index (`0x80000e20`): the value popped too and the
message (both handles lost), or `DC_EATONE` on an empty stack. -/
theorem fcol_str (hlive : ∀ p ∈ dcText, live p.1) {r : Nat} {R' : Nat → BitVec 64}
    {M' : Mem} {H' : Heap} {G' : DcG} {o : StrObj} {st' : St}
    (h' : DcAt S M' H' F L C G' (.str o.hb.pay :: hs) st')
    (hc' : FnAt S sp W M0 R0 R' M') (hW : 192 + 336 ≤ W) (hal2 : 2 ≤ al)
    (htg : ldv .lw M' (sp - 192 + 16) = BitVec.ofNat 64 2)
    (hk : FnK live S Q al t0 st (dcFunc 70 (st'.push (.str o.s)) 58 (some r) neg) G hs
      sp W M0 R0)
    (elk : G.lk = G'.lk) (estr : G.strs = G'.strs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000e20#64 R' M' := by
  fr_ctx
  bc_run hlive hS [e2', htg] at 0x80000e30
  all_goals try exact frame_acc hsf (by omega) (by omega)
  bc_run hlive hS [e2', htg] at 0x80000e30
  all_goals try exact frame_acc hsf (by omega) (by omega)
  refine fn_popW (p := 0x80000e30) (tE := 0x80000e38) (tN := 0x80000de4) hlive h'
    (hc'.mod (by keeps_tac Keeps.refl _ _)) hW (by bsimp []) (by decide) ?_ ?_ ?_ ?_
  · intro t R M k
    have htx : tohostAddr = 0x8001ad00 := rfl
    bc_run hlive hlive [] at 0x8000310c
    exact k _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
  · intro t R M k1 k2
    simp only [Nat.reduceAdd] at k1 k2 ⊢
    have htx : tohostAddr = 0x8001ad00 := rfl
    bc_run hlive hlive [] at 0x80000de4 0x80000e38
    all_goals first | exact k1 | exact k2
  · intro he R3 M3 hc4 h4
    rw [dcFunc_colon_one st' _ he] at hk
    have htx : tohostAddr = 0x8001ad00 := rfl
    bc_run hlive hlive [] at 0x80000c14
    exact (hc4.mod (by keeps_tac Keeps.refl _ _)).close hlive hk (.eatOne _) (ex := [_]) h4
      (by simp) (by simp [elk]; omega) (StrPin.of_eq estr.symm _) (by bsimp [])
  · intro R3 M3 H3 G3 g v st2 est eG hc4 h4 hv hd hkeep
    subst est
    rw [dcFunc_colon_two, ite_T (by simp [valInt])] at hk
    obtain ⟨c, rfl⟩ := eG
    exact fsc_msg (s := st2) hlive (ex := [g, _]) h4 hc4 hW hk rfl (by simp)
      (by simp [elk]; omega) (StrPin.of_eq estr.symm _)

/-- `:` (`0x80000e08`): pop the index and the value; a number `t ≥ 0` stores
the value as element `t` of register `peekc`'s array (`arraySet`); a string
or negative index prints the message and loses the popped handles;
`DC_EATONE`. -/
theorem fa_colon (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (hal2 : 2 ≤ al)
    (h11 : R 11 = chW peek) (hpk : ∀ r, peek = some r → r < 256)
    (hk : FnK live S Q al t0 st (dcFunc 70 st 58 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000e08#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hsl := hc.frame.lo; have hsh := hc.frame.hi; have hbig := hc.big; have hroom := hc.room
  have hsf : StackFrame S sp 192 := hc.frame.mono hc.big
  have hsa := hc.frame.al
  have e2 := hc.r2
  cases peek with
  | none =>
    bc_run hlive hlive [h11, chW] at 0x80001264
    exact fa_eof hlive rfl h (hc.mod (by keeps_tac Keeps.refl _ _)) hk
  | some r =>
    have hr := hpk r rfl
    bc_run hlive hlive [h11, chW, chW_ne hr, e2] at 0x80000e18
    bc_run hlive hlive [h11, e2] at 0x80000e18
    all_goals try exact frame_acc hsf (by omega) (by omega)
    refine fn_popW (p := 0x80000e18) (tE := 0x80000d5c) (tN := 0x80000e20) hlive
      (h.fnStore hc (a := sp - 192) (by omega) _)
      ((hc.store (a := sp - 192) (by omega) (by omega) _).mod (by keeps_tac Keeps.refl _ _)) hW
      (by bsimp []) (by decide) ?_ ?_ ?_ ?_
    fr_pop_sites_eat 0x80000e20
    · intro he R' M' hc' h'
      rw [dcFunc_colon_nil he] at hk
      exact fa_eat hlive (ex := []) h' hc' hk (.eatOne _) (by simp) (by simp) (StrPin.refl _ _)
    · intro R' M' H' G' g v st' est eG hc' h' hv hd hkeep
      have hw := hkeep 0 (by omega)
      subst est
      obtain ⟨c, rfl⟩ := eG
      simp only [Nat.add_zero] at hw
      have hw' := hw.trans (ldv_store_hit _ _ _)
      have htg := hd.lw
      have hpt := hd.ptr
      simp only [fnSlot] at htg hpt
      rcases GV.den_cases hv with ⟨x, hx, rfl, rfl⟩ | ⟨o, ho', rfl, rfl⟩
      · exact fcol_num (st' := st') (G' := G') hlive hr h' hx hc' hW ho (by omega) htg hpt hw' hk rfl rfl
      · exact fcol_str (st' := st') (G' := G') hlive h' hc' hW hal2 htg hk rfl rfl

end

end Dc.Mach
