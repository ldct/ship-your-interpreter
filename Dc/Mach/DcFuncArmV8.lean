import Dc.Mach.DcFuncArmV7
import Dc.Mach.DcNum2Int
import Dc.Mach.DcMakeString

/-!
# `dc_func`'s `a` arm (M10)

`a` pops a datum and makes a one-character string of it: a number's low byte
(`dc_num2int (value, DC_TOSS)`), or a string's first byte (`dc_str2charp`, the
leaf `ld a0, 0(a0); ret` stepped inline, then `dc_free_str`); the byte is
stored at `sp + 160`, then `dc_makestring (sp + 160, 1)` and `dc_push`
(`fa_mk`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `sb` of an `int` word stores its low byte. -/
theorem sbData_ofInt (x : Int) : sbData (BitVec.ofInt 64 x) = BitVec.ofNat 8 (x % 256).toNat := by
  rw [sbData_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [lo8, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-- The first byte of a string object's text (`NUL` for the empty string). -/
theorem StrAt.head {M : Mem} {o : StrObj} (h : StrAt M o) :
    ldv .lbu M o.tb.pay = BitVec.ofNat 64 (o.s.headD 0) := by
  rw [ldv_lbu]
  cases hs : o.s with
  | nil =>
    have := h.nul; rw [hs] at this; simp only [List.length_nil, Nat.add_zero] at this
    rw [this]; rfl
  | cons c l =>
    have hb := h.bytes 0 (by rw [hs]; simp)
    have hc := h.byte c (by rw [hs]; exact List.mem_cons_self)
    rw [hs] at hb; simp only [Nat.add_zero, List.getD_cons_zero] at hb
    rw [hb]; apply BitVec.eq_of_toNat_eq
    simp [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
    omega

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {M0 : Mem} {hs : List GV} {sp W : Nat} {R0 : Nat → BitVec 64}
  {peek : Option Nat} {neg : Bool}

/-- `a`'s tail (`0x80000f8c`, the byte `b` at `sp + 160`):
`dc_push (dc_makestring (sp + 160, 1))`, `DC_OKAY`. -/
theorem fa_mk (hlive : ∀ p ∈ dcText, live p.1) {st1 : St} {b : Nat} {M2 : Mem} {H2 : Heap}
    {F2 : List Blk} {L2 : List NumObj} {C2 : BcConsts} {G G2 : DcG} {R2 : Nat → BitVec 64}
    (h2 : DcAt S M2 H2 F2 L2 C2 G2 hs st1) (hc2 : FnAt S sp W M0 R0 R2 M2) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0) (hb : b < 256)
    (hby : imgM M2 (sp - 192 + 160) = BitVec.ofNat 8 b)
    (hlk : G2.lk = G.lk) (hpin : StrPin G.strs G2.strs hs)
    (hk : FnK live S Q t0 st1 (.ok (st1.push (.str [b]))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st1.out) 0x80000f8c#64 R2 M2 := by
  fv_frame hc2
  have e22 := hc2.r2
  bc_run hlive hlive [e22] at 0x80003a58
  refine dc_makestring_spec hlive h2 (sp := sp - 192) (src := sp - 192 + 160) (s := [b])
    ⟨⟨fun i hi => hsf.own _ (by simp at hi; omega) (by simp at hi; omega), by omega, by simp; omega⟩,
      fun i hi => .inr ⟨(hfr _ (by omega)).1, by simp at hi ⊢; omega⟩,
      fun i hi => by
        have : i = 0 := by simp at hi; omega
        subst this; simpa using hby,
      fun c hc => by simp at hc; omega, by simp⟩
    (hc2.cf (Wc := 64) (by omega)) (hc2.cab (by omega)) _ (by bsimp [e22]) (by bsimp [])
    (by bsimp []; rfl) (by bsimp []) (fun R3 M3 H3 b1 b2 k3 e32 etag e11 h3 hout3 => ?_)
    (fun R3 M3 e3 hout3 => hc2.oom ho (Wc := 64) (by omega) (by omega) (by omega) e3
      fun a e1 e2 _ e4 => hout3 a e1 e2 e4)
  have hc3 := hc2.callS (R' := R3) (Wc := 64) (by omega)
    (by keeps_tac ((k3.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (e32.trans (by bsimp [])) hout3
  bsimp []
  bc_run hlive hlive [] at 0x80002da4
  refine dc_push_spec hlive h3 (v := .str [b]) ⟨msObj b1 b2 [b], List.mem_cons_self, rfl, rfl⟩
    (hc3.cf (Wc := 64) (by omega)) (hc3.cab (by omega)) _
    ⟨by bsimp []; exact etag, by bsimp []; exact e11⟩ (by bsimp [hc3.r2]) (by bsimp [])
    (fun R4 M4 H4 c4 k4 h4 hout4 => ?_) (fun R4 M4 e4 hout4 => ?_)
  · have hc4 := hc3.callS (R' := R4) (Wc := 64) (by omega)
      (by keeps_tac ((k4.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      ((k4.get 2 (by decide)).trans (by bsimp [])) hout4
    bsimp []
    bc_run hlive hlive [] at 0x80000c10
    exact fa_ok (st' := st1.push (.str [b])) hlive (ex := []) h4 hc4 hk (.ok _) (by simp)
      (by show G2.lk.length ≤ _; rw [hlk]; exact Nat.le_add_right _ _)
      (hpin.trans (StrPin.cons _ _ _))
  · exact hc3.oom ho (Wc := 64) (by omega) (by omega) (by omega) e4
      fun a e1 e2 _ e4 => hout4 a e1 e2 e4

/-- `a` on a popped number (`0x800013a4`): its low byte. -/
theorem fa_num (hlive : ∀ p ∈ dcText, live p.1) {st1 : St} {x : NumObj} {M1 : Mem} {H1 : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G G1 : DcG} {R1 : Nat → BitVec 64}
    (h1 : DcAt S M1 H1 F L C G1 (.num x.rep.p :: hs) st1) (hx : x ∈ L)
    (hpt : ldv .ld M1 (sp - 192 + 24) = BitVec.ofNat 64 x.rep.p)
    (hc1 : FnAt S sp W M0 R0 R1 M1) (hW : 192 + 336 ≤ W) (ho : FnOom live S Q sp W M0)
    (hlk : G1.lk = G.lk) (hstr : G1.strs = G.strs)
    (hk : FnK live S Q t0 st1 (.ok (st1.push (.str [(x.rep.num.toInt.1 % 256).toNat]))) G hs sp W
      M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st1.out) 0x800013a4#64 R1 M1 := by
  fv_frame hc1
  have e21 := hc1.r2
  bc_run hlive hlive [e21, hpt] at 0x80002648
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_num2int_spec hlive h1 (keep := false) (fun _ => rfl) hx (hc1.cf (Wc := 336) (by omega))
    (hc1.cab (by omega)) _ (by bsimp [e21]) (by bsimp []) (by bsimp []) (by bsimp [])
    fun R2 M2 H2 F2 L2 C2 k2 e22 e102 h2 hout2 => ?_
  have e2b : R2 2 = BitVec.ofNat 64 (sp - 192) := e22.trans (by bsimp [e21])
  bsimp []
  bc_run hlive hlive [e2b, e102] at 0x80000f8c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hm : MemOnly (fun a => sp - 192 + 160 ≤ a ∧ a < sp - 192 + 160 + 1)
      (writeLog M2 [(sp - 192 + 160, 1, BitVec.ofInt 64 x.rep.num.toInt.1)]) M2 := MemOnly.store M2 _ 1 _
  have h2' := h2.outWrite hm fun a ha => ⟨(hfr a (by omega)).1, (hfr a (by omega)).2.1⟩
  have hc2 := hc1.callL (R' := R2) (M' := writeLog M2 [(sp - 192 + 160, 1, BitVec.ofInt 64 x.rep.num.toInt.1)])
    (Wc := 336) (by omega)
    (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) (e2b.trans e21.symm)
    fun a e1 e2 _ e4 e5 => (hm a (by simp only [frameIn] at e5; omega)).trans (hout2 a e1 e2 e4)
  exact fa_mk hlive h2' (hc2.mod (by keeps_tac Keeps.refl _ _)) hW ho (by omega)
    (by simp only [imgM_sb, ite_true, sbData_ofInt]) hlk (StrPin.of_eq hstr _) hk

/-- `a` on a popped string (`0x80001328`): its first byte, the string released. -/
theorem fa_str (hlive : ∀ p ∈ dcText, live p.1) {st1 : St} {o : StrObj} {M1 : Mem} {H1 : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G G1 : DcG} {R1 : Nat → BitVec 64}
    (h1 : DcAt S M1 H1 F L C G1 (.str o.hb.pay :: hs) st1) (ho' : o ∈ G1.strs)
    (hpt : ldv .ld M1 (sp - 192 + 24) = BitVec.ofNat 64 o.hb.pay)
    (hc1 : FnAt S sp W M0 R0 R1 M1) (hW : 192 + 336 ≤ W) (ho : FnOom live S Q sp W M0)
    (hlk : G1.lk = G.lk) (hstr : G1.strs = G.strs)
    (hk : FnK live S Q t0 st1 (.ok (st1.push (.str [o.s.headD 0]))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st1.out) 0x80001328#64 R1 M1 := by
  fv_frame hc1
  have e21 := hc1.r2
  have hS : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  have hso := h1.view.strs o ho'
  have hp0 := hso.ptr
  have hl0 := hso.head
  have hsz := hso.hsz
  have htz := hso.tsz
  have bh := blk_bounds h1.heap.heap (h1.heap.raw.live o.hb
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho', by simp⟩))))
  have bt := blk_bounds h1.heap.heap (h1.heap.raw.live o.tb
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho', by simp⟩))))
  simp only [heapStart, heapEnd] at bh bt
  have hc0 : o.s.headD 0 < 256 := by
    cases e : o.s with
    | nil => simp
    | cons c l => exact hso.byte c (by rw [e]; exact List.mem_cons_self)
  bc_run hlive hS [e21, hpt, hp0, hl0] at 0x800039a4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hm : MemOnly (fun a => sp - 192 + 160 ≤ a ∧ a < sp - 192 + 160 + 1)
      (writeLog M1 [(sp - 192 + 160, 1, BitVec.ofNat 64 (o.s.headD 0))]) M1 := MemOnly.store M1 _ 1 _
  have h1' := h1.outWrite hm fun a ha => ⟨(hfr a (by omega)).1, (hfr a (by omega)).2.1⟩
  have hc1' := hc1.callL (Wc := 0) (M' := writeLog M1 [(sp - 192 + 160, 1, BitVec.ofNat 64 (o.s.headD 0))])
    (by omega) (Keeps.refl _ _) rfl fun a _ _ _ _ e5 => hm a (by simp only [frameIn] at e5; omega)
  refine dc_free_str_spec hlive h1' (hc1.frame.slot (q := sp - 192 + 24) (by omega) (by omega) (by omega))
    (by rw [ldv_ld_miss _ _ (by omega)]; exact hpt) (hc1.cf (Wc := 32) (by omega))
    (hc1.cab (by omega)) _ (by bsimp []) (by bsimp [e21]) (by bsimp [])
    fun R3 M3 H3 G3 k3 hsn h3 hout3 hpin3 => ?_
  have hc3 := hc1'.callS (R' := R3) (Wc := 32) (by omega)
    (by keeps_tac ((k3.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    ((k3.get 2 (by decide)).trans (by bsimp [])) hout3
  have hby : imgM M3 (sp - 192 + 160) = BitVec.ofNat 8 (o.s.headD 0) := by
    rw [hout3 _ (hfr _ (by omega)).1 (hfr _ (by omega)).2.1 ((hfr _ (by omega)).2.2 _), imgM_sb]
    simp only [ite_true, sbData_ofNat]
  bsimp []
  bc_run hlive hlive [] at 0x80000f8c
  exact fa_mk hlive h3 (hc3.mod (by keeps_tac Keeps.refl _ _)) hW ho hc0 hby (hsn.lk.trans hlk)
    ((StrPin.of_eq hstr _).trans hpin3) hk

/-- `a` (`0x80000f5c`): a one-character string of the popped datum. -/
theorem fa_a (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {R : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (ho : FnOom live S Q sp W M0)
    (hk : FnK live S Q t0 st (dcFunc 70 st 97 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000f5c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := hc.r2
  bc_run hlive hlive [e2] at 0x80000f60
  refine fn_pop (p := 0x80000f60) (tgt0 := 0x80000c10) hlive h (hc.mod (by keeps_tac Keeps.refl _ _))
    (by omega) (by bsimp []) (by decide) ?_ ?_ ?_ ?_
  fn_pop_sites st_80000f60 st_80000f64
  · intro he R1 M1 hc1 h1
    have hr : dcFunc 70 st 97 peek neg = .ok st := by
      cases st with | mk stk => simp only at he; subst he; rfl
    rw [hr] at hk
    exact fa_ok hlive (ex := []) h1 hc1 hk (.ok _) (by simp) (by simp) (StrPin.refl _ _)
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
      have hr : dcFunc 70 (st1.push (.num x.rep.num)) 97 peek neg =
          .ok (st1.push (.str [(x.rep.num.toInt.1 % 256).toNat])) := rfl
      rw [hr] at hk
      simp only [GV.tag, GV.ptr] at htg hpt
      bc_run hlive hlive [e21, htg] at 0x800013a4
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      exact fa_num (st1 := st1) (G1 := G1) hlive h1 hx hpt (hc1.mod (by keeps_tac Keeps.refl _ _))
        hW ho rfl rfl (hk.okIdx rfl rfl)
    | str q =>
      cases v with
      | num _ => exact hv.elim
      | str s =>
      obtain ⟨o, ho', rfl, rfl⟩ := hv
      have hr : dcFunc 70 (st1.push (.str o.s)) 97 peek neg = .ok (st1.push (.str [o.s.headD 0])) :=
        rfl
      rw [hr] at hk
      simp only [GV.tag, GV.ptr] at htg hpt
      bc_run hlive hlive [e21, htg] at 0x80001328
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      bc_run hlive hlive [e21, htg] at 0x80001328
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      exact fa_str (st1 := st1) (G1 := G1) hlive h1 ho' hpt (hc1.mod (by keeps_tac Keeps.refl _ _))
        hW ho rfl rfl (hk.okIdx rfl rfl)

end

end Dc.Mach
