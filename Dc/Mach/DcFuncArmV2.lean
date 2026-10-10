import Dc.Mach.DcFuncArmV1
import Dc.Mach.DcFuncArm2
import Dc.Mach.DcSqrt

/-!
# `dc_func`'s `v` arm (M10)

`v` pops a datum. A number goes to `dc_sqrt` (scale `dc_scale`, result slot
`sp + 160`); on success the popped reference is freed (`dc_free_num`) and the
root pushed under the popped type word, a negative operand leaves the popped
reference lost (`DcAt.leak`). A string prints `"%s: square root of nonnumeric
attempted\n"` to `stderr` and is lost (the post's `ex`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `"%s: square root of nonnumeric attempted\n"`. -/
theorem sqrtNonnumMsg : ProgMsg 0x80007a98 38 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩


/-- **The frame after a callee** that may also write `dc_func`'s own locals
(below the saved `ra`), e.g. a result slot of the frame. -/
theorem FnAt.callL {S : Nat → Prop} {sp W Wc : Nat} {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) (hW : 192 + Wc ≤ W) (k : Keeps (1 :: 2 :: cClob) R' R)
    (e2 : R' 2 = R 2)
    (hout : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn (sp - 192) Wc a →
      ¬ frameIn (sp - 8) 184 a → imgM M' a = imgM M a) : FnAt S sp W M0 R0 R' M' := by
  have hh := hc.room
  have hl := hc.frame.lo
  have hab : heapEnd ≤ sp - 192 := by simp only [heapEnd] at hh ⊢; omega
  refine { hc with r2 := e2.trans hc.r2, ra := ?_, keep := ?_, out := ?_ }
  · rw [← hc.ra]
    exact ldv_congr .ld fun j hj => by
      have := above_sp hab (a := sp - 192 + 184 + j) (by omega)
      exact hout _ this.1 this.2.1 (not_ocG_of_ge hab (by omega)) (this.2.2 _)
        (by simp only [frameIn, widthOfM] at hj ⊢; omega)
  · exact (k.mono (by decide)).trans hc.keep
  · intro a e1 e2 e3 e4
    exact (hout a e1 e2 e3 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))
      fun hf => e4 (by simp only [frameIn] at hf ⊢; omega)).trans (hc.out a e1 e2 e3 e4)

/-- `dcFunc`'s `v` on a popped number. -/
theorem dcFunc_v (st : St) (n : Num) (peek : Option Nat) (neg : Bool) :
    dcFunc 70 (st.push (.num n)) 118 peek neg =
      match Num.cmp n (Num.zero 0) with
      | .lt => .ok st
      | .eq => .ok (st.push (.num (Num.zero 0)))
      | .gt => if Num.cmp n Num.one == .eq then .ok (st.push (.num Num.one)) else .sqrt st n := rfl

/-- `v`'s result through `SqOut`: the returned code and state. -/
theorem sqOut_fn {st : St} {n r : Num} (peek : Option Nat) (neg : Bool)
    (hO : SqOut n st.scale (some r)) :
    FnOut (st.push (.num n)) (dcFunc 70 (st.push (.num n)) 118 peek neg) 0 (st.push (.num r)) := by
  rw [dcFunc_v]
  cases hO with
  | zero hz => rw [hz]; exact .ok _
  | one hg h1 => rw [hg]; simp only [h1, beq_self_eq_true, ite_true]; exact .ok _
  | root hg h1 hs =>
    rw [hg]
    have : (Num.cmp n Num.one == .eq) = false := by simpa using h1
    simp only [this]
    exact .sqrt hs

theorem sqOut_none {st : St} {n : Num} (peek : Option Nat) (neg : Bool)
    (hO : SqOut n st.scale none) : dcFunc 70 (st.push (.num n)) 118 peek neg = .ok st := by
  rw [dcFunc_v]
  cases hO with
  | neg hl => rw [hl]

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {M0 : Mem} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {hs : List GV} {sp W : Nat} {R0 : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

set_option hygiene false in
/-- `dc_func`'s frame bounds and the bytes at or above `sp - 192`. -/
macro "fv_frame " hc:ident : tactic =>
  `(tactic| (
    have hsf : StackFrame S sp 192 := ($hc).frame.mono ($hc).big
    have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
    have hab := ($hc).room; simp only [heapEnd] at hab
    have htx : tohostAddr = 0x8001ad00 := rfl
    have hfr : ∀ a, sp - 192 ≤ a → OutHeap a ∧ ¬ DcGlob a ∧ ∀ n, ¬ frameIn (sp - 192) n a :=
      fun a ha => above_sp (by simp only [heapEnd]; omega) ha))

/-- `v` after `dc_free_num` (`0x800012f8`): the root pushed under the popped
type word, `DC_OKAY`. -/
theorem fv_push (hlive : ∀ p ∈ dcText, live p.1) {st st1 : St} {res : Res} {r : Num} {y : Nat}
    {M3 : Mem} {H3 : Heap} {F3 : List Blk} {L3 : List NumObj} {C3 : BcConsts} {G G2 : DcG}
    {R3 : Nat → BitVec 64}
    (h3 : DcAt S M3 H3 F3 L3 C3 G2 (.num y :: hs) st1) (hy : (GV.num y).Den ⟨L3, G2.strs⟩ (.num r))
    (hc3 : FnAt S sp W M0 R0 R3 M3) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (e3b : R3 2 = BitVec.ofNat 64 (sp - 192))
    (hy3 : ldv .ld M3 (sp - 192 + 160) = BitVec.ofNat 64 y)
    (htg3 : (ldv .ld M3 (sp - 192 + 16)).toNat % 2 ^ 32 = 1)
    (hlk : G2.lk.length ≤ G.lk.length + 2) (hstr : G2.strs = G.strs)
    (hf : FnOut st res 0 (st1.push (.num r))) (hk : FnK live S Q t0 st res G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st1.out) 0x800012f8#64 R3 M3 := by
  fv_frame hc3
  bc_run hlive hlive [e3b, hy3] at 0x80002da4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hc4 : FnAt S sp W M0 R0 R3 (writeLog M3 [(sp - 192 + 24, 8, BitVec.ofNat 64 y)]) :=
    hc3.callL (Wc := 0) (by omega) (Keeps.refl _ _) rfl fun a _ _ _ _ e5 =>
      imgM_store_miss _ _ (by simp only [frameIn] at e5; omega)
  have h4 := h3.outWrite (MemOnly.store M3 (sp - 192 + 24) 8 (BitVec.ofNat 64 y)) fun a ha =>
    ⟨(hfr a (by omega)).1, (hfr a (by omega)).2.1⟩
  refine dc_push_spec hlive h4 hy (hc4.cf (Wc := 64) (by omega)) (hc4.cab (by omega)) _
    ⟨by bsimp []; exact htg3, by bsimp []; rfl⟩ (by bsimp [e3b]) (by bsimp [])
    (fun R5 M5 H5 c5 k5 h5 hout5 => ?_) (fun R5 M5 e5 hout5 => ?_)
  · have hc5 := hc4.callS (R' := R5) (Wc := 64) (by omega)
      (by keeps_tac ((k5.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      ((k5.get 2 (by decide)).trans (by bsimp [])) hout5
    bsimp []
    bc_run hlive hlive [] at 0x80000c10
    exact fa_ok (st' := st1.push (.num r)) hlive (ex := []) h5 hc5 hk hf (by simp) hlk
      (StrPin.of_eq hstr _)
  · exact hc4.oom ho (Wc := 64) (by omega) (by omega) (by omega) e5 fun a e1 e2 _ e4 => hout5 a e1 e2 e4

/-- `v` after `dc_sqrt` succeeded (`0x800012ec`): the popped reference freed
(`dc_free_num`), then `fv_push`. -/
theorem fv_ret (hlive : ∀ p ∈ dcText, live p.1) {st st1 : St} {res : Res} {r : Num} {y : Nat}
    {x : NumObj} {pl : List Nat} {M2 : Mem} {H2 : Heap} {F2 : List Blk} {L2 : List NumObj}
    {C2 : BcConsts} {G G1 : DcG} {R2 : Nat → BitVec 64}
    (h2 : DcAt S M2 H2 F2 L2 C2 { G1 with lk := pl ++ G1.lk } (.num y :: .num x.rep.p :: hs) st1)
    (hy : (GV.num y).Den ⟨L2, G1.strs⟩ (.num r))
    (hc2 : FnAt S sp W M0 R0 R2 M2) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (e2b : R2 2 = BitVec.ofNat 64 (sp - 192)) (e10 : R2 10 = 0#64)
    (hrq : ldv .ld M2 (sp - 192 + 160) = BitVec.ofNat 64 y)
    (hpt2 : ldv .ld M2 (sp - 192 + 24) = BitVec.ofNat 64 x.rep.p)
    (htg2 : (ldv .ld M2 (sp - 192 + 16)).toNat % 2 ^ 32 = 1)
    (hpl : pl.length ≤ 1) (hlk : G1.lk = G.lk) (hstr : G1.strs = G.strs)
    (hf : FnOut st res 0 (st1.push (.num r))) (hk : FnK live S Q t0 st res G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st1.out) 0x800012ec#64 R2 M2 := by
  fv_frame hc2
  bc_run hlive hlive [e10, e2b] at 0x80002ba0
  bc_run hlive hlive [e10, e2b] at 0x80002ba0
  refine dc_free_num_specP hlive (Pend.id _) (h2.perm (List.Perm.swap _ _ _))
    (hc2.frame.slot (q := sp - 192 + 24) (by omega) (by omega) (by omega))
    (.above (by simp only [heapEnd]; omega)) hpt2
    (hc2.cf (Wc := 32) (by omega)) (hc2.cab (by omega)) (.inr (by omega)) _ (by bsimp [e2b])
    (by bsimp [e2b]) (by bsimp []) fun R3 M3 H3 F3 L3 C3 k3 h3 _ hout3 _ hkeep => ?_
  have e3b : R3 2 = BitVec.ofNat 64 (sp - 192) := (k3.get 2 (by decide)).trans (by bsimp [e2b])
  have hc3 := hc2.callL (R' := R3) (M' := M3) (Wc := 32) (by omega)
    (by keeps_tac ((k3.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (e3b.trans e2b.symm) fun a e1 e2 _ e4 e5 => hout3 a e1 e2 e4 fun hb => e5 (by
      simp only [slotBytes, frameIn] at hb ⊢; omega)
  have m3 : ∀ a, sp - 192 ≤ a → ¬ (sp - 192 + 24 ≤ a ∧ a < sp - 192 + 32) →
      imgM M3 a = imgM M2 a := fun a l1 l2 =>
    hout3 a (hfr a l1).1 (hfr a l1).2.1 ((hfr a l1).2.2 _) (by simp only [slotBytes]; omega)
  have hy3 : ldv .ld M3 (sp - 192 + 160) = BitVec.ofNat 64 y := by
    rw [ldv_congr .ld fun j hj => m3 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hrq
  have htg3 : (ldv .ld M3 (sp - 192 + 16)).toNat % 2 ^ 32 = 1 := by
    rw [ldv_congr .ld fun j hj => m3 _ (by omega) (by simp only [widthOfM] at hj; omega)]
    exact htg2
  bsimp []
  exact fv_push hlive h3 (hkeep _ List.mem_cons_self _ hy) hc3 hW ho e3b hy3 htg3
    (by simp only [List.length_append, hlk] at *; omega) hstr hf hk

/-- `v` on a popped number (`0x800011f4`): `dc_sqrt (value, dc_scale, &result)`,
then `fv_ret`; a negative operand returns `1` and the popped reference is lost. -/
theorem fv_num (hlive : ∀ p ∈ dcText, live p.1) {st1 : St} {x : NumObj} {o : Option Num}
    {M1 : Mem} {H1 : Heap} {G G1 : DcG} {R1 : Nat → BitVec 64}
    (h1 : DcAt S M1 H1 F L C G1 (.num x.rep.p :: hs) st1) (hx : x ∈ L)
    (hd : DatAt M1 (fnSlot sp) (.num x.rep.p))
    (hc1 : FnAt S sp W M0 R0 R1 M1) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0) (e21 : R1 2 = BitVec.ofNat 64 (sp - 192))
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlkb : G.lk.length + 2 ≤ 2 ^ 29)
    (hO : SqOut x.rep.num st1.scale o) (hz : x.rep.num.wid + st1.scale < 2 ^ 20)
    (hlk : G1.lk = G.lk) (hstr : G1.strs = G.strs)
    (hk : FnK live S Q t0 (st1.push (.num x.rep.num))
      (dcFunc 70 (st1.push (.num x.rep.num)) 118 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st1.out) 0x800011f4#64 R1 M1 := by
  fv_frame hc1
  have hS : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  have hG := h1.glob
  have htg := hd.lw
  have hpt := hd.ptr
  simp only [fnSlot, GV.tag, GV.ptr] at htg hpt
  rw [show sp - 192 + 16 + 8 = sp - 192 + 24 by omega] at hpt
  have hsc : ldv .lw M1 0x8001cd8c = BitVec.ofNat 64 st1.scale := h1.view.scale
  bc_run hlive hS [e21, htg, hpt, hsc] at 0x800025cc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [e21, htg, hpt, hsc] at 0x800025cc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hwd := NumRep.len_le_wid (h1.heap.nums x hx).shape (h1.den.norm x hx)
  have hlk1 : G1.lk.length + 2 ≤ 2 ^ 29 := by rw [hlk]; exact hlkb
  have hrm := hc1.big
  refine dc_sqrt_spec hlive h1 hx (by omega) (by omega)
    (by simp only [NumRep.num] at hz hwd ⊢; omega) hO (hc1.mulBase hmb)
    (hc1.cf (Wc := sqN) (by simp only [sqN]; omega)) (hc1.cab (by simp only [sqN]; omega))
    (hc1.frame.slot (q := sp - 192 + 160) (by omega) (by omega) (by omega)) (by omega) _
    (by bsimp []) (by bsimp []) (by bsimp [e21]) (by bsimp [e21]) (by bsimp []) ?_ ?_
    (fun R' M' sp' oo => fn_opOom hc1 ho (Wc := sqN) (by simp only [sqN]; omega) oo)
  · intro r hr R2 M2 H2 F2 L2 C2 pl y k2 e22 e102 hpl h2 hy hrq hout2
    subst hr
    have e2b : R2 2 = BitVec.ofNat 64 (sp - 192) := e22.trans (by bsimp [e21])
    have hc2 := hc1.callL (R' := R2) (M' := M2) (Wc := sqN) (by simp only [sqN]; omega)
      (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (e2b.trans e21.symm) fun a e1 e2 _ e4 e5 => hout2 a e1 e2 e4 fun hb => e5 (by
        simp only [slotBytes, frameIn] at hb ⊢; omega)
    have m2 : ∀ a, sp - 192 + 16 ≤ a → a < sp - 192 + 32 → imgM M2 a = imgM M1 a := fun a l1 l2 =>
      hout2 a (hfr a (by omega)).1 (hfr a (by omega)).2.1 ((hfr a (by omega)).2.2 _)
        (by simp only [slotBytes]; omega)
    have hpt2 : ldv .ld M2 (sp - 192 + 24) = BitVec.ofNat 64 x.rep.p := by
      rw [ldv_congr .ld fun j hj => m2 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hpt
    have htg2 : (ldv .ld M2 (sp - 192 + 16)).toNat % 2 ^ 32 = 1 := by
      rw [ldv_congr .ld fun j hj => m2 _ (by omega) (by simp only [widthOfM] at hj; omega)]
      exact hd.tag
    bsimp []
    exact fv_ret hlive h2 hy hc2 hW ho e2b e102 hrq hpt2 htg2 hpl hlk hstr
      (sqOut_fn (st := st1) peek neg hO) hk
  · intro hn R2 M2 H2 F2 L2 C2 k2 e22 e102 h2 hout2
    subst hn
    rw [sqOut_none (st := st1) peek neg hO] at hk
    have hc2 := hc1.callS (R' := R2) (Wc := sqN) (by simp only [sqN]; omega)
      (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
      (e22.trans (by bsimp [])) hout2
    bsimp []
    bc_run hlive hlive [e102] at 0x80000c10
    exact fa_ok (st' := st1) hlive (ex := []) (h2.leak (by omega)) hc2 hk (.ok _) (by simp)
      (by simp [hlk]) (StrPin.of_eq hstr _)

/-- `v` on a popped string (`0x800011f4`): the `stderr` message, the string's
reference lost. -/
theorem fv_str (hlive : ∀ p ∈ dcText, live p.1) {st1 : St} {q : Nat} {M1 : Mem} {H1 : Heap}
    {G G1 : DcG} {R1 : Nat → BitVec 64}
    (h1 : DcAt S M1 H1 F L C G1 (.str q :: hs) st1) (hd : DatAt M1 (fnSlot sp) (.str q))
    (hc1 : FnAt S sp W M0 R0 R1 M1) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (e21 : R1 2 = BitVec.ofNat 64 (sp - 192))
    (hlk : G1.lk = G.lk) (hstr : G1.strs = G.strs)
    (hk : FnK live S Q t0 st1 (.ok st1) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st1.out) 0x800011f4#64 R1 M1 := by
  fv_frame hc1
  have hS : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  have hG := h1.glob
  have htg := hd.lw
  simp only [fnSlot, GV.tag] at htg
  have hpn := h1.view.prog
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hS [e21, htg] at 0x80000774
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [e21, htg, hpn, stderr_word] at 0x80000774
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hrm := hc1.big
  refine fprintf_prog_spec hlive sqrtNonnumMsg (by decide) (hc1.cf (Wc := 304) (by omega))
    (by simp only [stderrAddr]; omega) h1.errFile _ (by bsimp [e21]) (by bsimp [stderrAddr])
    (by bsimp []) (by bsimp []) (by bsimp []) fun R2 M2 k2 hfr2 => ?_
  have hc2 := hc1.call (R' := R2) (M' := M2) (Wc := 304) (by omega)
    (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    ((k2.get 2 (by decide)).trans (by bsimp []))
    fun a _ _ _ hf => hfr2 a (by simp only [frameIn] at hf; omega)
  have h2 : DcAt S M2 H1 F L C G1 ([.str q] ++ hs) st1 :=
    h1.outWrite (P := frameIn (sp - 192) 304)
      (fun a ha => hfr2 a (by simp only [frameIn] at ha; omega)) fun a ha => by
        simp only [frameIn] at ha
        exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
          have := hg.lt; simp only [heapStart] at this; omega⟩
  bsimp []
  bc_run hlive hlive [] at 0x80000c10
  exact fa_ok (st' := st1) hlive h2 hc2 hk (.ok _) (by simp) (by simp [hlk])
    (StrPin.of_eq hstr _)

/-- `v` (`0x800011e8`): the square root of a popped number (`dc_sqrt`); a
string or a negative number is lost with a `stderr` message. -/
theorem fa_v (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {G : DcG}
    {R : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 1216 + rmStack (2 ^ 30) ≤ W)
    (ho : FnOom live S Q sp W M0) (hmb : MulBase S M0)
    (hhs : hs.length + 4 ≤ 2 ^ 20) (hlk : G.lk.length + 2 ≤ 2 ^ 29)
    (hsq : ∀ n rest, st.stack = .num n :: rest → ∃ o, SqOut n st.scale o)
    (hsz : ∀ n rest, st.stack = .num n :: rest → n.wid + st.scale < 2 ^ 20)
    (hk : FnK live S Q t0 st (dcFunc 70 st 118 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800011e8#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := hc.r2
  bc_run hlive hlive [e2] at 0x800011ec
  refine fn_pop (p := 0x800011ec) (tgt0 := 0x80000c10) hlive h (hc.mod (by keeps_tac Keeps.refl _ _))
    (by omega) (by bsimp []) (by decide) ?_ ?_ ?_ ?_
  fn_pop_sites st_800011ec st_800011f0
  · intro he R1 M1 hc1 h1
    have hr : dcFunc 70 st 118 peek neg = .ok st := by
      cases st with | mk stk => simp only at he; subst he; rfl
    rw [hr] at hk
    exact fa_ok hlive (ex := []) h1 hc1 hk (.ok _) (by simp) (by simp) (StrPin.refl _ _)
  · intro R1 M1 H1 G1 g v st1 est eG hc1 h1 hv hd
    subst est
    obtain ⟨c, rfl⟩ := eG
    simp only [Nat.reduceAdd]
    cases g with
    | str q =>
      cases v with
      | num _ => exact hv.elim
      | str s =>
        have hr : dcFunc 70 (st1.push (.str s)) 118 peek neg = .ok st1 := rfl
        rw [hr] at hk
        exact fv_str (st1 := st1) (G1 := G1) hlive h1 hd hc1 hW hc1.r2 rfl rfl (hk.okIdx rfl rfl)
    | num xp =>
      cases v with
      | str _ => exact hv.elim
      | num n =>
      obtain ⟨x, hx, rfl, rfl⟩ := hv
      obtain ⟨o, hO⟩ := hsq x.rep.num st1.stack rfl
      exact fv_num (st1 := st1) (G1 := G1) hlive h1 hx hd hc1 hW ho hmb hc1.r2 hhs hlk hO (hsz x.rep.num st1.stack rfl)
        rfl rfl hk

end

end Dc.Mach
