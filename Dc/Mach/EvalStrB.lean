import Dc.Mach.EvalScan
import Dc.Mach.EvalNum

/-!
# `evalstr`'s loop: `DC_STR` (M10)

`DC_STR` (`0x800015e4`, after `[`): the scan to the matching `]`
(`scan_loop`, or nothing for an empty rest), then `rt_str` (`0x80001640`):
the end position saved at `sp + 8`, `dc_makestring` of the contents,
`dc_push` of the new string, `s0` the end position, to the test at
`0x80001660`. `evs_str_k : EvStrCore`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The bytes `DC_STR`'s span leaves as they were: all but the 64 bytes
below `sp` and the scratch words `[sp, sp + 88)`. -/
def StrOut (sp : Nat) (M' M : Mem) : Prop :=
  ∀ a, OutHeap a → ¬ (DcGlob a ∧ ¬ PinWords a) → ¬ frameIn sp 64 a → ¬ (sp ≤ a ∧ a < sp + 88) →
    imgM M' a = imgM M a

/-- **`DC_STR`'s span** at `0x80001640` (frame `sp`, `s7` the contents `s`
at `a`, `a1` their length, `a5` the end position `e`). -/
theorem rt_str {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t : String} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {sp a e : Nat}
    {s : List Nat} (h : DcAt S M H F L C G hs st) (hsrc : MsSrc S M G sp a s)
    (hsf : StackFrame S sp 64) (hab : heapEnd + 64 ≤ sp) (hown : ∀ b, sp ≤ b → b < sp + 88 → S b)
    (hsrcl : a + s.length ≤ sp)
    {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp) (h23 : R 23 = BitVec.ofNat 64 a)
    (h11 : R 11 = BitVec.ofNat 64 s.length) (h15 : R 15 = BitVec.ofNat 64 e)
    (hk : ∀ R2 M2 H2 b1 b2 c, Keeps (8 :: 12 :: cClob) R2 R → R2 8 = BitVec.ofNat 64 e →
      R2 12 = 0#64 →
      DcAt S M2 H2 F L C { { G with strs := msObj b1 b2 s :: G.strs } with
        stk := (c, .str b1.pay) :: G.stk } hs (st.push (.str s)) →
      StrOut sp M2 M → DWO live S Q t 0x80001660#64 R2 M2)
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 64) → StrOut sp M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80001640#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  bc_run hlive hS [h2, h23, h11, h15] at 0x80003a58
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | skip
  have hm1 : MemOnly (fun x => sp + 8 ≤ x ∧ x < sp + 16) (writeLog M [(sp + 8, 8, BitVec.ofNat 64 e)]) M :=
    fun x hx => imgM_store_miss _ _ (by omega)
  have hP1 : ∀ x, (sp + 8 ≤ x ∧ x < sp + 16) → OutHeap x ∧ ¬ DcGlob x := fun x hx =>
    have := above_sp (sp := sp) (a := x) (by omega) (by omega)
    ⟨this.1, this.2.1⟩
  have hsrc1 : MsSrc S (writeLog M [(sp + 8, 8, BitVec.ofNat 64 e)]) G sp a s :=
    ⟨hsrc.own, hsrc.loc, fun i hi => by rw [hm1 _ (by omega)]; exact hsrc.val i hi, hsrc.byte, hsrc.len⟩
  refine dc_makestring_spec hlive (h.outWrite hm1 hP1) hsrc1 hsf hab _ (by bsimp [h2]) (by bsimp [])
    (by bsimp [h11]) (by bsimp []) (fun R3 M3 H3 b1 b2 k3 e32 etag e11 h3 hout3 => ?_)
    (fun R3 M3 e3 hout3 => hoom R3 M3 e3 fun x e1 e2 e4 e5 => by
      rw [hout3 x e1 e2 e4]; exact hm1 x (fun hx => e5 (by omega)))
  have e32' : R3 2 = BitVec.ofNat 64 sp := by rw [e32]; bsimp [h2]
  bsimp []
  bc_run hlive hS [e32'] at 0x80002da4
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | skip
  have hm2 : MemOnly (fun x => sp + 64 ≤ x ∧ x < sp + 80)
      (writeLog (writeLog M3 [(sp + 64, 8, R3 10)]) [(sp + 72, 8, R3 11)]) M3 :=
    fun x hx => by rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hP2 : ∀ x, (sp + 64 ≤ x ∧ x < sp + 80) → OutHeap x ∧ ¬ DcGlob x := fun x hx =>
    have := above_sp (sp := sp) (a := x) (by omega) (by omega)
    ⟨this.1, this.2.1⟩
  refine dc_push_spec hlive (h3.outWrite hm2 hP2) (v := .str s) ⟨msObj b1 b2 s, List.mem_cons_self, rfl, rfl⟩
    hsf hab _ ⟨by bsimp []; exact etag, by bsimp []; exact e11⟩ (by bsimp [e32']) (by bsimp [])
    (fun R4 M4 H4 c k4 h4 hout4 => ?_)
    (fun R4 M4 e4 hout4 => hoom R4 M4 e4 fun x e1 e2 e4 e5 => by
      rw [hout4 x e1 e2 e4, hm2 x (fun hx => e5 (by omega)), hout3 x e1 e2 e4]
      exact hm1 x (fun hx => e5 (by omega)))
  have hout : StrOut sp M4 M := fun x e1 e2 e4 e5 => by
    rw [hout4 x e1 e2 e4, hm2 x (fun hx => e5 (by omega)), hout3 x e1 e2 e4]
    exact hm1 x (fun hx => e5 (by omega))
  have hag : ∀ x, sp + 8 ≤ x → x < sp + 16 →
      imgM M4 x = imgM (writeLog M [(sp + 8, 8, BitVec.ofNat 64 e)]) x := fun x h1 h2 => by
    have hb := above_sp (sp := sp) (a := x) (by omega) (by omega)
    rw [hout4 _ hb.1 (nglob_pin hb.2.1) (hb.2.2 _), hm2 _ (by omega),
      hout3 _ hb.1 (nglob_pin hb.2.1) (hb.2.2 _)]
  have hld : ldv .ld M4 (sp + 8) = BitVec.ofNat 64 e := by
    rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]
    exact ldv_store_hit _ _ _
  have e42 : R4 2 = BitVec.ofNat 64 sp := by rw [k4.get 2 (by decide)]; bsimp [e32']
  bsimp []
  bc_run hlive hS [e42, hld] at 0x80001660
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | skip
  exact hk _ M4 H4 b1 b2 c
    (by keeps_tac ((k4.mono (by decide)).trans (by keeps_tac ((k3.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _)))))
    (by bsimp []) (by bsimp []) h4 hout

/-- The contents of a `[`…`]` from the text after the command. -/
theorem EvRest.scanSrc {S : Nat → Prop} {M : Mem} {G : DcG} {R : Nat → BitVec 64} {a sp : Nat}
    {rest : List Nat} (er : EvRest S M G R a rest) :
    MsSrc S M G sp a (scanStr 1 rest).1 := by
  obtain ⟨a1, -, a3⟩ := scanStr_split 1 rest
  have hg : ∀ i, i < (scanStr 1 rest).1.length → (scanStr 1 rest).1.getD i 0 = rest.getD i 0 :=
    fun i hi => by
      rw [show (scanStr 1 rest).1.getD i 0 = (rest.take (scanStr 1 rest).1.length).getD i 0 from
        congrArg (fun l => l.getD i 0) a1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]
  exact
    { own := ⟨fun i hi => er.own.own i (by omega), er.own.lo, by have := er.own.hi; omega⟩
      loc := fun i hi => .inl (er.inb i (by omega))
      val := fun i hi => by rw [hg i hi]; exact er.val i (by omega)
      byte := fun x hx => er.byte x (by rw [a1] at hx; exact List.mem_of_mem_take hx)
      len := by have := er.len; omega }

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {ex : List GV}

/-- **`DC_STR` after the scan** (`0x80001640`, `a1` the contents' length,
`a5` the end of the scan): `rt_str`, the invariant over the rest after the
`]`, the test at `0x80001660`. -/
theorem evs_str_tail (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex) (hlc : leakOne c ≤ k) (hoom : EvOom live S Q sp W q M0)
    (hhead : EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs
      (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩)
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs (st.push (.str (scanStr 1 rest).1))
      ⟨(scanStr 1 rest).2, td, false⟩)
    {R2 : Nat → BitVec 64} (k2 : Keeps [10, 11, 12, 13, 14, 15] R2 R')
    (h11 : R2 11 = BitVec.ofNat 64 (scanStr 1 rest).1.length)
    (h15 : R2 15 = R' 23 + BitVec.ofNat 64 (rest.length - (scanStr 1 rest).2.length)) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001640#64 R2 M' := by
  obtain ⟨o0, -, -, -, ev0⟩ := e.same (e.hal hlc) e.ev.sb e.ev.srt (R2 := R2) (k2.mono (by decide))
  obtain ⟨a, er⟩ := ev0.rest
  have hstk := e.ev.stk; have hab := e.ev.room
  have hfr := e.ev.frame
  have hfl := hfr.lo; have hfh := hfr.hi
  have h23 : R' 23 = BitVec.ofNat 64 a := by
    rw [e.k1.get 23 (by decide), e.c23, ← er.r8, k2.get 8 (by decide), e.k1.get 8 (by decide),
      e.kc.get 8 (by decide)]
  obtain ⟨-, a2, a3⟩ := scanStr_split 1 rest
  have hin := ev0.dc.inBlocks_heap (er.inb rest.length (Nat.le_refl _))
  simp only [heapStart, heapEnd] at hin hab
  refine rt_str hlive ev0.dc er.scanSrc (hfr.within (m := 176) (n := 64) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (fun b h1 h2 => hfr.own b (by omega) (by omega)) (by omega)
    ev0.r2 (by rw [k2.get 23 (by decide)]; exact h23) h11
    (by rw [h15, h23, BitVec.ofNat_add_ofNat])
    (fun R3 M3 H3 b1 b2 c3 k3 h8 h12 h3 hout => ?_)
    (fun R3 M3 e3 hout => ev0.oomK hoom (sp' := sp - 176 - 64) (by omega) (by omega) e3
      (by have := hfr.al; omega)
      fun x e1 e2 e3 e5 _ => hout x e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)) e5)
  have hrl : rest.length < 2 ^ 24 := by
    obtain ⟨i, hi, hdrop, -⟩ := e.ev.pos
    have := congrArg List.length hdrop
    simp only [List.length_drop, List.length_cons] at this
    have := e.ev.strLen; omega
  rw [List.append_assoc] at h3
  have hst := e.step.then h3 (by exact Nat.le_refl _) (StrPin.cons _ _ _)
    fun x e1 e2 e3 e5 _ => hout x e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)) e5
  obtain ⟨o', -, -, -, ev'⟩ := ev_advS e.ev e.kc e.c23 e.k1 e.e2 hst (e.hal hlc) (e.ev.sb.scan hrl)
    (e.ev.srt.stack _) (m := rest.length - (scanStr 1 rest).2.length) (td' := td) (neg' := false)
    (by omega) e.ev.tdLt (R2 := R3) ((k3.mono (by decide)).trans (k2.mono (by decide)))
    (by rw [h8, h23, BitVec.ofNat_add_ofNat])
    (by rw [k3.get 24 (by decide), k2.get 24 (by decide), e.k1.get 24 (by decide),
      e.kc.get 24 (by decide)]; exact e.ev.s8)
  rw [← a2] at ev'
  have h12' : R3 12 = boolWord false := by rw [h12]; rfl
  have hc := ev_cont_k (bltu_80001660 hlive) ev' h12' (e.grow0 hlc)
    (e.pin0.trans (StrPin.cons _ _ _)) hhead hend
  exact hc

/-- **`DC_STR`** from `0x800015e4` (either dispatch table): the scan to the
matching `]`, then `evs_str_tail`. -/
theorem evs_str_at (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex) (hlc : leakOne c ≤ k) (hoom : EvOom live S Q sp W q M0)
    (hhead : EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs
      (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩)
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs (st.push (.str (scanStr 1 rest).1))
      ⟨(scanStr 1 rest).2, td, false⟩)
    {R1 : Nat → BitVec 64} (k1 : Keeps [10, 15] R1 R') :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800015e4#64 R1 M' := by
  obtain ⟨o0, -, -, -, ev0⟩ := e.same (e.hal hlc) e.ev.sb e.ev.srt (R2 := R1) (k1.mono (by decide))
  obtain ⟨a, er⟩ := ev0.rest
  have h23 : R' 23 = BitVec.ofNat 64 a := by
    rw [e.k1.get 23 (by decide), e.c23, ← er.r8, k1.get 8 (by decide), e.k1.get 8 (by decide),
      e.kc.get 8 (by decide)]
  have h23' : R1 23 = BitVec.ofNat 64 a := by rw [k1.get 23 (by decide)]; exact h23
  have h9 := er.r9
  have hin := ev0.dc.inBlocks_heap (er.inb rest.length (Nat.le_refl _))
  have hin0 := ev0.dc.inBlocks_heap (er.inb 0 (Nat.zero_le _))
  have hS : HeapOwn S := fun a e1 e2 => ev0.dc.heap.heap.own a e1 e2
  simp only [heapStart, heapEnd] at hin hin0 hS
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hlen := er.len
  bc_run hlive hS [h23', h9] at 0x80001618 0x80001640
  all_goals try bc_run hlive hS [h23', h9] at 0x80001618 0x80001640
  · -- a nonempty rest: the scan
    intro hc
    have hval : ∀ i, i < rest.length → ldv .lbu M' (a + i) = BitVec.ofNat 64 (rest.getD i 0) :=
      fun i hi => by
        rw [ldv_lbu, er.val i hi]
        have hb := er.byte (rest.getD i 0) (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi)
        generalize rest.getD i 0 = b at hb ⊢
        apply BitVec.eq_of_toNat_eq
        simp [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
        omega
    have h8 : R1 8 = BitVec.ofNat 64 (a - 1) := by
      have e8 := er.r8
      have : R1 8 = BitVec.ofNat 64 a - 1#64 := by rw [← e8, BitVec.add_sub_cancel]
      rw [this]; exact BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) (by omega)
    refine scan_loop hlive hS (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
      (by omega) (by omega) rfl hval er.byte rest.length 0 1 _ (by omega) (by omega) (Nat.le_refl _)
      (by omega) (by bsimp [h8]) (by bsimp [h9]) (by bsimp []) (by bsimp []) (by bsimp [])
      (by bsimp []) fun R2 k2 e11 e15 => ?_
    refine evs_str_tail hlive e hlc hoom hhead hend (R2 := R2)
      (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac (k1.mono (by decide)))))
      (by rw [e11]; simp) (by rw [e15, h23, BitVec.ofNat_add_ofNat]; congr 1
                              have := (scanStr_split 1 rest).2.2; simp only [List.drop_zero] at *; omega)
  · -- an empty rest: nothing to scan
    intro hc
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    bc_run hlive hS [h23', h9] at 0x80001640
    refine evs_str_tail hlive e hlc hoom hhead hend
      (by keeps_tac (k1.mono (by decide))) (by bsimp []; rfl) (by bsimp [h23']; rw [h23]; simp [scanStr])

end

/-- **`DC_STR`** (status `6`), continuation-generic: the status dispatch then
`evs_str_at`. -/
theorem evs_str_k {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) : EvStrCore live S Q := by
  intro t0 sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C' G' ex
    e _ h10 hlc hoom hhead hend
  split
  · exact evl_6 hlive h10 e.cs fun R1 k1 => evs_str_at hlive e hlc hoom hhead hend k1
  · exact evm_6 hlive h10 e.cs fun R1 k1 => evs_str_at hlive e hlc hoom hhead hend k1

end Dc.Mach
