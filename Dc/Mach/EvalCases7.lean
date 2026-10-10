import Dc.Mach.EvalCases6

/-!
# `evalstr`'s loop: `DC_EVALREG` (M10)

`dcFunc_peek`: a register evaluation names the lookahead character.
`evs_reg`: with the register's value, the value pushed and the
`DC_EVALTOS` code on the rest after the register name; without, on to that
rest.
-/

namespace Dc

/-- The register a result evaluates is the lookahead. -/
def ResPeek (peek : Option Nat) : Res → Prop
  | .evalReg _ r => peek = some r
  | _ => True

theorem dcFunc_peek {lm : Nat} {st : St} {c : Nat} {peek : Option Nat} {neg : Bool} :
    ResPeek peek (dcFunc lm st c peek neg) := by
  unfold dcFunc; dsimp only
  rcases hs : st.stack with _ | ⟨v, rest⟩
  rotate_left
  rcases v with n | s
  all_goals simp only [hs]
  all_goals split
  all_goals (repeat' split) <;> simp only [ResPeek]
  all_goals first | trivial | rfl | simp_all

end Dc

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The call's data as an `EvStep`. -/
theorem EvCall.step {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64}
    {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
    {hs xs : List GV} {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
    {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
    {C' : BcConsts} {G' : DcG} {st' : St} {ex : List GV}
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex) : EvStep S sp W (leakAllow c) M G hs xs M' H' F' L' C' G' st' ex :=
  EvStep.ofPost e.mem.only e.post

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st' st'' : St} {ex : List GV} {r : Status} {n : Nat}
  {Ge : DcG} {hse xse : List GV} {ke : Nat}

/-- **`DC_EVALREG`** from `0x800016d8` (either dispatch table), the
register `p` the lookahead. -/
theorem evs_reg_at (hlive : ∀ p ∈ dcText, live p.1) (IH : LoopIH live S Q n) (TIH : TosIH live S Q n)
    {p : Nat} {rest : List Nat}
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c (p :: rest) td neg o Rc R' Mc M' H' F'
      L' C' G' st' ex)
    (hres : dcFunc 70 st c (some p) neg = .evalReg st' p)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: p :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r)
    {R1 : Nat → BitVec 64} (k1 : Keeps [10, 15] R1 R') :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x800016d8#64 R1 M' := by
  have h1 := dcFunc_strBound (lm := 70) (c := c) (peek := some p) (neg := neg) e.ev.sb (by decide)
  have h2 := dcFunc_arrSorted (lm := 70) (c := c) (peek := some p) (neg := neg) e.ev.srt
  rw [hres] at h1 h2
  have hlc : leakOne c ≤ k := by
    cases hg : regGet st' p with
    | none => exact (hfu.evalRegNone hres hg).2.2
    | some v => exact (hfu.evalReg hres hg).2.2
  obtain ⟨o0, -, -, -, ev0⟩ := e.same (e.hal hlc) h1 h2 (R2 := R1) (k1.mono (by decide))
  have hstk := e.ev.stk; have hab := e.ev.room; have hbud := ev0.budget
  have hfr := e.ev.frame
  have hfl := hfr.lo; have hfh := hfr.hi; have hfa := hfr.al
  have hpk : ldv .lw M' (sp - 176 + 28) = BitVec.ofNat 64 p := e.peek
  have hp : p < 256 := e.ev.chars p (by simp)
  have e8 : R1 8 + 2#64 = R' 23 + BitVec.ofNat 64 1 := by rw [k1.get 8 (by decide)]; exact e.eat8
  have hW : 176 + 336 ≤ W := by omega
  refine rt_reg hlive ev0.dc (by simp only [List.length_append] at hbud ⊢; omega) hp
    (hfr.within (m := 176) (n := 336) (by omega) (by decide)) (by simp only [heapEnd] at hab ⊢; omega)
    ⟨fun i hi => hfr.own _ (by omega) (by omega), by omega, by omega, by omega⟩
    (fun b h1 h2 => hfr.own b (by omega) (by omega)) ev0.r2 hpk
    (fun R2 M2 H2 F2 L2 C2 Gp cn g v hg k2 h8 h25 hsn h4 hpin4 hout => ?_)
    (fun hg R2 M2 H2 k2 h8 h12 h3 hout => ?_)
    (fun R2 M2 sp2 l1 l2 e2 hal2 hout => ev0.oomK hoom (sp' := sp2) (by omega) (by omega) e2 hal2
      fun a e1 e2 e3 e5 _ => hout a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))
        (by omega))
  · -- the value pushed, then `DC_EVALTOS`
    obtain ⟨hfu', -, -⟩ := hfu.evalReg hres hg
    have hst := e.step.then (by rw [← List.append_assoc]; exact h4) (by rw [hsn.lk]; exact Nat.le_refl _)
      (by rw [List.append_assoc] at hpin4; exact hpin4)
      fun a e1 e2 e3 e5 _ => hout a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))
        (by omega)
    obtain ⟨o', -, -, -, ev'⟩ := ev_advS e.ev e.kc e.c23 e.k1 e.e2 hst (e.hal hlc)
      (h1.push (h1.regGet hg)) (h2.stack _) (m := 1) (td' := td) (neg' := false) (by simp) e.ev.tdLt
      (R2 := R2) ((k2.mono (by decide)).trans (k1.mono (by decide))) (by rw [h8, e8])
      (by rw [k2.get 24 (by decide), k1.get 24 (by decide), e.k1.get 24 (by decide),
        e.kc.get 24 (by decide)]; exact e.ev.s8)
    simp only [List.drop_one, List.tail_cons] at ev' hfu'
    exact TIH t0 sp W d _ q M0 R0 R2 M2 H2 F2 L2 C2 _ hs _ (st'.push v) st'' rest td o' r Ge hse
      xse ke hfu' ev' h25 hoom htl
      (by show Gp.lk.length + _ + _ ≤ _; rw [hsn.lk]; exact e.grow hlc hgrow)
      ((e.pin hpin).trans (hpin4.mono fun g hg => List.mem_append_right _ (List.mem_of_mem_tail hg)))
      hk
  · -- no value: on to the rest
    obtain ⟨hfu', -, -⟩ := hfu.evalRegNone hres hg
    have hst := e.step.then (by rw [← List.append_assoc]; exact h3) (Nat.le_refl _)
      (StrPin.refl _ _)
      fun a e1 e2 e3 e5 _ => hout a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))
        (by omega)
    obtain ⟨o', -, -, -, ev'⟩ := ev_advS e.ev e.kc e.c23 e.k1 e.e2 hst (e.hal hlc) h1 h2
      (m := 1) (td' := td) (neg' := false) (by simp) e.ev.tdLt
      (R2 := R2) ((k2.mono (by decide)).trans (k1.mono (by decide))) (by rw [h8, e8])
      (by rw [k2.get 24 (by decide), k1.get 24 (by decide), e.k1.get 24 (by decide),
        e.kc.get 24 (by decide)]; exact e.ev.s8)
    simp only [List.drop_one, List.tail_cons] at ev' hfu'
    exact ev_cont hlive (bltu_800015a0 hlive) ev' hfu' htl (e.grow hlc hgrow) (e.pin hpin) hk
      fun hne => IH t0 sp W d _ q M0 R0 R2 M2 H2 F' L' C' G' hs _ st' st'' _ o' r Ge hse xse ke
        hfu' hne ev' h12 hoom htl (e.grow hlc hgrow) (e.pin hpin) hk

/-- **`DC_EVALREG`**: the status dispatch then `evs_reg_at`. -/
theorem evs_reg (hlive : ∀ p ∈ dcText, live p.1) (IH : LoopIH live S Q n) (TIH : TosIH live S Q n)
    {rest : List Nat} {reg : Nat}
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (hres : dcFunc 70 st c rest.head? neg = .evalReg st' reg) (h10 : R' 10 = BitVec.ofNat 64 2)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  have hpe : rest.head? = some reg := by
    have := dcFunc_peek (lm := 70) (st := st) (c := c) (peek := rest.head?) (neg := neg)
    rw [hres] at this; exact this
  cases rest with
  | nil => cases hpe
  | cons p rest' =>
    cases hpe
    simp only [List.cons_ne_nil, ite_false]
    exact evm_2 hlive h10 e.cs fun R1 k1 =>
      evs_reg_at hlive IH TIH e hres hfu hoom htl hgrow hpin hk k1

end

end Dc.Mach
