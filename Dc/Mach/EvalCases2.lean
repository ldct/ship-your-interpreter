import Dc.Mach.EvalCases1

/-!
# `evalstr`'s loop: `DC_EATONE` (M10)

`DC_EATONE` skips the lookahead character: after a character with a
lookahead, `s0 = s0 + 2` (`rt_eat_mid`); after the last character the
lookahead word is `EOF` and `s0 = s7` ends the string (`rt_eat_last`).
`EvCall.peek`: the lookahead word survives `dc_func`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The characters of the invariant's frame are bytes. -/
theorem EvAt.chars {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64}
    {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
    {hs xs : List GV} {st : St} {f : Frame} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o) : ∀ x ∈ f.s, x < 256 := by
  obtain ⟨i, -, hdrop, -⟩ := ev.pos
  intro x hx
  rw [← hdrop] at hx
  exact (ev.dc.view.strs o ev.strIn).byte x (List.mem_of_mem_drop hx)

/-- `DC_EATONE` after the last character (`EOF` at `sp + 28`): `s0 = s7`,
`a2 = 0`, the test at `0x800017d0`. -/
theorem rt_eat_last {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t : String} {R : Nat → BitVec 64} {M : Mem} {sp : Nat}
    (h2 : R 2 = BitVec.ofNat 64 (sp - 176)) (hsf : StackFrame S sp 176)
    (hpk : ldv .lw M (sp - 176 + 28) = 0xFFFFFFFFFFFFFFFF#64)
    (hk : ∀ R2, Keeps [8, 12, 14, 15] R2 R → R2 8 = R 23 → R2 12 = 0#64 →
      DWO live S Q t 0x800017d0#64 R2 M) :
    DWO live S Q t 0x80001704#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  bc_run hlive hlive [h2, hpk] at 0x800017d0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first | (intro hc; exact absurd rfl hc) | intro _ | skip
  bc_run hlive hlive [h2, hpk] at 0x800017d0
  exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp [])

namespace EvCall

variable {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st' : St} {ex : List GV}

/-- **The lookahead word survives `dc_func`** (it lies in `evalstr`'s
frame, above `dc_func`'s). -/
theorem peek (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F'
    L' C' G' st' ex) : ldv .lw M' (sp - 176 + 28) = peekWord rest.head? := by
  have hab := e.ev.room; have hstk := e.ev.stk
  rw [ldv_congr .lw fun j hj => ?_]
  · exact e.mem.peek
  have hj' : j < 4 := hj
  have ha := above_sp (sp := sp - 176) (a := sp - 176 + 28 + j)
    (by simp only [heapEnd] at hab ⊢; omega) (by omega)
  exact e.post.out _ ha.1 (nglob_pin ha.2.1)
    (not_ocG_of_ge (sp := sp - 176) (by simp only [heapEnd] at hab ⊢; omega) (by omega)) (ha.2.2 _)

/-- `s0` two characters on: `R' 8 + 2 = R' 23 + 1`. -/
theorem eat8 (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F'
    L' C' G' st' ex) : R' 8 + 2#64 = R' 23 + BitVec.ofNat 64 1 := by
  rw [e.k1.get 8 (by decide), e.k1.get 23 (by decide), e.kc.get 8 (by decide), e.c23,
    BitVec.add_assoc]
  rfl

end EvCall

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st' st'' : St} {ex : List GV} {r : Status} {n : Nat}
  {Ge : DcG} {hse xse : List GV} {ke : Nat}

/-- **`DC_EATONE`**: the lookahead skipped, on to `rest.tail`. -/
theorem evs_eat (hlive : ∀ p ∈ dcText, live p.1) (IH : LoopIH live S Q n)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (hres : dcFunc 70 st c rest.head? neg = .eatOne st') (h10 : R' 10 = BitVec.ofNat 64 1)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  obtain ⟨hfu', -, hlc⟩ := hfu.eatOne hres
  have h1 := dcFunc_strBound (lm := 70) (c := c) (peek := rest.head?) (neg := neg) e.ev.sb (by decide)
  have h2 := dcFunc_arrSorted (lm := 70) (c := c) (peek := rest.head?) (neg := neg) e.ev.srt
  rw [hres] at h1 h2
  have hsf : StackFrame S sp 176 := e.ev.frame.mono (by have := e.ev.stk; omega)
  have e2 : R' 2 = BitVec.ofNat 64 (sp - 176) := by rw [e.e2, e.kc.get 2 (by decide), e.ev.r2]
  have h24 : R' 24 = BitVec.ofNat 64 td := by
    rw [e.k1.get 24 (by decide), e.kc.get 24 (by decide)]; exact e.ev.s8
  have hpk := e.peek
  -- the invariant at `s0 = s7 + m`
  have hadv : ∀ (m : Nat) (R2 : Nat → BitVec 64), m ≤ rest.length →
      Keeps (8 :: 12 :: cClob) R2 R' → R2 8 = R' 23 + BitVec.ofNat 64 m →
      ∃ o', EvAt S sp W d (k - leakOne c) q M0 R0 R2 M' H' F' L' C' G' hs (ex ++ xs) st'
        ⟨rest.drop m, td, false⟩ o' := fun m R2 hm k2 h8 => by
    obtain ⟨o', -, -, -, ev'⟩ := ev_adv e.ev e.kc e.c23 e.mem e.k1 e.e2 e.post (e.hal hlc) h1 h2
      (m := m) (td' := td) (neg' := false) hm e.ev.tdLt (R2 := R2) (k2.mono (by decide)) h8
      (by rw [k2.get 24 (by decide)]; exact h24)
    exact ⟨o', ev'⟩
  cases rest with
  | nil =>
    simp only [if_true]
    refine evl_1 hlive h10 e.cs fun R1 k1 => ?_
    have e2' : R1 2 = BitVec.ofNat 64 (sp - 176) := (k1.get 2 (by decide)).trans e2
    refine rt_eat_last hlive e2' hsf hpk fun R2 k2 h8 h12 => ?_
    obtain ⟨o', ev'⟩ := hadv 0 R2 (by simp) (by keeps_tac ((k2.mono (by decide)).trans (k1.mono (by decide))))
      (by rw [h8, k1.get 23 (by decide)]; simp)
    exact ev_cont hlive (bltu_800017d0 hlive) ev' hfu' htl (e.grow hlc hgrow) (e.pin hpin) hk
      fun hne => absurd rfl hne
  | cons p rest' =>
    simp only [List.cons_ne_nil, if_false]
    have hp : p < 256 := e.ev.chars p (by simp)
    refine rt_eat_mid hlive h10 e.cs e2 hsf hpk hp fun R2 k2 h8 h12 => ?_
    obtain ⟨o', ev'⟩ := hadv 1 R2 (by simp) (k2.mono (by decide)) (by rw [h8]; exact e.eat8)
    simp only [List.drop_one, List.tail_cons] at ev' hfu'
    exact ev_cont hlive (bltu_80001718 hlive) ev' hfu' htl (e.grow hlc hgrow) (e.pin hpin) hk
      fun hne => IH t0 sp W d _ q M0 R0 R2 M' H' F' L' C' G' hs _ st' st'' _ o' r Ge hse xse ke
        hfu' hne ev' h12 hoom htl (e.grow hlc hgrow) (e.pin hpin) hk

/-- **The square root** (`v`, status `0` with the root pushed): on to
`rest`, or the exit after the last character. -/
theorem evs_sqrt (hlive : ∀ p ∈ dcText, live p.1) (IH : LoopIH live S Q n) {s : St} {x y : Num}
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' (s.push (.num y)) ex)
    (hres : dcFunc 70 st c rest.head? neg = .sqrt s x) (hsq : Sqrt x s.scale y)
    (h10 : R' 10 = BitVec.ofNat 64 0)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr (s.push (.num y)).out)
      (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  obtain ⟨y', hy', hfu', -, hlc⟩ := hfu.sqrt hres
  obtain rfl := Sqrt.fuel_eq hsq hy'
  have h1 := dcFunc_strBound (lm := 70) (c := c) (peek := rest.head?) (neg := neg) e.ev.sb (by decide)
  have h2 := dcFunc_arrSorted (lm := 70) (c := c) (peek := rest.head?) (neg := neg) e.ev.srt
  rw [hres] at h1 h2
  have hsb : StrBound (2 ^ 24) (s.push (.num y)) := h1.push (VB.num _ _)
  have hsrt : ArrSorted (s.push (.num y)) := h2.stack _
  cases rest with
  | nil => exact evs_zero_last hlive e h10 hfu' hlc hsb hsrt htl hgrow hpin hk
  | cons p rest' =>
    simp only [List.cons_ne_nil, if_false]
    exact evs_zero_mid hlive IH e h10 hfu' hlc hsb hsrt hoom htl hgrow hpin hk

end

end Dc.Mach
