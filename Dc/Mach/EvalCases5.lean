import Dc.Mach.EvalCases4

/-!
# `evalstr`'s loop: `DC_EOF_ERROR` (M10)

`DC_EOF_ERROR` (`0x80001540`): `ferror (stdin)` (`0`), then
`fprintf (stderr, "%s: unexpected EOS\n", progname)` and the loop's exit
with the state unchanged (`DC_OKAY`). `EvCall.frame`: the call's data after
a callee that writes only its stack frame.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `"%s: unexpected EOS\n"`. -/
theorem eosMsg : ProgMsg 0x80007b80 17 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

/-- **`DC_EOF_ERROR`'s span** (`0x80001540`, frame `sp`): the message to
`stderr`, then the exit `0x8000156c`; only the 304 bytes below `sp` change. -/
theorem rt_eof {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t : String} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {sp : Nat}
    (h : DcAt S M H F L C G hs st) (hsf : StackFrame S sp 304) (hab : heapEnd + 304 ≤ sp)
    {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp)
    (hk : ∀ R' M', Keeps cClob R' R → (∀ a, (a < sp - 304 ∨ sp ≤ a) → imgM M' a = imgM M a) →
      DWO live S Q t 0x8000156c#64 R' M') :
    DWO live S Q t 0x80001540#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hpn := h.view.prog
  have hfd := h.errFile
  have hG := h.glob
  have hro : ∀ b ∈ accAddrs 2147516944 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  have hro2 : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hS [h2, stdin_word] at 0x8000071c
  refine ferror_spec hlive _ (by bsimp []) fun R1 k1 e1 => ?_
  bsimp []
  bc_run hlive hS [h2, hpn, stderr_word, e1, (k1.get 2 (by decide))] at 0x80000774
  all_goals first | (intro hc; exact absurd e1 hc) | intro _ | skip
  bc_run hlive hS [h2, hpn, stderr_word, e1, (k1.get 2 (by decide))] at 0x80000774
  refine fprintf_prog_spec hlive eosMsg (by decide) hsf (by simp only [stderrAddr]; omega) hfd _
    ?_ ?_ ?_ ?_ ?_ fun R' M' hk2 hfr => ?_
  · have e2 : R1 2 = BitVec.ofNat 64 sp := (k1.get 2 (by decide)).trans (by bsimp [h2])
    bsimp [e2]
  all_goals first
    | (bsimp []; done)
    | (bsimp []; decide)
    | skip
  bsimp []
  exact hk R' M' (by keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac
    ((k1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))) hfr

namespace EvCall

variable {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st' : St} {ex : List GV}

/-- **The call's data after a callee writing only its frame** (`n` bytes
below `evalstr`'s, the state unchanged). -/
theorem frame (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H'
    F' L' C' G' st' ex) {M'' : Mem} {H'' : Heap}
    (hdc : DcAt S M'' H'' F' L' C' G' (ex ++ xs ++ hs) st') {n : Nat}
    (hso : StkOut (sp - 176) n M'' M') (hn : n ≤ W - 176) :
    EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M'' H'' F' L' C' G'
      st' ex :=
  { e with post := e.post.stk (by rw [← List.append_assoc]; exact hdc) hso hn }

end EvCall

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st'' : St} {ex : List GV} {r : Status} {n : Nat}
  {Ge : DcG} {hse xse : List GV} {ke : Nat}

/-- **`DC_EOF_ERROR`** from `0x80001540` (either dispatch table). -/
theorem evs_eof_at (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex)
    (hlc : leakOne c ≤ k) (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st .ok)
    {R1 : Nat → BitVec 64} (k1 : Keeps [10, 15] R1 R') :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001540#64 R1 M' := by
  obtain ⟨o0, -, -, -, ev0⟩ := e.same (e.hal hlc) e.ev.sb e.ev.srt (R2 := R1) (k1.mono (by decide))
  have hstk := e.ev.stk; have hab := e.ev.room
  refine rt_eof hlive ev0.dc (ev0.frame.within (m := 176) (n := 304) (by omega) (by decide))
    (by simp only [heapEnd] at hab ⊢; omega) ev0.r2 fun R2 M2 k2 hfr => ?_
  have hP : ∀ a, (sp - 176 - 304 ≤ a ∧ a < sp - 176) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    have := above_sp (sp := sp - 176 - 304) (a := a)
      (by simp only [heapEnd] at hab ⊢; omega) (by omega)
    ⟨this.1, this.2.1⟩
  have hdc := ev0.dc.outWrite (M' := M2) (fun a ha => hfr a (by omega)) hP
  have e' := e.frame hdc (n := 304) (fun a _ _ hf => hfr a (by simp only [frameIn] at hf; omega))
    (by omega)
  obtain ⟨o2, -, -, -, ev2⟩ := e'.same (e.hal hlc) e.ev.sb e.ev.srt (R2 := R2)
    ((k2.mono (by decide)).trans (k1.mono (by decide)))
  exact ev_exit hlive ev2 htl (e.grow hlc hgrow) (e.pin hpin) hk

/-- **`DC_EOF_ERROR`**: the status dispatch then `evs_eof_at`; the
evaluation ends with the state unchanged. -/
theorem evs_eof (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex)
    (hres : dcFunc 70 st c rest.head? neg = .eofError) (h10 : R' 10 = BitVec.ofNat 64 10)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  obtain ⟨rfl, rfl, -, hlc⟩ := hfu.eofError hres
  split
  · exact evl_10 hlive h10 e.cs fun R1 k1 => evs_eof_at hlive e hlc htl hgrow hpin hk k1
  · exact evm_10 hlive h10 e.cs fun R1 k1 => evs_eof_at hlive e hlc htl hgrow hpin hk k1

end

end Dc.Mach
