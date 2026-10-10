import Dc.Mach.EvalCases3
import Dc.Mach.DcSystem

/-!
# `evalstr`'s loop: `DC_SYSTEM` (M10)

`DC_SYSTEM` (`0x800015cc`): `s0 = dc_system (s7)` (`dc_system_spec`, the
state unchanged, the result past the command line, `skipSys`), then the
test at `0x800015dc`. `FnPost.stk`: `dc_func`'s post extended by a callee
that writes only its own stack frame. `EvAt.oomK`: the loop's
out-of-memory continuation from any state agreeing with the invariant's
memory outside the frames below `evalstr`'s.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `skipSys` drops a prefix. -/
theorem skipSys_drop : ∀ (s : List Nat), skipSys s = s.drop (s.length - (skipSys s).length)
  | [] => rfl
  | c :: cs => by
    have hle := skipSys_length_le cs
    unfold skipSys
    split
    · simp
    · split
      · simp
      · rw [List.length_cons, show cs.length + 1 - (skipSys cs).length =
          (cs.length - (skipSys cs).length) + 1 by omega, List.drop_succ_cons, ← skipSys_drop cs]

/-- **`dc_func`'s post, then a callee writing only its frame** (`n` bytes
below `sp`) with the state unchanged. -/
theorem FnPost.stk {S : Nat → Prop} {al sp W : Nat} {M : Mem} {G : DcG} {hs : List GV} {M' : Mem}
    {H' : Heap} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG} {st' : St}
    {ex : List GV} (hp : FnPost S al sp W M G hs M' H' F' L' C' G' st' ex) {M'' : Mem} {H'' : Heap}
    (hdc : DcAt S M'' H'' F' L' C' G' (ex ++ hs) st') {n : Nat} (hso : StkOut sp n M'' M')
    (hW : n ≤ W) :
    FnPost S al sp W M G hs M'' H'' F' L' C' G' st' ex where
  dc := hdc
  lk := hp.lk
  ex := hp.ex
  pin := hp.pin
  out a e1 e2 e3 e4 := by
    rw [hso a e1 e2 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))]
    exact hp.out a e1 e2 e3 e4

/-- **The loop's out-of-memory continuation** from a state whose memory
agrees with the invariant's outside the frames below `evalstr`'s. -/
theorem EvAt.oomK {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV} {st : St} {f : Frame} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o) (hoom : EvOom live S Q sp W q M0)
    {t' : String} {sp' : Nat} {R' : Nat → BitVec 64} {M' : Mem} (hlo : sp - W ≤ sp')
    (hhi : sp' ≤ sp - 176) (h2 : R' 2 = BitVec.ofNat 64 sp') (hal : sp' % 16 = 0)
    (hout : ∀ a, OutHeap a → ¬ (DcGlob a ∧ ¬ PinWords a) → ¬ frameIn (sp - 176) (W - 176) a →
      ¬ (sp - 176 ≤ a ∧ a < sp - 176 + 88) → ¬ InP a → imgM M' a = imgM M a) :
    DWO live S Q t' 0x80001e74#64 R' M' := by
  have hW : 176 ≤ W := by have := ev.stk; omega
  have hab := ev.room; simp only [heapEnd] at hab
  exact hoom t' R' M' sp' ⟨by omega, by omega, h2, fun a e1 e2 e3 e4 => by
    rw [hout a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))
      (fun hw => e3 (by simp only [frameIn]; omega)) (fun h => e4 (.inr (.inr h)))]
    exact ev.out a e1 e2 (fun h => e4 (.inl h)) (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))
      (fun hf => e3 (by simp only [frameIn]; omega)) (fun h => e4 (.inr (.inl h)))
      (fun h => e4 (.inr (.inr h))), hal⟩

/-- **`DC_SYSTEM`'s span** (`0x800015cc`, `s7` at the text after `!`):
`dc_system (s7)`, `s0` its result, `a2 = 0`, to the test at `0x800015dc`. -/
theorem rt_system {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t : String} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {sp a : Nat}
    {s : List Nat} (h : DcAt S M H F L C G hs st) (hsrc : SysSrc S M G sp a s)
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp) {R : Nat → BitVec 64}
    (h2 : R 2 = BitVec.ofNat 64 sp) (h23 : R 23 = BitVec.ofNat 64 a)
    (hk : ∀ R2 M2 H2, Keeps (8 :: 12 :: cClob) R2 R →
      R2 8 = BitVec.ofNat 64 (a + (s.length - (skipSys s).length)) → R2 12 = 0#64 →
      DcAt S M2 H2 F L C G hs st → StkOut sp 48 M2 M → DWO live S Q t 0x800015dc#64 R2 M2)
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 48) → StkOut sp 48 M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x800015cc#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h23] at 0x80001f60
  refine dc_system_spec hlive h hsrc hsf hab _ (by bsimp [h2]) (by bsimp [h23]) (by bsimp [])
    (fun R' M' H' k' e2 e10 hdc hso => ?_) hoom
  bsimp []
  bc_run hlive hlive [e10] at 0x800015dc
  exact hk _ M' H' (by keeps_tac ((k'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (by bsimp [e10]) (by bsimp []) hdc hso

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st'' : St} {ex : List GV} {r : Status} {n : Nat}
  {Ge : DcG} {hse xse : List GV} {ke : Nat}

/-- **`DC_SYSTEM`** from `0x800015cc` (either dispatch table). -/
theorem evs_system_at (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex) (hlc : leakOne c ≤ k) (hoom : EvOom live S Q sp W q M0)
    (hhead : EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs st
      ⟨skipSys rest, td, false⟩)
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st ⟨skipSys rest, td, false⟩)
    {R1 : Nat → BitVec 64} (k1 : Keeps [10, 15] R1 R') :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800015cc#64 R1 M' := by
  obtain ⟨o0, -, -, -, ev0⟩ := e.same (e.hal hlc) e.ev.sb e.ev.srt (R2 := R1) (k1.mono (by decide))
  obtain ⟨a, er⟩ := ev0.rest
  have hstk := e.ev.stk; have hab := e.ev.room
  have h23 : R' 23 = BitVec.ofNat 64 a := by
    rw [e.k1.get 23 (by decide), e.c23, ← er.r8, k1.get 8 (by decide), e.k1.get 8 (by decide),
      e.kc.get 8 (by decide)]
  have hsrc : SysSrc S M' G' (sp - 176) a rest :=
    ⟨er.own, fun j hj => .inl (er.inb j hj), er.val, er.nul, er.byte, by have := er.len; omega⟩
  refine rt_system hlive ev0.dc hsrc (ev0.frame.within (m := 176) (n := 48) (by omega) (by decide))
    (by simp only [heapEnd] at hab ⊢; omega) ev0.r2 (by rw [k1.get 23 (by decide)]; exact h23)
    (fun R2 M2 H2 k2 h8 h12 hdc hso => ?_)
    (fun R2 M2 e2 hso => ev0.oomK hoom (sp' := sp - 176 - 48) (by omega) (by omega) e2
      (by have := ev0.frame.al; omega)
      fun a e1 e2 e3 _ _ => hso a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)))
  have hle := skipSys_length_le rest
  have hp' := e.post.stk (by rw [← List.append_assoc]; exact hdc) hso (by omega)
  obtain ⟨o', -, -, -, ev'⟩ := ev_adv e.ev e.kc e.c23 e.mem e.k1 e.e2 hp' (e.hal hlc) e.ev.sb
    e.ev.srt (m := rest.length - (skipSys rest).length) (td' := td) (neg' := false) (by omega)
    e.ev.tdLt (R2 := R2) ((k2.mono (by decide)).trans (k1.mono (by decide)))
    (by rw [h8, h23, BitVec.ofNat_add_ofNat])
    (by rw [k2.get 24 (by decide), k1.get 24 (by decide), e.k1.get 24 (by decide),
      e.kc.get 24 (by decide)]; exact e.ev.s8)
  rw [← skipSys_drop rest] at ev'
  exact ev_cont_k (bltu_800015dc hlive) ev' h12 (e.grow0 hlc) e.pin0 hhead hend

/-- **`DC_SYSTEM`**: the status dispatch then `evs_system_at`. -/
theorem evs_system_k (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex) (h10 : R' 10 = BitVec.ofNat 64 7) (hlc : leakOne c ≤ k)
    (hoom : EvOom live S Q sp W q M0)
    (hhead : EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs st
      ⟨skipSys rest, td, false⟩)
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st ⟨skipSys rest, td, false⟩) :
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  split
  · exact evl_7 hlive h10 e.cs fun R1 k1 => evs_system_at hlive e hlc hoom hhead hend k1
  · exact evm_7 hlive h10 e.cs fun R1 k1 => evs_system_at hlive e hlc hoom hhead hend k1

/-- **`DC_SYSTEM`** (term direction). -/
theorem evs_system (hlive : ∀ p ∈ dcText, live p.1) (IH : LoopIH live S Q n)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex)
    (hres : dcFunc 70 st c rest.head? neg = .system) (h10 : R' 10 = BitVec.ofNat 64 7)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  obtain ⟨hfu', -, hlc⟩ := hfu.system hres
  exact evs_system_k hlive e h10 hlc hoom (EvHeadK.ofIH IH hfu' hoom htl hgrow hpin hk)
    (EvEndK.ofFuel hlive hfu' htl hgrow hpin hk)

end

end Dc.Mach
