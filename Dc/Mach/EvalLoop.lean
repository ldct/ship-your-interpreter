import Dc.Mach.EvalComment

/-!
# `evalstr`'s loop: the induction (M10)

`LoopIH n`/`TosIH n`: `EvLoopSpec`/`EvTosSpec` at fuel `n`. `EvCall`: the
data after `dc_func` returned to `evalstr` (the invariant before the call,
the call's registers and memory, `dc_func`'s post). The status cases
`evs_*` each prove the run from `dc_func`'s return from the inductive
hypotheses at the smaller fuel; `ev_loop` assembles them by strong
induction on the fuel.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A command's allowance is at most four per leaking command. -/
theorem leakAllow_le (c : Nat) : leakAllow c ≤ 4 * leakOne c := by
  unfold leakOne leakCmd leakAllow
  split
  · simp
  · split <;> simp

/-- `EvLoopSpec` at fuel `n`. -/
def LoopIH (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (n : Nat) : Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st st' : St)
    (f : Frame) (o : StrObj) (r : Status) (Ge : DcG) (hse xse : List GV) (ke : Nat),
    EvFuel 70 n d k st f st' r → f.s ≠ [] →
    EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o → R 12 = boolWord f.neg →
    EvOom live S Q sp W q M0 →
    hs.tail = hse.tail → G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke →
    StrPin Ge.strs G.strs hs.tail →
    EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st' r →
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800014f8#64 R M

/-- `EvTosSpec` at fuel `n`. -/
def TosIH (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (n : Nat) : Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st st' : St)
    (rest : List Nat) (td : Nat) (o : StrObj) (r : Status) (Ge : DcG) (hse xse : List GV) (ke : Nat),
    TosFuel 70 n d k st rest td st' r →
    EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o →
    R 25 = BitVec.ofNat 64 (sp - 176 + 32) →
    EvOom live S Q sp W q M0 →
    hs.tail = hse.tail → G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke →
    StrPin Ge.strs G.strs hs.tail →
    EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st' r →
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001748#64 R M

/-- **After `dc_func` returned** to `evalstr`: the invariant before the call
(frame `c :: rest`), the call's registers `Rc` and memory `Mc`, the return's
registers `R'` and `dc_func`'s post. -/
structure EvCall (S : Nat → Prop) (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem)
    (H : Heap) (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV)
    (st : St) (c : Nat) (rest : List Nat) (td : Nat) (neg : Bool) (o : StrObj)
    (Rc R' : Nat → BitVec 64) (Mc M' : Mem) (H' : Heap) (F' : List Blk) (L' : List NumObj)
    (C' : BcConsts) (G' : DcG) (st' : St) (ex : List GV) : Prop where
  ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨c :: rest, td, neg⟩ o
  kc : Keeps [1, 10, 11, 15, 23] Rc R
  c23 : Rc 23 = R 8 + 1#64
  mem : EvCallMem sp M Mc (peekWord rest.head?)
  k1 : Keeps cClob R' Rc
  e2 : R' 2 = Rc 2
  post : FnPost S (leakAllow c) (sp - 176) (W - 176) Mc G (xs ++ hs) M' H' F' L' C' G' st' ex

namespace EvCall

variable {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st' : St} {ex : List GV}

/-- The loop constants survive the call. -/
theorem cs (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F'
    L' C' G' st' ex) : EvConsts R' :=
  ⟨by rw [e.k1.get 18 (by decide), e.kc.get 18 (by decide)]; exact e.ev.cs.s2,
   by rw [e.k1.get 19 (by decide), e.kc.get 19 (by decide)]; exact e.ev.cs.s3,
   by rw [e.k1.get 20 (by decide), e.kc.get 20 (by decide)]; exact e.ev.cs.s4,
   by rw [e.k1.get 21 (by decide), e.kc.get 21 (by decide)]; exact e.ev.cs.s5⟩

/-- **The continuation's bookkeeping**: the lost references, strings and
budget, and the pinned strings, after the call. -/
theorem grow (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F'
    L' C' G' st' ex) {Ge : DcG} {xse : List GV} {ke : Nat} (hlc : leakOne c ≤ k)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke) :
    G'.lk.length + (ex ++ xs).length + 4 * (k - leakOne c) ≤ Ge.lk.length + xse.length + 4 * ke := by
  have := e.post.lk; have := leakAllow_le c
  simp only [List.length_append]; omega

theorem pin (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F'
    L' C' G' st' ex) {Ge : DcG} (hpin : StrPin Ge.strs G.strs hs.tail) :
    StrPin Ge.strs G'.strs hs.tail :=
  hpin.trans (e.post.pin.mono fun g hg => List.mem_append_right _ (List.mem_of_mem_tail hg))

theorem hal (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F'
    L' C' G' st' ex) (hlc : leakOne c ≤ k) : leakAllow c + 4 * (k - leakOne c) ≤ 4 * k := by
  have := leakAllow_le c; omega

end EvCall

/-- The state after a command keeps the invariant's model facts. -/
theorem res_ok_facts {st s : St} {c : Nat} {peek : Option Nat} {neg : Bool}
    (hsb : StrBound (2 ^ 24) st) (hsrt : ArrSorted st) (hres : dcFunc 70 st c peek neg = .ok s) :
    StrBound (2 ^ 24) s ∧ ArrSorted s := by
  have h1 := dcFunc_strBound (lm := 70) (c := c) (peek := peek) (neg := neg) hsb (by decide)
  have h2 := dcFunc_arrSorted (lm := 70) (c := c) (peek := peek) (neg := neg) hsrt
  rw [hres] at h1 h2
  exact ⟨h1, h2⟩

end Dc.Mach
