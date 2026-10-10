import Dc.Mach.EvalEntry

/-!
# `evalstr`'s loop: continuation-generic case statements (M10)

The status cases after `dc_func` returned (`EvCall`), stated over their
continuations instead of the fuel and the caller's `EvK`: `EvHeadK` (the
loop head with the invariant over the next frame) and `EvEndK` (the loop's
exit `0x8000156c` with the invariant). The term direction instantiates them
with `LoopIH` and `ev_exit`; the stuck direction with its own end
conditions. `EvIntCore`/`EvStrCore`: `DC_INT` and `DC_STR` in this shape.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **The loop head with the invariant** over the next state `st'` and a
frame `f'` (nonempty) with the budget `k'`: any ghost `G2` and lost strings `xs2`
whose leaks fit the activation's (`G`, `xs`, `k` before the command), the
caller's strings pinned. -/
def EvHeadK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W d k k' q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (G : DcG)
    (hs xs : List GV) (st' : St) (f' : Frame) : Prop :=
  ∀ (R2 : Nat → BitVec 64) (M2 : Mem) (H2 : Heap) (F2 : List Blk) (L2 : List NumObj)
    (C2 : BcConsts) (G2 : DcG) (xs2 : List GV) (o' : StrObj),
    EvAt S sp W d k' q M0 R0 R2 M2 H2 F2 L2 C2 G2 hs xs2 st' f' o' → R2 12 = boolWord f'.neg →
    f'.s ≠ [] → G2.lk.length + xs2.length + 4 * k' ≤ G.lk.length + xs.length + 4 * k →
    StrPin G.strs G2.strs hs.tail →
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x800014f8#64 R2 M2

/-- **The loop's exit** (`0x8000156c`, `DC_OKAY` with the state `st'`) from
the invariant over any frame. -/
def EvExitK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (G : DcG)
    (hs xs : List GV) (st' : St) : Prop :=
  ∀ k' (R2 : Nat → BitVec 64) (M2 : Mem) (H2 : Heap) (F2 : List Blk) (L2 : List NumObj)
    (C2 : BcConsts) (G2 : DcG) (xs2 : List GV) (f'' : Frame) (o' : StrObj),
    EvAt S sp W d k' q M0 R0 R2 M2 H2 F2 L2 C2 G2 hs xs2 st' f'' o' →
    G2.lk.length + xs2.length + 4 * k' ≤ G.lk.length + xs.length + 4 * k →
    StrPin G.strs G2.strs hs.tail →
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x8000156c#64 R2 M2

/-- **The loop's exit when the next frame `f'` is empty** (`EvExitK`). -/
def EvEndK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (G : DcG)
    (hs xs : List GV) (st' : St) (f' : Frame) : Prop :=
  f'.s = [] → EvExitK live S Q t0 sp W d k q M0 R0 G hs xs st'

/-- **The `DC_EVALTOS` code** (`0x80001748`) with the invariant over the
state `st'` and the frame `⟨rest, td, false⟩`, `s9 = sp + 32`. -/
def EvTosK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W d k k' q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (G : DcG)
    (hs xs : List GV) (st' : St) (rest : List Nat) (td : Nat) : Prop :=
  ∀ (R2 : Nat → BitVec 64) (M2 : Mem) (H2 : Heap) (F2 : List Blk) (L2 : List NumObj)
    (C2 : BcConsts) (G2 : DcG) (xs2 : List GV) (o' : StrObj),
    EvAt S sp W d k' q M0 R0 R2 M2 H2 F2 L2 C2 G2 hs xs2 st' ⟨rest, td, false⟩ o' →
    R2 25 = BitVec.ofNat 64 (sp - 176 + 32) →
    G2.lk.length + xs2.length + 4 * k' ≤ G.lk.length + xs.length + 4 * k →
    StrPin G.strs G2.strs hs.tail →
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80001748#64 R2 M2

/-- **`DC_QUIT` leaving the activation** (`0x800016b8`, `unwind_depth ≥
tail_depth = td`) with the invariant over the state `st'`. -/
def EvQuitK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (G : DcG)
    (hs xs : List GV) (st' : St) (td : Nat) : Prop :=
  ∀ k' (R2 : Nat → BitVec 64) (M2 : Mem) (H2 : Heap) (F2 : List Blk) (L2 : List NumObj)
    (C2 : BcConsts) (G2 : DcG) (xs2 : List GV) (f'' : Frame) (o' : StrObj),
    EvAt S sp W d k' q M0 R0 R2 M2 H2 F2 L2 C2 G2 hs xs2 st' f'' o' → f''.td = td →
    G2.lk.length + xs2.length + 4 * k' ≤ G.lk.length + xs.length + 4 * k →
    StrPin G.strs G2.strs hs.tail →
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x800016b8#64 R2 M2

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k k' q : Nat} {M0 : Mem} {R0 : Nat → BitVec 64} {G : DcG}
  {hs xs : List GV} {st' st'' : St} {r : Status} {n : Nat}
  {Ge : DcG} {hse xse : List GV} {ke : Nat}

/-- The loop head from the loop at fuel `n`. -/
theorem EvHeadK.ofIH (IH : LoopIH live S Q n) {f' : Frame}
    (hfu : EvFuel 70 n d k' st' f' st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    EvHeadK live S Q t0 sp W d k k' q M0 R0 G hs xs st' f' :=
  fun R2 M2 H2 F2 L2 C2 G2 xs2 o' ev h12 hne hg hp =>
    IH t0 sp W d k' q M0 R0 R2 M2 H2 F2 L2 C2 G2 hs xs2 st' st'' f' o' r Ge hse xse ke hfu hne ev h12
      hoom htl (by omega) (hpin.trans hp) hk

/-- The exit with the caller's continuation for `DC_OKAY`. -/
theorem EvExitK.ofK (hlive : ∀ p ∈ dcText, live p.1) (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st' .ok) :
    EvExitK live S Q t0 sp W d k q M0 R0 G hs xs st' :=
  fun _ _ _ _ _ _ _ _ _ _ _ ev hg hp => ev_exit hlive ev htl (by omega) (hpin.trans hp) hk

/-- The exit for an empty next frame, from its evaluation. -/
theorem EvEndK.ofFuel (hlive : ∀ p ∈ dcText, live p.1) {f' : Frame}
    (hfu : EvFuel 70 n d k' st' f' st'' r) (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st' f' := fun he => by
  obtain ⟨s, td, neg⟩ := f'
  simp only at he
  subst he
  obtain ⟨rfl, rfl⟩ := hfu.nil
  exact EvExitK.ofK hlive htl hgrow hpin hk

/-- The `DC_EVALTOS` code from its hypothesis at fuel `n`. -/
theorem EvTosK.ofIH (TIH : TosIH live S Q n) {rest : List Nat} {td : Nat}
    (hfu : TosFuel 70 n d k' st' rest td st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    EvTosK live S Q t0 sp W d k k' q M0 R0 G hs xs st' rest td :=
  fun R2 M2 H2 F2 L2 C2 G2 xs2 o' ev h25 hg hp =>
    TIH t0 sp W d k' q M0 R0 R2 M2 H2 F2 L2 C2 G2 hs xs2 st' st'' rest td o' r Ge hse xse ke hfu ev
      h25 hoom htl (by omega) (hpin.trans hp) hk

/-- `DC_QUIT` leaving with the caller's continuation. -/
theorem EvQuitK.ofK (hlive : ∀ p ∈ dcText, live p.1) {td : Nat} (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail)
    (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse { st' with unwind := st'.unwind - td } .quit)
    (hle : td ≤ st'.unwind) :
    EvQuitK live S Q t0 sp W d k q M0 R0 G hs xs st' td :=
  fun _ _ _ _ _ _ _ _ _ f'' _ ev hf hg hp => by
    subst hf
    exact ev_quit_out hlive ev hle htl (by omega) (hpin.trans hp) hk

/-- **The loop test** at a `bltu` site, closed by the continuations. -/
theorem ev_cont_k {p : Nat} (hb : BltuAt live S Q p) {R : Nat → BitVec 64} {M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G2 : DcG} {xs2 : List GV} {f' : Frame}
    {o : StrObj} (ev : EvAt S sp W d k' q M0 R0 R M H F L C G2 hs xs2 st' f' o)
    (h12 : R 12 = boolWord f'.neg)
    (hg : G2.lk.length + xs2.length + 4 * k' ≤ G.lk.length + xs.length + 4 * k)
    (hp : StrPin G.strs G2.strs hs.tail)
    (hhead : EvHeadK live S Q t0 sp W d k k' q M0 R0 G hs xs st' f')
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st' f') :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (BitVec.ofNat 64 p) R M :=
  ev_join hb ev (fun hne => hhead R M H F L C G2 xs2 o ev h12 hne hg hp)
    (fun he => hend he k' R M H F L C G2 xs2 f' o ev hg hp)

end

/-- **`DC_INT`** (status `5`): the number read pushed, on to the rest after it. -/
def EvIntCore (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St) (c : Nat)
    (rest : List Nat) (td : Nat) (neg : Bool) (o : StrObj) (Rc R' : Nat → BitVec 64) (Mc M' : Mem)
    (H' : Heap) (F' : List Blk) (L' : List NumObj) (C' : BcConsts) (G' : DcG) (ex : List GV),
    EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C' G'
      st ex →
    dcFunc 70 st c rest.head? neg = .int → R' 10 = BitVec.ofNat 64 5 → leakOne c ≤ k →
    EvOom live S Q sp W q M0 →
    EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs
      (st.push (.num (readNum st.ibase (c :: rest)).1)) ⟨(readNum st.ibase (c :: rest)).2, td, false⟩ →
    EvEndK live S Q t0 sp W d k q M0 R0 G hs xs (st.push (.num (readNum st.ibase (c :: rest)).1))
      ⟨(readNum st.ibase (c :: rest)).2, td, false⟩ →
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M'

/-- **`DC_STR`** (status `6`): the bracketed string pushed, on to the rest
after it. -/
def EvStrCore (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St) (c : Nat)
    (rest : List Nat) (td : Nat) (neg : Bool) (o : StrObj) (Rc R' : Nat → BitVec 64) (Mc M' : Mem)
    (H' : Heap) (F' : List Blk) (L' : List NumObj) (C' : BcConsts) (G' : DcG) (ex : List GV),
    EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C' G'
      st ex →
    dcFunc 70 st c rest.head? neg = .str → R' 10 = BitVec.ofNat 64 6 → leakOne c ≤ k →
    EvOom live S Q sp W q M0 →
    EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs
      (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩ →
    EvEndK live S Q t0 sp W d k q M0 R0 G hs xs (st.push (.str (scanStr 1 rest).1))
      ⟨(scanStr 1 rest).2, td, false⟩ →
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M'

/-- **`evalstr`'s entry** (`0x80001448`), continuation-generic: the loop
head with the invariant over the first frame `⟨o.s, 1, false⟩`, or for an
empty text the return `DC_OKAY` with the state unchanged. -/
def EvEntryCore (live S : Nat → Prop)
    (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) : Prop :=
  ∀ (t0 : String) (sp W d k q : Nat) (M : Mem) (R : Nat → BitVec 64) (H : Heap) (F : List Blk)
    (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St) (o : StrObj),
    EvEntry S sp W d k q M R H F L C G hs xs st o →
    (o.s ≠ [] → EvHeadK live S Q t0 sp W d k k q M R G hs xs st ⟨o.s, 1, false⟩) →
    (o.s = [] → EvK live S Q t0 sp W k q M R G hs xs st .ok) →
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001448#64 R M

/-- `EvEntrySpec` at fuel `n` from the generic entry and the loop at `n`. -/
theorem ev_entry_of_core {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hc : EvEntryCore live S Q) {n : Nat}
    (IH : LoopIH live S Q n) : EvEntrySpec live S Q n := by
  intro t0 sp W d k q M R H F L C G hs xs st st' o r hfu en hoom hk
  refine hc t0 sp W d k q M R H F L C G hs xs st o en
    (fun _ => EvHeadK.ofIH IH hfu hoom rfl (Nat.le_refl _) (StrPin.refl _ _) hk) fun he => ?_
  have e : (⟨o.s, 1, false⟩ : Frame) = ⟨[], 1, false⟩ := by rw [he]
  rw [e] at hfu
  obtain ⟨rfl, rfl⟩ := hfu.nil
  exact hk

end Dc.Mach
