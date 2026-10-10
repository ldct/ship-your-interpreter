import Dc.Mach.EvalTosStep
import Dc.Mach.EvalIntB

/-!
# `evalstr`: the loop and the theorem (M10)

`ev_dispatch`: after `dc_func` returned (`EvCall`) with the outcome
`FnOut`, the status case for the result; `loop_step`: `LoopIH` at fuel
`n + 1`; `ev_loop`: `LoopIH n ∧ TosIH n` for every `n` by induction;
`evalstr_spec`: `EvalstrSpec` from the entry (`ev_entry_k`) at the
evaluation's fuel.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem EvFuel.callOK {lm n d k : Nat} {st st'' : St} {c : Nat} {rest : List Nat} {td : Nat}
    {neg : Bool} {r : Status} (h : EvFuel lm (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) :
    CallOK st := by
  have hsz := h.size; unfold AllCalls at hsz; exact hsz.1

/-- `dc_func`'s contract from `dc_func_spec`. -/
theorem fnSpecH_of {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) : FnSpecH live S Q :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hr ho hk => dc_func_spec hlive hp hr ho hk

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st' st'' : St} {ex : List GV} {r : Status} {n : Nat}
  {Ge : DcG} {hse xse : List GV} {ke : Nat}

/-- **The status cases** after `dc_func` returned with outcome `code`/`st'`. -/
theorem ev_dispatch (hlive : ∀ p ∈ dcText, live p.1)
    (IH : LoopIH live S Q n) (TIH : TosIH live S Q n)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex) {code : Nat} (hfo : FnOut st (dcFunc 70 st c rest.head? neg) code st')
    (h10 : R' 10 = BitVec.ofNat 64 code)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (if rest = [] then 0x80001728#64 else 0x80001528#64)
      R' M' := by
  generalize hres : dcFunc 70 st c rest.head? neg = res at hfo
  cases hfo with
  | ok s => exact evs_ok hlive IH e hres h10 hfu hoom htl hgrow hpin hk
  | eatOne s => exact evs_eat hlive IH e hres h10 hfu hoom htl hgrow hpin hk
  | evalReg s reg => exact evs_reg hlive IH TIH e hres h10 hfu hoom htl hgrow hpin hk
  | evalTos s => exact evs_tos hlive TIH e hres h10 hfu hoom htl hgrow hpin hk
  | quit s => exact evs_quit hlive IH e hres h10 hfu hoom htl hgrow hpin hk
  | int =>
    obtain ⟨hfu', -, hlc⟩ := hfu.int hres
    exact evs_int_k hlive t0 sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H'
      F' L' C' G' ex e hres h10 hlc hoom (EvHeadK.ofIH IH hfu' hoom htl hgrow hpin hk)
      (EvEndK.ofFuel hlive hfu' htl hgrow hpin hk)
  | str =>
    obtain ⟨hfu', -, hlc⟩ := hfu.str hres
    exact evs_str_k hlive t0 sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H'
      F' L' C' G' ex e hres h10 hlc hoom (EvHeadK.ofIH IH hfu' hoom htl hgrow hpin hk)
      (EvEndK.ofFuel hlive hfu' htl hgrow hpin hk)
  | system => exact evs_system hlive IH e hres h10 hfu hoom htl hgrow hpin hk
  | comment => exact evs_comment hlive IH e hres h10 hfu hoom htl hgrow hpin hk
  | negcmp => exact evs_neg hlive IH e hres h10 hfu hoom htl hgrow hpin hk
  | eofError => exact evs_eof hlive e hres h10 hfu htl hgrow hpin hk
  | sqrt hsq => exact evs_sqrt hlive IH e hres hsq h10 hfu hoom htl hgrow hpin hk

end

/-- **One more unit of fuel for the loop**. -/
theorem loop_step {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {n : Nat}
    (IH : LoopIH live S Q n) (TIH : TosIH live S Q n) : LoopIH live S Q (n + 1) := by
  intro t0 sp W d k q M0 R0 R M H F L C G hs xs st st'' f o r Ge hse xse ke hfu hne ev h12 hoom htl
    hgrow hpin hk
  obtain ⟨s, td, neg⟩ := f
  cases s with
  | nil => exact absurd rfl hne
  | cons c rest =>
    have hcall := hfu.callOK
    by_cases hr : rest = []
    · subst hr
      refine ev_call_last hlive (fnSpecH_of hlive) ev h12 hcall hoom fun Rc Mc kc c23 mem => ?_
      intro R' M' H' F' L' C' G' code st' ex k1 e2 e10 hfo hp
      have := ev_dispatch hlive IH TIH ⟨ev, kc, c23, mem, k1, e2, hp⟩ hfo e10 hfu hoom htl hgrow
        hpin hk
      simpa using this
    · refine ev_call_mid hlive (fnSpecH_of hlive) ev h12 hr hcall hoom fun Rc Mc kc c23 mem => ?_
      intro R' M' H' F' L' C' G' code st' ex k1 e2 e10 hfo hp
      have := ev_dispatch hlive IH TIH ⟨ev, kc, c23, mem, k1, e2, hp⟩ hfo e10 hfu hoom htl hgrow
        hpin hk
      simpa [hr] using this

/-- **The loop and the `DC_EVALTOS` code at every fuel**. -/
theorem ev_loop {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) : ∀ n, LoopIH live S Q n ∧ TosIH live S Q n := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfu => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfu => ?_⟩
    · obtain ⟨m, hm⟩ := hfu.pos; cases hm
    · obtain ⟨m, hm⟩ := hfu.pos; cases hm
  | succ n ih => exact ⟨loop_step hlive ih.1 ih.2, tos_step hlive ih.1⟩

/-- **`evalstr`**, term direction. -/
theorem evalstr_spec {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) : EvalstrSpec live S Q := by
  intro t0 sp W d k q M R H F L C G hs xs st st' o r hl hb hsb hsrt hdc ho hh hd hq h2 h10 hal hsf hab
    hstk hpr hdn hbud hmb herr hgl hoom hk
  obtain ⟨n, hfu⟩ := hb.fuel hl
  exact ev_entry_of_core (ev_entry_k hlive) (ev_loop hlive n).1 t0 sp W d k q M R H F L C G hs xs
    st st' o r hfu ⟨hb.frameLen, hsb, hsrt, hdc, ho, hh, hd, hq, h2, h10, hal, hsf, hab, hstk, hpr, hdn,
      hbud, hmb, herr, hgl⟩ hoom hk

end Dc.Mach

namespace Dc.Mach

/-- `evalstr` at every fuel (the stuck direction's premise). -/
theorem evEntrySpec_all {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (n : Nat) : EvEntrySpec live S Q n :=
  ev_entry_of_core (ev_entry_k hlive) (ev_loop hlive n).1

end Dc.Mach
