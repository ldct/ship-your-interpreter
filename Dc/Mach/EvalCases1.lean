import Dc.Mach.EvalPieces

/-!
# `evalstr`'s loop: status cases without callees (M10)

`DC_OKAY` (and the square root's status `0`), `DC_NEGCMP`, `DC_EVALTOS`,
`DC_QUIT`, each as a continuation-generic core `evs_*_k` (`EvHeadK`,
`EvEndK`, `EvTosK`, `EvQuitK`) and its term-direction instance at fuel
`n + 1`. `EvCall.same`: the invariant after the call with `s0` where it was
(the command's own position), for the routes that return.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace EvCall

variable {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st' : St} {ex : List GV}

/-- **The invariant after the call, `s0` unchanged** (registers `R2`, all
else as after the call). -/
theorem same (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F'
    L' C' G' st' ex) {k' : Nat} (hal : leakAllow c + 4 * k' ≤ 4 * k) (hsb : StrBound (2 ^ 24) st')
    (hsrt : ArrSorted st') {R2 : Nat → BitVec 64} (k2 : Keeps cClob R2 R') :
    ∃ o', o'.hb = o.hb ∧ o'.tb = o.tb ∧ o'.s = o.s ∧
      EvAt S sp W d k' q M0 R0 R2 M' H' F' L' C' G' hs (ex ++ xs) st' ⟨c :: rest, td, neg⟩ o' := by
  obtain ⟨i, hi, hdrop, h8⟩ := e.ev.pos
  exact e.ev.next e.mem.only e.post hal (j := i) hi hdrop
    (by rw [k2.get 8 (by decide), e.k1.get 8 (by decide), e.kc.get 8 (by decide)]; exact h8)
    (by rw [k2.get 9 (by decide), e.k1.get 9 (by decide), e.kc.get 9 (by decide)])
    (by rw [k2.get 22 (by decide), e.k1.get 22 (by decide), e.kc.get 22 (by decide)])
    (by rw [k2.get 24 (by decide), e.k1.get 24 (by decide), e.kc.get 24 (by decide)]; exact e.ev.s8)
    e.ev.tdLt
    ⟨by rw [k2.get 18 (by decide)]; exact e.cs.s2, by rw [k2.get 19 (by decide)]; exact e.cs.s3,
      by rw [k2.get 20 (by decide)]; exact e.cs.s4, by rw [k2.get 21 (by decide)]; exact e.cs.s5⟩
    (by rw [k2.get 2 (by decide), e.e2, e.kc.get 2 (by decide)])
    (((k2.mono (by decide)).trans (e.k1.mono (by decide))).trans (e.kc.mono (by decide))) hsb hsrt

/-- The call's leaks within the activation's before it. -/
theorem grow0 (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H'
    F' L' C' G' st' ex) (hlc : leakOne c ≤ k) :
    G'.lk.length + (ex ++ xs).length + 4 * (k - leakOne c) ≤ G.lk.length + xs.length + 4 * k :=
  e.grow hlc (Nat.le_refl _)

theorem pin0 (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F'
    L' C' G' st' ex) : StrPin G.strs G'.strs hs.tail :=
  e.pin (StrPin.refl _ _)

end EvCall

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st' st'' : St} {ex : List GV} {r : Status} {n : Nat}
  {Ge : DcG} {hse xse : List GV} {ke : Nat}

/-- **Status `0`** (`DC_OKAY`, or the square root pushed): on to `rest`
with the state `st'`. -/
theorem evs_zero_k (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (h10 : R' 10 = BitVec.ofNat 64 0) (hlc : leakOne c ≤ k)
    (hsb : StrBound (2 ^ 24) st') (hsrt : ArrSorted st')
    (hhead : EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs st' ⟨rest, td, false⟩)
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st' ⟨rest, td, false⟩) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (if rest = [] then 0x80001728#64 else 0x80001528#64)
      R' M' := by
  split
  · rename_i hr
    subst hr
    refine evl_0 hlive h10 e.cs fun R2 k2 => ?_
    obtain ⟨o', -, -, -, ev'⟩ := e.same (e.hal hlc) hsb hsrt (R2 := R2) (k2.mono (by decide))
    exact hend rfl _ R2 M' H' F' L' C' G' _ _ o' ev' (e.grow0 hlc) e.pin0
  · refine rt_ok_mid hlive h10 e.cs fun R2 k2 h8 h12 => ?_
    obtain ⟨o', -, -, -, ev'⟩ := ev_adv e.ev e.kc e.c23 e.mem e.k1 e.e2 e.post (e.hal hlc) hsb hsrt
      (m := 0) (td' := td) (neg' := false) (by omega) e.ev.tdLt (R2 := R2)
      (k2.mono (by decide)) (by rw [h8]; simp)
      (by rw [k2.get 24 (by decide), e.k1.get 24 (by decide), e.kc.get 24 (by decide)]; exact e.ev.s8)
    simp only [List.drop_zero] at ev'
    exact ev_cont_k (bltu_800017d0 hlive) ev' h12 (e.grow0 hlc) e.pin0 hhead hend

/-- **`DC_OKAY`** (term direction). -/
theorem evs_ok (hlive : ∀ p ∈ dcText, live p.1) (IH : LoopIH live S Q n)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (hres : dcFunc 70 st c rest.head? neg = .ok st') (h10 : R' 10 = BitVec.ofNat 64 0)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (if rest = [] then 0x80001728#64 else 0x80001528#64)
      R' M' := by
  obtain ⟨hfu', -, hlc⟩ := hfu.ok hres
  obtain ⟨hsb, hsrt⟩ := res_ok_facts e.ev.sb e.ev.srt hres
  exact evs_zero_k hlive e h10 hlc hsb hsrt (EvHeadK.ofIH IH hfu' hoom htl hgrow hpin hk)
    (EvEndK.ofFuel hlive hfu' htl hgrow hpin hk)

/-- **`DC_NEGCMP`**: `next_negcmp = 1`, on to `rest`. -/
theorem evs_neg_k (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex)
    (h10 : R' 10 = BitVec.ofNat 64 9) (hlc : leakOne c ≤ k)
    (hhead : EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs st ⟨rest, td, true⟩)
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st ⟨rest, td, true⟩) :
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64)
      R' M' := by
  have hj : ∀ R2, Keeps [8, 10, 12, 15] R2 R' → R2 8 = R' 23 → R2 12 = 1#64 →
      DWO live S Q (t0 ++ Dc.outStr st.out) 0x800015a0#64 R2 M' := fun R2 k2 h8 h12 => by
    obtain ⟨o', -, -, -, ev'⟩ := ev_adv e.ev e.kc e.c23 e.mem e.k1 e.e2 e.post (e.hal hlc) e.ev.sb
      e.ev.srt (m := 0) (td' := td) (neg' := true) (by omega) e.ev.tdLt (R2 := R2)
      (k2.mono (by decide)) (by rw [h8]; simp)
      (by rw [k2.get 24 (by decide), e.k1.get 24 (by decide), e.kc.get 24 (by decide)]; exact e.ev.s8)
    simp only [List.drop_zero] at ev'
    exact ev_cont_k (bltu_800015a0 hlive) ev' h12 (e.grow0 hlc) e.pin0 hhead hend
  split
  · exact rt_neg_last hlive h10 e.cs hj
  · exact rt_neg_mid hlive h10 e.cs hj

/-- **`DC_NEGCMP`** (term direction). -/
theorem evs_neg (hlive : ∀ p ∈ dcText, live p.1) (IH : LoopIH live S Q n)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex)
    (hres : dcFunc 70 st c rest.head? neg = .negcmp) (h10 : R' 10 = BitVec.ofNat 64 9)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  obtain ⟨hfu', -, hlc⟩ := hfu.negcmp hres
  exact evs_neg_k hlive e h10 hlc (EvHeadK.ofIH IH hfu' hoom htl hgrow hpin hk)
    (EvEndK.ofFuel hlive hfu' htl hgrow hpin hk)

/-- **`DC_EVALTOS`**: the `DC_EVALTOS` code on `rest`. -/
theorem evs_tos_k (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (hres : dcFunc 70 st c rest.head? neg = .evalTos st') (h10 : R' 10 = BitVec.ofNat 64 3)
    (hlc : leakOne c ≤ k)
    (htos : EvTosK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs st' rest td) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (if rest = [] then 0x80001728#64 else 0x80001528#64)
      R' M' := by
  have h1 := dcFunc_strBound (lm := 70) (c := c) (peek := rest.head?) (neg := neg) e.ev.sb (by decide)
  have h2 := dcFunc_arrSorted (lm := 70) (c := c) (peek := rest.head?) (neg := neg) e.ev.srt
  rw [hres] at h1 h2
  have hj : ∀ R2, Keeps [8, 10, 15, 25] R2 R' → R2 8 = R' 23 → R2 25 = R' 2 + 32#64 →
      DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80001748#64 R2 M' := fun R2 k2 h8 h25 => by
    obtain ⟨o', -, -, -, ev'⟩ := ev_adv e.ev e.kc e.c23 e.mem e.k1 e.e2 e.post (e.hal hlc) h1 h2
      (m := 0) (td' := td) (neg' := false) (by omega) e.ev.tdLt (R2 := R2)
      (k2.mono (by decide)) (by rw [h8]; simp)
      (by rw [k2.get 24 (by decide), e.k1.get 24 (by decide), e.kc.get 24 (by decide)]; exact e.ev.s8)
    simp only [List.drop_zero] at ev'
    exact htos R2 M' H' F' L' C' G' _ o' ev'
      (by rw [h25, e.e2, e.kc.get 2 (by decide), e.ev.r2, BitVec.ofNat_add_ofNat])
      (e.grow0 hlc) e.pin0
  split
  · exact rt_tos_last hlive h10 e.cs hj
  · exact rt_tos_mid hlive h10 e.cs hj

/-- **`DC_EVALTOS`** (term direction). -/
theorem evs_tos (hlive : ∀ p ∈ dcText, live p.1) (IH : TosIH live S Q n)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (hres : dcFunc 70 st c rest.head? neg = .evalTos st') (h10 : R' 10 = BitVec.ofNat 64 3)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  obtain ⟨hfu', -, hlc⟩ := hfu.evalTos hres
  exact evs_tos_k hlive e hres h10 hlc (EvTosK.ofIH IH hfu' hoom htl hgrow hpin hk)

/-- **`DC_QUIT`**: out of the activation (`EvQuitK`), or on to `rest` with
fewer levels to quit. -/
theorem evs_quit_k (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (hres : dcFunc 70 st c rest.head? neg = .quit st') (h10 : R' 10 = BitVec.ofNat 64 4)
    (hlc : leakOne c ≤ k)
    (hout : td ≤ st'.unwind → EvQuitK live S Q t0 sp W d k q M0 R0 G hs xs st' td)
    (hhead : st'.unwind < td →
      EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs st' ⟨rest, td - st'.unwind, false⟩)
    (hend : st'.unwind < td →
      EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st' ⟨rest, td - st'.unwind, false⟩) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  have h1 := dcFunc_strBound (lm := 70) (c := c) (peek := rest.head?) (neg := neg) e.ev.sb (by decide)
  have h2 := dcFunc_arrSorted (lm := 70) (c := c) (peek := rest.head?) (neg := neg) e.ev.srt
  rw [hres] at h1 h2
  have hj : ∀ R1, Keeps [10, 15] R1 R' → DWO live S Q (t0 ++ Dc.outStr st'.out) 0x800016b8#64 R1 M' := by
    intro R1 k1
    by_cases hle : td ≤ st'.unwind
    · obtain ⟨o', -, -, -, ev'⟩ := e.same (e.hal hlc) h1 h2 (R2 := R1) (k1.mono (by decide))
      exact hout hle _ R1 M' H' F' L' C' G' _ _ o' ev' rfl (e.grow0 hlc) e.pin0
    · have hlt : st'.unwind < td := by omega
      refine rt_quit_stay hlive e.post.dc.glob e.post.dc.view.unwind
        (by rw [k1.get 24 (by decide), e.k1.get 24 (by decide), e.kc.get 24 (by decide)]; exact e.ev.s8)
        hlt e.ev.tdLt fun R2 k2 h8 h12 h24 => ?_
      obtain ⟨o', -, -, -, ev'⟩ := ev_adv e.ev e.kc e.c23 e.mem e.k1 e.e2 e.post (e.hal hlc) h1 h2
        (m := 0) (td' := td - st'.unwind) (neg' := false) (by omega)
        (by have h := e.ev.tdLt; simp only at h; omega)
        (R2 := R2) ((k2.mono (by decide)).trans (k1.mono (by decide)))
        (by rw [h8, k1.get 23 (by decide)]; simp) h24
      simp only [List.drop_zero] at ev'
      exact ev_cont_k (bltu_800016d0 hlive) ev' h12 (e.grow0 hlc) e.pin0 (hhead hlt) (hend hlt)
  split
  · exact evl_4 hlive h10 e.cs hj
  · exact evm_4 hlive h10 e.cs hj

/-- **`DC_QUIT`** (term direction). -/
theorem evs_quit (hlive : ∀ p ∈ dcText, live p.1) (IH : LoopIH live S Q n)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (hres : dcFunc 70 st c rest.head? neg = .quit st') (h10 : R' 10 = BitVec.ofNat 64 4)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  have hlc : leakOne c ≤ k := by
    by_cases hle : td ≤ st'.unwind
    · exact (hfu.quitOut hres hle).2.2.2
    · exact (hfu.quitStay hres (by omega)).2.2
  refine evs_quit_k hlive e hres h10 hlc (fun hle => ?_) (fun hlt => ?_) (fun hlt => ?_)
  · obtain ⟨rfl, rfl, -, -⟩ := hfu.quitOut hres hle
    exact EvQuitK.ofK hlive htl hgrow hpin hk hle
  · exact EvHeadK.ofIH IH (hfu.quitStay hres hlt).1 hoom htl hgrow hpin hk
  · exact EvEndK.ofFuel hlive (hfu.quitStay hres hlt).1 htl hgrow hpin hk

end

end Dc.Mach
