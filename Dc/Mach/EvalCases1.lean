import Dc.Mach.EvalLoop

/-!
# `evalstr`'s loop: status cases without callees (M10)

`DC_OKAY` after the last character, `DC_NEGCMP`, `DC_EVALTOS`, `DC_QUIT`.
`EvCall.same`: the invariant after the call with `s0` where it was (the
command's own position), for the routes that return.
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

end EvCall

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st' st'' : St} {ex : List GV} {r : Status} {n : Nat}
  {Ge : DcG} {hse xse : List GV} {ke : Nat}

/-- **`DC_OKAY` after the last character**: the exit. -/
theorem evs_ok_last (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c [] td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (hres : dcFunc 70 st c none neg = .ok st') (h10 : R' 10 = BitVec.ofNat 64 0)
    (hfu : EvFuel 70 (n + 1) d k st ⟨[c], td, neg⟩ st'' r)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80001728#64 R' M' := by
  obtain ⟨hfu', -, hlc⟩ := hfu.ok hres
  obtain ⟨rfl, rfl⟩ := hfu'.nil
  obtain ⟨hsb, hsrt⟩ := res_ok_facts e.ev.sb e.ev.srt hres
  refine evl_0 hlive h10 e.cs fun R2 k2 => ?_
  obtain ⟨o', -, -, -, ev'⟩ := e.same (e.hal hlc) hsb hsrt (R2 := R2) (k2.mono (by decide))
  exact ev_exit hlive ev' htl (e.grow hlc hgrow) (e.pin hpin) hk

/-- **`DC_NEGCMP`**: `next_negcmp = 1`, on to `rest`. -/
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
  have hj : ∀ R2, Keeps [8, 10, 12, 15] R2 R' → R2 8 = R' 23 → R2 12 = 1#64 →
      DWO live S Q (t0 ++ Dc.outStr st.out) 0x800015a0#64 R2 M' := fun R2 k2 h8 h12 => by
    obtain ⟨o', -, -, -, ev'⟩ := ev_adv e.ev e.kc e.c23 e.mem e.k1 e.e2 e.post (e.hal hlc) e.ev.sb
      e.ev.srt (m := 0) (td' := td) (neg' := true) (by omega) e.ev.tdLt (R2 := R2)
      (k2.mono (by decide)) (by rw [h8]; simp)
      (by rw [k2.get 24 (by decide), e.k1.get 24 (by decide), e.kc.get 24 (by decide)]; exact e.ev.s8)
    simp only [List.drop_zero] at ev'
    exact ev_cont hlive (bltu_800015a0 hlive) ev' hfu' htl (e.grow hlc hgrow) (e.pin hpin) hk
      fun hne => IH t0 sp W d _ q M0 R0 R2 M' H' F' L' C' G' hs _ st st'' _ o' r Ge hse xse ke
        hfu' hne ev' h12 hoom htl (e.grow hlc hgrow) (e.pin hpin) hk
  split
  · exact rt_neg_last hlive h10 e.cs hj
  · exact rt_neg_mid hlive h10 e.cs hj

/-- **`DC_EVALTOS`**: the `DC_EVALTOS` code on `rest`. -/
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
    exact IH t0 sp W d _ q M0 R0 R2 M' H' F' L' C' G' hs _ st' st'' rest td o' r Ge hse xse ke
      hfu' ev' (by rw [h25, e.e2, e.kc.get 2 (by decide), e.ev.r2, BitVec.ofNat_add_ofNat])
      hoom htl (e.grow hlc hgrow) (e.pin hpin) hk
  split
  · exact rt_tos_last hlive h10 e.cs hj
  · exact rt_tos_mid hlive h10 e.cs hj

/-- **`DC_QUIT`**: out of the activation, or on to `rest` with fewer
tail-recursion levels. -/
theorem evs_quit (hlive : ∀ p ∈ dcText, live p.1) (IH : LoopIH live S Q n)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (hres : dcFunc 70 st c rest.head? neg = .quit st') (h10 : R' 10 = BitVec.ofNat 64 4)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  have h1 := dcFunc_strBound (lm := 70) (c := c) (peek := rest.head?) (neg := neg) e.ev.sb (by decide)
  have h2 := dcFunc_arrSorted (lm := 70) (c := c) (peek := rest.head?) (neg := neg) e.ev.srt
  rw [hres] at h1 h2
  have hj : ∀ R1, Keeps [10, 15] R1 R' → DWO live S Q (t0 ++ Dc.outStr st'.out) 0x800016b8#64 R1 M' := by
    intro R1 k1
    by_cases hle : td ≤ st'.unwind
    · obtain ⟨rfl, rfl, -, hlc⟩ := hfu.quitOut hres hle
      obtain ⟨o', -, -, -, ev'⟩ := e.same (e.hal hlc) h1 h2 (R2 := R1) (k1.mono (by decide))
      exact ev_quit_out hlive ev' hle htl (e.grow hlc hgrow) (e.pin hpin) hk
    · have hlt : st'.unwind < td := by omega
      obtain ⟨hfu', -, hlc⟩ := hfu.quitStay hres hlt
      refine rt_quit_stay hlive e.post.dc.glob e.post.dc.view.unwind
        (by rw [k1.get 24 (by decide), e.k1.get 24 (by decide), e.kc.get 24 (by decide)]; exact e.ev.s8)
        hlt e.ev.tdLt fun R2 k2 h8 h12 h24 => ?_
      obtain ⟨o', -, -, -, ev'⟩ := ev_adv e.ev e.kc e.c23 e.mem e.k1 e.e2 e.post (e.hal hlc) h1 h2
        (m := 0) (td' := td - st'.unwind) (neg' := false) (by omega) (by have h := e.ev.tdLt; simp only at h; omega)
        (R2 := R2) ((k2.mono (by decide)).trans (k1.mono (by decide)))
        (by rw [h8, k1.get 23 (by decide)]; simp) h24
      simp only [List.drop_zero] at ev'
      exact ev_cont hlive (bltu_800016d0 hlive) ev' hfu' htl (e.grow hlc hgrow) (e.pin hpin) hk
        fun hne => IH t0 sp W d _ q M0 R0 R2 M' H' F' L' C' G' hs _ st' st'' _ o' r Ge hse xse ke
          hfu' hne ev' h12 hoom htl (e.grow hlc hgrow) (e.pin hpin) hk
  split
  · exact evl_4 hlive h10 e.cs hj
  · exact evm_4 hlive h10 e.cs hj

end

end Dc.Mach
