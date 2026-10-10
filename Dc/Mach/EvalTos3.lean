import Dc.Mach.EvalTos2

/-!
# `DC_EVALTOS`: the nested activation's entry and return (M10)

`EvAt.nestEntry`: after `dc_pop` moved a string into the slot
`s9 = sp - 176 + 32`, the nested `evalstr (s9)` meets `EvEntry` at
`sp - 176`, one level of nesting less, a budget `k1 ≤ k`, the caller's
handles behind the popped one.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **The nested activation's premises** after `dc_pop (s9)`. -/
theorem EvAt.nestEntry {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64}
    {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
    {hs xs : List GV} {st : St} {f : Frame} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o) {d1 k1 : Nat} (hd : d = d1 + 1)
    (hk1 : k1 ≤ k) {M1 : Mem} {H1 : Heap} {G1 : DcG} {x : List Nat} {st1 : St} {p' : Nat}
    (h1 : DcAt S M1 H1 F L C G1 (.str p' :: (xs ++ hs)) st1) (hst : st = st1.push (.str x))
    (hlk : G1.lk = G.lk) (hd1 : DatAt M1 (sp - 176 + 32) (.str p'))
    (hpo : PopOut (sp - 176) (sp - 176 + 32) M1 M)
    {o1 : StrObj} (ho1 : o1 ∈ G1.strs) (hp1 : o1.hb.pay = p') (hx : o1.s = x)
    {R1 : Nat → BitVec 64} (h2 : R1 2 = BitVec.ofNat 64 (sp - 176))
    (h10 : R1 10 = BitVec.ofNat 64 (sp - 176 + 32)) (hal : (R1 1).toNat % 4 = 0) :
    EvEntry S (sp - 176) (W - 176) d1 k1 (sp - 176 + 32) M1 R1 H1 F L C G1
      (.str p' :: (xs ++ hs)) [] st1 o1 := by
  have hstk := ev.stk; have hab := ev.room; have hbud := ev.budget
  have hfr := ev.frame
  have hfl := hfr.lo; have hfh := hfr.hi; have hfa := hfr.al
  have hs0 : st.stack = .str x :: st1.stack := by rw [hst]; rfl
  have hvb := ev.sb.top hs0
  exact
    { len := by rw [hx]; exact hvb x (by simp [Val.strs])
      sb := ev.sb.stk (by rw [hst]; rfl) fun v hv => ev.sb.vb v (by rw [hs0]; exact List.mem_cons_of_mem _ hv)
      srt := ev.srt.regs (by rw [hst]; rfl)
      dc := by simpa using h1
      strIn := ho1
      held := by rw [hp1]; rfl
      slot := by rw [hp1]; exact hd1
      slotPlace := ⟨fun i hi => hfr.own _ (by omega) (by omega), by omega, by omega, by omega⟩
      r2 := h2
      r10 := h10
      al := hal
      frame := hfr.within (m := 176) (n := W - 176) (by omega) (by decide)
      room := by simp only [heapEnd] at hab ⊢; omega
      stk := by omega
      stkPr := by have := ev.stkPr; omega
      stkDn := by have := ev.stkDn; omega
      budget := by simp only [List.length_append, List.length_cons, List.length_nil, hlk] at hbud ⊢; omega
      mb := (ev.mbGlobs fun a e1 e2 _ e4 e5 _ => hpo a e1 e2
        (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega)) (by omega)).1
      err := ev.err
      globs := (ev.mbGlobs fun a e1 e2 _ e4 e5 _ => hpo a e1 e2
        (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega)) (by omega)).2 }

/-- **The nested activation's out-of-memory continuation** from the
activation's. -/
theorem EvAt.nestOom {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {sp W d k q : Nat} {M0 : Mem}
    {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
    {G : DcG} {hs xs : List GV} {st : St} {f : Frame} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o) (hoom : EvOom live S Q sp W q M0)
    {M1 : Mem} (hpo : PopOut (sp - 176) (sp - 176 + 32) M1 M) :
    EvOom live S Q (sp - 176) (W - 176) (sp - 176 + 32) M1 := by
  have hstk := ev.stk; have hab := ev.room
  intro t' R' M' sp' o'
  have := o'.lo; have := o'.hi
  refine hoom t' R' M' sp' ⟨by omega, by omega, o'.r2, fun a e1 e2 e3 e4 => ?_, o'.al⟩
  have hoc : ¬ ocG a := fun h => e4 (.inl h)
  have hq : ¬ (q ≤ a ∧ a < q + 16) := fun h => e4 (.inr (.inl h))
  have hip : ¬ InP a := fun h => e4 (.inr (.inr h))
  rw [o'.out a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))
    (fun h => by rcases h with h | h | h
                 · exact hoc h
                 · exact e3 (by simp only [frameIn]; omega)
                 · exact hip h),
    hpo a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))
      (Classical.byContradiction fun hc => e3 (by simp only [frameIn]; omega))]
  exact ev.out a e1 e2 hoc (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))
    (fun hf => e3 (by simp only [frameIn]; omega)) hq hip

/-- **The activation's return with status `r`** (`0x8000185c`) with the
invariant over the state `st'`. -/
def EvRetK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (G : DcG)
    (hs xs : List GV) (st' : St) (r : Status) : Prop :=
  ∀ k' (R2 : Nat → BitVec 64) (M2 : Mem) (H2 : Heap) (F2 : List Blk) (L2 : List NumObj)
    (C2 : BcConsts) (G2 : DcG) (xs2 : List GV) (f'' : Frame) (o' : StrObj),
    EvAt S sp W d k' q M0 R0 R2 M2 H2 F2 L2 C2 G2 hs xs2 st' f'' o' → R2 10 = statusWord r →
    G2.lk.length + xs2.length + 4 * k' ≤ G.lk.length + xs.length + 4 * k →
    StrPin G.strs G2.strs hs.tail →
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x8000185c#64 R2 M2

theorem EvRetK.ofK {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {sp W d k q : Nat} {M0 : Mem}
    {R0 : Nat → BitVec 64} {G : DcG} {hs xs : List GV} {st' : St} {r : Status}
    {Ge : DcG} {hse xse : List GV} {ke : Nat} (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st' r) :
    EvRetK live S Q t0 sp W d k q M0 R0 G hs xs st' r :=
  fun _ _ _ _ _ _ _ _ _ _ _ ev h10 hg hp => ev_ret hlive ev h10 htl (by omega) (hpin.trans hp) hk

/-- **Back from the nested evaluation** (its return to `0x80001804` as an
`EvK` of the nested activation): its string freed, the activation's
invariant again over `⟨skipWs rest, td, false⟩` with the nested state `st1'`
and the nested activation's lost strings, then `DC_OKAY` on (`hok`) or
`DC_QUIT` (`hq1`, `hq0`). -/
theorem nest_return {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {sp W d k q : Nat} {M0 : Mem}
    {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
    {G : DcG} {hs xs : List GV} {st : St} {rest : List Nat} {td : Nat} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o)
    {d1 k1 : Nat} (hd : d = d1 + 1) (hk1 : k1 ≤ k)
    {M1 : Mem} {G1 : DcG} {p' : Nat} (hlk1 : G1.lk = G.lk) (hstr1 : G1.strs = G.strs)
    (hpo : PopOut (sp - 176) (sp - 176 + 32) M1 M)
    {j : Nat} (hj : j ≤ o.s.length) (hdj : o.s.drop j = skipWs rest)
    {R1 : Nat → BitVec 64} (hkR : Keeps (1 :: 8 :: 10 :: 23 :: cClob) R1 R)
    (h8 : R1 8 = BitVec.ofNat 64 (o.tb.pay + j)) (h23 : R1 23 = 2#64)
    (h1 : R1 1 = 0x80001804#64)
    {st1' : St} {r1 : Status} (hsb1 : StrBound (2 ^ 24) st1') (hsrt1 : ArrSorted st1')
    (hok : r1 = .ok →
      EvHeadK live S Q t0 sp W d k (k - k1) q M0 R0 G hs xs st1' ⟨skipWs rest, td, false⟩ ∧
      EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st1' ⟨skipWs rest, td, false⟩)
    (hq1 : r1 = .quit → 0 < st1'.unwind →
      EvRetK live S Q t0 sp W d k q M0 R0 G hs xs { st1' with unwind := st1'.unwind - 1 } .quit)
    (hq0 : r1 = .quit → st1'.unwind = 0 → EvExitK live S Q t0 sp W d k q M0 R0 G hs xs st1') :
    EvK live S Q t0 (sp - 176) (W - 176) k1 (sp - 176 + 32) M1 R1 G1 (.str p' :: (xs ++ hs)) []
      st1' r1 := by
  intro R' M2 H2 F2 L2 C2 G2 xs' p'' kR e2 e10 post
  have hstk := ev.stk; have hab := ev.room
  have hfr := ev.frame
  have hfl := hfr.lo; have hfh := hfr.hi; have hfa := hfr.al
  have hdc := post.dc.perm (List.perm_middle (a := .str p'') (l₁ := xs') (l₂ := xs ++ hs))
  rw [h1]
  have e2' : R' 2 = BitVec.ofNat 64 (sp - 176) := by
    rw [e2, hkR.get 2 (by decide)]; exact ev.r2
  have e23 : R' 23 = 2#64 := by rw [kR.get 23 (by decide)]; exact h23
  refine rt_call_free hlive hdc post.slot (fun b h1 h2 => hfr.own b (by omega) (by omega))
    (by omega) (hfr.within (m := 176) (n := 32) (by omega) (by decide))
    (by simp only [heapEnd] at hab ⊢; omega) e2' e23
    fun R3 M3 H3 G3 k3 e14 hsn h3 hpin3 hout3 => ?_
  have hgr := post.grow
  simp only [List.length_nil, Nat.add_zero, hlk1] at hgr
  have hpinA : StrPin G.strs G3.strs (xs ++ hs) := by
    have := post.pin; rw [hstr1] at this
    exact this.trans (hpin3.mono fun g hg => List.mem_append_right _ hg)
  have hstep : EvStep S sp W (4 * k1) M G hs xs M3 H3 F2 L2 C2 G3 st1' xs' :=
    ⟨h3, by rw [hsn.lk]; exact hgr, hpinA, fun a e1 e2 e3 e4 e5 e6 => by
      rw [hout3 a e1 e2 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega)) e5,
        post.out a e1 e2 e3 e4 (fun h => e5 ⟨by omega, by omega⟩) e6,
        hpo a e1 e2 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))
          (Classical.byContradiction fun hc => e5 ⟨by omega, by omega⟩)]⟩
  have hk3 : Keeps (1 :: 8 :: 10 :: 14 :: 15 :: 23 :: cClob) R3 R :=
    by keeps_tac ((k3.mono (by decide)).trans ((kR.mono (by decide)).trans (hkR.mono (by decide))))
  have e8 : R3 8 = BitVec.ofNat 64 (o.tb.pay + j) := by
    rw [k3.get 8 (by decide), kR.get 8 (by decide)]; exact h8
  obtain ⟨o', -, -, -, ev'⟩ := ev.step hstep (k' := k - k1) (f' := ⟨skipWs rest, td, false⟩) (by omega)
    (j := j) hj hdj e8
    (by rw [hk3.get 9 (by decide)]) (by rw [hk3.get 22 (by decide)])
    (by rw [hk3.get 24 (by decide)]; exact ev.s8) ev.tdLt
    ⟨by rw [hk3.get 18 (by decide)]; exact ev.cs.s2, by rw [hk3.get 19 (by decide)]; exact ev.cs.s3,
      by rw [hk3.get 20 (by decide)]; exact ev.cs.s4, by rw [hk3.get 21 (by decide)]; exact ev.cs.s5⟩
    (by rw [hk3.get 2 (by decide)]) (hk3.mono (by decide)) hsb1 hsrt1
  have hg : G3.lk.length + (xs' ++ xs).length + 4 * (k - k1) ≤ G.lk.length + xs.length + 4 * k := by
    simp only [List.length_append]; rw [hsn.lk]; omega
  have hp : StrPin G.strs G3.strs hs.tail :=
    hpinA.mono fun g hg => List.mem_append_right _ (List.mem_of_mem_tail hg)
  have e14' : R3 14 = statusWord r1 := by rw [e14, e10]
  cases r1 with
  | ok =>
    obtain ⟨hhead, hend⟩ := hok rfl
    exact ev_after_ok hlive e14' fun R4 k4 h12 =>
      ev_cont_k (bltu_800017d0 hlive) (ev'.mod (k4.mono (by decide))) h12 hg hp hhead hend
  | quit =>
    refine ev_after_quit hlive ev' e14' (fun h0 R4 k4 => ?_) (fun h1 R4 M4 k4 e10' ev4 => ?_)
    · exact hq0 rfl h0 _ R4 M3 H3 F2 L2 C2 G3 _ _ o' (ev'.mod (k4.mono (by decide))) hg hp
    · exact hq1 rfl h1 _ R4 M4 H3 F2 L2 C2 G3 _ _ o' (ev4.mod (Keeps.refl _ _)) (by rw [e10']; rfl) hg hp


end Dc.Mach
