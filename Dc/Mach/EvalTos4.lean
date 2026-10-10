import Dc.Mach.EvalTos3

/-!
# `DC_EVALTOS`: the cases after `dc_pop` (M10)

From the popped datum's type at `0x800017a8`, with the invariant of the
activation at the `DC_EVALTOS` code (`ev`, over `⟨rest, td, false⟩`) and the
skip's position `j` (`o.s.drop j = skipWs rest`): a number pushed back and
the loop test (`tos_num`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The popped node's datum denotes the popped value. -/
theorem pop_den {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G G3 : DcG} {hs : List GV} {st st3 : St} {v : Val} {g : GV} {c : Blk}
    (h : DcAt S M H F L C G hs st) (hst : st = st3.push v)
    (hG : G = { G3 with stk := (c, g) :: G3.stk }) : g.Den ⟨L, G3.strs⟩ v := by
  have hd := h.den.stk
  subst hst hG
  cases hd with
  | cons h1 _ => exact h1

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {rest : List Nat} {td : Nat} {o : StrObj}

/-- **A number popped**: pushed back, the loop test at `0x800017d0` on
`⟨skipWs rest, td, false⟩`. -/
theorem tos_num (hlive : ∀ p ∈ dcText, live p.1)
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o)
    (hoom : EvOom live S Q sp W q M0)
    {j : Nat} (hj : j ≤ o.s.length) (hdj : o.s.drop j = skipWs rest)
    {R3 : Nat → BitVec 64} {M3 : Mem} {H3 : Heap} {G3 : DcG} {g : GV} {v : Val} {st3 : St} {c : Blk}
    (hst : st = st3.push v) (hG : G = { G3 with stk := (c, g) :: G3.stk })
    (hk3 : Keeps (1 :: 8 :: 23 :: cClob) R3 R) (h8 : R3 8 = BitVec.ofNat 64 (o.tb.pay + j))
    (h3 : DcAt S M3 H3 F L C G3 (g :: (xs ++ hs)) st3) (hd3 : DatAt M3 (sp - 176 + 32) g)
    (hpo : PopOut (sp - 176) (sp - 176 + 32) M3 M) {x : Num} (hv : v = .num x)
    (hhead : EvHeadK live S Q t0 sp W d k k q M0 R0 G hs xs st ⟨skipWs rest, td, false⟩)
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st ⟨skipWs rest, td, false⟩) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800017a8#64 R3 M3 := by
  have hstk := ev.stk; have hab := ev.room
  have hfr := ev.frame
  have hfl := hfr.lo; have hfh := hfr.hi; have hfa := hfr.al
  have hgv := pop_den ev.dc hst hG
  have hg1 : g.tag = 1 := by
    subst hv; cases g with
    | num _ => rfl
    | str _ => exact absurd hgv (by simp [GV.Den])
  have e2 : R3 2 = BitVec.ofNat 64 (sp - 176) := by rw [hk3.get 2 (by decide)]; exact ev.r2
  refine rt_tos_num hlive h3 hgv hg1 hd3 (fun b h1 h2 => hfr.own b (by omega) (by omega))
    (hfr.within (m := 176) (n := 64) (by omega) (by decide)) (by simp only [heapEnd] at hab ⊢; omega)
    e2 (fun R4 M4 H4 c4 k4 h12 h4 hso4 => ?_) (fun R4 M4 e4 hso4 => ev.oomK hoom (by omega) (by omega)
      e4 (by have := hfr.al; omega) fun a e1 e2 e3 e5 _ => (hso4 a e1 e2
        (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))).trans (hpo a e1 e2
          (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)) (by omega)))
  have hG4 : ({ G3 with stk := (c4, g) :: G3.stk } : DcG).lk = G.lk := by rw [hG]
  have hS4 : ({ G3 with stk := (c4, g) :: G3.stk } : DcG).strs = G.strs := by rw [hG]
  rw [← hst] at h4
  have hstep : EvStep S sp W 0 M G hs xs M4 H4 F L C { G3 with stk := (c4, g) :: G3.stk } st [] :=
    ⟨by simpa using h4, by rw [hG4]; simp, by rw [hS4]; exact StrPin.refl _ _,
      fun a e1 e2 e3 e4 e5 e6 => by
        rw [hso4 a e1 e2 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))]
        exact hpo a e1 e2 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))
          (Classical.byContradiction fun hc => e5 ⟨by omega, by omega⟩)⟩
  obtain ⟨o', -, -, -, ev'⟩ := ev.step hstep (k' := k) (f' := ⟨skipWs rest, td, false⟩) (by omega)
    (j := j) hj hdj (by rw [k4.get 8 (by decide)]; exact h8)
    (by rw [k4.get 9 (by decide), hk3.get 9 (by decide)]) (by rw [k4.get 22 (by decide), hk3.get 22 (by decide)])
    (by rw [k4.get 24 (by decide), hk3.get 24 (by decide)]; exact ev.s8) ev.tdLt
    ⟨by rw [k4.get 18 (by decide), hk3.get 18 (by decide)]; exact ev.cs.s2,
      by rw [k4.get 19 (by decide), hk3.get 19 (by decide)]; exact ev.cs.s3,
      by rw [k4.get 20 (by decide), hk3.get 20 (by decide)]; exact ev.cs.s4,
      by rw [k4.get 21 (by decide), hk3.get 21 (by decide)]; exact ev.cs.s5⟩
    (by rw [k4.get 2 (by decide), hk3.get 2 (by decide)])
    ((k4.mono (by decide)).trans (hk3.mono (by decide))) ev.sb ev.srt
  exact ev_cont_k (bltu_800017d0 hlive) ev' h12 (by simp only [List.nil_append]; rw [hG4]; omega)
    (by rw [hS4]; exact StrPin.refl _ _) hhead hend

/-- **A string popped at the text's end: the tail call** (`0x800017a8`):
`*string` the popped string, the loop on its text with `tail_depth + 1`. -/
theorem tos_tail (hlive : ∀ p ∈ dcText, live p.1)
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o)
    {R3 : Nat → BitVec 64} {M3 : Mem} {H3 : Heap} {G3 : DcG} {g : GV} {v : Val} {st3 : St} {c : Blk}
    (hst : st = st3.push v) (hG : G = { G3 with stk := (c, g) :: G3.stk })
    (hk3 : Keeps (1 :: 8 :: 23 :: cClob) R3 R) (h8 : R3 8 = BitVec.ofNat 64 (o.tb.pay + o.s.length))
    (h3 : DcAt S M3 H3 F L C G3 (g :: (xs ++ hs)) st3) (hd3 : DatAt M3 (sp - 176 + 32) g)
    (hpo : PopOut (sp - 176) (sp - 176 + 32) M3 M) {x : List Nat} (hv : v = .str x)
    (htail : ∀ p', g = .str p' → td + 1 < 2 ^ 31 ∧
      EvHeadK live S Q t0 sp W d k k q M0 R0 G (.str p' :: hs.tail) xs st3 ⟨x, td + 1, false⟩ ∧
      EvEndK live S Q t0 sp W d k q M0 R0 G (.str p' :: hs.tail) xs st3 ⟨x, td + 1, false⟩) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800017a8#64 R3 M3 := by
  have hstk := ev.stk; have hab := ev.room
  have hfr := ev.frame
  have hfl := hfr.lo; have hfh := hfr.hi; have hfa := hfr.al
  have hq := ev.slotPlace
  have hql := hq.lo; have hqh := hq.hi
  have hgv := pop_den ev.dc hst hG
  subst hv
  obtain ⟨p', rfl⟩ : ∃ p', g = .str p' := by
    cases g with
    | num _ => exact absurd hgv (by simp [GV.Den])
    | str p' => exact ⟨p', rfl⟩
  obtain ⟨o1, ho1, hp1, hx1⟩ := hgv
  obtain ⟨htd, hhead, hend⟩ := htail p' rfl
  obtain ⟨hst', rfl⟩ : ∃ hst', hs = .str o.hb.pay :: hst' := by
    have hh := ev.held
    cases hs with
    | nil => cases hh
    | cons g hs' => simp at hh; subst hh; exact ⟨hs', rfl⟩
  have hs0 : st.stack = .str x :: st3.stack := by rw [hst]; rfl
  have hvb := ev.sb.top hs0
  have e2 : R3 2 = BitVec.ofNat 64 (sp - 176) := by rw [hk3.get 2 (by decide)]; exact ev.r2
  have e9 : R3 9 = BitVec.ofNat 64 (o.tb.pay + o.s.length) := by rw [hk3.get 9 (by decide)]; exact ev.s1
  have hw : ldv .ld M3 (q + 8) = BitVec.ofNat 64 o.hb.pay := by
    rw [ldv_congr .ld fun i hi => hpo _ (outHeap_of_ge (by simp only [heapEnd] at hab ⊢; omega))
      (fun hg => by have := hg.1.lt; simp only [heapStart, heapEnd] at this hab; omega)
      (fun hf => by simp only [frameIn] at hf; omega) (by simp only [widthOfM] at hi; omega)]
    exact ev.slot.ptr
  have hdc : DcAt S M3 H3 F L C G3 (.str o.hb.pay :: (.str p' :: (xs ++ hst'))) st3 :=
    h3.perm (List.perm_middle (a := GV.str o.hb.pay) (l₁ := GV.str p' :: xs) (l₂ := hst'))
  refine rt_tos_str hlive (g := .str p') rfl hd3 (fun b h1 h2 => hfr.own b (by omega) (by omega))
    (hfr.within (m := 176) (n := 64) (by omega) (by decide)) e2
    (fun R4 k4 h89 => ?_) (fun R4 k4 _ hne => absurd (by rw [h8, e9]) hne)
  refine rt_tail hlive hdc (by rw [Nat.sub_add_cancel (by omega)]; exact hq) hw hd3 (by simp) ho1 hp1
    (fun b h1 h2 => hfr.own b (by omega) (by omega)) (hfr.within (m := 176) (n := 32) (by omega) (by decide))
    (by simp only [heapEnd] at hab ⊢; omega) htd (by rw [k4.get 2 (by decide)]; exact e2)
    (by rw [k4.get 22 (by decide), hk3.get 22 (by decide)]; exact ev.s6)
    (by rw [k4.get 24 (by decide), hk3.get 24 (by decide)]; exact ev.s8)
    fun R5 H5 G5 M5 o' k5 ho' f1 f2 f3 e8 e9' e24 e12 hsn h5 hpin5 hd5 hout5 => ?_
  have hlk : G5.lk = G.lk := by rw [hsn.lk, hG]
  have hstr : G3.strs = G.strs := by rw [hG]
  have hdc5 : DcAt S M5 H5 F L C G5 (xs ++ (.str o'.hb.pay :: hst')) st3 := by
    rw [f1, hp1]
    exact h5.perm (List.perm_middle (a := GV.str p') (l₁ := xs) (l₂ := hst')).symm
  have hkR : Keeps (1 :: 8 :: 9 :: 12 :: 15 :: 23 :: 24 :: cClob) R5 R := by
    keeps_tac ((k5.mono (by decide)).trans ((k4.mono (by decide)).trans (hk3.mono (by decide))))
  have ev5 := ev.retarget (hs' := .str o'.hb.pay :: hst') (td' := td + 1) hdc5
    (by rw [hlk]; exact Nat.le_refl _) (by rfl) ho' rfl (by rw [f1, hp1]; exact hd5)
    (fun a e1 e2 e3 e4 e5 e6 e7 => by
      rw [hout5 a e1 e2 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega)) e7]
      exact hpo a e1 e2 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))
        (Classical.byContradiction fun hc => e5 ⟨by omega, by omega⟩))
    (ev.sb.stk (by rw [hst]; rfl) fun w hw => ev.sb.vb w (by rw [hs0]; exact List.mem_cons_of_mem _ hw))
    (ev.srt.regs (by rw [hst]; rfl)) (by rw [f3, hx1]; exact hvb x (by simp [Val.strs]))
    e8 e9' (by rw [hkR.get 22 (by decide)]) e24 htd
    ⟨by rw [hkR.get 18 (by decide)]; exact ev.cs.s2, by rw [hkR.get 19 (by decide)]; exact ev.cs.s3,
      by rw [hkR.get 20 (by decide)]; exact ev.cs.s4, by rw [hkR.get 21 (by decide)]; exact ev.cs.s5⟩
    (by rw [hkR.get 2 (by decide)]) (hkR.mono (by decide))
  rw [f3, hx1] at ev5
  have hst3 : (st3 : St).out = st.out := by rw [hst]; rfl
  rw [← hst3]
  exact ev_cont_k (G := G) (xs := xs) (k := k) (bltu_800018f0 hlive) ev5 e12 (by rw [hlk]; omega)
    (by rw [← hstr]; exact hpin5.mono fun g hg => List.mem_cons_of_mem _ (List.mem_append_right _ hg))
    (by rw [f1, hp1]; exact hhead) (by rw [f1, hp1]; exact hend)

/-- **The nested evaluation's hook**: a nesting level `d1` below `d`, a budget
`k1 ≤ k`, outcomes `Pn` of the nested evaluation of the popped string over
the state `st3`; the run of the nested `evalstr` from its entry for every
return continuation covering `Pn`; for each outcome, the state's model facts
and the activation's continuations (`DC_OKAY` on, `DC_QUIT` up or out). -/
def TosNestK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W d k q : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (F : List Blk)
    (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st3 : St) (rest : List Nat)
    (td : Nat) : Prop :=
  ∃ d1 k1 : Nat, ∃ Pn : St → Status → Prop, d = d1 + 1 ∧ k1 ≤ k ∧
    (∀ (R1 : Nat → BitVec 64) (M1 : Mem) (H1 : Heap) (G1 : DcG) (p' : Nat) (o1 : StrObj),
      EvEntry S (sp - 176) (W - 176) d1 k1 (sp - 176 + 32) M1 R1 H1 F L C G1
        (.str p' :: (xs ++ hs)) [] st3 o1 →
      EvOom live S Q (sp - 176) (W - 176) (sp - 176 + 32) M1 →
      (∀ st1 r1, Pn st1 r1 → EvK live S Q t0 (sp - 176) (W - 176) k1 (sp - 176 + 32) M1 R1 G1
        (.str p' :: (xs ++ hs)) [] st1 r1) →
      DWO live S Q (t0 ++ Dc.outStr st3.out) 0x80001448#64 R1 M1) ∧
    (∀ st1 r1, Pn st1 r1 → StrBound (2 ^ 24) st1 ∧ ArrSorted st1 ∧
      (r1 = .ok →
        EvHeadK live S Q t0 sp W d k (k - k1) q M0 R0 G hs xs st1 ⟨skipWs rest, td, false⟩ ∧
        EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st1 ⟨skipWs rest, td, false⟩) ∧
      (r1 = .quit → 0 < st1.unwind →
        EvRetK live S Q t0 sp W d k q M0 R0 G hs xs { st1 with unwind := st1.unwind - 1 } .quit) ∧
      (r1 = .quit → st1.unwind = 0 → EvExitK live S Q t0 sp W d k q M0 R0 G hs xs st1))

/-- **A string popped before another byte: the nested evaluation**
(`0x800017a8`, then `evalstr (s9)` at `0x800017fc`). -/
theorem tos_call (hlive : ∀ p ∈ dcText, live p.1)
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o)
    (h25 : R 25 = BitVec.ofNat 64 (sp - 176 + 32)) (hoom : EvOom live S Q sp W q M0)
    {j : Nat} (hj : j < o.s.length) (hdj : o.s.drop j = skipWs rest)
    {R3 : Nat → BitVec 64} {M3 : Mem} {H3 : Heap} {G3 : DcG} {g : GV} {v : Val} {st3 : St} {c : Blk}
    (hst : st = st3.push v) (hG : G = { G3 with stk := (c, g) :: G3.stk })
    (hk3 : Keeps (1 :: 8 :: 23 :: cClob) R3 R) (h8 : R3 8 = BitVec.ofNat 64 (o.tb.pay + j))
    (h3 : DcAt S M3 H3 F L C G3 (g :: (xs ++ hs)) st3) (hd3 : DatAt M3 (sp - 176 + 32) g)
    (hpo : PopOut (sp - 176) (sp - 176 + 32) M3 M) {x : List Nat} (hv : v = .str x)
    (hnest : TosNestK live S Q t0 sp W d k q M0 R0 F L C G hs xs st3 rest td) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800017a8#64 R3 M3 := by
  have hstk := ev.stk; have hab := ev.room
  have hfr := ev.frame
  have hfl := hfr.lo; have hfh := hfr.hi; have hfa := hfr.al
  have hgv := pop_den ev.dc hst hG
  subst hv
  obtain ⟨p', rfl⟩ : ∃ p', g = .str p' := by
    cases g with
    | num _ => exact absurd hgv (by simp [GV.Den])
    | str p' => exact ⟨p', rfl⟩
  obtain ⟨o1, ho1, hp1, hx1⟩ := hgv
  obtain ⟨d1, k1, Pn, hd, hk1, hrun, hcont⟩ := hnest
  have hlk : G3.lk = G.lk := by rw [hG]
  have hstr : G3.strs = G.strs := by rw [hG]
  have e2 : R3 2 = BitVec.ofNat 64 (sp - 176) := by rw [hk3.get 2 (by decide)]; exact ev.r2
  have e9 : R3 9 = BitVec.ofNat 64 (o.tb.pay + o.s.length) := by rw [hk3.get 9 (by decide)]; exact ev.s1
  have e25 : R3 25 = BitVec.ofNat 64 (sp - 176 + 32) := by
    rw [hk3.get 25 (by decide)]; exact h25
  have hne89 : R3 8 ≠ R3 9 := by
    rw [h8, e9]; intro e
    have := congrArg BitVec.toNat e
    have hso := ev.dc.view.strs o ev.strIn
    have hmem : o.tb ∈ G.blocks :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ev.strIn, by simp⟩))
    have bt := blk_bounds ev.dc.heap.heap (ev.dc.heap.raw.live o.tb hmem)
    have htz := hso.tsz
    simp only [heapStart, heapEnd] at bt
    simp only [BitVec.toNat_ofNat] at this; omega
  have hst3 : st.out = st3.out := by rw [hst]; rfl
  refine rt_tos_str hlive (g := .str p') rfl hd3 (fun b h1 h2 => hfr.own b (by omega) (by omega))
    (hfr.within (m := 176) (n := 64) (by omega) (by decide)) e2
    (fun R4 k4 h89 => absurd h89 hne89) (fun R4 k4 h23 _ => ?_)
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e25' : R4 25 = BitVec.ofNat 64 (sp - 176 + 32) := by rw [k4.get 25 (by decide)]; exact e25
  bc_run hlive hlive [e25'] at 0x80001448
  rw [hst3]
  refine hrun _ M3 H3 G3 p' o1 ?_ (ev.nestOom hoom hpo) fun st1 r1 hP => ?_
  · exact ev.nestEntry hd hk1 h3 hst hlk hd3 hpo ho1 hp1 hx1
      (by bsimp []; rw [k4.get 2 (by decide)]; exact e2) (by bsimp []) (by bsimp [])
  · obtain ⟨hsb1, hsrt1, hok, hq1, hq0⟩ := hcont st1 r1 hP
    exact nest_return hlive ev hd hk1 hlk hstr hpo (Nat.le_of_lt hj) hdj
      (by keeps_tac ((k4.mono (by decide)).trans (hk3.mono (by decide))))
      (by bsimp []; rw [k4.get 8 (by decide)]; exact h8) (by bsimp []; exact h23) (by bsimp [])
      hsb1 hsrt1 hok hq1 hq0

end

end Dc.Mach
