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

end

end Dc.Mach
