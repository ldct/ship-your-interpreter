import Dc.Mach.EvalTos4

/-!
# `DC_EVALTOS`, continuation-generic (M10)

`ev_tos_k`: the `DC_EVALTOS` code at `0x80001748` from the invariant over
`⟨rest, td, false⟩` (`s9 = sp - 176 + 32`): the skip (`tos_skip`), then
`dc_pop`; an empty stack or a number on to `⟨skipWs rest, td, false⟩`
(`hplain`), a string at the text's end the tail call (`htail`), else the
nested evaluation (`hnest`, `TosNestK`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The state below a pushed value. -/
theorem push_with {st st3 : St} {v v' : Val} {more : List Val} (hst : st = st3.push v)
    (hs : st.stack = v' :: more) : ({ st with stack := more } : St) = st3 ∧ v' = v := by
  subst hst
  simp only [St.push, List.cons.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  exact ⟨rfl, rfl⟩

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {rest : List Nat} {td : Nat} {o : StrObj}

/-- **The invariant after a failed `dc_pop`** (the state unchanged), at the
skip's position `j`. -/
theorem EvAt.afterPop (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o)
    {j : Nat} (hj : j ≤ o.s.length) {f' : Frame} (hdj : o.s.drop j = f'.s) (hf : f'.td = td)
    {R3 : Nat → BitVec 64} {M3 : Mem} (hk3 : Keeps (1 :: 8 :: 12 :: 23 :: cClob) R3 R)
    (h8 : R3 8 = BitVec.ofNat 64 (o.tb.pay + j))
    (h3 : DcAt S M3 H F L C G (xs ++ hs) st) (hpo : PopOut (sp - 176) (sp - 176 + 32) M3 M) :
    ∃ o', EvAt S sp W d k q M0 R0 R3 M3 H F L C G hs xs st f' o' := by
  have hstk := ev.stk
  have hstep : EvStep S sp W 0 M G hs xs M3 H F L C G st [] :=
    ⟨by simpa using h3, by simp, StrPin.refl _ _, fun a e1 e2 e3 e4 e5 e6 =>
      hpo a e1 e2 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))
        (Classical.byContradiction fun hc => e5 ⟨by omega, by omega⟩)⟩
  obtain ⟨o', -, -, -, ev'⟩ := ev.step hstep (k' := k) (f' := f') (by omega) (j := j) hj hdj h8
    (by rw [hk3.get 9 (by decide)]) (by rw [hk3.get 22 (by decide)])
    (by rw [hk3.get 24 (by decide), hf]; exact ev.s8) (by rw [hf]; exact ev.tdLt)
    ⟨by rw [hk3.get 18 (by decide)]; exact ev.cs.s2, by rw [hk3.get 19 (by decide)]; exact ev.cs.s3,
      by rw [hk3.get 20 (by decide)]; exact ev.cs.s4, by rw [hk3.get 21 (by decide)]; exact ev.cs.s5⟩
    (by rw [hk3.get 2 (by decide)]) (hk3.mono (by decide)) ev.sb ev.srt
  exact ⟨o', by simpa using ev'⟩

/-- **`dc_pop` before the byte at `j`** (`0x800017d8`): an empty stack to the
loop head, a number pushed back, a string the nested evaluation. -/
theorem tos_mid (hlive : ∀ p ∈ dcText, live p.1)
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o)
    (h25 : R 25 = BitVec.ofNat 64 (sp - 176 + 32)) (hoom : EvOom live S Q sp W q M0)
    {j : Nat} (hj : j < o.s.length) (hdj : o.s.drop j = skipWs rest)
    {R2 : Nat → BitVec 64} (k2 : Keeps (23 :: skipClob) R2 R)
    (h8 : R2 8 = BitVec.ofNat 64 (o.tb.pay + j))
    (hplain : (∀ x more, st.stack ≠ .str x :: more) →
      EvHeadK live S Q t0 sp W d k k q M0 R0 G hs xs st ⟨skipWs rest, td, false⟩ ∧
      EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st ⟨skipWs rest, td, false⟩)
    (hnest : ∀ x more, st.stack = .str x :: more → skipWs rest ≠ [] →
      TosNestK live S Q t0 sp W d k q M0 R0 F L C G hs xs { st with stack := more } rest td) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800017d8#64 R2 M := by
  have hstk := ev.stk; have hab := ev.room
  have hfr := ev.frame
  have hfl := hfr.lo; have hfh := hfr.hi; have hfa := hfr.al
  have hne : skipWs rest ≠ [] := by
    intro h; rw [h] at hdj; have := congrArg List.length hdj; simp at this; omega
  have e2 : R2 2 = BitVec.ofNat 64 (sp - 176) := by rw [k2.get 2 (by decide)]; exact ev.r2
  have e25 : R2 25 = BitVec.ofNat 64 (sp - 176 + 32) := by rw [k2.get 25 (by decide)]; exact h25
  refine rt_pop_mid hlive ev.dc (hfr.within (m := 176) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd] at hab ⊢; omega)
    ⟨fun i hi => hfr.own _ (by omega) (by omega), by omega, by omega, by omega⟩ e2 e25
    (fun R3 M3 H3 G3 g v st3 hst hG k3 h3 hd3 hpo => ?_) (fun hemp R3 M3 k3 h12 h3 hpo => ?_)
  · obtain ⟨c, hG⟩ := hG
    have hk3 : Keeps (1 :: 8 :: 23 :: cClob) R3 R :=
      by keeps_tac ((k3.mono (by decide)).trans (k2.mono (by decide)))
    have e8 : R3 8 = BitVec.ofNat 64 (o.tb.pay + j) := by rw [k3.get 8 (by decide)]; exact h8
    cases v with
    | num x =>
      obtain ⟨hhead, hend⟩ := hplain fun x' more e => by
        have := (push_with hst e).2; cases this
      exact tos_num hlive ev hoom (Nat.le_of_lt hj) hdj hst hG hk3 e8 h3 hd3 hpo rfl hhead hend
    | str x =>
      have hs0 : st.stack = .str x :: st3.stack := by rw [hst]; rfl
      have hn := hnest x st3.stack hs0 hne
      rw [(push_with hst hs0).1] at hn
      exact tos_call hlive ev h25 hoom hj hdj hst hG hk3 e8 h3 hd3 hpo rfl hn
  · obtain ⟨hhead, -⟩ := hplain fun x more e => by rw [hemp] at e; cases e
    obtain ⟨o', ev'⟩ := ev.afterPop (Nat.le_of_lt hj) (f' := ⟨skipWs rest, td, false⟩) hdj rfl
      (by keeps_tac ((k3.mono (by decide)).trans (k2.mono (by decide))))
      (by rw [k3.get 8 (by decide)]; exact h8) h3 hpo
    exact hhead R3 M3 H F L C G xs o' ev' h12 hne (by omega) (StrPin.refl _ _)

/-- **`dc_pop` at the text's end** (`0x8000179c`): an empty stack to the
loop's exit, a number pushed back, a string the tail call. -/
theorem tos_end (hlive : ∀ p ∈ dcText, live p.1)
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o)
    (h25 : R 25 = BitVec.ofNat 64 (sp - 176 + 32)) (hoom : EvOom live S Q sp W q M0)
    (hdj : o.s.drop o.s.length = skipWs rest)
    {R2 : Nat → BitVec 64} (k2 : Keeps (23 :: skipClob) R2 R)
    (h8 : R2 8 = BitVec.ofNat 64 (o.tb.pay + o.s.length))
    (hplain : (∀ x more, st.stack ≠ .str x :: more) →
      EvHeadK live S Q t0 sp W d k k q M0 R0 G hs xs st ⟨skipWs rest, td, false⟩ ∧
      EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st ⟨skipWs rest, td, false⟩)
    (htail : ∀ x more p', st.stack = .str x :: more → skipWs rest = [] → td + 1 < 2 ^ 31 ∧
      EvHeadK live S Q t0 sp W d k k q M0 R0 G (.str p' :: hs.tail) xs { st with stack := more }
        ⟨x, td + 1, false⟩ ∧
      EvEndK live S Q t0 sp W d k q M0 R0 G (.str p' :: hs.tail) xs { st with stack := more }
        ⟨x, td + 1, false⟩) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x8000179c#64 R2 M := by
  have hstk := ev.stk; have hab := ev.room
  have hfr := ev.frame
  have hfl := hfr.lo; have hfh := hfr.hi; have hfa := hfr.al
  have hnil : skipWs rest = [] := by rw [← hdj]; simp
  have e2 : R2 2 = BitVec.ofNat 64 (sp - 176) := by rw [k2.get 2 (by decide)]; exact ev.r2
  have e25 : R2 25 = BitVec.ofNat 64 (sp - 176 + 32) := by rw [k2.get 25 (by decide)]; exact h25
  refine rt_pop_end hlive ev.dc (hfr.within (m := 176) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd] at hab ⊢; omega)
    ⟨fun i hi => hfr.own _ (by omega) (by omega), by omega, by omega, by omega⟩ e2 e25
    (fun R3 M3 H3 G3 g v st3 hst hG k3 h3 hd3 hpo => ?_) (fun hemp R3 M3 k3 h3 hpo => ?_)
  · obtain ⟨c, hG⟩ := hG
    have hk3 : Keeps (1 :: 8 :: 23 :: cClob) R3 R :=
      by keeps_tac ((k3.mono (by decide)).trans (k2.mono (by decide)))
    have e8 : R3 8 = BitVec.ofNat 64 (o.tb.pay + o.s.length) := by
      rw [k3.get 8 (by decide)]; exact h8
    cases v with
    | num x =>
      obtain ⟨hhead, hend⟩ := hplain fun x' more e => by
        have := (push_with hst e).2; cases this
      exact tos_num hlive ev hoom (Nat.le_refl _) hdj hst hG hk3 e8 h3 hd3 hpo rfl hhead hend
    | str x =>
      have hs0 : st.stack = .str x :: st3.stack := by rw [hst]; rfl
      refine tos_tail hlive ev hst hG hk3 e8 h3 hd3 hpo rfl fun p' _ => ?_
      have ht := htail x st3.stack p' hs0 hnil
      rw [(push_with hst hs0).1] at ht
      exact ht
  · obtain ⟨-, hend⟩ := hplain fun x more e => by rw [hemp] at e; cases e
    obtain ⟨o', ev'⟩ := ev.afterPop (Nat.le_refl _) (f' := ⟨skipWs rest, td, false⟩) hdj rfl
      (by keeps_tac ((k3.mono (by decide)).trans (k2.mono (by decide))))
      (by rw [k3.get 8 (by decide)]; exact h8) h3 hpo
    exact hend hnil _ R3 M3 H F L C G xs _ o' ev' (by omega) (StrPin.refl _ _)

/-- **The `DC_EVALTOS` code** (`0x80001748`), continuation-generic. -/
theorem ev_tos_k (hlive : ∀ p ∈ dcText, live p.1)
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o)
    (h25 : R 25 = BitVec.ofNat 64 (sp - 176 + 32)) (hoom : EvOom live S Q sp W q M0)
    (hplain : (∀ x more, st.stack ≠ .str x :: more) →
      EvHeadK live S Q t0 sp W d k k q M0 R0 G hs xs st ⟨skipWs rest, td, false⟩ ∧
      EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st ⟨skipWs rest, td, false⟩)
    (htail : ∀ x more p', st.stack = .str x :: more → skipWs rest = [] → td + 1 < 2 ^ 31 ∧
      EvHeadK live S Q t0 sp W d k k q M0 R0 G (.str p' :: hs.tail) xs { st with stack := more }
        ⟨x, td + 1, false⟩ ∧
      EvEndK live S Q t0 sp W d k q M0 R0 G (.str p' :: hs.tail) xs { st with stack := more }
        ⟨x, td + 1, false⟩)
    (hnest : ∀ x more, st.stack = .str x :: more → skipWs rest ≠ [] →
      TosNestK live S Q t0 sp W d k q M0 R0 F L C G hs xs { st with stack := more } rest td) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001748#64 R M := by
  obtain ⟨i, hi, hdrop, h8⟩ := ev.pos
  simp only at hdrop
  have hso := ev.dc.view.strs o ev.strIn
  have hmem : o.tb ∈ G.blocks :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ev.strIn, by simp⟩))
  have bt := blk_bounds ev.dc.heap.heap (ev.dc.heap.raw.live o.tb hmem)
  have htz := hso.tsz
  have hS : HeapOwn S := fun a e1 e2 => ev.dc.heap.heap.own a e1 e2
  simp only [heapStart, heapEnd] at bt
  refine tos_skip hlive hS rfl hi (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
    (fun j hj => hso.lbu hj) (fun j hj => (hso.img hj).1) hso.byte h8 ev.s1
    (fun R2 k2 hw e8 => ?_) (fun R2 k2 hw e8 => ?_)
  · rw [hdrop] at hw
    exact tos_end hlive ev h25 hoom (by rw [hw]; simp) k2 e8 hplain htail
  · rw [hdrop] at hw e8
    have hlen : rest.length = o.s.length - i := by rw [← hdrop, List.length_drop]
    have hle := skipWs_length_le rest.length rest (Nat.le_refl _)
    have hpos : 0 < (skipWs rest).length := List.length_pos_iff.mpr hw
    have e := skipWs_drop rest.length rest (Nat.le_refl _)
    generalize hk0 : rest.length - (skipWs rest).length = k0 at e
    have hdj : o.s.drop (o.s.length - (skipWs rest).length) = skipWs rest := by
      calc o.s.drop (o.s.length - (skipWs rest).length) = (o.s.drop i).drop k0 := by
            simp only [List.drop_drop]; congr 1; omega
        _ = rest.drop k0 := by rw [hdrop]
        _ = skipWs rest := e.symm
    exact tos_mid hlive ev h25 hoom (by omega) hdj k2
      (by rw [e8]; congr 1; omega) hplain hnest

end

end Dc.Mach
