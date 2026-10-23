import Dc.Mach.EvalTos5
import Dc.Mach.EvalNum

/-!
# The model invariants along an evaluation (M10)

`run_inv`/`tos_inv`: an evaluation (`run`, `tos`) from a state with
`StrBound (2 ^ 24)` and `ArrSorted` and a frame text shorter than `2 ^ 24`
ends in a state with both.
-/

namespace Dc

theorem takeDigits_rest_len : ∀ l : List Nat, (takeDigits l).2.length ≤ l.length
  | [] => Nat.le_refl _
  | c :: cs => by
    unfold takeDigits
    cases digitVal c with
    | none => exact Nat.le_refl _
    | some _ => have := takeDigits_rest_len cs; simp; omega

theorem rdTail_len (ib : Nat) (neg : Bool) (s : List Nat) : (rdTail ib neg s).2.length ≤ s.length := by
  unfold rdTail
  have h1 := takeDigits_rest_len s
  generalize takeDigits s = p at h1
  obtain ⟨ds, s2⟩ := p
  dsimp only at h1 ⊢
  rcases s2 with _ | ⟨c, r⟩
  · simp
  · have := takeDigits_rest_len r
    simp only [List.length_cons] at h1
    (repeat' split) <;> simp_all <;> omega

theorem dropWhile_len {p : Nat → Bool} : ∀ l : List Nat, (l.dropWhile p).length ≤ l.length
  | [] => Nat.le_refl _
  | c :: cs => by
    simp only [List.dropWhile]
    cases p c with
    | true => have := dropWhile_len (p := p) cs; simp; omega
    | false => exact Nat.le_refl _

theorem readNum_len (ib : Nat) (s : List Nat) : (readNum ib s).2.length ≤ s.length := by
  rcases s with _ | ⟨c, cs⟩
  · rw [readNum_nosign ib [] (by simp)]; exact rdTail_len ib false []
  · by_cases hc : c = 95
    · subst hc
      rw [readNum_sign]
      have := rdTail_len ib true (cs.dropWhile isSpace)
      have h2 : (cs.dropWhile isSpace).length ≤ cs.length := dropWhile_len cs
      simp only [List.length_cons]; omega
    · rw [readNum_nosign ib _ (by simpa using hc)]; exact rdTail_len ib false _

end Dc

namespace Dc.Mach

open Dc

/-- The invariants of a state and a frame text. -/
abbrev Inv (st : St) (s : List Nat) : Prop :=
  StrBound (2 ^ 24) st ∧ ArrSorted st ∧ s.length < 2 ^ 24

theorem inv_step :
    ∀ n, (∀ st f st' r, Dc.run 70 n st f = some (st', r) → Inv st f.s →
        StrBound (2 ^ 24) st' ∧ ArrSorted st') ∧
      (∀ st rest td st' r, Dc.tos 70 n st rest td = some (st', r) → Inv st rest →
        StrBound (2 ^ 24) st' ∧ ArrSorted st') := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ _ h => by simp [Dc.run] at h, fun _ _ _ _ _ h => by simp [Dc.tos] at h⟩
  | succ n ih =>
    obtain ⟨ihr, iht⟩ := ih
    refine ⟨fun st f st' r h hi => ?_, fun st rest td st' r h hi => ?_⟩
    · obtain ⟨s, td, neg⟩ := f
      obtain ⟨hsb, hsrt, hlen⟩ := hi
      cases s with
      | nil => simp [Dc.run] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hsb, hsrt⟩
      | cons c rest =>
        simp only [List.length_cons] at hlen
        have h1 := dcFunc_strBound (lm := 70) (c := c) (peek := rest.head?) (neg := neg) hsb (by decide)
        have h2 := dcFunc_arrSorted (lm := 70) (c := c) (peek := rest.head?) (neg := neg) hsrt
        unfold Dc.run at h
        revert h1 h2 h
        cases dcFunc 70 st c rest.head? neg with
        | ok s => intro h1 h2 h; exact ihr _ _ _ _ h ⟨h1, h2, by simp; omega⟩
        | eatOne s => intro h1 h2 h; exact ihr _ _ _ _ h ⟨h1, h2, by simp; omega⟩
        | evalReg s reg =>
          intro h1 h2 h
          simp only at h
          revert h
          cases hg : regGet s reg with
          | none => intro h; exact ihr _ _ _ _ h ⟨h1, h2, by simp; omega⟩
          | some v =>
            intro h
            exact iht _ _ _ _ _ h ⟨h1.push (h1.regGet hg), h2.stack _, by simp; omega⟩
        | evalTos s => intro h1 h2 h; exact iht _ _ _ _ _ h ⟨h1, h2, by omega⟩
        | quit s =>
          intro h1 h2 h
          simp only at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨h1.stk rfl fun v hv => h1.vb v hv, h2.regs rfl⟩
          · exact ihr _ _ _ _ h ⟨h1, h2, by simp; omega⟩
        | int =>
          intro _ _ h
          exact ihr _ _ _ _ h ⟨hsb.push (VB.num _ _), hsrt.stack _, by
            have := readNum_len st.ibase (c :: rest); simp at this ⊢; omega⟩
        | str =>
          intro _ _ h
          have hs := scanStr_split 1 rest
          exact ihr _ _ _ _ h ⟨hsb.scan (by omega), hsrt.stack _, by simp; omega⟩
        | comment =>
          intro _ _ h
          exact ihr _ _ _ _ h ⟨hsb, hsrt, by have := skipEol_length_le rest; simp; omega⟩
        | negcmp => intro _ _ h; exact ihr _ _ _ _ h ⟨hsb, hsrt, by simp; omega⟩
        | eofError =>
          intro _ _ h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hsb, hsrt⟩
        | sqrt s x =>
          intro h1 h2 h
          simp only at h
          split at h
          · exact ihr _ _ _ _ h ⟨h1.push (VB.num _ _), h2.stack _, by simp; omega⟩
          · cases h
        | system =>
          intro _ _ h
          exact ihr _ _ _ _ h ⟨hsb, hsrt, by have := skipSys_length_le rest; simp; omega⟩
    · obtain ⟨hsb, hsrt, hlen⟩ := hi
      have hws := skipWs_length_le rest.length rest (Nat.le_refl _)
      unfold Dc.tos at h
      revert h
      cases hs : st.stack with
      | nil => intro h; exact ihr _ _ _ _ h ⟨hsb, hsrt, by simp; omega⟩
      | cons v more =>
        cases v with
        | num x => intro h; exact ihr _ _ _ _ h ⟨hsb, hsrt, by simp; omega⟩
        | str x =>
          intro h
          have hx := hsb.top hs
          have hx' : x.length < 2 ^ 24 := hx x (by simp [Val.strs])
          have hsb' := hsb.pop hs
          have hsrt' := hsrt.stack more
          simp only at h
          split at h
          · exact ihr _ _ _ _ h ⟨hsb', hsrt', hx'⟩
          · revert h
            cases hr : Dc.run 70 n { st with stack := more } ⟨x, 1, false⟩ with
            | none => intro h; cases h
            | some p =>
              obtain ⟨st1, r1⟩ := p
              have hi1 := ihr _ _ _ _ hr ⟨hsb', hsrt', hx'⟩
              cases r1 with
              | ok => intro h; exact ihr _ _ _ _ h ⟨hi1.1, hi1.2, by simp; omega⟩
              | quit =>
                intro h
                simp only at h
                split at h
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ⟨hi1.1.stk rfl fun v hv => hi1.1.vb v hv, hi1.2.regs rfl⟩
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact hi1

end Dc.Mach
