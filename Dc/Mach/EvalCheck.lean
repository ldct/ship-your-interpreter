import Dc.Mach.EvalStable

/-!
# Deciding `DcAdmissible`'s per-call premise

`fnSizeB`: `FnSize` as a `Bool` (`fnSizeB_sound`). `allCallsB`: `AllCalls`
for a `Bool` predicate, computed (`allCallsB_sound`), so a terminating
program's `size` premise is one evaluation by the kernel (`size_of_run`).
-/

namespace Dc.Mach

open Dc

/-- `FnSize` as a `Bool`. -/
def fnSizeB (st : St) (c : Nat) : Bool :=
  (c != 102 || st.stack.all (fun v => match v with | .num n => decide (n.wid < 2 ^ 20) | _ => true)) &&
  (match st.stack with
    | .num n :: _ => (!(c == 110 || c == 112 || c == 80) || decide (n.wid < 2 ^ 20)) &&
      (c != 118 || decide (n.wid + st.scale < 2 ^ 20))
    | _ => true) &&
  (match st.stack with
    | .num b :: .num a :: _ =>
      (c != 47 || decide (a.wid + st.scale + b.wid < 2 ^ 27)) &&
      (!(c == 37 || c == 126) || decide (a.wid + st.scale + b.wid < 2 ^ 24)) &&
      (c != 94 || decide ((b.toLong.natAbs + 1) * (a.wid + 1) + st.scale < 2 ^ 24))
    | _ => true) &&
  (match st.stack with
    | .num c' :: .num b :: .num a :: _ =>
      c != 124 || decide (8 * (a.wid + c'.wid + st.scale + 1) + b.wid < 2 ^ 24)
    | _ => true)

theorem fnSizeB_sound {st : St} {c : Nat} (h : fnSizeB st c = true) : FnSize st c := by
  unfold fnSizeB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hall, h1⟩, h2⟩, h3⟩ := h
  refine ⟨fun hc v hv n e => ?_, fun hc n rest e => ?_, fun hc b a rest e => ?_, fun hc b a rest e => ?_,
    fun hc b a rest e => ?_, fun hc c' b a rest e => ?_, fun hc n rest e => ?_⟩
  · rcases hall with h0 | h0
    · exact absurd hc h0
    · have := h0 v hv; subst e; simpa using this
  all_goals first
    | (rw [e] at h1; simp at h1; omega)
    | (rw [e] at h2; simp at h2; omega)
    | (rw [e] at h3; simp at h3; omega)

mutual

/-- `AllCalls` for a `Bool` predicate, computed. -/
def allCallsB (lm : Nat) (P : St → Nat → Bool) : Nat → St → Frame → Bool
  | 0, _, _ => true
  | _ + 1, _, ⟨[], _, _⟩ => true
  | fuel + 1, st, ⟨c :: rest, td, neg⟩ =>
    P st c &&
    match dcFunc lm st c rest.head? neg with
    | .ok st' => allCallsB lm P fuel st' ⟨rest, td, false⟩
    | .eatOne st' => allCallsB lm P fuel st' ⟨rest.tail, td, false⟩
    | .evalReg st' reg =>
      match regGet st' reg with
      | some v => tosCallsB lm P fuel (st'.push v) rest.tail td
      | none => allCallsB lm P fuel st' ⟨rest.tail, td, false⟩
    | .evalTos st' => tosCallsB lm P fuel st' rest td
    | .quit st' =>
      if td ≤ st'.unwind then true else allCallsB lm P fuel st' ⟨rest, td - st'.unwind, false⟩
    | .int =>
      allCallsB lm P fuel (st.push (.num (readNum st.ibase (c :: rest)).1))
        ⟨(readNum st.ibase (c :: rest)).2, td, false⟩
    | .str => allCallsB lm P fuel (st.push (.str (scanStr 1 rest).1)) ⟨(scanStr 1 rest).2, td, false⟩
    | .comment => allCallsB lm P fuel st ⟨skipEol rest, td, false⟩
    | .negcmp => allCallsB lm P fuel st ⟨rest, td, true⟩
    | .eofError => true
    | .sqrt st' x =>
      match Num.sqrtLoopFuel x (max st'.scale x.scale) fuel (Num.sqrtInit x).1 (Num.sqrtInit x).2 with
      | some y => allCallsB lm P fuel (st'.push (.num y)) ⟨rest, td, false⟩
      | none => true
    | .system => allCallsB lm P fuel st ⟨skipSys rest, td, false⟩

/-- `TosCalls` for a `Bool` predicate, computed. -/
def tosCallsB (lm : Nat) (P : St → Nat → Bool) : Nat → St → List Nat → Nat → Bool
  | 0, _, _, _ => true
  | fuel + 1, st, rest, td =>
    match st.stack with
    | [] => allCallsB lm P fuel st ⟨skipWs rest, td, false⟩
    | .num _ :: _ => allCallsB lm P fuel st ⟨skipWs rest, td, false⟩
    | .str x :: more =>
      if skipWs rest = [] then allCallsB lm P fuel { st with stack := more } ⟨x, td + 1, false⟩
      else
        allCallsB lm P fuel { st with stack := more } ⟨x, 1, false⟩ &&
        match run lm fuel { st with stack := more } ⟨x, 1, false⟩ with
        | some (st', .ok) => allCallsB lm P fuel st' ⟨skipWs rest, td, false⟩
        | _ => true

end

theorem allCallsB_sound (lm : Nat) (P : St → Nat → Bool) (Q : St → Nat → Prop)
    (hP : ∀ st c, P st c = true → Q st c) :
    ∀ n,
    (∀ st f, allCallsB lm P n st f = true → AllCalls lm (fun st c _ => Q st c) n st f) ∧
    (∀ st rest td, tosCallsB lm P n st rest td = true →
      TosCalls lm (fun st c _ => Q st c) n st rest td) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ => by simp [AllCalls], fun _ _ _ _ => by simp [TosCalls]⟩
  | succ n ih =>
    obtain ⟨ihr, iht⟩ := ih
    constructor
    · rintro st ⟨s, td, neg⟩ h
      cases s with
      | nil => simp [AllCalls]
      | cons c rest =>
        simp only [allCallsB, Bool.and_eq_true] at h
        simp only [AllCalls]
        refine ⟨hP _ _ h.1, ?_⟩
        have h2 := h.2
        generalize dcFunc lm st c rest.head? neg = d at h2 ⊢
        cases d <;> simp only at h2 ⊢
        all_goals first
          | exact ihr _ _ h2
          | exact iht _ _ _ h2
          | trivial
          | (split <;> simp_all)
    · intro st rest td h
      simp only [tosCallsB] at h
      simp only [TosCalls]
      cases hs : st.stack with
      | nil => simp only [hs] at h ⊢; exact ihr _ _ h
      | cons v more =>
        cases v with
        | num _ => simp only [hs] at h ⊢; exact ihr _ _ h
        | str y =>
          simp only [hs] at h ⊢
          split
          · rename_i he; simp only [he, ite_true] at h; exact ihr _ _ h
          · rename_i he
            simp only [he, ite_false, Bool.and_eq_true] at h
            refine ⟨ihr _ _ h.1, ?_⟩
            have h2 := h.2
            split
            · rename_i st' heq; rw [heq] at h2; exact ihr _ _ h2
            · trivial

/-- **The size premise of a terminating program**, from one computation. -/
theorem size_of_run {lm N : Nat} {prog : List Nat} {x : St × Status}
    (h : run lm N St.init ⟨prog, 1, false⟩ = some x)
    (hb : allCallsB lm fnSizeB N St.init ⟨prog, 1, false⟩ = true) :
    ∀ n, AllCalls lm (fun st c' _ => CallP st c') n St.init ⟨prog, 1, false⟩ :=
  allCalls_of_run h ((allCallsB_sound lm fnSizeB CallP (fun _ _ e => fnSizeB_sound e) N).1 _ _ hb)

end Dc.Mach
