import Dc.Machine

/-!
# Model facts for `evalstr`'s number and string reads (M10)

`readNum_takeNul`: `readNum` reads no NUL, so it agrees with its read of the
bytes up to the first NUL (`dc_getnum`'s input, `rdW`). `scanStr_split`:
`scanStr`'s contents are a prefix and its rest a suffix of the input.
-/

namespace Dc

/-- A suffix that stops a number read: empty or a NUL first. -/
def NulStop (t : List Nat) : Prop := ∀ c, t.head? = some c → c = 0

theorem takeDigits_append {t : List Nat} (ht : NulStop t) : ∀ w : List Nat,
    takeDigits (w ++ t) = ((takeDigits w).1, (takeDigits w).2 ++ t)
  | [] => by
    cases t with
    | nil => rfl
    | cons c cs =>
      have := ht c rfl; subst this
      simp [takeDigits, digitVal]
  | c :: cs => by
    simp only [List.cons_append, takeDigits]
    cases digitVal c with
    | none => rfl
    | some d => simp [takeDigits_append ht cs]

theorem dropSpace_append {t : List Nat} (ht : NulStop t) : ∀ w : List Nat,
    (w ++ t).dropWhile isSpace = w.dropWhile isSpace ++ t
  | [] => by
    cases t with
    | nil => rfl
    | cons c cs =>
      have := ht c rfl; subst this
      simp [List.dropWhile, isSpace]
  | c :: cs => by
    simp only [List.cons_append, List.dropWhile]
    cases isSpace c with
    | true => exact dropSpace_append ht cs
    | false => rfl

/-- `readNum` after the sign. -/
def rdTail (ib : Nat) (neg : Bool) (s : List Nat) : Num × List Nat :=
  let (ids, s) := takeDigits s
  let ip : Num := ⟨false, ofDigits ib ids, 0⟩
  let (n, s) := match s with
    | 46 :: rest =>
      let (fds, s') := takeDigits rest
      let dec := fds.length
      let build : Num := ⟨false, ofDigits ib fds, 0⟩
      let frac := (Num.div build ⟨false, ib ^ dec, 0⟩ dec).getD (Num.zero dec)
      (Num.add ip frac 0, s')
    | _ => (ip, s)
  ((if neg then Num.sub (Num.zero 0) n 0 else n), s)

theorem readNum_sign (ib : Nat) (rest : List Nat) :
    readNum ib (95 :: rest) = rdTail ib true (rest.dropWhile isSpace) := rfl

theorem readNum_nosign (ib : Nat) (s : List Nat) (h : s.head? ≠ some 95) :
    readNum ib s = rdTail ib false s := by
  cases s with
  | nil => rfl
  | cons c cs =>
    by_cases hc : c = 95
    · subst hc; exact absurd rfl h
    · unfold readNum rdTail; split <;> simp_all <;> exact ⟨rfl, rfl⟩

theorem rdTail_append (ib : Nat) (neg : Bool) {t : List Nat} (ht : NulStop t) (w : List Nat) :
    rdTail ib neg (w ++ t) = ((rdTail ib neg w).1, (rdTail ib neg w).2 ++ t) := by
  unfold rdTail
  rw [takeDigits_append ht]
  generalize takeDigits w = p
  obtain ⟨ds, s2⟩ := p
  dsimp only
  rcases s2 with _ | ⟨c, r⟩
  · rcases t with _ | ⟨c, cs⟩
    · rfl
    · have := ht c rfl; subst this; rfl
  · by_cases hc : c = 46
    · subst hc; simp only [List.cons_append, takeDigits_append ht]
    · simp only [List.cons_append]
      (repeat' split) <;> simp_all

theorem readNum_append (ib : Nat) {t : List Nat} (ht : NulStop t) (w : List Nat) :
    readNum ib (w ++ t) = ((readNum ib w).1, (readNum ib w).2 ++ t) := by
  rcases w with _ | ⟨c, cs⟩
  · rcases t with _ | ⟨c, cs⟩
    · rfl
    · have := ht c rfl; subst this
      rw [List.nil_append, readNum_nosign ib _ (by simp), readNum_nosign ib [] (by simp)]
      exact rdTail_append ib false (t := 0 :: cs) ht []
  · by_cases hc : c = 95
    · subst hc
      rw [List.cons_append, readNum_sign, readNum_sign, dropSpace_append ht, rdTail_append ib true ht]
    · rw [List.cons_append, readNum_nosign ib _ (by simpa using hc), readNum_nosign ib _ (by simpa using hc)]
      exact rdTail_append ib false ht (c :: cs)

theorem nulStop_dropWhile (l : List Nat) : NulStop (l.dropWhile (· ≠ 0)) := by
  intro c hc
  induction l with
  | nil => simp at hc
  | cons x xs ih =>
    by_cases hx : x = 0
    · subst hx; simp at hc; omega
    · simp only [List.dropWhile, ne_eq, hx, not_false_eq_true, decide_true] at hc
      exact ih hc

/-- **`readNum` reads no NUL**: on the bytes up to the first NUL. -/
theorem readNum_takeNul (ib : Nat) (l : List Nat) :
    readNum ib l = ((readNum ib (l.takeWhile (· ≠ 0))).1,
      (readNum ib (l.takeWhile (· ≠ 0))).2 ++ l.dropWhile (· ≠ 0)) := by
  conv => lhs; rw [← List.takeWhile_append_dropWhile (p := fun x => decide (x ≠ 0)) (l := l)]
  exact readNum_append ib (nulStop_dropWhile l) _

/-- `scanStr`'s contents are a prefix and its rest a suffix of the input. -/
theorem scanStr_split : ∀ (d : Nat) (l : List Nat),
    (scanStr d l).1 = l.take (scanStr d l).1.length ∧
    (scanStr d l).2 = l.drop (l.length - (scanStr d l).2.length) ∧
    (scanStr d l).1.length + (scanStr d l).2.length ≤ l.length
  | _, [] => by simp [scanStr]
  | d, c :: cs => by
    rw [scanStr.eq_2]
    have h1 := scanStr_split (d - 1) cs
    have h2 := scanStr_split (d + 1) cs
    have h3 := scanStr_split d cs
    split
    · split
      · simp
      · obtain ⟨a1, a2, a3⟩ := h1
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.length_cons, List.take_succ_cons]; exact congrArg _ a1
        · simp only [List.length_cons]
          rw [show cs.length + 1 - (scanStr (d - 1) cs).2.length =
            (cs.length - (scanStr (d - 1) cs).2.length) + 1 by omega, List.drop_succ_cons]
          exact a2
        · simp only [List.length_cons]; omega
    · split
      · obtain ⟨a1, a2, a3⟩ := h2
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.length_cons, List.take_succ_cons]; exact congrArg _ a1
        · simp only [List.length_cons]
          rw [show cs.length + 1 - (scanStr (d + 1) cs).2.length =
            (cs.length - (scanStr (d + 1) cs).2.length) + 1 by omega, List.drop_succ_cons]
          exact a2
        · simp only [List.length_cons]; omega
      · obtain ⟨a1, a2, a3⟩ := h3
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.length_cons, List.take_succ_cons]; exact congrArg _ a1
        · simp only [List.length_cons]
          rw [show cs.length + 1 - (scanStr d cs).2.length =
            (cs.length - (scanStr d cs).2.length) + 1 by omega, List.drop_succ_cons]
          exact a2
        · simp only [List.length_cons]; omega

end Dc
