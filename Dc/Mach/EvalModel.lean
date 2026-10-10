import Dc.Mach.EvalLeak

/-!
# Model lemmas for `evalstr` (M10)

`StrBound` is preserved by `dcFunc` (`dcFunc_strBound`): its results' states
hold only strings the state held before, the one-character string of `a`
and the empty string of `?`.
-/

namespace Dc

/-- A value's strings are shorter than `N`. -/
def VB (N : Nat) (v : Val) : Prop := ∀ s ∈ v.strs, s.length < N

/-- A register level's strings are shorter than `N`. -/
def EB (N : Nat) (e : Entry) : Prop := (∀ v, e.val = some v → VB N v) ∧ ∀ iv ∈ e.arr, VB N iv.2

theorem StrBound.mk' {N : Nat} {st : St} (hs : ∀ v ∈ st.stack, VB N v)
    (hr : ∀ r, ∀ e ∈ st.regs r, EB N e) : StrBound N st :=
  ⟨hs, fun r e he => hr r e he⟩

theorem StrBound.vb {N : Nat} {st : St} (h : StrBound N st) : ∀ v ∈ st.stack, VB N v := h.stack

theorem StrBound.eb {N : Nat} {st : St} (h : StrBound N st) : ∀ r, ∀ e ∈ st.regs r, EB N e :=
  fun r e he => h.regs r e he

theorem VB.num (N : Nat) (n : Num) : VB N (.num n) := fun s hs => by simp [Val.strs] at hs

/-- A state with the same registers whose stack values are bounded. -/
theorem StrBound.stk {N : Nat} {st st' : St} (h : StrBound N st) (hr : st'.regs = st.regs)
    (hs : ∀ v ∈ st'.stack, VB N v) : StrBound N st' :=
  .mk' hs fun r e he => h.eb r e (by rw [← hr]; exact he)

/-- The result's state, if any. -/
def ResOK (N : Nat) : Res → Prop
  | .ok s | .eatOne s | .evalReg s _ | .evalTos s | .quit s | .sqrt s _ => StrBound N s
  | _ => True

section
variable {N : Nat} {st : St}

theorem StrBound.push (h : StrBound N st) {v : Val} (hv : VB N v) : StrBound N (st.push v) :=
  h.stk rfl fun w hw => by
    simp only [St.push, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hv
    · exact h.vb w hw

theorem StrBound.pop (h : StrBound N st) {v : Val} {rest : List Val} (e : st.stack = v :: rest) :
    StrBound N { st with stack := rest } :=
  h.stk rfl fun w hw => h.vb w (by rw [e]; exact List.mem_cons_of_mem _ hw)

theorem StrBound.top (h : StrBound N st) {v : Val} {rest : List Val} (e : st.stack = v :: rest) :
    VB N v := h.vb v (by rw [e]; exact List.mem_cons_self)

theorem StrBound.emit (h : StrBound N st) (bs : List Nat) : StrBound N (st.emit bs) :=
  h.stk rfl fun w hw => h.vb w hw

theorem StrBound.setReg (h : StrBound N st) {r : Nat} {l : List Entry} (hl : ∀ e ∈ l, EB N e) :
    StrBound N (st.setReg r l) :=
  .mk' (fun w hw => h.vb w hw) fun q e he => by
    simp only [St.setReg] at he
    split at he
    · exact hl e he
    · exact h.eb q e he

theorem StrBound.regSet (h : StrBound N st) {r : Nat} {v : Val} (hv : VB N v) :
    StrBound N (regSet st r v) := by
  unfold Dc.regSet
  split
  · exact h.setReg fun e he => by
      simp at he; subst he; exact ⟨fun w hw => (by cases hw; exact hv), fun iv hiv => by simp at hiv⟩
  · rename_i e es he
    exact h.setReg fun e' he' => by
      simp only [List.mem_cons] at he'
      have hb := h.eb r
      rw [he] at hb
      rcases he' with rfl | he'
      · exact ⟨fun w hw => (by cases hw; exact hv), (hb e List.mem_cons_self).2⟩
      · exact hb e' (List.mem_cons_of_mem _ he')

theorem arrSet_vb {i : Nat} {v : Val} (hv : VB N v) :
    ∀ (arr : List (Nat × Val)), (∀ iv ∈ arr, VB N iv.2) → ∀ iv ∈ arrSet i v arr, VB N iv.2
  | [], _ => by simp [arrSet]; exact hv
  | (j, w) :: rest, ha => by
    unfold arrSet
    split
    · intro iv hiv
      simp only [List.mem_cons] at hiv
      rcases hiv with rfl | hiv
      · exact ha _ List.mem_cons_self
      · exact arrSet_vb hv rest (fun x hx => ha x (List.mem_cons_of_mem _ hx)) iv hiv
    · split
      · intro iv hiv
        simp only [List.mem_cons] at hiv
        rcases hiv with rfl | hiv
        · exact hv
        · exact ha iv (List.mem_cons_of_mem _ hiv)
      · intro iv hiv
        simp only [List.mem_cons] at hiv
        rcases hiv with rfl | hiv
        · exact hv
        · exact ha iv (List.mem_cons.mpr hiv)

theorem StrBound.arraySet (h : StrBound N st) {r i : Nat} {v : Val} (hv : VB N v) :
    StrBound N (arraySet st r i v) := by
  unfold Dc.arraySet
  split
  · exact h.setReg fun e he => by
      simp at he; subst he
      exact ⟨fun w hw => (by simp at hw), fun iv hiv => by simp at hiv; subst hiv; exact hv⟩
  · rename_i e es he
    exact h.setReg fun e' he' => by
      simp only [List.mem_cons] at he'
      have hb := h.eb r
      rw [he] at hb
      rcases he' with rfl | he'
      · exact ⟨(hb e List.mem_cons_self).1,
          arrSet_vb hv _ (hb e List.mem_cons_self).2⟩
      · exact hb e' (List.mem_cons_of_mem _ he')

theorem StrBound.arrayGet (h : StrBound N st) (r i : Nat) : VB N (arrayGet st r i) := by
  unfold Dc.arrayGet
  dsimp only
  split
  · rename_i iv v hf
    have hm := List.mem_of_find?_eq_some hf
    split at hm
    · simp at hm
    · rename_i e es he
      have hb := h.eb r
      rw [he] at hb
      exact (hb e List.mem_cons_self).2 _ hm
  · exact VB.num N _

theorem StrBound.regGet (h : StrBound N st) {r : Nat} {v : Val} (hg : regGet st r = some v) :
    VB N v := by
  unfold Dc.regGet at hg
  split at hg
  · cases hg; exact VB.num N _
  · rename_i e es he
    have hb := h.eb r
    rw [he] at hb
    exact (hb e List.mem_cons_self).1 v hg

theorem rotate_mem {n : Int} {s : List Val} {v : Val} (hv : v ∈ rotate n s) : v ∈ s := by
  unfold rotate at hv
  dsimp only at hv
  split at hv
  · exact hv
  · split at hv
    · exact hv
    · split at hv
      · split at hv
        · rename_i p hp
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact List.mem_of_getElem? hp
          · exact List.mem_of_mem_eraseIdx hv
        · exact hv
      · split at hv
        · rename_i top rest
          simp only [List.mem_append, List.mem_cons] at hv ⊢
          rcases hv with hv | rfl | hv
          · exact .inr (List.mem_of_mem_take hv)
          · exact .inl rfl
          · exact .inr (List.mem_of_mem_drop hv)
        · exact hv

theorem StrBound.binop (h : StrBound N st) (f : Num → Num → Option Num) : StrBound N (binop st f) := by
  unfold Dc.binop
  split
  · rename_i b a rest e
    split
    · exact h.stk rfl fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact VB.num N _
        · exact h.vb w (by rw [e]; simp [hw])
    · exact h
  · exact h

theorem StrBound.binop2 (h : StrBound N st) (f : Num → Num → Option (Num × Num)) :
    StrBound N (binop2 st f) := by
  unfold Dc.binop2
  split
  · rename_i b a rest e
    split
    · exact h.stk rfl fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | rfl | hw
        · exact VB.num N _
        · exact VB.num N _
        · exact h.vb w (by rw [e]; simp [hw])
    · exact h
  · exact h

theorem StrBound.triop (h : StrBound N st) (f : Num → Num → Num → Option Num) :
    StrBound N (triop st f) := by
  unfold Dc.triop
  split
  · rename_i c b a rest e
    split
    · exact h.stk rfl fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact VB.num N _
        · exact h.vb w (by rw [e]; simp [hw])
    · exact h
  · exact h

theorem StrBound.cmpop (h : StrBound N st) : StrBound N (cmpop st).2 := by
  unfold Dc.cmpop
  split
  · rename_i b a rest e
    exact h.stk rfl fun w hw => h.vb w (by rw [e]; simp [hw])
  · exact h

end

end Dc

namespace Dc

theorem VB.str1 {N : Nat} (hN : 2 ≤ N) (b : Nat) : VB N (.str [b]) := fun s hs => by
  simp [Val.strs] at hs; subst hs; simp; omega

theorem VB.str0 {N : Nat} (hN : 2 ≤ N) : VB N (.str []) := fun s hs => by
  simp [Val.strs] at hs; subst hs; simp; omega

theorem StrBound.regPop {N : Nat} {st : St} (h : StrBound N st) {r : Nat} {e : Entry}
    {es : List Entry} (he : st.regs r = e :: es) : StrBound N (st.setReg r es) :=
  h.setReg fun e' he' => h.eb r e' (by rw [he]; exact List.mem_cons_of_mem _ he')

theorem StrBound.regTop {N : Nat} {st : St} (h : StrBound N st) {r : Nat} {e : Entry}
    {es : List Entry} (he : st.regs r = e :: es) {v : Val} (hv : e.val = some v) : VB N v :=
  (h.eb r e (by rw [he]; exact List.mem_cons_self)).1 v hv

theorem StrBound.rot {N : Nat} {st : St} (h : StrBound N st) {l : List Val} (hs : ∀ w ∈ l, VB N w)
    (n : Int) : StrBound N { st with stack := rotate n l } :=
  h.stk rfl fun w hw => hs w (rotate_mem (n := n) hw)

theorem StrBound.pushLev {N : Nat} {st : St} (h : StrBound N st) {v : Val} (hv : VB N v) (r : Nat) :
    StrBound N (st.setReg r (⟨some v, []⟩ :: st.regs r)) :=
  h.setReg fun e he => by
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨fun w hw => (by cases hw; exact hv), fun iv hiv => by simp at hiv⟩
    · exact h.eb r e he

theorem StrBound.drop2 {N : Nat} {st : St} (h : StrBound N st) {a b : Val} {l : List Val}
    (hs : st.stack = a :: b :: l) : StrBound N { st with stack := l } :=
  h.stk rfl fun w hw => h.vb w (by rw [hs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))

theorem StrBound.snd {N : Nat} {st : St} (h : StrBound N st) {a b : Val} {l : List Val}
    (hs : st.stack = a :: b :: l) : VB N b :=
  h.vb b (by rw [hs]; exact List.mem_cons_of_mem _ List.mem_cons_self)

theorem StrBound.all {N : Nat} {st : St} (h : StrBound N st) {l : List Val} (hs : st.stack = l) :
    ∀ w ∈ l, VB N w := fun w hw => h.vb w (hs ▸ hw)

theorem StrBound.rest {N : Nat} {st : St} (h : StrBound N st) {v : Val} {l : List Val}
    (hs : st.stack = v :: l) : ∀ w ∈ l, VB N w := fun w hw => h.all hs w (List.mem_cons_of_mem _ hw)

set_option hygiene false in
/-- The cases with a popped datum. -/
macro "sb_cons" : tactic => `(tactic| first
  | exact (h.pop hs) | exact (h.pop hs).emit _ | exact (h.pop hs).push (VB.num _ _)
  | exact (h.pop hs).push (VB.str1 hN _) | exact h.push (h.top hs)
  | exact (h.pop hs).regSet (h.top hs) | exact (h.pop hs).push ((h.pop hs).arrayGet _ _)
  | exact h.rot (h.rest hs) _
  | exact h.stk rfl (fun w hw => h.rest hs w hw)
  | exact (h.pop hs).stk rfl (fun w hw => (h.pop hs).vb w hw)
  | exact h.push (h.regGet ‹_›)
  | exact (h.regPop ‹_›).push (h.regTop ‹_› rfl)
  | exact (h.pop hs).pushLev (h.top hs) _
  | exact h.drop2 hs
  | exact (h.drop2 hs).arraySet (h.snd hs))

set_option hygiene false in
/-- One case of `dcFunc_strBound`. -/
macro "sb_close" : tactic => `(tactic| first
  | trivial | exact h | exact h.emit _ | exact h.cmpop | exact h.binop _ | exact h.binop2 _
  | exact h.triop _ | exact h.push (VB.num _ _) | exact h.push (VB.str0 hN)
  | exact h.stk rfl (fun w hw => absurd hw List.not_mem_nil)
  | exact h.rot (h.all hs) _
  | exact h.stk rfl (fun w hw => h.all hs w hw)
  | sb_cons)

theorem dcFunc_strBound {N lm : Nat} {st : St} {c : Nat} {peek : Option Nat} {neg : Bool}
    (h : StrBound N st) (hN : 2 ≤ N) : ResOK N (dcFunc lm st c peek neg) := by
  unfold dcFunc; dsimp only
  rcases hs : st.stack with _ | ⟨v, rest⟩
  rotate_left
  rcases v with n | s
  all_goals simp only [hs]
  all_goals split
  all_goals (repeat' split) <;> simp only [ResOK]
  all_goals sb_close

end Dc

namespace Dc

theorem StrBound.init (N : Nat) : StrBound N St.init :=
  ⟨fun v hv => by simp [St.init] at hv, fun r e he => by simp [St.init] at he⟩

/-- `DC_STR`'s string is no longer than the rest of the frame. -/
theorem scanStr_len : ∀ (d : Nat) (s : List Nat), (scanStr d s).1.length ≤ s.length
  | _, [] => by simp [scanStr]
  | d, c :: cs => by
    unfold scanStr
    split
    · split
      · simp
      · have := scanStr_len (d - 1) cs; simp; omega
    · split
      · have := scanStr_len (d + 1) cs; simp; omega
      · have := scanStr_len d cs; simp; omega

/-- `DC_STR` keeps `StrBound` when the frame is shorter than `N`. -/
theorem StrBound.scan {N : Nat} {st : St} (h : StrBound N st) {rest : List Nat}
    (hr : rest.length < N) : StrBound N (st.push (.str (scanStr 1 rest).1)) :=
  h.push fun s hs => by
    simp [Val.strs] at hs; subst hs; have := scanStr_len 1 rest; omega

end Dc
