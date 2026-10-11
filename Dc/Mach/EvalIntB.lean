import Dc.Mach.EvalStrB
import Dc.Mach.DcGetnumSpec

/-!
# `evalstr`'s loop: `DC_INT` (M10)

`DC_INT` (`0x80001668`, the number's first character at `s0`):
`input_str_string = s0`, `dc_getnum (input_str, dc_ibase, sp + 28)`,
`dc_push` of the number, `s0` back at the character `readahead` holds (or
at the end of the text for `EOF`), to the test at `0x800016b0` (or
`0x800015a0`). `rt_int` is the span; `evs_int_at` re-establishes the
invariant (`EvStep.thenLk`: `dc_getnum` may lose the fraction's divisor,
within `numLeak` by `numLeak_ge`; the rest after the number by
`readNum_nul_drop`); `evs_int_k : EvIntCore`.
-/

namespace Dc

/-- A number result starts at a number character. -/
def ResInt (c : Nat) : Res → Prop
  | .int => c = 95 ∨ c = 46 ∨ (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 70)
  | _ => True

theorem dcFunc_int {lm : Nat} {st : St} {c : Nat} {peek : Option Nat} {neg : Bool} :
    ResInt c (dcFunc lm st c peek neg) := by
  unfold dcFunc; dsimp only
  rcases hs : st.stack with _ | ⟨v, rest⟩
  rotate_left
  rcases v with n | s
  all_goals simp only [hs]
  all_goals split
  all_goals (repeat' split) <;> simp only [ResInt]
  all_goals first | trivial | omega | simp_all

end Dc

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The character of a number result is a number's first character. -/
theorem headOK_of_int {lm : Nat} {st : St} {c : Nat} {peek : Option Nat} {neg : Bool}
    (h : dcFunc lm st c peek neg = .int) : HeadOK (some c) := by
  have := dcFunc_int (lm := lm) (st := st) (c := c) (peek := peek) (neg := neg)
  rw [h] at this
  rcases this with e | e | e | e
  · exact .inl e
  · exact .inr (.inl e)
  · refine .inr (.inr ?_); simp only [digitVal]
    split
    · rfl
    · rename_i h'; simp at h'; omega
  · refine .inr (.inr ?_); simp only [digitVal]
    split
    · rfl
    · rw [if_pos (by simp; omega)]; rfl

/-- `rdSign` past a stopping suffix. -/
theorem rdSign_append {t : List Nat} (ht : NulStop t) (w : List Nat) :
    (rdSign (w ++ t)).2 = (rdSign w).2 ++ t := by
  rcases w with _ | ⟨c, r⟩
  · rcases t with _ | ⟨c, cs⟩
    · rfl
    · have := ht c rfl; subst this; rfl
  · by_cases hc : c = 95
    · subst hc
      show (List.dropWhile isSpace (r ++ t)) = List.dropWhile isSpace r ++ t
      exact dropSpace_append ht r
    · rw [List.cons_append, rdSign_no (by simpa using hc), rdSign_no (by simpa using hc)]
      rfl

theorem numFrac_true {s Y : List Nat} (h : (takeDigits (rdSign s).2).2 = 46 :: Y) :
    numFrac s = true := by
  unfold numFrac
  split
  · rfl
  · rename_i hn
    exfalso
    apply hn Y
    split
    · exact h
    · rename_i hn2
      rw [rdSign_no] at h
      · exact h
      · intro h0
        rcases s with _ | ⟨c, r⟩
        · cases h0
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
          subst h0; exact hn2 r rfl

/-- `dc_getnum`'s lost references within the literal's allowance. -/
theorem numLeak_ge (l : List Nat) :
    (if (takeDigits (rdSign (l.takeWhile (· ≠ 0))).2).2.head? = some 46 then 1 else 0) ≤ numLeak l := by
  split
  · rename_i h
    have ht := nulStop_dropWhile l
    have hl : l = l.takeWhile (· ≠ 0) ++ l.dropWhile (· ≠ 0) := List.takeWhile_append_dropWhile.symm
    generalize l.takeWhile (· ≠ 0) = w at h hl
    generalize l.dropWhile (· ≠ 0) = t at ht hl
    subst hl
    have e : numFrac (w ++ t) = true := by
      obtain ⟨Y, hY⟩ : ∃ Y, (takeDigits (rdSign w).2).2 = 46 :: Y := by
        generalize (takeDigits (rdSign w).2).2 = X at h ⊢
        rcases X with _ | ⟨x, xs⟩
        · cases h
        · simp only [List.head?_cons, Option.some.injEq] at h; subst h; exact ⟨xs, rfl⟩
      refine numFrac_true (Y := Y ++ t) ?_
      rw [rdSign_append ht, takeDigits_append ht, hY]; rfl
    simp [numLeak, e]
  · exact Nat.zero_le _

/-- `readNum` of a text from `dc_getnum`'s read up to the first NUL. -/
theorem readNum_nul_drop (ib : Nat) (l : List Nat) {jE : Nat}
    (h : (readNum ib (l.takeWhile (· ≠ 0))).2 = (l.takeWhile (· ≠ 0)).drop jE) :
    readNum ib l = ((readNum ib (l.takeWhile (· ≠ 0))).1,
      l.drop (min jE (l.takeWhile (· ≠ 0)).length)) := by
  rw [readNum_takeNul, h]
  congr 1
  have hl : l = l.takeWhile (· ≠ 0) ++ l.dropWhile (· ≠ 0) := List.takeWhile_append_dropWhile.symm
  generalize l.takeWhile (· ≠ 0) = w at hl ⊢
  generalize l.dropWhile (· ≠ 0) = t at hl ⊢
  subst hl
  rw [List.drop_append_of_le_length (Nat.min_le_right _ _)]
  congr 1
  rcases Nat.le_total jE w.length with h1 | h1
  · rw [Nat.min_eq_left h1]
  · rw [Nat.min_eq_right h1, List.drop_eq_nil_of_le h1, List.drop_eq_nil_of_le (Nat.le_refl _)]

/-- `lw` of the `readahead` word `dc_getnum` stored: the character, or `EOF`. -/
theorem lw_chW (M : Mem) (a : Nat) {x : Option Nat} (hx : ∀ c, x = some c → c < 256)
    (h : imgLE (imgM M) a 4 = (chW x).toNat % 2 ^ 32) : ldv .lw M a = chW x := by
  rw [ldv_lw_img, h]
  cases x with
  | some c =>
    have hc := hx c rfl
    simp only [chW, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt (by omega : c < 2 ^ 32)]
    exact sext32_small (by omega)
  | none => rfl

/-- The bytes `DC_INT`'s span leaves as they were: all but `dc_getnum`'s
frame below `sp`, the scratch words `[sp, sp + 88)` and `input_str_string`. -/
def IntOut (sp : Nat) (M' M : Mem) : Prop :=
  ∀ a, OutHeap a → ¬ (DcGlob a ∧ ¬ PinWords a) → ¬ frameIn sp (144 + cfW) a →
    ¬ (sp ≤ a ∧ a < sp + 88) → ¬ InP a → imgM M' a = imgM M a

/-- **`DC_INT`'s span** at `0x80001668` (frame `sp`, `s0` at byte `j0` of
the string `o`). -/
theorem rt_int {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t : String} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {sp : Nat}
    {o : StrObj} {j0 : Nat} (h : DcAt S M H F L C G hs st) (gx : GnCtx S M sp G o j0)
    (hhs : hs.length + 6 ≤ 2 ^ 20) (hl : G.lk.length < 2 ^ 29) (hhd : HeadOK (rdW o j0)[0]?)
    (hsz : (rdW o j0).length < 2 ^ 24) (hown : ∀ b, sp ≤ b → b < sp + 88 → S b)
    (hsp88 : sp + 88 ≤ 0x88000000) {R : Nat → BitVec 64} (h2 : R 2 = BitVec.ofNat 64 sp) (h8 : R 8 = BitVec.ofNat 64 (o.tb.pay + j0))
    (hk : ∀ R2 M2 H2 F2 L2 C2 (lks : List Nat) pr c jE p, (p = 0x800015a0 ∨ p = 0x800016b0) →
      Keeps (8 :: 12 :: cClob) R2 R →
      R2 8 = BitVec.ofNat 64 (o.tb.pay + j0 + min jE (rdW o j0).length) → R2 12 = 0#64 →
      lks.length ≤ (if (takeDigits (rdSign (rdW o j0)).2).2.head? = some 46 then 1 else 0) →
      DcAt S M2 H2 F2 L2 C2 { { G with lk := lks ++ G.lk } with stk := (c, .num pr) :: G.stk } hs
        (st.push (.num (readNum st.ibase (rdW o j0)).1)) →
      (readNum st.ibase (rdW o j0)).2 = (rdW o j0).drop jE →
      IntOut sp M2 M → DWO live S Q t (BitVec.ofNat 64 p) R2 M2)
    (hoom : ∀ R' M' sp', OomAt S sp (144 + cfW) M (fun a => (sp ≤ a ∧ a < sp + 88) ∨ InP a) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80001668#64 R M := by
  have cx := gx.cx
  have hsf := cx.sf
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.ab
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hib := h.view.ibase
  have hG : ∀ a, DcGlob a → S a := h.glob
  bc_run hlive hS [h2, h8, hib] at 0x80002714
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | (intro b hb; have := of_mem_accAddrs hb; exact gx.own b (by simp only [InP, inPtrAddr]; omega))
    | skip
  have hma : MemOnly InP (writeLog M [(2147601776, 8, BitVec.ofNat 64 (o.tb.pay + j0))]) M :=
    fun x hx => imgM_store_miss _ _ (by simp only [InP, inPtrAddr] at hx; omega)
  have hPa : ∀ x, InP x → OutHeap x ∧ ¬ DcGlob x := fun x hx => hx.off
  have gx1 : GnCtx S (writeLog M [(2147601776, 8, BitVec.ofNat 64 (o.tb.pay + j0))]) sp G o j0 :=
    ⟨cx, gx.mem, gx.j0, gx.own, gx.mb.transport fun x e1 e2 => hma x (by
      simp only [InP, inPtrAddr, mulBaseAddr] at e1 e2 ⊢; omega)⟩
  refine dc_getnum_spec hlive (ra := sp + 28) (h.outWrite hma hPa) gx1 hhs hl
    (fun R' M' sp' oa => hoom R' M' sp' ⟨oa.lo, oa.hi, oa.r2, fun x e1 e2 e3 e4 => by
      rw [oa.out x e1 e2 e3 (fun hx => e4 (.inr hx))]; exact hma x (fun hx => e4 (.inr hx)), oa.al⟩)
    (.inr ⟨fun b h1 h2 => hown b (by omega) (by omega), by omega, by omega, by omega⟩) hhd hsz _
    (by bsimp [h2]) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) (ldv_store_hit _ _ _)
    (fun R' M' H' F' L' C' lks pr jE hlks k2 e2 hd hden hkp r11 r10 erest hptr hra hout => ?_)
  have e2' : R' 2 = BitVec.ofNat 64 sp := by rw [e2]; bsimp [h2]
  bsimp []
  bc_run hlive hS [e2'] at 0x80002da4
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | (intro b hb; have := of_mem_accAddrs hb; exact hown b (by omega) (by omega))
    | skip
  have hm2 : MemOnly (fun x => sp + 48 ≤ x ∧ x < sp + 64)
      (writeLog (writeLog M' [(sp + 48, 8, R' 10)]) [(sp + 56, 8, R' 11)]) M' :=
    fun x hx => by rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hP2 : ∀ x, (sp + 48 ≤ x ∧ x < sp + 64) → OutHeap x ∧ ¬ DcGlob x := fun x hx =>
    have := above_sp (sp := sp) (a := x) (by omega) (by omega)
    ⟨this.1, this.2.1⟩
  have hsf64 : StackFrame S sp 64 := hsf.mono (by omega)
  refine dc_push_spec hlive (hd.outWrite hm2 hP2) hden hsf64 (by omega) _
    ⟨by bsimp []; exact r10, by bsimp []; exact r11⟩ (by bsimp [e2']) (by bsimp [])
    (fun R4 M4 H4 c k4 h4 hout4 => ?_)
    (fun R4 M4 e4 hout4 => hoom R4 M4 (sp - 64) ⟨by omega, by omega, e4, fun x e1 e2 e3 e5 => by
      have hq : ¬ (sp ≤ x ∧ x < sp + 88) := fun hq => e5 (.inl hq)
      have hi : ¬ InP x := fun hi => e5 (.inr hi)
      rw [hout4 x e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)),
        hm2 x (fun hx => hq (by omega)),
        hout x e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)) hi
          (fun hr => hq (by simp only [RaB] at hr; omega))]
      exact hma x hi, by omega⟩)
  -- the words read after the push
  have hag : ∀ x, sp ≤ x → (x < sp + 48 ∨ sp + 64 ≤ x) → imgM M4 x = imgM M' x := fun x h1 h2 => by
    have hb := above_sp (sp := sp) (a := x) (by omega) h1
    rw [hout4 _ hb.1 (nglob_pin hb.2.1) (hb.2.2 _), hm2 _ (by omega)]
  have hagI : ∀ x, InP x → imgM M4 x = imgM M' x := fun x hx => by
    have hb := hx.off
    rw [hout4 _ hb.1 (nglob_pin hb.2) (fun hf => by simp only [frameIn, InP, inPtrAddr] at hf hx; omega),
      hm2 _ (by simp only [InP, inPtrAddr] at hx; omega)]
  have hc : ∀ c, (rdW o j0)[jE]? = some c → c < 256 := fun c e =>
    (h.rd gx.mem gx.j0).lt c (List.mem_of_getElem? e)
  have hlw : ldv .lw M4 (sp + 28) = chW (rdW o j0)[jE]? := by
    rw [ldv_congr .lw fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]
    exact lw_chW _ _ hc (hra (by omega))
  have hp4 : ldv .ld M4 inPtrAddr =
      BitVec.ofNat 64 (o.tb.pay + j0 + min (jE + 1) (rdW o j0).length) := by
    rw [ldv_congr .ld fun j hj => hagI _ (by simp only [InP, widthOfM] at hj ⊢; omega)]
    exact hptr
  have e42 : R4 2 = BitVec.ofNat 64 sp := by rw [k4.get 2 (by decide)]; bsimp [e2']
  bsimp []
  have hob : OwnedBytes S sp 88 := ⟨fun i hi => hown _ (by omega) (by omega), by omega, by omega⟩
  have hio : IntOut sp M4 M := fun x e1 e2 e3 e5 e6 => by
    have hq : ¬ (sp + 48 ≤ x ∧ x < sp + 64) := fun hq => e5 (by omega)
    rw [hout4 x e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)), hm2 x hq,
      hout x e1 e2 e3 e6 (fun hr => e5 (by simp only [RaB] at hr; omega))]
    exact hma x e6
  clear hown hag hagI hG
  have hpa : ∀ b ∈ accAddrs inPtrAddr 8, S b := fun b hb => by
    have := of_mem_accAddrs hb; exact gx.own b (by simp only [InP, inPtrAddr]; omega)
  have hjl := (h.rd gx.mem gx.j0).hi
  simp only [heapEnd] at hjl
  rcases hx : (rdW o j0)[jE]? with _ | ch
  · -- `EOF`: the reader at the end of the text
    rw [hx] at hlw
    have hge : (rdW o j0).length ≤ jE := List.getElem?_eq_none_iff.mp hx
    simp only [chW, show BitVec.ofInt 64 (-1) = 18446744073709551615#64 from rfl] at hlw
    bc_run hlive hS [e42, hlw, hp4] at 0x800015a0
    all_goals first
      | exact frame_acc hsf (by omega) (by omega)
      | (intro b hb; have := of_mem_accAddrs hb; exact hob.own' (by omega) (by omega))
      | skip
    refine hk _ M4 H4 F' L' C' lks pr c jE 0x800015a0 (.inl rfl)
      (by keeps_tac ((k4.mono (by decide)).trans (by keeps_tac ((k2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))))
      (by bsimp []; congr 1; omega) (by bsimp []) hlks h4 erest hio
  · -- a character: the reader one back
    rw [hx] at hlw
    have hlt : jE < (rdW o j0).length := (List.getElem?_eq_some_iff.mp hx).1
    have hch := hc ch hx
    simp only [chW] at hlw
    have hne : BitVec.ofNat 64 ch ≠ 18446744073709551615#64 := fun hc' => by
      have := congrArg BitVec.toNat hc'; simp only [BitVec.toNat_ofNat] at this; omega
    have hdec : BitVec.ofNat 64 (o.tb.pay + j0 + min (jE + 1) (rdW o j0).length) +
        18446744073709551615#64 = BitVec.ofNat 64 (o.tb.pay + j0 + min jE (rdW o j0).length) := by
      rw [word_pred (by omega)]; congr 1; omega
    bc_run hlive hS [e42, hlw, hp4] at 0x800016b0
    all_goals first
      | exact frame_acc hsf (by omega) (by omega)
      | (intro b hb; have := of_mem_accAddrs hb; exact hob.own' (by omega) (by omega))
      | (intro hc'; exact absurd hc' hne)
      | skip
    intro _
    bc_run hlive hS [e42, hlw, hp4, hdec] at 0x800016b0
    refine hk _ M4 H4 F' L' C' lks pr c jE 0x800016b0 (.inr rfl)
      (by keeps_tac ((k4.mono (by decide)).trans (by keeps_tac ((k2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))))
      (by bsimp [hdec]) (by bsimp []) hlks h4 erest hio

/-- **Steps compose** with `n` more lost references than the first step's
allowance. -/
theorem EvStep.thenLk {S : Nat → Prop} {sp W al : Nat} {M : Mem} {G : DcG} {hs xs : List GV}
    {M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG} {st' : St}
    {ex : List GV} (hp : EvStep S sp W al M G hs xs M' H' F' L' C' G' st' ex)
    {M'' : Mem} {H'' : Heap} {F'' : List Blk} {L'' : List NumObj} {C'' : BcConsts} {G'' : DcG}
    {st'' : St} (hdc : DcAt S M'' H'' F'' L'' C'' G'' (ex ++ (xs ++ hs)) st'') {n : Nat}
    (hlk : G''.lk.length ≤ G'.lk.length + n) (hpin : StrPin G'.strs G''.strs (ex ++ (xs ++ hs)))
    (hout : ∀ a, OutHeap a → ¬ (DcGlob a ∧ ¬ PinWords a) → ¬ frameIn (sp - 176) (W - 176) a →
      ¬ (sp - 176 ≤ a ∧ a < sp - 176 + 88) → ¬ InP a → imgM M'' a = imgM M' a) :
    EvStep S sp W (al + n) M G hs xs M'' H'' F'' L'' C'' G'' st'' ex :=
  ⟨hdc, by have := hp.lk; omega,
    hp.pin.trans (hpin.mono fun g hg => List.mem_append_right _ hg),
    fun a e1 e2 e3 e4 e5 e6 => (hout a e1 e2 e4 e5 e6).trans (hp.out a e1 e2 e3 e4 e5 e6)⟩

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {ex : List GV}

/-- **`DC_INT`** from `0x80001668` (either dispatch table): `rt_int`, the
invariant over the rest after the number, the test. -/
theorem evs_int_at (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex) (hres : dcFunc 70 st c rest.head? neg = .int)
    (hlc : leakOne c + numLeak (c :: rest) ≤ k) (hoom : EvOom live S Q sp W q M0)
    (hhead : EvHeadK live S Q t0 sp W d k (k - leakOne c - numLeak (c :: rest)) q M0 R0 G hs xs
      (st.push (.num (readNum st.ibase (c :: rest)).1)) ⟨(readNum st.ibase (c :: rest)).2, td, false⟩)
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs (st.push (.num (readNum st.ibase (c :: rest)).1))
      ⟨(readNum st.ibase (c :: rest)).2, td, false⟩)
    {R1 : Nat → BitVec 64} (k1 : Keeps [10, 15] R1 R') :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001668#64 R1 M' := by
  obtain ⟨o0, ho1, ho2, ho3, ev0⟩ := e.same (e.hal (by omega)) e.ev.sb e.ev.srt (R2 := R1)
    (k1.mono (by decide))
  obtain ⟨i, hi, hdrop, h8⟩ := e.ev.pos
  have h8' : R1 8 = BitVec.ofNat 64 (o0.tb.pay + i) := by
    rw [k1.get 8 (by decide), e.k1.get 8 (by decide), e.kc.get 8 (by decide), h8, ho2]
  have hdrop0 : o0.s.drop i = c :: rest := by rw [ho3]; exact hdrop
  have hw : rdW o0 i = (c :: rest).takeWhile (· ≠ 0) := by simp only [rdW]; rw [hdrop0]
  have hhc := headOK_of_int hres
  have hc0 : c ≠ 0 := by have := hhc.range; omega
  have hhd : HeadOK (rdW o0 i)[0]? := by
    rw [hw]; simp only [List.takeWhile_cons, ne_eq, hc0, not_false_eq_true, decide_true]; exact hhc
  have hlen : (c :: rest).length + i = o.s.length := by
    have := congrArg List.length hdrop; simp only [List.length_drop] at this; omega
  have hsz : (rdW o0 i).length < 2 ^ 24 := by
    rw [hw]; have := (List.takeWhile_prefix (p := fun x => decide (x ≠ 0)) (l := c :: rest)).length_le
    have := e.ev.strLen; omega
  have hstk := e.ev.stk; have hab := e.ev.room; have hbud := ev0.budget
  have hfr := e.ev.frame
  have hfl := hfr.lo; have hfh := hfr.hi; have hfa := hfr.al
  have cx : CfCtx S 144 (sp - 176) :=
    ⟨hfr.within (m := 176) (n := 144 + cfW) (by simp only [cfW]; omega) (by decide),
      by simp only [cfW, heapEnd] at hab ⊢; omega, by decide⟩
  have gx : GnCtx S M' (sp - 176) G' o0 i :=
    ⟨cx, ev0.strIn, by rw [ho3]; omega, ev0.globs.inOwn, ev0.mb⟩
  refine rt_int hlive ev0.dc gx (by simp only [List.length_append] at hbud ⊢; omega) (by omega) hhd hsz
    (fun b h1 h2 => hfr.own b (by omega) (by omega)) (by omega) ev0.r2 h8'
    (fun R2 M2 H2 F2 L2 C2 lks pr c2 jE p hp k2 h82 h12 hlks h4 erest hio => ?_)
    (fun R2 M2 sp2 oa => ev0.oomK hoom (sp' := sp2) (by have := oa.lo; simp only [cfW] at this; omega)
      oa.hi oa.r2 oa.al fun x e1 e2 e3 e5 e6 => oa.out x e1 e2
        (fun hf => e3 (by simp only [frameIn, cfW] at hf ⊢; omega))
        (fun hP => hP.elim (fun hq => e5 (by omega)) e6))
  have hn := readNum_nul_drop st.ibase (c :: rest) (jE := jE) (by rw [← hw]; exact erest)
  rw [← hw] at hn
  have hlk : lks.length ≤ numLeak (c :: rest) :=
    Nat.le_trans hlks (by rw [hw]; exact numLeak_ge _)
  rw [List.append_assoc] at h4
  have hst := e.step.thenLk h4 (n := numLeak (c :: rest))
    (by show (lks ++ G'.lk).length ≤ _; simp only [List.length_append]; omega) (StrPin.refl _ _)
    fun x e1 e2 e3 e5 e6 => hio x e1 e2 (fun hf => e3 (by simp only [frameIn, cfW] at hf ⊢; omega)) e5 e6
  have hmin : min jE (rdW o0 i).length ≤ (c :: rest).length := by
    rw [hw]; have := (List.takeWhile_prefix (p := fun x => decide (x ≠ 0)) (l := c :: rest)).length_le
    omega
  have cs := e.ev.cs
  obtain ⟨o', -, -, -, ev'⟩ := e.ev.step hst (k' := k - leakOne c - numLeak (c :: rest))
    (by have := leakAllow_le c; omega)
    (f' := ⟨(readNum st.ibase (c :: rest)).2, td, false⟩) (R2 := R2)
    (j := i + min jE (rdW o0 i).length) (by omega)
    (by rw [hn]; show o.s.drop (i + _) = _; rw [← List.drop_drop, hdrop])
    (by rw [h82, ho2, Nat.add_assoc])
    (by rw [k2.get 9 (by decide), k1.get 9 (by decide), e.k1.get 9 (by decide), e.kc.get 9 (by decide)])
    (by rw [k2.get 22 (by decide), k1.get 22 (by decide), e.k1.get 22 (by decide),
      e.kc.get 22 (by decide)])
    (by rw [k2.get 24 (by decide), k1.get 24 (by decide), e.k1.get 24 (by decide),
      e.kc.get 24 (by decide)]; exact e.ev.s8)
    e.ev.tdLt
    ⟨by rw [k2.get 18 (by decide), k1.get 18 (by decide), e.k1.get 18 (by decide),
        e.kc.get 18 (by decide)]; exact cs.s2,
      by rw [k2.get 19 (by decide), k1.get 19 (by decide), e.k1.get 19 (by decide),
        e.kc.get 19 (by decide)]; exact cs.s3,
      by rw [k2.get 20 (by decide), k1.get 20 (by decide), e.k1.get 20 (by decide),
        e.kc.get 20 (by decide)]; exact cs.s4,
      by rw [k2.get 21 (by decide), k1.get 21 (by decide), e.k1.get 21 (by decide),
        e.kc.get 21 (by decide)]; exact cs.s5⟩
    (by rw [k2.get 2 (by decide), k1.get 2 (by decide), e.e2, e.kc.get 2 (by decide)])
    ((((k2.mono (by decide)).trans (k1.mono (by decide))).trans (e.k1.mono (by decide))).trans
      (e.kc.mono (by decide)))
    (e.ev.sb.push (VB.num _ _)) (e.ev.srt.stack _)
  have h12' : R2 12 = boolWord false := by rw [h12]; rfl
  have hg : (lks ++ G'.lk).length + (ex ++ xs).length + 4 * (k - leakOne c - numLeak (c :: rest)) ≤
      G.lk.length + xs.length + 4 * k := by
    have := e.post.lk; have := leakAllow_le c
    simp only [List.length_append] at this ⊢; omega
  simp only [hn] at hhead hend ev'
  rcases hp with rfl | rfl
  · have hc := ev_cont_k (bltu_800015a0 hlive) ev' h12' hg e.pin0 hhead hend
    exact hc
  · have hc := ev_cont_k (bltu_800016b0 hlive) ev' h12' hg e.pin0 hhead hend
    exact hc

end

/-- **`DC_INT`** (status `5`), continuation-generic: the status dispatch then
`evs_int_at`. -/
theorem evs_int_k {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) : EvIntCore live S Q := by
  intro t0 sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C' G' ex
    e hres h10 hlc hoom hhead hend
  split
  · exact evl_5 hlive h10 e.cs fun R1 k1 => evs_int_at hlive e hres hlc hoom hhead hend k1
  · exact evm_5 hlive h10 e.cs fun R1 k1 => evs_int_at hlive e hres hlc hoom hhead hend k1

end Dc.Mach
