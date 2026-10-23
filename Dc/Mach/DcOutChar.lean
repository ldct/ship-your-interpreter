import Dc.Mach.DcTell
import Dc.Mach.Bc.OutNum
import Dc.Refinement

/-!
# `out_char` (M9)

    out_char (c):
      if (c == '\0') { out_col = 0; return; }
      if (line_max < 0) { line_max = 70; }     -- getenv returns NULL
      if (++out_col >= line_max && line_max) { putchar('\\'); putchar('\n'); out_col = 1; }
      putchar (c);

`bc_out_num`'s callback as a `CharFn` over the invariant `OcInv`: the
console holds the bytes of `ocRun cs` after the text `t0`, `out_col` holds
its column. Without a `'\0'`, `ocRun` is the model's `Num.wrap 70 0`
(`ocRun_wrap`).

- `ocStep`, `ocRun`: the callback on one character and on a list.
- `OcInv`, `ocG`: the invariant and the bytes it reads.
- `out_char_fn`: the `CharFn` at `0x800020d8` with a 48-byte frame.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-! ## The model -/

/-- One character: the bytes written and the new column. -/
def ocStep (col c : Nat) : List Nat × Nat :=
  if c = 0 then ([], 0) else if 70 ≤ col + 1 then ([92, 10, c], 1) else ([c], col + 1)

/-- From the bytes `o` written and the column `col`, one more character. -/
def ocAcc (s : List Nat × Nat) (c : Nat) : List Nat × Nat :=
  (s.1 ++ (ocStep s.2 c).1, (ocStep s.2 c).2)

/-- The characters `cs` from column `0`. -/
def ocRun (cs : List Nat) : List Nat × Nat := cs.foldl ocAcc ([], 0)

theorem ocRun_snoc (cs : List Nat) (c : Nat) : ocRun (cs ++ [c]) = ocAcc (ocRun cs) c := by
  simp [ocRun, List.foldl_append]

theorem ocStep_col (col c : Nat) : (ocStep col c).2 < 70 := by
  unfold ocStep; split
  · simp
  · split <;> simp <;> omega

theorem ocRun_col (cs : List Nat) : (ocRun cs).2 < 70 := by
  rcases cs.eq_nil_or_concat with h | ⟨l, c, rfl⟩
  · subst h; simp [ocRun]
  · rw [List.concat_eq_append, ocRun_snoc]; exact ocStep_col _ _

theorem ocFold_wrap : ∀ (cs : List Nat) (o : List Nat) (col : Nat), (∀ c ∈ cs, c ≠ 0) →
    (cs.foldl ocAcc (o, col)).1 = o ++ Dc.Num.wrap 70 col cs
  | [], o, col, _ => by simp [Dc.Num.wrap]
  | c :: cs, o, col, h => by
    have hc : c ≠ 0 := h c List.mem_cons_self
    simp only [List.foldl_cons, ocAcc, ocStep, hc, ↓reduceIte, Dc.Num.wrap]
    by_cases hl : 70 ≤ col + 1
    · simp only [hl, ↓reduceIte, show ((70 : Nat) != 0 && decide (col + 1 ≥ 70)) = true by simp; omega]
      rw [ocFold_wrap cs _ 1 fun d hd => h d (List.mem_cons_of_mem _ hd)]
      simp
    · simp only [hl, ↓reduceIte, show ((70 : Nat) != 0 && decide (col + 1 ≥ 70)) = false by simp; omega]
      rw [ocFold_wrap cs _ (col + 1) fun d hd => h d (List.mem_cons_of_mem _ hd)]
      simp

/-- **Without `'\0'`, the callback writes the model's wrapped bytes.** -/
theorem ocRun_wrap {cs : List Nat} (h : ∀ c ∈ cs, c ≠ 0) : (ocRun cs).1 = Dc.Num.wrap 70 0 cs := by
  simpa [ocRun] using ocFold_wrap cs [] 0 h

theorem outStr_snoc (o : List Nat) (c : Nat) :
    Dc.outStr (o ++ [c]) = Dc.outStr o ++ toString (Char.ofNat c) := by
  simp [Dc.outStr, String.ofList_append]
  rfl

/-! ## The invariant -/

/-- `errno`, which `out_char`'s first call clears. -/
abbrev errnoAddr : Nat := 0x8001cd58

/-- The bytes the invariant reads and the callback writes: `stdout`'s
descriptor, `line_max`, `errno`, `out_col`. -/
def ocG (a : Nat) : Prop :=
  (stdoutFile ≤ a ∧ a < stdoutFile + 4) ∨ (lineMaxAddr ≤ a ∧ a < lineMaxAddr + 4) ∨
    (errnoAddr ≤ a ∧ a < errnoAddr + 4) ∨ (outColAddr ≤ a ∧ a < outColAddr + 4)

/-- **`out_char`'s invariant**: after the characters `cs`, the console is
`t0` and `ocRun cs`'s bytes, `out_col` its column, `line_max` unset or `70`. -/
structure OcInv (S : Nat → Prop) (t0 : String) (cs : List Nat) (t : String) (M : Mem) : Prop where
  own : ∀ a, ocG a → S a
  fd : ldv .lw M stdoutFile = BitVec.ofNat 64 1
  lm : ldv .lw M lineMaxAddr = BitVec.ofInt 64 (-1) ∨ ldv .lw M lineMaxAddr = BitVec.ofNat 64 70
  col : ldv .lw M outColAddr = BitVec.ofNat 64 (ocRun cs).2
  out : t = t0 ++ Dc.outStr (ocRun cs).1

theorem OcInv.stab {S : Nat → Prop} {t0 : String} {cs : List Nat} {t : String} {M M' : Mem}
    (h : OcInv S t0 cs t M) (hg : ∀ a, ocG a → imgM M' a = imgM M a) : OcInv S t0 cs t M' := by
  have e : ∀ x, (∀ j, j < 4 → ocG (x + j)) → ldv .lw M' x = ldv .lw M x := fun x hx =>
    ldv_congr .lw fun j hj => hg _ (hx j (by simpa [widthOfM] using hj))
  refine ⟨h.own, ?_, ?_, ?_, h.out⟩
  · rw [e _ fun j hj => by simp only [ocG]; omega]; exact h.fd
  · rw [e _ fun j hj => by simp only [ocG]; omega]; exact h.lm
  · rw [e _ fun j hj => by simp only [ocG]; omega]; exact h.col

theorem putc_ofNat {c : Nat} (hc : c < 256) : putcStr (lo8 (BitVec.ofNat 64 c)) = toString (Char.ofNat c) := by
  have e : (lo8 (BitVec.ofNat 64 c)).toNat = c := by
    simp only [lo8, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  simp only [putcStr, e]

/-- `stdout` for `putchar` from the invariant's bytes. -/
theorem OcInv.fdAt {S : Nat → Prop} {t0 : String} {cs : List Nat} {t : String} {M : Mem}
    (h : OcInv S t0 cs t M) : FdAt S M stdoutFile 1 :=
  ⟨fun i hi => h.own _ (by simp only [ocG, stdoutFile]; omega), h.fd, by decide, by decide, by decide⟩

/-! ## The callback -/

/-- `out_char`'s last `putchar (c)` (`0x80002120`), the column stored: the
invariant after `cs ++ [c]` once `c` is out. -/
theorem oc_put {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {cs o : List Nat} {c : Nat} {t : String}
    {sp : Nat} {R : Nat → BitVec 64} {M : Mem} {ra : BitVec 64}
    (own : ∀ a, ocG a → S a) (fd : ldv .lw M stdoutFile = BitVec.ofNat 64 1)
    (lm : ldv .lw M lineMaxAddr = BitVec.ofNat 64 70)
    (col : ldv .lw M outColAddr = BitVec.ofNat 64 (ocRun (cs ++ [c])).2)
    (ho : (ocRun (cs ++ [c])).1 = o ++ [c]) (ht : t = t0 ++ Dc.outStr o)
    (hsf : StackFrame S sp 48) (hsp : heapEnd + 48 ≤ sp)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h13 : R 13 = BitVec.ofNat 64 c) (hc : c < 256)
    (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps (2 :: cClob) R' R → R' 2 = BitVec.ofNat 64 sp → ∀ t', OcInv S t0 (cs ++ [c]) t' M →
      DWO live S Q t' ra R' M) :
    DWO live S Q t 0x80002120#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hsp
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, h13, hra] at 0x80000628
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine putchar_spec hlive ⟨fun i hi => own _ (by simp only [ocG, stdoutFile]; omega), fd, by decide,
    by decide, by decide⟩ _ (by bsimp [hal]) fun R' hk' e10 => ?_
  have e1 : (upd (upd (upd R 1 ra) 10 (BitVec.ofNat 64 c)) 2 (BitVec.ofNat 64 (sp - 48 + 48))) 1 = ra := by
    bsimp []
  have e2 : (upd (upd (upd R 1 ra) 10 (BitVec.ofNat 64 c)) 2 (BitVec.ofNat 64 (sp - 48 + 48))) 10 =
      BitVec.ofNat 64 c := by bsimp []
  rw [e1, e2, putc_ofNat hc]
  refine hk R' ?_ ?_ _ ⟨own, fd, .inr lm, col, by rw [ho, outStr_snoc, ht, String.append_assoc]⟩
  · exact by keeps_tac ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
  · rw [hk'.get 2 (by decide)]; bsimp []; congr 1; omega

/-- `out_char` from the column update (`0x80002104`, `sp` lowered by 48,
`a3` the character, `a4 = line_max = 70`, `a2 = 1`). -/
theorem oc_tail {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {cs : List Nat} {c : Nat} {t : String}
    {sp : Nat} {R : Nat → BitVec 64} {M : Mem} {ra : BitVec 64}
    (hI : OcInv S t0 cs t M) (hl70 : ldv .lw M lineMaxAddr = BitVec.ofNat 64 70)
    (hsf : StackFrame S sp 48) (hsp : heapEnd + 48 ≤ sp)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h13 : R 13 = BitVec.ofNat 64 c) (hc : c < 256)
    (hc0 : c ≠ 0) (h14 : R 14 = BitVec.ofNat 64 70) (h12 : R 12 = 1#64)
    (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' t', Keeps (2 :: cClob) R' R → R' 2 = BitVec.ofNat 64 sp → OcInv S t0 (cs ++ [c]) t' M' →
      (∀ a, ¬ ocG a → (a < sp - 48 ∨ sp ≤ a) → imgM M' a = imgM M a) → DWO live S Q t' ra R' M') :
    DWO live S Q t 0x80002104#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hsp
  have htx : tohostAddr = 0x8001ad00 := rfl
  have oCol : ∀ b ∈ accAddrs 2147601808 4, S b :=
    accOwn fun i hi => hI.own _ (by simp only [ocG, outColAddr]; omega)
  have hcol := hI.col
  have hcb := ocRun_col cs
  have wk := sxw_ofNat (k := (ocRun cs).2 + 1) (by omega)
  have ti : (BitVec.ofNat 64 ((ocRun cs).2 + 1)).toInt = (((ocRun cs).2 + 1 : Nat) : Int) :=
    toInt_ofNat_small (by omega)
  have t70 : (70#64).toInt = 70 := by decide
  have hlo := hI.out
  have hfd := hI.fd
  bc_run hlive hlive [h2, h13, h14, h12, hcol, wk, ti, t70]
  -- no wrap
  · intro hlt
    have e : ocRun (cs ++ [c]) = ((ocRun cs).1 ++ [c], (ocRun cs).2 + 1) := by
      rw [ocRun_snoc]; simp only [ocAcc, ocStep, hc0, ↓reduceIte, show ¬ 70 ≤ (ocRun cs).2 + 1 by omega]
    refine oc_put hlive (o := (ocRun cs).1) hI.own ?_ ?_ ?_ (by rw [e]) hlo hsf (by simp only [heapEnd]; omega)
      (by bsimp [h2]) (by bsimp [h13]) hc ?_ hal fun R' hk' e2 t' hI' => hk R' _ t' ?_ e2 hI' ?_
    · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, stdoutFile]; omega)]; exact hfd
    · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, lineMaxAddr]; omega)]; exact hl70
    · rw [e]; exact ldv_lw_hitN M rfl (toNat_ofNat_mod32 (by omega)) (by omega)
    · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact hra
    · exact by keeps_tac ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
    · intro a ha _
      exact imgM_store_miss _ _ (Classical.byContradiction fun hc => ha (by simp only [ocG, outColAddr]; omega))
  -- the wrap: `\`, newline, column 1
  · intro hge
    have h69 : (ocRun cs).2 = 69 := by omega
    bc_run hlive hlive [h2, h12, h13] at 0x80000628
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    bc_run hlive hlive [h2, h12, h13] at 0x80000628
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have own := hI.own
    have fd2 : ldv .lw (writeLog (writeLog M [(2147601808, 4, BitVec.ofNat 64 ((ocRun cs).2 + 1))])
        [(sp - 48 + 8, 8, BitVec.ofNat 64 c)]) stdoutFile = BitVec.ofNat 64 1 := by
      rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, stdoutFile]; omega),
        ldv_store_miss .lw _ _ (by simp only [widthOfM, stdoutFile]; omega)]; exact hfd
    have fdA : FdAt S (writeLog (writeLog M [(2147601808, 4, BitVec.ofNat 64 ((ocRun cs).2 + 1))])
        [(sp - 48 + 8, 8, BitVec.ofNat 64 c)]) stdoutFile 1 :=
      ⟨fun i hi => own _ (by simp only [ocG, stdoutFile]; omega), fd2, by decide, by decide, by decide⟩
    refine putchar_spec hlive fdA _ ?_ fun R1 hk1 e1 => ?_
    · bsimp []
    bsimp []
    have q1 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
    bc_run hlive hlive [q1] at 0x80000628
    refine putchar_spec hlive fdA _ ?_ fun R2 hk2 e2 => ?_
    · bsimp []
    bsimp []
    have q2 : R2 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk2.get 2 (by decide)]; bsimp [q1]
    bc_run hlive hlive [q2] at 0x80002120
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have g8 : ldv .ld (writeLog (writeLog M [(2147601808, 4, BitVec.ofNat 64 ((ocRun cs).2 + 1))])
        [(sp - 48 + 8, 8, BitVec.ofNat 64 c)]) (sp - 48 + 8) = BitVec.ofNat 64 c := ldv_store_hit _ _ _
    rw [g8]
    have p92 : putcStr (lo8 92#64) = toString (Char.ofNat 92) := putc_ofNat (by decide)
    have p10 : putcStr (lo8 10#64) = toString (Char.ofNat 10) := putc_ofNat (by decide)
    rw [p92, p10]
    have e : ocRun (cs ++ [c]) = ((ocRun cs).1 ++ [92, 10] ++ [c], 1) := by
      rw [ocRun_snoc]; simp only [ocAcc, ocStep, hc0, ↓reduceIte, show 70 ≤ (ocRun cs).2 + 1 by omega]
      simp
    refine oc_put hlive (o := (ocRun cs).1 ++ [92, 10]) own ?_ ?_ ?_ (by rw [e]) ?_ hsf
      (by simp only [heapEnd]; omega) (by bsimp [q2]) (by bsimp []) hc ?_ hal
      fun R' hk' e2' t' hI' => hk R' _ t' ?_ e2' hI' ?_
    · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, stdoutFile]; omega)]; exact fd2
    · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, lineMaxAddr]; omega),
        ldv_store_miss .lw _ _ (by simp only [widthOfM, lineMaxAddr]; omega),
        ldv_store_miss .lw _ _ (by simp only [widthOfM, lineMaxAddr]; omega)]; exact hl70
    · rw [e]; exact ldv_lw_hitN _ rfl (by simp) (by simp)
    · rw [hlo, show (ocRun cs).1 ++ [92, 10] = (ocRun cs).1 ++ [92] ++ [10] by simp, outStr_snoc,
        outStr_snoc, String.append_assoc, String.append_assoc, String.append_assoc]
    · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega),
        ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega),
        ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact hra
    · exact by keeps_tac ((hk'.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
        (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))))
    · intro a ha hw
      have hn : ¬ (2147601808 ≤ a ∧ a < 2147601808 + 4) := fun hc => ha (by simp only [ocG, outColAddr]; omega)
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]

/-! ## The callback -/

theorem oc_call {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {cs : List Nat} {c : Nat} {t : String}
    {sp : Nat} {R : Nat → BitVec 64} {M : Mem}
    (hI : OcInv S t0 cs t M) (hsf : StackFrame S sp 48) (hsp : heapEnd + 48 ≤ sp)
    (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 c) (hc : c < 256)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' t', Keeps cClob R' R → OcInv S t0 (cs ++ [c]) t' M' →
      (∀ a, ¬ ocG a → (a < sp - 48 ∨ sp ≤ a) → imgM M' a = imgM M a) → DWO live S Q t' (R 1) R' M') :
    DWO live S Q t 0x800020d8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hsp
  have htx : tohostAddr = 0x8001ad00 := rfl
  have oLm : ∀ b ∈ accAddrs 2147601724 4, S b := accOwn fun i hi => hI.own _ (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr]; omega)
  have oCol : ∀ b ∈ accAddrs 2147601808 4, S b := accOwn fun i hi => hI.own _ (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr]; omega)
  have oErr : ∀ b ∈ accAddrs 2147601752 4, S b := accOwn fun i hi => hI.own _ (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr]; omega)
  have hcol := hI.col
  have hcb := ocRun_col cs
  rcases Nat.eq_zero_or_pos c with hc0 | hc0
  · subst hc0
    bc_run hlive hlive [h10, h2]
    bc_run hlive hlive [h10, h2]
    all_goals first | exact hal | skip
    have e0 : ocRun (cs ++ [0]) = ((ocRun cs).1, 0) := by
      rw [ocRun_snoc]; simp [ocAcc, ocStep]
    refine hk _ _ _ (by keeps_tac Keeps.refl _ _) ⟨hI.own, ?_, ?_, ?_, ?_⟩ fun a ha _ => ?_
    · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, stdoutFile]; omega)]; exact hI.fd
    · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, lineMaxAddr]; omega)]; exact hI.lm
    · rw [e0]; exact ldv_lw_hitN M rfl (by simp) (by simp)
    · rw [e0]; exact hI.out
    · exact imgM_store_miss _ _ (Classical.byContradiction fun hc => ha (by simp only [ocG, outColAddr]; omega))
  · have hlm := hI.lm
    have hfd := hI.fd
    have hnz : BitVec.ofNat 64 c ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    bc_run hlive hlive [h10, h2]
    all_goals first | (intro hc; exact absurd hc (by simpa using hnz)) | skip
    intro _
    rcases hlm with hm1 | h70
    · have hm1' : ldv .lw M 2147601724 = 18446744073709551615#64 := by
        rw [show 2147601724 = lineMaxAddr from rfl, hm1]; rfl
      have tm1 : (18446744073709551615#64).toInt = -1 := by simp [BitVec.toInt]
      bc_run hlive hlive [h10, h2, hm1', tm1, word_sub48 (show 48 ≤ sp by omega)] at 0x800020f4
      clear oLm oCol oErr
      bc_run hlive hlive [h10, h2, hm1', tm1, word_sub48 (show 48 ≤ sp by omega)] at 0x80002134
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      have oLm : ∀ b ∈ accAddrs 2147601724 4, S b := accOwn fun i hi => hI.own _ (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr]; omega)
      have oErr : ∀ b ∈ accAddrs 2147601752 4, S b := accOwn fun i hi => hI.own _ (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr]; omega)
      bc_run hlive hlive [h2, word_sub48 (show 48 ≤ sp by omega)] at 0x80002104
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      have own := hI.own
      refine oc_tail hlive (cs := cs) (c := c) (ra := R 1) ⟨own, ?_, .inr ?_, ?_, hI.out⟩ ?_ hsf
        (by simp only [heapEnd]; omega) ?_ ?_ hc (by omega) ?_ ?_ ?_ hal
        fun R' M' t' hk' e2 hI' hfr => hk R' M' t' ?_ hI' fun a ha hw => ?_
      · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, stdoutFile]; omega),
          ldv_store_miss .lw _ _ (by simp only [widthOfM, stdoutFile]; omega),
          ldv_store_miss .lw _ _ (by simp only [widthOfM, stdoutFile]; omega),
          ldv_store_miss .lw _ _ (by simp only [widthOfM, stdoutFile]; omega)]; exact hfd
      · exact ldv_lw_hitN _ rfl (by simp) (by simp)
      · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, outColAddr]; omega),
          ldv_store_miss .lw _ _ (by simp only [widthOfM, outColAddr]; omega),
          ldv_store_miss .lw _ _ (by simp only [widthOfM, outColAddr]; omega),
          ldv_store_miss .lw _ _ (by simp only [widthOfM, outColAddr]; omega)]; exact hcol
      · exact ldv_lw_hitN _ rfl (by simp) (by simp)
      · bsimp [h2]
      · bsimp []
      · bsimp []
      · bsimp []
      · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega),
          ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega),
          ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega)]; exact ldv_store_hit _ _ _
      · refine Keeps.restoreAll (rs := [2]) ?_ fun z hz => ?_
        · exact by keeps_tac ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
        · simp only [List.mem_singleton] at hz; subst hz; rw [e2, h2]
      · have hn1 : ¬ (2147601724 ≤ a ∧ a < 2147601724 + 4) := fun hc => ha (by simp only [ocG, lineMaxAddr]; omega)
        have hn2 : ¬ (2147601752 ≤ a ∧ a < 2147601752 + 4) := fun hc => ha (by simp only [ocG, errnoAddr]; omega)
        rw [hfr a ha hw, imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
          imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
    · have h70' : ldv .lw M 2147601724 = 70#64 := h70
      have t70 : (70#64).toInt = 70 := by decide
      bc_run hlive hlive [h10, h2, h70', t70, word_sub48 (show 48 ≤ sp by omega)] at 0x800020f4
      clear oLm oCol oErr
      bc_run hlive hlive [h10, h2, h70', t70, word_sub48 (show 48 ≤ sp by omega)] at 0x80002104
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      have own := hI.own
      have gmiss : ∀ a, ocG a → imgM (writeLog M [(sp - 48 + 40, 8, R 1)]) a = imgM M a := fun a ha =>
        imgM_store_miss _ _ (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr] at ha; omega)
      refine oc_tail hlive (cs := cs) (c := c) (ra := R 1) (hI.stab gmiss) ?_ hsf
        (by simp only [heapEnd]; omega) ?_ ?_ hc (by omega) ?_ ?_ (ldv_store_hit _ _ _) hal
        fun R' M' t' hk' e2 hI' hfr => hk R' M' t' ?_ hI' fun a ha hw => ?_
      · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, lineMaxAddr]; omega)]; exact h70
      · bsimp [h2]
      · bsimp [h10]
      · bsimp []
      · bsimp []; first | decide | rfl
      · refine Keeps.restoreAll (rs := [2]) ?_ fun z hz => ?_
        · exact by keeps_tac ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
        · simp only [List.mem_singleton] at hz; subst hz; rw [e2, h2]
      · rw [hfr a ha hw]; exact imgM_store_miss _ _ (by omega)

/-- **`out_char` is a `CharFn`** over `ocG` and `OcInv`: the callback
`bc_out_num` receives from dc. -/
theorem out_char_fn {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (t0 : String) :
    CharFn live S Q 0x800020d8#64 48 ocG (OcInv S t0) where
  call := fun _ _ _ _ _ _ hI hsf hab h2 h10 hc hal hk => oc_call hlive hI hsf hab h2 h10 hc hal hk
  off := fun a ha => by
    simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr] at ha
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, constBytes, twoAddr, zeroAddr,
      mulBaseAddr]
    omega
  stab := fun _ _ _ _ hI hg => hI.stab hg

end Dc.Mach
