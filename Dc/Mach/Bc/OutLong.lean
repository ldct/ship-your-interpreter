import Dc.Mach.Bc.Int2Num
import Dc.Mach.Printf
import Dc.Mach.Strlen

/-!
# `bc_out_long` (`lib/number.c`)

```
800064ec addi sp,sp,-96 ; save s0,s1,s2,ra,s3 ; s0 = size ; s1 = out_char ; s2 = val
80006510 if space: out_char (' ')
8000651c snprintf (buf = sp+8, 40, "%ld", val) ; s2 = s3 = strlen (buf)
80006544 while s2 != s0: out_char ('0'), s0--          (entered when len < size)
80006558 for each byte of buf: out_char (byte)
80006584 restore, ret
```

`out_char` is a function pointer. `CharCb` is its contract: an invariant on
the characters sent so far, the console and the memory, kept by every call.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## `%ld` of a nonnegative value -/

theorem udigits_small {v : Nat} (h : v < 10) : udigits 10 v = [digitChar v] := by
  simp only [udigits, ndig_of_lt h, List.range_one, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, dg, Nat.pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt h]

theorem udigits_step {v : Nat} (h : 10 ≤ v) :
    udigits 10 v = udigits 10 (v / 10) ++ [digitChar (v % 10)] := by
  simp only [udigits, ndig_of_ge (by decide) h, List.range_succ_eq_map, List.map_cons,
    List.map_map, List.reverse_cons]
  congr 2
  · apply List.map_congr_left
    intro j _
    simp only [Function.comp, dg, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  · simp [dg]

theorem decText_pos {n : Nat} (h : n ≠ 0) : Num.decText n = (Num.digits 10 n).map Num.decChar := by
  have hst := BcModel.digits_step 10 (by decide) n h
  unfold Num.decText
  split
  · rename_i he; rw [hst] at he; simp at he
  · rfl

/-- `udigits 10 v` is the decimal text of `v`. -/
theorem udigits_text (v : Nat) : (udigits 10 v).map BitVec.toNat = Num.decText v := by
  induction v using Nat.strongRecOn with
  | _ v ih =>
  have hd : v % 10 < 10 := Nat.mod_lt _ (by decide)
  have hc : (digitChar (v % 10)).toNat = Num.decChar (v % 10) := by
    simp only [digitChar, if_pos hd, BitVec.toNat_ofNat, Num.decChar]; omega
  by_cases h : v < 10
  · rw [udigits_small h]
    by_cases h0 : v = 0
    · subst h0; rfl
    · rw [decText_pos h0, BcModel.digits_step 10 (by decide) v h0, Nat.div_eq_of_lt h]
      rw [Nat.mod_eq_of_lt h] at hc
      simp only [List.map_cons, List.map_nil, hc, show Num.digits 10 0 = [] from rfl,
        List.nil_append, Nat.mod_eq_of_lt h]
  · have h1 : v / 10 ≠ 0 := by omega
    rw [udigits_step (by omega), decText_pos (by omega),
      BcModel.digits_step 10 (by decide) v (by omega), List.map_append, List.map_append,
      ih (v / 10) (by omega), decText_pos h1]
    simp only [List.map_cons, List.map_nil, hc]

theorem decText_len {v : Nat} (hv : v < 2 ^ 63) :
    1 ≤ (Num.decText v).length ∧ (Num.decText v).length ≤ 19 := by
  rw [← udigits_text, List.length_map, udigits_length]
  exact ⟨ndig_pos _ _, ndig_le (by decide) 19 v (by decide) (by omega)⟩

theorem decText_char {v : Nat} : ∀ c ∈ Num.decText v, 48 ≤ c ∧ c < 58 := by
  intro c hc
  rw [← udigits_text] at hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  simp only [udigits, List.mem_reverse, List.mem_map] at hb
  obtain ⟨j, _, rfl⟩ := hb
  have hd : v / 10 ^ j % 10 < 10 := Nat.mod_lt _ (by decide)
  simp only [dg, digitChar, hd, if_true, BitVec.toNat_ofNat]
  omega

/-- The `%ld` piece. -/
abbrev ldPiece : Piece := .conv false true .d

theorem fmt_ld {v : Nat} (hv : v < 2 ^ 63) :
    fmt [ldPiece] [⟨BitVec.ofNat 64 v, []⟩] = udigits 10 v := by
  simp only [fmt, convOut, fmtDval, if_true, msb_ofNat_small hv, Bool.false_eq_true, if_false,
    BitVec.toNat_ofNat, List.append_nil]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- Bytes `l` at `p` in `.rodata`, from per-index facts. -/
theorem RoBytes.of_get : ∀ {p : Nat} {l : List (BitVec 8)},
    (∀ i, i < l.length → dcROImg (p + i) = l.getD i 0 ∧ (p + i, l.getD i 0) ∈ dcRO) →
    0x80000000 ≤ p → p + l.length ≤ tohostAddr → RoBytes p l
  | _, [], _, _, _ => trivial
  | p, b :: l, h, hlo, hhi => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    refine ⟨h0.1, h0.2, hlo, by simp only [List.length_cons] at hhi; omega,
      RoBytes.of_get (fun i hi => ?_) (by omega) (by simp only [List.length_cons] at hhi; omega)⟩
    have := h (i + 1) (by simp only [List.length_cons]; omega)
    simpa only [List.getD_cons_succ, show p + (i + 1) = p + 1 + i by omega] using this

theorem ld_ro_bytes : ∀ i, i < 4 →
    dcROImg (0x80007ea0 + i) = [37#8, 108#8, 100#8, 0#8].getD i 0 ∧
      (0x80007ea0 + i, [37#8, 108#8, 100#8, 0#8].getD i 0) ∈ dcRO := by
  decide +kernel

/-- `"%ld"` at `0x80007ea0`. -/
theorem ld_ro : RoBytes 0x80007ea0 (fmtBytes [ldPiece] ++ [0#8]) :=
  RoBytes.of_get (l := [37#8, 108#8, 100#8, 0#8]) ld_ro_bytes (by decide)
    (by simp only [tohostAddr]; decide)

/-! ## The callback -/

/-- The registers a C function may change: `ra`, `t0`–`t6`, `a0`–`a7`. -/
abbrev cClob : List Nat := [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- **A character callback** at `f` (`bc_out_num`'s `out_char`) using `d`
bytes of stack: from `I cs t M` (the characters `cs` sent so far, the console
`t`, the memory), a call with the byte `c` in `a0` returns to `ra` with
`I (cs ++ [c])`, keeping `sp`, `s0`–`s11` and every byte at or above `sp`. -/
structure CharCb (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (f : BitVec 64) (d : Nat) (I : List Nat → String → Mem → Prop) : Prop where
  call : ∀ cs c t sp (R : Nat → BitVec 64) M, I cs t M → StackFrame S sp d →
    heapEnd + d ≤ sp → R 2 = BitVec.ofNat 64 sp → R 10 = BitVec.ofNat 64 c → c < 256 →
    (R 1).toNat % 4 = 0 →
    (∀ R' M' t', Keeps cClob R' R → I (cs ++ [c]) t' M' → (∀ a, sp ≤ a → imgM M' a = imgM M a) →
      DWO live S Q t' (R 1) R' M') →
    DWO live S Q t f R M

/-! ## Frame, state and continuation -/

/-- `bc_out_long`'s saved registers at `sp - 96`. -/
abbrev olSlots : List (Nat × Nat) := [(19, 56), (1, 88), (18, 64), (9, 72), (8, 80)]

/-- The registers changed inside `bc_out_long` before its epilogue. -/
abbrev olAll : List Nat :=
  [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 28, 29, 30, 31]

/-- `bc_out_long`'s fixed context: its 96-byte frame, `snprintf`'s 320 bytes
and the callback's `d` below it, all above the heap; the entry's `sp`,
return address and callback (4-aligned). -/
structure OLCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp d : Nat) : Prop where
  frame : StackFrame S sp (416 + d)
  above : heapEnd + 416 + d ≤ sp
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0
  fal : (R0 13).toNat % 4 = 0

/-- `bc_out_long`'s continuation: back at `ra` with the characters `target`
sent, `ra`, `sp`, `s0`–`s11` kept, nothing at or above `sp` changed. -/
def OLK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (R0 : Nat → BitVec 64) (M0 : Mem) (sp : Nat)
    (target : List Nat) : Prop :=
  ∀ R' M' t', Keeps cClob R' R0 → I target t' M' → (∀ a, sp ≤ a → imgM M' a = imgM M0 a) →
    DWO live S Q t' (R0 1) R' M'

/-- Inside `bc_out_long`: `sp` lowered by 96, the saved registers in the
frame, `s1` the callback, nothing at or above `sp` changed. -/
structure OLAt (M0 : Mem) (R0 R : Nat → BitVec 64) (sp : Nat) (M : Mem) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 96)
  saved : SavedWords M (sp - 96) olSlots R0
  rf : R 9 = R0 13
  regs : Keeps olAll R R0
  hi : ∀ a, sp ≤ a → imgM M a = imgM M0 a

/-- `OLAt` through a C call: registers in `cClob` and bytes below `sp - 48`
changed. -/
theorem OLAt.keep {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp : Nat}
    (st : OLAt M0 R0 R sp M) (hsp : 96 ≤ sp) (hk : Keeps cClob R' R)
    (hm : ∀ a, sp - 48 ≤ a → imgM M' a = imgM M a) : OLAt M0 R0 R' sp M' :=
  { r2 := by rw [hk.get 2]; exact st.r2
    saved := st.saved.transport (lo := 56) (top := 96) (hag := fun a h1 _ => hm a (by omega))
    rf := by rw [hk.get 9]; exact st.rf
    regs := (hk.mono (by decide)).trans st.regs
    hi := fun a ha => (hm a (by omega)).trans (st.hi a ha) }

/-- Leaving `bc_out_long`: `ra`, `sp`, `s0`–`s3` restored, the rest kept. -/
theorem ol_restore {R' R R0 : Nat → BitVec 64} (h1 : R' 1 = R0 1) (h2 : R' 2 = R0 2)
    (h8 : R' 8 = R0 8) (h9 : R' 9 = R0 9) (h18 : R' 18 = R0 18) (h19 : R' 19 = R0 19)
    (hk : Keeps olAll R' R) (hkp : Keeps olAll R R0) : Keeps cClob R' R0 := fun z hz => by
  by_cases e2 : z = 2; · subst e2; exact h2
  by_cases e8 : z = 8; · subst e8; exact h8
  by_cases e9 : z = 9; · subst e9; exact h9
  by_cases e18 : z = 18; · subst e18; exact h18
  by_cases e19 : z = 19; · subst e19; exact h19
  have hz' : z ∉ olAll := by
    simp only [cClob, olAll, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz ⊢; omega
  exact (hk z hz').trans (hkp z hz')

/-! ## The epilogue (`0x80006584`) -/

theorem ol_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp d : Nat}
    {target : List Nat} {t : String}
    (cx : OLCtx S R0 sp d) (hk : OLK live S Q I R0 M0 sp target) (st : OLAt M0 R0 R sp M)
    (hI : I target t M) : DWO live S Q t 0x80006584#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e1 := st.saved.get 1 88
  have e8 := st.saved.get 8 80
  have e9 := st.saved.get 9 72
  have e18 := st.saved.get 18 64
  have e19 := st.saved.get 19 56
  have hr2 := st.r2
  have hal := cx.al
  bc_run hlive hsf [hr2, e1, e8, e9, e18, e19]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  exact hk _ _ _ (ol_restore (by bsimp []) (by bsimp [cx.sp0]; congr 1; omega) (by bsimp [])
    (by bsimp []) (by bsimp []) (by bsimp []) (by keeps_tac Keeps.refl _ _) st.regs) hI st.hi

/-- Registers `bc_out_long` sets freely: all of `olAll` but `sp` and `s1`. -/
abbrev olSet : List Nat :=
  [1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 28, 29, 30, 31]

theorem OLAt.set {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp : Nat} (st : OLAt M0 R0 R sp M)
    {z : Nat} (w : BitVec 64) (hz : z ∈ olSet := by decide) : OLAt M0 R0 (upd R z w) sp M := by
  have h2 : z ≠ 2 := by simp only [olSet, List.mem_cons, List.not_mem_nil, or_false] at hz; omega
  have h9 : z ≠ 9 := by simp only [olSet, List.mem_cons, List.not_mem_nil, or_false] at hz; omega
  exact
    { st with
      r2 := by rw [upd_other _ _ (Ne.symm h2)]; exact st.r2
      rf := by rw [upd_other _ _ (Ne.symm h9)]; exact st.rf
      regs := Keeps.upd _ (by
        simp only [olSet, olAll, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢; omega) st.regs }

theorem take_succ_getD {l : List Nat} {i : Nat} (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  rfl

theorem zext8_ofNat {c : Nat} (h : c < 256) :
    zero_extend (m := 64) (BitVec.ofNat 8 c) = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The callback's frame below `bc_out_long`'s. -/
theorem ol_cbFrame {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp d : Nat} (cx : OLCtx S R0 sp d) :
    StackFrame S (sp - 96) d := by
  have hsf := cx.frame
  have := hsf.lo; have := hsf.hi; have := hsf.al
  exact ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩

theorem ol_cbAbove {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp d : Nat} (cx : OLCtx S R0 sp d) :
    heapEnd + d ≤ sp - 96 := by
  have := cx.above; omega

/-! ## The output loop (`0x80006574`) -/

theorem ol_out {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {M0 : Mem} {R0 : Nat → BitVec 64} {sp d : Nat}
    {pre text : List Nat} (cb : CharCb live S Q (R0 13) d I) (cx : OLCtx S R0 sp d)
    (hk : OLK live S Q I R0 M0 sp (pre ++ text)) (hl40 : text.length < 40)
    (hch : ∀ c ∈ text, c < 256) :
    ∀ k i (R : Nat → BitVec 64) (M : Mem) (t : String), text.length - i = k → i < text.length →
      OLAt M0 R0 R sp M → BufAt M (sp - 88) text → I (pre ++ text.take i) t M →
      R 8 = BitVec.ofNat 64 (sp - 88 + i) → R 18 = BitVec.ofNat 64 (sp - 88 + text.length) →
      DWO live S Q t 0x80006574#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k with
  | zero => intro i R M t hk' hi; omega
  | succ k ih =>
    intro i R M t hk' hi st hbuf hI h8 h18
    have hr9 := st.rf; have hr2 := st.r2
    have hb := hbuf i hi
    have hc : text.getD i 0 < 256 := hch _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi)
    have hz := zext8_ofNat hc
    bc_run hlive hsf [h8, h18, hr9, hr2, hb, hz]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    · rw [jalr_tgt _ cx.fal]; exact cx.fal
    rw [jalr_tgt _ cx.fal]
    refine cb.call _ _ t (sp - 96) _ M hI (ol_cbFrame cx) (ol_cbAbove cx) (by bsimp [hr2]) (by bsimp [])
      hc (by bsimp []) fun R' M' t' hk1 hI' hm => ?_
    bsimp []
    have st' := (((st.set (z := 10) _).set (z := 8) _).set (z := 1) _).keep (by omega) hk1
      fun a ha => hm a (by omega)
    have hbuf' : BufAt M' (sp - 88) text := fun j hj => by rw [hm _ (by omega)]; exact hbuf j hj
    have r8 : R' 8 = BitVec.ofNat 64 (sp - 88 + i + 1) := by rw [hk1.get 8]; bsimp []
    have r18 : R' 18 = BitVec.ofNat 64 (sp - 88 + text.length) := by rw [hk1.get 18]; bsimp [h18]
    have hI2 : I (pre ++ text.take (i + 1)) t' M' := by
      rw [take_succ_getD hi, ← List.append_assoc]; exact hI'
    bc_run hlive hsf [r8, r18] at 0x80006574 0x80006584
    · intro hne
      have hlt : i + 1 < text.length := by
        rcases Nat.lt_or_ge (i + 1) text.length with h | h
        · exact h
        · exact absurd (by rw [show sp - 88 + i + 1 = sp - 88 + text.length by omega]) hne
      exact ih (i + 1) R' M' t' (by omega) hlt st' hbuf' hI2 r8 r18
    · intro heq
      have hL : i + 1 = text.length := by
        have := (ofNat_eq_iff (x := sp - 88 + i + 1) (y := sp - 88 + text.length) (by omega)
          (by omega)).mp (Classical.not_not.mp heq)
        omega
      rw [hL, List.take_of_length_le (Nat.le_refl _)] at hI2
      exact ol_epi hlive cx hk st' hI2

end Dc.Mach
