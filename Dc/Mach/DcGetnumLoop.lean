import Dc.Mach.DcGetnumBase

/-!
# `dc_getnum`: the digit loops (M9)

`dc_getnum`'s frame is 144 bytes: the slots `base` (`8`), `result` (`16`),
`build` (`24`), `temp` (`32`), `divisor` (`40`), the return word (`48`), and
the saved `s7`…`s0`, `ra` from `72`. Its body keeps the reader in `s2`, the
`readahead` pointer in `s3`, `&_zero_` in `s4`, `9` in `s5`, the sign
character in `s6`, `5` in `s7`.

- `GnCtx`, `GnRegs`, `GnRd`: the fixed context, the body's registers, the
  reader after the character at `j`.
- `GnI`, `gn_int`: the integer loop at `0x80002820`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `dc_getnum`'s saved registers. -/
abbrev gnSv : List (Nat × Nat) :=
  [(0x88, 1), (0x80, 8), (0x78, 9), (0x70, 18), (0x68, 19), (0x60, 20), (0x58, 21), (0x50, 22),
    (0x48, 23)]

theorem gnSv_above {o : Nat} (ho : o ≤ 48) : ∀ q ∈ gnSv, o + 8 ≤ q.1 := by
  intro q hq; simp only [gnSv, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

/-- **`dc_getnum`'s fixed context**: its frame, the input (a string of the
state from byte `j0`, the reader's pointer owned), `mul_base_digits`. -/
structure GnCtx (S : Nat → Prop) (M0 : Mem) (sp : Nat) (G : DcG) (o : StrObj) (j0 : Nat) :
    Prop where
  cx : CfCtx S 144 sp
  mem : o ∈ G.strs
  j0 : j0 ≤ o.s.length
  own : ∀ a, InP a → S a
  mb : MulBase S M0

/-- The body's registers: the reader, `readahead`, `&_zero_`, `9`, the sign
character, `5`. -/
structure GnRegs (R : Nat → BitVec 64) (ra : Nat) (s6 : BitVec 64) : Prop where
  r18 : R 18 = 0x80000b70#64
  r19 : R 19 = BitVec.ofNat 64 ra
  r20 : R 20 = BitVec.ofNat 64 zeroAddr
  r21 : R 21 = 9#64
  r22 : R 22 = s6
  r23 : R 23 = 5#64

theorem GnRegs.keep {R R' : Nat → BitVec 64} {ra : Nat} {s6 : BitVec 64} (h : GnRegs R ra s6)
    {ks : List Nat} (k : Keeps ks R' R) (h18 : 18 ∉ ks := by decide) (h19 : 19 ∉ ks := by decide)
    (h20 : 20 ∉ ks := by decide) (h21 : 21 ∉ ks := by decide) (h22 : 22 ∉ ks := by decide)
    (h23 : 23 ∉ ks := by decide) : GnRegs R' ra s6 :=
  ⟨(k 18 h18).trans h.r18, (k 19 h19).trans h.r19, (k 20 h20).trans h.r20, (k 21 h21).trans h.r21,
    (k 22 h22).trans h.r22, (k 23 h23).trans h.r23⟩

/-- **The reader after the character at `j`** (in `s0`). -/
structure GnRd (M : Mem) (R : Nat → BitVec 64) (o : StrObj) (j0 j : Nat) : Prop where
  le : j ≤ (rdW o j0).length
  ch : R 8 = chW (rdW o j0)[j]?
  ptr : ldv .ld M inPtrAddr = BitVec.ofNat 64 (o.tb.pay + j0 + min (j + 1) (rdW o j0).length)

/-- **The integer loop's state** at `0x80002820`: `result` holds `v`, `temp`
and `build` a handle each, `base` the input base; the reader after `j`. -/
structure GnI (S : Nat → Prop) (M0 : Mem) (R0 : Nat → BitVec 64) (sp : Nat) (G : DcG)
    (hs0 : List GV) (st : St) (o : StrObj) (j0 ra : Nat) (s6 : BitVec 64) (L0 : List NumObj)
    (R : Nat → BitVec 64) (M : Mem) (j v : Nat) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (pr pt pd pb : Nat) : Prop where
  fr : CFr InP 144 gnSv M0 M R0 R sp
  h : DcAt S M H F L C G (.num pr :: .num pt :: .num pd :: .num pb :: hs0) st
  w16 : ldv .ld M (sp - 144 + 16) = BitVec.ofNat 64 pr
  w32 : ldv .ld M (sp - 144 + 32) = BitVec.ofNat 64 pt
  w24 : ldv .ld M (sp - 144 + 24) = BitVec.ofNat 64 pd
  w8 : ldv .ld M (sp - 144 + 8) = BitVec.ofNat 64 pb
  dr : (GV.num pr).Den ⟨L, G.strs⟩ (.num ⟨false, v, 0⟩)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num ⟨false, st.ibase, 0⟩)
  keep : HsKeep ⟨L0, G.strs⟩ ⟨L, G.strs⟩ hs0
  regs : GnRegs R ra s6
  rd : GnRd M R o j0 j

/-- The reader's character as an integer (`EOF` is `-1`). -/
def chI : Option Nat → Int
  | some c => c
  | none => -1

theorem chW_eq (x : Option Nat) : chW x = BitVec.ofInt 64 (chI x) := by
  cases x with
  | some c => simp [chW, chI]
  | none => rfl

/-- `addiw` of a negative immediate `-k` (the word `K`) to a character. -/
theorem sxw_addK {x : Int} {K k : Nat} (hK : K + k = 2 ^ 64) (h1 : -1 ≤ x) (h2 : x < 256)
    (hk : k ≤ 256) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofInt 64 x + BitVec.ofNat 64 K)) =
      BitVec.ofInt 64 (x - k) := by
  have e : BitVec.ofInt 64 x + BitVec.ofNat 64 K = BitVec.ofInt 64 (x - k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  rw [e]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.extractLsb_toNat, BitVec.toNat_ofInt]
  split <;> split <;> omega

theorem sxw_addK' {c K k : Nat} (hK : K + k = 2 ^ 64) (hc : c < 256) (hk : k ≤ 256) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (c + K))) =
      BitVec.ofInt 64 ((c : Int) - k) := by
  rw [← sxw_addK hK (by omega) (by omega) hk]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-- The frame with saved registers the body changed (`sp` kept). -/
theorem CFr.sregs {P : Nat → Prop} {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem} {R0 R R' : Nat → BitVec 64}
    {sp : Nat} (hfr : CFr P fs sv M0 M R0 R sp) (k : Keeps (sv.map Prod.snd ++ cClob) R' R)
    (h2 : R' 2 = R 2) : CFr P fs sv M0 M R0 R' sp where
  r2 := h2.trans hfr.r2
  saved := hfr.saved
  keep := fun z hz => by
    by_cases e : z = 2
    · subst e; exact h2.trans (hfr.keep 2 hz)
    · exact (k z fun hm => hz (List.mem_cons_of_mem _ hm)).trans (hfr.keep z hz)
  out := hfr.out

/-- The reader's pointer word through a callee. -/
theorem CfOut.inP {M M' : Mem} {sp fs o : Nat} (h : CfOut M M' sp fs o) (hab : heapEnd + cfW ≤ sp - fs) :
    ldv .ld M' inPtrAddr = ldv .ld M inPtrAddr :=
  ldv_congr .ld fun j hj => by
    have hp : InP (inPtrAddr + j) := by simp only [InP, widthOfM] at hj ⊢; omega
    exact h _ hp.off.1 hp.off.2 (fun hf => by simp only [frameIn, InP, inPtrAddr, heapEnd] at hf hp hab; omega)
      (fun hs => by simp only [slotBytes, InP, inPtrAddr, heapEnd] at hs hp hab; omega)

/-- `dc_getnum`'s out-of-memory continuation. -/
abbrev GnOom (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t : String) (M0 : Mem) (sp : Nat) : Prop :=
  ∀ R' M' sp', OomAt S sp (144 + cfW) M0 InP sp' R' M' → DWO live S Q t 0x80001e74#64 R' M'

/-- **One integer digit** (`0x800027e4`, the digit `d` in `s1`): read the
next character, `temp = d`, `result = result * base + temp`. -/
theorem gn_int_body {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (gx : GnCtx S M0 sp G o j0) (hhs : hs0.length + 6 ≤ 2 ^ 20)
    (hoom : GnOom live S Q t M0 sp) {R : Nat → BitVec 64} {M : Mem} {j v d : Nat} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {pr pt pd pb : Nat}
    (hI : GnI S M0 R0 sp G hs0 st o j0 ra s6 L0 R M j v H F L C pr pt pd pb)
    (hj : j < (rdW o j0).length) (hd : d < 16) (h9 : R 9 = BitVec.ofInt 64 d)
    (hnext : ∀ R' M' H' F' L' C' pr' pt',
      GnI S M0 R0 sp G hs0 st o j0 ra s6 L0 R' M' (j + 1) (v * st.ibase + d) H' F' L' C' pr' pt' pd pb →
      DWO live S Q t 0x80002820#64 R' M') :
    DWO live S Q t 0x800027e4#64 R M := by
  have cx := gx.cx
  have hab := cx.abv
  have hab' := cx.ab
  have hW : cfW = 176 + rmStack (2 ^ 30) := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hsf := cx.sf
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h := hI.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have q2 := hI.fr.r2
  have r18 := hI.regs.r18
  have jt : Sail.BitVec.update (0x80000b70#64) 0 0#1 = 0x80000b70#64 := jalr_tgt _ (by decide)
  bc_run hlive hS [q2, r18]
  · rw [jt]; decide
  rw [jt]
  refine cf_read hlive (hI.fr.regs (by keeps_tac Keeps.refl _ _)) cx.abv h gx.own gx.mem gx.j0 (j := j + 1) (by omega)
    (by rw [hI.rd.ptr, Nat.min_eq_left (by omega)]) (by bsimp []) fun R1 M1 hk1 e10 fr1 h1 hm1 hp1 => ?_
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  have q21 := fr1.r2
  have k9 : R1 9 = BitVec.ofInt 64 d := by rw [hk1 9 (by decide)]; bsimp [h9]
  bsimp []
  bc_run hlive hS1 [q21, k9] at 0x8000690c
  refine cf_i2n hlive cx (fr1.sregs (by keeps_tac Keeps.refl _ _) (by bsimp [q21])) (h1.perm (List.Perm.swap _ _ _))
    (gnSv_above (by omega)) (o := 32) (v := (d : Int)) (by omega) (by omega)
    ((ldv_inP hm1 (by simp only [heapEnd]; omega) _).trans hI.w32) (by bsimp [q21]) (by bsimp [k9])
    (by bsimp []) (by omega) (by omega) (fun R2 M2 H2 F2 L2 C2 y2 hk2 fr2 h2 hn2 hw2 ho2 hkp2 => ?_) hoom
  · have hS2 : HeapOwn S := fun a e1 e2 => h2.heap.heap.own a e1 e2
    have q22 := fr2.r2
    have l16 : ldv .ld M2 (sp - 144 + 16) = BitVec.ofNat 64 pr :=
      (ho2.word cx.abv (by omega)).trans ((ldv_inP hm1 (by simp only [heapEnd]; omega) _).trans hI.w16)
    have l8 : ldv .ld M2 (sp - 144 + 8) = BitVec.ofNat 64 pb :=
      (ho2.word cx.abv (by omega)).trans ((ldv_inP hm1 (by simp only [heapEnd]; omega) _).trans hI.w8)
    bsimp []
    bc_run hlive hS2 [q22, l16, l8] at 0x8000573c
    any_goals (exact frame_acc hsf (by omega) (by omega))
    have hcab : heapEnd + cfW ≤ sp - 144 := by simp only [heapEnd]; omega
    refine cf_mul hlive cx (fr2.regs (by keeps_tac Keeps.refl _ _)) (h2.perm (List.Perm.swap _ _ _))
      (fr2.mulBase cx.ab gx.mb fun a e1 e2 hp => by simp only [InP, inPtrAddr, mulBaseAddr] at e1 e2 hp; omega)
      (by simp only [List.length_cons]; omega) (gnSv_above (by omega)) (o := 16) (by omega) (by omega) l16
      (hkp2 _ List.mem_cons_self _ hI.dr) (hkp2 _ (by simp) _ hI.db) (k := 0) (by decide)
      (by bsimp []) (by bsimp []) (by bsimp [q22]) (by bsimp [] <;> rfl) (by bsimp [])
      (fun R3 M3 H3 F3 L3 C3 y3 hk3 fr3 h3 hn3 hw3 ho3 hkp3 => ?_) hoom
    have hS3 : HeapOwn S := fun a e1 e2 => h3.heap.heap.own a e1 e2
    have q23 := fr3.r2
    have l32 : ldv .ld M3 (sp - 144 + 32) = BitVec.ofNat 64 y2.rep.p := (ho3.word cx.abv (by omega)).trans hw2
    bsimp []
    bc_run hlive hS3 [q23, l32, hw3] at 0x80005634
    any_goals (exact frame_acc hsf (by omega) (by omega))
    refine cf_add hlive cx (fr3.regs (by keeps_tac Keeps.refl _ _)) h3 (gnSv_above (by omega)) (o := 16)
      (by omega) (by omega) hw3 (n1 := ⟨false, v * st.ibase, 0⟩) (n2 := ⟨false, d, 0⟩)
      ⟨y3, List.mem_cons_self, rfl, by rw [hn3, num_mul_int]⟩
      (hkp3 _ List.mem_cons_self _ ⟨y2, List.mem_cons_self, rfl, by rw [hn2, ofInt_nat]⟩) (smin := 0)
      (by decide) (by bsimp []) (by bsimp []) (by bsimp [q23]) (by bsimp [] <;> rfl) (by bsimp [])
      (fun R4 M4 H4 F4 L4 C4 y4 hk4 fr4 h4 hn4 hw4 ho4 hkp4 => ?_) hoom
    have kk : Keeps (8 :: cClob) R4 R :=
      (hk4.mono (by decide)).trans (by keeps_tac ((hk3.mono (by decide)).trans (by keeps_tac
        ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
          (by keeps_tac Keeps.refl _ _)))))))
    have k8 : R4 8 = R1 10 := by
      rw [hk4.get 8]; bsimp []; rw [hk3.get 8]; bsimp []; rw [hk2.get 8]; bsimp []
    have hsub : ∀ g ∈ hs0, ∀ l : List GV, g ∈ l ++ hs0 := fun g hg l => List.mem_append_right _ hg
    bsimp []
    exact hnext R4 M4 H4 F4 (y4 :: L4) C4 y4.rep.p y2.rep.p
      { fr := fr4
        h := h4
        w16 := hw4
        w32 := (ho4.word cx.abv (by omega)).trans l32
        w24 := (ho4.word cx.abv (by omega)).trans ((ho3.word cx.abv (by omega)).trans
          ((ho2.word cx.abv (by omega)).trans ((ldv_inP hm1 (by simp only [heapEnd]; omega) _).trans hI.w24)))
        w8 := (ho4.word cx.abv (by omega)).trans ((ho3.word cx.abv (by omega)).trans
          ((ho2.word cx.abv (by omega)).trans ((ldv_inP hm1 (by simp only [heapEnd]; omega) _).trans hI.w8)))
        dr := ⟨y4, List.mem_cons_self, rfl, by rw [hn4, num_add_int]⟩
        db := hkp4 _ (by simp) _ (hkp3 _ (by simp) _ (hkp2 _ (by simp) _ hI.db))
        keep := hI.keep.trans (((hkp2.mono fun g hg => hsub g hg [_, _, _]).trans
          (hkp3.mono fun g hg => hsub g hg [_, _, _])).trans (hkp4.mono fun g hg => hsub g hg [_, _, _]))
        regs := hI.regs.keep kk
        rd := ⟨by omega, k8.trans e10, (ho4.inP hcab).trans ((ho3.inP hcab).trans ((ho2.inP hcab).trans hp1))⟩ }

theorem digitVal_lo {c : Nat} (h1 : 48 ≤ c) (h2 : c ≤ 57) : digitVal c = some (c - 48) := by
  simp [digitVal, h1, h2]

theorem digitVal_hi {c : Nat} (h1 : 65 ≤ c) (h2 : c ≤ 70) : digitVal c = some (c - 55) := by
  have h3 : ¬ c ≤ 57 := by omega
  simp [digitVal, h1, h2, h3]

theorem digitVal_none {c : Nat} (h1 : ¬ (48 ≤ c ∧ c ≤ 57)) (h2 : ¬ (65 ≤ c ∧ c ≤ 70)) : digitVal c = none := by
  unfold digitVal
  split
  · rename_i h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
  · split
    · rename_i h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
    · rfl

theorem digitVal_lt {c d : Nat} (h : digitVal c = some d) : d < 16 := by
  by_cases h1 : 48 ≤ c ∧ c ≤ 57
  · rw [digitVal_lo h1.1 h1.2] at h; cases h; omega
  · by_cases h2 : 65 ≤ c ∧ c ≤ 70
    · rw [digitVal_hi h2.1 h2.2] at h; cases h; omega
    · rw [digitVal_none h1 h2] at h; cases h

theorem chI_bounds {ch : Option Nat} (hc : ∀ c, ch = some c → c < 256) : -1 ≤ chI ch ∧ chI ch < 256 := by
  cases ch with
  | none => simp [chI]
  | some c => have := hc c rfl; simp only [chI]; omega

/-- **The integer loop's test** at `0x80002820` on the character `ch` in `s0`:
a digit `d` to the body with `d` in `s1`, else to `0x80002834`. -/
theorem gn_head {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {R : Nat → BitVec 64} {M : Mem}
    {ch : Option Nat} (hc : ∀ c, ch = some c → c < 256)
    (h8 : R 8 = chW ch) (h21 : R 21 = 9#64) (h23 : R 23 = 5#64)
    (hdig : ∀ c d R', ch = some c → digitVal c = some d → Keeps [9, 11, 15] R' R →
      R' 9 = BitVec.ofInt 64 d → DWO live S Q t 0x800027e4#64 R' M)
    (hstop : ∀ R', (∀ c, ch = some c → digitVal c = none) → Keeps [9, 11, 15] R' R →
      DWO live S Q t 0x80002834#64 R' M) :
    DWO live S Q t 0x80002820#64 R M := by
  obtain ⟨hx1, hx2⟩ := chI_bounds hc
  rw [chW_eq] at h8
  bc_run hlive hS [h8, h21, h23] at 0x800027e4
  all_goals rw [sxw_addK (k := 48) rfl hx1 hx2 (by decide), sxw_addK (k := 65) rfl hx1 hx2 (by decide)]
  · intro hb
    rw [BitVec.toNat_ofInt] at hb
    cases ch with
    | none => simp [chI] at hb
    | some c =>
      simp only [chI] at hb hx2
      have hl : 48 ≤ c ∧ c ≤ 57 := by omega
      refine hdig c (c - 48) _ rfl (digitVal_lo hl.1 hl.2) (by keeps_tac Keeps.refl _ _) ?_
      bsimp []
      congr 1; simp only [chI]; omega
  · intro hb
    bc_run hlive hS [h8, h21, h23] at 0x80002834
    · intro hb'
      rw [BitVec.toNat_ofInt] at hb hb'
      bc_run hlive hS [h8] at 0x800027e4
      rw [sxw_addK (k := 55) rfl hx1 hx2 (by decide)]
      cases ch with
      | none => simp [chI] at hb'
      | some c =>
        simp only [chI] at hb hb' hx2
        have hl : 65 ≤ c ∧ c ≤ 70 := by omega
        refine hdig c (c - 55) _ rfl (digitVal_hi hl.1 hl.2) (by keeps_tac Keeps.refl _ _) ?_
        bsimp []
        congr 1; simp only [chI]; omega
    · intro hb'
      rw [BitVec.toNat_ofInt] at hb hb'
      refine hstop _ (fun c e => ?_) (by keeps_tac Keeps.refl _ _)
      subst e
      simp only [chI] at hb hb' hx2
      exact digitVal_none (by omega) (by omega)

/-- The integer loop's state with the registers the test changed. -/
theorem GnI.keepT {S : Nat → Prop} {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat} {G : DcG}
    {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64} {L0 : List NumObj}
    {R R' : Nat → BitVec 64} {M : Mem} {j v : Nat} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {pr pt pd pb : Nat} (hI : GnI S M0 R0 sp G hs0 st o j0 ra s6 L0 R M j v H F L C pr pt pd pb)
    (k : Keeps [9, 11, 15] R' R) : GnI S M0 R0 sp G hs0 st o j0 ra s6 L0 R' M j v H F L C pr pt pd pb :=
  { hI with
    fr := hI.fr.sregs (k.mono (by decide)) (k.get 2)
    regs := hI.regs.keep k
    rd := { hI.rd with ch := (k.get 8).trans hI.rd.ch } }

/-- The digit value read as `ofDigits` continues. -/
abbrev digF (ib : Nat) : Nat → Nat → Nat := fun r d => r * ib + d

/-- **The integer loop** from `0x80002820`: the digits from `j` folded into
`result`, ending at the first non-digit. -/
theorem gn_int {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (gx : GnCtx S M0 sp G o j0) (hhs : hs0.length + 6 ≤ 2 ^ 20)
    (hoom : GnOom live S Q t M0 sp) {pd pb : Nat} :
    ∀ (n j v : Nat) (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
      (C : BcConsts) (pr pt : Nat), (rdW o j0).length - j = n →
      GnI S M0 R0 sp G hs0 st o j0 ra s6 L0 R M j v H F L C pr pt pd pb →
      (∀ R' M' H' F' L' C' pr' pt',
        GnI S M0 R0 sp G hs0 st o j0 ra s6 L0 R' M' (j + (takeDigits ((rdW o j0).drop j)).1.length)
          ((takeDigits ((rdW o j0).drop j)).1.foldl (digF st.ibase) v) H' F' L' C' pr' pt' pd pb →
        DWO live S Q t 0x80002834#64 R' M') →
      DWO live S Q t 0x80002820#64 R M := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro j v R M H F L C pr pt hn hI hk
  have h := hI.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hr := h.rd gx.mem gx.j0
  refine gn_head hlive hS (ch := (rdW o j0)[j]?) (fun c e => hr.lt c (List.mem_of_getElem? e)) hI.rd.ch
    hI.regs.r21 hI.regs.r23 (fun c d R' e hdv k h9 => ?_) (fun R' hst k => ?_)
  · have hj : j < (rdW o j0).length := by
      rcases Nat.lt_or_ge j (rdW o j0).length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at e; cases e
    have hc : (rdW o j0).getD j 0 = c := by rw [getElem?_of_lt hj] at e; exact Option.some.inj e
    have hd : digitVal ((rdW o j0).getD j 0) = some d := hc ▸ hdv
    refine gn_int_body hlive gx hhs hoom (hI.keepT k) hj (digitVal_lt hdv) h9
      fun R2 M2 H2 F2 L2 C2 pr2 pt2 hI2 => ih _ (by omega) (j + 1) _ R2 M2 H2 F2 L2 C2 pr2 pt2 rfl hI2
        fun R3 M3 H3 F3 L3 C3 pr3 pt3 hI3 => hk R3 M3 H3 F3 L3 C3 pr3 pt3 ?_
    rw [takeDigits_drop_digit hj hd]
    simp only [List.length_cons, List.foldl_cons]
    rwa [show j + ((takeDigits ((rdW o j0).drop (j + 1))).1.length + 1) =
      j + 1 + (takeDigits ((rdW o j0).drop (j + 1))).1.length by omega]
  · refine hk R' M H F L C pr pt ?_
    rw [takeDigits_drop_stop hst]
    simpa using hI.keepT k

/-! ## The fraction loop -/

/-- **The fraction loop's state** at `0x80002968` after `k` fraction digits:
`result` holds `vI`, `build` holds `u`, `divisor` holds `ibase ^ k`, `temp`
a handle or `NULL`, `base` the input base; `s1 = k`. -/
structure GnF (S : Nat → Prop) (M0 : Mem) (R0 : Nat → BitVec 64) (sp : Nat) (G : DcG)
    (hs0 : List GV) (st : St) (ra : Nat) (s6 : BitVec 64) (L0 : List NumObj)
    (R : Nat → BitVec 64) (M : Mem) (k vI u : Nat) (og : Option Nat) (H : Heap) (F : List Blk)
    (L : List NumObj) (C : BcConsts) (pr pd pv pb : Nat) : Prop where
  fr : CFr InP 144 gnSv M0 M R0 R sp
  h : DcAt S M H F L C G (.num pr :: .num pd :: .num pv :: .num pb :: (slotHs og ++ hs0)) st
  w16 : ldv .ld M (sp - 144 + 16) = BitVec.ofNat 64 pr
  w24 : ldv .ld M (sp - 144 + 24) = BitVec.ofNat 64 pd
  w32 : ldv .ld M (sp - 144 + 32) = BitVec.ofNat 64 (og.getD 0)
  w40 : ldv .ld M (sp - 144 + 40) = BitVec.ofNat 64 pv
  w8 : ldv .ld M (sp - 144 + 8) = BitVec.ofNat 64 pb
  dr : (GV.num pr).Den ⟨L, G.strs⟩ (.num ⟨false, vI, 0⟩)
  dd : (GV.num pd).Den ⟨L, G.strs⟩ (.num ⟨false, u, 0⟩)
  dv : (GV.num pv).Den ⟨L, G.strs⟩ (.num ⟨false, st.ibase ^ k, 0⟩)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num ⟨false, st.ibase, 0⟩)
  keep : HsKeep ⟨L0, G.strs⟩ ⟨L, G.strs⟩ hs0
  regs : GnRegs R ra s6
  r9 : R 9 = BitVec.ofNat 64 k
  z0 : k = 0 → pd = C.z.rep.p

theorem slotHs_perm (a b c d : GV) (og : Option Nat) (l : List GV) :
    (a :: b :: c :: d :: (slotHs og ++ l)).Perm (slotHs og ++ a :: b :: c :: d :: l) := by
  cases og with
  | none => exact List.Perm.refl _
  | some x => exact List.perm_middle (l₁ := [a, b, c, d])

/-- **The fraction loop's test** at `0x8000296c` on the character `ch` read
into `a0`: a digit `d` to the body with `d` in `a1`, else to `0x80002980`. -/
theorem gnf_test {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {R : Nat → BitVec 64} {M : Mem}
    {ch : Option Nat} (hc : ∀ c, ch = some c → c < 256)
    (h10 : R 10 = chW ch) (h21 : R 21 = 9#64) (h23 : R 23 = 5#64)
    (hdig : ∀ c d R', ch = some c → digitVal c = some d → Keeps [8, 11, 15] R' R →
      R' 11 = BitVec.ofInt 64 d → R' 8 = chW ch → DWO live S Q t 0x80002920#64 R' M)
    (hstop : ∀ R', (∀ c, ch = some c → digitVal c = none) → Keeps [8, 11, 15] R' R →
      R' 8 = chW ch → DWO live S Q t 0x80002980#64 R' M) :
    DWO live S Q t 0x8000296c#64 R M := by
  obtain ⟨hx1, hx2⟩ := chI_bounds hc
  rw [chW_eq] at h10
  bc_run hlive hS [h10, h21, h23] at 0x80002920
  all_goals rw [sxw_addK (k := 48) rfl hx1 hx2 (by decide), sxw_addK (k := 65) rfl hx1 hx2 (by decide)]
  · intro hb
    rw [BitVec.toNat_ofInt] at hb
    cases ch with
    | none => simp [chI] at hb
    | some c =>
      simp only [chI] at hb hx2
      have hl : 48 ≤ c ∧ c ≤ 57 := by omega
      refine hdig c (c - 48) _ rfl (digitVal_lo hl.1 hl.2) (by keeps_tac Keeps.refl _ _) ?_ (by bsimp []; exact (chW_eq _).symm)
      bsimp []
      congr 1; simp only [chI]; omega
  · intro hb
    bc_run hlive hS [h10, h21, h23] at 0x80002980
    · intro hb'
      rw [BitVec.toNat_ofInt] at hb hb'
      bc_run hlive hS [h10] at 0x80002920
      rw [sxw_addK (k := 55) rfl hx1 hx2 (by decide)]
      cases ch with
      | none => simp [chI] at hb'
      | some c =>
        simp only [chI] at hb hb' hx2
        have hl : 65 ≤ c ∧ c ≤ 70 := by omega
        refine hdig c (c - 55) _ rfl (digitVal_hi hl.1 hl.2) (by keeps_tac Keeps.refl _ _) ?_ (by bsimp []; exact (chW_eq _).symm)
        bsimp []
        congr 1; simp only [chI]; omega
    · intro hb'
      rw [BitVec.toNat_ofInt] at hb hb'
      refine hstop _ (fun c e => ?_) (by keeps_tac Keeps.refl _ _) (by bsimp []; exact (chW_eq _).symm)
      subst e
      simp only [chI] at hb hb' hx2
      exact digitVal_none (by omega) (by omega)

/-- **One fraction digit** (`0x80002920`, the digit `d` in `a1`):
`temp = d`, `build = build * base + temp`, `divisor *= base`, `s1 += 1`. -/
theorem gnf_body {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (gx : GnCtx S M0 sp G o j0) (hhs : hs0.length + 6 ≤ 2 ^ 20)
    (hoom : GnOom live S Q t M0 sp) {R : Nat → BitVec 64} {M : Mem} {k vI u d : Nat} {og : Option Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {pr pd pv pb : Nat}
    (hF : GnF S M0 R0 sp G hs0 st ra s6 L0 R M k vI u og H F L C pr pd pv pb)
    (hk : k + 1 < 2 ^ 31) (hd : d < 16) (h11 : R 11 = BitVec.ofInt 64 d)
    (hnext : ∀ R' M' H' F' L' C' y pd' pv', Keeps (9 :: cClob) R' R →
      GnF S M0 R0 sp G hs0 st ra s6 L0 R' M' (k + 1) vI (u * st.ibase + d) (some y) H' F' L' C'
        pr pd' pv' pb → ldv .ld M' inPtrAddr = ldv .ld M inPtrAddr →
      DWO live S Q t 0x80002968#64 R' M') :
    DWO live S Q t 0x80002920#64 R M := by
  have cx := gx.cx
  have hab := cx.abv
  have hab' := cx.ab
  have hW : cfW = 176 + rmStack (2 ^ 30) := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hsf := cx.sf
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab hab'
  have hcab : heapEnd + cfW ≤ sp - 144 := by simp only [heapEnd]; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h := hF.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have q2 := hF.fr.r2
  bc_run hlive hS [q2, h11] at 0x8000690c
  refine cf_i2nO hlive cx (hF.fr.regs (by keeps_tac Keeps.refl _ _)) (h.perm (slotHs_perm _ _ _ _ _ _))
    (gnSv_above (by omega)) (o := 32) (v := (d : Int)) (by omega) (by omega) hF.w32 (by bsimp [q2])
    (by bsimp [h11]) (by bsimp []) (by omega) (by omega)
    (fun R2 M2 H2 F2 L2 C2 y1 hk2 fr2 h2 hn2 hw2 ho2 hkp2 => ?_) hoom
  have hS2 : HeapOwn S := fun a e1 e2 => h2.heap.heap.own a e1 e2
  have q22 := fr2.r2
  have l24 : ldv .ld M2 (sp - 144 + 24) = BitVec.ofNat 64 pd := (ho2.word cx.abv (by omega)).trans hF.w24
  have l8 : ldv .ld M2 (sp - 144 + 8) = BitVec.ofNat 64 pb := (ho2.word cx.abv (by omega)).trans hF.w8
  bsimp []
  bc_run hlive hS2 [q22, l24, l8] at 0x8000573c
  any_goals (exact frame_acc hsf (by omega) (by omega))
  refine cf_mul hlive cx (fr2.regs (by keeps_tac Keeps.refl _ _)) (h2.perm (perm_rev3 _ _ _ _))
    (fr2.mulBase cx.ab gx.mb fun a e1 e2 hp => by simp only [InP, inPtrAddr, mulBaseAddr] at e1 e2 hp; omega)
    (by simp only [List.length_cons]; omega) (gnSv_above (by omega)) (o := 24) (by omega) (by omega) l24
    (hkp2 _ (by simp) _ hF.dd) (hkp2 _ (by simp) _ hF.db) (k := 0) (by decide)
    (by bsimp []) (by bsimp []) (by bsimp [q22]) (by bsimp [] <;> rfl) (by bsimp [])
    (fun R3 M3 H3 F3 L3 C3 y2 hk3 fr3 h3 hn3 hw3 ho3 hkp3 => ?_) hoom
  have hS3 : HeapOwn S := fun a e1 e2 => h3.heap.heap.own a e1 e2
  have q23 := fr3.r2
  have l32 : ldv .ld M3 (sp - 144 + 32) = BitVec.ofNat 64 y1.rep.p := (ho3.word cx.abv (by omega)).trans hw2
  bsimp []
  bc_run hlive hS3 [q23, l32, hw3] at 0x80005634
  any_goals (exact frame_acc hsf (by omega) (by omega))
  refine cf_add hlive cx (fr3.regs (by keeps_tac Keeps.refl _ _)) h3 (gnSv_above (by omega)) (o := 24)
    (by omega) (by omega) hw3 (n1 := ⟨false, u * st.ibase, 0⟩) (n2 := ⟨false, d, 0⟩)
    ⟨y2, List.mem_cons_self, rfl, by rw [hn3, num_mul_int]⟩
    (hkp3 _ (by simp) _ ⟨y1, List.mem_cons_self, rfl, by rw [hn2, ofInt_nat]⟩) (smin := 0)
    (by decide) (by bsimp []) (by bsimp []) (by bsimp [q23]) (by bsimp [] <;> rfl) (by bsimp [])
    (fun R4 M4 H4 F4 L4 C4 y3 hk4 fr4 h4 hn4 hw4 ho4 hkp4 => ?_) hoom
  have hS4 : HeapOwn S := fun a e1 e2 => h4.heap.heap.own a e1 e2
  have q24 := fr4.r2
  have m8 : ldv .ld M4 (sp - 144 + 8) = BitVec.ofNat 64 pb :=
    (ho4.word cx.abv (by omega)).trans ((ho3.word cx.abv (by omega)).trans l8)
  have m40 : ldv .ld M4 (sp - 144 + 40) = BitVec.ofNat 64 pv :=
    (ho4.word cx.abv (by omega)).trans ((ho3.word cx.abv (by omega)).trans
      ((ho2.word cx.abv (by omega)).trans hF.w40))
  bsimp []
  bc_run hlive hS4 [q24, m8, m40] at 0x8000573c
  any_goals (exact frame_acc hsf (by omega) (by omega))
  refine cf_mul hlive cx (fr4.regs (by keeps_tac Keeps.refl _ _)) (h4.perm (perm_4th _ _ _ _ _))
    (fr4.mulBase cx.ab gx.mb fun a e1 e2 hp => by simp only [InP, inPtrAddr, mulBaseAddr] at e1 e2 hp; omega)
    (by simp only [List.length_cons]; omega) (gnSv_above (by omega)) (o := 40) (by omega) (by omega) m40
    (hkp4 _ (by simp) _ (hkp3 _ (by simp) _ (hkp2 _ (by simp) _ hF.dv)))
    (hkp4 _ (by simp) _ (hkp3 _ (by simp) _ (hkp2 _ (by simp) _ hF.db))) (k := 0) (by decide)
    (by bsimp []) (by bsimp []) (by bsimp [q24]) (by bsimp [] <;> rfl) (by bsimp [])
    (fun R5 M5 H5 F5 L5 C5 y4 hk5 fr5 h5 hn5 hw5 ho5 hkp5 => ?_) hoom
  have hS5 : HeapOwn S := fun a e1 e2 => h5.heap.heap.own a e1 e2
  have kk : Keeps cClob R5 R :=
    (hk5.mono (by decide)).trans (by keeps_tac ((hk4.mono (by decide)).trans (by keeps_tac
      ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))))))
  have r9 : R5 9 = BitVec.ofNat 64 k := (kk.get 9).trans hF.r9
  have wp := word_succ k
  have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (k + 1))) =
      BitVec.ofNat 64 (k + 1) := sxw_ofNat hk
  bsimp []
  bc_run hlive hS5 [r9, wp, wq] at 0x80002968
  have hsub : ∀ g ∈ hs0, ∀ l : List GV, g ∈ l ++ hs0 := fun g hg l => List.mem_append_right _ hg
  have hP : (GV.num y4.rep.p :: .num y3.rep.p :: .num pr :: .num y1.rep.p :: .num pb :: hs0).Perm
      (.num pr :: .num y3.rep.p :: .num y4.rep.p :: .num pb :: (slotHs (some y1.rep.p) ++ hs0)) :=
    (perm_rev3 _ _ _ _).trans (.cons _ (.cons _ (.cons _ (.swap _ _ _))))
  refine hnext _ M5 H5 F5 (y4 :: L5) C5 y1.rep.p y3.rep.p y4.rep.p
    ((Keeps.upd _ (by decide) (kk.mono (by decide))))
    { fr := fr5.sregs ((Keeps.upd (ks := [9]) _ (by decide) (Keeps.refl _ _)).mono (by decide)) (by bsimp [])
      h := h5.perm hP
      w16 := (ho5.word cx.abv (by omega)).trans ((ho4.word cx.abv (by omega)).trans
        ((ho3.word cx.abv (by omega)).trans ((ho2.word cx.abv (by omega)).trans hF.w16)))
      w24 := (ho5.word cx.abv (by omega)).trans hw4
      w32 := (ho5.word cx.abv (by omega)).trans ((ho4.word cx.abv (by omega)).trans l32)
      w40 := hw5
      w8 := (ho5.word cx.abv (by omega)).trans m8
      dr := hkp5 _ (by simp) _ (hkp4 _ (by simp) _ (hkp3 _ (by simp) _ (hkp2 _ (by simp) _ hF.dr)))
      dd := hkp5 _ (by simp) _ ⟨y3, List.mem_cons_self, rfl, by rw [hn4, num_add_int]⟩
      dv := ⟨y4, List.mem_cons_self, rfl, by rw [hn5, num_mul_int, Nat.pow_succ]⟩
      db := hkp5 _ (by simp) _ (hkp4 _ (by simp) _ (hkp3 _ (by simp) _ (hkp2 _ (by simp) _ hF.db)))
      keep := hF.keep.trans ((((hkp2.mono fun g hg => hsub g hg [_, _, _, _]).trans
        (hkp3.mono fun g hg => hsub g hg [_, _, _, _])).trans
        (hkp4.mono fun g hg => hsub g hg [_, _, _, _])).trans (hkp5.mono fun g hg => hsub g hg [_, _, _, _]))
      regs := hF.regs.keep ((Keeps.upd _ (by decide) (kk.mono (by decide))) : Keeps (9 :: cClob) _ R)
      r9 := by bsimp []
      z0 := fun e => absurd e (Nat.succ_ne_zero k) }
    ((ho5.inP hcab).trans ((ho4.inP hcab).trans ((ho3.inP hcab).trans (ho2.inP hcab))))

theorem Rd.len_lt {M : Mem} {src : Nat} {w : List Nat} (hr : Rd M src w) : w.length < 2 ^ 27 := by
  have := hr.lo; have := hr.hi; simp only [heapStart, heapEnd] at *; omega

/-- The fraction loop's state after `input_str`. -/
theorem GnF.read {S : Nat → Prop} {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat} {G : DcG}
    {hs0 : List GV} {st : St} {ra : Nat} {s6 : BitVec 64} {L0 : List NumObj}
    {R R' : Nat → BitVec 64} {M M' : Mem} {k vI u : Nat} {og : Option Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {pr pd pv pb : Nat}
    (hF : GnF S M0 R0 sp G hs0 st ra s6 L0 R M k vI u og H F L C pr pd pv pb)
    (fr : CFr InP 144 gnSv M0 M' R0 R' sp)
    (h : DcAt S M' H F L C G (.num pr :: .num pd :: .num pv :: .num pb :: (slotHs og ++ hs0)) st)
    (kp : Keeps [1, 10, 14, 15] R' R) (hm : MemOnly InP M' M) (hab : heapEnd ≤ sp - 144) :
    GnF S M0 R0 sp G hs0 st ra s6 L0 R' M' k vI u og H F L C pr pd pv pb :=
  { hF with
    fr := fr
    h := h
    w16 := (ldv_inP hm (by omega) _).trans hF.w16
    w24 := (ldv_inP hm (by omega) _).trans hF.w24
    w32 := (ldv_inP hm (by omega) _).trans hF.w32
    w40 := (ldv_inP hm (by omega) _).trans hF.w40
    w8 := (ldv_inP hm (by omega) _).trans hF.w8
    regs := hF.regs.keep kp
    r9 := (kp.get 9).trans hF.r9 }

/-- The fraction loop's state with the registers the test changed. -/
theorem GnF.keepT {S : Nat → Prop} {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat} {G : DcG}
    {hs0 : List GV} {st : St} {ra : Nat} {s6 : BitVec 64} {L0 : List NumObj}
    {R R' : Nat → BitVec 64} {M : Mem} {k vI u : Nat} {og : Option Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {pr pd pv pb : Nat}
    (hF : GnF S M0 R0 sp G hs0 st ra s6 L0 R M k vI u og H F L C pr pd pv pb)
    (kp : Keeps [8, 11, 15] R' R) : GnF S M0 R0 sp G hs0 st ra s6 L0 R' M k vI u og H F L C pr pd pv pb :=
  { hF with
    fr := hF.fr.sregs (kp.mono (by decide)) (kp.get 2)
    regs := hF.regs.keep kp
    r9 := (kp.get 9).trans hF.r9 }

/-- **The fraction loop** from `0x80002968`, the character at `j` read last:
the digits from `j + 1` folded into `build`, `divisor` multiplied by the base
for each, ending at the first non-digit. -/
theorem gnf_loop {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (gx : GnCtx S M0 sp G o j0) (hhs : hs0.length + 6 ≤ 2 ^ 20)
    (hoom : GnOom live S Q t M0 sp) {vI pr pb : Nat} :
    ∀ (n j k u : Nat) (R : Nat → BitVec 64) (M : Mem) (og : Option Nat) (H : Heap) (F : List Blk)
      (L : List NumObj) (C : BcConsts) (pd pv : Nat), (rdW o j0).length - j = n →
      j < (rdW o j0).length → k ≤ j →
      GnF S M0 R0 sp G hs0 st ra s6 L0 R M k vI u og H F L C pr pd pv pb → GnRd M R o j0 j →
      (∀ R' M' og' H' F' L' C' pd' pv',
        GnF S M0 R0 sp G hs0 st ra s6 L0 R' M' (k + (takeDigits ((rdW o j0).drop (j + 1))).1.length) vI
          ((takeDigits ((rdW o j0).drop (j + 1))).1.foldl (digF st.ibase) u) og' H' F' L' C' pr pd' pv' pb →
        GnRd M' R' o j0 (j + 1 + (takeDigits ((rdW o j0).drop (j + 1))).1.length) →
        DWO live S Q t 0x80002980#64 R' M') →
      DWO live S Q t 0x80002968#64 R M := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro j k u R M og H F L C pd pv hn hj hkj hF hrd hk
  have cx := gx.cx
  have hab := cx.abv
  have h := hF.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hr := h.rd gx.mem gx.j0
  have hwl := hr.len_lt
  have q2 := hF.fr.r2
  have r18 := hF.regs.r18
  have jt : Sail.BitVec.update (0x80000b70#64) 0 0#1 = 0x80000b70#64 := jalr_tgt _ (by decide)
  bc_run hlive hS [q2, r18]
  · rw [jt]; decide
  rw [jt]
  refine cf_read hlive (hF.fr.regs (by keeps_tac Keeps.refl _ _)) cx.abv h gx.own gx.mem gx.j0 (j := j + 1)
    (by omega) (by rw [hrd.ptr, Nat.min_eq_left (by omega)]) (by bsimp [])
    fun R1 M1 hk1 e10 fr1 h1 hm1 hp1 => ?_
  have hF1 := hF.read fr1 h1 ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) hm1 cx.abv
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  bsimp []
  refine gnf_test hlive hS1 (ch := (rdW o j0)[j + 1]?) (fun c e => hr.lt c (List.mem_of_getElem? e)) e10
    hF1.regs.r21 hF1.regs.r23 (fun c d R2 e hdv k2 h11 h8 => ?_) (fun R2 hst k2 h8 => ?_)
  · have hj1 : j + 1 < (rdW o j0).length := by
      rcases Nat.lt_or_ge (j + 1) (rdW o j0).length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at e; cases e
    have hc : (rdW o j0).getD (j + 1) 0 = c := by rw [getElem?_of_lt hj1] at e; exact Option.some.inj e
    have hd : digitVal ((rdW o j0).getD (j + 1) 0) = some d := hc ▸ hdv
    refine gnf_body hlive gx hhs hoom (hF1.keepT k2) (by omega) (digitVal_lt hdv) h11
      fun R3 M3 H3 F3 L3 C3 y pd' pv' k3 hF3 hp3 => ih _ (by omega) (j + 1) (k + 1) (u * st.ibase + d) R3 M3 (some y) H3 F3
        L3 C3 pd' pv' rfl hj1 (by omega) hF3 ⟨by omega, (k3.get 8).trans h8, hp3.trans hp1⟩
        fun R4 M4 og4 H4 F4 L4 C4 pd4 pv4 hF4 hrd4 => hk R4 M4 og4 H4 F4 L4 C4 pd4 pv4 ?_ ?_
    · rw [takeDigits_drop_digit hj1 hd]
      simp only [List.length_cons, List.foldl_cons]
      rwa [show k + ((takeDigits ((rdW o j0).drop (j + 1 + 1))).1.length + 1) =
        k + 1 + (takeDigits ((rdW o j0).drop (j + 1 + 1))).1.length by omega]
    · rw [takeDigits_drop_digit hj1 hd]
      simp only [List.length_cons]
      rwa [show j + 1 + ((takeDigits ((rdW o j0).drop (j + 1 + 1))).1.length + 1) =
        j + 1 + 1 + (takeDigits ((rdW o j0).drop (j + 1 + 1))).1.length by omega]
  · refine hk R2 M1 og H F L C pd pv ?_ ?_
    · rw [takeDigits_drop_stop hst]
      simpa using hF1.keepT k2
    · rw [takeDigits_drop_stop hst]
      exact ⟨by simp only [List.length_nil]; omega, by simpa using h8, by simpa using hp1⟩

end Dc.Mach