import Dc.Mach.DcGetnumFrac

/-!
# `dc_getnum` (M9)

    dc_data dc_getnum (int (*input) (void), int ibase, int *readahead)

The prologue (`gn_pro1`, `gn_pro2`), the first character and the `_` path
with its space skip (`gn_first`, `gn_sp`), and the whole function
`dc_getnum_spec`: the number `readNum ibase w` of the text `w` the reader
returns, the reader after the first character not consumed.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

theorem word_sub144 {x : Nat} (h : 144 ≤ x) :
    BitVec.ofNat 64 x + 18446744073709551472#64 = BitVec.ofNat 64 (x - 144) := by
  change BitVec.ofNat 64 x + -(144#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le x 144 (by decide) h

/-- **`dc_getnum`'s prologue** to the first `bc_init_num`: the frame. -/
theorem gn_pro1 {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {sp : Nat}
    (h : DcAt S M H F L C G hs st) (cx : CfCtx S 144 sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hk : ∀ R1 M1, CFr InP 144 gnSv M M1 R R1 sp → DcAt S M1 H F L C G hs st →
      Keeps [1, 2, 8, 10, 18, 19] R1 R → R1 18 = R 10 → R1 8 = R 11 → R1 19 = R 12 →
      R1 10 = BitVec.ofNat 64 (sp - 144 + 32) → R1 1 = 0x80002750#64 → MemOnly (frameIn sp 144) M1 M →
      DWO live S Q t 0x800049bc#64 R1 M1) :
    DWO live S Q t 0x80002714#64 R M := by
  have hab := cx.abv
  have hab' := cx.ab
  have hsf := cx.sf
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  bc_run hlive hS [h2, word_sub144 (x := sp) (by omega)] at 0x800049bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  generalize hM1 : writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog
    (writeLog M [(sp - 144 + 112, 8, R 18)]) [(sp - 144 + 136, 8, R 1)]) [(sp - 144 + 128, 8, R 8)])
    [(sp - 144 + 104, 8, R 19)]) [(sp - 144 + 96, 8, R 20)]) [(sp - 144 + 120, 8, R 9)])
    [(sp - 144 + 88, 8, R 21)]) [(sp - 144 + 80, 8, R 22)]) [(sp - 144 + 72, 8, R 23)] = M1
  have hm1 : MemOnly (frameIn sp 144) M1 M := fun a ha => by
    rw [← hM1]; simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hab2 : heapEnd ≤ sp - 144 := by simp only [heapEnd]; omega
  have hP : ∀ a, frameIn sp 144 a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
     (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have sv : ∀ q ∈ gnSv, ldv .ld M1 (sp - 144 + q.1) = R q.2 := by
    intro q hq
    simp only [gnSv, List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [← hM1]
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only <;> repeat (first | rw [ldv_store_hit] | rw [ldv_ld_miss _ _ (by omega)])
  refine hk _ M1 ⟨by bsimp [], sv, by keeps_tac Keeps.refl _ _, fun a _ _ hf _ =>
      hm1 a fun h => hf (by simp only [frameIn] at h ⊢; omega)⟩
    (h.outWrite hm1 hP) (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
    (by bsimp []) hm1

theorem sltiu_ne0 (a b : BitVec 64) :
    (zero_extend (bool_to_bit (zopz0zI_u a b)) ≠ 0#64) ↔ a.toNat < b.toNat := by
  rcases Bool.eq_false_or_eq_true (zopz0zI_u a b) with e | e
  · rw [e]; exact ⟨fun _ => (ult_iff a b).mp e, fun _ => by decide⟩
  · rw [e]; exact ⟨fun h => absurd (by decide) h, fun h => absurd ((ult_iff a b).mpr h) (by simp [e])⟩

theorem sltiu_eq0 (a b : BitVec 64) :
    (zero_extend (bool_to_bit (zopz0zI_u a b)) = 0#64) ↔ ¬ a.toNat < b.toNat := by
  rw [← sltiu_ne0, ne_eq, Decidable.not_not]

theorem ofInt_toNat_lt5 {y : Int} (h1 : -265 ≤ y) (h2 : y < 256) :
    (BitVec.ofInt 64 y).toNat < (5#64).toNat ↔ 0 ≤ y ∧ y < 5 := by
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]; omega

theorem ofInt_add_eq0 {x : Int} {K k : Nat} (hK : K + k = 2 ^ 64) (hk : k ≤ 256) (h1 : -1 ≤ x)
    (h2 : x < 256) : BitVec.ofInt 64 x + BitVec.ofNat 64 K = 0#64 ↔ x = k := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat] at this
    omega
  · intro e; subst e
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega

theorem isSpace_iff (c : Nat) : isSpace c = true ↔ c = 32 ∨ (9 ≤ c ∧ c ≤ 13) := by
  simp [isSpace]

/-- **The space test** at `0x800028b4` on the character `ch` read into `a0`
(`s0 = a0`): a space back to `0x800028b0`, else to `0x800027d4`. -/
theorem gn_sptest {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {R : Nat → BitVec 64} {M : Mem}
    {ch : Option Nat} (hc : ∀ c, ch = some c → c < 256) (h10 : R 10 = chW ch)
    (hsp : ∀ R', (∃ c, ch = some c ∧ isSpace c = true) → Keeps [8, 14, 15] R' R →
      DWO live S Q t 0x800028b0#64 R' M)
    (hno : ∀ R', (∀ c, ch = some c → isSpace c = false) → Keeps [8, 14, 15] R' R → R' 8 = chW ch →
      DWO live S Q t 0x800027d4#64 R' M) :
    DWO live S Q t 0x800028b4#64 R M := by
  obtain ⟨hx1, hx2⟩ := chI_bounds hc
  rw [chW_eq] at h10
  bc_run hlive hS [h10] at 0x800028b0
  all_goals rw [sxw_addK (k := 9) rfl hx1 hx2 (by decide), sltiu_ne0, ofInt_toNat_lt5 (by omega) (by omega)]
  · intro hb
    refine hsp _ ?_ (by keeps_tac Keeps.refl _ _)
    cases ch with
    | none => simp [chI] at hb
    | some c => exact ⟨c, rfl, (isSpace_iff c).mpr (.inr (by simp only [chI] at hb; omega))⟩
  · intro hb
    bc_run hlive hS [h10] at 0x800027d4
    all_goals rw [ofInt_add_eq0 (k := 32) rfl (by decide) hx1 hx2]
    · intro e
      refine hsp _ ?_ (by keeps_tac Keeps.refl _ _)
      cases ch with
      | none => simp [chI] at e
      | some c => exact ⟨c, rfl, (isSpace_iff c).mpr (.inl (by simp only [chI] at e; omega))⟩
    · intro e
      bc_run hlive hS [] at 0x800027d4
      refine hno _ (fun c ec => ?_) (by keeps_tac Keeps.refl _ _) (by bsimp []; exact (chW_eq _).symm)
      subst ec
      simp only [chI] at hb e
      cases hsc : isSpace c
      · rfl
      · rw [isSpace_iff] at hsc; omega

theorem ofInt_eq_lit {x : Int} {k : Nat} (hk : k < 256) (h1 : -1 ≤ x) (h2 : x < 256) :
    BitVec.ofInt 64 x = BitVec.ofNat 64 k ↔ x = k := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat] at this
    omega
  · intro e; subst e
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega

/-- **The first character** `dc_getnum` may see (evalstr's dispatch): a
digit, `_` or `.`. -/
def HeadOK : Option Nat → Prop
  | some c => c = 95 ∨ c = 46 ∨ (digitVal c).isSome
  | none => False

theorem HeadOK.range {c : Nat} (h : HeadOK (some c)) :
    c = 95 ∨ c = 46 ∨ (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 70) := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · by_cases h1 : 48 ≤ c ∧ c ≤ 57
    · exact .inr (.inr (.inl h1))
    · by_cases h2 : 65 ≤ c ∧ c ≤ 70
      · exact .inr (.inr (.inr h2))
      · rw [digitVal_none h1 h2] at h; cases h

/-- **The first character's test** at `0x80002784` (`a0`): `_` to
`0x8000289c`, a digit or `.` to `0x800027d4` with `s6 = 0`. -/
theorem gn_htest {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {R : Nat → BitVec 64} {M : Mem}
    {ch : Option Nat} (hhd : HeadOK ch) (h10 : R 10 = chW ch)
    (hus : ∀ R', ch = some 95 → Keeps [8, 15] R' R → R' 8 = chW ch → DWO live S Q t 0x8000289c#64 R' M)
    (hdg : ∀ R', ch ≠ some 95 → Keeps [8, 15, 22] R' R → R' 8 = chW ch → R' 22 = 0#64 →
      DWO live S Q t 0x800027d4#64 R' M) :
    DWO live S Q t 0x80002784#64 R M := by
  cases ch with
  | none => exact hhd.elim
  | some c =>
  have hr := hhd.range
  have hx1 : (-1 : Int) ≤ chI (some c) := by simp only [chI]; omega
  have hx2 : chI (some c) < 256 := by simp only [chI]; omega
  rw [chW_eq] at h10
  bc_run hlive hS [h10] at 0x80002790
  all_goals rw [sxw_addK (k := 9) rfl hx1 hx2 (by decide), sltiu_ne0, ofInt_toNat_lt5 (by omega) (by omega)]
  · intro hb; simp only [chI] at hb; omega
  intro _
  bc_run hlive hS [h10] at 0x800027b8
  all_goals simp only [ne_eq, ofInt_add_eq0 (k := 32) rfl (by decide) hx1 hx2]
  rotate_left
  · intro hb; simp only [chI, Decidable.not_not] at hb; omega
  intro _
  bc_run hlive hS [h10] at 0x8000289c
  all_goals simp only [ofInt_add_eq0 (k := 95) rfl (by decide) hx1 hx2]
  · intro e
    simp only [chI] at e
    have e' : c = 95 := by omega
    subst e'
    exact hus _ rfl (by keeps_tac Keeps.refl _ _) (by bsimp []; exact (chW_eq _).symm)
  · intro e
    simp only [chI] at e
    bc_run hlive hS [h10] at 0x800027d4
    all_goals simp only [ofInt_add_eq0 (k := 45) rfl (by decide) hx1 hx2]
    · intro e2; simp only [chI] at e2; omega
    · intro _
      bc_run hlive hS [h10] at 0x800027d4
      all_goals rw [ofInt_eq_lit (k := 43) (by decide) hx1 hx2]
      · intro e3; simp only [chI] at e3; omega
      · intro _
        exact hdg _ (by intro e4; apply e; simp only [Option.some.injEq] at e4; omega)
          (by keeps_tac Keeps.refl _ _) (by bsimp []; exact (chW_eq _).symm) (by bsimp [])

/-- **The `_` sign's space test** at `0x800028a0` (`s6 = s0`), on the
character `ch` read into `a0`: a space to the space loop at `0x800028b0`,
else `s0 = a0` and on to `0x800027d4`. -/
theorem gn_ustest {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {R : Nat → BitVec 64} {M : Mem}
    {ch : Option Nat} (hc : ∀ c, ch = some c → c < 256) (h10 : R 10 = chW ch)
    (hsp : ∀ R', (∃ c, ch = some c ∧ isSpace c = true) → Keeps [8, 14, 15, 22] R' R → R' 22 = R 8 →
      DWO live S Q t 0x800028b0#64 R' M)
    (hno : ∀ R', (∀ c, ch = some c → isSpace c = false) → Keeps [8, 14, 15, 22] R' R → R' 22 = R 8 →
      R' 8 = chW ch → DWO live S Q t 0x800027d4#64 R' M) :
    DWO live S Q t 0x800028a0#64 R M := by
  obtain ⟨hx1, hx2⟩ := chI_bounds hc
  rw [chW_eq] at h10
  bc_run hlive hS [h10] at 0x800028b0
  all_goals rw [sxw_addK (k := 9) rfl hx1 hx2 (by decide), sltiu_eq0, ofInt_toNat_lt5 (by omega) (by omega)]
  · intro hb
    bc_run hlive hS [h10] at 0x800027d4
    all_goals rw [ofInt_add_eq0 (k := 32) rfl (by decide) hx1 hx2]
    · intro e
      refine hsp _ ?_ (by keeps_tac Keeps.refl _ _) (by bsimp [])
      cases ch with
      | none => simp [chI] at e
      | some c => exact ⟨c, rfl, (isSpace_iff c).mpr (.inl (by simp only [chI] at e; omega))⟩
    · intro e
      bc_run hlive hS [] at 0x800027d4
      refine hno _ (fun c ec => ?_) (by keeps_tac Keeps.refl _ _) (by bsimp [])
        (by bsimp [h10]; exact (chW_eq _).symm)
      subst ec
      simp only [chI] at hb e
      cases hsc : isSpace c
      · rfl
      · rw [isSpace_iff] at hsc; omega
  · intro hb
    refine hsp _ ?_ (by keeps_tac Keeps.refl _ _) (by bsimp [])
    cases ch with
    | none => simp [chI] at hb
    | some c => exact ⟨c, rfl, (isSpace_iff c).mpr (.inr (by simp only [chI] at hb; omega))⟩

/-- **Before the integer loop** (from the first read to `0x800027d4`):
`result` holds `0`, `temp` and `build` a handle each, `base` the input base;
the reader at position `n`, the sign character in `s6`. -/
structure GnQ (S : Nat → Prop) (M0 : Mem) (R0 : Nat → BitVec 64) (sp : Nat) (G : DcG)
    (hs0 : List GV) (st : St) (o : StrObj) (j0 ra : Nat) (s6 : BitVec 64) (L0 : List NumObj)
    (R : Nat → BitVec 64) (M : Mem) (n : Nat) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (pr pt pd pb : Nat) : Prop where
  fr : CFr InP 144 gnSv M0 M R0 R sp
  h : DcAt S M H F L C G (.num pr :: .num pt :: .num pd :: .num pb :: hs0) st
  w16 : ldv .ld M (sp - 144 + 16) = BitVec.ofNat 64 pr
  w32 : ldv .ld M (sp - 144 + 32) = BitVec.ofNat 64 pt
  w24 : ldv .ld M (sp - 144 + 24) = BitVec.ofNat 64 pd
  w8 : ldv .ld M (sp - 144 + 8) = BitVec.ofNat 64 pb
  dr : (GV.num pr).Den ⟨L, G.strs⟩ (.num ⟨false, 0, 0⟩)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num ⟨false, st.ibase, 0⟩)
  keep : HsKeep ⟨L0, G.strs⟩ ⟨L, G.strs⟩ hs0
  r18 : R 18 = 0x80000b70#64
  r19 : R 19 = BitVec.ofNat 64 ra
  r20 : R 20 = BitVec.ofNat 64 zeroAddr
  r22 : R 22 = s6
  le : n ≤ (rdW o j0).length
  ptr : ldv .ld M inPtrAddr = BitVec.ofNat 64 (o.tb.pay + j0 + n)

/-- The state after a read: a new memory changed only at the reader's
pointer, the registers `s2`, `s3`, `s4` kept. -/
theorem GnQ.next {S : Nat → Prop} {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat} {G : DcG}
    {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 s6' : BitVec 64} {L0 : List NumObj}
    {R R' : Nat → BitVec 64} {M M' : Mem} {n n' : Nat} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {pr pt pd pb : Nat}
    (hQ : GnQ S M0 R0 sp G hs0 st o j0 ra s6 L0 R M n H F L C pr pt pd pb) (hab : heapEnd ≤ sp - 144)
    (fr : CFr InP 144 gnSv M0 M' R0 R' sp)
    (h : DcAt S M' H F L C G (.num pr :: .num pt :: .num pd :: .num pb :: hs0) st)
    (hm : MemOnly InP M' M) (k : Keeps [1, 8, 10, 14, 15, 22] R' R) (r22 : R' 22 = s6')
    (le : n' ≤ (rdW o j0).length) (ptr : ldv .ld M' inPtrAddr = BitVec.ofNat 64 (o.tb.pay + j0 + n')) :
    GnQ S M0 R0 sp G hs0 st o j0 ra s6' L0 R' M' n' H F L C pr pt pd pb :=
  { hQ with
    fr := fr
    h := h
    w16 := (ldv_inP hm (by omega) _).trans hQ.w16
    w32 := (ldv_inP hm (by omega) _).trans hQ.w32
    w24 := (ldv_inP hm (by omega) _).trans hQ.w24
    w8 := (ldv_inP hm (by omega) _).trans hQ.w8
    r18 := (k.get 18).trans hQ.r18
    r19 := (k.get 19).trans hQ.r19
    r20 := (k.get 20).trans hQ.r20
    r22 := r22
    le := le
    ptr := ptr }

/-- **Into the integer loop** (`0x800027d4`, `s5 = 9`, `s7 = 5`): the
character at `j` in `s0`. -/
theorem gn_go {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} {R : Nat → BitVec 64} {M : Mem} {j : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {pr pt pd pb : Nat}
    (hQ : GnQ S M0 R0 sp G hs0 st o j0 ra s6 L0 R M (min (j + 1) (rdW o j0).length) H F L C pr pt pd pb)
    (hj : j ≤ (rdW o j0).length) (h8 : R 8 = chW (rdW o j0)[j]?)
    (hk : ∀ R', GnI S M0 R0 sp G hs0 st o j0 ra s6 L0 R' M j 0 H F L C pr pt pd pb →
      DWO live S Q t 0x80002820#64 R' M) :
    DWO live S Q t 0x800027d4#64 R M := by
  have hS : HeapOwn S := fun a e1 e2 => hQ.h.heap.heap.own a e1 e2
  have r18 := hQ.r18; have r19 := hQ.r19; have r20 := hQ.r20; have r22 := hQ.r22
  bc_run hlive hS [] at 0x80002820
  exact hk _
    { fr := hQ.fr.sregs (by keeps_tac Keeps.refl _ _) (by bsimp [])
      h := hQ.h
      w16 := hQ.w16
      w32 := hQ.w32
      w24 := hQ.w24
      w8 := hQ.w8
      dr := hQ.dr
      db := hQ.db
      keep := hQ.keep
      regs := ⟨by bsimp [r18], by bsimp [r19], by bsimp [r20], by bsimp [], by bsimp [r22], by bsimp []⟩
      rd := ⟨hj, by bsimp [h8], hQ.ptr⟩ }

/-- **The space loop** at `0x800028b0` after the space at `j`: the spaces
read, ending at `0x800027d4` with the first other character `jS` in `s0`. -/
theorem gn_sp {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (gx : GnCtx S M0 sp G o j0) {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {pr pt pd pb : Nat} :
    ∀ (m j : Nat) (R : Nat → BitVec 64) (M : Mem), (rdW o j0).length - j = m → j < (rdW o j0).length →
      GnQ S M0 R0 sp G hs0 st o j0 ra s6 L0 R M (j + 1) H F L C pr pt pd pb →
      (∀ R' M' jS, GnQ S M0 R0 sp G hs0 st o j0 ra s6 L0 R' M' (min (jS + 1) (rdW o j0).length) H F L C
          pr pt pd pb → jS ≤ (rdW o j0).length → R' 8 = chW (rdW o j0)[jS]? →
          ((rdW o j0).drop (j + 1)).dropWhile isSpace = (rdW o j0).drop jS →
          DWO live S Q t 0x800027d4#64 R' M') →
      DWO live S Q t 0x800028b0#64 R M := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro j R M hm hj hQ hk
  have cx := gx.cx
  have hab := cx.abv
  have h := hQ.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have r18 := hQ.r18
  have hr := h.rd gx.mem gx.j0
  have jt : Sail.BitVec.update (0x80000b70#64) 0 0#1 = 0x80000b70#64 := jalr_tgt _ (by decide)
  bc_run hlive hS [r18]
  · rw [jt]; decide
  rw [jt]
  refine cf_read hlive (hQ.fr.regs (by keeps_tac Keeps.refl _ _)) hab h gx.own gx.mem gx.j0 (j := j + 1)
    (by omega) hQ.ptr (by bsimp []) fun R1 M1 hk1 e10 fr1 h1 hm1 hp1 => ?_
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  bsimp []
  refine gn_sptest hlive hS1 (ch := (rdW o j0)[j + 1]?) (fun c e => hr.lt c (List.mem_of_getElem? e)) e10
    (fun R2 ⟨c, ec, hsc⟩ k2 => ?_) (fun R2 hno k2 e8 => ?_)
  · have hj1 : j + 1 < (rdW o j0).length := by
      rcases Nat.lt_or_ge (j + 1) (rdW o j0).length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at ec; cases ec
    have kk : Keeps [1, 8, 10, 14, 15, 22] R2 R :=
      (k2.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans
        ((hk1.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans (by keeps_tac Keeps.refl _ _))
    refine ih _ (by omega) (j + 1) R2 M1 rfl hj1
      (hQ.next hab (fr1.sregs (k2.mono (by decide)) (k2.get 2)) h1 hm1 kk (by rw [k2.get 22, hk1.get 22]; bsimp [hQ.r22])
        (by omega) (by rw [hp1, Nat.min_eq_left (by omega)]))
      fun R' M' jS hQ' hjS e8 ed => hk R' M' jS hQ' hjS e8 ?_
    have hc : (rdW o j0).getD (j + 1) 0 = c := by rw [getElem?_of_lt hj1] at ec; exact Option.some.inj ec
    rw [dropSpace_drop_space hj1 (hc ▸ hsc)]; exact ed
  · have kk : Keeps [1, 8, 10, 14, 15, 22] R2 R :=
      (k2.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans
        ((hk1.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans (by keeps_tac Keeps.refl _ _))
    refine hk R2 M1 (j + 1) (hQ.next hab (fr1.sregs (k2.mono (by decide)) (k2.get 2)) h1 hm1 kk
      (by rw [k2.get 22, hk1.get 22]; bsimp [hQ.r22]) (by omega) hp1) (by omega) e8 (dropSpace_drop_stop hno)

/-- **The `_` sign** (`0x8000289c`, `s0 = '_'` read at `0`): read on, the
spaces after it skipped, `s6 = '_'`; on to `0x800027d4` with the first
other character `jS` in `s0`. -/
theorem gn_under {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (gx : GnCtx S M0 sp G o j0) {R : Nat → BitVec 64} {M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {pr pt pd pb : Nat}
    (hQ : GnQ S M0 R0 sp G hs0 st o j0 ra s6 L0 R M 1 H F L C pr pt pd pb)
    (h8 : R 8 = chW (some 95))
    (hk : ∀ R' M' jS, GnQ S M0 R0 sp G hs0 st o j0 ra (chW (some 95)) L0 R' M'
        (min (jS + 1) (rdW o j0).length) H F L C pr pt pd pb → jS ≤ (rdW o j0).length →
        R' 8 = chW (rdW o j0)[jS]? → ((rdW o j0).drop 1).dropWhile isSpace = (rdW o j0).drop jS →
        DWO live S Q t 0x800027d4#64 R' M') :
    DWO live S Q t 0x8000289c#64 R M := by
  have cx := gx.cx
  have hab := cx.abv
  have h := hQ.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have r18 := hQ.r18
  have hr := h.rd gx.mem gx.j0
  have jt : Sail.BitVec.update (0x80000b70#64) 0 0#1 = 0x80000b70#64 := jalr_tgt _ (by decide)
  bc_run hlive hS [r18]
  · rw [jt]; decide
  rw [jt]
  refine cf_read hlive (hQ.fr.regs (by keeps_tac Keeps.refl _ _)) hab h gx.own gx.mem gx.j0 (j := 1)
    hQ.le hQ.ptr (by bsimp []) fun R1 M1 hk1 e10 fr1 h1 hm1 hp1 => ?_
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  bsimp []
  have s8 : R1 8 = chW (some 95) := (hk1.get 8).trans h8
  refine gn_ustest hlive hS1 (ch := (rdW o j0)[1]?) (fun c e => hr.lt c (List.mem_of_getElem? e)) e10
    (fun R2 ⟨c, ec, hsc⟩ k2 e22 => ?_) (fun R2 hno k2 e22 e8 => ?_)
  · have hj1 : 1 < (rdW o j0).length := by
      rcases Nat.lt_or_ge 1 (rdW o j0).length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at ec; cases ec
    have kk : Keeps [1, 8, 10, 14, 15, 22] R2 R :=
      (k2.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans
        ((hk1.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans (by keeps_tac Keeps.refl _ _))
    refine gn_sp hlive gx _ 1 R2 M1 rfl hj1
      (hQ.next hab (fr1.sregs (k2.mono (by decide)) (k2.get 2)) h1 hm1 kk (e22.trans s8)
        (by omega) (by rw [hp1, Nat.min_eq_left (by omega)]))
      fun R' M' jS hQ' hjS e8 ed => hk R' M' jS hQ' hjS e8 ?_
    have hc : (rdW o j0).getD 1 0 = c := by rw [getElem?_of_lt hj1] at ec; exact Option.some.inj ec
    rw [dropSpace_drop_space hj1 (hc ▸ hsc)]; exact ed
  · have kk : Keeps [1, 8, 10, 14, 15, 22] R2 R :=
      (k2.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans
        ((hk1.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans (by keeps_tac Keeps.refl _ _))
    refine hk R2 M1 1 (hQ.next hab (fr1.sregs (k2.mono (by decide)) (k2.get 2)) h1 hm1 kk
      (e22.trans s8) (by omega) hp1) hQ.le e8 (dropSpace_drop_stop hno)

end Dc.Mach
