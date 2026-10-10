import Dc.Mach.DcPrintAll

/-!
# `dc_num2int` (M9)

    dc_num2int (value, discard):
      result = bc_num2long (value);
      if (result == 0 && !bc_is_zero (value)) {
        fprintf (stderr, "%s: value overflows simple integer; punting...\n", progname);
        result = -1;
      }
      if (discard == DC_TOSS) bc_free_num (&value);
      return (int) result;

- `sxw_ofInt`: the `sext.w` of a `long` is `Num.toInt32`.
- `n2i_epi`, `n2i_toss`: the returns, with the handle kept or released.
- `dc_num2int_spec`: `a0 = (Num.toInt n).1`; the message goes to `stderr`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `(int) l` as `sext.w` of the 64-bit word. -/
theorem sxw_ofInt (r : Int) : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofInt 64 r)) =
    BitVec.ofInt 64 (Dc.Num.toInt32 r) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt]
  have e : (BitVec.extractLsb 31 0 (BitVec.ofInt 64 r)).toNat = (r % 2 ^ 32).toNat := by
    simp only [BitVec.extractLsb_toNat, BitVec.toNat_ofInt]
    omega
  rw [BitVec.toInt_eq_toNat_cond, e]
  simp only [Dc.Num.toInt32]
  split <;> split <;> rw [Int.bmod_eq_of_le (by omega) (by omega)] <;> omega

/-- `bc_num2long`'s result is within `±(10 · (LONG_MAX / 10) + 9)`. -/
theorem toLong_small (n : Dc.Num) : -2147483649 ≤ n.toLong ∧ n.toLong ≤ 2147483649 := by
  simp only [Dc.Num.toLong, Dc.Num.longMax]
  split <;> split <;> omega

/-- A `long` of that range is `0` exactly when its word is. -/
theorem ofInt_eq_zero_small {r : Int} (h1 : -2147483649 ≤ r) (h2 : r ≤ 2147483649) :
    BitVec.ofInt 64 r = 0#64 ↔ r = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toInt h
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)] at this
    simpa using this
  · rintro rfl; rfl

theorem overflowMsg : ProgMsg 0x80007d10 45 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

/-- `dc_num2int`'s epilogue (`0x8000266c`): `ra`, `s0` reloaded, `a0 = a5`. -/
theorem n2i_epi {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} {s0v ra : BitVec 64}
    (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (f16 : ldv .ld M (sp - 32 + 16) = s0v)
    (f24 : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 8, 10] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp → R' 8 = s0v →
      R' 10 = R 15 → DWO live S Q t ra R' M) :
    DWO live S Q t 0x8000266c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, f16, f24]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) ?_ (by bsimp []) (by bsimp [])
  bsimp []; congr 1; omega

/-- `dc_num2int`'s release (`0x800026b4`): `bc_free_num (&value)` on the
handle at `sp - 32 + 8`, then the epilogue with `a0 = a5`. -/
theorem n2i_toss {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p sp : Nat}
    {s0v ra : BitVec 64} (h : DcAt S M H F L C G (.num p :: hs) st)
    (hsf : StackFrame S sp 64) (hab : heapEnd + 64 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (f8 : ldv .ld M (sp - 32 + 8) = BitVec.ofNat 64 p)
    (f16 : ldv .ld M (sp - 32 + 16) = s0v) (f24 : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps [1, 2, 8, 10, 13, 14, 15] R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = s0v → R' 10 = R 15 → DcAt S M' H' F' L' C' G hs st →
      StkOut sp 64 M' M → DWO live S Q t ra R' M') :
    DWO live S Q t 0x800026b4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  bc_run hlive hS [h2] at 0x800048c0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM2 : MemOnly (frameIn sp 32) (writeLog M [(sp - 32, 8, R 15)]) M := fun a ha => by
    simp only [frameIn] at ha
    rw [imgM_store_miss _ _ (by omega)]
  have m0 : ldv .ld (writeLog M [(sp - 32, 8, R 15)]) (sp - 32) = R 15 := ldv_store_hit _ _ _
  have m8 : ldv .ld (writeLog M [(sp - 32, 8, R 15)]) (sp - 32 + 8) = BitVec.ofNat 64 p := by
    rw [ldv_ld_miss _ _ (by omega)]; exact f8
  have m16 : ldv .ld (writeLog M [(sp - 32, 8, R 15)]) (sp - 32 + 16) = s0v := by
    rw [ldv_ld_miss _ _ (by omega)]; exact f16
  have m24 : ldv .ld (writeLog M [(sp - 32, 8, R 15)]) (sp - 32 + 24) = ra := by
    rw [ldv_ld_miss _ _ (by omega)]; exact f24
  generalize writeLog M [(sp - 32, 8, R 15)] = M2 at hM2 m0 m8 m16 m24 ⊢
  have hab2 : heapEnd ≤ sp - 32 := by simp only [heapEnd]; omega
  have h2' := h.outWrite hM2 fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  refine bc_free_num_dc hlive h2' (hsf.slot (by omega) (by omega) (by omega))
    (by simp only [heapEnd]; omega) m8 (hsf.within (m := 32) (n := 32) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (.inr (by omega)) _ (by bsimp [h2]) (by bsimp [h2]) (by bsimp [])
    fun R6 M6 H6 F6 L6 C6 hk6 hd6 hz6 hout6 => ?_
  have k0 : ∀ o, o < 32 → (o + 8 ≤ 8 ∨ 16 ≤ o) → ∀ j, j < 8 →
      imgM M6 (sp - 32 + o + j) = imgM M2 (sp - 32 + o + j) :=
    fun o ho h8 j hj => hout6 _ (above_sp hab2 (by omega)).1 (above_sp hab2 (by omega)).2.1
      ((above_sp hab2 (by omega)).2.2 _) (fun hs' => by simp only [slotBytes] at hs'; omega)
  have g0 : ldv .ld M6 (sp - 32) = R 15 :=
    (ldv_congr .ld fun j hj => by
      simpa using k0 0 (by omega) (by omega) j (by have : widthOfM .ld = 8 := rfl; omega)).trans m0
  have g16 : ldv .ld M6 (sp - 32 + 16) = s0v :=
    (ldv_congr .ld fun j hj => k0 16 (by omega) (by omega) j (by have : widthOfM .ld = 8 := rfl; omega)).trans m16
  have g24 : ldv .ld M6 (sp - 32 + 24) = ra :=
    (ldv_congr .ld fun j hj => k0 24 (by omega) (by omega) j (by have : widthOfM .ld = 8 := rfl; omega)).trans m24
  have q6 : R6 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk6.get 2 (by decide)]; bsimp [h2]
  have hS6 : HeapOwn S := fun a e1 e2 => hd6.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS6 [q6, g0, g16, g24]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ M6 H6 F6 L6 C6 ?_ (by bsimp []) ?_ (by bsimp []) (by bsimp []) hd6 fun a ho hg hf => ?_
  · exact by keeps_tac ((hk6.mono (ks' := [1, 2, 8, 10, 13, 14, 15]) (by decide)).trans
      (by keeps_tac Keeps.refl _ _))
  · bsimp []; congr 1; omega
  · rw [hout6 a ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
      (fun hs' => hf (by simp only [slotBytes, frameIn] at hs' ⊢; omega))]
    exact hM2 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

/-- `dc_num2int`'s join (`0x80002668` `beqz s0` or `0x800026b0` `bnez s0`, the
result in `a5`): the epilogue, or the release when the handle is tossed. -/
theorem n2i_join {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p sp : Nat} {keep : Bool}
    {ra : BitVec 64} {R0 : Nat → BitVec 64} {pc : BitVec 64} (hpc : pc = 0x80002668#64 ∨ pc = 0x800026b0#64)
    (h : DcAt S M H F L C G hs st) (hd : keep = false → hs.head? = some (.num p))
    (hsf : StackFrame S sp 64) (hab : heapEnd + 64 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h8 : R 8 = boolWord keep)
    (f8 : ldv .ld M (sp - 32 + 8) = BitVec.ofNat 64 p)
    (f16 : ldv .ld M (sp - 32 + 16) = R0 8) (f24 : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps [1, 2, 8, 10, 13, 14, 15] R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = R0 8 → R' 10 = R 15 →
      DcAt S M' H' F' L' C' G (if keep then hs else hs.tail) st →
      StkOut sp 64 M' M → DWO live S Q t ra R' M') :
    DWO live S Q t pc R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hsf32 : StackFrame S sp 32 := by simpa using hsf.within (m := 0) (n := 32) (by omega) (by decide)
  cases keep
  · obtain ⟨hs0, rfl⟩ : ∃ hs0, hs = .num p :: hs0 := by
      rcases hs with _ | ⟨g0, hs0⟩
      · exact absurd (hd rfl) (by simp)
      · exact ⟨hs0, by rw [Option.some.inj (hd rfl)]⟩
    have h8' : R 8 = 0#64 := h8
    rcases hpc with rfl | rfl
    all_goals
      bc_run hlive hlive [h8']
      all_goals try (intro hc; exact absurd hc (by decide))
      try intro _
      refine n2i_toss hlive h hsf hab _ (by bsimp [h2]) f8 f16 f24 hal
        fun R' M' H' F' L' C' hk' e1 e2 e8 e10 hD hfr => hk R' M' H' F' L' C' ?_ e1 e2 e8 ?_ hD hfr
      · exact hk'.trans (by keeps_tac Keeps.refl _ _)
      · rw [e10]; try bsimp []
  · have h8' : R 8 = 1#64 := h8
    rcases hpc with rfl | rfl
    all_goals
      bc_run hlive hlive [h8']
      all_goals try (intro hc; exact absurd hc (by decide))
      try intro _
      refine n2i_epi hlive hsf32 (by simp only [heapEnd]; omega) _ (by bsimp [h2]) f16 f24 hal
        fun R' hk' e1 e2 e8 e10 => hk R' M H F L C ?_ e1 e2 e8 ?_ h fun _ _ _ _ => rfl
      · exact hk'.mono (by decide) |>.trans (by keeps_tac Keeps.refl _ _)
      · rw [e10]; try bsimp []

/-- **`dc_num2int (value, discard)`** at `0x80002648` on the number `x`
(with `DC_TOSS`, the head of the caller's handles `hs`): `a0` is
`(Num.toInt n).1` as an `int`; the overflow message goes to `stderr`; the
handle is released unless `keep`. -/
theorem dc_num2int_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {x : NumObj}
    {sp : Nat} {keep : Bool}
    (h : DcAt S M H F L C G hs st) (hd : keep = false → hs.head? = some (.num x.rep.p)) (hx : x ∈ L)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 x.rep.p)
    (h11 : R 11 = boolWord keep) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps cClob R' R → R' 2 = R 2 →
      R' 10 = BitVec.ofInt 64 x.rep.num.toInt.1 →
      DcAt S M' H' F' L' C' G (if keep then hs else hs.tail) st → StkOut sp 336 M' M →
      DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80002648#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have fsub : ∀ a, frameIn (sp - 32) 304 a → frameIn sp 336 a := fun a hf' => by
    simp only [frameIn, Nat.sub_sub] at hf' ⊢; omega
  bc_run hlive hS [h2, h10, h11, word_sub32 (show 32 ≤ sp by omega)] at 0x800065a0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hab2 : heapEnd ≤ sp - 32 := by simp only [heapEnd]; omega
  have hM1 : MemOnly (frameIn sp 32) (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
      [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) M := fun a ha => by
    simp only [frameIn] at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hM1 fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have m8 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
      [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) (sp - 32 + 8) =
      BitVec.ofNat 64 x.rep.p := ldv_store_hit _ _ _
  have m16 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
      [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) (sp - 32 + 16) = R 8 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have m24 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
      [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) (sp - 32 + 24) = R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
      [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)] = M1 at hM1 h1 m8 m16 m24 ⊢
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  have hn := h1.heap.nums x hx
  have hlp := h1.den.pos x hx
  have hsf64 : StackFrame S sp 64 := by simpa using hsf.within (m := 0) (n := 64) (by omega) (by decide)
  have hfin : ∀ M2 : Mem, MemOnly (frameIn (sp - 32) 304) M2 M1 →
      ∀ R1 : Nat → BitVec 64, ∀ {pc : BitVec 64}, (pc = 0x80002668#64 ∨ pc = 0x800026b0#64) →
      R1 2 = BitVec.ofNat 64 (sp - 32) → R1 8 = boolWord keep →
      R1 15 = BitVec.ofInt 64 x.rep.num.toInt.1 → Keeps ([1, 2, 8] ++ cClob) R1 R →
      DWO live S Q t pc R1 M2 := by
    intro M2 hM2 R1 pc hpc e2 e8 e15 hk1
    have hab3 : heapEnd ≤ sp - 32 - 304 := by simp only [heapEnd]; omega
    have h2' := h1.outWrite hM2 fun a ha =>
      ⟨(above_sp hab3 (by simp only [frameIn] at ha; omega)).1,
        (above_sp hab3 (by simp only [frameIn] at ha; omega)).2.1⟩
    have kf : ∀ o, o < 32 → imgM M2 (sp - 32 + o) = imgM M1 (sp - 32 + o) := fun o ho =>
      hM2 _ fun hf => by simp only [frameIn] at hf; omega
    have n8 : ldv .ld M2 (sp - 32 + 8) = BitVec.ofNat 64 x.rep.p := (ldv_congr .ld fun j hj => by
      have := kf (8 + j) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m8
    have n16 : ldv .ld M2 (sp - 32 + 16) = R 8 := (ldv_congr .ld fun j hj => by
      have := kf (16 + j) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m16
    have n24 : ldv .ld M2 (sp - 32 + 24) = R 1 := (ldv_congr .ld fun j hj => by
      have := kf (24 + j) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m24
    refine n2i_join hlive (R0 := R) hpc h2' hd hsf64 (by omega) R1 e2 e8 n8 n16 n24 hal
      fun R' M' H' F' L' C' hk' e1 e2' e8' e10 hD hfr => ?_
    have hk2 : Keeps cClob R' R :=
      Keeps.restoreAll (rs := [1, 2, 8]) ((hk'.mono (ks' := [1, 2, 8] ++ cClob) (by decide)).trans
        hk1) fun z hz => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact e1
          · rw [e2', h2]
          · exact e8'
    refine hk R' M' H' F' L' C' hk2 (by rw [e2', h2]) (by rw [e10, e15]) hD fun a ho hg hf => ?_
    have hf1 : ¬ frameIn sp 64 a := fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
    have hf2 : ¬ frameIn (sp - 32) 304 a := fun hf' => hf (fsub a hf')
    have hf3 : ¬ frameIn sp 32 a := fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
    exact (hfr a ho hg hf1).trans ((hM2 a hf2).trans (hM1 a hf3))
  refine bc_num2long_spec hlive hS1 hn hlp _ (by bsimp [h10]) (by bsimp []) fun R1 hk1 e10 => ?_
  have r8 : R1 8 = boolWord keep := by rw [hk1.get 8 (by decide)]; bsimp []
  have r2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2 (by decide)]; bsimp []
  have k1 : Keeps ([1, 2, 8] ++ cClob) R1 R :=
    (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  obtain ⟨hlo, hhi⟩ := toLong_small x.rep.num
  bsimp []
  by_cases hr : x.rep.num.toLong = 0
  · have hz0 : BitVec.ofInt 64 x.rep.num.toLong = 0#64 := by rw [hr]; rfl
    bc_run hlive hS1 [e10, r2, r8, sxw_ofInt]
    all_goals first | (intro hc; exact absurd hz0 hc) | skip
    try intro _
    bc_run hlive hS1 [e10, r2, r8, m8] at 0x80004a10
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hz : ldv .ld M1 zeroAddr = BitVec.ofNat 64 x.rep.p → x.rep.num.isZero = true := fun e => by
      have hzn := h1.heap.nums C.z h1.den.mz
      have p1 := hn.shape.pLo; have p2 := hn.shape.pHi
      have p3 := hzn.shape.pLo; have p4 := hzn.shape.pHi
      have e' := h1.view.zw.symm.trans e
      have hp : C.z.rep.p = x.rep.p := by
        have := congrArg BitVec.toNat e'
        simp only [BitVec.toNat_ofNat] at this
        omega
      rw [← h1.heap.eq_of_p h1.den.mz hx hp, h1.den.zv]; rfl
    refine bc_is_zero_spec hlive hS1 hn hlp
      (fun b e1 e2 => h1.glob b (by simp only [DcGlob, dc_addrs]; omega)) hz _ (by bsimp [])
      (by bsimp []) fun R2 hk2 e10b => ?_
    bsimp []
    have s2 : R2 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk2.get 2 (by decide)]; bsimp [r2]
    have s8 : R2 8 = boolWord keep := by rw [hk2.get 8 (by decide)]; bsimp [r8]
    have k2 : Keeps ([1, 2, 8] ++ cClob) R2 R :=
      (hk2.mono (by decide)).trans (by keeps_tac k1)
    cases hiz : x.rep.num.isZero
    · rw [hiz] at e10b
      have e10c : R2 10 = 0#64 := e10b
      have hpn := h1.view.prog
      have hG := h1.glob
      have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
      bc_run hlive hS1 [e10c, s2, s8, hpn, stderr_word] at 0x80000774
      bc_run hlive hS1 [e10c, s2, s8, hpn, stderr_word] at 0x80000774
      refine fprintf_prog_spec hlive overflowMsg (by decide)
        (hsf.within (m := 32) (n := 304) (by omega) (by decide)) (by simp only [stderrAddr]; omega)
        h1.errFile _ ?q2 (by bsimp []; decide) (by bsimp []) (by bsimp []) (by bsimp [])
        fun R3 M3 hk3 hfr3 => ?_
      case q2 => bsimp [s2]
      bsimp []
      bc_run hlive hS1 [] at 0x800026b0
      refine hfin M3 (fun a ha => hfr3 a (by simp only [frameIn, Nat.sub_sub] at ha; omega)) _ (.inr rfl)
        ?r2 ?r8 ?r15 ?rk
      case r2 => bsimp [hk3.get 2 (by decide), s2]
      case r8 => bsimp [hk3.get 8 (by decide), s8]
      case r15 =>
        bsimp []
        simp [Dc.Num.toInt, hr, hiz]
      case rk => exact by keeps_tac ((hk3.mono (ks' := [1, 2, 8] ++ cClob) (by decide)).trans
        (by keeps_tac k2))
    · rw [hiz] at e10b
      have e10c : R2 10 = 1#64 := e10b
      bc_run hlive hS1 [e10c, s2, s8]
      all_goals first | (intro hc; exact absurd rfl hc) | skip
      try intro _
      refine hfin M1 (MemOnly.refl _ _) _ (.inl rfl) (by bsimp [s2]) (by bsimp [s8]) ?_
        (by keeps_tac k2)
      bsimp []
      simp [Dc.Num.toInt, hr, hiz]; rfl
  · have hnz : BitVec.ofInt 64 x.rep.num.toLong ≠ 0#64 := fun e => hr ((ofInt_eq_zero_small hlo hhi).1 e)
    bc_run hlive hS1 [e10, r2, r8, sxw_ofInt]
    all_goals first | (intro hc; exact absurd hc hnz) | skip
    try intro _
    refine hfin M1 (MemOnly.refl _ _) _ (.inl rfl) (by bsimp [r2]) (by bsimp [r8]) ?_ (by keeps_tac k1)
    bsimp []
    simp [Dc.Num.toInt, hr]

end Dc.Mach
