import Dc.Mach.DcFuncCtx
import Dc.Mach.DcScalars

/-!
# `dc_func`'s arms without a callee (M10)

From the dispatch into the frame (`FnAt.of_disp`), the arms that only set
the status: whitespace (`DC_OKAY`), a number's first character (`DC_INT`,
its own epilogue at `0x80000c20`), `#`, `!`, `[`, `x`, and `q` (which stores
`unwind_noexit` and `unwind_depth`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The frame after the dispatch of `DcFuncDisp.lean`. -/
theorem FnAt.of_disp {S : Nat → Prop} {sp W : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64}
    (hsf : StackFrame S sp W) (hab : heapEnd + W ≤ sp) (hW : 192 ≤ W)
    (h20 : R0 2 = BitVec.ofNat 64 sp) (hal : (R0 1).toNat % 4 = 0)
    (k : Keeps [2, 13, 14, 15] R R0) (e2 : R 2 = BitVec.ofNat 64 (sp - 192)) :
    FnAt S sp W M0 R0 R (writeLog M0 [(sp - 192 + 184, 8, R0 1)]) where
  frame := hsf
  room := hab
  big := hW
  r2 := e2
  r20 := h20
  ra := ldv_store_hit _ _ _
  al := hal
  keep := k.mono (by decide)
  out a _ _ _ hf := imgM_store_miss _ _ (by
    have := hsf.lo; simp only [frameIn] at hf; omega)

/-- The state after the dispatch's store of `ra`. -/
theorem DcAt.of_disp {S : Nat → Prop} {M0 : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {sp : Nat} {ra : BitVec 64}
    (h : DcAt S M0 H F L C G hs st) (hab : heapEnd + 192 ≤ sp) :
    DcAt S (writeLog M0 [(sp - 192 + 184, 8, ra)]) H F L C G hs st :=
  h.outWrite (MemOnly.store M0 _ 8 ra) fun a ha =>
    have := above_sp (sp := sp - 192) (by simp only [heapEnd] at hab ⊢; omega) (a := a)
      (by omega)
    ⟨this.1, this.2.1⟩

/-- An arm returning a code, the heap and ghost unchanged. -/
theorem fa_code {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {st st' : St} {r : Res} {M0 M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {sp W code : Nat}
    {R0 R : Nat → BitVec 64} (h : DcAt S M H F L C G hs st') (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q t0 st r G hs sp W M0 R0) (hf : FnOut st r code st')
    (h10 : R 10 = BitVec.ofNat 64 code) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000c14#64 R M :=
  hc.close hlive hk hf (ex := []) h (by simp) (by omega) (StrPin.refl _ _) h10

/-- The frame after stores confined to the scalar globals. -/
theorem FnAt.scalars {S : Nat → Prop} {sp W : Nat} {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) (k : Keeps cClob R' R) (hm : MemOnly ScalarWord M' M) :
    FnAt S sp W M0 R0 R' M' :=
  hc.call (Wc := 0) (by have := hc.big; omega) (k.mono (by decide)) (k.get 2 (by decide))
    fun a _ e2 _ _ => hm a fun hw => e2 hw.glob

/-- `DC_OKAY` (`0x80000c10`) after an arm's callees. -/
theorem fa_ok {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {st st' : St} {r : Res} {M0 M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G G' : DcG} {hs ex : List GV} {sp W : Nat}
    {R0 R : Nat → BitVec 64} (h : DcAt S M H F L C G' (ex ++ hs) st') (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q t0 st r G hs sp W M0 R0) (hf : FnOut st r 0 st') (hex : ex.length ≤ 2)
    (hlk : G'.lk.length ≤ G.lk.length + 2) (hpin : StrPin G.strs G'.strs hs) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000c10#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [] at 0x80000c14
  exact (hc.mod (by keeps_tac Keeps.refl _ _)).close hlive hk hf h hex hlk hpin (by bsimp [])

-- The arms share the state, the frame and the continuation.
section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {st : St} {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {G : DcG} {hs : List GV} {sp W : Nat} {R0 R : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- Whitespace (`0x80000c10`): `DC_OKAY`. -/
theorem fa_ws (hlive : ∀ p ∈ dcText, live p.1) {c : Nat} (hcw : c = 9 ∨ c = 10 ∨ c = 32)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q t0 st (dcFunc 70 st c peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000c10#64 R M := by
  have hr : dcFunc 70 st c peek neg = .ok st := by rcases hcw with rfl | rfl | rfl <;> rfl
  rw [hr] at hk
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [] at 0x80000c14
  exact fa_code hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hk (.ok st) (by bsimp [])

/-- `#` (`0x80000c84`): `DC_COMMENT`. -/
theorem fa_hash (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q t0 st (dcFunc 70 st 35 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000c84#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [] at 0x80000c14
  exact fa_code hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hk .comment (by bsimp [])

/-- `[` (`0x80001258`): `DC_STR`. -/
theorem fa_lbrack (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q t0 st (dcFunc 70 st 91 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001258#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [] at 0x80000c14
  exact fa_code hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hk .str (by bsimp [])

/-- `x` (`0x80000d30`): `DC_EVALTOS`. -/
theorem fa_x (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q t0 st (dcFunc 70 st 120 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000d30#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [] at 0x80000c14
  exact fa_code hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hk (.evalTos st) (by bsimp [])

/-- `!` (`0x80000c8c`): `DC_NEGCMP` before `<`, `=`, `>`, else `DC_SYSTEM`. -/
theorem fa_bang (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M)
    (h11 : R 11 = chW peek) (hpk : ∀ r, peek = some r → r < 256)
    (hk : FnK live S Q t0 st (dcFunc 70 st 33 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000c8c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hw : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (chW peek + 18446744073709551556#64)) =
      BitVec.ofInt 64 (chI peek - 60) := by
    rw [chW_eq]
    exact sxw_addK (K := 18446744073709551556) (k := 60) (by decide)
      (by cases peek <;> simp [chI]) (by cases peek with
        | none => simp [chI]
        | some r => have := hpk r rfl; simp only [chI]; omega) (by decide)
  bc_run hlive hlive [h11, hw] at 0x80000c98
  by_cases hn : peek = some 60 ∨ peek = some 61 ∨ peek = some 62
  · have hr : dcFunc 70 st 33 peek neg = .negcmp := by
      rcases hn with rfl | rfl | rfl <;> rfl
    rw [hr] at hk
    have hle : (BitVec.ofInt 64 (chI peek - 60)).toNat ≤ 2 := by
      rcases hn with rfl | rfl | rfl <;> decide
    bc_run hlive hlive [hle] at 0x80000c14
    all_goals first | (intro hc'; exact absurd hle (by omega)) | skip
    all_goals try intro _
    exact fa_code hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hk .negcmp (by bsimp [])
  · have hr : dcFunc 70 st 33 peek neg = .system := by
      simp only [not_or] at hn
      show (if peek == some 60 || peek == some 61 || peek == some 62 then Res.negcmp
        else Res.system) = .system
      simp [hn.1, hn.2.1, hn.2.2]
    rw [hr] at hk
    have hgt : 2 < (BitVec.ofInt 64 (chI peek - 60)).toNat := by
      rw [BitVec.toNat_ofInt]
      cases peek with
      | none => simp [chI]
      | some r =>
        have := hpk r rfl
        simp only [chI, Option.some.injEq] at hn ⊢
        omega
    bc_run hlive hlive [hgt] at 0x80000c14
    all_goals first | (intro hc'; exact absurd hgt (by omega)) | skip
    all_goals try intro _
    exact fa_code hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hk .system (by bsimp [])

/-- A number's first character (`0x80000c20`, its own epilogue): `DC_INT`. -/
theorem fa_int (hlive : ∀ p ∈ dcText, live p.1) {c : Nat}
    (hci : dcFunc 70 st c peek neg = .int)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q t0 st (dcFunc 70 st c peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000c20#64 R M := by
  rw [hci] at hk
  have hsf : StackFrame S sp 192 := hc.frame.mono hc.big
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := hc.room; have hbig := hc.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have f := hc.ra
  have e2 := hc.r2
  have hal := hc.al
  bc_run hlive hlive [e2, f]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ M H F L C G 5 st [] ?_ ?_ (by bsimp []) .int
    ⟨h, by simp, by omega, StrPin.refl _ _, hc.out⟩
  · refine Keeps.restoreAll (rs := [1, 2]) (show Keeps ([1, 2] ++ cClob) _ R0 from
      (by keeps_tac (hc.keep.mono (by decide)))) fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · bsimp []
    · bsimp [hc.r20]; rw [Nat.sub_add_cancel (by omega)]
  · bsimp [hc.r20]; rw [Nat.sub_add_cancel (by omega)]

/-- `q` (`0x80000f00`): `unwind_noexit = 0`, `unwind_depth = 1`, `DC_QUIT`. -/
theorem fa_q (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M)
    (hk : FnK live S Q t0 st (dcFunc 70 st 113 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000f00#64 R M := by
  have hq : dcFunc 70 st 113 peek neg = .quit { st with unwind := 1, noexit := false } := rfl
  rw [hq] at hk
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hg := h.glob
  bc_run hlive hS [] at 0x80000c14
  all_goals first
    | (intro b hb; have := of_mem_accAddrs hb; exact hg b (by simp only [DcGlob, dc_addrs]; omega))
    | skip
  have hm : MemOnly ScalarWord (writeLog (writeLog M [(noexitAddr, 4, 0#64)]) [(unwindAddr, 4, 1#64)]) M :=
    fun a ha => by
      simp only [ScalarWord, dc_addrs, not_or] at ha
      rw [imgM_store_miss _ _ (by simp only [dc_addrs]; omega),
        imgM_store_miss _ _ (by simp only [dc_addrs]; omega)]
  have v := h.view
  have h' := h.setScalars hm (i := st.ibase) (o := st.obase) (k := st.scale) (u := 1) (n := false)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega),
          ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact v.ibase)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega),
          ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact v.obase)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega),
          ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact v.scale)
    (ldv_lw_hitN _ rfl (by decide) (by decide))
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]
        exact ldv_lw_hitN _ rfl (by decide) (by decide))
    h.den.ibase h.den.obase h.den.scale (by decide)
  exact fa_code (st' := { st with unwind := 1, noexit := false }) hlive h'
    (hc.scalars (by keeps_tac Keeps.refl _ _) hm) hk (.quit _) (by bsimp [])

end

end Dc.Mach
