import Dc.Mach.DcFuncArmV2
import Dc.Mach.DcReadString

/-!
# `dc_func`'s `?` arm (M10)

`?` reads a line from standard input (`dc_readstring (stdin, '\n', '\n')`):
with the input exhausted the result is a new empty string, pushed, and
`DC_EVALTOS` returned. `stdin_lookahead` (`0x8001cd30`, outside `DcAt`'s
globals) holds `EOF` (premise `hla`), so the `ungetc` branch is not taken.
The arm spills `s0` (the `stdin` pointer) to `sp + 176` across its calls; the
frame is carried at the registers with `s0` restored (`Keeps.updSame`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- One register written alike on both sides. -/
theorem Keeps.updSame {ks : List Nat} {R' R : Nat → BitVec 64} (h : Keeps ks R' R) (k : Nat)
    (v : BitVec 64) : Keeps ks (VsaIris.Sym.upd R' k v) (VsaIris.Sym.upd R k v) := fun z hz => by
  by_cases e : z = k
  · subst e; rw [upd_same, upd_same]
  · rw [upd_other _ _ e, upd_other _ _ e]; exact h z hz

/-- The `stdin` pointer in `.rodata`. -/
theorem stdin_word : ldvf .ld dcROImg 2147516944 = BitVec.ofNat 64 0x8001ad10 := by decide +kernel

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {M0 : Mem} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {hs : List GV} {sp W : Nat} {R0 : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- `?` from the status test after `ferror` (`0x80000d1c`, `a0 = 0`): the datum
reloaded from the frame and pushed, `s0` reloaded, `DC_EVALTOS`. The frame is
at the registers with `s0` restored to `v8`. -/
theorem fq_push (hlive : ∀ p ∈ dcText, live p.1) {st : St} {p : Nat} {v8 tw : BitVec 64}
    {M3 : Mem} {H2 : Heap} {G G' : DcG} {R3 : Nat → BitVec 64}
    (h3 : DcAt S M3 H2 F L C G' (.str p :: hs) st) (hv : (GV.str p).Den ⟨L, G'.strs⟩ (.str []))
    (hcv : FnAt S sp W M0 R0 (VsaIris.Sym.upd R3 8 v8) M3) (hW : 192 + 128 ≤ W)
    (ho : FnOom live S Q sp W M0) (e2 : R3 2 = BitVec.ofNat 64 (sp - 192)) (e10 : R3 10 = 0#64)
    (l16 : ldv .ld M3 (sp - 192 + 16) = tw) (htw : tw.toNat % 2 ^ 32 = 2)
    (l24 : ldv .ld M3 (sp - 192 + 24) = BitVec.ofNat 64 p)
    (l176 : ldv .ld M3 (sp - 192 + 176) = v8)
    (hlk : G'.lk = G.lk) (hpin : StrPin G.strs G'.strs hs)
    (hk : FnK live S Q t0 st (.evalTos (st.push (.str []))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000d1c#64 R3 M3 := by
  fv_frame hcv
  bc_run hlive hlive [e10, l16, l24, e2] at 0x80002da4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hlive [e10, l16, l24, e2] at 0x80002da4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_push_spec hlive h3 hv (hcv.cf (Wc := 64) (by omega)) (hcv.cab (by omega)) _
    ⟨by bsimp []; exact htw, by bsimp []; rfl⟩ (by bsimp [e2])
    (by bsimp []) (fun R5 M5 H5 c5 k5 h5 hout5 => ?_) (fun R5 M5 e5 hout5 => ?_)
  · have hc5 : FnAt S sp W M0 R0 (VsaIris.Sym.upd R5 8 v8) M5 :=
      hcv.callS (Wc := 64) (by omega)
        (Keeps.updSame ((k5.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) 8 v8)
        (by rw [upd_other _ _ (by decide), upd_other _ _ (by decide), k5.get 2 (by decide)]
            bsimp [e2]) hout5
    have hs5 : ldv .ld M5 (sp - 192 + 176) = v8 := by
      rw [ldv_congr .ld fun j hj => hout5 _ (hfr _ (by omega)).1 (hfr _ (by omega)).2.1
        ((hfr _ (by omega)).2.2 _)]
      exact l176
    have e52 : R5 2 = BitVec.ofNat 64 (sp - 192) := by rw [k5.get 2 (by decide)]; bsimp [e2]
    bsimp []
    bc_run hlive hlive [hs5, e52] at 0x80000c14
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact (hc5.mod (by keeps_tac Keeps.refl _ _)).close (st' := st.push (.str [])) hlive hk (.evalTos _) (ex := []) h5 (by simp)
      (by simp [hlk]) hpin (by bsimp [])
  · exact hcv.oom ho (Wc := 64) (by omega) (by omega) (by omega) e5 fun a e1 e2 _ e4 => hout5 a e1 e2 e4

/-- `?` after `dc_readstring` (`0x80000d0c`): the datum spilled to the frame,
`ferror (stdin)` (`0`), then `fq_push`. -/
theorem fq_tail (hlive : ∀ p ∈ dcText, live p.1) {st : St} {p : Nat} {v8 : BitVec 64} {M2 : Mem}
    {H2 : Heap} {G G' : DcG} {R2 : Nat → BitVec 64}
    (h2 : DcAt S M2 H2 F L C G' (.str p :: hs) st) (hv : (GV.str p).Den ⟨L, G'.strs⟩ (.str []))
    (hcv : FnAt S sp W M0 R0 (VsaIris.Sym.upd R2 8 v8) M2) (hW : 192 + 128 ≤ W)
    (ho : FnOom live S Q sp W M0) (e2 : R2 2 = BitVec.ofNat 64 (sp - 192))
    (e10 : (R2 10).toNat % 2 ^ 32 = 2) (e11 : R2 11 = BitVec.ofNat 64 p)
    (hs0 : ldv .ld M2 (sp - 192 + 176) = v8)
    (hlk : G'.lk = G.lk) (hpin : StrPin G.strs G'.strs hs)
    (hk : FnK live S Q t0 st (.evalTos (st.push (.str []))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000d0c#64 R2 M2 := by
  fv_frame hcv
  bc_run hlive hlive [e2] at 0x8000071c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hm3 : MemOnly (fun a => sp - 192 + 16 ≤ a ∧ a < sp - 192 + 32)
      (writeLog (writeLog M2 [(sp - 192 + 16, 8, R2 10)]) [(sp - 192 + 24, 8, R2 11)]) M2 :=
    fun a ha => by rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have h3 := h2.outWrite hm3 fun a ha => ⟨(hfr a (by omega)).1, (hfr a (by omega)).2.1⟩
  have hcv3 : FnAt S sp W M0 R0 (VsaIris.Sym.upd R2 8 v8)
      (writeLog (writeLog M2 [(sp - 192 + 16, 8, R2 10)]) [(sp - 192 + 24, 8, R2 11)]) :=
    hcv.callL (Wc := 0) (by omega) (Keeps.refl _ _) rfl fun a _ _ _ _ e5 =>
      hm3 a (by simp only [frameIn] at e5; omega)
  refine ferror_spec hlive _ (by bsimp []) fun R3 k3 e3 => ?_
  have e32 : R3 2 = BitVec.ofNat 64 (sp - 192) := (k3.get 2 (by decide)).trans (by bsimp [e2])
  bsimp []
  refine fq_push hlive h3 hv (hcv3.mod (Keeps.updSame ((k3.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) 8 v8)) hW ho e32 e3
    (by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]) e10 (ldv_store_hit _ _ _ |>.trans e11)
    (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hs0) hlk hpin hk

/-- `?` at the call of `dc_readstring` (`s0` spilled, `stdin` in `a0`):
the new empty string, then `fq_tail`. -/
theorem fq_rs (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {G : DcG}
    {R Rq : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 128 ≤ W)
    (ho : FnOom live S Q sp W M0) (kq : Keeps (8 :: 1 :: 2 :: cClob) Rq R)
    (eq2 : Rq 2 = BitVec.ofNat 64 (sp - 192)) (eq1 : Rq 1 = 0x80000d0c#64)
    (hk : FnK live S Q t0 st (.evalTos (st.push (.str []))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80003ad8#64 Rq (writeLog M [(sp - 192 + 176, 8, R 8)]) := by
  fv_frame hc
  have e2 := hc.r2
  have hm : MemOnly (fun a => sp - 192 + 176 ≤ a ∧ a < sp - 192 + 176 + 8)
      (writeLog M [(sp - 192 + 176, 8, R 8)]) M := MemOnly.store M _ 8 _
  have h0 := h.outWrite hm fun a ha => ⟨(hfr a (by omega)).1, (hfr a (by omega)).2.1⟩
  have hcq : FnAt S sp W M0 R0 R (writeLog M [(sp - 192 + 176, 8, R 8)]) :=
    hc.callL (Wc := 0) (by omega) (Keeps.refl _ _) rfl fun a _ _ _ _ e5 =>
      hm a (by simp only [frameIn] at e5; omega)
  refine dc_readstring_spec hlive h0 (hc.cf (Wc := 128) (by omega)) (hc.cab (by omega)) _
    (by bsimp [eq2]) (by rw [eq1]; decide) (fun R2 M2 H2 G2 b1 b2 k2 e22 e10 e11 hnext h2 hout2 => ?_)
    (fun R2 M2 e2' hout2 => hcq.oom ho (Wc := 128) (by omega) (by omega) (by omega) e2'
      fun a e1 e2 _ e4 => hout2 a e1 e2 e4)
  have e2b : R2 2 = BitVec.ofNat 64 (sp - 192) := by rw [k2.get 2 (by decide)]; exact eq2
  have hcv : FnAt S sp W M0 R0 (VsaIris.Sym.upd R2 8 (R 8)) M2 :=
    hc.callL (Wc := 128) (by omega)
      (Keeps.restore rfl ((k2.mono (by decide)).trans kq))
      (by rw [upd_other _ _ (by decide)]; exact e2b.trans e2.symm)
      fun a e1 e2 _ e4 e5 => (hout2 a e1 e2 e4).trans (hm a (by simp only [frameIn] at e5; omega))
  have hs0 : ldv .ld M2 (sp - 192 + 176) = R 8 := by
    rw [ldv_congr .ld fun j hj => hout2 _ (hfr _ (by omega)).1 (hfr _ (by omega)).2.1
      ((hfr _ (by omega)).2.2 _)]
    exact ldv_store_hit _ _ _
  rw [eq1]
  exact fq_tail hlive h2 ⟨msObj b1 b2 [], List.mem_cons_self, rfl, rfl⟩ hcv hW ho e2b e10 e11 hs0
    hnext.lk (by rw [hnext.strs]; exact StrPin.cons _ _ _) hk

/-- `?` (`0x80000ccc`): `DC_EVALTOS` on a new empty string read from the
exhausted input. -/
theorem fa_query (hlive : ∀ p ∈ dcText, live p.1) {st : St} {M : Mem} {H : Heap} {G : DcG}
    {R : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 128 ≤ W)
    (ho : FnOom live S Q sp W M0)
    (hlaS : ∀ a, 0x8001cd30 ≤ a → a < 0x8001cd34 → S a)
    (hla : ldv .lw M 0x8001cd30 = 0xFFFFFFFFFFFFFFFF#64)
    (hk : FnK live S Q t0 st (dcFunc 70 st 63 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000ccc#64 R M := by
  fv_frame hc
  have e2 := hc.r2
  have hro : ∀ b ∈ accAddrs 2147516944 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  have hlaA : ∀ b ∈ accAddrs 2147601712 4, S b := fun b hb => by
    have := of_mem_accAddrs hb; exact hlaS b (by omega) (by omega)
  bc_run hlive hlive [e2, hla, stdin_word] at 0x80003ad8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hlive [e2, hla, stdin_word] at 0x80003ad8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hr : dcFunc 70 st 63 peek neg = .evalTos (st.push (.str [])) := rfl
  rw [hr] at hk
  exact fq_rs hlive h hc hW ho (by keeps_tac Keeps.refl _ _) (by bsimp [e2]) (by bsimp []) hk

end

end Dc.Mach
