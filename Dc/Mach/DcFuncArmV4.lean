import Dc.Mach.DcFuncArmV3
import Dc.Mach.DcShowId

/-!
# `dc_func`'s default arm (M10)

A character without a command (`0x80000c30`): `fprintf (stderr, "%s: ",
progname)`, then `dc_show_id (stdout, c, " unimplemented\n")`, whose bytes
are the model's `unimplemented c` (`showId_unimpl_bytes`, decided over
`c < 256`), and `DC_OKAY`. The character arrives in `a3` (`dcf_disp_out`
and the table dispatch copy `a0` there).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `" unimplemented\n"` at `0x80007b28`. -/
theorem unimplMsg : RtMsg 0x80007b28 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide⟩

/-- `"%s: "` at `0x80007b20`. -/
theorem unimplPre : ProgMsg 0x80007b20 2 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

theorem showId_unimpl_bytes : ∀ c, c < 256 →
    showIdBytes c 0x80007b28 (msgBytes 0x80007b28 15) = (unimplemented c).map (BitVec.ofNat 8) := by
  decide +kernel

theorem unimpl_lt : ∀ c, c < 256 → ∀ x ∈ unimplemented c, x < 256 := by decide +kernel

/-- Bytes below `256` as console text. -/
theorem bytesStr_map : ∀ (l : List Nat), (∀ x ∈ l, x < 256) →
    bytesStr (l.map (BitVec.ofNat 8)) = Dc.outStr l
  | [], _ => rfl
  | x :: l, h => by
    have hx := h x List.mem_cons_self
    rw [List.map_cons, bytesStr, bytesStr_map l fun y hy => h y (List.mem_cons_of_mem _ hy),
      show x :: l = [x] ++ l from rfl, outStr_append]
    simp only [putcStr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
    rfl

/-- The state relation does not read the output. -/
theorem DcAt.emit {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    (bs : List Nat) : DcAt S M H F L C G hs (st.emit bs) where
  heap := h.heap
  nodup := h.nodup
  view := { h.view with }
  den := { h.den with }
  glob := h.glob
  col := h.col

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {M0 : Mem} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {hs : List GV} {sp W : Nat} {R0 : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- The default arm after its `stderr` prefix (`0x80000c50`): `dc_show_id` to
`stdout`, `DC_OKAY`. -/
theorem fd_show (hlive : ∀ p ∈ dcText, live p.1) {st : St} {c : Nat} {M2 : Mem} {H : Heap}
    {G : DcG} {R2 : Nat → BitVec 64}
    (h2 : DcAt S M2 H F L C G hs st) (hc2 : FnAt S sp W M0 R0 R2 M2) (hW : 192 + 304 ≤ W)
    (hcc : c < 256) (e2 : R2 2 = BitVec.ofNat 64 (sp - 192))
    (hc0 : ldv .ld M2 (sp - 192) = BitVec.ofNat 64 c)
    (hk : FnK live S Q t0 st (.ok (st.emit (unimplemented c))) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000c50#64 R2 M2 := by
  fv_frame hc2
  have hro : ∀ b ∈ accAddrs 2147516936 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hlive [e2, hc0, stdout_word] at 0x80001ec0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hfd : FdAt S M2 stdoutFile 1 :=
    ⟨fun i hi => h2.glob _ (by simp only [DcGlob, stdoutFile, dc_addrs]; omega),
      h2.view.outFd, by decide, by decide, by decide⟩
  refine dc_show_id_spec hlive (sp := sp - 192) (f := stdoutFile) (fd := 1) (id := c)
    (m := 0x80007b28) (hc2.cf (Wc := 304) (by omega)) hfd (.inl (by simp only [stdoutFile]; omega))
    unimplMsg.roStr (by rw [msgBytes_length]; decide) _ (by bsimp [stdoutFile]) (by bsimp [])
    (by omega) (by bsimp []) (by bsimp [e2]) (by bsimp []) fun R3 M3 k3 hfr3 => ?_
  rw [fdOut_one, showId_unimpl_bytes c hcc, bytesStr_map _ (unimpl_lt c hcc), String.append_assoc,
    ← outStr_append]
  have hc3 := hc2.call (R' := R3) (M' := M3) (Wc := 304) (by omega)
    (by keeps_tac ((k3.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    ((k3.get 2 (by decide)).trans (by bsimp []))
    fun a _ _ _ hf => hfr3 a (by simp only [frameIn] at hf; omega)
  have h3 : DcAt S M3 H F L C G hs st :=
    h2.outWrite (P := frameIn (sp - 192) 304)
      (fun a ha => hfr3 a (by simp only [frameIn] at ha; omega)) fun a ha => by
        simp only [frameIn] at ha
        exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
          have := hg.lt; simp only [heapStart] at this; omega⟩
  bsimp []
  bc_run hlive hlive [] at 0x80000c10
  exact fa_ok (st' := st.emit (unimplemented c)) hlive (ex := []) (h3.emit _) hc3 hk (.ok _) (by simp)
    (by simp) (StrPin.refl _ _)

/-- The default arm (`0x80000c30`, the character `c` in `a3`): the
`unimplemented` diagnostic, `DC_OKAY`. -/
theorem fa_default (hlive : ∀ p ∈ dcText, live p.1) {st : St} {c : Nat} {M : Mem} {H : Heap}
    {G : DcG} {R : Nat → BitVec 64}
    (hcd : dcFunc 70 st c peek neg = .ok (st.emit (unimplemented c))) (hcc : c < 256)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 304 ≤ W)
    (h13 : R 13 = BitVec.ofNat 64 c)
    (hk : FnK live S Q t0 st (dcFunc 70 st c peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000c30#64 R M := by
  rw [hcd] at hk
  fv_frame hc
  have e2 := hc.r2
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hG := h.glob
  have hpn := h.view.prog
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hS [e2, hpn, stderr_word] at 0x80000774
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hm1 : MemOnly (fun a => sp - 192 ≤ a ∧ a < sp - 192 + 8)
      (writeLog M [(sp - 192, 8, R 13)]) M := MemOnly.store M _ 8 _
  have h1 := h.outWrite hm1 fun a ha => ⟨(hfr a (by omega)).1, (hfr a (by omega)).2.1⟩
  have hc1 : FnAt S sp W M0 R0 R (writeLog M [(sp - 192, 8, R 13)]) :=
    hc.callL (Wc := 0) (by omega) (Keeps.refl _ _) rfl fun a _ _ _ _ e5 =>
      hm1 a (by simp only [frameIn] at e5; omega)
  refine fprintf_prog_spec hlive unimplPre (by decide) (hc.cf (Wc := 304) (by omega))
    (by simp only [stderrAddr]; omega) h1.errFile _ (by bsimp [e2]) (by bsimp [stderrAddr])
    (by bsimp []) (by bsimp []) (by bsimp []) fun R2 M2 k2 hfr2 => ?_
  have hc2 := hc1.call (R' := R2) (M' := M2) (Wc := 304) (by omega)
    (by keeps_tac ((k2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    ((k2.get 2 (by decide)).trans (by bsimp []))
    fun a _ _ _ hf => hfr2 a (by simp only [frameIn] at hf; omega)
  have h2 : DcAt S M2 H F L C G hs st :=
    h1.outWrite (P := frameIn (sp - 192) 304)
      (fun a ha => hfr2 a (by simp only [frameIn] at ha; omega)) fun a ha => by
        simp only [frameIn] at ha
        exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
          have := hg.lt; simp only [heapStart] at this; omega⟩
  have hc0 : ldv .ld M2 (sp - 192) = BitVec.ofNat 64 c := by
    rw [ldv_congr .ld fun j hj => hfr2 _ (.inr (by simp only [widthOfM] at hj; omega)),
      ldv_store_hit, h13]
  bsimp []
  exact fd_show hlive h2 hc2 hW hcc ((k2.get 2 (by decide)).trans (by bsimp [e2])) hc0 hk

end

end Dc.Mach
