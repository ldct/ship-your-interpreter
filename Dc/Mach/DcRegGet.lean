import Dc.Mach.DcInt
import Dc.Mach.DcShowId
import Dc.Mach.DcTop

/-!
# `dc_register_get` (M9)

    if (!r) dc_int2data (0) to *result;          (an unused register reads 0)
    else if (r->value.dc_type == DC_UNINITIALIZED)
      fprintf (stderr, "%s: BUG: register "); dc_show_id (stderr, regid,
        " exists but is uninitialized?\n"); return DC_FAIL;
    else *result = dc_dup (r->value);

`dc_register_get_spec`: `regGet st r` is the value copied to the slot `q`
(one more reference, `dc_dup` or a fresh zero), or `none` and the status `2`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A message without `%` is a string of `.rodata`. -/
theorem RtMsg.roStr {p n : Nat} (h : RtMsg p n) : RoStr p (msgBytes p n) :=
  ⟨h.ro_bytes, fun b hb => by
    simp only [msgBytes, List.mem_map, List.mem_range] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact (h.lit i hi).1⟩

/-- `"%s: BUG: register "` at `0x80007da8`. -/
theorem regBugMsg : ProgMsg 0x80007da8 16 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

/-- `" exists but is uninitialized?\n"` at `0x80007dc0`. -/
theorem regUninitMsg : RtMsg 0x80007dc0 30 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide⟩

theorem ldvf_stderr {a : BitVec 64} (ha : a.toNat = 2147516928) :
    ldvf .ld dcROImg a.toNat = BitVec.ofNat 64 stderrAddr := by
  rw [ha]; exact stderr_word

/-- `dc_register_get` on a level without value (`0x80002f70`, `sp` lowered
by 32, `a5` the register): the two messages to `stderr`, status `2`. -/
theorem reg_get_err {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp r : Nat} (hr : r < 256)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h15 : R 15 = BitVec.ofNat 64 r)
    {ra : BitVec 64} (hra : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M', Keeps (1 :: 2 :: fprintfClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 10 = 2#64 → (∀ a, (a < sp - 336 ∨ sp ≤ a) → imgM M' a = imgM M a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x80002f70#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hpn := h.view.prog
  have hG := h.glob
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  refine st_80002f70 hlive ?_
  refine stR_80002f74 hlive ?_ ?_ ?_
  · bsimp []; decide
  · bsimp []; exact hro
  rw [ldvf_stderr (by bsimp []; decide)]
  refine st_80002f78 hlive ?_
  refine st_80002f7c hlive ?_ ?_ ?_
  · bsimp []; decide
  · bsimp []
    rw [show (2147495800#64 + BitVec.signExtend 64 (26#20 +++ 0#12) + 18446744073709551080#64).toNat =
      0x8001cd60 by decide]
    intro b hb; have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs]; omega)
  bc_run hlive hS [h2, hpn, h15] at 0x80000774
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hwin : ∀ a, (a < sp - 336 ∨ sp ≤ a) → a < sp - 32 - 304 ∨ sp - 32 ≤ a :=
    fun a ha => by rw [Nat.sub_sub]; omega
  have hfd := h.errFile.transport (M' := writeLog (writeLog M [(sp - 32 + 8, 8, BitVec.ofNat 64 r)])
      [(sp - 32, 8, BitVec.ofNat 64 stderrAddr)]) fun j hj => by
    simp only [stderrAddr] at *
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  refine fprintf_prog_spec hlive regBugMsg (by decide) (hsf.sub (m := 32) (n := 304) (by decide))
    (by simp only [stderrAddr]; omega) hfd _ (by bsimp [h2]) (by bsimp [stderrAddr]) (by bsimp [])
    (by bsimp []) (by bsimp []) fun R1 M1 hk1 hfr1 => ?_
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  have hl0 : ldv .ld M1 (sp - 32) = BitVec.ofNat 64 stderrAddr := by
    rw [ldv_congr .ld fun j hj => hfr1 _ (.inr (by simp only [widthOfM] at hj; omega))]
    exact ldv_store_hit _ _ _
  have hl1 : ldv .ld M1 (sp - 32 + 8) = BitVec.ofNat 64 r := by
    rw [ldv_congr .ld fun j hj => hfr1 _ (.inr (by simp only [widthOfM] at hj; omega))]
    rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _
  bsimp []
  bc_run hlive hS [q2, hl0, hl1] at 0x80001ec0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hfd1 := hfd.transport (M' := M1) fun j hj => hfr1 _ (.inl (by simp only [stderrAddr]; omega))
  refine dc_show_id_spec hlive (sp := sp - 32) (f := stderrAddr) (fd := 2) (id := r) (m := 0x80007dc0)
    (hsf.sub (m := 32) (n := 304) (by decide)) hfd1 (.inl (by simp only [stderrAddr]; omega))
    regUninitMsg.roStr (by rw [msgBytes_length]; decide) _ (by bsimp [stderrAddr]) (by bsimp [])
    (by omega) (by bsimp []) (by bsimp [q2]) (by bsimp []) fun R2 M2 out hk2 hfr2 => ?_
  rw [fdOut_ne (by decide), String.append_empty]
  have q3 : R2 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk2.get 2]; bsimp [q2]
  have hra2 : ldv .ld M2 (sp - 32 + 24) = ra := by
    rw [ldv_congr .ld fun j hj => (hfr2 _ (.inr (by simp only [widthOfM] at hj; omega))).trans
      (hfr1 _ (.inr (by simp only [widthOfM] at hj; omega)))]
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hra
  bsimp []
  bc_run hlive hS [q3, hra2]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hal
  refine hk _ M2 (by keeps_tac (((hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)).trans
      ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))
    (by bsimp []) (by rw [upd_same]; congr 1; omega) (by bsimp []) fun a ha => ?_
  rw [hfr2 a (hwin a ha), hfr1 a (hwin a ha), imgM_store_miss _ _ (by omega),
    imgM_store_miss _ _ (by omega)]

end Dc.Mach
