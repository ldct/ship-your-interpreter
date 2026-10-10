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

/-- The bytes `dc_register_get` changes outside its frame and the slot: none. -/
def GetOut (sp q : Nat) (M' M : Mem) : Prop :=
  ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 336 a → (a < q ∨ q + 16 ≤ a) → imgM M' a = imgM M a

/-- The slot stores `*result = d` and the epilogue at `0x80002f58`/`0x80002fcc`
(`sp` lowered by 32): the datum `g` in `a0`/`a1` lands at `q`. -/
theorem slotMem_dat {M : Mem} {q : Nat} {w0 w1 : BitVec 64} {g : GV} (hd : DatRegs w0 w1 g) :
    DatAt (writeLog (writeLog M [(q, 8, w0)]) [(q + 8, 8, w1)]) q g :=
  ⟨by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]; exact hd.tag,
    by rw [ldv_store_hit]; exact hd.ptr⟩

/-- `dc_register_get` on a level with a value (`0x80002f44`, `sp` lowered by
32, `a4` the level's node at `a`): `dc_dup` of the value into the slot `q`. -/
theorem reg_get_dup {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) {sp q a : Nat} {g : GV} {v : Val}
    (hv : g.Den ⟨L, G.strs⟩ v) (hd : DatAt M a g) (hal16 : heapStart ≤ a ∧ a + 16 ≤ heapEnd ∧ a % 8 = 0)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h11 : R 11 = BitVec.ofNat 64 q)
    (h14 : R 14 = BitVec.ofNat 64 a)
    {ra : BitVec 64} (hra : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' L' C' G', Keeps (1 :: 2 :: popClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 10 = 0#64 → SameNodes G G' → DcAt S M' H F L' C' G' (g :: hs) st →
      g.Den ⟨L', G'.strs⟩ v → DatAt M' q g → GetOut sp q M' M → StrPin G.strs G'.strs hs →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x80002f44#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hq1 := hq.lo; have hq2 := hq.hi; have hq3 := hq.al
  obtain ⟨ha1, ha2, ha3⟩ := hal16
  simp only [heapEnd, heapStart] at hab ha1 ha2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hP : ∀ x, frameIn sp 336 x → OutHeap x ∧ ¬ DcGlob x := fun x hx => by
    simp only [frameIn] at hx
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have hl0 : ldv .ld (writeLog M [(sp - 32, 8, BitVec.ofNat 64 q)]) a = ldv .ld M a :=
    ldv_ld_miss _ _ (by omega)
  have hl1 : ldv .ld (writeLog M [(sp - 32, 8, BitVec.ofNat 64 q)]) (a + 8) = ldv .ld M (a + 8) :=
    ldv_ld_miss _ _ (by omega)
  bc_run hlive hS [h2, h11, h14, hl0, hl1] at 0x800020a0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 336) (writeLog M [(sp - 32, 8, BitVec.ofNat 64 q)]) M :=
    fun x hx => by simp only [frameIn] at hx; rw [imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hM1 hP
  refine dc_dup_spec hlive h1 hhs hv
    (StackFrame.sub (m := 32) (n := 16) (hsf.shrink (m := 48) (by omega)) (by decide))
    (by simp only [heapEnd]; omega) _ ⟨?_, ?_⟩
    (by bsimp [h2]) (by bsimp []) fun R1 M2 L' C' G' hk1 hd' hsn h' hden hfr hpin => ?_
  · rw [ldv_ld_miss _ _ (by omega)]; exact hd.tag
  · bsimp []; rw [ldv_ld_miss _ _ (by omega)]; exact hd.ptr
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  have hfs : ∀ x, sp - 24 ≤ x → x < sp → imgM M2 x = imgM M x := fun x hx1 hx2 => by
    have hin : frameIn sp 336 x := by simp only [frameIn]; omega
    have hnf : ¬ frameIn (sp - 32) 16 x := by simp only [frameIn]; omega
    rw [hfr x (hP x hin).1 (hP x hin).2 hnf, imgM_store_miss _ _ (by omega)]
  have hlq : ldv .ld M2 (sp - 32) = BitVec.ofNat 64 q := by
    rw [ldv_congr .ld fun j hj => hfr _ (hP _ (by simp only [frameIn, widthOfM] at hj ⊢; omega)).1
      (hP _ (by simp only [frameIn, widthOfM] at hj ⊢; omega)).2
      (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact ldv_store_hit _ _ _
  have hra2 : ldv .ld M2 (sp - 32 + 24) = ra := by
    rw [ldv_congr .ld fun j hj => hfs _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)]; exact hra
  bsimp []
  bc_run hlive hS [q2, hlq, hra2]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first
    | (intro b hb; have := of_mem_accAddrs hb; have := hq.own (b - q) (by omega)
       rwa [Nat.add_sub_cancel' (by omega)] at this)
    | (rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), hra2]; exact hal)
    | skip
  have e : ldv .ld (writeLog (writeLog M2 [(q, 8, R1 10)]) [(q + 8, 8, R1 11)]) (sp - 32 + 24) = ra := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), hra2]
  rw [e]
  have hMq : MemOnly (fun x => q ≤ x ∧ x < q + 16)
      (writeLog (writeLog M2 [(q, 8, R1 10)]) [(q + 8, 8, R1 11)]) M2 := fun x hx => by
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  refine hk _ _ L' C' G' (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (by bsimp []) (by bsimp []; congr 1; omega) (by bsimp []) hsn
    (h'.outWrite hMq fun x hx => ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩) hden (slotMem_dat hd') ?_ hpin
  intro x ho hg hf hqx
  rw [hMq x (by omega), hfr x ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))]
  exact hM1 x hf

/-- `dc_register_get` on a register without levels (`0x80002fbc`, `sp`
lowered by 32): a fresh zero into the slot `q`, or `out_of_memory`. -/
theorem reg_get_zero {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) {sp q : Nat}
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (h11 : R 11 = BitVec.ofNat 64 q)
    {ra : BitVec 64} (hra : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' g, Keeps (1 :: 2 :: popClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 10 = 0#64 → DcAt S M' H' F' L' C' G (g :: hs) st →
      g.Den ⟨L', G.strs⟩ (.num (Num.zero 0)) → DatAt M' q g → GetOut sp q M' M →
      DWO live S Q t ra R' M')
    (hoom : ∀ R' M', GetOut sp q M' M → DWO live S Q t 0x80002bcc#64 R' M') :
    DWO live S Q t 0x80002fbc#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hq1 := hq.lo; have hq2 := hq.hi; have hq3 := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hP : ∀ x, frameIn sp 336 x → OutHeap x ∧ ¬ DcGlob x := fun x hx => by
    simp only [frameIn] at hx
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  bc_run hlive hS [h2, h11] at 0x800026d8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 336) (writeLog M [(sp - 32, 8, BitVec.ofNat 64 q)]) M :=
    fun x hx => by simp only [frameIn] at hx; rw [imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hM1 hP
  refine dc_int2data_spec hlive h1 hhs (v := 0)
    (StackFrame.sub (m := 32) (n := 192) (hsf.shrink (m := 224) (by omega)) (by decide))
    (by simp only [heapEnd]; omega) _ (by bsimp []; rfl) (by bsimp [h2]) (by bsimp []) (by decide)
    (by decide) (fun R1 M2 H' F' L' C' g hk1 hd' hden h' hfr => ?_) (fun R1 M2 _ hfr => ?_)
  rotate_left
  · refine hoom R1 M2 fun x ho hg hf _ => ?_
    rw [hfr x ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))]
    exact hM1 x hf
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
  have hfs : ∀ x, sp - 32 ≤ x → x < sp → imgM M2 x = imgM (writeLog M [(sp - 32, 8, BitVec.ofNat 64 q)]) x :=
    fun x hx1 hx2 => by
      have hin : frameIn sp 336 x := by simp only [frameIn]; omega
      exact hfr x (hP x hin).1 (hP x hin).2 (by simp only [frameIn]; omega)
  have hlq : ldv .ld M2 (sp - 32) = BitVec.ofNat 64 q := by
    rw [ldv_congr .ld fun j hj => hfs _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)]
    exact ldv_store_hit _ _ _
  have hra2 : ldv .ld M2 (sp - 32 + 24) = ra := by
    rw [ldv_congr .ld fun j hj => hfs _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)]
    rw [ldv_ld_miss _ _ (by omega)]; exact hra
  bsimp []
  bc_run hlive hS [q2, hlq]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first
    | (intro b hb; have := of_mem_accAddrs hb; have := hq.own (b - q) (by omega)
       rwa [Nat.add_sub_cancel' (by omega)] at this)
    | (rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), hra2]; exact hal)
    | skip
  have e : ldv .ld (writeLog (writeLog M2 [(q, 8, R1 10)]) [(q + 8, 8, R1 11)]) (sp - 32 + 24) = ra := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), hra2]
  rw [e]
  have hMq : MemOnly (fun x => q ≤ x ∧ x < q + 16)
      (writeLog (writeLog M2 [(q, 8, R1 10)]) [(q + 8, 8, R1 11)]) M2 := fun x hx => by
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  refine hk _ _ H' F' L' C' g (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    (by bsimp []) (by bsimp []; congr 1; omega) (by bsimp [])
    (h'.outWrite hMq fun x hx => ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩) hden (slotMem_dat hd') ?_
  intro x ho hg hf hqx
  rw [hMq x (by omega), hfr x ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))]
  exact hM1 x hf

/-- `zext.b; slli 3; add` of a register number `r < 256` onto `dc_register`. -/
theorem regWord_addr {r : Nat} (hr : r < 256) :
    2147601872#64 + (BitVec.ofNat 64 r &&& 255#64) <<< 3 = BitVec.ofNat 64 (regAddr r) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, toNat_and255]
  simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr, Nat.shiftLeft_eq]
  omega

theorem and255_small {r : Nat} (hr : r < 256) : BitVec.ofNat 64 r &&& 255#64 = BitVec.ofNat 64 r := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and255]; simp only [BitVec.toNat_ofNat]; omega

/-- **`dc_register_get(regid, result)`** at `0x80002f18`, `r = regid`: the
value `regGet st r` copied to the slot `q` with one more reference (`hk`),
or none and the status `2` (`hkn`); a fresh zero may run out of memory. -/
theorem dc_register_get_spec {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) {sp q r : Nat} (hr : r < 256)
    (hsf : StackFrame S sp 336) (hab : heapEnd + 336 ≤ sp) (hq : DatSlot S sp q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 r) (h11 : R 11 = BitVec.ofNat 64 q)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G' g v, regGet st r = some v → Keeps popClob R' R → R' 10 = 0#64 →
      SameNodes G G' → DcAt S M' H' F' L' C' G' (g :: hs) st → g.Den ⟨L', G'.strs⟩ v →
      DatAt M' q g → GetOut sp q M' M → StrPin G.strs G'.strs hs → DWO live S Q t (R 1) R' M')
    (hkn : regGet st r = none → ∀ R' M', Keeps popClob R' R → R' 10 = 2#64 →
      DcAt S M' H F L C G hs st → GetOut sp q M' M → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M', GetOut sp q M' M → DWO live S Q t 0x80002bcc#64 R' M') :
    DWO live S Q t 0x80002f18#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hP : ∀ x, frameIn sp 336 x → OutHeap x ∧ ¬ DcGlob x := fun x hx => by
    simp only [frameIn] at hx
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have hM1 : MemOnly (frameIn sp 336) (writeLog M [(sp - 32 + 24, 8, R 1)]) M :=
    fun x hx => by simp only [frameIn] at hx; rw [imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hM1 hP
  have hout : ∀ M', GetOut sp q M' (writeLog M [(sp - 32 + 24, 8, R 1)]) → GetOut sp q M' M :=
    fun M' hm x ho hg hf hqx => (hm x ho hg hf hqx).trans (hM1 x hf)
  have hv := h.view.regs r hr
  have hd := h.den.regs r hr
  have hmem : ∀ b e, (b, e) ∈ G.regs r → b ∈ G.blocks := fun b e hbe => by
    unfold DcG.blocks
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    exact List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, List.mem_flatMap.mpr ⟨(b, e), hbe,
      List.mem_cons_self⟩⟩
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  have hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs, regAddr] at this ⊢; omega)
  generalize hl : G.regs r = l at hv hd hmem
  cases hv with
  | nil h0 =>
    have hst : st.regs r = [] := by
      revert hd; generalize st.regs r = m; intro hd; cases hd; rfl
    have hget : regGet st r = some (.num (Num.zero 0)) := by unfold regGet; rw [hst]
    bc_run hlive hS [h2, h10, regWord_addr hr, hra8, h0] at 0x80002fbc
    all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [LdOK, regAddr, dcRegAddr]; omega) | skip
    refine reg_get_zero hlive h1 hhs hsf (by simp only [heapEnd]; omega) hq _ (by bsimp [h2])
      (by bsimp [h11]) (ldv_store_hit _ _ _) hal (fun R' M' H' F' L' C' g hk1 e1 e2 e10 h' hden hdat hfr => ?_)
      (fun R' M' hfr => hoom R' M' (hout M' hfr))
    exact hk R' M' H' F' L' C' G g _ hget
      (hk1.restore2 (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2])) e10 ⟨rfl, rfl, rfl⟩ h' hden hdat
      (hout M' hfr) (StrPin.refl _ _)
  | @cons _ b e l' h0 hb hl' =>
    obtain ⟨v0, rest, hst, hde⟩ : ∃ v0 rest, st.regs r = v0 :: rest ∧ e.Den ⟨L, G.strs⟩ v0 := by
      revert hd; generalize st.regs r = m; intro hd; cases hd with | cons h _ => exact ⟨_, _, rfl, h⟩
    have hget : regGet st r = v0.val := by unfold regGet; rw [hst]
    have hcG := hmem b e List.mem_cons_self
    have fbb := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live b hcG))
    have hsz := hb.sz
    have hpl : 2147603936 ≤ b.pay ∧ b.pay + 32 ≤ 2273312768 ∧ b.pay % 16 = 0 := by
      have a1 : 2147603920 ≤ b.h := fbb.lo
      have a2 : b.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
      have a3 : b.h % 16 = 0 := fbb.al
      have e1 : b.pay = b.h + 16 := rfl
      have e2 : b.fin = b.h + 16 + b.sz := rfl
      omega
    obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
    have hc0 : BitVec.ofNat 64 b.pay ≠ 0#64 := fun hc => by
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat] at this
      omega
    have hdat := hb.dat
    have hval := hde.val
    revert hdat hval
    cases hev : e.v with
    | none =>
      intro hdat hval
      have hn : v0.val = none := by
        revert hval; generalize v0.val = w; intro hval; cases hval; rfl
      bc_run hlive hS [h2, h10, regWord_addr hr, hra8, h0, ldv_lw_miss M (R 1) (a := b.pay)
        (b := sp - 32 + 24) (w := 8) (by omega), hdat] at 0x80002f70
      all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [LdOK, regAddr, dcRegAddr]; omega) | skip
      all_goals try (intro hc; exact absurd hc hc0)
      intro _
      bc_run hlive hS [h2, h10, regWord_addr hr, hra8, h0, ldv_lw_miss M (R 1) (a := b.pay)
        (b := sp - 32 + 24) (w := 8) (by omega), hdat] at 0x80002f70
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      refine reg_get_err hlive h1 hr hsf (by simp only [heapEnd]; omega) _ (by bsimp [h2])
        (by bsimp [and255_small hr]) (ldv_store_hit _ _ _) hal fun R' M' hk1 e1 e2 e10 hfr => ?_
      have hfr' : MemOnly (frameIn sp 336) M' (writeLog M [(sp - 32 + 24, 8, R 1)]) :=
        fun x hx => hfr x (by simp only [frameIn] at hx; omega)
      exact hkn (by rw [hget, hn]) R' M'
        (hk1.restore2 (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2])) e10 (h1.outWrite hfr' hP)
        (hout M' fun x _ _ hf _ => hfr' x hf)
    | some g =>
      intro hdat hval
      obtain ⟨v, hv0, hgv⟩ : ∃ v, v0.val = some v ∧ g.Den ⟨L, G.strs⟩ v := by
        revert hval; generalize v0.val = w; intro hval; cases hval with | some h => exact ⟨_, rfl, h⟩
      have hlw := hdat.lw
      have hne : BitVec.ofNat 64 g.tag ≠ 0#64 := by cases g <;> simp only [GV.tag] <;> decide
      have hdat1 : DatAt (writeLog M [(sp - 32 + 24, 8, R 1)]) b.pay g :=
        ⟨by rw [ldv_ld_miss _ _ (by omega)]; exact hdat.tag,
          by rw [ldv_ld_miss _ _ (by omega)]; exact hdat.ptr⟩
      bc_run hlive hS [h2, h10, regWord_addr hr, hra8, h0] at 0x80002f44
      all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [LdOK, regAddr, dcRegAddr]; omega) | skip
      all_goals try (intro hc; exact absurd hc hc0)
      intro _
      bc_run hlive hS [h2, h10, regWord_addr hr, hra8, h0, ldv_lw_miss M (R 1) (a := b.pay)
        (b := sp - 32 + 24) (w := 8) (by omega), hlw] at 0x80002f44
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      all_goals try (intro hc; exact absurd hc hne)
      intro _
      refine reg_get_dup hlive h1 hhs hgv hdat1 ⟨by simp only [heapStart]; omega,
        by simp only [heapEnd]; omega, by omega⟩ hsf (by simp only [heapEnd]; omega) hq _
        (by bsimp [h2]) (by bsimp [h11]) (by bsimp []) (ldv_store_hit _ _ _) hal
        fun R' M' L' C' G' hk1 e1 e2 e10 hsn h' hden hd' hfr hpin => ?_
      exact hk R' M' H F L' C' G' g v (by rw [hget, hv0])
        (hk1.restore2 (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2])) e10 hsn h' hden hd' (hout M' hfr) hpin

end Dc.Mach
