import Dc.Mach.DcOutChar
import Dc.Mach.DcSqrt

/-!
# `dc_out_num` (M9)

    dc_out_num (value, obase, discard):
      out_col = 0;
      bc_out_num (value, obase, out_char, 0);
      if (discard == DC_TOSS) bc_free_num (&value);

- `outChars_ne_zero`: `bc_out_num` sends no NUL, so `out_char`'s `ocRun` is
  the model's `Num.out 70`.
- `DcAt.ocRet`: the state through `bc_out_num` with dc's `out_char`.
- `dc_out_num_spec`: the console extended by `Num.out 70 obase n`, the
  handle kept or released.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-! ## The model: no NUL -/

theorem decText_ne_zero (v : Nat) : ∀ c ∈ Dc.Num.decText v, c ≠ 0 := by
  intro c hc
  unfold Dc.Num.decText at hc
  split at hc
  · simp at hc; omega
  · simp only [List.mem_map, Dc.Num.decChar] at hc; obtain ⟨_, _, rfl⟩ := hc; omega

theorem outLong_ne_zero (v size : Nat) (sp : Bool) : ∀ c ∈ Dc.Num.outLong v size sp, c ≠ 0 := by
  intro c hc
  simp only [Dc.Num.outLong, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · split at hc <;> simp at hc; omega
  · rw [List.eq_of_mem_replicate hc]; omega
  · exact decText_ne_zero v c hc

/-- **`bc_out_num` sends no NUL.** -/
theorem outChars_ne_zero (n : Dc.Num) (ob : Nat) : ∀ c ∈ Dc.Num.outChars n ob, c ≠ 0 := by
  intro c hc
  have hd : ∀ (b d : Nat) (s : Bool), ∀ c ∈ (if b ≤ 16 then [Dc.Num.hexChar d] else
      Dc.Num.outLong d ((Dc.Num.decText (b - 1)).length) s), c ≠ 0 := fun b d s c hc => by
    split at hc
    · simp only [List.mem_singleton, Dc.Num.hexChar] at hc; split at hc <;> omega
    · exact outLong_ne_zero _ _ _ c hc
  unfold Dc.Num.outChars at hc
  simp only at hc
  split at hc
  · simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · split at hc <;> simp at hc; omega
    · simp at hc; omega
  split at hc
  · simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · split at hc <;> simp at hc; omega
    · split at hc
      · simp at hc
      · simp only [List.mem_map, Dc.Num.decChar] at hc; obtain ⟨_, _, rfl⟩ := hc; omega
    · split at hc
      · simp at hc
      · simp only [List.mem_cons, List.mem_map, Dc.Num.decChar] at hc
        rcases hc with rfl | ⟨_, _, rfl⟩ <;> omega
  · simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · split at hc <;> simp at hc; omega
    · simp only [List.mem_flatMap] at hc; obtain ⟨d, _, hc⟩ := hc; exact hd _ _ _ c hc
    · split at hc
      · simp at hc
      · simp only [List.mem_cons, List.mem_flatMap] at hc
        rcases hc with rfl | ⟨d, _, hc⟩
        · omega
        · exact hd _ _ _ c hc

theorem ocRun_out (n : Dc.Num) (ob : Nat) :
    (ocRun (Dc.Num.outChars n ob)).1 = Dc.Num.out 70 ob n :=
  ocRun_wrap (outChars_ne_zero n ob)

/-! ## The state through `out_char` -/

/-- **The state after `bc_out_num` with dc's `out_char`**: the number heap
as the callee left it, off the heap only `out_char`'s bytes `ocG` and the
window `W` (below the globals and off the heap) changed, `line_max` and
`stdout`'s descriptor as the invariant says. -/
theorem DcAt.ocRet {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F F' : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {W : Nat → Prop} {t0 : String}
    {cs : List Nat} {t : String}
    (h : DcAt S M H F L C G hs st) (hb : BcHeap S (G.raws M) M' H' F' L)
    (hfr : ∀ a, OutHeap a → ¬ ocG a → ¬ W a → imgM M' a = imgM M a)
    (hW : ∀ a, W a → ¬ DcGlob a) (hI : OcInv S t0 cs t M') :
    DcAt S M' H' F' L C G hs st := by
  have hag : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a := fun a ⟨c, hc, ha⟩ =>
    hb.raw.img c hc a ha
  refine ⟨hb.subRaw (fun c hc => hc) (fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm), h.nodup,
    h.view.frameW hag (fun a hg hw => hfr a ?_ ?_ fun hw' => hW a hw' hg) hI.lm hI.fd, h.den, h.glob,
    h.col⟩
  · simp only [DcGlob, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, dc_addrs] at hg ⊢
    omega
  · simp only [DcGlob, OcWords, ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr, dc_addrs] at hg hw ⊢
    omega

/-! ## `dc_out_num` -/

/-- `bc_out_num`'s window below `dc_out_num`'s 32-byte frame. -/
abbrev onW : Nat := 176 + 512 + rmStack (2 ^ 30) + 48

/-- `dc_out_num`'s stack: its frame and `bc_out_num`'s window. -/
abbrev onN : Nat := 32 + onW

/-- `dc_out_num` at its call of `bc_out_num` (`0x80006f3c`, `sp` lowered by
32, the handle at `sp - 32 + 8`, `out_col = 0`): the console extended by
`Num.out 70 ob`, back at `ra` with the handle kept (`keep`) or released. -/
theorem out_num_call {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M1 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {x : NumObj}
    {ob sp : Nat} {keep : Bool} {s0v ra : BitVec 64}
    (h1 : DcAt S M1 H F L C G (.num x.rep.p :: hs) st) (hx : x ∈ L) (hhs : hs.length + 1 ≤ 2 ^ 20)
    (hsz : x.rep.len + x.rep.scale < 2 ^ 20) (hmb : MulBase S M1) (hob2 : 2 ≤ ob) (hob : ob < 2 ^ 31)
    (herr : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a)
    (hsf : StackFrame S sp onN) (hab : heapEnd + onN ≤ sp)
    (hc0 : ldv .lw M1 outColAddr = 0#64) (m8 : ldv .ld M1 (sp - 32 + 8) = BitVec.ofNat 64 x.rep.p)
    (m16 : ldv .ld M1 (sp - 32 + 16) = s0v) (m24 : ldv .ld M1 (sp - 32 + 24) = ra)
    (hal : ra.toNat % 4 = 0)
    (R0 : Nat → BitVec 64) (e2 : R0 2 = BitVec.ofNat 64 (sp - 32))
    (e10 : R0 10 = BitVec.ofNat 64 x.rep.p) (e11 : R0 11 = BitVec.ofNat 64 ob)
    (e12 : R0 12 = 0x800020d8#64) (e13 : R0 13 = 0#64) (e1 : R0 1 = 0x80002a78#64)
    (e8 : R0 8 = boolWord keep)
    (hk : ∀ R' M' H' F' L' C', Keeps (2 :: 8 :: cClob) R' R0 → R' 2 = BitVec.ofNat 64 sp → R' 8 = s0v →
      DcAt S M' H' F' L' C' G (if keep then .num x.rep.p :: hs else hs) st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp onN a → imgM M' a = imgM M1 a) →
      DWO live S Q (t ++ Dc.outStr (Dc.Num.out 70 ob x.rep.num)) ra R' M')
    (hoom : ∀ t' R' M' sp', OomAt S sp onN M1 ocG sp' R' M' → DWO live S Q t' 0x80001e74#64 R' M') :
    DWO live S Q t 0x80006f3c#64 R0 M1 := by
  have hNW : onN = 32 + (176 + 512 + rmStack (2 ^ 30) + 48) := rfl
  rw [hNW] at hsf hab
  have hWN : onW = 176 + 512 + rmStack (2 ^ 30) + 48 := rfl
  have hNN : onN = 32 + onW := rfl
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  have hab2 : heapEnd ≤ sp - 32 := by simp only [heapEnd]; omega
  have hI : OcInv S t [] t M1 :=
    ⟨fun a ha => by
      simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr] at ha
      rcases ha with ha | ha | ha | ha
      · exact h1.glob a (by simp only [DcGlob, dc_addrs]; omega)
      · exact h1.glob a (by simp only [DcGlob, dc_addrs]; omega)
      · exact herr a (by simp only [errnoAddr]; omega) (by simp only [errnoAddr]; omega)
      · exact h1.col a (by simp only [outColAddr]; omega) (by simp only [outColAddr]; omega),
     h1.view.outFd, h1.view.lineMax, hc0, by simp [ocRun, Dc.outStr]⟩
  have hrl := h1.refs_le (x := x)
  refine bc_out_num_spec hlive (X := G.raws M1) (I := OcInv S t) (G := ocG) (W := onW) (d := 48)
    (cs := []) (cb := by rw [e12]; exact out_char_fn hlive t)
    ⟨⟨hsf.within (m := 32) (n := onW) (by omega) (by decide), by simp only [heapEnd]; omega,
      hmb.own, fun a ha => h1.glob a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega)⟩,
      Nat.le_refl _, by decide, e2, by rw [e1]; decide, by rw [e12]; decide, e13⟩
    ⟨hx, h1.den.norm x hx, h1.den.pos x hx, hsz,
      fun y hy => by have := h1.refs_le hy; simp only [List.length_cons] at this; omega,
      h1.den.live, h1.den.owns, h1.den.mz, h1.kzero (by simp only [List.length_cons]; omega),
      h1.den.mo, h1.view.ow, h1.den.ov, h1.den.norm _ h1.den.mo, h1.den.pos _ h1.den.mo, hmb.word,
      hob2, hob⟩
    ⟨fun R' M' t' H' F' hk' hI' hb' hfr' => ?_, fun t' R' M' sp' hlo hhi hr2 hfr' => ?_⟩
    h1.heap hI e10 e11
  · -- back from `bc_out_num`
    have hW : ∀ a, frameIn (sp - 32) onW a → ¬ DcGlob a := fun a ha =>
      (above_sp (sp := sp - 32 - onW) (by simp only [heapEnd]; omega)
        (by simp only [frameIn] at ha; omega)).2.1
    have h' := h1.ocRet hb' hfr' hW hI'
    have ht' : t' = t ++ Dc.outStr (Dc.Num.out 70 ob x.rep.num) := by
      rw [hI'.out, List.nil_append, ocRun_out]
    rw [e1, ht']
    have kf : ∀ o, 8 ≤ o → o < 32 → imgM M' (sp - 32 + o) = imgM M1 (sp - 32 + o) := fun o h8 h32 =>
      hfr' _ (above_sp hab2 (by omega)).1
        (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr]; omega)
        (by simp only [frameIn]; omega)
    have g16 : ldv .ld M' (sp - 32 + 16) = s0v := (ldv_congr .ld fun j hj => by
      have := kf (16 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m16
    have g24 : ldv .ld M' (sp - 32 + 24) = ra := (ldv_congr .ld fun j hj => by
      have := kf (24 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m24
    have g8 : ldv .ld M' (sp - 32 + 8) = BitVec.ofNat 64 x.rep.p := (ldv_congr .ld fun j hj => by
      have := kf (8 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m8
    have q2 : R' 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk'.get 2 (by decide)]; exact e2
    have q8 : R' 8 = boolWord keep := by rw [hk'.get 8 (by decide)]; exact e8
    have hS' : HeapOwn S := fun a e1 e2 => hb'.heap.own a e1 e2
    have hfr : ∀ a, OutHeap a → ¬ ocG a → ¬ frameIn sp onN a → imgM M' a = imgM M1 a := fun a ho hg hf =>
      hfr' a ho hg fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
    cases keep
    · have q8' : R' 8 = 0#64 := by rw [q8]; rfl
      bc_run hlive hS' [q2, q8'] at 0x800048c0
      bc_run hlive hS' [q2, q8'] at 0x800048c0
      refine bc_free_num_dc hlive h' (hsf.slot (by omega) (by omega) (by omega))
        (by simp only [heapEnd]; omega) g8 (hsf.within (m := 32) (n := 32) (by omega) (by decide))
        (by simp only [heapEnd]; omega) (.inr (by omega)) _ (by bsimp []) (by bsimp [q2]) (by bsimp [])
        fun R6 M6 H6 F6 L6 C6 hk6 hd6 hz6 hout6 => ?_
      have k6 : ∀ o, 16 ≤ o → o < 32 → imgM M6 (sp - 32 + o) = imgM M' (sp - 32 + o) := fun o h8 h32 =>
        hout6 _ (above_sp hab2 (by omega)).1 (above_sp hab2 (by omega)).2.1
          ((above_sp hab2 (by omega)).2.2 _) (fun hs' => by simp only [slotBytes] at hs'; omega)
      have f16 : ldv .ld M6 (sp - 32 + 16) = s0v := (ldv_congr .ld fun j hj => by
        have := k6 (16 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega)
        simpa [Nat.add_assoc] using this).trans g16
      have f24 : ldv .ld M6 (sp - 32 + 24) = ra := (ldv_congr .ld fun j hj => by
        have := k6 (24 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega)
        simpa [Nat.add_assoc] using this).trans g24
      have q6 : R6 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk6.get 2 (by decide)]; bsimp [q2]
      have hS6 : HeapOwn S := fun a e1 e2 => hd6.heap.heap.own a e1 e2
      bsimp []
      bc_run hlive hS6 [q6, f16, f24]
      all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
      have hWN : onW = 176 + 512 + rmStack (2 ^ 30) + 48 := rfl
      have hNN : onN = 32 + onW := rfl
      refine hk _ M6 H6 F6 L6 C6 ?_ ?_ ?_ hd6 fun a ho hg hc hf => ?_
      · exact by keeps_tac ((hk6.mono (ks' := 2 :: 8 :: cClob) (by decide)).trans
          (by keeps_tac (hk'.mono (ks' := 2 :: 8 :: cClob) (by decide))))
      · bsimp []; congr 1; omega
      · bsimp []
      · rw [hout6 a ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
          (fun hs' => hf (by simp only [slotBytes, frameIn] at hs' ⊢; omega))]
        exact hfr a ho hc hf
    · have q8' : R' 8 = 1#64 := by rw [q8]; rfl
      bc_run hlive hS' [q2, q8', g16, g24]
      bc_run hlive hS' [q2, q8', g16, g24]
      all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
      refine hk _ M' H' F' L C ?_ ?_ ?_ h' fun a ho _ hc hf => hfr a ho hc hf
      · exact by keeps_tac (hk'.mono (ks' := 2 :: 8 :: cClob) (by decide))
      · bsimp []; congr 1; omega
      · bsimp []
  · -- out of memory
    bc_run hlive hS [] at 0x80001e74
    have hWN : onW = 176 + 512 + rmStack (2 ^ 30) + 48 := rfl
    have hNN : onN = 32 + onW := rfl
    exact hoom t' R' M' sp' ⟨by omega, by omega, hr2, fun a ho _ hf hg =>
      hfr' a ho hg fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)⟩

/-- **`dc_out_num (value, obase, discard)`** at `0x80002a4c` on the handle
`.num x.rep.p` the caller holds: the console extended by `Num.out 70 ob` of
the number, the handle kept (`keep`, `DC_KEEP`) or released (`DC_TOSS`). Off
the heap only `out_char`'s bytes and the stack below `sp` change; out of
memory reaches `dc_memfail`. -/
theorem dc_out_num_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {x : NumObj}
    {ob sp : Nat} {keep : Bool}
    (h : DcAt S M H F L C G (.num x.rep.p :: hs) st) (hx : x ∈ L) (hhs : hs.length + 1 ≤ 2 ^ 20)
    (hsz : x.rep.len + x.rep.scale < 2 ^ 20) (hmb : MulBase S M) (hob2 : 2 ≤ ob) (hob : ob < 2 ^ 31)
    (herr : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a)
    (hsf : StackFrame S sp onN) (hab : heapEnd + onN ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 x.rep.p)
    (h11 : R 11 = BitVec.ofNat 64 ob) (h12 : R 12 = boolWord keep) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps cClob R' R → R' 2 = R 2 →
      DcAt S M' H' F' L' C' G (if keep then .num x.rep.p :: hs else hs) st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp onN a → imgM M' a = imgM M a) →
      DWO live S Q (t ++ Dc.outStr (Dc.Num.out 70 ob x.rep.num)) (R 1) R' M')
    (hoom : ∀ t' R' M' sp', OomAt S sp onN M ocG sp' R' M' → DWO live S Q t' 0x80001e74#64 R' M') :
    DWO live S Q t 0x80002a4c#64 R M := by
  have hNW : onN = 32 + (176 + 512 + rmStack (2 ^ 30) + 48) := rfl
  have hsf' := hsf
  have hab0 := hab
  rw [hNW] at hsf' hab0
  have hsl := hsf'.lo; have hsh := hsf'.hi; have hsa := hsf'.al
  simp only [heapEnd] at hab0
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  bc_run hlive hS [h2, h10, h11, h12, word_sub32 (show 32 ≤ sp by omega)] at 0x80002a70
  all_goals first | exact frame_acc hsf' (by omega) (by omega) | skip
  have oCol : ∀ b ∈ accAddrs 2147601808 4, S b :=
    accOwn fun i hi => h.col _ (by simp only [outColAddr]; omega) (by simp only [outColAddr]; omega)
  bc_run hlive hS [] at 0x80006f3c
  have hNW : onN = 32 + (176 + 512 + rmStack (2 ^ 30) + 48) := rfl
  have hab2 : heapEnd ≤ sp - 32 := by simp only [heapEnd]; omega
  have hM1 : MemOnly (fun a => (sp - 32 ≤ a ∧ a < sp) ∨ (outColAddr ≤ a ∧ a < outColAddr + 4))
      (writeLog (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)])
        [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) [(2147601808, 4, 0#64)]) M := fun a ha => by
    simp only [outColAddr] at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hM1 fun a ha => by
    rcases ha with ha | ha
    · exact ⟨(above_sp hab2 ha.1).1, (above_sp hab2 ha.1).2.1⟩
    · refine ⟨?_, ?_⟩
      · simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, outColAddr] at ha ⊢; omega
      · simp only [DcGlob, dc_addrs] at ha ⊢; omega
  have hmb1 := hmb.transport (M' := writeLog (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
      [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)]) [(2147601808, 4, 0#64)])
    fun a e1 e2 => hM1 a fun hp => by
      simp only [mulBaseAddr, outColAddr] at e1 e2 hp; simp only [heapEnd] at hab2; omega
  have hfr1 : ∀ a, ¬ ocG a → ¬ frameIn sp onN a → imgM (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 x.rep.p)])
      [(2147601808, 4, 0#64)]) a = imgM M a := fun a hg hf => hM1 a fun hp => by
    simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr, frameIn, hNW] at hg hf hp; omega
  refine out_num_call hlive (s0v := R 8) (ra := R 1) (keep := keep) h1 hx hhs hsz hmb1 hob2 hob herr hsf hab
    ?_ ?_ ?_ ?_ hal _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun R' M' H' F' L' C' hk' e2 e8 hd hfr => hk R' M' H' F' L' C' ?_ (by rw [e2, h2]) hd
      fun a ho hg hc hf => (hfr a ho hg hc hf).trans (hfr1 a hc hf))
    fun t' R' M' sp' ho => hoom t' R' M' sp' ⟨ho.lo, ho.hi, ho.r2, fun a e1 e2 e3 e4 =>
      (ho.out a e1 e2 e3 e4).trans (hfr1 a e4 e3)⟩
  · exact ldv_lw_hitN _ rfl (by simp) (by simp)
  · rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_store_hit]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  · bsimp []
  · bsimp [h10]
  · bsimp [h11]
  · bsimp []
  · bsimp []
  · bsimp []
  · bsimp []
  · refine Keeps.restoreAll (rs := [2, 8]) ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
      fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · rw [e2, h2]
    · exact e8

end Dc.Mach
