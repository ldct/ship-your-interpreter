import Dc.Mach.DcOutNum

/-!
# `dc_out_str` (M9)

    dc_out_str (string, discard):
      fwrite (string->s_ptr, string->s_len, 1, stdout);
      if (discard == DC_TOSS) dc_free_str (&string);   -- inlined

- `outBytes_str`: `fwrite`'s console text of a string's bytes is the
  model's `outStr`.
- `dc_out_str_spec`: the console extended by the string, the handle kept or
  released (one reference fewer, or both blocks freed).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **A string's bytes as console text.** -/
theorem outBytes_take {f : Nat → BitVec 8} {p : Nat} {s : List Nat}
    (hb : ∀ i, i < s.length → f (p + i) = BitVec.ofNat 8 (s.getD i 0)) (hc : ∀ c ∈ s, c < 256) :
    ∀ k, k ≤ s.length → outBytes f p k = Dc.outStr (s.take k)
  | 0, _ => by simp [outBytes, Dc.outStr]
  | k + 1, hk => by
    have hk' : k < s.length := by omega
    have hsk : s.getD k 0 = s[k] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    have hlt : s[k] < 256 := hc _ (List.getElem_mem hk')
    rw [outBytes_succ, outBytes_take hb hc k (by omega), hb k hk', List.take_succ,
      List.getElem?_eq_getElem hk', Option.toList_some, outStr_snoc, hsk]
    simp only [putcStr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem outBytes_str {f : Nat → BitVec 8} {p : Nat} {s : List Nat}
    (hb : ∀ i, i < s.length → f (p + i) = BitVec.ofNat 8 (s.getD i 0)) (hc : ∀ c ∈ s, c < 256) :
    outBytes f p s.length = Dc.outStr s := by
  rw [outBytes_take hb hc _ (Nat.le_refl _), List.take_length]

/-- `stdout`'s `FILE` pointer, the word at `0x80008208` of `.rodata`. -/
theorem stdout_word : ldvf .ld dcROImg 2147516936 = BitVec.ofNat 64 stdoutFile := by decide +kernel

/-- `dc_out_str`'s epilogue (`0x80003a14`): `ra`, `s0`, `s1` reloaded from
the 32-byte frame, `sp` restored, back at `ra`. -/
theorem os_epi {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} {s0v s1v ra : BitVec 64}
    (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 32)) (f16 : ldv .ld M (sp - 32 + 16) = s0v)
    (f8 : ldv .ld M (sp - 32 + 8) = s1v) (f24 : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 8, 9] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp → R' 8 = s0v →
      R' 9 = s1v → DWO live S Q t ra R' M) :
    DWO live S Q t 0x80003a14#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, f16, f8, f24]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) ?_ (by bsimp []) (by bsimp [])
  bsimp []; congr 1; omega

/-- `dc_out_str`'s release (`0x80003a38`, the last reference dropped):
`free (s_ptr)`, the frame popped, then the tail call `free (string)`; both
blocks fresh to the state, `s0` the header `b1`. -/
theorem os_rel {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b1 b2 : Blk}
    (h : DcAt S M H F L C G hs st) (hf1 : DcFresh H F L G b1) (hf2 : DcFresh H F L G b2)
    (hne : b1 ≠ b2) (hsz1 : 8 ≤ b1.sz) (hptr : ldv .ld M b1.pay = BitVec.ofNat 64 b2.pay) {sp : Nat}
    {s0v s1v ra : BitVec 64} (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (R : Nat → BitVec 64) (h8 : R 8 = BitVec.ofNat 64 b1.pay) (h2 : R 2 = BitVec.ofNat 64 (sp - 32))
    (f16 : ldv .ld M (sp - 32 + 16) = s0v) (f8 : ldv .ld M (sp - 32 + 8) = s1v)
    (f24 : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H', Keeps [1, 2, 8, 9, 10, 14, 15] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0v → R' 9 = s1v → DcAt S M' H' F L C G hs st →
      (∀ a, OutHeap a → imgM M' a = imgM M a) → DWO live S Q t ra R' M') :
    DWO live S Q t 0x80003a38#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have fbb := h.heap.heap.blk (List.mem_append_right _ hf1.live)
  have hblo : 2147603920 ≤ b1.h := fbb.lo
  have hbhi : b1.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : b1.h % 16 = 0 := fbb.al
  have hpl : 2147603936 ≤ b1.pay ∧ b1.pay + 8 ≤ 2273312768 ∧ b1.pay % 16 = 0 := by
    simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  bc_run hlive hS [h8, hptr] at 0x80000a0c
  obtain ⟨lpre, lpost, hl2⟩ := List.append_of_mem hf2.live
  refine free_spec hlive h.heap.heap hl2 _ ?h10 ?hal fun R1 M2 hk1 hp => ?_
  case h10 => bsimp []
  case hal => bsimp []
  have h2' := h.free hf2 hl2 hp
  have hf1' := hf1.afterFree hl2 hne H.braw (b2 :: H.free)
  have hfm : ∀ o, o + 8 ≤ 32 → ldv .ld M2 (sp - 32 + o) = ldv .ld M (sp - 32 + o) := fun o ho =>
    ldv_congr .ld fun j hj => hp.frame _ (OutHeap.not_alloc h.heap.heap (outHeap_of_ge (by
      simp only [heapEnd, widthOfM] at hj ⊢; omega)))
  have g16 : ldv .ld M2 (sp - 32 + 16) = s0v := (hfm 16 (by omega)).trans f16
  have g8 : ldv .ld M2 (sp - 32 + 8) = s1v := (hfm 8 (by omega)).trans f8
  have g24 : ldv .ld M2 (sp - 32 + 24) = ra := (hfm 24 (by omega)).trans f24
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  have q8 : R1 8 = BitVec.ofNat 64 b1.pay := by rw [hk1.get 8]; bsimp [h8]
  bsimp []
  bc_run hlive hS [q2, q8, g16, g8, g24] at 0x80000a0c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  obtain ⟨lpre2, lpost2, hl3⟩ := List.append_of_mem hf1'.live
  refine free_spec hlive h2'.heap.heap hl3 _ ?h10 ?hal fun R2 M3 hk2 hp2 => ?_
  case h10 => bsimp []
  case hal => bsimp []; exact hal
  have h3 := h2'.free hf1' hl3 hp2
  refine hk R2 M3 _ ?_ ?_ ?_ ?_ ?_ h3 fun a ho => ?_
  · exact (hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  · rw [hk2.get 1]; bsimp []
  · rw [hk2.get 2]; bsimp []; congr 1; omega
  · rw [hk2.get 8]; bsimp []
  · rw [hk2.get 9]; bsimp []
  · rw [hp2.frame a (OutHeap.not_alloc h2'.heap.heap ho), hp.frame a (OutHeap.not_alloc h.heap.heap ho)]

/-- `dc_out_str`'s inlined `dc_free_str` (`0x80003a28`, `s0` the header):
one reference fewer, or both blocks freed. -/
theorem os_toss {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {o : StrObj}
    (h : DcAt S M H F L C G (.str o.hb.pay :: hs) st) (ho : o ∈ G.strs) {sp : Nat}
    {s0v s1v ra : BitVec 64} (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (R : Nat → BitVec 64) (h8 : R 8 = BitVec.ofNat 64 o.hb.pay) (h2 : R 2 = BitVec.ofNat 64 (sp - 32))
    (f16 : ldv .ld M (sp - 32 + 16) = s0v) (f8 : ldv .ld M (sp - 32 + 8) = s1v)
    (f24 : ldv .ld M (sp - 32 + 24) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' G', Keeps [1, 2, 8, 9, 10, 14, 15] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0v → R' 9 = s1v → SameNodes G G' → DcAt S M' H' F L C G' hs st →
      (∀ a, OutHeap a → imgM M' a = imgM M a) → StrPin G.strs G'.strs hs → DWO live S Q t ra R' M') :
    DWO live S Q t 0x80003a28#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  obtain ⟨A, B, he⟩ := List.append_of_mem ho
  have hso := h.view.strs o ho
  have hsz := hso.hsz
  have fbb := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live _ (G.str_mem ho).1))
  have hblo : 2147603920 ≤ o.hb.h := fbb.lo
  have hbhi : o.hb.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : o.hb.h % 16 = 0 := fbb.al
  have hpl : 2147603936 ≤ o.hb.pay ∧ o.hb.pay + 24 ≤ 2273312768 ∧ o.hb.pay % 16 = 0 := by
    simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  have hrf := hso.refs
  have hrl := hso.refsLt
  have wp : BitVec.ofNat 64 o.refs + 18446744073709551615#64 = BitVec.ofNat 64 (o.refs - 1) :=
    word_pred (by have := hso.refsPos; omega)
  have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (o.refs - 1))) =
      BitVec.ofNat 64 (o.refs - 1) := sxw_ofNat (by omega)
  have hv1 : (BitVec.ofNat 64 (o.refs - 1)).toNat % 2 ^ 32 = o.refs - 1 := toNat_ofNat_mod32 (by omega)
  have hm : MemOnly o.hb.In (writeLog M [(o.hb.pay + 16, 4, BitVec.ofNat 64 (o.refs - 1))]) M :=
    fun a ha => MemOnly.store M _ 4 _ a fun hh => ha (by simp only [Blk.In, Blk.pay, Blk.fin] at hh ⊢; omega)
  have hout : ∀ a, OutHeap a → imgM (writeLog M [(o.hb.pay + 16, 4, BitVec.ofNat 64 (o.refs - 1))]) a =
      imgM M a := fun a ho' => hm a fun hin => ho'.1 (live_in_heap h.heap.heap
        (h.heap.raw.live _ (G.str_mem ho).1) hin)
  rcases (show o.refs = 1 ∨ 2 ≤ o.refs by have := hso.refsPos; omega) with h1 | h2r
  · -- the last reference: both blocks freed
    have hz : BitVec.ofNat 64 (o.refs - 1) = 0#64 := by rw [h1]
    rw [hz] at hm hout wq
    bc_run hlive hS [h8, hrf, wp, wq, hz] at 0x80003a38
    have kf : ∀ k, k + 8 ≤ 32 → ldv .ld (writeLog M [(o.hb.pay + 16, 4, 0#64)])
        (sp - 32 + k) = ldv .ld M (sp - 32 + k) := fun k hk => ldv_ld_miss _ _ (by omega)
    obtain ⟨h0, fh, ft⟩ := h.dropStr he h1
    have h1' := h0.rawWrite fh hm
    have hss := h.str_ne_str he
    have hptr : ldv .ld (writeLog M [(o.hb.pay + 16, 4, 0#64)]) o.hb.pay = BitVec.ofNat 64 o.tb.pay := by
      rw [ldv_ld_miss _ _ (by omega)]; exact hso.ptr
    refine os_rel hlive h1' fh ft (Ne.symm hss.1) (by omega) hptr hsf hab _ (by bsimp [h8]) (by bsimp [h2])
      ((kf 16 (by omega)).trans f16) ((kf 8 (by omega)).trans f8) ((kf 24 (by omega)).trans f24) hal
      fun R' M' H' hk1 e1 e2 e8 e9 hD hfr => hk R' M' H' (G.dropStr A B) ?_ e1 e2 e8 e9 ⟨rfl, rfl, rfl⟩ hD
        (fun a ho' => (hfr a ho').trans (hout a ho')) (by rw [he]; exact StrPin.dropStr h.den he h1)
    exact hk1.trans (by keeps_tac Keeps.refl _ _)
  · -- one reference fewer
    have hpos : ¬ (BitVec.ofNat 64 (o.refs - 1)).toInt ≤ (0#64).toInt := by
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [BitVec.toInt_zero]
      split <;> omega
    bc_run hlive hS [h8, hrf, wp, wq] at 0x80003a34
    refine st_80003a34 hlive (fun _ => ?_) fun hc => absurd hc ?_
    rotate_left
    · bsimp []; simpa using hpos
    have kf : ∀ k, k + 8 ≤ 32 → ldv .ld (writeLog M [(o.hb.pay + 16, 4, BitVec.ofNat 64 (o.refs - 1))])
        (sp - 32 + k) = ldv .ld M (sp - 32 + k) := fun k hk => ldv_ld_miss _ _ (by omega)
    refine os_epi hlive hsf hab _ (by bsimp [h2]) ((kf 16 (by omega)).trans f16)
      ((kf 8 (by omega)).trans f8) ((kf 24 (by omega)).trans f24) hal
      fun R' hk1 e1 e2 e8 e9 => hk R' _ H (G.withStr A B (o.withRefs (o.refs - 1))) ?_ e1 e2 e8 e9 ⟨rfl, rfl, rfl⟩ (h.decStr he h2r hv1) hout
        (by rw [he]; exact StrPin.withRefs _ _)
    exact (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)

/-- The registers `dc_out_str` changes. -/
abbrev outStrClob : List Nat := [10, 11, 12, 13, 14, 15]

/-- **`dc_out_str (string, discard)`** at `0x800039e0` on the string
`o` (with `DC_TOSS`, the head of the caller's handles `hs`): the console extended by the string, the
handle kept (`keep`) or released. -/
theorem dc_out_str_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {o : StrObj}
    {sp : Nat} {keep : Bool}
    (h : DcAt S M H F L C G hs st) (hd : keep = false → hs.head? = some (.str o.hb.pay))
    (ho : o ∈ G.strs)
    (hsf : StackFrame S sp 64) (hab : heapEnd + 64 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 o.hb.pay)
    (h11 : R 11 = boolWord keep) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' G', Keeps outStrClob R' R → R' 2 = R 2 → SameNodes G G' →
      DcAt S M' H' F L C G' (if keep then hs else hs.tail) st → StkOut sp 64 M' M →
      StrPin G.strs G'.strs (if keep then hs else hs.tail) →
      DWO live S Q (t ++ Dc.outStr o.s) (R 1) R' M') :
    DWO live S Q t 0x800039e0#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hso := h.view.strs o ho
  have fbb := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live _ (G.str_mem ho).1))
  have hblo : 2147603920 ≤ o.hb.h := fbb.lo
  have hbhi : o.hb.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : o.hb.h % 16 = 0 := fbb.al
  have hsz := hso.hsz
  have hpl : 2147603936 ≤ o.hb.pay ∧ o.hb.pay + 24 ≤ 2273312768 ∧ o.hb.pay % 16 = 0 := by
    simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  have hptr := hso.ptr
  have hlen := hso.len
  bc_run hlive hS [h2, h10, h11, word_sub32 (show 32 ≤ sp by omega)] at 0x800039f0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have g0 : ldv .ld (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 8, 8, R 9)]) o.hb.pay =
      BitVec.ofNat 64 o.tb.pay := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hptr
  have g8 : ldv .ld (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 8, 8, R 9)]) (o.hb.pay + 8) =
      BitVec.ofNat 64 o.s.length := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hlen
  have hro : ∀ b ∈ accAddrs 2147516936 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hS [h10, h11, g0, g8, stdout_word] at 0x80000658
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have g0' : ldv .ld (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 8, 8, R 9)]) o.hb.pay =
      BitVec.ofNat 64 o.tb.pay := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact hso.ptr
  rw [g0']
  have fbt := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live _ (G.str_mem ho).2))
  have htlo : 2147603920 ≤ o.tb.h := fbt.lo
  have hthi : o.tb.fin ≤ 2273312768 := Nat.le_trans fbt.fin fbt.top
  have htsz := hso.tsz
  have hM1 : MemOnly (frameIn sp 32) (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
      [(sp - 32 + 8, 8, R 9)]) [(sp - 32 + 24, 8, R 1)]) M := fun a ha => by
    simp only [frameIn] at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hfd1 : ldv .lw (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
      [(sp - 32 + 8, 8, R 9)]) [(sp - 32 + 24, 8, R 1)]) stdoutFile = BitVec.ofNat 64 1 :=
    (ldv_congr .lw fun j hj => hM1 _ (by simp only [frameIn, stdoutFile, widthOfM] at hj ⊢; omega)).trans
      h.view.outFd
  refine fwrite_spec hlive (sp := sp - 32) (p := o.tb.pay) (len := o.s.length) (f := stdoutFile) (fd := 1)
    ⟨hsf.within (m := 32) (n := 32) (by omega) (by decide),
      ⟨fun i hi => hS _ (by simp only [heapStart, Blk.pay] at *; omega)
        (by simp only [heapEnd, Blk.pay, Blk.fin] at *; omega), by simp only [Blk.pay] at *; omega,
        by simp only [Blk.pay, Blk.fin] at *; omega⟩,
      .inl (by simp only [Blk.pay, Blk.fin] at *; omega),
      ⟨fun i hi => h.glob _ (by simp only [DcGlob, stdoutFile, dc_addrs]; omega), hfd1, by decide, by decide,
        by decide⟩, .inl (by simp only [stdoutFile]; omega)⟩
    _ ?_ ?_ ?_ ?_ ?_ fun R' M' hk' e10 hso' => ?_
  · bsimp []
  · bsimp []
  · have hl64 : o.s.length < 18446744073709551616 := by simp only [Blk.pay, Blk.fin] at *; omega
    bsimp []; simpa using hl64
  · bsimp []; decide
  · bsimp []
  have hbytes : ∀ i, i < o.s.length → imgM (writeLog (writeLog (writeLog M [(sp - 32 + 16, 8, R 8)])
      [(sp - 32 + 8, 8, R 9)]) [(sp - 32 + 24, 8, R 1)]) (o.tb.pay + i) = BitVec.ofNat 8 (o.s.getD i 0) :=
    fun i hi => (hM1 _ (by simp only [frameIn, Blk.pay, Blk.fin] at *; omega)).trans (hso.bytes i hi)
  rw [fdOut_one, outBytes_str hbytes hso.byte]
  bsimp []
  have hm' : MemOnly (frameIn sp 64) M' M := fun a ha =>
    (hso'.rest a (by simp only [frameIn] at ha; omega)).trans (hM1 a fun h' => ha (by
      simp only [frameIn] at h' ⊢; omega))
  have hab2 : heapEnd ≤ sp - 64 := by simp only [heapEnd]; omega
  have hD := h.outWrite hm' fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have kf : ∀ o', o' < 32 → imgM M' (sp - 32 + o') = imgM (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 8, 8, R 9)]) [(sp - 32 + 24, 8, R 1)]) (sp - 32 + o') :=
    fun o' ho' => hso'.rest _ (.inr (by omega))
  have f16 : ldv .ld M' (sp - 32 + 16) = R 8 := by
    rw [ldv_congr .ld fun j hj => by have : widthOfM .ld = 8 := rfl; simpa [Nat.add_assoc] using kf (16 + j) (by omega)]
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have f8 : ldv .ld M' (sp - 32 + 8) = R 9 := by
    rw [ldv_congr .ld fun j hj => by have : widthOfM .ld = 8 := rfl; simpa [Nat.add_assoc] using kf (8 + j) (by omega)]
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have f24 : ldv .ld M' (sp - 32 + 24) = R 1 := by
    rw [ldv_congr .ld fun j hj => by have : widthOfM .ld = 8 := rfl; simpa [Nat.add_assoc] using kf (24 + j) (by omega)]
    rw [ldv_store_hit]
  have q2 : R' 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk'.get 2 (by decide)]; bsimp []
  have q8 : R' 8 = BitVec.ofNat 64 o.hb.pay := by rw [hk'.get 8 (by decide)]; bsimp []
  have q9 : R' 9 = boolWord keep := by rw [hk'.get 9 (by decide)]; bsimp []
  have hS' : HeapOwn S := fun a e1 e2 => hD.heap.heap.own a e1 e2
  cases keep
  · obtain ⟨hs0, rfl⟩ : ∃ hs0, hs = .str o.hb.pay :: hs0 := by
      rcases hs with _ | ⟨g0, hs0⟩
      · exact absurd (hd rfl) (by simp)
      · exact ⟨hs0, by rw [Option.some.inj (hd rfl)]⟩
    have q9' : R' 9 = 0#64 := q9
    bc_run hlive hS' [q2, q9']
    refine os_toss hlive hD ho (sp := sp) (by simpa using hsf.within (m := 0) (n := 32) (by omega) (by decide))
      (by simp only [heapEnd]; omega) R' q8 q2 f16 f8 f24 hal
      fun R'' M'' H'' G'' hk'' e1 e2 e8 e9 hsn hD' hfr hpin =>
        hk R'' M'' H'' G'' ?_ (by rw [e2, h2]) hsn hD' (fun a ho' hg hf => (hfr a ho').trans (hm' a hf)) hpin
    refine Keeps.restoreAll (rs := [1, 2, 8, 9]) ((hk''.mono (by decide)).trans
      ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact e1
    · rw [e2, h2]
    · exact e8
    · exact e9
  · have q9' : R' 9 = 1#64 := q9
    bc_run hlive hS' [q2, q9']
    refine os_epi hlive (sp := sp) (by simpa using hsf.within (m := 0) (n := 32) (by omega) (by decide))
      (by simp only [heapEnd]; omega) R' q2 f16 f8 f24 hal fun R'' hk'' e1 e2 e8 e9 => ?_
    refine hk R'' M' H G ?_ (by rw [e2, h2]) ⟨rfl, rfl, rfl⟩ hD (fun a ho hg hf => hm' a hf) (StrPin.refl _ _)
    refine Keeps.restoreAll (rs := [1, 2, 8, 9]) ((hk''.mono (by decide)).trans
      ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact e1
    · rw [e2, h2]
    · exact e8
    · exact e9

end Dc.Mach
