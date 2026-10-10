import Dc.Mach.DcReadString

/-!
# `dc_system` (M9)

    dc_system (s):
      p = strchr (s, '\n');
      if (p) { tmpstr = malloc (p - s + 1); if (!tmpstr) dc_memfail ();
               strncpy (tmpstr, s, p - s); tmpstr[p - s] = '\0';
               system (tmpstr); free (tmpstr); return p + 1; }
      system (s); return s + strlen (s);

The bare-metal `system` returns `-1` and reads nothing, so the copy is scratch:
the state is unchanged and the result is the model's `skipSys` position.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

theorem skipSys_length_le : ∀ s : List Nat, (skipSys s).length ≤ s.length
  | [] => Nat.le_refl _
  | c :: cs => by
    simp only [skipSys]
    split
    · simp
    · split
      · exact Nat.le_refl _
      · exact Nat.le_trans (skipSys_length_le cs) (by simp)

theorem findFrom_range {f : Nat → BitVec 8} {c : BitVec 8} :
    ∀ {a m p : Nat}, findFrom f c a m = some p → a ≤ p ∧ p < a + m ∧ f p = c
  | _, 0, _, h => by simp [findFrom] at h
  | a, m + 1, p, h => by
    by_cases e : f a = c
    · rw [findFrom_hit m e] at h; cases h; exact ⟨Nat.le_refl _, by omega, e⟩
    · rw [findFrom_miss m e] at h
      have := findFrom_range h
      exact ⟨by omega, by omega, this.2.2⟩

/-- A string's C length: the bytes before its first NUL (or its end). -/
theorem cstr_len (s : List Nat) (f : Nat → BitVec 8) :
    ∀ a, (∀ i, i < s.length → f (a + i) = BitVec.ofNat 8 (s.getD i 0)) → (∀ c ∈ s, c < 256) →
      f (a + s.length) = 0 → ∃ k, k ≤ s.length ∧ (∀ i, i < k → f (a + i) ≠ 0) ∧ f (a + k) = 0 := by
  induction s with
  | nil => intro a _ _ hn; exact ⟨0, Nat.le_refl _, fun i h => absurd h (Nat.not_lt_zero _), hn⟩
  | cons c cs ih =>
    intro a hv hb hn
    have h0 := hv 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    by_cases hc : c = 0
    · exact ⟨0, Nat.zero_le _, fun i h => absurd h (Nat.not_lt_zero _), by
        rw [Nat.add_zero, h0, hc]; rfl⟩
    · obtain ⟨k, hk, hnz, hz⟩ := ih (a + 1) (fun i hi => by
          have := hv (i + 1) (by simp; omega)
          rw [show a + 1 + i = a + (i + 1) by omega, this]; simp)
        (fun x hx => hb x (List.mem_cons_of_mem _ hx))
        (by rw [show a + 1 + cs.length = a + (c :: cs).length by simp; omega]; exact hn)
      refine ⟨k + 1, by simp; omega, fun i hi => ?_, by rw [← hz]; congr 1; omega⟩
      rcases i with _ | i
      · rw [Nat.add_zero, h0]
        intro e
        have hcb := hb c List.mem_cons_self
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt hcb] at this
        exact hc (by simpa using this)
      · rw [show a + (i + 1) = a + 1 + i by omega]; exact hnz i (by omega)

/-- **`strchr (s, '\n')` against `skipSys`**: a newline at `p` leaves the
input after it, none leaves it at the first NUL (the C length `k`). -/
theorem skipSys_find (s : List Nat) (f : Nat → BitVec 8) :
    ∀ a k, (∀ i, i < s.length → f (a + i) = BitVec.ofNat 8 (s.getD i 0)) → (∀ c ∈ s, c < 256) →
      f (a + s.length) = 0 → (∀ i, i < k → f (a + i) ≠ 0) → f (a + k) = 0 →
      (∀ p, findFrom f 10#8 a (k + 1) = some p →
        a + (s.length - (skipSys s).length) = p + 1) ∧
      (findFrom f 10#8 a (k + 1) = none → s.length - (skipSys s).length = k) := by
  have byte : ∀ c, c < 256 → ∀ d, d < 256 → BitVec.ofNat 8 c = BitVec.ofNat 8 d → c = d :=
    fun c hc d hd e => by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at this
  induction s with
  | nil =>
    intro a k _ _ hn hnz _
    have hk : k = 0 := by
      rcases k with _ | k
      · rfl
      · exact absurd (by simpa using hn) (hnz 0 (by omega))
    subst hk
    refine ⟨fun p h => ?_, fun _ => rfl⟩
    rw [findFrom_miss 0 (by simp at hn; rw [hn]; decide)] at h
    simp [findFrom] at h
  | cons c cs ih =>
    intro a k hv hb hn hnz hz
    have hcb := hb c List.mem_cons_self
    have h0 := hv 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    have hle := skipSys_length_le cs
    by_cases c10 : c = 10
    · subst c10
      have hk : 1 ≤ k := by
        rcases k with _ | k
        · simp at hz; rw [hz] at h0; exact absurd h0 (by decide)
        · omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hf : findFrom f 10#8 a (k' + 1 + 1) = some a := findFrom_hit _ h0
      refine ⟨fun p h => ?_, fun h => (by rw [hf] at h; cases h)⟩
      rw [hf] at h; cases h
      simp only [skipSys, beq_self_eq_true, ite_true, List.length_cons]
      omega
    · by_cases c0 : c = 0
      · subst c0
        have hk : k = 0 := by
          rcases k with _ | k
          · rfl
          · exact absurd h0 (hnz 0 (by omega))
        subst hk
        have hf : findFrom f 10#8 a (0 + 1) = none := by
          rw [findFrom_miss 0 (by rw [h0]; decide)]; rfl
        refine ⟨fun p h => (by rw [hf] at h; cases h), fun _ => ?_⟩
        simp [skipSys]
      · have hk : 1 ≤ k := by
          rcases k with _ | k
          · simp at hz; rw [hz] at h0
            exact absurd (byte c hcb 0 (by decide) h0.symm) c0
          · omega
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hne : f a ≠ 10#8 := fun e => c10 (byte c hcb 10 (by decide) (h0.symm.trans e))
        rw [findFrom_miss _ hne]
        have hih := ih (a + 1) k' (fun i hi => by
            have := hv (i + 1) (by simp; omega)
            rw [show a + 1 + i = a + (i + 1) by omega, this]; simp)
          (fun x hx => hb x (List.mem_cons_of_mem _ hx))
          (by rw [show a + 1 + cs.length = a + (c :: cs).length by simp; omega]; exact hn)
          (fun i hi => by rw [show a + 1 + i = a + (i + 1) by omega]; exact hnz _ (by omega))
          (by rw [show a + 1 + k' = a + (k' + 1) by omega]; exact hz)
        have es : skipSys (c :: cs) = skipSys cs := by
          simp [skipSys, c10, c0]
        rw [es]
        simp only [List.length_cons]
        refine ⟨fun p h => ?_, fun h => ?_⟩
        · have := hih.1 p h; omega
        · have := hih.2 h; omega

/-- The registers `dc_system` saves. -/
abbrev sysSaved : List Nat := [1, 8, 9, 18, 19]

/-- `dc_system`'s frame slots on the newline route, in prologue order. -/
abbrev sysSlots : List (Nat × Nat) := [(19, 8), (8, 32), (18, 16), (1, 40), (9, 24)]

/-- `dc_system` without a newline (`0x80001fe4`): `system (s)`, then
`s + strlen (s)`. -/
theorem sys_eol {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp src k : Nat} {R0 : Nat → BitVec 64}
    (hs : OwnedCStr S M src k) (hsf : StackFrame S sp 48)
    (hsv : SavedWords M (sp - 48) [(1, 40), (9, 24)] R0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h9 : R 9 = BitVec.ofNat 64 src)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps ([2, 9] ++ cClob) R' R → R' 1 = R0 1 → R' 9 = R0 9 →
      R' 2 = BitVec.ofNat 64 sp → R' 10 = BitVec.ofNat 64 (src + k) → DW live S Q (R0 1) R' M) :
    DW live S Q 0x80001fe4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hlo := hs.lo; have hhi := hs.hi
  bc_run hlive hlive [h9] at 0x80000854
  refine system_spec hlive _ (by bsimp []) fun R1 hk1 _ => ?_
  have q9 : R1 9 = BitVec.ofNat 64 src := by rw [hk1.get 9]; bsimp [h9]
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp [h2]
  bsimp []
  bc_run hlive hlive [q9] at 0x80000904
  refine strlen_spec hlive hs _ (by bsimp [q9]) (by bsimp []) fun R2 e10 hk2 => ?_
  have hk2' := hk2.keeps
  have r9 : R2 9 = BitVec.ofNat 64 src := by rw [hk2'.get 9]; bsimp [q9]
  have r2 : R2 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk2'.get 2]; bsimp [q2]
  have e40 := hsv.get 1 40
  have e24 := hsv.get 9 24
  bsimp []
  bc_run hlive hlive [r2, r9, e10, e40, e24]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · bsimp [e40]; exact hal
  refine hk _ (by keeps_tac ((hk2'.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))))) (by bsimp [e40]) (by bsimp [e24])
    (by bsimp []; congr 1; omega) (by bsimp [r9, e10])

/-- `dc_system` after `malloc` returned the block `b` (`0x80001f98`): the
copy, its NUL, `system`, `free`, and `p + 1`. -/
theorem sys_tail {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {sp src j k : Nat} {R0 : Nat → BitVec 64}
    {b : Blk} {lr : List Blk}
    (h : DcAt S M H F L C G hs st) (f : DcFresh H F L G b) (hl : H.live = b :: lr)
    (hsz : j + 1 ≤ b.sz) (hcs : OwnedCStr S M src k)
    (hoff : ∀ i, i ≤ k → ¬ b.In (src + i))
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp) (hsv : SavedWords M (sp - 48) sysSlots R0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h8 : R 8 = BitVec.ofNat 64 (src + j))
    (h9 : R 9 = BitVec.ofNat 64 src) (h18 : R 18 = BitVec.ofNat 64 j)
    (h10 : R 10 = BitVec.ofNat 64 b.pay) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' M' H', Keeps ([2, 8, 9, 18, 19] ++ cClob) R' R → (∀ z ∈ sysSaved, R' z = R0 z) →
      R' 2 = BitVec.ofNat 64 sp → R' 10 = BitVec.ofNat 64 (src + j + 1) →
      DcAt S M' H' F L C G hs st → StkOut sp 48 M' M → DW live S Q (R0 1) R' M') :
    DW live S Q 0x80001f98#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := h.heap.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hbb := blk_bounds hi f.live
  simp only [heapStart, heapEnd] at hbb
  have hbp : b.fin = b.pay + b.sz := rfl
  have hbp2 : b.pay = b.h + 16 := rfl
  have hlo := hcs.lo; have hhi := hcs.hi
  have hne := blk_ptr_ne hi f.live
  bc_run hlive hS [h10] at 0x80000928
  all_goals first | (intro hc; exact absurd hc hne) | skip
  intro _
  bc_run hlive hS [h9, h18, h10] at 0x80000928
  have hc : StrncpyArgs S M b.pay src j k :=
    { dst := ⟨fun i hi' => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega),
        by simp only [tohostAddr]; omega, by omega⟩
      src := hcs
      disj := by
        by_cases e : src ≤ b.pay ∧ b.pay ≤ src + k
        · exact (hoff (b.pay - src) (by omega) ⟨by simp only [Blk.pay] at *; omega,
            by simp only [Blk.pay, Blk.fin] at *; omega⟩).elim
        · have h0 := hoff 0 (by omega)
          simp only [Blk.In, Blk.pay, Blk.fin, Nat.add_zero] at h0 e hbb hsz ⊢
          omega }
  refine strncpy_spec hlive hc _ (by bsimp [h10]) (by bsimp [h9]) (by bsimp [h18]) (by bsimp [])
    fun R1 M1 hk1 hf1 => ?_
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp [h2]
  have q8 : R1 8 = BitVec.ofNat 64 (src + j) := by rw [hk1.get 8]; bsimp [h8]
  have q18 : R1 18 = BitVec.ofNat 64 j := by rw [hk1.get 18]; bsimp [h18]
  have q19 : R1 19 = BitVec.ofNat 64 b.pay := by rw [hk1.get 19]; bsimp [h10]
  have hm1 : MemOnly b.In M1 M := fun a ha => hf1.rest a (by
    simp only [Blk.In, Blk.pay, Blk.fin] at ha hsz ⊢; omega)
  have h1 := h.rawWrite f hm1
  bsimp []
  bc_run hlive hS [q18, q19, ofNat_add_ofNat] at 0x80000854
  have hm2 : MemOnly b.In (writeLog M1 [(b.pay + j, 1, 0#64)]) M1 := fun a ha =>
    imgM_store_miss _ _ (by simp only [Blk.In, Blk.pay, Blk.fin] at ha hsz ⊢; omega)
  have h2' := h1.rawWrite f hm2
  refine system_spec hlive _ (by bsimp []) fun R2 hk2 _ => ?_
  bsimp []
  bc_run hlive hS [q19] at 0x80000a0c
  refine free_spec hlive h2'.heap.heap (lpre := []) (by rw [hl]; rfl) _ (by bsimp [hk2.get 19, q19])
    (by bsimp []) fun R3 M3 hk3 hp => ?_
  have h3 := h2'.free f (lpre := []) (by rw [hl]; rfl) hp
  have hag : ∀ a, sp - 48 ≤ a → imgM M3 a = imgM M a := fun a ha => by
    rw [hp.frame a fun hx => by
      rcases AllocByte.glob_or_heap h2'.heap.heap hx with e | e <;>
        simp only [freeListAddr, heapStart, heapEnd] at e <;> omega,
      imgM_store_miss _ _ (by omega), hf1.rest a (by omega)]
  have hsv3 := hsv.transport (M' := M3) (lo := 8) (top := 48) (hag := fun a e1 _ => hag a (by omega))
  have e1 := hsv3.get 1 40
  have e8 := hsv3.get 8 32
  have e18 := hsv3.get 18 16
  have e19 := hsv3.get 19 8
  have e9 := hsv3.get 9 24
  have r8 : R3 8 = BitVec.ofNat 64 (src + j) := by rw [hk3.get 8]; bsimp []; rw [hk2.get 8]; bsimp [q8]
  have r2 : R3 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk3.get 2]; bsimp []; rw [hk2.get 2]; bsimp [q2]
  bsimp []
  bc_run hlive hS [r2, r8, e1, e8, e18, e19, e9, ofNat_add_ofNat]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · bsimp [e1]; exact hal
  refine hk _ M3 _ (by keeps_tac ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
      (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))))) ?_
    (by bsimp []; congr 1; omega) (by bsimp [r8]) h3 fun a ho _ hf => ?_
  · simp only [sysSaved, List.mem_cons, List.not_mem_nil, or_false]
    rintro z (rfl | rfl | rfl | rfl | rfl)
    all_goals bsimp [e1, e8, e9, e18, e19]
  · have := ho
    simp only [OutHeap] at this
    rw [hp.frame a (OutHeap.not_alloc h2'.heap.heap ho), hm2 a fun hb => by
        have := live_in_heap hi f.live hb; simp only [OutHeap] at ho; omega,
      hm1 a fun hb => by have := live_in_heap hi f.live hb; simp only [OutHeap] at ho; omega]

/-- A C string whose bytes are unchanged. -/
theorem OwnedCStr.congr {S : Nat → Prop} {M M' : Mem} {a len : Nat} (h : OwnedCStr S M a len)
    (hag : ∀ i, i ≤ len → imgM M' (a + i) = imgM M (a + i)) : OwnedCStr S M' a len :=
  ⟨h.own, fun i hi => by rw [hag i (by omega)]; exact h.nz i hi, by rw [hag len (Nat.le_refl _)]; exact h.nul,
    h.lo, h.hi⟩

/-- `dc_system`'s argument: the input `s` at `src`, NUL-terminated, in the
state's blocks or outside the heap and the frame. -/
structure SysSrc (S : Nat → Prop) (M : Mem) (G : DcG) (sp src : Nat) (s : List Nat) : Prop where
  own : OwnedBytes S src (s.length + 1)
  loc : ∀ i, i ≤ s.length → InBlocks G.blocks (src + i) ∨ (OutHeap (src + i) ∧ ¬ frameIn sp 48 (src + i))
  val : ∀ i, i < s.length → imgM M (src + i) = BitVec.ofNat 8 (s.getD i 0)
  nul : imgM M (src + s.length) = 0
  byte : ∀ c ∈ s, c < 256
  len : s.length < 2 ^ 60

/-- **`dc_system (s)`** at `0x80001f60`: `system` (which returns `-1`) runs,
the state is unchanged, and the result is `s` advanced past the command
(`skipSys`); the copy's `malloc` may run out of memory. -/
theorem dc_system_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {sp src : Nat} {s : List Nat}
    (h : DcAt S M H F L C G hs st) (hsrc : SysSrc S M G sp src s)
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 src)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H', Keeps cClob R' R → R' 2 = R 2 →
      R' 10 = BitVec.ofNat 64 (src + (s.length - (skipSys s).length)) →
      DcAt S M' H' F L C G hs st → StkOut sp 48 M' M → DW live S Q (R 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 48) → StkOut sp 48 M' M →
      DW live S Q 0x80001e74#64 R' M') :
    DW live S Q 0x80001f60#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hlen := hsrc.len
  have hlo := hsrc.own.lo; have hhi := hsrc.own.hi
  -- source bytes lie off the frame
  have hnf : ∀ i, i ≤ s.length → ¬ frameIn sp 48 (src + i) := fun i hi => by
    rcases hsrc.loc i hi with hb | ⟨_, hf⟩
    · have := (h.inBlocks_heap hb).1
      simp only [frameIn, heapEnd] at this ⊢; omega
    · exact hf
  obtain ⟨k, hkl, hknz, hkz⟩ := cstr_len s (imgM M) src hsrc.val hsrc.byte hsrc.nul
  have hcs : OwnedCStr S M src k :=
    ⟨fun i hi => hsrc.own.own i (by omega), hknz, hkz, hlo, by omega⟩
  have sv := ((SavedWords.nil M (sp - 48) R).store 9 24).store 1 40
  bc_run hlive hS [h2, h10, word_sub48 (show 48 ≤ sp by omega)] at 0x800008d8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  generalize hM1 : writeLog (writeLog M [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)] = M1 at sv ⊢
  have hMo1 : MemOnly (frameIn sp 48) M1 M := fun a ha => by
    rw [← hM1]; simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hfo : ∀ a, frameIn sp 48 a → OutHeap a ∧ ¬ DcGlob a := fun a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at *; omega⟩
  have h1 := h.outWrite hMo1 hfo
  have hag1 : ∀ i, i ≤ s.length → imgM M1 (src + i) = imgM M (src + i) := fun i hi =>
    hMo1 _ (hnf i hi)
  have hcs1 := hcs.congr fun i hi => hag1 i (by omega)
  refine strchr_spec hlive hcs1 _ (by bsimp [h10]) (by bsimp []) fun R1 hk1 e10 => ?_
  have hf10 : lo8 (upd (upd (upd (upd R 2 (BitVec.ofNat 64 (sp - 48))) 11 10#64) 9
      (BitVec.ofNat 64 src)) 1 2147491704#64 11) = 10#8 := by bsimp []; rfl
  rw [hf10] at e10
  have hsk := skipSys_find s (imgM M1) src k (fun i hi => (hag1 i (by omega)).trans (hsrc.val i hi))
    hsrc.byte ((hag1 _ (Nat.le_refl _)).trans hsrc.nul) (fun i hi => by
      rw [hag1 i (by omega)]; exact hknz i hi) (by rw [hag1 k hkl]; exact hkz)
  have q9 : R1 9 = BitVec.ofNat 64 src := by rw [hk1.get 9]; bsimp [h10]
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp []
  cases hfd : findFrom (imgM M1) 10#8 src (k + 1) with
  | none =>
    rw [hfd] at e10
    bsimp []
    bc_run hlive hS [e10] at 0x80001fe4
    refine sys_eol hlive hcs1 hsf sv R1 q2 q9 hal fun R' hkE e1 e9 e2 e10' => hk R' M1 H
      (Keeps.restoreAll (rs := [2, 9]) ((hkE.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))) fun z hz => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · rw [e2, h2]
          · exact e9)
      (by rw [e2, h2]) (by rw [e10', hsk.2 hfd]) h1 fun a _ _ hf => hMo1 a hf
  | some p =>
    rw [hfd] at e10
    simp only [ptrOr0, Option.getD_some] at e10
    obtain ⟨hp1, hp2, hp3⟩ := findFrom_range hfd
    have hpk : p ≠ src + k := fun e => by
      rw [e, hag1 k hkl, hkz] at hp3; exact absurd hp3 (by decide)
    obtain ⟨j, rfl⟩ : ∃ j, p = src + j := ⟨p - src, by omega⟩
    have hsub : BitVec.ofNat 64 (src + j) - BitVec.ofNat 64 src = BitVec.ofNat 64 j := by
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]; congr 1; omega
    have hne : BitVec.ofNat 64 (src + j) ≠ 0#64 := by
      rw [Ne, ofNat_eq_zero_iff (by omega)]; simp only [tohostAddr] at hlo; omega
    bsimp []
    bc_run hlive hS [e10, q2, q9, hsub, ofNat_add_ofNat] at 0x8000096c
    all_goals first | (intro hc; exact absurd hc hne) | skip
    intro _
    bc_run hlive hS [e10, q2, q9, hsub, ofNat_add_ofNat] at 0x8000096c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    rw [hk1.get 18, hk1.get 8, hk1.get 19]
    bsimp []
    have sv2 := ((sv.store 18 16).store 8 32).store 19 8
    generalize hM2 : writeLog (writeLog (writeLog M1 [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 32, 8, R 8)])
      [(sp - 48 + 8, 8, R 19)] = M2 at sv2 ⊢
    have hMo2 : MemOnly (frameIn sp 48) M2 M := fun a ha => by
      rw [← hM2]; simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
      exact hMo1 a (by simp only [frameIn]; omega)
    have h2' := h.outWrite hMo2 hfo
    have hi2 := h2'.heap.heap
    refine malloc_spec hlive hi2 (n := j + 1) (by omega) _ (by bsimp []) (by bsimp [])
      fun R2 M3 H' hk2 hp => ?_
    have r2 : R2 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk2.get 2]; bsimp [q2]
    have hfr : ∀ a, ¬ AllocByte H a → ¬ frameIn sp 48 a → imgM M3 a = imgM M a := fun a ha hf =>
      (hp.frame a ha).trans (hMo2 a hf)
    have hso : ∀ M', StkOut sp 48 M' M3 → StkOut sp 48 M' M := fun M' hs1 a ho hg hf =>
      (hs1 a ho hg hf).trans (hfr a (OutHeap.not_alloc hi2 ho) hf)
    cases hres : hp.res with
    | null e1 _ _ =>
      bsimp []
      bc_run hlive hS [e1] at 0x80001e74
      bc_run hlive hS [e1] at 0x80001e74
      exact hoom _ M3 (by bsimp [r2]) (hso M3 fun _ _ _ _ => rfl)
    | block b e1 e2 e3 e4 e5 =>
      obtain ⟨h3, f⟩ := h2'.malloc (sp := sp) ⟨hp.inv, e3, e4, e2, e5, fun a ha _ => hp.frame a ha⟩
        (by omega) (by omega)
      have hna : ∀ i, i ≤ s.length → ¬ AllocByte H (src + i) := fun i hi => by
        rcases hsrc.loc i hi with hb | ⟨ho, _⟩
        · exact (h.inBlocks_heap hb).2
        · exact OutHeap.not_alloc h.heap.heap ho
      have hcs3 := hcs.congr fun i hi => hfr _ (hna i (by omega)) (hnf i (by omega))
      have hsv3 : SavedWords M3 (sp - 48) sysSlots R := sv2.transport (lo := 8) (top := 48)
        (hag := fun a e1 _ => hp.frame a fun hx => by
          rcases AllocByte.glob_or_heap hi2 hx with e | e <;>
            simp only [freeListAddr, heapStart, heapEnd] at e <;> omega)
      have hoff : ∀ i, i ≤ k → ¬ b.In (src + i) := fun i hi => ms_src_off h3 f (by
        rcases hsrc.loc i (by omega) with hb | ⟨ho, _⟩
        · exact Or.inl hb
        · exact Or.inr ho)
      bsimp []
      refine sys_tail hlive h3 f e3 e2 hcs3 hoff hsf hab hsv3 R2 r2
        (by rw [hk2.get 8]; bsimp []) (by rw [hk2.get 9]; bsimp [q9]) (by rw [hk2.get 18]; bsimp [])
        e1 hal fun R' M' H'' hkT hsvT e2' e10' hd hs1 => hk R' M' H''
          (Keeps.restoreAll (rs := [2, 8, 9, 18, 19]) ((hkT.mono (by decide)).trans (by keeps_tac
            ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
              (by keeps_tac Keeps.refl _ _)))))) fun z hz => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl | rfl | rfl
            · rw [e2', h2]
            all_goals exact hsvT _ (by decide))
          (by rw [e2', h2]) (by rw [e10', hsk.1 _ hfd]) hd (hso M' hs1)

end Dc.Mach
