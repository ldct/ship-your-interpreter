import Dc.Mach.DcMemfail

/-!
# `dc_readstring` on empty input (M9)

    dc_readstring (fp, ldelim, rdelim):
      if (!line_buf) { buflen = 2016; line_buf = dc_malloc (buflen); }
      p = line_buf; end = line_buf + buflen;
      while ((c = getc (fp)) != EOF) { … }
      return dc_makestring (line_buf, p - line_buf);   -- inlined

The bare-metal `getc` returns `EOF` at once, so the result is the empty
string; the first call allocates `line_buf` (`DcAt.newLbuf`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The words of `buflen` and `line_buf`. -/
abbrev LbWords (a : Nat) : Prop := bufLenAddr ≤ a ∧ a < lineBufAddr + 8

/-- **The view with a new line buffer**: the blocks and the globals other
than `LbWords` read the same, `line_buf` and `buflen` read again. -/
theorem DcView.withLbuf {Mt Mt' : Mem} {G : DcG} {C : BcConsts} {st : St} {lb : Option Blk}
    (h : DcView Mt G C st)
    (hb : ∀ a, InBlocks G.blocks a → imgM Mt' a = imgM Mt a)
    (hg : ∀ a, DcGlob a → ¬ LbWords a → imgM Mt' a = imgM Mt a)
    (hl : ldv .ld Mt' lineBufAddr = BitVec.ofNat 64 (match lb with | some b => b.pay | none => 0))
    (hll : ∀ b, lb = some b → ldv .ld Mt' bufLenAddr = BitVec.ofNat 64 2016) :
    DcView Mt' { G with lbuf := lb } C st := by
  have gw : ∀ (k : MKind) a, (∀ j, j < widthOfM k → DcGlob (a + j) ∧ ¬ LbWords (a + j)) →
      ldv k Mt' a = ldv k Mt a := fun k a ha =>
    ldv_congr k fun j hj => hg _ (ha j hj).1 (ha j hj).2
  exact
    { stk := stkChain_frame h.stk
        (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega)
        fun bg hm x hx => hb x ⟨bg.1, G.stk_mem hm, hx⟩
      regs := fun r hr => regChain_frame (h.regs r hr)
        (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, LbWords, regAddr, dc_addrs] at hj ⊢; omega)
        fun be hm c hc x hx => hb x ⟨c, by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact G.reg_mem hr hm
          · obtain ⟨bn, hn, rfl⟩ := List.mem_map.mp hc
            exact G.arr_mem hr hm hn, hx⟩
      strs := fun o ho => (h.strs o ho).frame (G.str_mem ho).1 (G.str_mem ho).2 hb
      zw := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.zw
      ow := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.ow
      tw := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.tw
      ibase := (gw .lw _ fun j hj => by
        simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.ibase
      obase := (gw .lw _ fun j hj => by
        simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.obase
      scale := (gw .lw _ fun j hj => by
        simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.scale
      unwind := (gw .lw _ fun j hj => by
        simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.unwind
      noexit := (gw .lw _ fun j hj => by
        simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.noexit
      lineMax := by
        rw [gw .lw _ fun j hj => by simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega]
        exact h.lineMax
      lbuf := hl
      lbufLen := hll
      outFd := (gw .lw _ fun j hj => by
        simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.outFd
      errFd := (gw .lw _ fun j hj => by
        simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.errFd
      prog := (gw .ld _ fun j hj => by
        simp only [widthOfM, DcGlob, LbWords, dc_addrs] at hj ⊢; omega).trans h.prog }

/-- **Stores to `buflen`/`line_buf`** keep the state when the words still
name its line buffer. -/
theorem DcAt.lbufWrite {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hm : MemOnly LbWords M' M)
    (hl : ldv .ld M' lineBufAddr = BitVec.ofNat 64 (match G.lbuf with | some b => b.pay | none => 0))
    (hll : ∀ b, G.lbuf = some b → ldv .ld M' bufLenAddr = BitVec.ofNat 64 2016) :
    DcAt S M' H F L C G hs st := by
  have hP : ∀ a, LbWords a → OutHeap a := fun a ha => by
    simp only [LbWords, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, dc_addrs] at ha ⊢; omega
  have hblk : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a := fun a ha =>
    hm a fun hp => (hP a hp).1 (h.inBlocks_heap ha).1
  exact { h with
    heap := (h.heap.out_frame hm hP).subRaw (fun c hc => hc) fun c hc a ha => (hblk a ⟨c, hc, ha⟩).symm
    view := h.view.withLbuf (lb := G.lbuf) hblk (fun a _ hw => hm a hw) hl hll }

/-- **`line_buf` allocated**: a block fresh to the state becomes the line
buffer, `buflen` and `line_buf` stored. -/
theorem DcAt.newLbuf {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk}
    (h : DcAt S M H F L C G hs st) (hn : G.lbuf = none) (f : DcFresh H F L G b) (hsz : 2016 ≤ b.sz)
    (hm : MemOnly LbWords M' M) (hl : ldv .ld M' lineBufAddr = BitVec.ofNat 64 b.pay)
    (hll : ldv .ld M' bufLenAddr = BitVec.ofNat 64 2016) :
    DcAt S M' H F L C { G with lbuf := some b } hs st := by
  have hP : ∀ a, LbWords a → OutHeap a := fun a ha => by
    simp only [LbWords, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, dc_addrs] at ha ⊢; omega
  have hb1 := h.heap.out_frame hm hP
  have hblk : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a := fun a ha =>
    hm a fun hp => (hP a hp).1 (h.inBlocks_heap ha).1
  have hbl : ({ G with lbuf := some b } : DcG).blocks = G.blocks ++ [b] := by
    simp only [DcG.blocks, hn, Option.toList_some, Option.toList_none, List.append_nil]
  refine ⟨((hb1.subRaw (X' := ⟨G.blocks, M'⟩) (fun c hc => hc)
      fun c hc a ha => (hblk a ⟨c, hc, ha⟩).symm).addRaw f.live f.notNum).subRaw
      (fun c hc => by
        simp only [DcG.raws, hbl, List.mem_append, List.mem_singleton] at hc ⊢
        rcases hc with hc | rfl
        · exact List.mem_cons_of_mem _ hc
        · exact List.mem_cons_self) (fun _ _ _ _ => rfl),
    ?_, h.view.withLbuf hblk (fun a _ hw => hm a hw) hl (fun _ e => by cases e; exact hll),
    { h.den with lbuf := fun c e => by cases e; exact hsz }, h.glob, h.col⟩
  rw [hbl]
  exact List.nodup_append.mpr ⟨h.nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, fun x hx y hy e => by
    simp only [List.mem_singleton] at hy; subst hy; subst e; exact f.notG hx⟩

/-! ## The machine -/

/-- `dc_readstring`'s saved registers in its 112-byte frame. -/
abbrev rsSlots : List (Nat × Nat) :=
  [(25, 24), (19, 72), (18, 80), (9, 88), (1, 104), (23, 40), (22, 48), (21, 56), (20, 64), (8, 96),
    (24, 32)]

/-- The registers `dc_readstring` restores. -/
abbrev rsSaved : List Nat := [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25]

/-- The last loads of `dc_readstring`'s epilogue (`0x80003bc4`): `a0` from
the tag word, `s2`–`s9` and `s1` back, `a1 = s1`. -/
theorem rs_ret {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} {R0 : Nat → BitVec 64}
    (hsf : StackFrame S sp 112) (hsv : SavedWords M (sp - 112) rsSlots R0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (h1 : R 1 = R0 1) (h8 : R 8 = R0 8)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [2, 9, 10, 11, 18, 19, 20, 21, 22, 23, 24, 25] R' R →
      (∀ z ∈ rsSaved, R' z = R0 z) → R' 2 = BitVec.ofNat 64 sp → R' 10 = ldv .ld M (sp - 112) →
      R' 11 = R 9 → DWO live S Q t (R0 1) R' M) :
    DWO live S Q t 0x80003bc4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e9 := hsv.get 9 88
  have e18 := hsv.get 18 80
  have e19 := hsv.get 19 72
  have e20 := hsv.get 20 64
  have e21 := hsv.get 21 56
  have e22 := hsv.get 22 48
  have e23 := hsv.get 23 40
  have e24 := hsv.get 24 32
  have e25 := hsv.get 25 24
  bc_run hlive hlive [h2, e9, e18, e19, e20, e21, e22, e23, e24, e25]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · bsimp [h1]; exact hal
  rw [h1]
  refine hk _ (by keeps_tac Keeps.refl _ _) ?_ (by bsimp []; congr 1; omega) (by bsimp []) (by bsimp [])
  simp only [rsSaved, List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [h1, h8, e9, e18, e19, e20, e21, e22, e23, e24, e25]

/-- `dc_readstring`'s epilogue (`0x80003bb4`): `s_refs = 1`, the tag word
`DC_STRING`, the saved registers back. -/
theorem rs_epi {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp p : Nat} {R0 : Nat → BitVec 64}
    (hS : HeapOwn S) (hp0 : heapStart ≤ p) (hp1 : p + 24 ≤ heapEnd) (hpa : p % 8 = 0)
    (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp) (hsv : SavedWords M (sp - 112) rsSlots R0)
    (htag : (ldv .ld M (sp - 112)).toNat % 2 ^ 32 = 2) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (h9 : R 9 = BitVec.ofNat 64 p)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps ([2, 10, 11, 15] ++ rsSaved) R' R → (∀ z ∈ rsSaved, R' z = R0 z) →
      R' 2 = BitVec.ofNat 64 sp → (R' 10).toNat % 2 ^ 32 = 2 → R' 11 = BitVec.ofNat 64 p →
      DWO live S Q t (R0 1) R' (writeLog M [(p + 16, 4, 1#64)])) :
    DWO live S Q t 0x80003bb4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab hp1
  simp only [heapStart] at hp0
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hsv' : SavedWords (writeLog M [(p + 16, 4, 1#64)]) (sp - 112) rsSlots R0 :=
    hsv.storeAway 1#64 fun q hq => by
      simp only [rsSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have e1 := hsv.get 1 104
  have e8 := hsv.get 8 96
  bc_run hlive hS [h2, h9, e1, e8] at 0x80003bc4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine rs_ret hlive hsf hsv' _ (by bsimp [h2]) (by bsimp [e1]) (by bsimp [e8]) hal
    fun R' hk1 hsv1 e2 e10 e11 => hk R' ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
      hsv1 e2 ?_ (by rw [e11]; bsimp [h9])
  rw [e10, ldv_ld_miss _ _ (by omega)]
  exact htag

/-- `dc_readstring`'s string stores and return (`0x80003b9c`, after
`memcpy`): the empty string `msObj b1 b2 []` joins the state. -/
theorem rs_tail {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b1 b2 : Blk}
    {sp : Nat} {R0 : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (f1 : DcFresh H F L G b1) (f2 : DcFresh H F L G b2)
    (hne : b1 ≠ b2) (hs1 : 24 ≤ b1.sz) (hs2 : 1 ≤ b2.sz)
    (hptr : ldv .ld M b1.pay = BitVec.ofNat 64 b2.pay)
    (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp) (hsv : SavedWords M (sp - 112) rsSlots R0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (h8 : R 8 = 0#64)
    (h9 : R 9 = BitVec.ofNat 64 b1.pay) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps ([2, 10, 11, 14, 15] ++ rsSaved) R' R → (∀ z ∈ rsSaved, R' z = R0 z) →
      R' 2 = BitVec.ofNat 64 sp → (R' 10).toNat % 2 ^ 32 = 2 → R' 11 = BitVec.ofNat 64 b1.pay →
      DcAt S M' H F L C { G with strs := msObj b1 b2 [] :: G.strs } (.str b1.pay :: hs) st →
      StkOut sp 112 M' M → DWO live S Q t (R0 1) R' M') :
    DWO live S Q t 0x80003b9c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hb1 := blk_bounds h.heap.heap f1.live
  have hb2 := blk_bounds h.heap.heap f2.live
  simp only [heapStart, heapEnd] at hb1 hb2
  have hsep := fresh_sep h f1 f2 hne (by omega) (by omega)
  bc_run hlive hS [h2, h8, h9, hptr] at 0x80003bb4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hD0 := h.outWrite (MemOnly.store M (sp - 112) 4 2#64) fun a ha =>
    ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have hD := hD0.makeStr (s := []) f1 f2 hne hs1 hs2 (by simp) (by simp)
    (fun i hi => absurd hi (by simp)) (by rw [ldv_ld_miss _ _ (by omega)]; exact hptr)
  have hsv' : SavedWords (writeLog (writeLog (writeLog M [(sp - 112, 4, 2#64)]) [(b2.pay, 1, 0#64)])
      [(b1.pay + 8, 8, 0#64)]) (sp - 112) rsSlots R0 :=
    ((hsv.storeAway 2#64 fun q hq => by
      simp only [rsSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega).storeAway
      0#64 fun q hq => by omega).storeAway 0#64 fun q hq => by omega
  refine rs_epi (p := b1.pay) (sp := sp) hlive hS (by simp only [heapStart]; omega)
    (by simp only [heapEnd]; omega) (by omega) hsf hab hsv' ?_ _ (by bsimp [h2]) (by bsimp [h9]) hal
    fun R' hk1 hsv1 e2 e10 e11 => hk R' _ ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
      hsv1 e2 e10 e11 hD ?_
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ld_lo32_sw]; rfl
  · intro a ho _ hf
    simp only [frameIn] at hf
    have := ho.1
    simp only [heapStart, heapEnd] at this
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]

/-- `dc_readstring` at end of input (`0x80003b70`, nothing read: the cursor
`s0` at `line_buf`): `dc_malloc(24)`, `dc_malloc(1)`, an empty `memcpy`, the
tail. -/
theorem rs_make {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {lb : Blk}
    {sp : Nat} {R0 : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hlb : G.lbuf = some lb)
    (hsf : StackFrame S sp 128) (hab : heapEnd + 128 ≤ sp) (hsv : SavedWords M (sp - 112) rsSlots R0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (h8 : R 8 = BitVec.ofNat 64 lb.pay)
    (h24 : R 24 = 0x8001cda8#64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' b1 b2, Keeps ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25] ++ cClob) R' R →
      (∀ z ∈ rsSaved, R' z = R0 z) → R' 2 = BitVec.ofNat 64 sp → (R' 10).toNat % 2 ^ 32 = 2 →
      R' 11 = BitVec.ofNat 64 b1.pay →
      DcAt S M' H' F L C { G with strs := msObj b1 b2 [] :: G.strs } (.str b1.pay :: hs) st →
      StkOut sp 128 M' M → DWO live S Q t (R0 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128) → StkOut sp 128 M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80003b70#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hG := h.glob
  have hlw : ldv .ld M lineBufAddr = BitVec.ofNat 64 lb.pay := by
    have := h.view.lbuf; rw [hlb] at this; exact this
  have hlbl : lb ∈ H.live := h.heap.raw.live lb (by
    show lb ∈ G.blocks
    simp only [DcG.blocks, hlb, Option.toList_some, List.mem_append, List.mem_singleton]; simp)
  have hlbb := blk_bounds h.heap.heap hlbl
  simp only [heapStart, heapEnd] at hlbb
  have hlw' : ldv .ld M 2147601832 = BitVec.ofNat 64 lb.pay := hlw
  bc_run hlive hS [h2, h24, hlw'] at 0x80001ea0
  case hLDS =>
    intro b hb
    have hb' := VsaIris.Sym.of_mem_accAddrs hb
    apply hG
    simp only [DcGlob, dc_addrs] at hb' ⊢
    omega
  -- the frame above the callee's 16 bytes
  have hP : ∀ a, (sp - 112 ≤ a ∧ a < sp) → OutHeap a := fun a ha =>
    outHeap_of_ge (by simp only [heapEnd]; omega)
  refine dc_malloc_spec hlive h.heap.heap (n := 24) (sp := sp - 112) (by decide)
    (hsf.sub (m := 112) (n := 16) (by decide)) (by simp only [heapEnd]; omega) _ (by bsimp [])
    (by bsimp [h2]) (by bsimp []) (fun R1 M2 H2 b1 hk1 hp hr10 => ?_) (fun R1 M2 hr2 hfr => ?_)
  rotate_left
  · refine hoom R1 M2 (by rw [hr2, Nat.sub_sub]) fun a ho hg hf => ?_
    exact hfr a (OutHeap.not_alloc h.heap.heap ho) fun hf' => hf (by
      simp only [frameIn] at hf' ⊢; omega)
  obtain ⟨h2', g1⟩ := h.malloc hp (by decide) (by simp only [heapEnd]; omega)
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
  have q8 : R1 8 = BitVec.ofNat 64 lb.pay := by rw [hk1.get 8 (by decide)]; bsimp [h8]
  have q18 : R1 18 = BitVec.ofNat 64 lb.pay := by rw [hk1.get 18 (by decide)]; bsimp [hlw']
  bsimp []
  bc_run hlive hS2 [q2, q8, q18, hr10, BitVec.sub_self] at 0x80001ea0
  refine dc_malloc_spec hlive h2'.heap.heap (n := 1) (sp := sp - 112) (by decide)
    (hsf.sub (m := 112) (n := 16) (by decide)) (by simp only [heapEnd]; omega) _ (by bsimp [])
    (by bsimp [q2]) (by bsimp []) (fun R2 M3 H3 b2 hk2 hp2 hr10' => ?_) (fun R2 M3 hr2 hfr => ?_)
  rotate_left
  · refine hoom R2 M3 (by rw [hr2, Nat.sub_sub]) fun a ho hg hf => ?_
    rw [hfr a (OutHeap.not_alloc h2'.heap.heap ho) fun hf' => hf (by
      simp only [frameIn] at hf' ⊢; omega)]
    exact hp.frame a (OutHeap.not_alloc h.heap.heap ho) fun hf' => hf (by
      simp only [frameIn] at hf' ⊢; omega)
  obtain ⟨h3, g2⟩ := h2'.malloc hp2 (by decide) (by simp only [heapEnd]; omega)
  have g1' := g1.afterMalloc hp2
  have hsz1 := hp.size
  have hsz2 := hp2.size
  have hne : b1 ≠ b2 := fun e => by
    subst e
    have e1 : b1.fin = b1.pay + b1.sz := rfl
    have e2 : b1.pay = b1.h + 16 := rfl
    exact live_not_alloc h2'.heap.heap g1.live (a := b1.pay) ⟨Nat.le_refl _, by omega⟩
      (hp2.alloc _ (by omega) (by omega))
  have hS3 : HeapOwn S := fun a e1 e2 => h3.heap.heap.own a e1 e2
  have hb1 := blk_bounds h3.heap.heap g1'.live
  have hb2 := blk_bounds h3.heap.heap g2.live
  simp only [heapStart, heapEnd] at hb1 hb2
  have r2 : R2 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk2.get 2 (by decide)]; bsimp [q2]
  have r8 : R2 8 = 0#64 := by rw [hk2.get 8 (by decide)]; bsimp [BitVec.sub_self]
  have r9 : R2 9 = BitVec.ofNat 64 b1.pay := by rw [hk2.get 9 (by decide)]; bsimp [hr10]
  have r18 : R2 18 = BitVec.ofNat 64 lb.pay := by
    rw [hk2.get 18 (by decide)]; bsimp []; exact q18
  bsimp []
  bc_run hlive hS3 [r2, r8, r9, r18, hr10'] at 0x8000086c
  refine memcpy_spec hlive (d := b2.pay) (s := lb.pay) (n := 0) ⟨⟨fun _ h0 => absurd h0 (Nat.not_lt_zero _), by rw [htx]; omega,
      by omega⟩, ⟨fun _ h0 => absurd h0 (Nat.not_lt_zero _), by rw [htx]; omega, by omega⟩, by omega⟩
    _ (by bsimp [hr10']) (by bsimp [r18]) (by bsimp [r8]) (by bsimp []) fun R3 M4 hk3 hfill => ?_
  have hin : ∀ a, (b1.pay ≤ a ∧ a < b1.pay + 8) → b1.In a := fun a ha => by
    simp only [Blk.In, Blk.pay, Blk.fin] at *; omega
  have hX := (h3.rawWrite g1' ((MemOnly.store M3 b1.pay 8 (BitVec.ofNat 64 b2.pay)).mono hin)).rawWrite g2
    (fun a _ => hfill.rest a (by omega))
  have hag : ∀ a, OutHeap a → ¬ frameIn (sp - 112) 16 a → imgM M4 a = imgM M a := fun a ho hf => by
    have := ho.1
    simp only [heapStart, heapEnd] at this
    rw [hfill.rest a (by omega), imgM_store_miss _ _ (by omega),
      hp2.frame a (OutHeap.not_alloc h2'.heap.heap ho) hf, hp.frame a (OutHeap.not_alloc h.heap.heap ho) hf]
  have hsv4 : SavedWords M4 (sp - 112) rsSlots R0 :=
    hsv.transport (lo := 24) (top := 112) (hag := fun a e1 e2 =>
      hag a (outHeap_of_ge (by simp only [heapEnd]; omega)) (by simp only [frameIn]; omega))
  have hptr : ldv .ld M4 b1.pay = BitVec.ofNat 64 b2.pay := by
    rw [ldv_congr .ld fun j hj => hfill.rest _ (by omega)]
    exact ldv_store_hit _ _ _
  refine rs_tail hlive hX g1' g2 hne hsz1 hsz2 hptr (hsf.shrink (by decide)) (by omega) hsv4 R3
    (by rw [hk3.get 2 (by decide)]; bsimp [r2]) (by rw [hk3.get 8 (by decide)]; bsimp [r8])
    (by rw [hk3.get 9 (by decide)]; bsimp [r9]) hal
    fun R' M' hk4 hsv1 e2 e10 e11 hd hso => hk R' M' H3 b1 b2 ?_ hsv1 e2 e10 e11 hd ?_
  · exact (hk4.mono (by decide)).trans ((hk3.mono (by decide)).trans (by keeps_tac
      ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _))))))
  · intro a ho hg hf
    rw [hso a ho hg fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]
    exact hag a ho fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

/-- `dc_readstring`'s read loop at end of input (`0x80003b2c`): `getc`
returns `EOF` at once. -/
theorem rs_read {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {lb : Blk}
    {sp : Nat} {R0 : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hlb : G.lbuf = some lb)
    (hsf : StackFrame S sp 128) (hab : heapEnd + 128 ≤ sp) (hsv : SavedWords M (sp - 112) rsSlots R0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (h8 : R 8 = BitVec.ofNat 64 lb.pay)
    (h20 : R 20 = 0x8001cda0#64) (h24 : R 24 = 0x8001cda8#64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' b1 b2, Keeps ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25] ++ cClob) R' R →
      (∀ z ∈ rsSaved, R' z = R0 z) → R' 2 = BitVec.ofNat 64 sp → (R' 10).toNat % 2 ^ 32 = 2 →
      R' 11 = BitVec.ofNat 64 b1.pay →
      DcAt S M' H' F L C { G with strs := msObj b1 b2 [] :: G.strs } (.str b1.pay :: hs) st →
      StkOut sp 128 M' M → DWO live S Q t (R0 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128) → StkOut sp 128 M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80003b2c#64 R M := by
  have hG := h.glob
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, h8, h20, h24] at 0x80000700
  case hLDS =>
    intro b hb
    have hb' := VsaIris.Sym.of_mem_accAddrs hb
    apply hG
    simp only [DcGlob, dc_addrs] at hb' ⊢
    omega
  refine getc_spec hlive _ ?hal fun R1 hk1 e10 => ?_
  case hal => bsimp []
  have r25 : R1 25 = BitVec.allOnes 64 := by rw [hk1.get 25 (by decide)]; bsimp []; rfl
  bsimp []
  bc_run hlive hlive [e10, r25] at 0x80003b70
  refine rs_make hlive h hlb hsf hab hsv _ ?q2 ?q8 ?q24 hal
    (fun R' M' H' b1 b2 hk2 => hk R' M' H' b1 b2 ((hk2.mono (by decide)).trans (by keeps_tac
      ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))) hoom
  case q2 => bsimp []; rw [hk1.get 2 (by decide)]; bsimp [h2]
  case q8 => bsimp []; rw [hk1.get 8 (by decide)]; bsimp [h8]
  case q24 => bsimp []; rw [hk1.get 24 (by decide)]; bsimp [h24]

/-- The ghost after `dc_readstring`: the same nodes, strings and lost
references, the line buffer allocated. -/
structure LbufNext (G G' : DcG) : Prop where
  stk : G'.stk = G.stk
  regs : G'.regs = G.regs
  strs : G'.strs = G.strs
  lk : G'.lk = G.lk
  lbuf : G'.lbuf.isSome

/-- `dc_readstring`'s first call (`0x80003c4c`): `buflen = 2016`,
`line_buf = dc_malloc (2016)`, then the read loop. -/
theorem rs_alloc {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {sp : Nat} {R0 : Nat → BitVec 64}
    (h : DcAt S M H F L C G hs st) (hn : G.lbuf = none)
    (hsf : StackFrame S sp 128) (hab : heapEnd + 128 ≤ sp) (hsv : SavedWords M (sp - 112) rsSlots R0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 112))
    (h20 : R 20 = 0x8001cda0#64) (h24 : R 24 = 0x8001cda8#64) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' G' b1 b2, Keeps ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25] ++ cClob) R' R →
      (∀ z ∈ rsSaved, R' z = R0 z) → R' 2 = BitVec.ofNat 64 sp → (R' 10).toNat % 2 ^ 32 = 2 →
      R' 11 = BitVec.ofNat 64 b1.pay → LbufNext G G' →
      DcAt S M' H' F L C { G' with strs := msObj b1 b2 [] :: G'.strs } (.str b1.pay :: hs) st →
      StkOut sp 128 M' M → DWO live S Q t (R0 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128) → StkOut sp 128 M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80003c4c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have hG := h.glob
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [h2, h20] at 0x80001ea0
  case hS =>
    intro b hb
    have hb' := VsaIris.Sym.of_mem_accAddrs hb
    apply hG
    simp only [DcGlob, dc_addrs] at hb' ⊢
    omega
  case hea => simp only [StOK, htx, and_true]; omega
  have hm1 : MemOnly LbWords (writeLog M [(2147601824, 8, 2016#64)]) M := fun a ha =>
    imgM_store_miss _ _ (by
      have : ¬(0x8001cda0 ≤ a ∧ a < 0x8001cda8 + 8) := ha
      omega)
  have h1 := h.lbufWrite hm1 (by
      rw [hn, ldv_ld_miss _ _ (by simp only [dc_addrs]; omega)]
      have := h.view.lbuf; rw [hn] at this; exact this)
    (fun b e => by rw [hn] at e; cases e)
  refine dc_malloc_spec hlive h1.heap.heap (n := 2016) (sp := sp - 112) (by decide)
    (hsf.sub (m := 112) (n := 16) (by decide)) (by simp only [heapEnd]; omega) _ ?a10 ?a2 ?a1
    (fun R1 M2 H2 b hk1 hp hr10 => ?_) (fun R1 M2 hr2 hfr => ?_)
  case a10 => bsimp []
  case a2 => bsimp [h2]
  case a1 => bsimp []
  rotate_left
  · refine hoom R1 M2 (by rw [hr2, Nat.sub_sub]) fun a ho hg hf => ?_
    rw [hfr a (OutHeap.not_alloc h1.heap.heap ho) fun hf' => hf (by
      simp only [frameIn] at hf' ⊢; omega)]
    exact imgM_store_miss _ _ (by simp only [DcGlob, dc_addrs] at hg; omega)
  obtain ⟨h2', g⟩ := h1.malloc hp (by decide) (by simp only [heapEnd]; omega)
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
  have q24 : R1 24 = 0x8001cda8#64 := by rw [hk1.get 24 (by decide)]; bsimp [h24]
  have hG2 := h2'.glob
  bsimp []
  bc_run hlive hlive [q2, q24, hr10] at 0x80003b2c
  case hea => simp only [StOK, htx, and_true]; omega
  case hS =>
    intro c hc
    have hc' := VsaIris.Sym.of_mem_accAddrs hc
    apply hG
    simp only [DcGlob, dc_addrs] at hc' ⊢
    omega
  have hm2 : MemOnly LbWords (writeLog M2 [(2147601832, 8, BitVec.ofNat 64 b.pay)]) M2 := fun a ha =>
    imgM_store_miss _ _ (by
      have : ¬(0x8001cda0 ≤ a ∧ a < 0x8001cda8 + 8) := ha
      omega)
  -- bytes outside the heap's allocator words and the callee frame survive `dc_malloc`
  have hfm : ∀ a, OutHeap a → ¬ frameIn (sp - 112) 16 a →
      imgM M2 a = imgM (writeLog M [(2147601824, 8, 2016#64)]) a := fun a ho hf =>
    hp.frame a (OutHeap.not_alloc h1.heap.heap ho) hf
  have hll : ldv .ld (writeLog M2 [(2147601832, 8, BitVec.ofNat 64 b.pay)]) bufLenAddr =
      BitVec.ofNat 64 2016 := by
    rw [show bufLenAddr = 2147601824 from rfl, ldv_ld_miss _ _ (by omega),
      ldv_congr .ld fun j hj => hfm _ (by
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, widthOfM] at hj ⊢; omega)
        (by simp only [frameIn, widthOfM] at hj ⊢; omega), ldv_store_hit]
  have h3 := h2'.newLbuf hn g hp.size hm2 (ldv_store_hit _ _ _) hll
  have hsv' : SavedWords (writeLog M2 [(2147601832, 8, BitVec.ofNat 64 b.pay)]) (sp - 112) rsSlots R0 :=
    (hsv.transport (lo := 24) (top := 112) (hag := fun a e1 e2 => by
      rw [hfm a (outHeap_of_ge (by simp only [heapEnd]; omega)) (by simp only [frameIn]; omega)]
      exact imgM_store_miss _ _ (by omega))).storeAway _ fun q hq => by
        simp only [rsSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hso : ∀ M', StkOut sp 128 M' (writeLog M2 [(2147601832, 8, BitVec.ofNat 64 b.pay)]) →
      StkOut sp 128 M' M := fun M' hs1 a ho hg hf => by
    have hgl := hg
    simp only [DcGlob, dc_addrs] at hgl
    rw [hs1 a ho hg hf, imgM_store_miss _ _ (by omega),
      hfm a ho (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)), imgM_store_miss _ _ (by omega)]
  refine rs_read hlive h3 rfl hsf hab hsv' _ ?r2 ?r8 ?r20 ?r24 hal
    (fun R' M' H' b1 b2 hk2 hsv2 e2 e10 e11 hd hs1 => hk R' M' H' ({ G with lbuf := some b } : DcG) b1 b2
      ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))) hsv2 e2 e10 e11 ⟨rfl, rfl, rfl, rfl, rfl⟩ hd (hso M' hs1))
    fun R' M' e2 hs1 => hoom R' M' e2 (hso M' hs1)
  case r2 => bsimp [q2]
  case r8 => bsimp []
  case r20 => bsimp []; rw [hk1.get 20 (by decide)]; bsimp [h20]
  case r24 => bsimp [q24]

/-- **`dc_readstring (fp, endch, unget)`** at `0x80003ad8`: the string read up to
end of input, here empty (`getc` reports end of file), as a new string object at
the head of the handles; the first call allocates the 2016-byte line buffer
(`LbufNext`); `dc_malloc` may run out of memory. -/
theorem dc_readstring_spec {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {sp : Nat}
    (h : DcAt S M H F L C G hs st) (hsf : StackFrame S sp 128) (hab : heapEnd + 128 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' G' b1 b2, Keeps cClob R' R → R' 2 = R 2 → (R' 10).toNat % 2 ^ 32 = 2 →
      R' 11 = BitVec.ofNat 64 b1.pay → LbufNext G G' →
      DcAt S M' H' F L C { G' with strs := msObj b1 b2 [] :: G'.strs } (.str b1.pay :: hs) st →
      StkOut sp 128 M' M → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128) → StkOut sp 128 M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80003ad8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hG := h.glob
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hsp := word_sub112 (x := sp) (by omega)
  have hl0 := h.view.lbuf
  bc_run hlive hS [h2, hsp] at 0x80003aec
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have sv1 := ((SavedWords.nil M (sp - 112) R).store 24 32).store 8 96
  generalize hM1 : writeLog (writeLog M [(sp - 112 + 32, 8, R 24)]) [(sp - 112 + 96, 8, R 8)] = M1
    at sv1 ⊢
  have hl1 : ldv .ld M1 0x8001cda8 = ldv .ld M lineBufAddr := by
    rw [← hM1, ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
  rw [← hl1] at hl0
  bc_run hlive hS [hl0] at 0x80003b28
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have sv := (((((((sv1.store 20 64).store 21 56).store 22 48).store 23 40).store 1 104).store 9 88
    ).store 18 80).store 19 72 |>.store 25 24
  generalize hM2 : writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog
    (writeLog M1 [(sp - 112 + 64, 8, R 20)]) [(sp - 112 + 56, 8, R 21)]) [(sp - 112 + 48, 8, R 22)])
    [(sp - 112 + 40, 8, R 23)]) [(sp - 112 + 104, 8, R 1)]) [(sp - 112 + 88, 8, R 9)])
    [(sp - 112 + 80, 8, R 18)]) [(sp - 112 + 72, 8, R 19)]) [(sp - 112 + 24, 8, R 25)] = M2 at sv ⊢
  have hMo : MemOnly (frameIn sp 112) M2 M := fun x hx => by
    rw [← hM2, ← hM1]; simp only [frameIn] at hx; repeat rw [imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hMo fun a ha => asFrame_out (by simp only [heapEnd]; omega) ha
  have hso : ∀ M', StkOut sp 128 M' M2 → StkOut sp 128 M' M := fun M' hs1 a ho hg hf =>
    (hs1 a ho hg hf).trans (hMo a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
  have hfin : ∀ R' Rc, Keeps ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25] ++ cClob) R' Rc →
      Keeps ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25] ++ cClob) Rc R →
      (∀ z ∈ rsSaved, R' z = R z) → R' 2 = BitVec.ofNat 64 sp → Keeps cClob R' R :=
    fun R' Rc k1 k2 hsv e2 => Keeps.restoreAll (rs := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25])
      (k1.trans k2) fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [e2, h2]
        all_goals exact hsv _ (by decide)
  cases hlb : G.lbuf with
  | none =>
    bc_run hlive hS [] at 0x80003c4c
    refine rs_alloc hlive h1 hlb hsf hab sv _ (by bsimp []) (by bsimp []) (by bsimp []) hal
      (fun R' M' H' G' b1 b2 hk2 hsv2 e2 e10 e11 hn hd hs1 => hk R' M' H' G' b1 b2
        (hfin R' _ hk2 (by keeps_tac Keeps.refl _ _) hsv2 e2) (by rw [e2, h2]) e10 e11 hn hd
        (hso M' hs1))
      fun R' M' e2 hs1 => hoom R' M' e2 (hso M' hs1)
  | some lb =>
    have hbG : lb ∈ G.blocks := by
      rw [DcG.blocks, hlb]; exact List.mem_append_right _ List.mem_cons_self
    have hnz := blk_ptr_ne h.heap.heap (h.heap.raw.live lb hbG)
    bc_run hlive hS [] at 0x80003b2c
    all_goals first | (intro hc; exact absurd hc hnz) | skip
    refine rs_read hlive h1 hlb hsf hab sv _ (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
      hal (fun R' M' H' b1 b2 hk2 hsv2 e2 e10 e11 hd hs1 => hk R' M' H' G b1 b2
        (hfin R' _ hk2 (by keeps_tac Keeps.refl _ _) hsv2 e2) (by rw [e2, h2]) e10 e11
        ⟨rfl, rfl, rfl, rfl, by rw [hlb]; rfl⟩ hd (hso M' hs1))
      fun R' M' e2 hs1 => hoom R' M' e2 (hso M' hs1)

end Dc.Mach
