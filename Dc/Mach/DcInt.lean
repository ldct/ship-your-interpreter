import Dc.Mach.DcFree
import Dc.Mach.Bc.Small
import Dc.Mach.Bc.Int2Num
import Dc.Mach.Bc.DoAdd
import Dc.Mach.DcStack

/-!
# A fresh number for a C `int` (M9)

`dc_int2data` (`dc/numeric.c`) is `bc_init_num(&n)` then `bc_int2num(&n,
val)`. On the dc state:

- `dc_init_num_spec`: `bc_init_num` into a stack slot is one more reference
  to `_zero_`, held by the slot as the handle `.num z.p`.
- `DcAt.newNum`: a callee that freed the handle's number and stored a fresh
  one (`FreedRest`, one reference) leaves the state with the new handle.
- `dc_int2num_spec`: `bc_int2num` on a handle held in a stack slot.
- `dc_int2data_spec`: the datum `.num p` for the value `val`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- A reference count rewritten keeps the handles' values. -/
theorem HsKeep.withRefs {L1 L2 : List NumObj} {x : NumObj} {ss : List StrObj} (n : Nat) (hs : List GV) :
    HsKeep ⟨L1 ++ x :: L2, ss⟩ ⟨L1 ++ x.withRefs n :: L2, ss⟩ hs := by
  classical
  exact fun _ _ _ hv => GV.Den.relist (O := ⟨L1 ++ x :: L2, ss⟩) (O' := ⟨L1 ++ x.withRefs n :: L2, ss⟩)
    ⟨fun y hy => ⟨_, BcConsts.subst_mem (x := x) (x' := x.withRefs n) hy,
      ite_rep (x := x) (x' := x.withRefs n) rfl rfl y _⟩, fun o ho => ⟨o, ho, rfl, rfl⟩⟩ hv

/-- **`bc_init_num(num)`** at `0x800049bc` on the dc state, for a stack slot
`q` above the heap: one more reference to `_zero_`, the slot's handle
`.num z.p` joins `hs`, whose values are kept; clobbers `a4`, `a5`. -/
theorem dc_init_num_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) {q : Nat} (hq : PtrSlot S q)
    (hqh : heapEnd ≤ q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' L' C', Keeps [14, 15] R' R → DcAt S M' H F L' C' G (.num C.z.rep.p :: hs) st →
      HsKeep ⟨L, G.strs⟩ ⟨L', G.strs⟩ hs → ldv .ld M' q = BitVec.ofNat 64 C.z.rep.p →
      (∀ a, OutHeap a → ¬ slotBytes q a → imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x800049bc#64 R M := by
  have hzL := h.den.mz
  obtain ⟨L1, L2, hL⟩ := List.append_of_mem hzL
  subst hL
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hn := h.heap.nums C.z hzL
  num_facts hn
  have hrf := hn.refs
  have hzw := h.view.zw
  have hr := h.numRefs_lt hhs hzL
  have hql := hq.lo; have hqh' := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hqh
  have hgz : ∀ b, 0x8001cdc8 ≤ b → b < 0x8001cdd0 → S b := fun b h1 h2 =>
    h.glob b (by unfold DcGlob; simp only [dc_addrs] at *; omega)
  dx_run hlive at 0x800049c0
  apply st_800049c0 hlive
  · bsimp []; bc_addr
  · bsimp []; intro b hb; have := of_mem_accAddrs hb; exact hgz b (by omega) (by omega)
  dx_run hlive
  all_goals bsimp [h10, hrf, hzw, sxw_ofNat]
  all_goals first | bc_addr | exact acc_heap hS (by omega) (by omega) | exact hq.acc | skip
  have h1 := h.bumpNum hhs (v := BitVec.ofNat 64 (C.z.rep.refs + 1)) (toNat_ofNat_mod32 (by omega))
  refine hk _ _ _ _ (by keeps_tac Keeps.refl _ _)
    (h1.outWrite (P := slotBytes q) (MemOnly.store _ _ _ _) fun a ha =>
      ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
        have := hg.lt; simp only [heapStart] at this; omega⟩) (HsKeep.withRefs _ hs) (ldv_store_hit _ _ _) ?_
  intro a ho hs
  rw [imgM_store_miss _ _ (by omega)]
  refine imgM_store_miss _ _ (Classical.byContradiction fun hc => ho.1 ?_)
  simp only [heapStart, heapEnd]; omega

/-- A number added keeps the handles' values. -/
theorem HsKeep.cons {L : List NumObj} {ss : List StrObj} {y : NumObj} (hs : List GV) :
    HsKeep ⟨L, ss⟩ ⟨y :: L, ss⟩ hs :=
  fun _ _ _ hv => GV.Den.relist (O := ⟨L, ss⟩) (O' := ⟨y :: L, ss⟩)
    ⟨fun z hz => ⟨z, List.mem_cons_of_mem _ hz, rfl, rfl⟩, fun o ho => ⟨o, ho, rfl, rfl⟩⟩ hv

/-- **A fresh number for a freed handle**: a callee freed the handle `.num
x.p`'s number (`FreedRest`) and added `y` with one reference; the state
holds the handle `.num y.p` instead. The constants may follow the
decremented object. -/
theorem DcAt.newNum {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F F' : List Blk}
    {L1 L2 L' : List NumObj} {x y : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st) (hr : FreedRest L1 L2 x L')
    (hb : BcHeap S (G.raws M) M' H' F' (y :: L')) (h1 : y.rep.refs = 1) (hno : y.rep.Norm)
    (hpos : 1 ≤ y.rep.len) (how : y.Owns) (hgl : ∀ a, DcGlob a → imgM M' a = imgM M a) :
    ∃ C', DcAt S M' H' F' (y :: L') C' G (.num y.rep.p :: hs) st ∧
      HsKeep ⟨L1 ++ x :: L2, G.strs⟩ ⟨y :: L', G.strs⟩ hs := by
  have hag : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a := fun a ⟨c, hc, ha⟩ =>
    hb.raw.img c hc a ha
  have hb0 : BcHeap S (G.raws M) M' H' F' ([] ++ y :: L') := hb
  have hne : ∀ z ∈ L', z.rep.p ≠ y.rep.p := fun z hz => hb0.p_ne_all z (by simpa using hz)
  have hb' : BcHeap S (G.raws M') M' H' F' (y :: L') :=
    hb.subRaw (X' := G.raws M') (fun c hc => hc) fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm
  cases hr with
  | dec h2 =>
    exact ⟨_, ⟨hb', h.nodup, (h.view.frame hag hgl).subst (x := x) (x' := x.decRef) rfl rfl,
      (h.den.dec h.heap.p_ne_all h2).addNum hne h1 hno hpos how, h.glob, h.col⟩,
      (HsKeep.decRef hs).trans (HsKeep.cons hs)⟩
  | rel h1' =>
    exact ⟨C, ⟨hb', h.nodup, h.view.frame hag hgl,
      (h.den.rel h.heap.p_ne_all h1').addNum hne h1 hno hpos how, h.glob, h.col⟩,
      (HsKeep.rel h.den h1' _).trans (HsKeep.cons hs)⟩

/-- **`bc_int2num(num, val)`** at `0x8000690c` on the dc state, the handle
`.num p` held in the stack slot `q` above the heap: the slot's handle is
replaced by a fresh number for `val`, or `out_of_memory`. -/
theorem dc_int2num_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat}
    (h : DcAt S M H F L C G (.num p :: hs) st) {q sp : Nat} {v : Int} (hq : PtrSlot S q)
    (hqh : heapEnd ≤ q) (hw : ldv .ld M q = BitVec.ofNat 64 p) (hsf : StackFrame S sp 128)
    (hab : heapEnd + 128 ≤ sp) (hqf : q + 8 ≤ sp - 128 ∨ sp ≤ q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h11 : R 11 = BitVec.ofInt 64 v)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0) (hvlo : -2 ^ 31 < v)
    (hvhi : v < 2 ^ 31)
    (hk : ∀ R' M' H' F' L' C' y, Keeps i2nClob R' R →
      DcAt S M' H' F' (y :: L') C' G (.num y.rep.p :: hs) st → y.rep.num = Num.ofInt v →
      ldv .ld M' q = BitVec.ofNat 64 y.rep.p →
      (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 128 a → imgM M' a = imgM M a) →
      HsKeep ⟨L, G.strs⟩ ⟨y :: L', G.strs⟩ hs → DW live S Q (R 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128) →
      (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 128 a → imgM M' a = imgM M a) →
      DW live S Q 0x80002bcc#64 R' M') :
    DW live S Q 0x8000690c#64 R M := by
  obtain ⟨L1, L2, x, rfl, rfl⟩ := h.handle_num
  have hqh' := hqh; have hab' := hab
  simp only [heapEnd] at hqh' hab'
  have hsl := hsf.lo
  have hsl' : ∀ a, slotBytes q a → OutHeap a := fun a ha => outHeap_of_ge (by simp only [heapEnd]; omega)
  have e := h.freeEntry (sp := sp - 96) hq hqh hw (StackFrame.sub (m := 96) (n := 32) hsf (by decide))
    (by simp only [heapEnd]; omega) (by omega)
  refine bc_int2num_spec hlive ⟨hsf, hab, hq, hsl', hqf, h2, hal, hvlo, hvhi⟩ e h10 h11
    ⟨fun R' Mt' H' F' L' y hk1 hp => ?_, fun R' Mt' h2' hm => hoom R' Mt' h2' hm⟩
  obtain ⟨C', hd, hkp⟩ := h.newNum hp.rest hp.heap hp.refs hp.norm hp.pos hp.owns fun a ha =>
    hp.out a ha.outHeap (fun hs => by have := ha.lt; simp only [heapStart] at this; omega)
      (fun hf => by have := ha.lt; simp only [heapStart, frameIn] at this hf; omega)
  refine hk R' Mt' H' F' L' C' y hk1 hd hp.num ?_ hp.out hkp
  rw [hp.slot, (hp.heap.blocks y List.mem_cons_self).sPay]

/-- **`dc_int2data(val)`** at `0x800026d8`, `-2^31 < val < 2^31`: returns a
fresh handle `g` (one reference) denoting `val`; clobbers `t0`, `a0`–`a5`. -/
theorem dc_int2data_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) {sp : Nat} {v : Int}
    (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofInt 64 v) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0) (hvlo : -2 ^ 31 < v) (hvhi : v < 2 ^ 31)
    (hk : ∀ R' M' H' F' L' C' g, Keeps i2nClob R' R → DatRegs (R' 10) (R' 11) g →
      g.Den ⟨L', G.strs⟩ (.num (Num.ofInt v)) → DcAt S M' H' F' L' C' G (g :: hs) st →
      StkOut sp 192 M' M → DW live S Q (R 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 192) → StkOut sp 192 M' M →
      DW live S Q 0x80002bcc#64 R' M') :
    DW live S Q 0x800026d8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  bc_run hlive hS [h2, h10, word_sub64 (x := sp) (by omega)] at 0x800049bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 64) (writeLog (writeLog M [(sp - 64 + 8, 8, BitVec.ofInt 64 v)])
      [(sp - 64 + 56, 8, R 1)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hP : ∀ a, frameIn sp 192 a → OutHeap a ∧ ¬ DcGlob a := fun a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have h1 := h.outWrite hM1 fun a ha => hP a (by simp only [frameIn] at ha ⊢; omega)
  have hq : PtrSlot S (sp - 64 + 24) :=
    ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩
  refine dc_init_num_spec hlive h1 hhs hq (by simp only [heapEnd]; omega) _ (by bsimp []) (by bsimp [])
    fun R1 M2 L2 C2 hk1 hd2 _ hw2 hfr2 => ?_
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk1.get 2 (by decide)]; bsimp []
  have hv8 : ldv .ld M2 (sp - 64 + 8) = BitVec.ofInt 64 v := by
    rw [ldv_congr .ld fun j hj => hfr2 _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))
      fun hs => by simp only [slotBytes, widthOfM] at hs hj; omega]
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have hS2 : HeapOwn S := fun a h1 h2 => hd2.heap.heap.own a h1 h2
  bsimp []
  bc_run hlive hS2 [q1, hv8] at 0x8000690c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_int2num_spec hlive hd2 hq (by simp only [heapEnd]; omega) hw2
    (StackFrame.sub (m := 64) (n := 128) hsf (by decide)) (by simp only [heapEnd]; omega)
    (.inr (by omega)) _ (by bsimp []) (by bsimp []) (by bsimp [q1]) (by bsimp []) hvlo hvhi
    (fun R3 M3 H3 F3 L3 C3 y hk3 hd3 hnum hw3 hfr3 _ => ?_) (fun R3 M3 hr2 hfr3 => ?_)
  rotate_left
  · refine hoom R3 M3 (by rw [hr2, Nat.sub_sub]) fun a ho hg hf => ?_
    rw [hfr3 a ho (fun hs => hf (by simp only [slotBytes, frameIn] at hs ⊢; omega))
      (fun hs => hf (by simp only [frameIn] at hs ⊢; omega)),
      hfr2 a ho (fun hs => hf (by simp only [slotBytes, frameIn] at hs ⊢; omega))]
    exact hM1 a fun hs => hf (by simp only [frameIn] at hs ⊢; omega)
  have q3 : R3 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk3.get 2 (by decide)]; bsimp [q1]
  have hra : ldv .ld M3 (sp - 64 + 56) = R 1 := by
    rw [ldv_congr .ld fun j hj => (hfr3 _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))
      (fun hs => by simp only [slotBytes, widthOfM] at hs hj; omega)
      (fun hs => by simp only [frameIn, widthOfM] at hs hj; omega)).trans
      (hfr2 _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))
      fun hs => by simp only [slotBytes, widthOfM] at hs hj; omega)]
    rw [ldv_store_hit]
  have hS3 : HeapOwn S := fun a h1 h2 => hd3.heap.heap.own a h1 h2
  bsimp []
  bc_run hlive hS3 [q3, hra, hw3]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first | exact hal | skip
  have hP3 : ∀ a, (sp - 64 + 16 ≤ a ∧ a < sp - 64 + 16 + 4) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    hP a (by simp only [frameIn]; omega)
  have hK : ∀ z, z ∉ 2 :: i2nClob → z ≠ 1 → R3 z = R z := fun z hz h1 => by
    simp only [i2nClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hk3 z (by simp only [i2nClob, List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)]
    simp only [upd, h1, show z ≠ 10 by omega, show z ≠ 11 by omega, ite_false]
    rw [hk1 z (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)]
    simp only [upd, h1, show z ≠ 10 by omega, show z ≠ 2 by omega, ite_false]
  all_goals
    refine hk _ _ H3 F3 (y :: L3) C3 (.num y.rep.p)
      (Keeps.restore (by rw [h2]; congr 1; omega) fun z hz => ?_) ⟨?_, by bsimp []; rfl⟩
      ⟨y, List.mem_cons_self, rfl, hnum⟩ (hd3.outWrite (MemOnly.store M3 _ 4 1#64) hP3)
      fun a ho hg hf => ?_
    · by_cases e1 : z = 1
      · subst e1; simp [upd]
      · simp only [i2nClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        simp only [upd, e1, show z ≠ 15 by omega, show z ≠ 10 by omega, show z ≠ 11 by omega,
          show z ≠ 2 by omega, ite_false]
        exact hK z (by simp only [i2nClob, List.mem_cons, List.not_mem_nil, or_false, not_or]; omega) e1
    · bsimp []; rw [ld_lo32_sw]; rfl
    · simp only [frameIn] at hf
      rw [imgM_store_miss _ _ (by omega),
        hfr3 a ho (fun hs => hf (by simp only [slotBytes] at hs; omega))
          (fun hs => hf (by simp only [frameIn] at hs; omega)),
        hfr2 a ho (fun hs => hf (by simp only [slotBytes] at hs; omega))]
      exact hM1 a fun hs => hf (by simp only [frameIn] at hs; omega)

end Dc.Mach
