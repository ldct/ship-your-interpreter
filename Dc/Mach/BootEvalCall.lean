import Dc.Mach.MainTail
import Dc.Mach.StackBound

/-!
# The boot's call of `evalstr` (M11/M12)

```
80001914 addi sp,sp,-16 ; sd ra,8(sp) ; jal evalstr        (dc_evalstr)
```

`EvEntryP`: `EvalstrSpec`'s machine premises at `evalstr`'s entry, as one
named structure (`EvEntryP.spec` applies the spec). `EvalstrDivSpec`: the
stuck direction, the partial-WP statement `evalstr` owes when its string has
no terminating evaluation (stated here for M12; its proof belongs with
`EvalstrSpec`'s).

`evcall_boot`: from `main`'s call of `dc_evalstr` (`BootEval`, on a loaded
configuration) to `evalstr`'s entry with `EvEntryP` at `sp = evSp`,
`W = evW`, nesting `dcD`, the string datum at `0x87ffffe0`, and the two
saved return addresses (`dc_evalstr`'s and `main`'s) the return path reads.
-/

namespace Dc.Mach

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config)

set_option linter.unusedSimpArgs false

/-- **`EvalstrSpec`'s machine premises** at `evalstr`'s entry. -/
structure EvEntryP (S : Nat → Prop) (sp W d k q : Nat) (M : Mem) (R : Nat → BitVec 64) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St)
    (o : StrObj) : Prop where
  sb : StrBound (2 ^ 24) st
  srt : ArrSorted st
  dc : DcAt S M H F L C G (xs ++ hs) st
  strIn : o ∈ G.strs
  held : hs.head? = some (.str o.hb.pay)
  slot : DatAt M q (.str o.hb.pay)
  slotPlace : DatSlot S sp q
  r2 : R 2 = BitVec.ofNat 64 sp
  r10 : R 10 = BitVec.ofNat 64 q
  al : (R 1).toNat % 4 = 0
  frame : StackFrame S sp W
  room : heapEnd + W ≤ sp
  stk : 176 * (d + 1) + 1216 + rmStack (2 ^ 30) ≤ W
  stkPr : 176 * (d + 1) + 192 + 336 + prN ≤ W
  stkDn : 176 * (d + 1) + 192 + 336 + dnN ≤ W
  budget : G.lk.length + xs.length + hs.length + 4 * k + 8 ≤ 2 ^ 20
  mb : MulBase S M
  err : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a
  globs : EvGlobs S M

/-- `EvalstrSpec` at premises `EvEntryP`. -/
theorem EvEntryP.spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hev : EvalstrSpec live S Q) {t0 : String} {sp W d k q : Nat} {M : Mem} {R : Nat → BitVec 64}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
    {st st' : St} {o : StrObj} {r : Status} (e : EvEntryP S sp W d k q M R H F L C G hs xs st o)
    (hl : Loop 70 st ⟨o.s, 1, false⟩ st' r) (hb : EvBudget 70 d k st ⟨o.s, 1, false⟩)
    (ho : EvOom live S Q sp W q M) (hk : EvK live S Q t0 sp W k q M R G hs xs st' r) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80001448#64 R M :=
  hev t0 sp W d k q M R H F L C G hs xs st st' o r hl hb e.sb e.srt e.dc e.strIn e.held e.slot e.slotPlace e.r2
    e.r10 e.al e.frame e.room e.stk e.stkPr e.stkDn e.budget e.mb e.err e.globs ho hk

/-- **`evalstr` in the stuck direction**: with no terminating evaluation of
its string, the run from `evalstr`'s entry (premises `EvEntryP`, budgets
`EvBudget`) satisfies the partial WP with a nonzero exit code: it diverges,
or it halts through an error exit (`dc_memfail`'s status 1). -/
def EvalstrDivSpec (live S : Nat → Prop) : Prop :=
  ∀ [_G : MachGS .hasLC MachGF] (t0 : String) (sp W d k q : Nat) (M : Mem) (R : Nat → BitVec 64)
    (H : Heap) (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St)
    (o : StrObj),
    (¬ ∃ st' r, Loop 70 st ⟨o.s, 1, false⟩ st' r) → EvBudget 70 d k st ⟨o.s, 1, false⟩ →
    EvEntryP S sp W d k q M R H F L C G hs xs st o →
    ∀ rv mv, Matches dcRegs S 0x80001448#64 R M rv mv →
    roOwn (GF := MachGF) roR dcText ∗ RunRes S t0 rv mv ⊢
      (wpW (GF := MachGF) (vsaModel live)).W (fun v => iprop(⌜v.1 ≠ 0⌝))

/-- The boot memory's words the evaluation reads outside the state: the
`_bc_rec_mul` cutoff, `stdin`'s lookahead (`.data`) and `interrupt_seen`
(`.bss`), at a memory agreeing with the loaded one off the stack and the
globals and with `.bss` zeroed. -/
theorem boot_words {prog : List Nat} {c : Config} (hld : DcLoaded prog c) {M1 M : Mem}
    (hf : Filled M1 c.σ.mem freeListAddr bssLen (fun _ => 0#8))
    (hout : ∀ a, OutHeap a → ¬ DcGlob a → a < heapStart → imgM M a = imgM M1 a) :
    MulBase dcOwn M ∧ EvGlobs dcOwn M := by
  have own : ∀ a, 0x8001ad10 ≤ a → a < stackTop → dcOwn a := fun a h1 h2 =>
    ⟨by simp only [tohostAddr]; omega, h2⟩
  have hc : ∀ a, 0x8001ad00 ≤ a → a < freeListAddr → ¬ DcGlob a → imgM M a = imgM c.σ.mem a :=
    fun a h1 h2 h3 => by
      have e1 : OutHeap a := by
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at h2 ⊢; omega
      have e2 : a < heapStart := by simp only [freeListAddr, heapStart] at h2 ⊢; omega
      exact (hout a e1 h3 e2).trans (hf.rest a (.inl h2))
  have hb : ∀ a, freeListAddr + 16 ≤ a → a < bcFreeAddr → ¬ DcGlob a → imgM M a = 0#8 :=
    fun a h1 h2 h3 => by
      rw [hout a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at h1 h2 ⊢; omega)
        h3 (by simp only [bcFreeAddr, heapStart] at h2 ⊢; omega)]
      have := hf.fill (a - freeListAddr) (by simp only [bssLen, freeListAddr, heapStart, bcFreeAddr] at h1 h2 ⊢; omega)
      rwa [show freeListAddr + (a - freeListAddr) = a by omega] at this
  refine ⟨⟨fun a h1 h2 => own a (by simp only [mulBaseAddr] at h1; omega)
      (by simp only [mulBaseAddr, stackTop] at h2 ⊢; omega), ?_⟩,
    ⟨fun a h1 h2 => own a (by omega) (by simp only [stackTop]; omega), ?_,
      fun a h1 h2 => own a (by omega) (by simp only [stackTop]; omega), ?_,
      fun a ha => own a (by simp only [InP, inPtrAddr] at ha; omega)
        (by simp only [InP, inPtrAddr, stackTop] at ha ⊢; omega)⟩⟩
  · rw [ldv_congr .lw (Mt := c.σ.mem) fun j hj => hc _ (by simp only [mulBaseAddr]; omega)
      (by simp only [widthOfM, mulBaseAddr, freeListAddr] at hj ⊢; omega)
      (by simp only [widthOfM, DcGlob, mulBaseAddr, dc_addrs] at hj ⊢; omega)]
    refine (hld.ldv_data .lw fun j hj => ?_).trans (by decide)
    simp only [widthOfM, scriptAddr, mulBaseAddr] at hj ⊢; omega
  · exact ldv_zero .lw (.inr rfl) fun j hj => hb _
      (by simp only [freeListAddr]; omega) (by simp only [widthOfM, bcFreeAddr] at hj ⊢; omega)
      (by simp only [widthOfM, DcGlob, dc_addrs] at hj ⊢; omega)
  · rw [ldv_congr .lw (Mt := c.σ.mem) fun j hj => hc _ (by omega)
      (by simp only [widthOfM, freeListAddr] at hj ⊢; omega)
      (by simp only [widthOfM, DcGlob, dc_addrs] at hj ⊢; omega)]
    refine (hld.ldv_data .lw fun j hj => ?_).trans (by decide)
    simp only [widthOfM, scriptAddr] at hj ⊢; omega

/-- **`main`'s call of `dc_evalstr`** on a loaded configuration, to
`evalstr`'s entry: `dc_evalstr`'s frame (`ra` saved at `0x87ffffd8`), the
premises `EvEntryP` at `evSp`/`evW`, nesting `dcD`, leak budget `k`. -/
theorem evcall_boot {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    {prog : List Nat} {c : Config} (hld : DcLoaded prog c) {k : Nat} (hk4 : 4 * k + 9 ≤ 2 ^ 20)
    {M1 : Mem} {R1 R' : Nat → BitVec 64} {M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {b1 b2 : Blk}
    (hf : Filled M1 c.σ.mem freeListAddr bssLen (fun _ => 0#8)) (hr1 : R1 1 = 0x8000003c#64)
    (be : BootEval dcOwn stackTop mainW M1 R1 R' M' H F L C (msObj b1 b2 prog) prog)
    (hk : ∀ (R2 : Nat → BitVec 64) (M2 : Mem), R2 1 = 0x80001920#64 →
      EvEntryP dcOwn evSp evW dcD k 0x87ffffe0 M2 R2 H F L C (bootG [msObj b1 b2 prog])
        [.str b1.pay] [] St.init (msObj b1 b2 prog) →
      ldv .ld M2 0x87ffffd8 = 0x80000b54#64 → ldv .ld M2 0x87fffff8 = 0x8000003c#64 →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn stackTop mainW a → imgM M2 a = imgM M1 a) →
      DWO dcLive dcOwn Q t 0x80001448#64 R2 M2) :
    DWO dcLive dcOwn Q t 0x80001914#64 R' M' := by
  have hlive := dcText_live
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h2 : R' 2 = 0x87ffffe0#64 := be.r2
  dx_run hlive at 0x80001448
  all_goals (try bsimp [h2])
  all_goals first | (simp only [StOK, tohostAddr]; decide) |
    exact stack_acc (by simp [heapEnd]) (by simp [stackTop]) | skip
  have hM : MemOnly (fun a => 0x87ffffd8 ≤ a ∧ a < 0x87ffffe0)
      (writeLog M' [(0x87ffffd8, 8, R' 1)]) M' := fun a ha => by
    simp only [not_and, Nat.not_lt] at ha
    exact imgM_store_miss _ _ (by omega)
  have hpre : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn stackTop mainW a →
      imgM (writeLog M' [(0x87ffffd8, 8, R' 1)]) a = imgM M1 a := fun a e1 e2 e3 =>
    (hM a fun h => e3 (by simp only [frameIn, mainW, stackTop, heapEnd] at h ⊢; omega)).trans
      (be.out a e1 e2 e3)
  obtain ⟨hmb, hgl⟩ := boot_words hld hf (M := writeLog M' [(0x87ffffd8, 8, R' 1)])
    fun a e1 e2 e3 => hpre a e1 e2 fun h => by
      simp only [frameIn, mainW, stackTop, heapEnd, heapStart] at h e3; omega
  have hsb := dc_stack_bound
  refine hk _ _ ?e1 ?en (by rw [ldv_store_hit]; exact be.r1) ?ra hpre
  case e1 => bsimp []
  case en =>
    refine
      { sb := StrBound.init _
        srt := ArrSorted.init
        dc := be.dc.outWrite hM fun a ha => ⟨outHeap_of_ge (by simp [heapEnd]; omega),
          fun hg => by have := hg.lt; simp [heapStart] at this; omega⟩
        strIn := List.mem_singleton_self _
        held := rfl
        slot := ?_
        slotPlace := ⟨fun i hi => ⟨by simp [tohostAddr]; omega, by simp [stackTop]; omega⟩,
          by decide, by decide, by decide⟩
        r2 := by bsimp [h2]
        r10 := by bsimp [be.r10]; rfl
        al := by bsimp []
        frame := stack_own (by decide) (by decide) (by decide)
        room := by decide
        stk := hsb.1
        stkPr := hsb.2.1
        stkDn := hsb.2.2
        budget := by simp [bootG]; omega
        mb := hmb
        err := fun a h1 h2 => ⟨by simp only [errnoAddr, tohostAddr] at h1 ⊢; omega,
          by simp only [errnoAddr, stackTop] at h2 ⊢; omega⟩
        globs := hgl }
    have hd := be.dat
    exact ⟨by rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega)]; exact hd.tag,
      by rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega)]; exact hd.ptr⟩
  case ra =>
    rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega)]
    exact be.ra.trans hr1

end Dc.Mach
