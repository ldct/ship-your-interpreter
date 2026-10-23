import Dc.Mach.HaltsLoaded
import Dc.Mach.EvalBase

/-!
# From `evalstr`'s return to `_exit` (M11)

```
80001920 beqz a0,80001930 ; li a5,4 ; beq a0,a5,8000193c ; li a0,2
80001930 ld ra,8(sp) ; addi sp,sp,16 ; ret                      (dc_evalstr)
8000193c lw a0,unwind_noexit ; ld ra,8(sp) ; addi a0,a0,-1 ; snez a0,a0 ; slliw a0,a0,1 ; ...
80000b54 bnez a0,80000b60 ; addi a0,sp,8 ; jal dc_free_str     (main)
80000b60 jal flush_okay ; ld ra,24(sp) ; addi sp,sp,32 ; ret
8000003c j exit                                                   (_start)
```

`main_ret`: from `main` after `dc_evalstr` (any status in `a0`) through
`dc_free_str` (status `0`) or not, `flush_okay` (status `0`), `main`'s
return to `_start` and `exit (0)`: the run ends at `_exit`'s store with the
exit word of `0` and the console unchanged (`ExitQ`). `evstr_ret`: the same
from `dc_evalstr`'s return point after `evalstr` (`EvPost`), the shape of
`EvalstrSpec`'s continuation `EvK`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `dcOwn` owns the stack. -/
theorem stack_own {sp n : Nat} (h1 : heapEnd + n ≤ sp) (h2 : sp ≤ stackTop) (hal : sp % 16 = 0) :
    StackFrame dcOwn sp n :=
  ⟨fun a e1 e2 => ⟨by simp only [heapEnd, tohostAddr] at h1 ⊢; omega, by omega⟩,
    by simp only [heapEnd, tohostAddr] at h1 ⊢; omega, by simp only [stackTop] at h2; omega, hal⟩

/-- An access `dcOwn` owns. -/
theorem own_acc {a w : Nat} (h1 : tohostAddr + 16 ≤ a) (h2 : a + w ≤ stackTop) :
    ∀ b ∈ accAddrs a w, dcOwn b :=
  fun b hb => by
    have := of_mem_accAddrs hb
    simp only [dcOwn, tohostAddr, stackTop] at h1 h2 ⊢; omega

/-- A stack access `dcOwn` owns. -/
theorem stack_acc {a w : Nat} (h1 : heapEnd ≤ a) (h2 : a + w ≤ stackTop) : ∀ b ∈ accAddrs a w, dcOwn b :=
  own_acc (by simp only [heapEnd, tohostAddr] at h1 ⊢; omega) h2

/-- **`main` after `dc_evalstr`** (`0x80000b54`, `sp = 0x87ffffe0`,
`main`'s `ra` at `0x87fffff8`): to `_exit`'s store with status `0`. -/
theorem main_ret {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV}
    {st : St} {p : Nat}
    (h : DcAt dcOwn M H F L C G (.str p :: hs) st)
    (hslot : ldv .ld M 0x87ffffe8 = BitVec.ofNat 64 p)
    (hra : ldv .ld M 0x87fffff8 = 0x8000003c#64) (R : Nat → BitVec 64)
    (h2 : R 2 = 0x87ffffe0#64)
    (hq : ∀ R' M', R' VsaIris.PC = BitVec.ofNat 64 exitSite.pc → R' 14 = exitSite.base →
      R' 15 = exitWord 0#64 → Q t R' M') :
    DWO dcLive dcOwn Q t 0x80000b54#64 R M := by
  have hlive := dcText_live
  have htx : tohostAddr = 0x8001ad00 := rfl
  -- the exit from `main`'s return
  have hexit : ∀ (R1 : Nat → BitVec 64) (M1 : Mem), R1 2 = 0x87ffffe0#64 →
      R1 10 = 0#64 → ldv .ld M1 0x87fffff8 = 0x8000003c#64 →
      DWO dcLive dcOwn Q t 0x80000b64#64 R1 M1 := fun R1 M1 e2 e10 e8 => by
    dx_run hlive at 0x8000003c
    all_goals (try bsimp [e2, e8])
    all_goals first | (simp only [LdOK, tohostAddr]; omega) |
      exact stack_acc (by simp [heapEnd]) (by simp [stackTop]) | (try decide) | skip
    refine start_exit dcText_live (stack_own (sp := stackTop) (by simp [heapEnd, stackTop])
      (Nat.le_refl _) (by decide)) _ ?_ fun R' M' e15 e14 => swpo_done fun rv mv hm => hq rv mv hm.pc ?_ ?_
    · bsimp [e2]
    · rw [hm.regs 14 (by decide) (by decide)]; exact e14
    · rw [hm.regs 15 (by decide) (by decide), e15]; bsimp [e10]; rfl
  -- `flush_okay` then the exit
  have hflush : ∀ (R1 : Nat → BitVec 64) (M1 : Mem), R1 2 = 0x87ffffe0#64 →
      ldv .ld M1 0x87fffff8 = 0x8000003c#64 → DWO dcLive dcOwn Q t 0x80000b60#64 R1 M1 :=
    fun R1 M1 e2 e8 => by
      dx_run hlive at 0x80000ab0
      refine flush_okay_spec dcText_live (stack_own (sp := 0x87ffffe0) (n := 16)
        (by simp [heapEnd]) (by simp [stackTop]) (by decide)) _ (by bsimp [e2])
        (by bsimp []) fun R2 M2 k2 e2' e10 hfr => ?_
      bsimp []
      refine hexit R2 M2 (by rw [e2']; bsimp [e2]) e10 ?_
      rw [ldv_congr .ld fun j hj => hfr _ (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
      exact e8
  apply st_80000b54 dcText_live
  · intro _
    exact hflush R M h2 hra
  · intro hz
    dx_run dcText_live at 0x800039a4
    all_goals (try bsimp [h2])
    refine dc_free_str_spec dcText_live (h.perm (List.Perm.refl _)) (q := 0x87ffffe8)
      ⟨fun i hi => ⟨by simp [tohostAddr]; omega, by simp [stackTop]; omega⟩, by decide,
        by simp [tohostAddr], by decide⟩ hslot
      (stack_own (sp := 0x87ffffe0) (by simp [heapEnd]) (by simp [stackTop]) (by decide))
      (by simp [heapEnd]) _ (by bsimp [h2]) (by bsimp [h2]) (by bsimp [])
      fun R2 M2 H2 G2 k2 _ _ hso _ => ?_
    bsimp []
    refine hflush R2 M2 (by rw [k2.get 2 (by decide)]; bsimp [h2]) ?_
    rw [ldv_congr .ld fun j hj => hso _ (outHeap_of_ge (by simp [heapEnd]; omega))
      (fun hg => by have := hg.1.lt; simp [heapStart] at this; omega)
      (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
    exact hra

/-- **After `evalstr` returns into `dc_evalstr`** (`0x80001920`, `sp =
0x87ffffd0`, `a0` the status, the string datum at `0x87ffffe0` in `main`'s
frame): `dc_evalstr`'s status mapping, `main`'s tail, `exit (0)`. -/
theorem evstr_ret {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {xs : List GV}
    {st : St} {p : Nat} {r : Status}
    (h : DcAt dcOwn M H F L C G (xs ++ [.str p]) st)
    (hslot : DatAt M 0x87ffffe0 (.str p))
    (hra1 : ldv .ld M 0x87ffffd8 = 0x80000b54#64)
    (hra : ldv .ld M 0x87fffff8 = 0x8000003c#64) (R : Nat → BitVec 64)
    (h2 : R 2 = 0x87ffffd0#64) (h10 : R 10 = statusWord r)
    (hq : ∀ R' M', R' VsaIris.PC = BitVec.ofNat 64 exitSite.pc → R' 14 = exitSite.base →
      R' 15 = exitWord 0#64 → Q t R' M') :
    DWO dcLive dcOwn Q t 0x80001920#64 R M := by
  have hlive := dcText_live
  have h' : DcAt dcOwn M H F L C G (.str p :: xs) st := h.perm (List.perm_append_singleton _ _)
  have hp8 : ldv .ld M 0x87ffffe8 = BitVec.ofNat 64 p := hslot.ptr
  have hret : ∀ R1 : Nat → BitVec 64, R1 2 = 0x87ffffe0#64 → DWO dcLive dcOwn Q t 0x80000b54#64 R1 M :=
    fun R1 e2 => main_ret h' hp8 hra R1 e2 hq
  cases r with
  | ok =>
    refine st_80001920 dcText_live (fun _ => ?_) (fun hne => absurd h10 hne)
    dx_run hlive at 0x80000b54
    all_goals (try bsimp [h2, hra1])
    all_goals first | (simp only [LdOK, tohostAddr]; omega) |
      exact stack_acc (by simp [heapEnd]) (by simp [stackTop]) | (try decide) | skip
    exact hret _ (by bsimp [h2])
  | quit =>
    refine st_80001920 dcText_live (fun e => absurd (h10.symm.trans e) (by decide)) (fun _ => ?_)
    dx_run hlive at 0x80001928
    refine st_80001928 dcText_live (fun _ => ?_) (fun hne => absurd (by bsimp [h10]; rfl) hne)
    dx_run hlive at 0x80001940
    refine st_80001940 dcText_live (by bsimp []; simp only [LdOK, tohostAddr]; omega)
      (by bsimp []; exact own_acc (by simp [tohostAddr]) (by simp [stackTop])) ?_
    dx_run hlive at 0x80000b54
    all_goals (try bsimp [h2, hra1])
    all_goals first | (simp only [LdOK, tohostAddr]; omega) |
      exact own_acc (by simp [tohostAddr]) (by simp [stackTop]) | skip
    exact hret _ (by bsimp [h2])

end Dc.Mach
