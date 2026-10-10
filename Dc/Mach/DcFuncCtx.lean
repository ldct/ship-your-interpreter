import Dc.Mach.DcFuncExit
import Dc.Mach.DcOutChar
import Dc.Mach.DcBinop
import Dc.Mach.DcArrFree
import Dc.Mach.DcGetnumLoop
import Dc.Semantics

/-!
# `dc_func`'s contract and the state inside its arms (M10)

`dc_func (c, peekc, negcmp)` returns `dcFunc`'s status as a word (`FnOut`:
the `dc_status` code and the state the caller continues with; for `v`,
`dc_func` runs `bc_sqrt` itself and returns `DC_OKAY` with the root pushed).
The lookahead character arrives as `chW`. Its post `FnPost`: the state relation over the caller's handles with
the strings an error route leaked in front (`ex`), at most two more lost
references, the caller's strings kept with their blocks and text
(`StrPin`), and every byte off the heap, the globals, `out_char`'s words and
the frame unchanged. `FnK` is the caller's continuation; `FnAt` the frame
inside an arm (after the dispatch of `DcFuncDisp.lean`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `dc_func`'s result `r` from `st` as the returned code and the state the
caller continues with. -/
inductive FnOut (st : St) : Res → Nat → St → Prop
  | ok (s : St) : FnOut st (.ok s) 0 s
  | eatOne (s : St) : FnOut st (.eatOne s) 1 s
  | evalReg (s : St) (r : Nat) : FnOut st (.evalReg s r) 2 s
  | evalTos (s : St) : FnOut st (.evalTos s) 3 s
  | quit (s : St) : FnOut st (.quit s) 4 s
  | int : FnOut st .int 5 st
  | str : FnOut st .str 6 st
  | system : FnOut st .system 7 st
  | comment : FnOut st .comment 8 st
  | negcmp : FnOut st .negcmp 9 st
  | eofError : FnOut st .eofError 10 st
  | sqrt {s : St} {x y : Num} : Sqrt x s.scale y → FnOut st (.sqrt s x) 0 (s.push (.num y))

/-- **What `dc_func` leaves its caller** (frame `sp`, `W` bytes): the state
over the caller's handles `hs` and the leaked strings `ex`. -/
structure FnPost (S : Nat → Prop) (sp W : Nat) (M : Mem) (G : DcG) (hs : List GV) (M' : Mem)
    (H' : Heap) (F' : List Blk) (L' : List NumObj) (C' : BcConsts) (G' : DcG) (st' : St)
    (ex : List GV) : Prop where
  dc : DcAt S M' H' F' L' C' G' (ex ++ hs) st'
  ex : ex.length ≤ 2
  lk : G'.lk.length ≤ G.lk.length + 2
  pin : StrPin G.strs G'.strs hs
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp W a → imgM M' a = imgM M a

/-- **The caller's continuation** after `dc_func` on `st` returning `r`
(entry registers `R`, memory `M`, frame `W` bytes below `sp`): the console
`t0` followed by the state's output. -/
def FnK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (st : St) (r : Res) (G : DcG) (hs : List GV) (sp W : Nat) (M : Mem)
    (R : Nat → BitVec 64) : Prop :=
  ∀ R' M' H' F' L' C' G' code st' ex, Keeps cClob R' R → R' 2 = R 2 →
    R' 10 = BitVec.ofNat 64 code → FnOut st r code st' →
    FnPost S sp W M G hs M' H' F' L' C' G' st' ex →
    DWO live S Q (t0 ++ Dc.outStr st'.out) (R 1) R' M'

/-- **Inside an arm of `dc_func`**: `sp` lowered by 192, `ra` saved at
`184`, the bytes `FnPost` keeps unchanged since entry (`R0`, `M0`), `s0`–`s11`
kept. -/
structure FnAt (S : Nat → Prop) (sp W : Nat) (M0 : Mem) (R0 : Nat → BitVec 64)
    (R : Nat → BitVec 64) (M : Mem) : Prop where
  frame : StackFrame S sp W
  room : heapEnd + W ≤ sp
  big : 192 ≤ W
  r2 : R 2 = BitVec.ofNat 64 (sp - 192)
  r20 : R0 2 = BitVec.ofNat 64 sp
  ra : ldv .ld M (sp - 192 + 184) = R0 1
  al : (R0 1).toNat % 4 = 0
  keep : Keeps (2 :: cClob) R R0
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp W a → imgM M a = imgM M0 a

/-- The frame with registers changed among the caller-saved ones. -/
theorem FnAt.mod {S : Nat → Prop} {sp W : Nat} {M0 M : Mem} {R0 R R' : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) (k : Keeps cClob R' R) : FnAt S sp W M0 R0 R' M :=
  { hc with
    r2 := (k.get 2 (by decide)).trans hc.r2
    keep := (k.mono (by decide)).trans hc.keep }

/-- The bytes at or above an `sp` over the heap are none of `out_char`'s. -/
theorem not_ocG_of_ge {sp a : Nat} (hh : heapEnd ≤ sp) (ha : sp ≤ a) : ¬ ocG a := by
  simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr, heapEnd] at hh ⊢; omega

/-- A callee's frame below `dc_func`'s. -/
theorem FnAt.cf {S : Nat → Prop} {sp W Wc : Nat} {M0 M : Mem} {R0 R : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) (hW : 192 + Wc ≤ W) : StackFrame S (sp - 192) Wc :=
  hc.frame.within hW (by decide)

theorem FnAt.cab {S : Nat → Prop} {sp W Wc : Nat} {M0 M : Mem} {R0 R : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) (hW : 192 + Wc ≤ W) : heapEnd + Wc ≤ sp - 192 := by
  have := hc.room; omega

/-- **The frame after a callee** at `sp - 192` using `Wc` bytes of stack:
the bytes `FnPost` keeps read as before the call. -/
theorem FnAt.call {S : Nat → Prop} {sp W Wc : Nat} {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) (hW : 192 + Wc ≤ W) (k : Keeps (1 :: 2 :: cClob) R' R)
    (e2 : R' 2 = R 2)
    (hout : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn (sp - 192) Wc a →
      imgM M' a = imgM M a) : FnAt S sp W M0 R0 R' M' := by
  have hh := hc.room
  have hl := hc.frame.lo
  have hab : heapEnd ≤ sp - 192 := by simp only [heapEnd] at hh ⊢; omega
  refine { hc with r2 := e2.trans hc.r2, ra := ?_, keep := ?_, out := ?_ }
  · rw [← hc.ra]
    exact ldv_congr .ld fun j hj => by
      have := above_sp hab (a := sp - 192 + 184 + j) (by omega)
      exact hout _ this.1 this.2.1 (not_ocG_of_ge hab (by omega)) (this.2.2 _)
  · exact (k.mono (by decide)).trans hc.keep
  · intro a e1 e2 e3 e4
    exact (hout a e1 e2 e3 fun hf => e4 (by simp only [frameIn] at hf ⊢; omega)).trans
      (hc.out a e1 e2 e3 e4)

/-- `FnAt.call` for a callee keeping every byte but its frame's off the
heap and the globals (`StkOut`). -/
theorem FnAt.callS {S : Nat → Prop} {sp W Wc : Nat} {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) (hW : 192 + Wc ≤ W) (k : Keeps (1 :: 2 :: cClob) R' R)
    (e2 : R' 2 = R 2) (hout : StkOut (sp - 192) Wc M' M) : FnAt S sp W M0 R0 R' M' :=
  hc.call hW k e2 fun a e1 e2 _ e4 => hout a e1 e2 e4

/-- **The caller's out-of-memory continuation**: `dc_memfail` from any
`sp'` inside `dc_func`'s `W` bytes, the bytes off the heap, the globals,
`out_char`'s words and the frame as at entry. -/
def FnOom (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (sp W : Nat) (M0 : Mem) : Prop :=
  ∀ t' R' M' sp', OomAt S sp W M0 ocG sp' R' M' → DWO live S Q t' 0x80001e74#64 R' M'

/-- **Out of memory inside a callee** at `sp - 192` using `Wc` bytes. -/
theorem FnAt.oom {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {sp W Wc sp' : Nat} {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {t' : String}
    (hc : FnAt S sp W M0 R0 R M) (ho : FnOom live S Q sp W M0) (hW : 192 + Wc ≤ W)
    (hlo : sp - 192 - Wc ≤ sp') (hhi : sp' ≤ sp - 192) (e2 : R' 2 = BitVec.ofNat 64 sp')
    (hout : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn (sp - 192) Wc a →
      imgM M' a = imgM M a) : DWO live S Q t' 0x80001e74#64 R' M' :=
  ho t' R' M' sp' ⟨by omega, by omega, e2, fun a e1 e2' e3 e4 =>
    (hout a e1 e2' e4 fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)).trans
      (hc.out a e1 e2' e4 e3)⟩

/-- **A `jal tgt` at `p`**, as a symbolic step (each site by `bc_run`). -/
def JalAt (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (p tgt : Nat) : Prop :=
  ∀ t R M, (∀ R', Keeps [1] R' R → R' 1 = BitVec.ofNat 64 (p + 4) →
    DWO live S Q t (BitVec.ofNat 64 tgt) R' M) → DWO live S Q t (BitVec.ofNat 64 p) R M

/-- **A `j tgt` at `p`**, as a symbolic step. -/
def JAt (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (p tgt : Nat) : Prop :=
  ∀ t R M, DWO live S Q t (BitVec.ofNat 64 tgt) R M → DWO live S Q t (BitVec.ofNat 64 p) R M

/-- **A `bnez a0, tgt` at `p`**, as a symbolic step. -/
def BnezAt (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (p tgt : Nat) : Prop :=
  ∀ t R M, (R 10 ≠ 0#64 → DWO live S Q t (BitVec.ofNat 64 tgt) R M) →
    (R 10 = 0#64 → DWO live S Q t (BitVec.ofNat 64 (p + 4)) R M) → DWO live S Q t (BitVec.ofNat 64 p) R M

/-- A `jal` site from its generated step `st_<p>`. -/
theorem JalAt.of_step {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {p tgt : Nat}
    (hs : ∀ t R M, DWO live S Q t (BitVec.ofNat 64 tgt) (upd R 1 (BitVec.ofNat 64 (p + 4))) M →
      DWO live S Q t (BitVec.ofNat 64 p) R M) : JalAt live S Q p tgt := fun t R M k =>
  hs t R M (k _ (Keeps.upd _ (by decide) (Keeps.refl _ _)) (by simp [upd]))

/-- A `bnez a0` site from its generated step `st_<p>`. -/
theorem BnezAt.of_step {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {p tgt : Nat}
    (hs : ∀ t R M, (R 10 ≠ 0#64 → DWO live S Q t (BitVec.ofNat 64 tgt) R M) →
      (¬ R 10 ≠ 0#64 → DWO live S Q t (BitVec.ofNat 64 (p + 4)) R M) →
      DWO live S Q t (BitVec.ofNat 64 p) R M) : BnezAt live S Q p tgt := fun t R M k1 k2 =>
  hs t R M k1 fun hn => k2 (Classical.not_not.mp hn)

/-- **An arm's `return code`** (`0x80000c14`, `a0 = code`): the epilogue,
then the caller's continuation. -/
theorem FnAt.close {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {st st' : St} {r : Res} {G G' : DcG}
    {hs ex : List GV} {sp W code : Nat} {M0 M : Mem} {R0 R : Nat → BitVec 64} {H' : Heap}
    {F' : List Blk} {L' : List NumObj} {C' : BcConsts}
    (hc : FnAt S sp W M0 R0 R M) (hk : FnK live S Q t0 st r G hs sp W M0 R0)
    (hf : FnOut st r code st') (h : DcAt S M H' F' L' C' G' (ex ++ hs) st') (hex : ex.length ≤ 2)
    (hlk : G'.lk.length ≤ G.lk.length + 2) (hpin : StrPin G.strs G'.strs hs)
    (h10 : R 10 = BitVec.ofNat 64 code) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000c14#64 R M := by
  have hsf : StackFrame S sp 192 := hc.frame.mono (by have := hc.big; omega)
  refine fn_epi hlive hsf (by have := hc.room; have := hc.big; omega) R hc.r2 hc.ra hc.al
    fun R' k e1 e2 => ?_
  refine hk R' M H' F' L' C' G' code st' ex ?_ (e2.trans hc.r20.symm) ?_ hf
    ⟨h, hex, hlk, hpin, hc.out⟩
  · refine Keeps.restoreAll (rs := [1, 2]) ((k.mono (ks' := [1, 2] ++ cClob) (by decide)).trans
      (hc.keep.mono (by decide))) fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact e1
    · exact e2.trans hc.r20.symm
  · rw [k.get 10 (by decide)]; exact h10

end Dc.Mach
