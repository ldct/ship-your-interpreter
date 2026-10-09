import Dc.Mach.Bc.CallFrame
import Dc.Mach.Bc.RaiseModEntry
import Dc.Mach.Bc.FreeSites
import Dc.BcModel.Sqrt
import Dc.Semantics

/-!
# `bc_sqrt`'s contract and state (`lib/number.c`, `0x80006a1c`)

    bc_sqrt (num, scale):
      cmp (*num, _zero_) < 0: return 0;  = 0: *num = copy (_zero_), return 1
      cmp (*num, _one_) = 0: *num = copy (_one_), return 1
      rscale = MAX (scale, (*num)->n_scale); guess = guess1 = diff = copy (_zero_)
      point5 = 0.5
      *num < 1: guess = copy (_one_), cscale = (*num)->n_scale   (leaks a `_zero_`)
      *num > 1: guess = 10 ^ (n_len / 2), cscale = 3
      loop: free guess1; guess1 = copy (guess)
            guess = (*num / guess at cscale + guess1) * 0.5 at cscale
            diff = guess - guess1 at cscale + 1
            near zero at cscale: cscale < rscale + 1 ? cscale = MIN (3 cscale, rscale + 1) : done
      free *num; *num = guess / 1 at rscale; free guess, guess1, point5, diff; return 1

The 160-byte frame holds `&_one_` at `+8`, `guess` at `+24`, the first
`guess1` at `+32` and `diff` at `+40`; in the loop `guess1` is `s10`. The
loop's numbers are the handles `[point5, diff, guess] ++ guess1` of `RList`
over the caller's heap with the leaked `_zero_` reference (`SqLeak`).

- `SqCtx`/`SqArgs`: the frame and the operand `x` in the slot `q`.
- `SqOut`: the result as `dc` describes it (`Dc.Sqrt` for `x > 0`, `x ≠ 1`).
- `SqPost`/`SqK`: the result in the slot, `0` for a negative `x`, or
  `out_of_memory`.
- `SqAt`: inside the frame.
- `RList.binPost`: a callee's new number for a handle's slot; `sq_mulH`,
  `sq_addH`, `sq_subH`: the callees on handles; `sq_divH`: `guess1 = copy
  (guess)` and the quotient into `guess`'s slot.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `bc_sqrt`'s context: a caller's window with room for its 160-byte frame
and `bc_raise` below it, the result slot `q` off the heap and apart from the
window and `_zero_`'s global. -/
structure SqCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp W q : Nat) : Prop where
  cc : CallerCtx S sp W
  big : 160 + 512 + rmStack (2 ^ 30) ≤ W
  far : stderrAddr + 4 ≤ sp - W
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0
  slot : DmSlot S sp W q
  slotZero : q + 8 ≤ zeroAddr ∨ zeroAddr + 8 ≤ q

/-- The facts of `SqCtx` the steps use, as `omega` sees them. -/
macro "sq_facts " cx:term : tactic =>
  `(tactic| (cf_facts ($cx).cc
             have _hW := ($cx).big
             have _hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega))

/-- The operand `x` of the caller's heap `L` in the slot `q`, `_zero_` (`z`)
and `_one_` (`o`) in `L` at their globals, sizes small enough for the
callees, room for four more references to each number, the stderr stream. -/
structure SqArgs (S : Nat → Prop) (M : Mem) (L : List NumObj) (x z o : NumObj) (q k : Nat) :
    Prop where
  mx : x ∈ L
  nx : x.rep.Norm
  lenx : 1 ≤ x.rep.len
  rx : 1 ≤ x.rep.refs
  wx : ldv .ld M q = BitVec.ofNat 64 x.rep.p
  mz : z ∈ L
  mo : o ∈ L
  size : x.rep.len + x.rep.scale + k < 2 ^ 20
  refs : ∀ y ∈ L, y.rep.refs + 4 < 2 ^ 31
  zero : KZero M z (2 ^ 30 + 4)
  one : ldv .ld M oneAddr = BitVec.ofNat 64 o.rep.p
  oneNum : o.rep.num = Num.one
  oneNorm : o.rep.Norm
  oneLen : 1 ≤ o.rep.len
  mulBase : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80
  owns : ∀ y ∈ L, y.Owns
  fd : FdAt S M stderrAddr 2

/-- What `dc` takes `v` of `x` at scale `k` to: nothing for a negative `x`
(`bc_sqrt` returns `0`), `0`, `1`, or the Newton iteration's result. -/
inductive SqOut (x : Num) (k : Nat) : Option Num → Prop
  | neg : Num.cmp x (Num.zero 0) = .lt → SqOut x k none
  | zero : Num.cmp x (Num.zero 0) = .eq → SqOut x k (some (Num.zero 0))
  | one : Num.cmp x (Num.zero 0) = .gt → Num.cmp x Num.one = .eq → SqOut x k (some Num.one)
  | root {r : Num} : Num.cmp x (Num.zero 0) = .gt → Num.cmp x Num.one ≠ .eq → Sqrt x k r →
      SqOut x k (some r)

/-- `L'` is `L`, or `L` with the reference to `_zero_` that `bc_sqrt` leaks
for `0 < x < 1`. -/
def SqLeak (L : List NumObj) (z : NumObj) (L' : List NumObj) : Prop :=
  L' = L ∨ ∃ A B, L = A ++ z :: B ∧ L' = A ++ z.withRefs (z.rep.refs + 1) :: B

/-- The result `y` for `n` in the slot `q`: the leak, `x` dropped, a
reference to `y` added. Off the heap only the slot and the window changed. -/
structure SqPost (S : Nat → Prop) (Mt0 Mt : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (x z : NumObj) (q sp W : Nat) (n : Num) (Lf : List NumObj) (y : NumObj) : Prop where
  heap : BcHeap S Mt H F Lf
  mid : ∃ Lw Ld, SqLeak L z Lw ∧ DropAt Lw x.rep.p Ld ∧ AddRef Ld y Lf
  num : y.rep.num = n
  norm : y.rep.Norm
  pos : 1 ≤ y.rep.len
  owns : y.Owns
  slot : ldv .ld Mt q = BitVec.ofNat 64 y.rep.p
  out : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM Mt a = imgM Mt0 a

/-- `bc_sqrt`'s continuations: the result and `1`, `0` with nothing changed
but the window (a negative `x`), or `out_of_memory`. -/
structure SqK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t : String) (R0 : Nat → BitVec 64) (Mt0 : Mem) (L : List NumObj) (x z : NumObj)
    (q sp W : Nat) (n : Option Num) : Prop where
  ret : ∀ r, n = some r → ∀ R' Mt' H F Lf y, Keeps binClob R' R0 → R' 10 = 1#64 →
    SqPost S Mt0 Mt' H F L x z q sp W r Lf y → DWO live S Q t (R0 1) R' Mt'
  fail : n = none → ∀ R' Mt', Keeps binClob R' R0 → R' 10 = 0#64 →
    (∀ a, ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) → DWO live S Q t (R0 1) R' Mt'
  oom : RaOom live S (DQ live S Q t) Mt0 sp W q

/-! ## Inside `bc_sqrt` -/

/-- The registers `bc_sqrt` changes before its epilogue. -/
abbrev sqAll : List Nat :=
  [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31]

/-- The prologue's saved registers (`s2`, `s1`, `s10`, `s0`, `s3`, `s4`,
`ra`, `s8`). -/
abbrev sqSlots0 : List (Nat × Nat) :=
  [(24, 80), (1, 152), (20, 112), (19, 120), (8, 144), (26, 64), (9, 136), (18, 128)]

/-- With `s5`, `s6`, `s7`, `s9`, `s11` saved too. -/
abbrev sqSlots1 : List (Nat × Nat) :=
  [(27, 56), (25, 72), (23, 88), (22, 96), (21, 104), (24, 80), (1, 152), (20, 112), (19, 120),
    (8, 144), (26, 64), (9, 136), (18, 128)]

/-- Inside `bc_sqrt`: `sp` lowered by 160, the saved registers in the
frame, and off the heap only the window and the slot changed. -/
structure SqAt (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (slots : List (Nat × Nat)) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 160)
  saved : SavedWords M (sp - 160) slots R0
  keep : Keeps sqAll R R0
  out : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a

/-- Through a call that changes the registers of `raCallClob`, the heap, the
frame's first 48 bytes and the bytes below the frame. -/
theorem SqAt.call {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    {sp W q : Nat} {slots : List (Nat × Nat)} (h : SqAt S Mt0 M R0 R sp W q slots)
    (hlo : ∀ p ∈ slots, 48 ≤ p.2 := by decide) (htop : ∀ p ∈ slots, p.2 + 8 ≤ 160 := by decide)
    (hsp : 160 ≤ sp) (hW : 160 ≤ W)
    (hkp : Keeps raCallClob R' R)
    (hag : ∀ a, OutHeap a → ¬ (sp - 160 ≤ a ∧ a < sp - 112) → ¬ frameIn (sp - 160) (W - 160) a →
      imgM M' a = imgM M a)
    (hst : ∀ a, sp - 112 ≤ a → a < sp → OutHeap a) :
    SqAt S Mt0 M' R0 R' sp W q slots where
  r2 := by rw [hkp.get 2]; exact h.r2
  saved := h.saved.transport hlo htop fun a h1 h2 =>
    hag a (hst a (by omega) (by omega)) (by omega) (by simp only [frameIn]; omega)
  keep := (hkp.mono (by decide)).trans h.keep
  out := fun a ha hs hf => by
    rw [hag a ha (fun h' => hf (by simp only [frameIn]; omega))
      (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
    exact h.out a ha hs hf

/-- Through a change of registers outside the saved ones. -/
theorem SqAt.regs {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {slots : List (Nat × Nat)} (h : SqAt S Mt0 M R0 R sp W q slots) {ks : List Nat}
    (hk : Keeps ks R' R) (hks : ∀ z ∈ ks, z ∈ sqAll ∧ z ≠ 2 := by decide) :
    SqAt S Mt0 M R0 R' sp W q slots :=
  { h with
    r2 := by rw [hk.get 2 fun hm => (hks 2 hm).2 rfl]; exact h.r2
    keep := (hk.mono fun z hz => (hks z hz).1).trans h.keep }

/-- Through a change of the heap alone. -/
theorem SqAt.heap {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {slots : List (Nat × Nat)} (cx : SqCtx S R0 sp W q) (h : SqAt S Mt0 M R0 R sp W q slots)
    (hlo : ∀ p ∈ slots, 48 ≤ p.2 := by decide) (htop : ∀ p ∈ slots, p.2 + 8 ≤ 160 := by decide)
    (hag : ∀ a, OutHeap a → imgM M' a = imgM M a) : SqAt S Mt0 M' R0 R sp W q slots := by
  sq_facts cx
  exact
    { h with
      saved := h.saved.transport hlo htop fun a h1 h2 =>
        hag a (outHeap_of_ge (by simp only [heapEnd]; omega))
      out := fun a ha hs hf => (hag a ha).trans (h.out a ha hs hf) }

/-- A word of the frame's first 48 bytes a callee leaves. -/
theorem sq_word {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp W q : Nat} {M M' : Mem}
    (cx : SqCtx S R0 sp W q) {o : Nat} (ho : o ≤ 40)
    (hag : ∀ a, OutHeap a → sp - 160 + o ≤ a → a < sp - 160 + o + 8 → imgM M' a = imgM M a) :
    ldv .ld M' (sp - 160 + o) = ldv .ld M (sp - 160 + o) := by
  sq_facts cx
  exact ldv_congr .ld fun j hj => hag _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))
    (by omega) (by simp only [widthOfM] at hj; omega)

/-- A word of the frame's first 48 bytes as a callee's result slot. -/
theorem SqCtx.fslot {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp W q : Nat} (cx : SqCtx S R0 sp W q)
    {o : Nat} (ho : o + 8 ≤ 48) (ho8 : o % 8 = 0) :
    DmSlot S (sp - 160) (W - 160) (sp - 160 + o) := by
  sq_facts cx
  exact cx.cc.slot (by omega) (by omega) ho8 (by omega)

/-- `out_of_memory` with the frame's words changed too. -/
theorem SqCtx.oomF {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {R0 : Nat → BitVec 64} {Mt0 M : Mem} {sp W q : Nat} (cx : SqCtx S R0 sp W q)
    (h : RaOom live S Q Mt0 sp W q)
    (houtM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    ∀ R' Mt' sp', sp - W ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
      (∀ a, OutHeap a → ¬ frameIn sp W a → imgM Mt' a = imgM M a) →
      DW live S Q 0x80002bcc#64 R' Mt' := fun R' Mt' sp' h1 h2 hr2 hout =>
  h R' Mt' sp' h1 h2 hr2 fun a ha hs hf => (hout a ha hf).trans (houtM a ha hs hf)

/-- `out_of_memory` from a callee of `bc_sqrt`'s frame. -/
theorem SqCtx.oom {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {R0 : Nat → BitVec 64} {Mt0 M : Mem} {sp W q : Nat} (cx : SqCtx S R0 sp W q)
    (h : RaOom live S Q Mt0 sp W q)
    (houtM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    ∀ R' Mt' sp', sp - 160 - (W - 160) ≤ sp' → sp' ≤ sp - 160 → R' 2 = BitVec.ofNat 64 sp' →
      (∀ a, OutHeap a → ¬ frameIn (sp - 160) (W - 160) a → imgM Mt' a = imgM M a) →
      DW live S Q 0x80002bcc#64 R' Mt' := by
  sq_facts cx
  have hap := cx.slot.apart
  intro R' Mt' sp' h1 h2 hr2 hout
  refine h R' Mt' sp' (by omega) (by omega) hr2 fun a ha hs hf => ?_
  rw [hout a ha (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
  exact houtM a ha hs hf

/-! ## The callees on handles -/

/-- **A callee's new number for a handle's slot**: the heap with the handle
replaced, and the number in the slot. -/
theorem RList.binPost {S : Nat → Prop} {Mt0 M : Mem} {H : Heap} {F : List Blk} {hs1 hs2 : List RH}
    {h : RH} {L L1 L2 L' : List NumObj} {x y : NumObj} {q sp W : Nat} {n : Num}
    (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hfr : ∀ L', FreedRest L1 L2 x L' → L' = RList (hs1 ++ hs2) L)
    (hp : BinPostW S Mt0 M H F L1 L2 x q sp W n L' y) :
    BcHeap S M H F (RList (hs1 ++ .own y :: hs2) L) ∧ MulRes M q n y ∧
      RHOwn (hs1 ++ .own y :: hs2) L := by
  have hyp : y.rep.p = y.sb.pay := (hp.heap.blocks y List.mem_cons_self).sPay
  exact ⟨RList.replace hown hp.owns hp.heap (hfr L' hp.rest),
    ⟨⟨hp.num, hp.norm, hp.pos, hp.refs, hp.owns⟩, by rw [hp.slot, hyp]⟩, hown.set hp.owns⟩

/-- The callee's window off `bc_sqrt`'s frame. -/
theorem SqCtx.outM {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp W q o : Nat} {M M' : Mem}
    (cx : SqCtx S R0 sp W q) (ho : o + 8 ≤ 48)
    (h : ∀ a, OutHeap a → ¬ slotBytes (sp - 160 + o) a → ¬ frameIn (sp - 160) (W - 160) a →
      imgM M' a = imgM M a) :
    ∀ a, OutHeap a → ¬ (sp - 160 ≤ a ∧ a < sp - 112) → ¬ frameIn (sp - 160) (W - 160) a →
      imgM M' a = imgM M a := by
  sq_facts cx
  exact fun a h1 h2 h3 => h a h1 (by simp only [slotBytes]; omega) h3

/-- **`bc_multiply (u1, u2, &h, k)`** on the handle `h` of `bc_sqrt` (its
word at `sp - 160 + o`): the product replaces it. -/
theorem sq_mulH {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o k : Nat}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {u1 u2 z : NumObj} {H : Heap}
    {F : List Blk}
    (cx : SqCtx S R0 sp W q) (hoom : RaOom live S Q Mt0 sp W q) (ho : o + 8 ≤ 48) (ho8 : o % 8 = 0)
    (houtM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h) (ha : MulArgs M (RList (hs1 ++ h :: hs2) L) u1 u2 z k)
    (hw : ldv .ld M (sp - 160 + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 160)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 160 + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ R' M' H' F' y, Keeps binClob R' R →
      BcHeap S M' H' F' (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      MulRes M' (sp - 160 + o) (Num.mul u1.rep.num u2.rep.num k) y →
      (∀ a, OutHeap a → ¬ (sp - 160 ≤ a ∧ a < sp - 112) → ¬ frameIn (sp - 160) (W - 160) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000573c#64 R M := by
  sq_facts cx
  obtain ⟨L1, L2, x, e, hp, hr1, hnv, _, _, hfr⟩ := RList.slot hb hh hown
  rw [e] at hb ha
  have hsz := ha.size
  have hrs := rmStack_mono (show u1.rep.len + u1.rep.scale + (u2.rep.len + u2.rep.scale) ≤ 2 ^ 30
    by omega)
  refine bc_multiply_spec hlive (cx.cc.mul (F := 160) (by omega) (by omega) (cx.fslot ho ho8) h2 hal)
    ha (by omega) hb ⟨hr1, by rw [hw, hp], hnv⟩ h10 h11 h12 h13
    ⟨fun R' M' H' F' L' y hk hp' => ?_, cx.oom hoom houtM⟩
  obtain ⟨hb', hres, hown'⟩ := RList.binPost hown hfr hp'
  exact hret R' M' H' F' y hk hb' hown' hres (cx.outM ho hp'.out)

/-- A `BinK` from a handle's slot (`bc_add`, `bc_sub`). -/
theorem sq_binK {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o : Nat}
    {hs1 hs2 : List RH} {h : RH} {L L1 L2 : List NumObj} {x : NumObj} {n : Num}
    (cx : SqCtx S R0 sp W q) (hoom : RaOom live S Q Mt0 sp W q) (ho : o + 8 ≤ 48)
    (houtM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hfr : ∀ L', FreedRest L1 L2 x L' → L' = RList (hs1 ++ hs2) L)
    (hret : ∀ R' M' H' F' y, Keeps binClob R' R →
      BcHeap S M' H' F' (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      MulRes M' (sp - 160 + o) n y →
      (∀ a, OutHeap a → ¬ (sp - 160 ≤ a ∧ a < sp - 112) → ¬ frameIn (sp - 160) (W - 160) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    BinK live S Q R M L1 L2 x (sp - 160 + o) (sp - 160) n := by
  sq_facts cx
  refine ⟨fun R' M' H' F' L' y hk hp' => ?_, fun R' M' sp' h1 h2 hr2 hout =>
    cx.oom hoom houtM R' M' sp' (by omega) (by omega) hr2 fun a ha hf =>
      hout a ha fun h' => hf (by simp only [frameIn] at h' ⊢; omega)⟩
  obtain ⟨hb', hres, hown'⟩ := RList.binPost hown hfr hp'
  exact hret R' M' H' F' y hk hb' hown' hres fun a h1 h2 h3 =>
    hp'.out a h1 (by simp only [slotBytes]; omega) fun h' => h3 (by simp only [frameIn] at h' ⊢; omega)

/-- **`bc_add (u1, u2, &h, k)`** on the handle `h` of `bc_sqrt`: the sum
replaces it. -/
theorem sq_addH {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o k : Nat}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {u1 u2 : NumObj} {H : Heap}
    {F : List Blk}
    (cx : SqCtx S R0 sp W q) (hoom : RaOom live S Q Mt0 sp W q) (ho : o + 8 ≤ 48) (ho8 : o % 8 = 0)
    (houtM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h) (ha : BinArgs (RList (hs1 ++ h :: hs2) L) u1 u2 k)
    (hl1 : 1 ≤ u1.rep.len) (hl2 : 1 ≤ u2.rep.len)
    (hw : ldv .ld M (sp - 160 + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 160)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 160 + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ R' M' H' F' y, Keeps binClob R' R →
      BcHeap S M' H' F' (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      MulRes M' (sp - 160 + o) (Num.add u1.rep.num u2.rep.num k) y →
      (∀ a, OutHeap a → ¬ (sp - 160 ≤ a ∧ a < sp - 112) → ¬ frameIn (sp - 160) (W - 160) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x80005634#64 R M := by
  sq_facts cx
  obtain ⟨L1, L2, x, e, hp, hr1, hnv, _, _, hfr⟩ := RList.slot hb hh hown
  rw [e] at hb ha
  exact bc_add_spec hlive (cx.cc.bin (F := 160) (by omega) (by omega) (cx.fslot ho ho8) h2 hal) ha
    (fun _ => ⟨hl1, hl2⟩) hb ⟨hr1, by rw [hw, hp], hnv⟩ h10 h11 h12 h13
    (sq_binK cx hoom ho houtM hown hfr hret)

/-- **`bc_sub (u1, u2, &h, k)`** on the handle `h` of `bc_sqrt`: the
difference replaces it. -/
theorem sq_subH {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o k : Nat}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {u1 u2 : NumObj} {H : Heap}
    {F : List Blk}
    (cx : SqCtx S R0 sp W q) (hoom : RaOom live S Q Mt0 sp W q) (ho : o + 8 ≤ 48) (ho8 : o % 8 = 0)
    (houtM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h) (ha : BinArgs (RList (hs1 ++ h :: hs2) L) u1 u2 k)
    (hl1 : 1 ≤ u1.rep.len) (hl2 : 1 ≤ u2.rep.len)
    (hw : ldv .ld M (sp - 160 + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 160)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 160 + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ R' M' H' F' y, Keeps binClob R' R →
      BcHeap S M' H' F' (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      MulRes M' (sp - 160 + o) (Num.sub u1.rep.num u2.rep.num k) y →
      (∀ a, OutHeap a → ¬ (sp - 160 ≤ a ∧ a < sp - 112) → ¬ frameIn (sp - 160) (W - 160) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x80004ac4#64 R M := by
  sq_facts cx
  obtain ⟨L1, L2, x, e, hp, hr1, hnv, _, _, hfr⟩ := RList.slot hb hh hown
  rw [e] at hb ha
  exact bc_sub_spec hlive (cx.cc.bin (F := 160) (by omega) (by omega) (cx.fslot ho ho8) h2 hal) ha
    (fun _ => ⟨hl1, hl2⟩) hb ⟨hr1, by rw [hw, hp], hnv⟩ h10 h11 h12 h13
    (sq_binK cx hoom ho houtM hown hfr hret)

/-- A member of a list other than `x` stays through a change of `x`'s count. -/
theorem mem_set_of_ne {L1 L2 : List NumObj} {x x' u : NumObj} (hu : u ∈ L1 ++ x :: L2) (hne : u ≠ x) :
    u ∈ L1 ++ x' :: L2 := by
  simp only [List.mem_append, List.mem_cons] at hu ⊢
  rcases hu with h | h | h
  · exact .inl h
  · exact absurd h hne
  · exact .inr (.inr h)

/-- **`guess1 = copy (guess)`, then `bc_divide (u, guess, &guess, k)`** on
the handles `[point5, diff, guess]` (`guess`'s word at `sp - 160 + 24`), a
nonzero `guess`: the quotient becomes `guess` and the old `guess` is
`guess1`, `[point5, diff, quotient, guess1]`. The memory `M` is `M0` with
`guess`'s count raised. -/
theorem sq_divH {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M0 : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat}
    {P D G : RH} {L : List NumObj} {u z : NumObj} {H : Heap} {F : List Blk}
    (cx : SqCtx S R0 sp W q) (hoom : RaOom live S Q Mt0 sp W q)
    (houtM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M0 a = imgM Mt0 a)
    (hb : BcHeap S M0 H F (RList [P, D, G] L)) (hown : RHOwn [P, D, G] L) (hG : RHOK L G)
    (hroom : (RH.obj [P, D, G] G).rep.refs + 1 < 2 ^ 31)
    (hu : u ∈ RList [P, D, G] L) (huG : u.rep.p ≠ G.p) (hz : z ∈ RList [P, D, G] L)
    (hzG : z.rep.p ≠ G.p)
    (hsz : u.rep.len + u.rep.scale + k + G.base.rep.len + G.base.rep.scale < 2 ^ 27)
    (hzg : ldv .ld M0 zeroAddr = BitVec.ofNat 64 z.rep.p) (hzm : z.rep.num.mag = 0)
    (hl1 : 1 ≤ u.rep.len) (hgm : G.base.rep.num.mag ≠ 0)
    (hw : ldv .ld M0 (sp - 160 + 24) = BitVec.ofNat 64 G.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 160)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u.rep.p) (h11 : R 11 = BitVec.ofNat 64 G.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 160 + 24)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ m, Num.div u.rep.num G.base.rep.num k = some m → ∀ R' M' H' F' y,
      Keeps binClob R' R → R' 10 = 0#64 →
      BcHeap S M' H' F' (RList [P, D, .own y, G] L) → RHOwn [P, D, .own y, G] L →
      MulRes M' (sp - 160 + 24) m y →
      (∀ a, OutHeap a → ¬ (sp - 160 ≤ a ∧ a < sp - 112) → ¬ frameIn (sp - 160) (W - 160) a →
        imgM M' a = imgM M0 a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000589c#64 R
      (writeLog M0 [(G.p + 12, 4, BitVec.ofNat 64 ((RH.obj [P, D, G] G).rep.refs + 1))]) := by
  sq_facts cx
  obtain ⟨L1, L2, x, e, hp, hr1, _, _, hxo, _⟩ := RList.slot (hs1 := [P, D]) (hs2 := []) hb hG hown
  subst hxo
  have e' : RList [P, D, G] L = L1 ++ RH.obj [P, D, G] G :: L2 := e
  have hr1' : 1 ≤ (RH.obj [P, D, G] G).rep.refs := hr1
  have hb0 : BcHeap S M0 H F (L1 ++ RH.obj [P, D, G] G :: L2) := by rw [← e']; exact hb
  have hGn := hb0.nums _ (List.mem_append_right _ List.mem_cons_self)
  num_facts hGn
  have hGp : (RH.obj [P, D, G] G).rep.p = G.p := RH.obj_p _ _
  have hb1 := hb0.setRefs (v := BitVec.ofNat 64 ((RH.obj [P, D, G] G).rep.refs + 1))
    (toNat_ofNat_mod32 (by omega)) hroom
  rw [hGp] at hb1
  have hu' : u ∈ L1 ++ RH.obj [P, D, G] G :: L2 := by rw [← e']; exact hu
  have hz' : z ∈ L1 ++ RH.obj [P, D, G] G :: L2 := by rw [← e']; exact hz
  have hne : ∀ w, w.rep.p ≠ G.p → w ≠ RH.obj [P, D, G] G := fun w hw he => hw (by
    rw [he, RH.obj_p])
  have hv : ((RH.obj [P, D, G] G).withRefs ((RH.obj [P, D, G] G).rep.refs + 1)).rep.num =
      G.base.rep.num := RH.obj_num _ _
  have hlen : ((RH.obj [P, D, G] G).withRefs ((RH.obj [P, D, G] G).rep.refs + 1)).rep.len =
      G.base.rep.len := RH.obj_len _ _
  have hsc : ((RH.obj [P, D, G] G).withRefs ((RH.obj [P, D, G] G).rep.refs + 1)).rep.scale =
      G.base.rep.scale := RH.obj_scale _ _
  have hst : ∀ a, OutHeap a → imgM (writeLog M0 [(G.p + 12, 4,
      BitVec.ofNat 64 ((RH.obj [P, D, G] G).rep.refs + 1))]) a = imgM M0 a := fun a ha => by
    simp only [OutHeap, heapStart, heapEnd] at ha
    exact imgM_store_miss _ _ (by omega)
  have hap := cx.slot.apart
  refine bc_divide_spec hlive (n := Num.div u.rep.num G.base.rep.num k)
    (cx.cc.div (F := 160) (by omega) (by omega) (cx.fslot (o := 24) (by omega) rfl)
      (.inr (by simp only [zeroAddr]; omega)) h2 hal)
    ⟨fun m hm R' M' H' F' L' y hk h10' hp' => ?_, fun hn => ?_, fun R' M' sp' h1 h2' hr2 hout =>
      cx.oomF hoom houtM R' M' sp' (by omega) (by omega) hr2 fun a ha hf => by
        rw [hout a ha (fun h' => hf (by simp only [slotBytes, frameIn] at h' ⊢; omega))
          (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
        exact hst a ha⟩
    ⟨by rw [hv], mem_set_of_ne hu' (hne u huG),
      List.mem_append_right _ List.mem_cons_self, mem_set_of_ne hz' (hne z hzG),
      fun h1 => by simp only [NumObj.withRefs_refs] at h1; omega,
      by rw [hlen, hsc]; omega,
      by rw [ldv_store_miss .ld _ _ (by simp only [widthOfM, zeroAddr]; omega)]; exact hzg, hl1⟩
    hzm hb1 ⟨by simp only [NumObj.withRefs_refs]; omega, by
      rw [ldv_store_miss .ld _ _ (by simp only [widthOfM]; omega), hw, NumObj.withRefs_p, hGp],
      fun h1 => by simp only [NumObj.withRefs_refs] at h1; omega⟩
    (by rw [h10]) (by rw [h11, NumObj.withRefs_p, hGp]) h12 h13
  · have hL : L' = L1 ++ RH.obj [P, D, G] G :: L2 := by
      cases hp'.rest with
      | dec _ => rw [NumObj.withRefs_succ_decRef]
      | rel h1 => simp only [NumObj.withRefs_refs] at h1; omega
    have hb2 : BcHeap S M' H' F' (y :: RList ([P, D] ++ [G]) L) := by
      have := hp'.heap; rw [hL, ← e'] at this; exact this
    have hown' : RHOwn ([P, D] ++ .own y :: [G]) L := ⟨fun w hw => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (hw | hw) | hw | hw
        · exact hown.temps w (by simp [hw])
        · exact hown.temps w (by simp [hw])
        · cases hw; exact hp'.owns
        · exact hown.temps w (by simp [hw]), hown.caller⟩
    have hyp : y.rep.p = y.sb.pay := (hp'.heap.blocks y List.mem_cons_self).sPay
    exact hret m hm R' M' H' F' y hk h10'
      (hb2.perm (RList.cons_perm [P, D] [G] y L) hown'.all) hown'
      ⟨⟨hp'.num, hp'.norm, hp'.pos, hp'.refs, hp'.owns⟩, by rw [hp'.slot, hyp]⟩
      fun a h1 h2' h3 => by
        rw [hp'.out a h1 (by simp only [slotBytes]; omega) h3]
        exact hst a h1
  · unfold Num.div at hn
    rw [if_neg (by simpa using hgm)] at hn
    cases hn

end Dc.Mach
