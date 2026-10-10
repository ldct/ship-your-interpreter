import Dc.Mach.Bc.RaiseModHeap
import Dc.BcModel.RaiseMod

/-!
# `bc_raisemod`'s contract and state (`lib/number.c`, `0x800061c4`)

    bc_raisemod (base, expo, mod, result, scale):
      if (mod == _zero_ || bc_is_zero (mod)) return -1;  if (expo->n_sign == MINUS) return -1;
      power = copy (base); exponent = copy (expo); temp = copy (_one_);
      parity = copy (_zero_)                    /* references only */
      warn on a scale in base, in expo (then exponent = exponent / 1 at scale 0), in mod
      rscale = MAX (scale, power->n_scale)
      while (!bc_is_zero (exponent)) {
        bc_divmod (exponent, _two_, &exponent, &parity, 0);
        if (!bc_is_zero (parity)) { temp = temp * power (rscale); temp = temp % mod (scale) }
        power = power * power (rscale); power = power % mod (scale) }
      free power and exponent; bc_free_num (result); *result = temp; return 0

`parity` is not freed (`lib/number.c` leaks it). The four numbers are the
handles `[power, exponent, temp, parity]` of `RList` (`RaiseModHeap.lean`),
in the frame at `sp - 112 + 0, 8, 24, 16`.

- `RxCtx`/`RxArgs`/`RxSlot`: the frame, the operands, the result slot.
- `RxPost`/`RxK`: the result `y` in the slot with one reference added, the
  leaked `parity` `w`, the old number dropped; `-1`; out of memory.
- `RxAt`: inside the frame.
- `rx_mulH`, `rx_modH`, `rx_halveH`, `rx_divH`: the callees on handles.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `bc_raisemod`'s context: its 112-byte frame, the callees' room below it,
the result slot `q` off the heap and apart from the window. -/
structure RxCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp W q : Nat) : Prop where
  frame : StackFrame S sp W
  above : heapEnd + W ≤ sp
  big : 640 + rmStack (2 ^ 30) ≤ W
  far : stderrAddr + 4 ≤ sp - W
  mulBase : ∀ a, mulBaseAddr ≤ a → a < mulBaseAddr + 4 → S a
  consts : ∀ a, constBytes a → S a
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0
  slot : DmSlot S sp W q

/-- The facts of `RxCtx` the steps use, as `omega` sees them. -/
macro "rx_facts " cx:term : tactic =>
  `(tactic| (have _hsf := ($cx).frame
             have _hsl := _hsf.lo; have _hsh := _hsf.hi; have _hsa := _hsf.al
             have _hab := ($cx).above; have _hW := ($cx).big
             have _hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
             simp only [heapEnd] at _hab
             have _htx : tohostAddr = 0x8001ad00 := rfl))

/-- The operands: `base` (`xb`), `expo` (`xe`) and `mod` (`xm`) of the
caller's heap `L` of owners, `_zero_` (`z`), `_one_` (`o`) and `_two_` (`t`)
in it at their globals, the numbers small enough for the callees, room for
four more references to each number (the operands referenced), the stderr
stream. -/
structure RxArgs (S : Nat → Prop) (M : Mem) (L : List NumObj) (xb xe xm z o t : NumObj) (k : Nat) :
    Prop where
  mb : xb ∈ L
  me : xe ∈ L
  mm : xm ∈ L
  mz : z ∈ L
  mo : o ∈ L
  mt : t ∈ L
  lenb : 1 ≤ xb.rep.len
  ne : xe.rep.Norm
  lene : 1 ≤ xe.rep.len
  nm : xm.rep.Norm
  size : 8 * (xb.rep.len + xb.rep.scale + xm.rep.len + xm.rep.scale + k + 1) +
    (xe.rep.len + xe.rep.scale) < 2 ^ 24
  refs : ∀ y ∈ L, y.rep.refs + 4 < 2 ^ 31
  rb : 1 ≤ xb.rep.refs
  re : 1 ≤ xe.rep.refs
  ro : 1 ≤ o.rep.refs
  zero : KZero M z (2 ^ 30 + 4)
  one : ldv .ld M oneAddr = BitVec.ofNat 64 o.rep.p
  oneNum : o.rep.num = Num.one
  oneNorm : o.rep.Norm
  oneLen : 1 ≤ o.rep.len
  two : ldv .ld M twoAddr = BitVec.ofNat 64 t.rep.p
  twoNum : t.rep.num = ⟨false, 2, 0⟩
  twoNorm : t.rep.Norm
  mulBase : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80
  owns : ∀ y ∈ L, y.Owns
  fd : FdAt S M stderrAddr 2

/-- The result slot `q` holds `xr` of the heap. -/
structure RxSlot (M : Mem) (L : List NumObj) (xr : NumObj) (q : Nat) : Prop where
  mr : xr ∈ L
  rr : 1 ≤ xr.rep.refs
  wr : ldv .ld M q = BitVec.ofNat 64 xr.rep.p

/-- The references `bc_raisemod` moves: one added to the leaked `parity`
(`w`, a number with digits), one to the result `y`, then the slot's old
number at `p` dropped. -/
structure RxMid (L : List NumObj) (w : NumObj) (Lw : List NumObj) (y : NumObj) (Lm : List NumObj)
    (p : Nat) (Lf : List NumObj) : Prop where
  addW : AddRef L w Lw
  addY : AddRef Lw y Lm
  drop : DropAt Lm p Lf
  normW : w.rep.Norm
  posW : 1 ≤ w.rep.len
  ownsW : w.Owns

/-- The result `y` for `n` in the slot `q`: one reference added to the
leaked `parity` (`w`), one to `y`, then the old number `xr` dropped. Off the
heap only the slot and the window changed. -/
structure RxPost (S : Nat → Prop) (X : Raws) (Mt0 Mt : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (xr : NumObj) (q sp W : Nat) (n : Num) (Lf : List NumObj) (y : NumObj) : Prop where
  heap : BcHeap S X Mt H F Lf
  mid : ∃ w Lw Lm, RxMid L w Lw y Lm xr.rep.p Lf
  num : y.rep.num = n
  norm : y.rep.Norm
  pos : 1 ≤ y.rep.len
  owns : y.Owns
  slot : ldv .ld Mt q = BitVec.ofNat 64 y.rep.p
  out : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM Mt a = imgM Mt0 a

/-- `bc_raisemod`'s continuations: the result (`Num.raisemod …`), `-1` with
nothing changed but the window (a zero modulus or a negative exponent), or
`out_of_memory`. -/
structure RxK (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t : String) (R0 : Nat → BitVec 64) (Mt0 : Mem) (L : List NumObj) (xr : NumObj)
    (q sp W : Nat) (n : Option Num) : Prop where
  ret : ∀ r, n = some r → ∀ R' Mt' H F Lf y, Keeps binClob R' R0 → R' 10 = 0#64 →
    RxPost S X Mt0 Mt' H F L xr q sp W r Lf y → DWO live S Q t (R0 1) R' Mt'
  fail : n = none → ∀ R' Mt', Keeps binClob R' R0 → R' 10 = 0xffffffffffffffff#64 →
    (∀ a, ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) → DWO live S Q t (R0 1) R' Mt'
  oom : RaOom live S (DQ live S Q t) Mt0 sp W q

/-! ## Inside `bc_raisemod` -/

/-- The registers `bc_raisemod` changes before its epilogue. -/
abbrev rxAll : List Nat :=
  [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 28, 29, 30, 31]

/-- The prologue's first saved registers (`s1`, `ra`). -/
abbrev rxSlots0 : List (Nat × Nat) := [(1, 104), (9, 88)]

/-- With `s8`, `s0`, `s2`, `s3`, `s4`, `s5`, `s7` saved. -/
abbrev rxSlots1 : List (Nat × Nat) :=
  [(23, 40), (21, 56), (20, 64), (19, 72), (18, 80), (8, 96), (24, 32), (1, 104), (9, 88)]

/-- With `s6` saved too (the loop). -/
abbrev rxSlots2 : List (Nat × Nat) :=
  [(22, 48), (23, 40), (21, 56), (20, 64), (19, 72), (18, 80), (8, 96), (24, 32), (1, 104), (9, 88)]

/-- Inside `bc_raisemod`: `sp` lowered by 112, the saved registers in the
frame, and off the heap only the window changed. -/
structure RxAt (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat)
    (slots : List (Nat × Nat)) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 112)
  saved : SavedWords M (sp - 112) slots R0
  keep : Keeps rxAll R R0
  out : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a

/-- Through a call that changes the registers of `raCallClob`, the heap, the
handles' words and the bytes below the frame. -/
theorem RxAt.call {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    {sp W : Nat} {slots : List (Nat × Nat)} (h : RxAt S Mt0 M R0 R sp W slots)
    (hlo : ∀ p ∈ slots, 32 ≤ p.2 := by decide) (htop : ∀ p ∈ slots, p.2 + 8 ≤ 112 := by decide)
    (hsp : 112 ≤ sp) (hW : 112 ≤ W)
    (hkp : Keeps raCallClob R' R)
    (hag : ∀ a, OutHeap a → ¬ (sp - 112 ≤ a ∧ a < sp - 80) → ¬ frameIn (sp - 112) (W - 112) a →
      imgM M' a = imgM M a)
    (hst : ∀ a, sp - 80 ≤ a → a < sp → OutHeap a) :
    RxAt S Mt0 M' R0 R' sp W slots where
  r2 := by rw [hkp.get 2]; exact h.r2
  saved := h.saved.transport hlo htop fun a h1 h2 =>
    hag a (hst a (by omega) (by omega)) (by omega) (by simp only [frameIn]; omega)
  keep := (hkp.mono (by decide)).trans h.keep
  out := fun a ha hf => by
    rw [hag a ha (fun h' => hf (by simp only [frameIn]; omega))
      (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
    exact h.out a ha hf

/-- Through a change of registers outside the saved ones. -/
theorem RxAt.regs {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W : Nat}
    {slots : List (Nat × Nat)} (h : RxAt S Mt0 M R0 R sp W slots) {ks : List Nat}
    (hk : Keeps ks R' R) (hks : ∀ z ∈ ks, z ∈ rxAll ∧ z ≠ 2 := by decide) :
    RxAt S Mt0 M R0 R' sp W slots :=
  { h with
    r2 := by rw [hk.get 2 fun hm => (hks 2 hm).2 rfl]; exact h.r2
    keep := (hk.mono fun z hz => (hks z hz).1).trans h.keep }

/-! ## The callees from the frame -/

/-- The handles' owned numbers and the caller's numbers own their digits. -/
structure RHOwn (hs : List RH) (L : List NumObj) : Prop where
  temps : ∀ y, .own y ∈ hs → y.Owns
  caller : ∀ y ∈ L, y.Owns

theorem RHOwn.all {hs : List RH} {L : List NumObj} (h : RHOwn hs L) : ∀ y ∈ RList hs L, y.Owns :=
  RList.owns h.temps h.caller

/-- A handle replaced by a new number that owns its digits. -/
theorem RHOwn.set {hs1 hs2 : List RH} {h : RH} {L : List NumObj} (ho : RHOwn (hs1 ++ h :: hs2) L)
    {y : NumObj} (hy : y.Owns) : RHOwn (hs1 ++ .own y :: hs2) L :=
  ⟨fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact ho.temps x (List.mem_append_left _ hx)
    rcases List.mem_cons.mp hx with hx | hx
    · cases hx; exact hy
    · exact ho.temps x (List.mem_append_right _ (List.mem_cons_of_mem _ hx)), ho.caller⟩

/-- **A new number** for a handle's slot: the heap with the handle replaced,
from the callee's heap `y :: L'` and its drop of the handle's reference. -/
theorem RList.replace {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {hs1 hs2 : List RH}
    {h : RH} {L L' : List NumObj} {y : NumObj} (ho : RHOwn (hs1 ++ h :: hs2) L) (hy : y.Owns)
    (hb : BcHeap S X M H F (y :: L')) (he : L' = RList (hs1 ++ hs2) L) :
    BcHeap S X M H F (RList (hs1 ++ .own y :: hs2) L) := by
  subst he
  exact hb.perm (RList.cons_perm hs1 hs2 y L) (ho.set hy).all

/-- **A call of `bc_multiply`** from `bc_raisemod`'s frame (`sp - 112`) into
the word at `sp - 112 + o`. -/
theorem rx_mulCall {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o k : Nat}
    {L1 L2 : List NumObj} {x1 x2 xr z : NumObj} {H : Heap} {F : List Blk}
    (cx : RxCtx S R0 sp W q) (hoom : DmOom live S Q Mt0 sp W) (ho : o ≤ 24) (ho8 : o % 8 = 0)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (ha : MulArgs M (L1 ++ xr :: L2) x1 x2 z k)
    (hb : BcHeap S X M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr (sp - 112 + o))
    (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 112 + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ R' M' H' F' L' y, Keeps binClob R' R →
      BinPostW S X M M' H' F' L1 L2 xr (sp - 112 + o) (sp - 112) (W - 112)
        (Num.mul x1.rep.num x2.rep.num k) L' y → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000573c#64 R M := by
  rx_facts cx
  have hsf := cx.frame
  have hsz := ha.size
  have hrs := rmStack_mono (show x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale) ≤ 2 ^ 30
    by omega)
  exact bc_multiply_spec hlive
    ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
      by simp only [heapEnd]; omega, by omega,
      ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩,
      fun a ha => by simp only [slotBytes] at ha; simp only [OutHeap, heapStart, heapEnd,
        freeListAddr, bcFreeAddr]; omega,
      .inr (by omega), cx.mulBase, cx.consts, h2, hal⟩
    ha (by omega) hb hr h10 h11 h12 h13
    ⟨hret, fun R' M' sp' h1 h2 hr2 hout => hoom R' M' sp' (by omega) (by omega) hr2
      fun a ha hf => by
        rw [hout a ha (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
        exact houtM a ha hf⟩

/-- What a callee's slot holds: the number a handle names. -/
theorem RList.slot {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {hs1 hs2 : List RH}
    {h : RH} {L : List NumObj} (hb : BcHeap S X M H F (RList (hs1 ++ h :: hs2) L)) (hh : RHOK L h)
    (ho : RHOwn (hs1 ++ h :: hs2) L) :
    ∃ L1 L2 x, RList (hs1 ++ h :: hs2) L = L1 ++ x :: L2 ∧ x.rep.p = h.p ∧ 1 ≤ x.rep.refs ∧
      (x.rep.refs = 1 → x.Owns → ∀ y ∈ L1, y.db ≠ x.db) ∧ (∀ y, h = .ref y → 2 ≤ x.rep.refs) ∧
      x = RH.obj (hs1 ++ h :: hs2) h ∧
      ∀ L', FreedRest L1 L2 x L' → L' = RList (hs1 ++ hs2) L := by
  obtain ⟨L1, L2, x, e, hp, hr, _, h2, hx, hf⟩ := RList.drop hb.pdist hh
  have hb' := hb; rw [e] at hb'
  have hall := ho.all; rw [e] at hall
  exact ⟨L1, L2, x, e, hp, hr, fun _ hxo y hy =>
    hb'.owner_db_ne hxo hy (hall y (List.mem_append_left _ hy)), h2, hx, hf⟩

/-- **`bc_multiply (u1, u2, &h, k)`** on the handle `h` of `bc_raisemod`
(its word at `sp - 112 + o`): the product replaces it. -/
theorem rx_mulH {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o k : Nat}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {u1 u2 z : NumObj} {H : Heap}
    {F : List Blk}
    (cx : RxCtx S R0 sp W q) (hoom : DmOom live S Q Mt0 sp W) (ho : o ≤ 24) (ho8 : o % 8 = 0)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S X M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h) (ha : MulArgs M (RList (hs1 ++ h :: hs2) L) u1 u2 z k)
    (hw : ldv .ld M (sp - 112 + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 112 + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ R' M' H' F' y, Keeps binClob R' R →
      BcHeap S X M' H' F' (RList (hs1 ++ .own y :: hs2) L) →
      MulRes M' (sp - 112 + o) (Num.mul u1.rep.num u2.rep.num k) y →
      (∀ a, OutHeap a → ¬ slotBytes (sp - 112 + o) a → ¬ frameIn (sp - 112) (W - 112) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000573c#64 R M := by
  obtain ⟨L1, L2, x, e, hp, hr1, hnv, _, _, hfr⟩ := RList.slot hb hh hown
  rw [e] at hb ha
  refine rx_mulCall hlive cx hoom ho ho8 houtM ha hb ⟨hr1, by rw [hw, hp], hnv⟩
    h2 hal h10 h11 h12 h13 fun R' M' H' F' L' y hk hp' => ?_
  have hyp : y.rep.p = y.sb.pay := (hp'.heap.blocks y List.mem_cons_self).sPay
  exact hret R' M' H' F' y hk (RList.replace hown hp'.owns hp'.heap (hfr L' hp'.rest))
    ⟨⟨hp'.num, hp'.norm, hp'.pos, hp'.refs, hp'.owns⟩, by rw [hp'.slot, hyp]⟩
    fun a h1 h2 h3 => hp'.out a h1 h2 h3

/-- `bc_divmod`'s context from `bc_raisemod`'s frame. -/
theorem RxCtx.dm {S : Nat → Prop} {R0 R : Nat → BitVec 64} {sp W q : Nat} (cx : RxCtx S R0 sp W q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (hal : (R 1).toNat % 4 = 0) :
    DmCtx S R (sp - 112) (W - 112) := by
  rx_facts cx
  have hsf := cx.frame
  exact ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
    by simp only [heapEnd]; omega, by omega, cx.mulBase, cx.consts, h2, hal⟩

/-- A word of `bc_raisemod`'s frame as a callee's result slot. -/
theorem RxCtx.dmSlot {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp W q o : Nat}
    (cx : RxCtx S R0 sp W q) (ho : o ≤ 24) (ho8 : o % 8 = 0) :
    DmSlot S (sp - 112) (W - 112) (sp - 112 + o) := by
  rx_facts cx
  have hsf := cx.frame
  exact ⟨⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩,
    fun a ha => by simp only [slotBytes] at ha; simp only [OutHeap, heapStart, heapEnd,
      freeListAddr, bcFreeAddr]; omega, .inr (by omega)⟩

/-- `out_of_memory` from a callee of `bc_raisemod`'s frame. -/
theorem DmOom.inner {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {Mt0 M : Mem} {sp W : Nat} (h : DmOom live S Q Mt0 sp W) (hW : 112 ≤ W) (hsp : 112 ≤ sp)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    DmOom live S Q M (sp - 112) (W - 112) :=
  fun R' M' sp' h1 h2 hr2 hout => h R' M' sp' (by omega) (by omega) hr2 fun a ha hf => by
    rw [hout a ha (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
    exact houtM a ha hf

/-- **`bc_divmod (u1, u2, NULL, &h, k)`** (`bc_modulo`) on the handle `h`
of `bc_raisemod` (its word at `sp - 112 + o`) by a nonzero `u2`: the
remainder replaces it. -/
theorem rx_modH {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o k : Nat}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {u1 u2 z : NumObj} {H : Heap}
    {F : List Blk}
    (cx : RxCtx S R0 sp W q) (hoom : DmOom live S Q Mt0 sp W) (ho : o ≤ 24) (ho8 : o % 8 = 0)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S X M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h) (ha : DmArgs M (RList (hs1 ++ h :: hs2) L) u1 u2 z k)
    (hm2 : u2.rep.num.mag ≠ 0)
    (hw : ldv .ld M (sp - 112 + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = 0#64) (h13 : R 13 = BitVec.ofNat 64 (sp - 112 + o))
    (h14 : R 14 = BitVec.ofNat 64 k)
    (hret : ∀ r, Num.modulo u1.rep.num u2.rep.num k = some r → ∀ R' M' H' F' y,
      Keeps binClob R' R → R' 10 = 0#64 →
      BcHeap S X M' H' F' (RList (hs1 ++ .own y :: hs2) L) → ResNum M' (sp - 112 + o) r y →
      (∀ a, OutHeap a → ¬ slotBytes (sp - 112 + o) a → ¬ frameIn (sp - 112) (W - 112) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x80005fd0#64 R M := by
  rx_facts cx
  have hpd := hb.pdist
  obtain ⟨L1, L2, x, e, hp, hr1, _, _, _, hfr⟩ := RList.slot hb hh hown
  have hxm : x ∈ RList (hs1 ++ h :: hs2) L := by rw [e]; exact List.mem_append_right _ List.mem_cons_self
  refine bc_divmod_rem_spec hlive (cx.dm h2 hal) ha (cx.dmSlot ho ho8) hxm hr1
    (by rw [hw, hp]) hb ⟨fun r hr R' M' H' F' Lf yr hk h10' hp' => ?_, fun hn => ?_,
      hoom.inner (by omega) (by omega) houtM⟩ h10 h11 h12 h13 h14
  · rw [e] at hpd
    have hf := DropAt.unique hpd (by rw [← e]; exact hp'.mid)
    exact hret r hr R' M' H' F' yr hk h10' (RList.replace hown hp'.rem.owns hp'.heap (hfr Lf hf))
      hp'.rem hp'.out
  · obtain ⟨r, hr, _⟩ := Dc.BcModel.modulo_res (a := u1.rep.num) (k := k) hm2
    rw [hr] at hn; cases hn

/-- **`bc_divmod (exponent, u2, &exponent, &parity, 0)`** on `bc_raisemod`'s
handles `[power, exponent, temp, parity]` (words at `sp - 112 + 8` and
`+ 16`): the quotient and remainder replace the exponent and the parity. -/
theorem rx_halveH {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {hP hE hT hX : RH} {L : List NumObj} {u1 u2 z : NumObj} {H : Heap} {F : List Blk}
    (cx : RxCtx S R0 sp W q) (hoom : DmOom live S Q Mt0 sp W)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S X M H F (RList [hP, hE, hT, hX] L)) (hown : RHOwn [hP, hE, hT, hX] L)
    (hhE : RHOK L hE) (hhX : RHOK L hX) (hEX : hE.p ≠ hX.p)
    (ha : DmArgs M (RList [hP, hE, hT, hX] L) u1 u2 z 0) (hm2 : u2.rep.num.mag ≠ 0)
    (hw8 : ldv .ld M (sp - 112 + 8) = BitVec.ofNat 64 hE.p)
    (hw16 : ldv .ld M (sp - 112 + 16) = BitVec.ofNat 64 hX.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 112 + 8)) (h13 : R 13 = BitVec.ofNat 64 (sp - 112 + 16))
    (h14 : R 14 = BitVec.ofNat 64 0)
    (hret : ∀ m, Num.divmod u1.rep.num u2.rep.num 0 = some m → ∀ R' M' H' F' yq yr,
      Keeps binClob R' R → R' 10 = 0#64 →
      BcHeap S X M' H' F' (RList [hP, .own yq, hT, .own yr] L) →
      ResNum M' (sp - 112 + 8) m.1 yq → ResNum M' (sp - 112 + 16) m.2 yr →
      (∀ a, OutHeap a → ¬ slotBytes (sp - 112 + 8) a → ¬ slotBytes (sp - 112 + 16) a →
        ¬ frameIn (sp - 112) (W - 112) a → imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x80005fd0#64 R M := by
  rx_facts cx
  have hpd := hb.pdist
  have hbX : BcHeap S X M H F (RList ([hP, hE, hT] ++ hX :: []) L) := hb
  have hoX : RHOwn ([hP, hE, hT] ++ hX :: []) L := hown
  have hbE : BcHeap S X M H F (RList ([hP] ++ hE :: [hT, hX]) L) := hb
  have hoE : RHOwn ([hP] ++ hE :: [hT, hX]) L := hown
  obtain ⟨L1r, L2r, xr, er, hpr, hrr, _, _, _, hfrr⟩ := RList.slot hbX hhX hoX
  obtain ⟨L1q, L2q, xq, eq, hpq, hrq, _, _, _, _⟩ := RList.slot hbE hhE hoE
  have hxr : xr ∈ RList [hP, hE, hT, hX] L := by
    show xr ∈ RList ([hP, hE, hT] ++ hX :: []) L
    rw [er]; exact List.mem_append_right _ List.mem_cons_self
  have hxq : xq ∈ RList [hP, hE, hT, hX] L := by
    show xq ∈ RList ([hP] ++ hE :: [hT, hX]) L
    rw [eq]; exact List.mem_append_right _ List.mem_cons_self
  refine bc_divmod_spec hlive (cx.dm h2 hal) ha
    ⟨cx.dmSlot (o := 8) (by omega) rfl, cx.dmSlot (o := 16) (by omega) rfl, by omega, by omega,
      hxq, hxr, hrq, hrr, fun e => absurd (by rw [← hpq, ← hpr, e]) hEX,
      by rw [hw8, hpq], by rw [hw16, hpr]⟩ hb
    ⟨fun m hm R' M' H' F' Lf yq yr hk h10' hp' => ?_, fun hn => ?_,
      hoom.inner (by omega) (by omega) houtM⟩ h10 h11 h12 h13 h14
  · obtain ⟨Lm, hd1, hd2⟩ := hp'.mid
    have hpdX : PDist (L1r ++ xr :: L2r) := by
      have := hpd; unfold PDist at this ⊢; rw [← er]; exact this
    have hd1' : DropAt (L1r ++ xr :: L2r) xr.rep.p Lm := by
      have : DropAt (RList ([hP, hE, hT] ++ hX :: []) L) xr.rep.p Lm := hd1
      rwa [er] at this
    have hm : Lm = RList [hP, hE, hT] L := hfrr Lm (DropAt.unique hpdX hd1')
    subst hm
    have hpdm : PDist (RList ([hP] ++ hE :: [hT]) L) :=
      PDist.drop (hs1 := [hP, hE, hT]) (hs2 := []) (h := hX) hpd
    obtain ⟨L1e, L2e, xe, ee, hpe, _, _, _, _, hfre⟩ := RList.drop hpdm hhE
    have hpdE : PDist (L1e ++ xe :: L2e) := by rw [← ee]; exact hpdm
    have hd2' : DropAt (L1e ++ xe :: L2e) xe.rep.p Lf := by
      rw [← ee, hpe, ← hpq]; exact hd2
    have hf : Lf = RList ([hP] ++ [hT]) L := hfre Lf (DropAt.unique hpdE hd2')
    subst hf
    have hoq : RHOwn [hP, .own yq, hT, hX] L := hoE.set hp'.quo.owns
    have hor : RHOwn [hP, .own yq, hT, .own yr] L :=
      (show RHOwn ([hP, .own yq, hT] ++ hX :: []) L from hoq).set hp'.rem.owns
    have hperm : (yr :: yq :: RList ([hP] ++ [hT]) L).Perm (RList [hP, .own yq, hT, .own yr] L) :=
      (List.Perm.cons yr (RList.cons_perm [hP] [hT] yq L)).trans
        (RList.cons_perm [hP, .own yq, hT] [] yr L)
    exact hret m hm R' M' H' F' yq yr hk h10' (hp'.heap.perm hperm hor.all) hp'.quo hp'.rem hp'.out
  · unfold Num.divmod at hn
    rw [Num.div, if_neg (by simpa using hm2)] at hn
    cases hn

/-- **`bc_divide (u1, u2, &h, k)`** on a reference handle `h` of
`bc_raisemod` (its word at `sp - 112 + o`) by a nonzero `u2`: the quotient
replaces it. -/
theorem rx_divH {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o k : Nat}
    {hs1 hs2 : List RH} {L : List NumObj} {p u1 u2 z : NumObj} {H : Heap} {F : List Blk}
    (cx : RxCtx S R0 sp W q) (hoom : RaOom live S Q Mt0 sp W q) (ho : o ≤ 24) (ho8 : o % 8 = 0)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S X M H F (RList (hs1 ++ .ref p :: hs2) L)) (hown : RHOwn (hs1 ++ .ref p :: hs2) L)
    (hh : RHOK L (.ref p))
    (hm1 : u1 ∈ RList (hs1 ++ .ref p :: hs2) L) (hm2 : u2 ∈ RList (hs1 ++ .ref p :: hs2) L)
    (hmz : z ∈ RList (hs1 ++ .ref p :: hs2) L)
    (hsz : u1.rep.len + u1.rep.scale + k + u2.rep.len + u2.rep.scale < 2 ^ 27)
    (hz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p) (hzm : z.rep.num.mag = 0)
    (hl1 : 1 ≤ u1.rep.len) (hn2 : u2.rep.num.mag ≠ 0)
    (hw : ldv .ld M (sp - 112 + o) = BitVec.ofNat 64 p.rep.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 112 + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ m, Num.div u1.rep.num u2.rep.num k = some m → ∀ R' M' H' F' y,
      Keeps binClob R' R → R' 10 = 0#64 →
      BcHeap S X M' H' F' (RList (hs1 ++ .own y :: hs2) L) → ResNum M' (sp - 112 + o) m y →
      (∀ a, OutHeap a → ¬ slotBytes (sp - 112 + o) a → ¬ frameIn (sp - 112) (W - 112) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000589c#64 R M := by
  rx_facts cx
  have hsf := cx.frame
  obtain ⟨L1, L2, x, e, hp, hr1, hnv, h2r, _, hfr⟩ := RList.slot hb hh hown
  have hx2 := h2r p rfl
  rw [e] at hb hm1 hm2 hmz
  refine bc_divide_spec hlive (q := sp - 112 + o) (W := W - 112)
    ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
      by simp only [heapEnd]; omega, by omega,
      ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩,
      fun a ha => by simp only [slotBytes] at ha; simp only [OutHeap, heapStart, heapEnd,
        freeListAddr, bcFreeAddr]; omega,
      .inr (by omega), .inr (by simp only [zeroAddr]; omega), cx.consts, h2, hal⟩
    ⟨fun m hm R' M' H' F' L' y hk h10' hp' => ?_, fun hn => ?_,
      fun R' M' sp' h1 h2 hr2 hout => hoom R' M' sp' (by omega) (by omega) hr2
        fun a ha hs hf => by
          have : ¬ slotBytes (sp - 112 + o) a := fun h => hf (by simp only [slotBytes, frameIn] at h ⊢; omega)
          rw [hout a ha this (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
          exact houtM a ha hf⟩
    ⟨rfl, hm1, hm2, hmz, fun h1 => absurd h1 (by omega), hsz, hz, hl1⟩ hzm hb
    ⟨hr1, by rw [hw, hp]; rfl, hnv⟩ h10 h11 h12 h13
  · have hyp : y.rep.p = y.sb.pay := (hp'.heap.blocks y List.mem_cons_self).sPay
    exact hret m hm R' M' H' F' y hk h10' (RList.replace hown hp'.owns hp'.heap (hfr L' hp'.rest))
      ⟨⟨hp'.num, hp'.norm, hp'.pos, hp'.refs, hp'.owns⟩, hp'.slot⟩ hp'.out
  · unfold Num.div at hn
    rw [if_neg (by simpa using hn2)] at hn
    cases hn

end Dc.Mach
