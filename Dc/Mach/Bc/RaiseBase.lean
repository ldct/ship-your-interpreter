import Dc.Mach.Bc.DivModEntry
import Dc.Mach.RtMsgSites
import Dc.BcModel.Raise

/-!
# `bc_raise`'s contract and state (`lib/number.c`, `0x8000660c`)

    bc_raise (num1, num2, result, scale):
      warn on a scale in num2; exponent = bc_num2long (num2)
      exponent 0: result = _one_ (error if num2's integer part is not 0)
      rscale = MIN (num1.scale * exponent, MAX (scale, num1.scale)) (or scale for a
      negative exponent); power = copy (num1), squared while the exponent is even;
      temp = copy (power), then power squared and multiplied into temp per bit;
      negative: bc_divide (_one_, temp, result, rscale), else result = temp
      with its scale truncated to rscale; temp and power freed.

The numbers `bc_raise` holds (`power` at `sp + 8`, `temp` at `sp`) are
handles (`Hd`, `KaraState.lean`): a new number of the step, or (`none`) a
reference to `num1`, so the heap is `KList [] hs A B x1` over the caller's
`A ++ x1 :: B`. While `temp` and `power` are the same object it has two
references (`KList [] [some (y.withRefs 2)] …` or `[none, none]`).

- `RaCtx`/`RaArgs`/`RaSlot`: the frame, the operands, the result slot.
- `RaPost`/`RaK`: the result `y` (a new number, or a number of the caller
  with one more reference, `AddRef`) in the slot, the old one dropped.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- What a `DWO` run reaches, as a `DW` postcondition. -/
abbrev DQ (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t : String) : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop :=
  LRO (vsaModel live) roR dcText dcRegs S Q t

/-- `L'` is `L` with one more reference to `y`: a new number with one
reference at the head, or a number of `L` shared. -/
inductive AddRef : List NumObj → NumObj → List NumObj → Prop
  | fresh {L : List NumObj} {y : NumObj} : y.rep.refs = 1 → AddRef L y (y :: L)
  | share {A B : List NumObj} {x : NumObj} :
      AddRef (A ++ x :: B) (x.withRefs (x.rep.refs + 1)) (A ++ x.withRefs (x.rep.refs + 1) :: B)

/-- `bc_raise`'s context: its 96-byte frame, the callees' room below it,
the result slot `q` off the heap and apart from the window and `_zero_`. -/
structure RaCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp W q : Nat) : Prop where
  frame : StackFrame S sp W
  above : heapEnd + W ≤ sp
  big : 512 + rmStack (2 ^ 30) ≤ W
  far : stderrAddr + 4 ≤ sp - W
  mulBase : ∀ a, mulBaseAddr ≤ a → a < mulBaseAddr + 4 → S a
  consts : ∀ a, constBytes a → S a
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0
  slot : DmSlot S sp W q
  slotZero : q + 8 ≤ zeroAddr ∨ zeroAddr + 8 ≤ q

/-- The exponent `bc_raise` uses: `bc_num2long (num2)`. -/
abbrev raExp (x2 : NumObj) : Int := x2.rep.num.toLong

/-- The operands: `num1` (`x1`) and `num2` (`x2`) normalized with an integer
digit, `_zero_` (`z`) and `_one_` (`o`) of the heap, every number an owner,
the powers small enough for `bc_multiply`, the stderr stream. -/
structure RaArgs (S : Nat → Prop) (M : Mem) (L : List NumObj) (x1 x2 z o : NumObj) (k : Nat) :
    Prop where
  m1 : x1 ∈ L
  m2 : x2 ∈ L
  mz : z ∈ L
  mo : o ∈ L
  n1 : x1.rep.Norm
  len1 : 1 ≤ x1.rep.len
  len2 : 1 ≤ x2.rep.len
  size : ((raExp x2).natAbs + 1) * (x1.rep.len + x1.rep.scale + 1) + k < 2 ^ 24
  refs1 : x1.rep.refs + 2 < 2 ^ 31
  zero : KZero M z (2 ^ 30)
  one : ldv .ld M oneAddr = BitVec.ofNat 64 o.rep.p
  oneNum : o.rep.num = Num.one
  oneNorm : o.rep.Norm
  oneLen : 1 ≤ o.rep.len
  oneRefs : o.rep.refs + 1 < 2 ^ 31
  mulBase : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80
  owns : ∀ y ∈ L, y.Owns
  fd : FdAt S M stderrAddr 2

/-- The result slot `q` holds `xr` of the heap. `_one_` replacing it needs a
second reference when it is `_one_`; a division by a zero power leaves it,
so then it is `0`. -/
structure RaSlot (M : Mem) (L : List NumObj) (x1 o xr : NumObj) (q : Nat) : Prop where
  mr : xr ∈ L
  rr : 1 ≤ xr.rep.refs
  wr : ldv .ld M q = BitVec.ofNat 64 xr.rep.p
  oneRef : xr = o → 2 ≤ xr.rep.refs
  zr : x1.rep.num.mag = 0 → raExp x2 < 0 →
    xr.rep.num = Num.zero 0 ∧ xr.rep.Norm ∧ 1 ≤ xr.rep.len

/-- The result `y` for `n` in the slot `q`: one reference added to it, then
the old number `xr` dropped. Off the heap only the slot and the window
changed. -/
structure RaPost (S : Nat → Prop) (Mt0 Mt : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (xr : NumObj) (q sp W : Nat) (n : Num) (Lf : List NumObj) (y : NumObj) : Prop where
  heap : BcHeap S Mt H F Lf
  mid : ∃ Lm, AddRef L y Lm ∧ DropAt Lm xr.rep.p Lf
  num : y.rep.num = n
  norm : y.rep.Norm
  pos : 1 ≤ y.rep.len
  owns : y.Owns
  slot : ldv .ld Mt q = BitVec.ofNat 64 y.rep.p
  out : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM Mt a = imgM Mt0 a

/-- `bc_raise`'s continuations: the result (`Num.raise …`.1), or
`out_of_memory`. -/
structure RaK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t : String) (R0 : Nat → BitVec 64) (Mt0 : Mem) (L : List NumObj) (xr : NumObj)
    (q sp W : Nat) (n : Num) : Prop where
  ret : ∀ R' Mt' H F Lf y, Keeps binClob R' R0 → RaPost S Mt0 Mt' H F L xr q sp W n Lf y →
    DWO live S Q t (R0 1) R' Mt'
  oom : DmOom live S (DQ live S Q t) Mt0 sp W

/-! ## Handles -/

/-- A temporary handle's object in the middle of the heap. -/
theorem KList.split_some (hs1 hs2 : List Hd) (x : NumObj) (A B : List NumObj) (z : NumObj) :
    KList [] (hs1 ++ some x :: hs2) A B z =
      temps hs1 ++ x :: (temps hs2 ++ A ++ z.withRefs (z.rep.refs + zeroCount (hs1 ++ hs2)) :: B) := by
  simp only [KList, temps_append, zeroCount_append, zeroCount_some, temps, List.filterMap_cons, id,
    List.nil_append, List.append_assoc, List.cons_append]

/-- A reference to `z` in the heap. -/
theorem KList.split_none (hs1 hs2 : List Hd) (A B : List NumObj) (z : NumObj) :
    KList [] (hs1 ++ none :: hs2) A B z =
      (temps (hs1 ++ hs2) ++ A) ++ z.withRefs (z.rep.refs + zeroCount (hs1 ++ none :: hs2)) :: B := by
  simp only [KList, temps_append, temps, List.filterMap_cons, id, List.nil_append, List.append_assoc]

/-- A temporary with one reference freed: its handle leaves. -/
theorem KList.freed_some {hs1 hs2 : List Hd} {x : NumObj} {A B : List NumObj} {z : NumObj}
    {L' : List NumObj} (hr : x.rep.refs = 1)
    (h : FreedRest (temps hs1) (temps hs2 ++ A ++ z.withRefs (z.rep.refs + zeroCount (hs1 ++ hs2)) :: B)
      x L') : L' = KList [] (hs1 ++ hs2) A B z := by
  cases h with
  | dec h2 => omega
  | rel _ =>
    simp only [KList, temps_append, List.nil_append, List.append_assoc]

/-- A reference to `z` dropped: its handle leaves. -/
theorem KList.freed_none {hs1 hs2 : List Hd} {A B : List NumObj} {z : NumObj} {L' : List NumObj}
    (hz : 1 ≤ z.rep.refs)
    (h : FreedRest (temps (hs1 ++ hs2) ++ A) B
      (z.withRefs (z.rep.refs + zeroCount (hs1 ++ none :: hs2))) L') :
    L' = KList [] (hs1 ++ hs2) A B z := by
  have hc : zeroCount (hs1 ++ none :: hs2) = zeroCount (hs1 ++ hs2) + 1 := by
    simp only [zeroCount_append, zeroCount_none]; omega
  cases h with
  | dec _ =>
    simp only [KList, List.nil_append, List.append_assoc, NumObj.decRef_eq, NumObj.withRefs_withRefs,
      NumObj.withRefs, hc]
    congr 4
  | rel h1 => simp only [NumObj.withRefs, hc] at h1; omega

/-- A new number heads the handles. -/
theorem KList.cons_some (y : NumObj) (hs : List Hd) (A B : List NumObj) (z : NumObj) :
    y :: KList [] hs A B z = KList [] (some y :: hs) A B z := by
  simp only [KList, temps, List.filterMap_cons, id, zeroCount_some, List.nil_append,
    List.cons_append]

/-- The object a handle names in the heap. -/
theorem KList.objIn_split (hs1 hs2 : List Hd) (h : Hd) (A B : List NumObj) (z : NumObj) :
    ∃ L1 L2, KList [] (hs1 ++ h :: hs2) A B z = L1 ++ Hd.objIn (hs1 ++ h :: hs2) z h :: L2 := by
  cases h with
  | some x => exact ⟨_, _, KList.split_some hs1 hs2 x A B z⟩
  | none => exact ⟨_, _, KList.split_none hs1 hs2 A B z⟩

/-! ## Truncation by `n_scale` -/

/-- The object with its scale cut to `s`: the digits past it are ignored. -/
def NumRep.cutScale (o : NumRep) (s : Nat) : NumRep :=
  { o with scale := s, ds := o.ds.take (o.len + s) }

/-- **`n_scale` lowered** to `s ≤ n_scale`. -/
theorem NumAt.setScale {Mt : Mem} {o : NumRep} (h : NumAt Mt o) {v : BitVec 64} {s : Nat}
    (hv : v.toNat % 2 ^ 32 = s) (hs : s ≤ o.scale) :
    NumAt (writeLog Mt [(o.p + 8, 4, v)]) (o.cutScale s) := by
  have sh := h.shape
  have hl : (o.ds.take (o.len + s)).length = o.len + s := by
    rw [List.length_take, sh.dsLen]; omega
  have hsh : NumShape (o.cutScale s) :=
    { sh with
      dsLen := hl
      dig := fun d hd => sh.dig d (List.mem_of_mem_take hd)
      size := by have := sh.size; simp only [NumRep.cutScale]; omega
      vHi := by have := sh.vHi; simp only [NumRep.cutScale]; omega
      sep := by have := sh.sep; simp only [NumRep.cutScale]; omega
      emptyScale := fun h0 => by have := sh.emptyScale h0; simp only [NumRep.cutScale]; omega }
  refine ⟨hsh, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, NumRep.cutScale]; omega)]; exact h.sign
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, NumRep.cutScale]; omega)]; exact h.len
  · exact ldv_lw_hitN (k := s) _ rfl hv (by have := sh.size; omega)
  · rw [ldv_store_miss .lw _ _ (by simp only [widthOfM, NumRep.cutScale]; omega)]; exact h.refs
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM, NumRep.cutScale]; omega)]; exact h.ptr
  · rw [ldv_store_miss .ld _ _ (by simp only [widthOfM, NumRep.cutScale]; omega)]; exact h.value
  · simp only [NumRep.cutScale] at hi ⊢
    rw [h.store_other v (by omega) (by omega), h.digit i (by omega), List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

/-- **The scale of `x` of the heap lowered** to `s`. -/
theorem BcHeap.setScale {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (L1 ++ x :: L2)) {v : BitVec 64}
    {s : Nat} (hv : v.toNat % 2 ^ 32 = s) (hs : s ≤ x.rep.scale) :
    BcHeap S (writeLog Mt [(x.rep.p + 8, 4, v)]) H F
      (L1 ++ { x with rep := x.rep.cutScale s } :: L2) := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  have hsp := hxb.sPay; have hsz := hxb.sSz
  have hin : ∀ a, x.rep.p + 8 ≤ a ∧ a < x.rep.p + 12 → x.sb.In a := fun a ha =>
    ⟨by omega, by simp only [Blk.fin, Blk.pay] at *; omega⟩
  exact BcHeap.update h rfl rfl rfl
    ⟨hxb.sLive, hxb.dLive, hxb.sPay, hxb.sSz, hxb.dPay, hxb.dLo,
      by have := hxb.dFit; simp only [NumRep.cutScale]; omega⟩
    (hn.setScale hv hs) (P := fun a => x.rep.p + 8 ≤ a ∧ a < x.rep.p + 12)
    (fun a ha => imgM_store_miss _ _ (by omega)) fun a ha => h.sb_writeOK (hin a ha)

/-- The value of the cut object: the magnitude truncated. -/
theorem NumRep.cutScale_num {o : NumRep} (hs : NumShape o) {s : Nat} (h : s ≤ o.scale) :
    (o.cutScale s).num = ⟨o.neg, o.num.mag / 10 ^ (o.scale - s), s⟩ := by
  have e := dval_div_take o.ds hs.dig (o.len + s)
  rw [hs.dsLen, show o.len + o.scale - (o.len + s) = o.scale - s by omega] at e
  simp only [NumRep.num, NumRep.cutScale, e]

/-- Cutting keeps a normalized object normalized. -/
theorem NumRep.cutScale_norm {o : NumRep} (hn : o.Norm) (hl : 1 ≤ o.len) (s : Nat) :
    (o.cutScale s).Norm := by
  rcases hn with hn | hn
  · exact .inl hn
  · refine .inr ?_
    simp only [NumRep.cutScale]
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD]
    exact hn

/-! ## Inside `bc_raise` -/

/-- The registers `bc_raise` changes before its epilogue. -/
abbrev raAll : List Nat :=
  [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 28, 29, 30, 31]

/-- The registers a call may change. -/
abbrev raCallClob : List Nat := [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- The prologue's saved registers (offsets from the lowered `sp`). -/
abbrev raSlots0 : List (Nat × Nat) := [(8, 80), (18, 64), (22, 32), (23, 24), (1, 88)]

/-- With `s1`, `s4`, `s8` saved (a nonzero exponent). -/
abbrev raSlots1 : List (Nat × Nat) :=
  [(24, 16), (20, 48), (9, 72), (8, 80), (18, 64), (22, 32), (23, 24), (1, 88)]

/-- With `s5` saved too (the second loop). -/
abbrev raSlots2 : List (Nat × Nat) :=
  [(21, 40), (24, 16), (20, 48), (9, 72), (8, 80), (18, 64), (22, 32), (23, 24), (1, 88)]

/-- Inside `bc_raise`: `sp` lowered by 96, the saved registers in the frame,
`s7` the result slot, and off the heap only the window changed. -/
structure RaAt (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (slots : List (Nat × Nat)) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 96)
  saved : SavedWords M (sp - 96) slots R0
  keep : Keeps raAll R R0
  r23 : R 23 = BitVec.ofNat 64 q
  out : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a

/-- Through a call that changes the registers of `raCallClob`, the heap, the
`power`/`temp` words and the bytes below the frame. -/
theorem RaAt.call {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    {sp W q : Nat} {slots : List (Nat × Nat)} (h : RaAt S Mt0 M R0 R sp W q slots)
    (hlo : ∀ p ∈ slots, 16 ≤ p.2 := by decide) (htop : ∀ p ∈ slots, p.2 + 8 ≤ 96 := by decide)
    (hsp : 96 ≤ sp) (hW : 96 ≤ W)
    (hkp : Keeps raCallClob R' R)
    (hag : ∀ a, OutHeap a → ¬ (sp - 96 ≤ a ∧ a < sp - 80) → ¬ frameIn (sp - 96) (W - 96) a →
      imgM M' a = imgM M a)
    (hst : ∀ a, sp - 80 ≤ a → a < sp → OutHeap a) :
    RaAt S Mt0 M' R0 R' sp W q slots where
  r2 := by rw [hkp.get 2]; exact h.r2
  saved := h.saved.transport hlo htop fun a h1 h2 =>
    hag a (hst a (by omega) (by omega)) (by omega) (by simp only [frameIn]; omega)
  keep := (hkp.mono (by decide)).trans h.keep
  r23 := by rw [hkp.get 23]; exact h.r23
  out := fun a ha hf => by
    rw [hag a ha (fun h' => hf (by simp only [frameIn]; omega))
      (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
    exact h.out a ha hf

/-! ## `bc_multiply` from `bc_raise`'s frame -/

/-- What freeing a handle's object leaves: a temporary with one reference
is gone, one with more keeps one reference fewer, a reference to `z` is
dropped. -/
def Hd.drop : Hd → List Hd
  | some x => if x.rep.refs = 1 then [] else [some x.decRef]
  | none => []

/-- **A call of `bc_multiply`** from `bc_raise`'s frame (`sp - 96`) into the
word at `sp - 96 + o`. -/
theorem ra_mulCall {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o k : Nat}
    {L1 L2 : List NumObj} {x1 x2 xr z : NumObj} {H : Heap} {F : List Blk}
    (cx : RaCtx S R0 sp W q) (hoom : DmOom live S Q Mt0 sp W) (ho : o = 0 ∨ o = 8)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (ha : MulArgs M (L1 ++ xr :: L2) x1 x2 z k)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr (sp - 96 + o))
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 96 + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ R' M' H' F' L' y, Keeps binClob R' R →
      BinPostW S M M' H' F' L1 L2 xr (sp - 96 + o) (sp - 96) (W - 96)
        (Num.mul x1.rep.num x2.rep.num k) L' y → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000573c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
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

/-- A new number for `n`, with its struct's word `w` in the slot. -/
structure MulRes (M : Mem) (w : Nat) (n : Num) (y : NumObj) : Prop extends NewNum n y where
  slot : ldv .ld M w = BitVec.ofNat 64 y.rep.p

/-- **`bc_multiply (u1, u2, &h, k)`** on the handle `h` of `bc_raise`: the
product heads the handles, `h`'s object is dropped once. -/
theorem ra_mulK {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q o k : Nat}
    {hs1 hs2 : List Hd} {h : Hd} {A B : List NumObj} {x1 u1 u2 z : NumObj} {H : Heap}
    {F : List Blk}
    (cx : RaCtx S R0 sp W q) (hoom : DmOom live S Q Mt0 sp W) (ho : o = 0 ∨ o = 8)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S M H F (KList [] (hs1 ++ h :: hs2) A B x1))
    (hown : ∀ y ∈ KList [] (hs1 ++ h :: hs2) A B x1, y.Owns) (hz1 : 1 ≤ x1.rep.refs)
    (hh : ∀ x, h = some x → 1 ≤ x.rep.refs)
    (ha : MulArgs M (KList [] (hs1 ++ h :: hs2) A B x1) u1 u2 z k)
    (hw : ldv .ld M (sp - 96 + o) = BitVec.ofNat 64 (Hd.p x1 h))
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - 96 + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ R' M' H' F' y, Keeps binClob R' R →
      BcHeap S M' H' F' (KList [] (some y :: (hs1 ++ Hd.drop h ++ hs2)) A B x1) →
      MulRes M' (sp - 96 + o) (Num.mul u1.rep.num u2.rep.num k) y →
      (∀ a, OutHeap a → ¬ slotBytes (sp - 96 + o) a → ¬ frameIn (sp - 96) (W - 96) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000573c#64 R M := by
  have post : ∀ {L1 L2 : List NumObj} {xr : NumObj},
      KList [] (hs1 ++ h :: hs2) A B x1 = L1 ++ xr :: L2 →
      (∀ L', FreedRest L1 L2 xr L' → L' = KList [] (hs1 ++ Hd.drop h ++ hs2) A B x1) →
      xr.rep.p = Hd.p x1 h → 1 ≤ xr.rep.refs →
      DW live S Q 0x8000573c#64 R M := by
    intro L1 L2 xr he hfr hp hr1
    rw [he] at hb ha hown
    have hxo : xr.Owns := hown xr (List.mem_append_right _ List.mem_cons_self)
    refine ra_mulCall hlive cx hoom ho houtM ha hb
      ⟨hr1, by rw [hw, hp], fun _ _ y hy => hb.owner_db_ne hxo hy (hown y (List.mem_append_left _ hy))⟩
      h2 hal h10 h11 h12 h13 fun R' M' H' F' L' y hk hp' => ?_
    have hyp : y.rep.p = y.sb.pay := (hp'.heap.blocks y List.mem_cons_self).sPay
    refine hret R' M' H' F' y hk ?_ ⟨⟨hp'.num, hp'.norm, hp'.pos, hp'.refs, hp'.owns⟩,
      by rw [hp'.slot, hyp]⟩ fun a h1 h2 h3 => hp'.out a h1 h2 h3
    rw [← KList.cons_some, ← hfr L' hp'.rest]
    exact hp'.heap
  cases h with
  | some x =>
    refine post (KList.split_some hs1 hs2 x A B x1) (fun L' hf => ?_) rfl (hh x rfl)
    by_cases hr : x.rep.refs = 1
    · simp only [Hd.drop, hr, ite_true, List.append_nil]
      exact KList.freed_some hr hf
    · simp only [Hd.drop, hr, ite_false]
      cases hf with
      | dec _ =>
        rw [show hs1 ++ [some x.decRef] ++ hs2 = hs1 ++ some x.decRef :: hs2 by simp,
          KList.split_some hs1 hs2 x.decRef A B x1]
      | rel h1 => exact absurd h1 hr
  | none =>
    refine post (KList.split_none hs1 hs2 A B x1) (fun L' hf => ?_) rfl
      (by simp only [NumObj.withRefs]; omega)
    simp only [Hd.drop, List.append_nil]
    exact KList.freed_none hz1 hf

end Dc.Mach
