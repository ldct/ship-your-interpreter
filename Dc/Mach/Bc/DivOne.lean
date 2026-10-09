import Dc.Mach.Bc.DivLink

/-!
# `bc_divide`'s divide-by-one detour (`0x80005e54`)

GNU bc 1.07's `bc_divide` builds `n1` truncated to `scale` as the quotient
when `n2` is `1`, stores it in the slot, and then falls through into the
general division (no `return`), which frees that quotient and stores its own.

- `FreedRest.keep`: an operand survives freeing the slot's old number.
- `DivKF.rebase`: the continuations with the detour's quotient in the slot.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

/-- **An operand survives** freeing `x` when it is not `x` or `x` keeps a
reference: the same representation up to the reference count. -/
theorem FreedRest.keep {L1 L2 L : List NumObj} {x y : NumObj} (h : FreedRest L1 L2 x L)
    (hy : y ∈ L1 ++ x :: L2) (hok : x.rep.refs = 1 → y ≠ x) :
    ∃ y' ∈ L, ∃ r, y'.rep = { y.rep with refs := r } := by
  have hy' : y = x ∨ y ∈ L1 ++ L2 := by
    rcases List.mem_append.mp hy with h1 | h1
    · exact .inr (List.mem_append_left _ h1)
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact .inl h2
      · exact .inr (List.mem_append_right _ h2)
  cases h with
  | dec h2 =>
    rcases hy' with rfl | h1
    · exact ⟨y.decRef, List.mem_append_right _ List.mem_cons_self, _, rfl⟩
    · refine ⟨y, ?_, y.rep.refs, rfl⟩
      rcases List.mem_append.mp h1 with h3 | h3
      · exact List.mem_append_left _ h3
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h3)
  | rel h1 =>
    rcases hy' with rfl | h3
    · exact absurd rfl (hok h1)
    · exact ⟨y, h3, y.rep.refs, rfl⟩

/-- **The continuations after the detour**: the slot holds `y` (one
reference), `L` is what freeing the old number left, and off the heap, the
slot and the window the memory is the entry's. -/
theorem DivKF.rebase {live S : Nat → Prop} {X : Raws} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {R0 : Nat → BitVec 64} {Mt0 Mt1 : Mem} {Fr : List NumObj → Prop} {L : List NumObj} {y : NumObj}
    {q sp W : Nat} {n : Option Num} (hk : DivKF live S X Q R0 Mt0 Fr q sp W n) (hfr : Fr L)
    (hy : y.rep.refs = 1) (hnn : n ≠ none)
    (hM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM Mt1 a = imgM Mt0 a) :
    DivKF live S X Q R0 Mt1 (FreedRest [] L y) q sp W n where
  ret m hm R' Mt' H F L' y' hkp h10 hp := hk.ret m hm R' Mt' H F L' y' hkp h10
    { heap := hp.heap
      rest := by
        cases hp.rest with
        | dec h2 => omega
        | rel _ => exact hfr
      num := hp.num
      norm := hp.norm
      pos := hp.pos
      refs := hp.refs
      owns := hp.owns
      slot := hp.slot
      out := fun a ho hs hf => (hp.out a ho hs hf).trans (hM a ho hs hf) }
  zero h := absurd h hnn
  oomW R' Mt' sp' h1 h2 h3 h4 := hk.oomW R' Mt' sp' h1 h2 h3 fun a ho hs hf =>
    (h4 a ho hs hf).trans (hM a ho hs hf)

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- An operand found again after freeing: the same representation up to the
reference count, so the same value, place and sizes. -/
structure SameRep (y x : NumObj) : Prop where
  num : y.rep.num = x.rep.num
  p : y.rep.p = x.rep.p
  len : y.rep.len = x.rep.len
  scale : y.rep.scale = x.rep.scale
  ds : y.rep.ds = x.rep.ds

theorem SameRep.of_eq {y x : NumObj} {r : Nat} (h : y.rep = { x.rep with refs := r }) :
    SameRep y x := ⟨by rw [h]; rfl, by rw [h], by rw [h], by rw [h], by rw [h]⟩

/-! ## Whole digit buffers rewritten -/

/-- **Every digit byte rewritten**: memory changed only in the digit range,
holding the digits `ds`. -/
theorem NumAt.setDigits {Mt Mt' : Mem} {o : NumRep} (h : NumAt Mt o) {ds : List Nat}
    (hl : ds.length = o.len + o.scale) (hd : Digits ds)
    (hfr : MemOnly (fun a => o.val ≤ a ∧ a < o.val + o.len + o.scale) Mt' Mt)
    (hb : ∀ i, i < o.len + o.scale → imgM Mt' (o.val + i) = BitVec.ofNat 8 (ds.getD i 0)) :
    NumAt Mt' { o with ds := ds } := by
  have hs := h.shape
  have hsep := hs.sep
  have hshape : NumShape { o with ds := ds } := { hs with dsLen := hl, dig := hd }
  refine ⟨hshape, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => hb j hj⟩
  all_goals dsimp only
  · rw [ldv_congr .lw fun j hj => hfr _ fun hc => by simp only [widthOfM] at hj; obtain ⟨c1, c2⟩ := hc; omega]; exact h.sign
  · rw [ldv_congr .lw fun j hj => hfr _ fun hc => by simp only [widthOfM] at hj; obtain ⟨c1, c2⟩ := hc; omega]; exact h.len
  · rw [ldv_congr .lw fun j hj => hfr _ fun hc => by simp only [widthOfM] at hj; obtain ⟨c1, c2⟩ := hc; omega]; exact h.scale
  · rw [ldv_congr .lw fun j hj => hfr _ fun hc => by simp only [widthOfM] at hj; obtain ⟨c1, c2⟩ := hc; omega]; exact h.refs
  · rw [ldv_congr .ld fun j hj => hfr _ fun hc => by simp only [widthOfM] at hj; obtain ⟨c1, c2⟩ := hc; omega]; exact h.ptr
  · rw [ldv_congr .ld fun j hj => hfr _ fun hc => by simp only [widthOfM] at hj; obtain ⟨c1, c2⟩ := hc; omega]; exact h.value

/-- **The head object's digits rewritten** (it owns its buffer): the heap
holds it with the digits `ds`. -/
theorem BcHeap.setDigits {S : Nat → Prop} {X : Raws} {Mt Mt' : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {x : NumObj} (h : BcHeap S X Mt H F (x :: L)) (ho : x.Owns) {ds : List Nat}
    (hl : ds.length = x.rep.len + x.rep.scale) (hd : Digits ds)
    (hfr : MemOnly (fun a => x.rep.val ≤ a ∧ a < x.rep.val + x.rep.len + x.rep.scale) Mt' Mt)
    (hb : ∀ i, i < x.rep.len + x.rep.scale → imgM Mt' (x.rep.val + i) = BitVec.ofNat 8 (ds.getD i 0)) :
    BcHeap S X Mt' H F (withDs x ds :: L) := by
  have hn := h.nums x List.mem_cons_self
  have hxb := h.blocks x List.mem_cons_self
  have hdf := hxb.dFit; have hdl := hxb.dLo
  have hfin : x.db.fin = x.db.pay + x.db.sz := rfl
  exact BcHeap.update (L1 := []) h rfl rfl rfl
    ⟨hxb.sLive, hxb.dLive, hxb.sPay, hxb.sSz, hxb.dPay, hxb.dLo, hxb.dFit⟩
    (hn.setDigits hl hd hfr hb) hfr
    fun a ha => h.db_writeOK (L1 := []) ho (h.head_noView ho) (by obtain ⟨c1, c2⟩ := ha; exact ⟨by omega, by omega⟩)

/-- The detour's quotient digits: `n1`'s first `c` digits, then zeros. -/
abbrev dvOneDs (ds : List Nat) (c t : Nat) : List Nat := ds.take c ++ List.replicate (t - c) 0

theorem dvOneDs_getD {ds : List Nat} {c t i : Nat} (hc : c ≤ ds.length) (hct : c ≤ t) :
    (dvOneDs ds c t).getD i 0 = if i < c then ds.getD i 0 else 0 := by
  simp only [dvOneDs, List.getD_eq_getElem?_getD]
  by_cases h : i < c
  · rw [if_pos h, List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt h]
  · rw [if_neg h, List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
    split <;> rfl

theorem dvOneDs_length {ds : List Nat} {c t : Nat} (hc : c ≤ ds.length) (hct : c ≤ t) :
    (dvOneDs ds c t).length = t := by
  simp only [dvOneDs, List.length_append, List.length_take, List.length_replicate]; omega

theorem dvOneDs_digits {ds : List Nat} (hd : Digits ds) (c t : Nat) : Digits (dvOneDs ds c t) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hd e (List.mem_of_mem_take h)
  · rw [(List.mem_replicate.mp h).2]; omega

/-- `bc_divide`'s operands: the dividend `x1` (a positive integer length),
the divisor `x2` and `_zero_` (`z`, its word at `zeroAddr`) in the heap, none
of them the slot's number when that has one reference, and the quotient `n`
the model's. -/
structure DivArgs (Mt0 : Mem) (L1 L2 : List NumObj) (xr x1 x2 z : NumObj) (n : Option Num)
    (k : Nat) : Prop where
  div : n = Num.div x1.rep.num x2.rep.num k
  m1 : x1 ∈ L1 ++ xr :: L2
  m2 : x2 ∈ L1 ++ xr :: L2
  mz : z ∈ L1 ++ xr :: L2
  apart : xr.rep.refs = 1 → x1 ≠ xr ∧ x2 ≠ xr ∧ z ≠ xr
  size : x1.rep.len + x1.rep.scale + k + x2.rep.len + x2.rep.scale < 2 ^ 27
  zero : ldv .ld Mt0 zeroAddr = BitVec.ofNat 64 z.rep.p
  /-- `bc_new_num` takes a positive integer length -/
  len1 : 1 ≤ x1.rep.len

/-- The divisor `1` at scale `0`, as the divide-by-one test reads it. -/
def IsOneRep (o : NumRep) : Prop := o.len = 1 ∧ o.scale = 0 ∧ o.ds.getD 0 0 = 1

/-- `DivArgs` over a slot `QSlot`: the heap `L0`, and, for a divisor `1`
(the divide-by-one detour frees the slot and then reads the operands again),
each operand found again (up to its count) in what freeing the slot leaves
(`Fr`). Any other divisor may share the slot's number with the dividend. -/
structure DivArgsF (Mt0 : Mem) (L0 : List NumObj) (Fr : List NumObj → Prop) (x1 x2 z : NumObj)
    (n : Option Num) (k : Nat) : Prop where
  div : n = Num.div x1.rep.num x2.rep.num k
  m1 : x1 ∈ L0
  m2 : x2 ∈ L0
  mz : z ∈ L0
  k1 : IsOneRep x2.rep → ∀ L, Fr L → ∃ y ∈ L, ∃ r, y.rep = { x1.rep with refs := r }
  k2 : IsOneRep x2.rep → ∀ L, Fr L → ∃ y ∈ L, ∃ r, y.rep = { x2.rep with refs := r }
  kz : IsOneRep x2.rep → ∀ L, Fr L → ∃ y ∈ L, ∃ r, y.rep = { z.rep with refs := r }
  size : x1.rep.len + x1.rep.scale + k + x2.rep.len + x2.rep.scale < 2 ^ 27
  zero : ldv .ld Mt0 zeroAddr = BitVec.ofNat 64 z.rep.p
  len1 : 1 ≤ x1.rep.len

/-- `DivArgs` for a slot holding a number. -/
theorem DivArgs.toF {Mt0 : Mem} {L1 L2 : List NumObj} {xr x1 x2 z : NumObj} {n : Option Num}
    {k : Nat} (h : DivArgs Mt0 L1 L2 xr x1 x2 z n k) :
    DivArgsF Mt0 (L1 ++ xr :: L2) (FreedRest L1 L2 xr) x1 x2 z n k :=
  ⟨h.div, h.m1, h.m2, h.mz, fun _ _ hf => hf.keep h.m1 fun e => (h.apart e).1,
    fun _ _ hf => hf.keep h.m2 fun e => (h.apart e).2.1,
    fun _ _ hf => hf.keep h.mz fun e => (h.apart e).2.2,
    h.size, h.zero, h.len1⟩

/-- `DivArgs` for a `NULL` slot: the heap is left as it is. -/
theorem DivArgsF.null {Mt0 : Mem} {L0 : List NumObj} {x1 x2 z : NumObj} {n : Option Num} {k : Nat}
    (hd : n = Num.div x1.rep.num x2.rep.num k) (h1 : x1 ∈ L0) (h2 : x2 ∈ L0) (hz : z ∈ L0)
    (hsz : x1.rep.len + x1.rep.scale + k + x2.rep.len + x2.rep.scale < 2 ^ 27)
    (hzg : ldv .ld Mt0 zeroAddr = BitVec.ofNat 64 z.rep.p) (hl1 : 1 ≤ x1.rep.len) :
    DivArgsF Mt0 L0 (· = L0) x1 x2 z n k :=
  ⟨hd, h1, h2, hz, fun _ _ e => e ▸ ⟨x1, h1, _, rfl⟩, fun _ _ e => e ▸ ⟨x2, h2, _, rfl⟩,
    fun _ _ e => e ▸ ⟨z, hz, _, rfl⟩, hsz, hzg, hl1⟩

/-- The divide-by-one detour's facts: `n2 = 1` (scale zero). -/
structure DvOne (Mt0 : Mem) (L0 : List NumObj) (Fr : List NumObj → Prop) (x1 x2 z : NumObj)
    (n : Option Num) (k : Nat) : Prop extends DivArgsF Mt0 L0 Fr x1 x2 z n k where
  len2 : x2.rep.len = 1
  scale2 : x2.rep.scale = 0
  dig2 : x2.rep.ds.getD 0 0 = 1

/-- **Back into the general path** at `0x80005954`: the detour's quotient
`y` in the slot, the operands found again in what freeing the old number
left; `dv_body` with `y` as the slot's number. -/
theorem dvone_enter {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 L : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S X Q R0 Mt0 Fr q sp W n)
    (one : DvOne Mt0 L0 Fr x1 x2 z n k)
    (sv : SavedWords M (sp - 208) divSlots R0) (hb : BcHeap S X M H F (y :: L))
    (hfr : Fr L) (hyr : y.rep.refs = 1)
    (hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h19 : R 19 = 0#64)
    (h21 : R 21 = BitVec.ofNat 64 k) (h22 : R 22 = BitVec.ofNat 64 q) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005954#64 R (writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)]) := by
  have hn := one.div; have hx1 := one.m1; have hx2 := one.m2; have hz := one.mz
  have hl2 := one.len2; have hs2 := one.scale2; have hd2 := one.dig2
  have hsz := one.size; have hzg := one.zero
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hap := cx.slotApart; have hqz := cx.slotZero
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  obtain ⟨y1, hy1, r1, e1⟩ := one.k1 ⟨one.len2, one.scale2, one.dig2⟩ L hfr
  obtain ⟨y2, hy2, r2, e2⟩ := one.k2 ⟨one.len2, one.scale2, one.dig2⟩ L hfr
  obtain ⟨y3, hy3, r3, e3⟩ := one.kz ⟨one.len2, one.scale2, one.dig2⟩ L hfr
  have s1 := SameRep.of_eq e1; have s2 := SameRep.of_eq e2; have s3 := SameRep.of_eq e3
  have hm2 : y2 ∈ y :: L := List.mem_cons_of_mem _ hy2
  have hn2 := hb.nums y2 hm2
  num_facts hn2
  have hl2' : x2.rep.ds.length = x2.rep.len + x2.rep.scale := by
    rw [← s2.ds, ← s2.len, ← s2.scale]; exact hn2.shape.dsLen
  have hmag : x2.rep.num.mag ≠ 0 := by
    have := dvalBE_ge_of_first (vs := x2.rep.ds) (by omega) (by rw [hd2]; omega)
    have := Nat.pow_pos (n := x2.rep.ds.length - 1) (show 0 < 10 by decide)
    simp only [NumRep.num_eq]; omega
  have hnn : n ≠ none := by rw [hn, num_div_some k hmag]; simp
  have hyp : y.rep.p = y.sb.pay := (hb.blocks y List.mem_cons_self).sPay
  have hl2y : y2.rep.len = 1 := by rw [s2.len]; exact hl2
  have hs2y : y2.rep.scale = 0 := by rw [s2.scale]; exact hs2
  simp only [zeroAddr] at hqz
  have hzo : ∀ j, j < 8 → OutHeap (zeroAddr + j) := fun j hj => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, zeroAddr]; omega
  have hzg' : ldv .ld (writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)]) zeroAddr =
      BitVec.ofNat 64 y3.rep.p := by
    rw [ldv_congr .ld fun j hj => imgM_store_miss _ _ (by simp only [zeroAddr, widthOfM] at hj ⊢; omega)]
    rw [ldv_congr .ld fun j hj => hout _ (hzo j hj) (by simp only [slotBytes, zeroAddr, widthOfM] at hj ⊢; omega)
      (by simp only [frameIn, zeroAddr, widthOfM] at hj ⊢; omega)]
    rw [s3.p]; exact hzg
  have hM : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a →
      imgM (writeLog M [(q, 8, BitVec.ofNat 64 y.sb.pay)]) a = imgM Mt0 a := fun a ha hs hf => by
    rw [imgM_store_miss _ _ (by simp only [slotBytes] at hs; omega)]; exact hout a ha hs hf
  refine dv_body (s2 := 0) (z0 := 0) (L0 := y :: L) (x1 := y1) (x2 := y2) (z := y3) hlive cx
    (hk.rebase hfr hyr hnn hM) (by rw [s1.num, s2.num]; exact hn)
    ⟨sv.transport (lo := 104) (top := 208) (hag := fun a h1 h2' => imgM_store_miss _ _ (by omega)),
      hb.out_frame (P := slotBytes q) (fun a ha => imgM_store_miss _ _ (by
        simp only [slotBytes] at ha; omega)) cx.slotOut, fun _ _ _ => rfl⟩
    (List.mem_cons_of_mem _ hy1) hm2
    ⟨Nat.zero_le _, fun j h1 h2 => absurd h2 (by omega), fun i hi => absurd hi (by omega),
      by omega, by rw [s2.ds, hd2]; omega⟩
    (by rw [s1.len, s1.scale, s2.len, s2.scale]; exact hsz)
    (QSlot.num (L1 := []) ⟨by omega, by rw [hyp]; exact ldv_store_hit _ _ _,
      fun _ _ z hz => absurd hz List.not_mem_nil⟩)
    (List.mem_cons_of_mem _ hy3) hzg'
    h2 (by rw [s1.p]; exact h8) (by rw [s2.p]; exact h9) h19 h21 h22 hkp


/-- **After the detour's `bc_free_num (quot)`** at `0x80005ebc`: `n2`'s scale
(zero) reloaded, the quotient stored in the slot, then `dvone_enter`. -/
theorem dvone_after {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 L : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S X Q R0 Mt0 Fr q sp W n)
    (one : DvOne Mt0 L0 Fr x1 x2 z n k)
    (sv : SavedWords M (sp - 208) divSlots R0) (hb : BcHeap S X M H F (y :: L))
    (hfr : Fr L) (hyr : y.rep.refs = 1)
    (hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h18 : R 18 = BitVec.ofNat 64 y.sb.pay)
    (h21 : R 21 = BitVec.ofNat 64 k) (h22 : R 22 = BitVec.ofNat 64 q) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005ebc#64 R M := by
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  obtain ⟨y2, hy2, r2, e2⟩ := one.k2 ⟨one.len2, one.scale2, one.dig2⟩ L hfr
  have s2 := SameRep.of_eq e2
  have hn2 := hb.nums y2 (List.mem_cons_of_mem _ hy2)
  num_facts hn2
  have l8 : ldv .lw M (x2.rep.p + 8) = BitVec.ofNat 64 x2.rep.scale := by
    rw [← s2.p, ← s2.scale]; exact hn2.scale
  have hs2 := one.scale2
  have hp2 := s2.p
  bc_run hlive hS [h9, h18, h22, l8, hs2] at 0x80005954
  all_goals first | exact hq.acc | exact acc_heap hS (by omega) (by omega) | skip
  bc_run hlive hS [] at 0x80005954
  refine dvone_enter hlive cx hk one sv hb hfr hyr hout ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · bsimp [h2]
  · bsimp [h8]
  · bsimp [h9]
  · bsimp []
  · bsimp [h21]
  · bsimp [h22]
  · keeps_tac hkp

/-- **The detour's `bc_free_num (quot)`** at `0x80005eb4`: the slot's old
number loses a reference or is released, then `dvone_after`. -/
theorem dvone_free {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S X Q R0 Mt0 Fr q sp W n)
    (one : DvOne Mt0 L0 Fr x1 x2 z n k)
    (sv : SavedWords M (sp - 208) divSlots R0) (hb : BcHeap S X M H F (y :: L0))
    (hr : QSlot M q L0 Fr) (hyr : y.rep.refs = 1) (hyo : y.Owns)
    (hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h18 : R 18 = BitVec.ofNat 64 y.sb.pay)
    (h21 : R 21 = BitVec.ofNat 64 k) (h22 : R 22 = BitVec.ofNat 64 q) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005eb4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hap := cx.slotApart
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  cases hr with
  | null h0 =>
    bc_run hlive hS [h22, h2] at 0x800048c0
    refine bc_free_num_null hlive hq h0 _ (by bsimp [h22]) (by bsimp []) fun R1 hk1 => ?_
    bsimp []
    exact dvone_after hlive cx hk one sv hb rfl hyr hout (by rw [hk1.get 2]; bsimp [h2])
      (by rw [hk1.get 8]; bsimp [h8]) (by rw [hk1.get 9]; bsimp [h9]) (by rw [hk1.get 18]; bsimp [h18])
      (by rw [hk1.get 21]; bsimp [h21]) (by rw [hk1.get 22]; bsimp [h22])
      ((hk1.mono (by decide)).trans (by keeps_tac hkp))
  | @num L1 L2 xr hr =>
    have hxm : xr ∈ y :: (L1 ++ xr :: L2) := List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
    have hxn := hb.nums xr hxm
    have hxp : heapStart ≤ xr.rep.p ∧ xr.rep.p + 16 ≤ heapEnd :=
      ⟨hxn.shape.pLo, by have := hxn.shape.pHi; omega⟩
    bc_run hlive hS [h22, h2] at 0x800048c0
    have hsf' : StackFrame S (sp - 208) 32 :=
      ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
    have e : FreeEntry S X M H F (y :: L1) L2 xr q (sp - 208) :=
      FreeEntry.of_slot hb hr (hr.noView_cons hb hyo) hq cx.slotOut hsf' (by simp only [heapEnd]; omega)
        (by omega)
    refine bc_free_num_spec hlive e _ (by bsimp [h22]) (by bsimp [h2]) (by bsimp [])
      ⟨fun hx2' R1 Mt1 hk1 hb1 _ hmo => ?_, fun hx1' R1 Mt1 H1 hk1 hrp => ?_⟩
    · bsimp []
      have hag : ∀ a, OutHeap a → ¬ slotBytes q a → imgM Mt1 a = imgM M a := fun a ha hs =>
        hmo a fun hc => by
          rcases hc with hc | hc
          · simp only [refsBytes, OutHeap, heapStart, heapEnd] at hc ha hxp; omega
          · exact hs hc
      exact dvone_after hlive cx hk one
        (sv.transport (lo := 104) (top := 208) (hag := fun a h1 h2' =>
          hag a (cx.stack_out (by omega)) (by simp only [slotBytes]; omega)))
        hb1 (.dec hx2') hyr (fun a ha hs hf => (hag a ha hs).trans (hout a ha hs hf)) (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8])
        (by rw [hk1.get 9]; bsimp [h9]) (by rw [hk1.get 18]; bsimp [h18])
        (by rw [hk1.get 21]; bsimp [h21]) (by rw [hk1.get 22]; bsimp [h22])
        ((hk1.mono (by decide)).trans (by keeps_tac hkp))
    · bsimp []
      have hxb := hb.blocks xr hxm
      have hag : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn (sp - 208) 32 a →
          imgM Mt1 a = imgM M a := fun a ha hs hf => hrp.frame a fun hc => by
        rcases hc with hc | hc | hc | hc | hc
        · exact OutHeap.not_alloc hb.heap ha hc
        · exact ha.1 (live_in_heap hb.heap hxb.sLive hc)
        · exact hs hc
        · exact hf hc
        · exact ha.2.2 hc
      exact dvone_after hlive cx hk one
        (sv.transport (lo := 104) (top := 208) (hag := fun a h1 h2' =>
          hag a (cx.stack_out (by omega)) (by simp only [slotBytes]; omega)
            (by simp only [frameIn]; omega)))
        hrp.heap (.rel hx1') hyr
        (fun a ha hs hf => (hag a ha hs (by simp only [frameIn] at hf ⊢; omega)).trans (hout a ha hs hf))
        (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8])
        (by rw [hk1.get 9]; bsimp [h9]) (by rw [hk1.get 18]; bsimp [h18])
        (by rw [hk1.get 21]; bsimp [h21]) (by rw [hk1.get 22]; bsimp [h22])
        ((hk1.mono (by decide)).trans (by keeps_tac hkp))


/-- **The detour's `memcpy`** from `0x80005ea0` (`a4 = min (scale1, k)`):
`n1`'s first `len1 + a4` digits into the quotient, then `dvone_free`. -/
theorem dvone_copy {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S X Q R0 Mt0 Fr q sp W n)
    (one : DvOne Mt0 L0 Fr x1 x2 z n k)
    (sv : SavedWords M (sp - 208) divSlots R0) (hb : BcHeap S X M H F (y :: L0))
    (hr : QSlot M q L0 Fr) (hyr : y.rep.refs = 1) (hyo : y.Owns)
    (hyl : y.rep.len = x1.rep.len) (hys : y.rep.scale = k)
    (hyz : y.rep.ds = List.replicate (x1.rep.len + k) 0)
    (hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h14 : R 14 = BitVec.ofNat 64 (min x1.rep.scale k))
    (h18 : R 18 = BitVec.ofNat 64 y.sb.pay)
    (h21 : R 21 = BitVec.ofNat 64 k) (h22 : R 22 = BitVec.ofNat 64 q) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005ea0#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hap := cx.slotApart
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hx1 := one.m1
  have hsz := one.size
  have hm1 : x1 ∈ y :: L0 := List.mem_cons_of_mem _ hx1
  have hn1 := hb.nums x1 hm1
  num_facts hn1
  have hyn := hb.nums y List.mem_cons_self
  num_facts hyn
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hval : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by rw [← hyp]; exact hyn.value
  have yp1 := hyn.shape.pLo; have yp2 := hyn.shape.pHi; have yp3 := hyn.shape.pAl
  rw [hyp] at yp1 yp2 yp3
  simp only [heapStart, heapEnd] at yp1 yp2
  have hdl1 := hn1.shape.dsLen
  have ea := addw_ofNat (a := min x1.rep.scale k) (b := x1.rep.len) (by omega)
  bc_run hlive hS [h8, h14, h18, hn1.len, hn1.value, hval, ea] at 0x8000086c
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  have hne : y ≠ x1 := fun e => hb.p_ne hx1 (by rw [e])
  have hdb : y.db ≠ x1.db := hb.head_noView hyo x1 hx1 |>.symm
  have hfa : ∀ a, y.rep.Foot a → x1.rep.Foot a → False := fun a ha hb' =>
    hb.foot_disjoint List.mem_cons_self hm1 hne hdb ha hb'
  have hca : CopyArgs S y.rep.val x1.rep.val (min x1.rep.scale k + x1.rep.len) :=
    ⟨⟨fun i hi => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
        by omega⟩,
      ⟨fun i hi => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
        by omega⟩,
      range_apart fun a h1 h2 h3 h4 => hfa a (.inr ⟨h3, by omega⟩) (.inr ⟨h1, by omega⟩)⟩
  refine memcpy_spec hlive hca _ (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
    fun R3 M3 hk3 hf3 => ?_
  bsimp []
  have hdg := dvOneDs_digits (hn1.shape.dig : Digits x1.rep.ds) (x1.rep.len + min x1.rep.scale k)
    (x1.rep.len + k)
  have hm3 : MemOnly (fun a => y.rep.val ≤ a ∧ a < y.rep.val + y.rep.len + y.rep.scale) M3 M :=
    fun a ha => hf3.rest a (by simp only [not_and, Nat.not_lt] at ha; omega)
  have hb3 := hb.setDigits hyo (ds := dvOneDs x1.rep.ds (x1.rep.len + min x1.rep.scale k)
      (x1.rep.len + k)) (by rw [dvOneDs_length (by omega) (by omega)]; omega) hdg hm3
    fun i hi => by
      rw [dvOneDs_getD (by omega) (by omega)]
      by_cases h : i < x1.rep.len + min x1.rep.scale k
      · rw [if_pos h, hf3.fill i (by omega)]
        exact hn1.digit i (by omega)
      · rw [if_neg h, hf3.rest _ (by omega), hyn.digit i hi, hyz, List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split <;> rfl
  have hag : ∀ a, OutHeap a → imgM M3 a = imgM M a := fun a ha => hm3 a fun h =>
    ha.1 ⟨by simp only [heapStart]; omega, by simp only [heapEnd]; omega⟩
  exact dvone_free hlive cx hk one
    (sv.transport (lo := 104) (top := 208) (hag := fun a h1 h2' => hag a (cx.stack_out (by omega))))
    hb3 (hr.transport fun a ha => hag a (cx.slotOut a ha)) hyr hyo (fun a ha hs hf => (hag a ha).trans (hout a ha hs hf))
    (by rw [hk3.get 2]; bsimp [h2]) (by rw [hk3.get 8]; bsimp [h8]) (by rw [hk3.get 9]; bsimp [h9])
    (by rw [hk3.get 18]; bsimp [h18]) (by rw [hk3.get 21]; bsimp [h21]) (by rw [hk3.get 22]; bsimp [h22])
    ((hk3.mono (by decide)).trans (by keeps_tac hkp))


/-- **`min (scale1, k)`** at `0x80005e90`, then `dvone_copy`. -/
theorem dvone_min {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S X Q R0 Mt0 Fr q sp W n)
    (one : DvOne Mt0 L0 Fr x1 x2 z n k)
    (sv : SavedWords M (sp - 208) divSlots R0) (hb : BcHeap S X M H F (y :: L0))
    (hr : QSlot M q L0 Fr) (hyr : y.rep.refs = 1) (hyo : y.Owns)
    (hyl : y.rep.len = x1.rep.len) (hys : y.rep.scale = k)
    (hyz : y.rep.ds = List.replicate (x1.rep.len + k) 0)
    (hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h18 : R 18 = BitVec.ofNat 64 y.sb.pay)
    (h21 : R 21 = BitVec.ofNat 64 k) (h22 : R 22 = BitVec.ofNat 64 q) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005e90#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := one.size
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ one.m1)
  num_facts hn1
  have t1 := toInt_ofNat_small (k := k) (by omega)
  have t2 := toInt_ofNat_small (k := x1.rep.scale) (by omega)
  bc_run hlive hS [h8, h21, hn1.scale, t1, t2] at 0x80005ea0
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro h
    exact dvone_copy hlive cx hk one sv hb hr hyr hyo hyl hys hyz hout (by bsimp [h2]) (by bsimp [h8])
      (by bsimp [h9]) (by bsimp []; exact congrArg _ (by omega)) (by bsimp [h18]) (by bsimp [h21])
      (by bsimp [h22]) (by keeps_tac hkp)
  · intro h
    bc_run hlive hS [h21] at 0x80005ea0
    exact dvone_copy hlive cx hk one sv hb hr hyr hyo hyl hys hyz hout (by bsimp [h2]) (by bsimp [h8])
      (by bsimp [h9]) (by bsimp [h21]; exact congrArg _ (by omega)) (by bsimp [h18]) (by bsimp [h21])
      (by bsimp [h22]) (by keeps_tac hkp)


/-- **The detour's sign and `memset`** from `0x80005e60` (`bc_new_num`
returned `y`, all zeros): `n1.sign != n2.sign` stored, the `k` fraction
digits from `len1` zeroed, then `dvone_min`. -/
theorem dvone_fill {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z y : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S X Q R0 Mt0 Fr q sp W n)
    (one : DvOne Mt0 L0 Fr x1 x2 z n k)
    (sv : SavedWords M (sp - 208) divSlots R0) (hb : BcHeap S X M H F (y :: L0))
    (hr : QSlot M q L0 Fr) (hrep : y.rep = zeroRep y.sb.pay y.db.pay x1.rep.len k)
    (hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h10 : R 10 = BitVec.ofNat 64 y.sb.pay)
    (h21 : R 21 = BitVec.ofNat 64 k) (h22 : R 22 = BitVec.ofNat 64 q) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005e60#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hap := cx.slotApart
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := one.size
  have hn1 := hb.nums x1 (List.mem_cons_of_mem _ one.m1)
  num_facts hn1
  have hn2 := hb.nums x2 (List.mem_cons_of_mem _ one.m2)
  num_facts hn2
  have hyn := hb.nums y List.mem_cons_self
  num_facts hyn
  have hyp := (hb.blocks y List.mem_cons_self).sPay
  have hval : ldv .ld M (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by rw [← hyp]; exact hyn.value
  have hyl : y.rep.len = x1.rep.len := by rw [hrep]; rfl
  have hys : y.rep.scale = k := by rw [hrep]; rfl
  have hyr : y.rep.refs = 1 := by rw [hrep]; rfl
  have hyz : y.rep.ds = List.replicate (x1.rep.len + k) 0 := by rw [hrep]; rfl
  have hpv : y.rep.ptr = y.rep.val := by rw [hrep]; rfl
  have hyo : y.Owns := by
    show y.rep.ptr ≠ 0
    have := hyn.shape.vLo
    simp only [heapStart] at this; omega
  have yp1 := hyn.shape.pLo; have yp2 := hyn.shape.pHi; have yp3 := hyn.shape.pAl
  rw [hyp] at yp1 yp2 yp3
  simp only [heapStart, heapEnd] at yp1 yp2
  bc_run hlive hS [h8, h9, h10, hn1.sign, hn2.sign, hn1.len, hval, snez_signs] at 0x80000890
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  have hob : OwnedBytes S (y.rep.val + x1.rep.len) k :=
    ⟨fun i hi => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
      by omega⟩
  refine memset_spec hlive hob _ (by bsimp []) (by bsimp [h21]) (by bsimp []) fun R2 M2 hk2 hf2 => ?_
  bsimp [] at hf2 ⊢
  have hbs := BcHeap.setSign (L1 := []) hb (x1.rep.neg != x2.rep.neg) (snezWord_toNat _)
  rw [hyp] at hbs
  simp only [List.nil_append] at hbs
  have hns := hbs.nums _ List.mem_cons_self
  have hm2 : MemOnly (fun a => y.rep.val ≤ a ∧ a < y.rep.val + y.rep.len + y.rep.scale) M2
      (writeLog M [(y.sb.pay, 4, BitVec.ofNat 64 (if (x1.rep.neg != x2.rep.neg) = true then 1 else 0))]) :=
    fun a ha => hf2.rest a (by simp only [not_and, Nat.not_lt] at ha; omega)
  have hb2 := hbs.setDigits (ds := y.rep.ds) hyo (by rw [hyz]; simp [hyl, hys]) (hyn.shape.dig) hm2
    fun i hi => by
      dsimp only at hi ⊢
      by_cases h : x1.rep.len ≤ i
      · rw [show y.rep.val + i = y.rep.val + x1.rep.len + (i - x1.rep.len) by omega,
          hf2.fill _ (by omega), hyz, List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split <;> rfl
      · rw [hf2.rest _ (by omega)]
        exact hns.digit i hi
  have hag : ∀ a, OutHeap a → imgM M2 a = imgM M a := fun a ha => by
    rw [hm2 a fun h => ha.1 ⟨by simp only [heapStart]; omega, by simp only [heapEnd]; omega⟩]
    exact imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
  exact dvone_min (y := { y with rep := { y.rep with neg := x1.rep.neg != x2.rep.neg } }) hlive cx hk one
    (sv.transport (lo := 104) (top := 208) (hag := fun a h1 h2' => hag a (cx.stack_out (by omega))))
    hb2 (hr.transport fun a ha => hag a (cx.slotOut a ha)) hyr hyo hyl hys hyz (fun a ha hs hf => (hag a ha).trans (hout a ha hs hf))
    (by rw [hk2.get 2]; bsimp [h2]) (by rw [hk2.get 8]; bsimp [h8]) (by rw [hk2.get 9]; bsimp [h9])
    (by rw [hk2.get 18]; bsimp [h10]) (by rw [hk2.get 21]; bsimp [h21]) (by rw [hk2.get 22]; bsimp [h22])
    ((hk2.mono (by decide)).trans (by keeps_tac hkp))


/-- **The divide-by-one detour** at `0x80005e54` (`n2 = 1`):
`bc_new_num (len1, k)` for the quotient, then `dvone_fill`. GNU bc 1.07 falls
through from here into the general division. -/
theorem dv_one {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L0 : List NumObj} {Fr : List NumObj → Prop}
    {x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKF live S X Q R0 Mt0 Fr q sp W n)
    (one : DvOne Mt0 L0 Fr x1 x2 z n k) (core : DvCore S X Mt0 M R0 sp W H F L0)
    (hr0 : QSlot Mt0 q L0 Fr)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h21 : R 21 = BitVec.ofNat 64 k)
    (h22 : R 22 = BitVec.ofNat 64 q) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005e54#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have hap := cx.slotApart
  have hq := cx.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => core.heap.heap.own a h1 h2
  have hsz := one.size; have hl1 := one.len1
  have hn1 := core.heap.nums x1 one.m1
  num_facts hn1
  bc_run hlive hS [h8, h21, hn1.len] at 0x80004250
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  have hsf' : StackFrame S (sp - 208) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine bc_new_num_spec hlive core.heap.newHeap hsf' (len := x1.rep.len) (scale := k)
    (by simp only [heapEnd]; omega) (by omega) hl1 _ (by bsimp []) (by bsimp [h21]) (by bsimp [h2])
    (by bsimp [])
    ⟨fun R1 M1 H1 F1 y hk1 hp1 hr1 => ?_, fun R' M' hr2' hout' => ?_⟩
  · bsimp []
    have hb1 := NewNumPost.insert core.heap hp1
    have hag : ∀ a, OutHeap a → ¬ frameIn (sp - 208) 32 a → imgM M1 a = imgM M a := hp1.out
    have hout : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp W a → imgM M1 a = imgM Mt0 a :=
      fun a ha _ hf => (hag a ha (by simp only [frameIn] at hf ⊢; omega)).trans (core.out a ha hf)
    exact dvone_fill hlive cx hk one
      (core.saved.transport (lo := 104) (top := 208) (hag := fun a h1 h2' =>
        hag a (cx.stack_out (by omega)) (by simp only [frameIn]; omega)))
      hb1 (hr0.transport fun a ha => (hag a (cx.slotOut a ha)
          (by simp only [frameIn, slotBytes] at ha ⊢; omega)).trans
            (core.out a (cx.slotOut a ha) (by simp only [frameIn, slotBytes] at ha ⊢; omega))) hp1.rep hout
      (by rw [hk1.get 2]; bsimp [h2]) (by rw [hk1.get 8]; bsimp [h8]) (by rw [hk1.get 9]; bsimp [h9])
      hr1 (by rw [hk1.get 21]; bsimp [h21]) (by rw [hk1.get 22]; bsimp [h22])
      ((hk1.mono (by decide)).trans (by keeps_tac hkp))
  · exact hk.oom R' M' (sp - 208 - 32) (by omega) (by omega) hr2' fun a ha hf =>
      (hout' a ha (by simp only [frameIn] at hf ⊢; omega)).trans (core.out a ha hf)

end

end Dc.Mach
