import Dc.Mach.DcRefOps
import Dc.Mach.DcStack

/-!
# `dc_dup` (M9)

    dc_dup (dc_data value):
      if (type is neither number nor string) dc_garbage (...);
      return number ? dc_dup_num (value.v.number) : dc_dup_str (value.v.string);

`dc_dup_num`/`dc_dup_str` increment the count and return the datum in
`a0`/`a1` (the type word is read back from a 16-byte frame below `sp`).

- `dc_dup_num_spec`, `dc_dup_str_spec`: over `DcAt.bumpNum`/`DcAt.bumpStr`.
- `dc_dup_spec`: the dispatch; the handle joins `hs`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The registers `dc_dup` may change. -/
abbrev dupClob : List Nat := [10, 11, 12, 13, 14, 15]

/-- A doubleword load reads back the low word of a word store at its address. -/
theorem ld_lo32_sw (M : Mem) (a : Nat) (v : BitVec 64) :
    (ldv .ld (writeLog M [(a, 4, v)]) a).toNat % 2 ^ 32 = v.toNat % 2 ^ 32 := by
  rw [Interp.ldv_ld_imgW, Interp.imgW_lo32, Interp.imgLE_store4_hit]

theorem word_succ (k : Nat) : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
  rw [show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]

/-- Objects with one number replaced by one of its pointer and value. -/
theorem DObjs.sub_swapNum {L1 L2 : List NumObj} {x x' : NumObj} {ss : List StrObj}
    (hp : x'.rep.p = x.rep.p) (hn : x'.rep.num = x.rep.num) :
    DObjs.Sub ⟨L1 ++ x :: L2, ss⟩ ⟨L1 ++ x' :: L2, ss⟩ :=
  ⟨fun y hy => by
    rcases mem_split_cases hy with rfl | hy
    · exact ⟨x', List.mem_append_right _ List.mem_cons_self, hp, hn⟩
    · exact ⟨y, mem_split_of hy, rfl, rfl⟩,
    fun o ho => ⟨o, ho, rfl, rfl⟩⟩

/-- Objects with one string replaced by one of its pointer and text. -/
theorem DObjs.sub_swapStr {L : List NumObj} {A B : List StrObj} {o o' : StrObj}
    (hp : o'.hb.pay = o.hb.pay) (hs : o'.s = o.s) :
    DObjs.Sub ⟨L, A ++ o :: B⟩ ⟨L, A ++ o' :: B⟩ :=
  ⟨fun y hy => ⟨y, hy, rfl, rfl⟩, fun c hc => by
    rcases mem_split_cases hc with rfl | hc
    · exact ⟨o', List.mem_append_right _ List.mem_cons_self, hp, hs⟩
    · exact ⟨c, mem_split_of hc, rfl, rfl⟩⟩

/-- **`dc_dup_num (x)`** at `0x80002ba4`: `n_refs` incremented, `.num p`
returned and added to the handles. -/
theorem dc_dup_num_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F (L1 ++ x :: L2) C G hs st) (hhs : hs.length ≤ 2 ^ 30) {sp : Nat}
    (hsf : StackFrame S sp 16) (hab : heapEnd + 16 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 x.rep.p) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps dupClob R' R → DatRegs (R' 10) (R' 11) (.num x.rep.p) →
      DcAt S M' H F (L1 ++ x.withRefs (x.rep.refs + 1) :: L2) (C.subst x (x.withRefs (x.rep.refs + 1)))
        G (.num x.rep.p :: hs) st → StkOut sp 16 M' M → DW live S Q (R 1) R' M') :
    DW live S Q 0x80002ba4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hb := h.heap.blocks x hx
  have hsz := hb.sSz; have hsp := hb.sPay
  have fbb := h.heap.heap.blk (List.mem_append_right _ hb.sLive)
  have hblo : 2147603920 ≤ x.sb.h := fbb.lo
  have hbhi : x.sb.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : x.sb.h % 16 = 0 := fbb.al
  have hpl : 2147603936 ≤ x.rep.p ∧ x.rep.p + 40 ≤ 2273312768 ∧ x.rep.p % 16 = 0 := by
    rw [hsp]; simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  have hrl := h.numRefs_lt hhs hx
  have hrf := (h.heap.nums x hx).refs
  have wp := word_succ x.rep.refs
  have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (x.rep.refs + 1))) =
      BitVec.ofNat 64 (x.rep.refs + 1) := sxw_ofNat hrl
  bc_run hlive hS [h10, h2, hrf, wp, wq]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hP : ∀ a, (sp - 16 ≤ a ∧ a < sp - 16 + 4) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have h1 := h.outWrite (MemOnly.store M (sp - 16) 4 1#64) hP
  have hv : (BitVec.ofNat 64 (x.rep.refs + 1)).toNat % 2 ^ 32 = x.rep.refs + 1 :=
    toNat_ofNat_mod32 (by omega)
  have h' := h1.bumpNum hhs hv
  refine hk _ _ (Keeps.restore (by rw [h2]; congr 1; omega) (by keeps_tac Keeps.refl _ _))
    ⟨?_, by bsimp []; rfl⟩ h' fun a ho hg hf => ?_
  · bsimp []
    rw [ldv_ld_miss _ _ (by omega), ld_lo32_sw]; rfl
  · have := ho.1; simp only [heapStart, heapEnd] at this
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]

/-- **`dc_dup_str (o)`** at `0x8000397c`: `s_refs` incremented, `.str p`
returned and added to the handles. -/
theorem dc_dup_str_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {A B : List StrObj} {o : StrObj}
    (h : DcAt S M H F L C G hs st) (he : G.strs = A ++ o :: B) (hhs : hs.length ≤ 2 ^ 30) {sp : Nat}
    (hsf : StackFrame S sp 16) (hab : heapEnd + 16 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 o.hb.pay) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps dupClob R' R → DatRegs (R' 10) (R' 11) (.str o.hb.pay) →
      DcAt S M' H F L C (G.withStr A B (o.withRefs (o.refs + 1))) (.str o.hb.pay :: hs) st →
      StkOut sp 16 M' M → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000397c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hom : o ∈ G.strs := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
  have hso := h.view.strs o hom
  have hsz := hso.hsz
  have fbb := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live _ (G.str_mem hom).1))
  have hblo : 2147603920 ≤ o.hb.h := fbb.lo
  have hbhi : o.hb.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : o.hb.h % 16 = 0 := fbb.al
  have hpl : 2147603936 ≤ o.hb.pay ∧ o.hb.pay + 24 ≤ 2273312768 ∧ o.hb.pay % 16 = 0 := by
    simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  have hrl := h.strRefs_lt hhs hom
  have hrf := hso.refs
  have wp := word_succ o.refs
  have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (o.refs + 1))) =
      BitVec.ofNat 64 (o.refs + 1) := sxw_ofNat hrl
  bc_run hlive hS [h10, h2, hrf, wp, wq]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hP : ∀ a, (sp - 16 ≤ a ∧ a < sp - 16 + 4) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have h1 := h.outWrite (MemOnly.store M (sp - 16) 4 2#64) hP
  have hv : (BitVec.ofNat 64 (o.refs + 1)).toNat % 2 ^ 32 = o.refs + 1 :=
    toNat_ofNat_mod32 (by omega)
  have h' := h1.bumpStr he hhs hv
  refine hk _ _ (Keeps.restore (by rw [h2]; congr 1; omega) (by keeps_tac Keeps.refl _ _))
    ⟨?_, by bsimp []; rfl⟩ h' fun a ho hg hf => ?_
  · bsimp []
    rw [ldv_ld_miss _ _ (by omega), ld_lo32_sw]; rfl
  · have := ho.1; simp only [heapStart, heapEnd] at this
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]

/-! ## The dispatch -/

/-- The low words of two doublewords agree. -/
theorem lo32_congr {x y : BitVec 64} (h : x.toNat % 2 ^ 32 = y.toNat % 2 ^ 32) :
    BitVec.extractLsb 31 0 x = BitVec.extractLsb 31 0 y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  simpa using h

/-- `sext.w` of a register whose low word is a small `t`. -/
theorem sxw_lo32 {x : BitVec 64} {t : Nat} (hx : x.toNat % 2 ^ 32 = t) (ht : t < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 x) = BitVec.ofNat 64 t := by
  rw [lo32_congr (y := BitVec.ofNat 64 t) (by rw [hx, toNat_ofNat_mod32 (by omega)])]
  exact sxw_ofNat ht

/-- `addiw r, x, -1` of a register whose low word is a small positive `t`. -/
theorem sxw_pred_lo32 {x : BitVec 64} {t : Nat} (hx : x.toNat % 2 ^ 32 = t) (h1 : 1 ≤ t)
    (ht : t < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (x + 18446744073709551615#64)) =
      BitVec.ofNat 64 (t - 1) := by
  have e : (x + 18446744073709551615#64).toNat % 2 ^ 32 = (BitVec.ofNat 64 (t - 1)).toNat % 2 ^ 32 := by
    rw [toNat_ofNat_mod32 (by omega), BitVec.toNat_add]
    have hm : (2 : Nat) ^ 32 ∣ 2 ^ 64 := ⟨2 ^ 32, by decide⟩
    rw [Nat.mod_mod_of_dvd _ hm, Nat.add_mod, hx]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [lo32_congr e]
  exact sxw_ofNat (by omega)

/-- The ghost's nodes are those of `G`. -/
structure SameNodes (G G' : DcG) : Prop where
  stk : G'.stk = G.stk
  regs : G'.regs = G.regs
  lbuf : G'.lbuf = G.lbuf

/-- **`dc_dup (value)`** at `0x800020a0`: one more reference to the datum
`g`, returned in `a0`/`a1` and added to the handles. -/
theorem dc_dup_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {g : GV} {v : Val}
    (h : DcAt S M H F L C G hs st) (hhs : hs.length ≤ 2 ^ 30) (hv : g.Den ⟨L, G.strs⟩ v) {sp : Nat}
    (hsf : StackFrame S sp 16) (hab : heapEnd + 16 ≤ sp)
    (R : Nat → BitVec 64) (hd : DatRegs (R 10) (R 11) g) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' L' C' G', Keeps dupClob R' R → DatRegs (R' 10) (R' 11) g → SameNodes G G' →
      DcAt S M' H F L' C' G' (g :: hs) st → g.Den ⟨L', G'.strs⟩ v → StkOut sp 16 M' M →
      StrPin G.strs G'.strs hs → DW live S Q (R 1) R' M') :
    DW live S Q 0x800020a0#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have h11 := hd.ptr
  cases g with
  | num p =>
    obtain ⟨x, hx, e1⟩ : ∃ x ∈ L, x.rep.p = p := by
      cases v with
      | num n => obtain ⟨x, hx, e1, -⟩ := hv; exact ⟨x, hx, e1⟩
      | str s => exact hv.elim
    obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hx
    have htg : (R 10).toNat % 2 ^ 32 = 1 := hd.tag
    have wq := sxw_pred_lo32 htg (by decide) (by decide)
    have wr := sxw_lo32 htg (by decide)
    simp only [GV.ptr] at h11
    have wr' : BitVec.signExtend 64 (Sail.BitVec.extractLsb (R 10) 31 0) = _ := wr
    bc_run hlive hS [wq, wr', h11] at 0x80002ba4
    refine st_800020ac hlive ?_
    bsimp [wr']
    bc_run hlive hS [wq, wr', h11] at 0x80002ba4
    refine st_800020bc hlive ?_
    refine dc_dup_num_spec hlive h hhs hsf (by simp only [heapEnd]; omega) _ ?_ ?_ ?_
      fun R' M' hk1 hd' h' hfr => ?_
    · bsimp [h11]; rw [e1]
    · bsimp [h2]
    · bsimp []; exact hal
    subst e1
    exact hk R' M' _ _ G (hk1.trans (by keeps_tac Keeps.refl _ _)) hd' ⟨rfl, rfl, rfl⟩ h'
      (hv.relist (DObjs.sub_swapNum (x := x) (x' := x.withRefs (x.rep.refs + 1)) rfl rfl)) hfr
      (StrPin.refl _ _)
  | str p =>
    obtain ⟨o, ho, e1⟩ : ∃ o ∈ G.strs, o.hb.pay = p := by
      cases v with
      | str s => obtain ⟨o, ho, e1, -⟩ := hv; exact ⟨o, ho, e1⟩
      | num n => exact hv.elim
    obtain ⟨A, B, he⟩ := List.append_of_mem ho
    have htg : (R 10).toNat % 2 ^ 32 = 2 := hd.tag
    have wq := sxw_pred_lo32 htg (by decide) (by decide)
    have wr := sxw_lo32 htg (by decide)
    simp only [GV.ptr] at h11
    have wr' : BitVec.signExtend 64 (Sail.BitVec.extractLsb (R 10) 31 0) = _ := wr
    bc_run hlive hS [wq, wr', h11] at 0x8000397c
    refine st_800020ac hlive ?_
    bsimp [wr']
    bc_run hlive hS [wq, wr', h11] at 0x8000397c
    refine st_800020b8 hlive ?_
    refine dc_dup_str_spec hlive h he hhs hsf (by simp only [heapEnd]; omega) _ ?_ ?_ ?_
      fun R' M' hk1 hd' h' hfr => ?_
    · bsimp [h11]; rw [e1]
    · bsimp [h2]
    · bsimp []; exact hal
    subst e1
    rw [he] at hv
    exact hk R' M' _ _ (G.withStr A B (o.withRefs (o.refs + 1))) (hk1.trans (by keeps_tac Keeps.refl _ _))
      hd' ⟨rfl, rfl, rfl⟩ h' (hv.relist (DObjs.sub_swapStr (o := o) (o' := o.withRefs (o.refs + 1)) rfl rfl)) hfr
      (by rw [he]; exact StrPin.withRefs _ _)

end Dc.Mach
