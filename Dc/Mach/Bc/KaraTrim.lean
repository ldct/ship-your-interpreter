import Dc.Mach.Bc.KaraM1Stage

/-!
# `_bc_rec_mul`'s Karatsuba step: the leading-zero trims

The step trims each of its four views (`u1`, `u0`, `v1`, `v0`) in place: while
the first digit is `0` and `n_len ≥ 2`, `n_value` advances and `n_len`
shrinks.

`BcHeap.advanceAt` is one such step on an object anywhere in the heap's list;
the four site proofs are generated (`scripts/dc/gen_kara_trim.py`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- Inside a 4-byte store's window the image is the byte stored, whatever the
memory underneath. -/
theorem imgM_in4 (M M' : Mem) {b a : Nat} (v : BitVec 64) (ha : b ≤ a ∧ a < b + 4) :
    imgM (writeLog M [(b, 4, v)]) a = imgM (writeLog M' [(b, 4, v)]) a := by
  have e : ∀ m : Mem, writeLog m [(b, 4, v)] = writeMap4 m b (swData v) := fun _ => rfl
  rw [e, e]
  simp only [imgM]
  rcases (show a = b ∨ a = b + 1 ∨ a = b + 2 ∨ a = b + 3 from by omega) with h | h | h | h
  · rw [h, getElem_writeMap4_0, getElem_writeMap4_0]
  · rw [h, getElem_writeMap4_1, getElem_writeMap4_1]
  · rw [h, getElem_writeMap4_2, getElem_writeMap4_2]
  · rw [h, getElem_writeMap4_3, getElem_writeMap4_3]

/-- Inside an 8-byte store's window the image is the byte stored, whatever the
memory underneath. -/
theorem imgM_in8 (M M' : Mem) {b a : Nat} (v : BitVec 64) (ha : b ≤ a ∧ a < b + 8) :
    imgM (writeLog M [(b, 8, v)]) a = imgM (writeLog M' [(b, 8, v)]) a := by
  have e : ∀ m : Mem, writeLog m [(b, 8, v)] = writeMap8 m b (sdData_val v) := fun _ => rfl
  rw [e, e]
  simp only [imgM]
  rcases (show a = b ∨ a = b + 1 ∨ a = b + 2 ∨ a = b + 3 ∨ a = b + 4 ∨ a = b + 5 ∨
      a = b + 6 ∨ a = b + 7 from by omega) with h | h | h | h | h | h | h | h
  · rw [h, getElem_writeMap8_0, getElem_writeMap8_0]
  · rw [h, getElem_writeMap8_1, getElem_writeMap8_1]
  · rw [h, getElem_writeMap8_2, getElem_writeMap8_2]
  · rw [h, getElem_writeMap8_3, getElem_writeMap8_3]
  · rw [h, getElem_writeMap8_4, getElem_writeMap8_4]
  · rw [h, getElem_writeMap8_5, getElem_writeMap8_5]
  · rw [h, getElem_writeMap8_6, getElem_writeMap8_6]
  · rw [h, getElem_writeMap8_7, getElem_writeMap8_7]

/-- Two stores on disjoint windows commute on the memory image. -/
theorem imgM_swap48 (M : Mem) {b1 b2 : Nat} (v1 v2 : BitVec 64)
    (hd : b1 + 4 ≤ b2 ∨ b2 + 8 ≤ b1) (a : Nat) :
    imgM (writeLog (writeLog M [(b1, 4, v1)]) [(b2, 8, v2)]) a
      = imgM (writeLog (writeLog M [(b2, 8, v2)]) [(b1, 4, v1)]) a := by
  by_cases h1 : b1 ≤ a ∧ a < b1 + 4
  · rw [imgM_store_miss (writeLog M [(b1, 4, v1)]) v2 (show a < b2 ∨ b2 + 8 ≤ a by omega)]
    exact imgM_in4 M _ v1 h1
  · by_cases h2 : b2 ≤ a ∧ a < b2 + 8
    · rw [imgM_store_miss (writeLog M [(b2, 8, v2)]) v1 (show a < b1 ∨ b1 + 4 ≤ a by omega)]
      exact imgM_in8 _ M v2 h2
    · rw [imgM_store_miss (writeLog M [(b1, 4, v1)]) v2 (show a < b2 ∨ b2 + 8 ≤ a by omega),
        imgM_store_miss (writeLog M [(b2, 8, v2)]) v1 (show a < b1 ∨ b1 + 4 ≤ a by omega),
        imgM_store_miss M v1 (show a < b1 ∨ b1 + 4 ≤ a by omega),
        imgM_store_miss M v2 (show a < b2 ∨ b2 + 8 ≤ a by omega)]

/-- **One trim step on any object of the heap**: `n_len` lowered, `n_value`
advanced past a leading zero. -/
theorem BcHeap.advanceAt {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (L1 ++ x :: L2))
    (hl : 2 ≤ x.rep.len) {v1 v2 : BitVec 64} (h1 : v1.toNat % 2 ^ 32 = x.rep.len - 1)
    (h2 : v2 = BitVec.ofNat 64 (x.rep.val + 1)) :
    BcHeap S (writeLog (writeLog Mt [(x.rep.p + 4, 4, v1)]) [(x.rep.p + 32, 8, v2)]) H F
      (L1 ++ { x with rep := x.rep.drop 1 } :: L2) := by
  have hx : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hn := h.nums x hx
  have hxb := h.blocks x hx
  have hsp := hxb.sPay; have hsz := hxb.sSz; have hdf := hxb.dFit; have hdl := hxb.dLo
  have hfin : x.sb.fin = x.sb.pay + x.sb.sz := rfl
  have hin : ∀ a, x.rep.p + 4 ≤ a ∧ a < x.rep.p + 40 → x.sb.In a := fun a ha => ⟨by omega, by omega⟩
  have hsep := hn.shape.sep; have hpl := hn.shape.ptrLe
  exact BcHeap.update h rfl rfl rfl ⟨hxb.sLive, hxb.dLive, hxb.sPay, hxb.sSz, hxb.dPay,
      by simp only [NumRep.drop]; omega, by simp only [NumRep.drop]; omega⟩
    (hn.advance hl h1 h2) (P := fun a => x.rep.p + 4 ≤ a ∧ a < x.rep.p + 40)
    (fun a ha => by rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)])
    fun a ha => h.sb_writeOK (hin a ha)

/-- The trim step as the code performs it: `n_value` stored first, then
`n_len`. -/
theorem BcHeap.advanceAt' {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S Mt H F (L1 ++ x :: L2))
    (hl : 2 ≤ x.rep.len) {v1 v2 : BitVec 64} (h1 : v1.toNat % 2 ^ 32 = x.rep.len - 1)
    (h2 : v2 = BitVec.ofNat 64 (x.rep.val + 1)) :
    BcHeap S (writeLog (writeLog Mt [(x.rep.p + 32, 8, v2)]) [(x.rep.p + 4, 4, v1)]) H F
      (L1 ++ { x with rep := x.rep.drop 1 } :: L2) :=
  (h.advanceAt hl h1 h2).congr fun a => (imgM_swap48 Mt v1 v2 (by omega) a).symm

end Dc.Mach
