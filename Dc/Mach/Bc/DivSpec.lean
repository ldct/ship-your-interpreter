import Dc.Mach.Bc.DivOne

/-!
# `bc_divide`'s entry and contract

- `BcHeap.eq_of_p`: two numbers of the heap at one address are one.
- `dv_scan`: from `n2`'s zero test (`0x80005914`) to the first nonzero digit
  (`dv_found`, the detour `dv_one`) or the `-1` return.
- `dv_pro`: the prologue (`0x800058a8`).
- `bc_divide_spec`: `bc_divide (n1, n2, quot, scale)` at `0x8000589c`
  against `Num.div`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

/-- **Two numbers of the heap at one address are one.** -/
theorem BcHeap.eq_of_p {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {x y : NumObj} (h : BcHeap S M H F L) (hx : x ∈ L) (hy : y ∈ L) (hp : x.rep.p = y.rep.p) :
    x = y := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
  have hy' : y ∈ A ++ B := by
    rcases List.mem_append.mp hy with h1 | h1
    · exact List.mem_append_left _ h1
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact absurd h2.symm hne
      · exact List.mem_append_right _ h2
  have hd := ((objBlocks_perm A B x).nodup_iff.mp (List.nodup_append.mp h.distinct).2.1)
  have hsb : x.sb ≠ y.sb := (List.nodup_append.mp hd).2.2 _ x.sb_mem_blocks _
    (List.mem_flatMap.mpr ⟨y, hy', y.sb_mem_blocks⟩)
  have hxb := h.blocks x hx
  have hyb := h.blocks y hy
  have hxs := hxb.sSz; have hys := hyb.sSz
  rw [hxb.sPay, hyb.sPay] at hp
  exact live_apart h.heap hxb.sLive hyb.sLive hsb (a := x.sb.pay)
    ⟨Nat.le_refl _, by simp only [Blk.fin, Blk.pay]; omega⟩
    ⟨by omega, by simp only [Blk.fin, Blk.pay] at hp ⊢; omega⟩

/-- `Num.div` by zero. -/
theorem num_div_none {a b : Num} (k : Nat) (hb : b.mag = 0) : Num.div a b k = none := by
  simp only [Num.div, hb, beq_self_eq_true, if_true]

/-- A number whose digits are all zero has magnitude zero. -/
theorem NumRep.mag_zero_of {o : NumRep} (hl : o.ds.length = o.len + o.scale)
    (h : ∀ j, j < o.len + o.scale → o.ds.getD j 0 = 0) : o.num.mag = 0 := by
  simp only [NumRep.num_eq, ← dval_eq_dvalBE]
  exact (dval_eq_zero_iff _).2 fun j hj => h j (by omega)

theorem word_sub208 {x : Nat} (h : 208 ≤ x) :
    BitVec.ofNat 64 x + 18446744073709551408#64 = BitVec.ofNat 64 (x - 208) := by
  change BitVec.ofNat 64 x + -(208#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le x 208 (by decide) h

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- **`n2`'s zero test** from `0x80005914` (`n2` has digits): the first
nonzero digit (`dv_found`, with the detour `dv_one`), or all zero and `-1`. -/
theorem dv_scan {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (ha : DivArgs Mt0 L1 L2 xr x1 x2 z n k) (core : DvCore S Mt0 M R0 sp W H F (L1 ++ xr :: L2))
    (hfr : ∀ a, ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hr0 : ResSlot Mt0 L1 xr q) (hpos : 0 < x2.rep.len + x2.rep.scale)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.len)
    (h13 : R 13 = BitVec.ofNat 64 (x2.rep.len + x2.rep.scale))
    (h14 : R 14 = BitVec.ofNat 64 x2.rep.val) (h15 : R 15 = BitVec.ofNat 64 x2.rep.val)
    (h16 : R 16 = BitVec.ofNat 64 (x2.rep.len + x2.rep.scale))
    (h19 : R 19 = BitVec.ofNat 64 x2.rep.scale) (h21 : R 21 = BitVec.ofNat 64 k)
    (h22 : R 22 = BitVec.ofNat 64 q) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005914#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => core.heap.heap.own a h1 h2
  have hsz := ha.size
  have hn2 := core.heap.nums x2 ha.m2
  num_facts hn2
  have hd2 : IsDigits x2.rep.ds := hn2.shape.dig
  refine dvz_scan hlive hS hd2 hn2.digit (by omega) (by omega) (by omega)
    (fun R' i0 hi0 hnz hlz kk => ?_) (fun R' hall kk => ?_) (x2.rep.len + x2.rep.scale - 1) 0 R
    (by omega) (fun j hj => absurd hj (Nat.not_lt_zero _)) (Keeps.refl _ _) (by rw [h13, Nat.sub_zero])
    (by rw [h14, Nat.add_zero])
  · have kp : Keeps divAll R' R0 := (kk.mono (by decide)).trans hkp
    exact dv_found hlive cx hk ha.div core ha.m1 ha.m2 hlz hnz hi0 ha.size hr0 ha.mz ha.zero
      (by rw [kk.get 2]; exact h2) (by rw [kk.get 8]; exact h8) (by rw [kk.get 9]; exact h9)
      (by rw [kk.get 11]; exact h11) (by rw [kk.get 15]; exact h15) (by rw [kk.get 16]; exact h16)
      (by rw [kk.get 19]; exact h19) (by rw [kk.get 21]; exact h21) (by rw [kk.get 22]; exact h22) kp
      fun R1 hl hs hd r2 r8 r9 r21 r22 kp1 =>
        dv_one hlive cx hk { ha with len2 := hl, scale2 := hs, dig2 := hd } core hr0 r2 r8 r9 r21 r22 kp1
  · have hnone : n = none := by
      rw [ha.div]; exact num_div_none k (NumRep.mag_zero_of hn2.shape.dsLen hall)
    bc_run hlive hS [] at 0x80005b3c
    exact dvt_neg hlive cx hk hnone core.saved (by bsimp []; rw [kk.get 2]; exact h2) (by bsimp [])
      (by keeps_tac ((kk.mono (by decide)).trans hkp)) hS hfr

end

end Dc.Mach
