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


/-- The prologue's first five saved registers. -/
abbrev divPro1 (M : Mem) (sp : Nat) (R : Nat → BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog M
    [(sp - 208 + 184, 8, R 9)]) [(sp - 208 + 168, 8, R 19)]) [(sp - 208 + 192, 8, R 8)])
    [(sp - 208 + 152, 8, R 21)]) [(sp - 208 + 144, 8, R 22)]

/-- The prologue's other eight saved registers. -/
abbrev divPro2 (M : Mem) (sp : Nat) (R : Nat → BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M
    [(sp - 208 + 200, 8, R 1)]) [(sp - 208 + 176, 8, R 18)]) [(sp - 208 + 160, 8, R 20)])
    [(sp - 208 + 136, 8, R 23)]) [(sp - 208 + 128, 8, R 24)]) [(sp - 208 + 120, 8, R 25)])
    [(sp - 208 + 112, 8, R 26)]) [(sp - 208 + 104, 8, R 27)]

/-- The first five slots, most recent first. -/
abbrev divSlots1 : List (Nat × Nat) := [(22, 144), (21, 152), (8, 192), (19, 168), (9, 184)]

theorem divPro1_saved (M : Mem) (sp : Nat) (R : Nat → BitVec 64) :
    SavedWords (divPro1 M sp R) (sp - 208) divSlots1 R :=
  (((((SavedWords.nil M (sp - 208) R).store 9 184).store 19 168).store 8 192).store 21 152).store 22 144

theorem divPro2_saved {M : Mem} {sp : Nat} {R : Nat → BitVec 64}
    (h : SavedWords M (sp - 208) divSlots1 R) : SavedWords (divPro2 M sp R) (sp - 208) divSlots R :=
  (((((((h.store 1 200).store 18 176).store 20 160).store 23 136).store 24 128).store 25 120).store
    26 112).store 27 104

theorem divPro1_frame {M : Mem} {sp : Nat} (R : Nat → BitVec 64) (hsp : 208 ≤ sp) :
    MemOnly (frameIn sp 208) (divPro1 M sp R) M := fun a ha => by
  simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]

theorem divPro2_frame {M : Mem} {sp : Nat} (R : Nat → BitVec 64) (hsp : 208 ≤ sp) :
    MemOnly (frameIn sp 208) (divPro2 M sp R) M := fun a ha => by
  simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]

/-- The registers the prologue's first half may change. -/
abbrev divPro1Clob : List Nat :=
  [2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22, 28, 29, 30, 31]

/-- **`bc_divide`'s prologue, second half** from `0x800058d4`: eight more
saved registers, then `n2` with digits to the zero test, `n2` without to the
`-1` return. -/
theorem dv_pro2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (ha : DivArgs Mt0 L1 L2 xr x1 x2 z n k) (hb : BcHeap S Mt0 H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (sv : SavedWords M (sp - 208) divSlots1 R0)
    (hm : MemOnly (frameIn sp 208) M Mt0)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h10 : R 10 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.len)
    (h12 : R 12 = BitVec.ofNat 64 q) (h13 : R 13 = BitVec.ofNat 64 k)
    (h15 : R 15 = BitVec.ofNat 64 x2.rep.val)
    (h16 : R 16 = BitVec.ofNat 64 (x2.rep.len + x2.rep.scale))
    (h19 : R 19 = BitVec.ofNat 64 x2.rep.scale)
    (hkc : Keeps divPro1Clob R R0) :
    DW live S Q 0x800058d4#64 R M := by
  have h1 := hkc.get 1; have h18 := hkc.get 18; have h20 := hkc.get 20; have h23 := hkc.get 23
  have h24 := hkc.get 24; have h25 := hkc.get 25; have h26 := hkc.get 26; have h27 := hkc.get 27
  have hkp : Keeps divAll R R0 := hkc.mono (by decide)
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := ha.size
  have hn2 := hb.nums x2 ha.m2
  num_facts hn2
  have t1 := toInt_ofNat_small (k := x2.rep.len + x2.rep.scale) (by omega)
  have z0 : (0#64).toInt = 0 := by decide
  have e0 := ofNat_eq_zero_iff (show x2.rep.len + x2.rep.scale < 2 ^ 64 by omega)
  have hpro : MemOnly (frameIn sp 208) (divPro2 M sp R0) Mt0 := fun a ha =>
    (divPro2_frame (M := M) (sp := sp) R0 (by omega) a ha).trans (hm a ha)
  have hb' := hb.out_frame hpro fun a ha => by
    simp only [frameIn, OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha ⊢; omega
  have hfr : ∀ a, ¬ frameIn sp W a → imgM (divPro2 M sp R0) a = imgM Mt0 a := fun a hf =>
    hpro a fun h => hf (by simp only [frameIn] at h ⊢; omega)
  have core : DvCore S Mt0 (divPro2 M sp R0) R0 sp W H F (L1 ++ xr :: L2) :=
    ⟨divPro2_saved sv, hb', fun a _ hf => hfr a hf⟩
  bc_run hlive hS [h2, h1, h18, h20, h23, h24, h25, h26, h27, h16, t1, z0] at 0x80005914 0x80005fac
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · intro hp
    exact dv_scan hlive cx hk ha core hfr hr0 (by omega) (by bsimp [h2]) (by bsimp [h10]) (by bsimp [h9])
      (by bsimp [h11]) (by bsimp [h16]) (by bsimp [h15]) (by bsimp [h15]) (by bsimp [h16])
      (by bsimp [h19]) (by bsimp [h13]) (by bsimp [h12]) (by keeps_tac hkp)
  · intro hp
    bc_run hlive hS [h16, e0] at 0x80005b3c
    · intro h0
      have hnone : n = none := by
        rw [ha.div]
        exact num_div_none k (NumRep.mag_zero_of hn2.shape.dsLen fun j hj => absurd hj (by omega))
      exact dvt_neg hlive cx hk hnone (divPro2_saved sv) (by bsimp [h2]) (by bsimp [])
        (by keeps_tac hkp) hS hfr
    · intro h0; exfalso; omega


/-- **`bc_divide`'s prologue, first half** from `0x800058a8` (`n2` is not
`_zero_`): five saved registers, `n2`'s length, scale and digits, then
`dv_pro2`. -/
theorem dv_pro1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (ha : DivArgs Mt0 L1 L2 xr x1 x2 z n k) (hb : BcHeap S Mt0 H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hkp0 : Keeps [15] R R0)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 q) (h13 : R 13 = BitVec.ofNat 64 k) :
    DW live S Q 0x800058a8#64 R Mt0 := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsz := ha.size
  have hn2 := hb.nums x2 ha.m2
  num_facts hn2
  have h2 : R 2 = BitVec.ofNat 64 sp := by rw [hkp0.get 2]; exact cx.sp0
  have g8 := hkp0.get 8; have g9 := hkp0.get 9; have g19 := hkp0.get 19; have g21 := hkp0.get 21
  have g22 := hkp0.get 22
  have hag : ∀ a, a < heapEnd →
      imgM (writeLog (writeLog Mt0 [(sp - 208 + 184, 8, R0 9)]) [(sp - 208 + 168, 8, R0 19)]) a =
        imgM Mt0 a := fun a ha => by
    simp only [heapEnd] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have l4 : ldv .lw (writeLog (writeLog Mt0 [(sp - 208 + 184, 8, R0 9)]) [(sp - 208 + 168, 8, R0 19)])
      (x2.rep.p + 4) = BitVec.ofNat 64 x2.rep.len := by
    rw [ldv_congr .lw fun j hj => hag _ (by simp only [widthOfM, heapEnd] at hj ⊢; omega)]; exact hn2.len
  have l8 : ldv .lw (writeLog (writeLog Mt0 [(sp - 208 + 184, 8, R0 9)]) [(sp - 208 + 168, 8, R0 19)])
      (x2.rep.p + 8) = BitVec.ofNat 64 x2.rep.scale := by
    rw [ldv_congr .lw fun j hj => hag _ (by simp only [widthOfM, heapEnd] at hj ⊢; omega)]; exact hn2.scale
  have l32 : ldv .ld (writeLog (writeLog Mt0 [(sp - 208 + 184, 8, R0 9)]) [(sp - 208 + 168, 8, R0 19)])
      (x2.rep.p + 32) = BitVec.ofNat 64 x2.rep.val := by
    rw [ldv_congr .ld fun j hj => hag _ (by simp only [widthOfM, heapEnd] at hj ⊢; omega)]; exact hn2.value
  have ea := addw_ofNat (a := x2.rep.len) (b := x2.rep.scale) (by omega)
  bc_run hlive hS [h2, h11, g9, g19, l4, hn2.len, word_sub208] at 0x800058bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [l8, l32, hn2.len, g8, g21, g22, ea] at 0x800058d4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | skip
  exact dv_pro2 hlive cx hk ha hb hr0 (divPro1_saved Mt0 sp R0)
    (divPro1_frame (sp := sp) R0 (by omega)) (by bsimp []) (by bsimp [h10]) (by bsimp [h11])
    (by bsimp []) (by bsimp [h12]) (by bsimp [h13]) (by bsimp []) (by bsimp [ea]) (by bsimp [])
    (by keeps_tac (hkp0.mono (by decide)))

/-- **`bc_divide (n1, n2, quot, scale)`** at `0x8000589c`, for `n1` (a
positive integer length) and `n2` of the heap, the slot `q` holding `xr`,
`_zero_` (`z`, magnitude zero) in the heap: `Num.div n1 n2 scale`'s number in
the slot and `0` (`DivKW.ret`), `-1` for a zero divisor with only the stack
window changed (`DivKW.zero`), or `out_of_memory` (`DivKW.oomW`). -/
theorem bc_divide_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {k : Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (ha : DivArgs Mt0 L1 L2 xr x1 x2 z n k) (hzm : z.rep.num.mag = 0)
    (hb : BcHeap S Mt0 H F (L1 ++ xr :: L2)) (hr0 : ResSlot Mt0 L1 xr q)
    (h10 : R0 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R0 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R0 12 = BitVec.ofNat 64 q) (h13 : R0 13 = BitVec.ofNat 64 k) :
    DW live S Q 0x8000589c#64 R0 Mt0 := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hn2 := hb.nums x2 ha.m2
  num_facts hn2
  have hzn := hb.nums z ha.mz
  num_facts hzn
  have hzg : ldv .ld Mt0 2147601864 = BitVec.ofNat 64 z.rep.p := ha.zero
  have hcst : ∀ b ∈ accAddrs 2147601864 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.consts b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  have e1 := ofNat_eq_iff (show x2.rep.p < 2 ^ 64 by omega) (show z.rep.p < 2 ^ 64 by omega)
  bc_run hlive hS [h11, hzg, e1] at 0x800058a8
  all_goals try (exact hcst)
  · intro he
    have hxz : x2 = z := hb.eq_of_p ha.m2 ha.mz he
    have hnone : n = none := by rw [ha.div, hxz]; exact num_div_none k hzm
    have hal := cx.al
    bc_run hlive hS []
    all_goals first | exact hal | skip
    exact hk.zero hnone _ _ (by keeps_tac Keeps.refl _ _) (by bsimp []) fun _ _ => rfl
  · intro _
    exact dv_pro1 hlive cx hk ha hb hr0 (by keeps_tac Keeps.refl _ _) (by bsimp [h10]) (by bsimp [h11])
      (by bsimp [h12]) (by bsimp [h13])

end

end Dc.Mach
