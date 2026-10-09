import Dc.Mach.Bc.DivAlloc

/-!
# `bc_divide`'s operand buffers (`0x800059d0` to `0x80005a50`)

- `count_rec`: induction on a loop's remaining count with the body taking
  the next iteration only when one remains (the shape of every scan loop).
- `dvn_skip`: the leading-zero skip over `num2` at `0x80005a34`.
- `dvn_head`: `num2`'s first digit at `0x80005a24`.
- `dvn_setup`: `num2` (allocation, copy, sentinel, skip) from `0x800059d0`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

/-- **Counted loops**: a body proving the head at `k` from the head at
`k - 1` (one iteration on) when `k` is a successor proves every head. -/
theorem count_rec {G : Nat → Nat → (Nat → BitVec 64) → Prop}
    (hbody : ∀ k i R, (∀ k', k = k' + 1 → ∀ R', G k' (i + 1) R') → G k i R) :
    ∀ k i R, G k i R := by
  intro k
  induction k with
  | zero => exact fun i R => hbody 0 i R fun k' h => absurd h (by omega)
  | succ k ih =>
    intro i R
    refine hbody (k + 1) i R fun k' h R' => ?_
    rw [show k' = k by omega]
    exact ih (i + 1) R'

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- **The leading-zero skip** at `0x80005a34` over `num2` (`while (*n2ptr == 0)
{ n2ptr++; len2--; }`): digits `0 … i` zero, `s8` at digit `i`, `s7 = len2 - i`;
the first nonzero digit `z0` ends it at `0x80005a50` with `s8` at `z0`,
`s7 = len2 - z0`, `a6 = s11 = len2 - z0 + 1`. -/
theorem dvn_skip {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {Rb : Nat → BitVec 64} (hS : HeapOwn S) {ds : List Nat} (hd : IsDigits ds)
    {N0 z0 len2 : Nat} (hb : ∀ i, i ≤ z0 → imgM M (N0 + i) = BitVec.ofNat 8 (ds.getD i 0))
    (hz : ∀ i, i < z0 → ds.getD i 0 = 0) (hnz : ds.getD z0 0 ≠ 0) (hzl : z0 < len2) (hl2 : len2 < 2 ^ 30)
    (hlo : 2147603920 ≤ N0) (hhi : N0 + len2 ≤ 2273312768)
    (hexit : ∀ R', Keeps [15, 16, 23, 24, 27] R' Rb → R' 24 = BitVec.ofNat 64 (N0 + z0) →
      R' 23 = BitVec.ofNat 64 (len2 - z0) → R' 16 = BitVec.ofNat 64 (len2 - z0 + 1) →
      R' 27 = BitVec.ofNat 64 (len2 - z0 + 1) → DW live S Q 0x80005a50#64 R' M) :
    ∀ k i R, i + 1 + k = z0 → Keeps [15, 16, 23, 24, 27] R Rb →
      R 24 = BitVec.ofNat 64 (N0 + i) → R 23 = BitVec.ofNat 64 (len2 - i) →
      DW live S Q 0x80005a34#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  refine count_rec fun k i R ih hi kk h24 h23 => ?_
  have hl := lbu_digit (hd.getD (i + 1)) (hb (i + 1) (by omega))
  have hdl := hd.getD (i + 1)
  have e1 : BitVec.ofNat 64 (N0 + i) + 1#64 = BitVec.ofNat 64 (N0 + (i + 1)) := by
    rw [show (1#64) = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat]; congr 1
  have e2 := subw_ofNat_le (a := len2 - i) (b := 1) (by omega) (by omega)
  bc_run hlive hS [h24, h23, hl, e1] at 0x80005a48
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  · intro h0
    bsimp [ofNat_eq_zero_iff (show ds.getD (i + 1) 0 < 2 ^ 64 by omega)] at h0
    rcases k with _ | k
    · exact absurd h0 (by rw [show i + 1 = z0 by omega]; exact hnz)
    exact ih k rfl _ (by omega) (by keeps_tac kk) (by bsimp []; try exact congrArg _ (by omega)) (by bsimp []; try exact congrArg _ (by omega))
  · intro h0
    bsimp [ofNat_eq_zero_iff (show ds.getD (i + 1) 0 < 2 ^ 64 by omega)] at h0
    have hiz : i + 1 = z0 := by
      rcases Nat.lt_or_ge (i + 1) z0 with h | h
      · exact absurd (hz _ h) h0
      · omega
    subst hiz
    have e3 : BitVec.ofNat 64 (len2 - i) <<< 32 >>> 32 = BitVec.ofNat 64 (len2 - i) := shl_shr32 (by omega)
    bc_run hlive hS [e3] at 0x80005a50
    exact hexit _ (by keeps_tac kk) (by bsimp []; try exact congrArg _ (by omega)) (by bsimp []; try exact congrArg _ (by omega))
      (by bsimp []; try exact congrArg _ (by omega)) (by bsimp []; try exact congrArg _ (by omega))

/-- **`num2`'s first digit** at `0x80005a24`: a nonzero first digit goes
straight to `0x80005a50`, a zero one enters the skip `dvn_skip`. -/
theorem dvn_head {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {sp W : Nat} (cx : DvCtx S sp W) (hS : HeapOwn S)
    {ds : List Nat} (hd : IsDigits ds)
    {N0 z0 len2 : Nat} (hb : ∀ i, i ≤ z0 → imgM M (N0 + i) = BitVec.ofNat 8 (ds.getD i 0))
    (hz : ∀ i, i < z0 → ds.getD i 0 = 0) (hnz : ds.getD z0 0 ≠ 0) (hzl : z0 < len2) (hl2 : len2 < 2 ^ 30)
    (hlo : 2147603920 ≤ N0) (hhi : N0 + len2 ≤ 2273312768)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h19 : R 19 = BitVec.ofNat 64 N0)
    (h23 : R 23 = BitVec.ofNat 64 len2) (h27 : R 27 = BitVec.ofNat 64 (len2 + 1))
    (m8 : ldv .ld M (sp - 208 + 8) = BitVec.ofNat 64 (len2 + 1))
    (hexit : ∀ R', Keeps [14, 15, 16, 23, 24, 27] R' R → R' 24 = BitVec.ofNat 64 (N0 + z0) →
      R' 23 = BitVec.ofNat 64 (len2 - z0) → R' 16 = BitVec.ofNat 64 (len2 - z0 + 1) →
      R' 27 = BitVec.ofNat 64 (len2 - z0 + 1) → DW live S Q 0x80005a50#64 R' M) :
    DW live S Q 0x80005a24#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hd0 := hb 0 (by omega)
  rw [Nat.add_zero] at hd0
  have hl0 := lbu_digit (hd.getD 0) hd0
  have hdl := hd.getD 0
  bc_run hlive hS [h2, h19, hl0, m8] at 0x80005a50 0x80005a34
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | skip
  · intro h0
    have hq := ofNat_eq_zero_iff (show ds.getD 0 0 < 2 ^ 64 by omega)
    replace h0 : ds.getD 0 0 ≠ 0 := fun e => h0 (hq.mpr e)
    have hz0 : z0 = 0 := by
      rcases Nat.eq_zero_or_pos z0 with h | h
      · exact h
      · exact absurd (hz 0 h) h0
    subst hz0
    exact hexit _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp [h23]) (by bsimp [])
      (by bsimp [h27])
  · intro h0
    have hq := ofNat_eq_zero_iff (show ds.getD 0 0 < 2 ^ 64 by omega)
    replace h0 : ds.getD 0 0 = 0 := hq.mp (Classical.not_not.mp h0)
    have hzp : 0 < z0 := by
      rcases Nat.eq_zero_or_pos z0 with h | h
      · subst h; exact absurd h0 hnz
      · exact h
    refine dvn_skip hlive hS hd hb hz hnz hzl hl2 hlo hhi ?_
      (z0 - 1) 0 _ (by omega) (Keeps.refl _ _) (by bsimp []) (by bsimp [h23])
    intro R' kk e24 e23 e16 e27
    exact hexit R' ((kk.mono (by decide) : Keeps [14, 15, 16, 23, 24, 27] R' _).trans
      (by keeps_tac Keeps.refl _ _)) e24 e23 e16 e27

/-- The frame, the number heap and `num1` (`b1`) before `num2` is allocated. -/
structure DvBuf1 (S : Nat → Prop) (Mt0 M : Mem) (R0 : Nat → BitVec 64) (sp W : Nat) (D : DvData)
    (H : Heap) (F : List Blk) (Lh : List NumObj) : Prop extends DvCore S Mt0 M R0 sp W H F Lh where
  b1l : D.b1 ∈ H.live
  b1n : D.b1 ∉ F ++ objBlocks Lh
  pPay : D.P = D.b1.pay
  pIn : ∀ i, i < D.xs.length → D.b1.In (D.P + i)

/-- Two byte ranges sharing no byte are apart. -/
theorem range_apart {s d n : Nat} (h : ∀ a, s ≤ a → a < s + n → d ≤ a → a < d + n → False) :
    s + n ≤ d ∨ d + n ≤ s := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · omega
  rcases Nat.lt_or_ge s d with hl | hl
  · exact .inl (Nat.le_of_not_lt fun h' => h d (by omega) h' (Nat.le_refl d) (by omega))
  · exact .inr (Nat.le_of_not_lt fun h' => h s (Nat.le_refl s) (by omega) hl h')

/-- **`num2`** from `0x800059d0`: `len2 = n2->n_len + scale2`, `malloc (len2 + 1)`,
`memcpy (num2, n2->n_value, len2)`, the zero sentinel, the leading-zero skip
to the first nonzero digit `z0`, landing at `0x80005a50`. -/
theorem dvn_setup {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {x2 : NumObj} {s2 z0 : Nat}
    (cx : DvCtx S sp W) (b1 : DvBuf1 S Mt0 M R0 sp W D H F Lh) (hx2 : x2 ∈ Lh)
    (hs2 : s2 ≤ x2.rep.scale) (hz : ∀ i, i < z0 → x2.rep.ds.getD i 0 = 0)
    (hnz : x2.rep.ds.getD z0 0 ≠ 0) (hzl : z0 < x2.rep.len + s2)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h9 : R 9 = BitVec.ofNat 64 x2.rep.p)
    (h19 : R 19 = BitVec.ofNat 64 s2)
    (hoom : ∀ R' Mt' sp', sp - W ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
      (∀ a, OutHeap a → ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) →
      DW live S Q 0x80002bcc#64 R' Mt')
    (hnext : ∀ R' M' H' b2, DvBufs S Mt0 M' R0 sp W
        { D with b2 := b2, N := b2.pay + z0, L := x2.rep.len + s2 - z0 } H' F Lh →
      (∀ a, D.b1.In a → imgM M' a = imgM M a) →
      (∀ i, i < x2.rep.len + s2 → imgM M' (b2.pay + i) = BitVec.ofNat 8 (x2.rep.ds.getD i 0)) →
      imgM M' (b2.pay + (x2.rep.len + s2)) = 0#8 →
      R' 24 = BitVec.ofNat 64 (b2.pay + z0) → R' 23 = BitVec.ofNat 64 (x2.rep.len + s2 - z0) →
      R' 16 = BitVec.ofNat 64 (x2.rep.len + s2 - z0 + 1) →
      R' 27 = BitVec.ofNat 64 (x2.rep.len + s2 - z0 + 1) →
      R' 19 = BitVec.ofNat 64 b2.pay → Keeps [1, 10, 11, 12, 13, 14, 15, 16, 19, 20, 23, 24, 27] R' R →
      DW live S Q 0x80005a50#64 R' M') :
    DW live S Q 0x800059d0#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => b1.heap.heap.own a h1 h2
  have hn2 := b1.heap.nums x2 hx2
  num_facts hn2
  have hp2 := (b1.heap.blocks x2 hx2).sPay
  have e1 := addw_ofNat (a := x2.rep.len) (b := s2) (by omega)
  have e2 := sxw_ofNat (k := x2.rep.len + s2 + 1) (by omega)
  have e3 := shl_shr32 (n := x2.rep.len + s2 + 1) (by omega)
  bc_run hlive hS [h2, h9, h19, hn2.len, e1, e2, e3] at 0x8000096c
  all_goals first | exact acc_heap hS (by omega) (by omega) | exact frame_acc hsf (by omega) (by omega) | skip
  have c1 := b1.toDvCore.slots cx.above (by omega)
    (M' := writeLog M [(sp - 208 + 8, 8, BitVec.ofNat 64 (x2.rep.len + s2 + 1))])
    fun a ha => by simp (disch := omega) only [imgM_store_miss]
  have b1' : DvBuf1 S Mt0 (writeLog M [(sp - 208 + 8, 8, BitVec.ofNat 64 (x2.rep.len + s2 + 1))])
      R0 sp W D H F Lh := { b1 with toDvCore := c1 }
  refine malloc_spec hlive b1'.heap.heap (n := x2.rep.len + s2 + 1) (by omega) _ (by bsimp [])
    (by bsimp []) fun R1 M1 H1 hk1 hpost => ?_
  bsimp []
  have hMa : ∀ a, OutHeap a → imgM M1 a =
      imgM (writeLog M [(sp - 208 + 8, 8, BitVec.ofNat 64 (x2.rep.len + s2 + 1))]) a := fun a ho =>
    hpost.frame a (OutHeap.not_alloc b1'.heap.heap ho)
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk1.get 2]; bsimp [h2]
  cases hres : hpost.res with
  | null e1 e2 e3 =>
    iterate 2 all_goals (try bc_run hlive hS [e1, q2] at 0x80002bcc)
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact hoom _ _ (sp - 208) (by omega) (by omega) (by bsimp [q2]) fun a ha hf => by
      rw [hMa a ha]
      simp only [frameIn] at hf
      simp (disch := omega) only [imgM_store_miss]
      exact b1.out a ha (by simp only [frameIn]; omega)
  | block b2 e1 e2 e3 e4 e5 =>
    have hp' : MallocPost S _ M1 H H1 (x2.rep.len + s2 + 1) (BitVec.ofNat 64 b2.pay) := e1 ▸ hpost
    have hb2l : b2 ∈ H1.live := by rw [e3]; exact List.mem_cons_self
    have hne := hp'.pay_ne hb2l
    have fbb := hpost.inv.blk (List.mem_append_right _ hb2l)
    have hb2lo := fbb.lo; have hb2t := fbb.top; have hb2f := fbb.fin
    have hbp : b2.pay = b2.h + 16 := rfl
    have hbf : b2.fin = b2.h + 16 + b2.sz := rfl
    simp only [heapStart] at hb2lo
    simp only [heapEnd] at hb2t
    have hb1 := b1'.heap.malloc hp'
    have hn2' := hb1.nums x2 hx2
    have h91 : R1 9 = BitVec.ofNat 64 x2.rep.p := by rw [hk1.get 9]; bsimp [h9]
    have hv1 : ldv .ld M1 (x2.rep.p + 32) = BitVec.ofNat 64 x2.rep.val := hn2'.value
    have hsh : BitVec.ofNat 64 (x2.rep.len + s2) <<< 32 >>> 32 = BitVec.ofNat 64 (x2.rep.len + s2) :=
      shl_shr32 (by omega)
    bc_run hlive hS [e1, q2, h91, hv1, hsh] at 0x8000086c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | skip
    · intro hc; exact absurd hc hne
    intro _
    have l8 : ldv .ld M1 (sp - 208 + 8) = BitVec.ofNat 64 (x2.rep.len + s2 + 1) := by
      rw [ldv_congr .ld fun j hj => hMa _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))]
      simp (disch := omega) only [ldv_store_hit]
    have r20 : R1 20 = BitVec.ofNat 64 (x2.rep.len + s2) := by rw [hk1.get 20]; bsimp []
    bc_run hlive hS [l8, r20, h91, hv1, hsh, q2] at 0x8000086c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | skip
    have hbp' : b2.pay = b2.h + 16 := rfl
    have hbf' : b2.fin = b2.h + 16 + b2.sz := rfl
    have hlo2 : 2147603920 ≤ b2.h := fbb.lo
    have hhi2 : b2.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
    have hca : CopyArgs S b2.pay x2.rep.val (x2.rep.len + s2) :=
      ⟨⟨fun i hi => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
          by omega⟩,
        ⟨fun i hi => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
          by omega⟩,
        range_apart fun a h1 h2 h3 h4 => b1'.heap.foot_not_alloc hx2 (a := a) (.inr ⟨h1, by omega⟩)
          (e5 a (by omega) (by omega))⟩
    refine memcpy_spec hlive hca _ (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
      fun R2 M2 hk2 hf => ?_
    bsimp []
    have hfill : ∀ i, i < x2.rep.len + s2 → imgM M2 (b2.pay + i) = BitVec.ofNat 8 (x2.rep.ds.getD i 0) :=
      fun i hi => by
        rw [hf.fill i hi]
        simp (disch := omega) only [imgM_store_miss]
        exact hn2'.digit i (by omega)
    have hst : ∀ a, (a < b2.pay ∨ b2.pay + (x2.rep.len + s2) ≤ a) → imgM M2 a = imgM
        (writeLog M1 [(sp - 208 + 8, 8, BitVec.ofNat 64 (x2.rep.len + s2 + 1))]) a := hf.rest
    have m8 : ldv .ld M2 (sp - 208 + 8) = BitVec.ofNat 64 (x2.rep.len + s2 + 1) := by
      rw [ldv_congr .ld fun j hj => hst _ (.inr (by simp only [widthOfM] at hj; omega))]
      simp (disch := omega) only [ldv_store_hit]
    have q20 : R2 20 = BitVec.ofNat 64 (b2.pay + (x2.rep.len + s2)) := by rw [hk2.get 20]; bsimp []
    have q19 : R2 19 = BitVec.ofNat 64 b2.pay := by rw [hk2.get 19]; bsimp []
    have q2' : R2 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk2.get 2]; bsimp [q2]
    bc_run hlive hS [q20, q19, q2'] at 0x80005a24
    all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | skip
    have hbp2 : b2.pay = b2.h + 16 := rfl
    have hbf2 : b2.fin = b2.h + 16 + b2.sz := rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    generalize hM3 : writeLog M2 [(b2.pay + (x2.rep.len + s2), 1, 0#64)] = M3
    have m3 : ∀ a, a ≠ b2.pay + (x2.rep.len + s2) → imgM M3 a = imgM M2 a := fun a h => by
      rw [← hM3]; simp (disch := omega) only [imgM_store_miss]
    have hsent : imgM M3 (b2.pay + (x2.rep.len + s2)) = 0#8 := by rw [← hM3, imgM_sb, sbData_eq]; rfl
    have hdig : ∀ i, i < x2.rep.len + s2 → imgM M3 (b2.pay + i) = BitVec.ofNat 8 (x2.rep.ds.getD i 0) :=
      fun i hi => (m3 _ (by omega)).trans (hfill i hi)
    -- bytes off `num2` and the slot word are those at `malloc`'s return
    have m31 : ∀ a, ¬ b2.In a → ¬ (sp - 208 + 8 ≤ a ∧ a < sp - 208 + 16) → imgM M3 a = imgM M1 a :=
      fun a h1 h2 => by
        simp only [Blk.In, Blk.fin, Blk.pay] at h1
        rw [m3 a (by omega), hst a (by omega)]
        simp (disch := omega) only [imgM_store_miss]
    have core : DvCore S Mt0 M3 R0 sp W H1 F Lh :=
      { saved := b1'.saved.transport (lo := 104) (top := 208) (hag := fun a h1 h2 => by
          rw [m31 a (by simp only [Blk.In, Blk.fin, Blk.pay]; omega) (by omega)]
          exact hMa a (outHeap_of_ge (by simp only [heapEnd]; omega)))
        heap := hb1.scratch hb2l (b1'.heap.fresh_not_owned (b := b2) (by omega) e5) hb2l
          (b1'.heap.fresh_not_owned (b := b2) (by omega) e5) fun a h =>
            m31 a (fun h' => h (.inl h')) (fun h' => h (.inr (.inr (by simp only [heapEnd]; omega))))
        out := fun a ho hf => by
          have hoh := ho.1
          simp only [heapStart, heapEnd] at hoh
          simp only [frameIn] at hf
          rw [m31 a (by simp only [Blk.In, Blk.fin, Blk.pay]; omega) (by omega), hMa a ho]
          simp (disch := omega) only [imgM_store_miss]
          exact b1.out a ho (by simp only [frameIn]; omega) }
    have hb12 : D.b1 ≠ b2 := fresh_ne_live (b := b2) b1'.heap.heap b1.b1l (by omega) e5
    have bfs : DvBufs S Mt0 M3 R0 sp W
        { D with b2 := b2, N := b2.pay + z0, L := x2.rep.len + s2 - z0 } H1 F Lh :=
      { toDvCore := core
        b1l := hp'.res.live_mono b1.b1l
        b2l := hb2l
        b1n := b1.b1n
        b2n := b1'.heap.fresh_not_owned (b := b2) (by omega) e5
        b12 := hb12
        pPay := b1.pPay
        pIn := b1.pIn
        nIn := fun i hi => by simp only [Blk.In, Blk.fin, Blk.pay] at hi ⊢; omega }
    have hkb1 : ∀ a, D.b1.In a → imgM M3 a = imgM M a := fun a ha => by
      have hap := live_apart hpost.inv (hp'.res.live_mono b1.b1l) hb2l hb12 ha
      have hin := (live_in_heap b1.heap.heap b1.b1l ha).2
      simp only [heapEnd] at hin
      rw [m31 a (fun h => hap h) (by omega), hpost.frame a (live_not_alloc b1'.heap.heap b1.b1l ha)]
      simp (disch := omega) only [imgM_store_miss]
    have m8' : ldv .ld M3 (sp - 208 + 8) = BitVec.ofNat 64 (x2.rep.len + s2 + 1) := by
      rw [ldv_congr .ld fun j hj => m3 _ (by simp only [widthOfM] at hj; omega)]; exact m8
    have r23 : R2 23 = BitVec.ofNat 64 (x2.rep.len + s2) := by rw [hk2.get 23]; bsimp []
    have r27 : R2 27 = BitVec.ofNat 64 (x2.rep.len + s2 + 1) := by
      rw [hk2.get 27]; bsimp [hk1.get 27]
    have hK : Keeps [1, 10, 11, 12, 13, 14, 15, 16, 19, 20, 23, 24, 27] R2 R :=
      (hk2.mono (by decide)).trans (by
        keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
    exact dvn_head hlive cx hS hn2.shape.dig (N0 := b2.pay) (fun i hi => hdig i (by omega)) hz hnz hzl
      (by omega) (by omega) (by omega) q2' q19 r23 r27 m8' fun R' kk e24 e23 e16 e27 =>
        hnext R' M3 H1 b2 bfs hkb1 hdig hsent e24 e23 e16 e27 (by rw [kk.get 19 (by decide)]; exact q19)
          ((kk.mono (by decide)).trans hK)

end

end Dc.Mach
