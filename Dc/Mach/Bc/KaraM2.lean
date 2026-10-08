import Dc.Mach.Bc.KaraM3

/-!
# `_bc_rec_mul`'s Karatsuba step: `m2 = d1 · d2`

From `0x80005050`: `bc_is_zero (d1)`, `bc_is_zero (d2)`; either zero, `m2`
is a copy of `_zero_` (`0x800054a8`), else `_bc_rec_mul (d1, d2, &m2)`
(`0x800050cc`, by `RmIH`); then `m3` (`kara_m3`). The stage is `kara_m2stage`.

- `KM2`: the step's state before `m2`: `KM3` without `m2`'s slot, with
  `&_zero_` in `s2` and the digit counts of `d1` (at `sp`) and `d2` (`a7`).
- `GlobAgree`: the words of `mul_base_digits` and `_zero_` unchanged.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- The words of `mul_base_digits` and `_zero_` unchanged. -/
def GlobAgree (M' M : Mem) : Prop :=
  ∀ a, (mulBaseAddr ≤ a ∧ a < mulBaseAddr + 4) ∨ (zeroAddr ≤ a ∧ a < zeroAddr + 8) →
    imgM M' a = imgM M a

theorem GlobAgree.zero {M M' : Mem} {z : NumObj} {k : Nat} (hg : GlobAgree M' M) (h : KZero M z k) :
    KZero M' z k :=
  { h with
    glob := (ldv_congr .ld fun j hj => hg _ (.inr (by simp only [widthOfM] at hj; omega))).trans h.glob }

theorem GlobAgree.mulBase {M M' : Mem} (hg : GlobAgree M' M) {v : BitVec 64}
    (h : ldv .lw M mulBaseAddr = v) : ldv .lw M' mulBaseAddr = v :=
  (ldv_congr .lw fun j hj => hg _ (.inl (by simp only [widthOfM] at hj; omega))).trans h

theorem GlobAgree.trans {M1 M2 M3 : Mem} (h1 : GlobAgree M3 M2) (h2 : GlobAgree M2 M1) :
    GlobAgree M3 M1 := fun a ha => (h1 a ha).trans (h2 a ha)

/-- Stores at or above the heap keep the globals. -/
theorem GlobAgree.store {M : Mem} {a w : Nat} (v : BitVec 64) (ha : 2147603920 ≤ a) :
    GlobAgree (writeLog M [(a, w, v)]) M := fun b h =>
  imgM_store_miss _ _ (by simp only [zeroAddr, mulBaseAddr] at h; omega)

/-- A run that changes only the heap, the allocator's words and a frame
above the heap keeps the globals. -/
theorem GlobAgree.call {M M' : Mem} {qs sp' W' : Nat} (hq : 2147603920 ≤ qs)
    (hsp : 2147603920 + W' ≤ sp')
    (hout : ∀ a, OutHeap a → ¬ slotBytes qs a → ¬ frameIn sp' W' a → imgM M' a = imgM M a) :
    GlobAgree M' M := fun a h => by
  simp only [mulBaseAddr, zeroAddr] at h
  exact hout a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
    (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)

theorem KZero.mono {M : Mem} {z : NumObj} {k k' : Nat} (h : KZero M z k) (hk : k' ≤ k) :
    KZero M z k' :=
  { h with room := by have := h.room; omega }

/-- The step's state before `m2`. -/
structure KM2 (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W n la lb : Nat)
    (z : NumObj) (hu1 hu0 hv1 hv0 hd1 hd2 hm1 : Hd) (fl : Bool) : Prop where
  st : KAt S M0 M R0 R sp q W
  tr : KTailRegs z hu1 hu0 hv1 hv0 hd1 hd2 q n R
  m1 : ldv .ld M (sp - 192 + 40) = BitVec.ofNat 64 (Hd.p z hm1)
  s6 : R 22 = BitVec.ofNat 64 (la + lb)
  s10 : R 26 = BitVec.ofNat 64 (if fl then 1 else 0)
  s2 : R 18 = BitVec.ofNat 64 zeroAddr
  l1 : ldv .ld M (sp - 192) = BitVec.ofNat 64 (Hd.o z hd1).rep.len
  l2 : R 17 = BitVec.ofNat 64 (Hd.o z hd2).rep.len

/-- `KM2` through register changes off the step's registers. -/
theorem KM2.keeps {S : Nat → Prop} {M0 M : Mem} {R0 R R' : Nat → BitVec 64}
    {sp q W n la lb : Nat} {z : NumObj} {hu1 hu0 hv1 hv0 hd1 hd2 hm1 : Hd} {fl : Bool}
    (pk : KM2 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 fl)
    {ks : List Nat} (kk : Keeps ks R' R)
    (hs : ∀ r ∈ [2, 8, 9, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], r ∉ ks := by decide)
    (hsub : ∀ r ∈ ks, r ∈ rmAll := by decide) :
    KM2 S M0 M R0 R' sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 fl :=
  ⟨⟨pk.st.rm.keeps (kk.mono hsub) (kk _ (hs 2 (by simp))), pk.st.saved2⟩,
    pk.tr.keeps kk fun r hr => hs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega), pk.m1,
    (kk _ (hs 22 (by simp))).trans pk.s6, (kk _ (hs 26 (by simp))).trans pk.s10,
    (kk _ (hs 18 (by simp))).trans pk.s2, pk.l1, (kk _ (hs 17 (by simp))).trans pk.l2⟩

/-- **`m2` is a copy of `_zero_`** (`0x800054a8`, `d1` or `d2` zero): its
pointer in `m2`'s slot and one more reference; then `m3` (`kara_m3`). -/
theorem kara_m2zero {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H : Heap} {F : List Blk} {fl : Bool}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hv0 hm1 hd1 hd2 : Hd} {hs : List Hd}
    (pk : KM2 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 fl)
    (hb : BcHeap S M H F (KList [] hs A B z))
    (hpm : ∀ h2 h3 : Hd, (h3 :: h2 :: hs).Perm (kHs hu1 hu0 hv1 hm1 hv0 h2 h3 hd1 hd2))
    (hown : HdOwned A B z hs) (hok : HdOK hs) (hu0m : hu0 ∈ hs) (hv0m : hv0 ∈ hs)
    (kz : KZero M z (zeroCount hs + 1 + (4 * ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len) + 8)))
    (h12 : R 12 = BitVec.ofNat 64 z.rep.p) (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hN : (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ N)
    (hW : rmStack ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len) + 192 ≤ W)
    (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (hm1z : fl = true → hdVal (Hd.o z hm1) = 0)
    (hfit1 : fl = false → 2 * n + valCount (Hd.o z hm1).rep ≤ la + lb + 1)
    (hfit3 : n + (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ la + lb + 1)
    (hw1 : fl = false → 1 ≤ (Hd.o z hm1).rep.len)
    (hu0p : 1 ≤ (Hd.o z hu0).rep.len) (hv0p : 1 ≤ (Hd.o z hv0).rep.len)
    (hz0 : hdVal (Hd.o z hd1) * hdVal (Hd.o z hd2) = 0)
    (hv : KFillVal (hdVal (Hd.o z hm1)) (hdVal (Hd.o z hd1) * hdVal (Hd.o z hd2))
      (hdVal (Hd.o z hu0) * hdVal (Hd.o z hv0)) (10 ^ n)
      (kUV u v la lb) (la + lb + 1) ((Hd.o z hd1).rep.neg != (Hd.o z hd2).rep.neg)) :
    DW live S Q 0x800054a8#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hzm : z.withRefs (z.rep.refs + zeroCount hs) ∈ KList [] hs A B z :=
    List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums _ hzm
  have hrf : ldv .lw M (z.rep.p + 12) = BitVec.ofNat 64 (z.rep.refs + zeroCount hs) := hn.refs
  have e1 : 2147603920 ≤ z.rep.p := hn.shape.pLo
  have e2 : z.rep.p + 40 ≤ heapEnd := hn.shape.pHi
  have e3 : z.rep.p % 8 = 0 := hn.shape.pAl
  simp only [heapEnd] at e2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have h2 := pk.st.rm.r2
  have hab := cx.above; have hW' := cx.big
  simp only [heapEnd] at hab
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hzk := kz.room
  have hrf' : ldv .lw (writeLog M [(sp - 192 + 48, 8, BitVec.ofNat 64 z.rep.p)]) (z.rep.p + 12) =
      BitVec.ofNat 64 (z.rep.refs + zeroCount hs) := by
    rw [ldv_store_miss .lw M _ (by simp only [widthOfM]; omega)]; exact hrf
  bc_run hlive hS [h12, hrf, hrf', h2, sxw_ofNat] at 0x800050d4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hmo : MemOnly (fun a => z.rep.p + 12 ≤ a ∧ a < z.rep.p + 12 + 4)
      (writeLog (writeLog M [(sp - 192 + 48, 8, BitVec.ofNat 64 z.rep.p)])
        [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + zeroCount hs + 1))])
      (writeLog M [(sp - 192 + 48, 8, BitVec.ofNat 64 z.rep.p)]) :=
    MemOnly.store _ _ _ _
  have hP1 : ∀ a, (z.rep.p + 12 ≤ a ∧ a < z.rep.p + 12 + 4) → heapStart ≤ a ∧ a < heapEnd :=
    fun a h => by simp only [heapStart, heapEnd]; omega
  have st1 := (pk.st.storeSlot cx 48 (BitVec.ofNat 64 z.rep.p) (by omega)).heapOnly cx hmo hP1
  have hga : GlobAgree (writeLog (writeLog M [(sp - 192 + 48, 8, BitVec.ofNat 64 z.rep.p)])
      [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + zeroCount hs + 1))]) M :=
    (GlobAgree.store _ (by omega)).trans (GlobAgree.store _ (by omega))
  have pk3 : KM3 S M0 (writeLog (writeLog M [(sp - 192 + 48, 8, BitVec.ofNat 64 z.rep.p)])
      [(z.rep.p + 12, 4, BitVec.ofNat 64 (z.rep.refs + zeroCount hs + 1))])
      R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 none fl :=
    ⟨st1, pk.tr,
      by rw [hmo.ldv_off hP1 (by simp only [heapStart, heapEnd]; omega), ldv_ld_miss _ _ (by omega)]
         exact pk.m1,
      by rw [hmo.ldv_off hP1 (by simp only [heapStart, heapEnd]; omega)]; exact ldv_store_hit _ _ _,
      pk.s6, pk.s10⟩
  have hb2 := (hb.out_frame (MemOnly.store _ (sp - 192 + 48) 8 (BitVec.ofNat 64 z.rep.p))
    fun a ha => by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega).kzero
    (toNat_ofNat_mod32 (by omega)) (by omega)
  have hzc : valCount z.rep = 0 := by simp only [valCount, kz.ds, kz.len]; rfl
  have hzv : hdVal z = 0 := by show dvalBE (z.rep.ds.take z.rep.len) = 0; rw [kz.ds, kz.len]; rfl
  refine kara_m3 hlive ih cx hk (pk3.keeps (ks := [15]) (by keeps_tac Keeps.refl _ _)) hb2 (hpm none)
    (hown.cons fun x e => nomatch e) (hok.cons fun x e => nomatch e)
    (List.mem_cons_of_mem _ hu0m) (List.mem_cons_of_mem _ hv0m)
    (hga.zero (by simpa only [zeroCount_none] using kz)) (by bsimp [h12]) (hga.mulBase hmb)
    hN hW hNla hn1 hm1z hfit1 (by show n + valCount z.rep ≤ _; omega) hfit3 hw1
    (by show 1 ≤ z.rep.len; have := kz.len; omega) hu0p hv0p ?_
  show KFillVal _ (hdVal z) _ _ _ _ _
  rw [hzv, ← hz0]; exact hv

/-- **`m2` returned** (`0x800050d0`): `_bc_rec_mul (d1, d2)`'s product in
`m2`'s slot; `a2 = _zero_`, then `m3` (`kara_m3`). -/
theorem kara_m2ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H' : Heap} {F' : List Blk} {fl : Bool}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hv0 hm1 : Hd} {hs : List Hd} {x1 y1 y : NumObj}
    (pk : KM2 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 (some x1) (some y1) hm1 fl)
    (hpm : ∀ h2 h3 : Hd, (h3 :: h2 :: hs).Perm (kHs hu1 hu0 hv1 hm1 hv0 h2 h3 (some x1) (some y1)))
    (hown : HdOwned A B z hs) (hok : HdOK hs) (hu0m : hu0 ∈ hs) (hv0m : hv0 ∈ hs)
    (hx1 : NumAt M x1.rep) (hy1 : NumAt M y1.rep)
    (kk : Keeps (1 :: binClob) R' R)
    (post : RmPost S M M' H' F' ((temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B)
      x1.rep y1.rep x1.rep.len y1.rep.len (sp - 192 + 48) (sp - 192) (W - 192) y)
    (kz : KZero M z (zeroCount hs + (4 * ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len) + 8)))
    (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hN : (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ N)
    (hW : rmStack ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len) + 192 ≤ W)
    (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (hm1z : fl = true → hdVal (Hd.o z hm1) = 0)
    (hfit1 : fl = false → 2 * n + valCount (Hd.o z hm1).rep ≤ la + lb + 1)
    (hfit2 : n + x1.rep.len + y1.rep.len ≤ la + lb + 1)
    (hfit3 : n + (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ la + lb + 1)
    (hw1 : fl = false → 1 ≤ (Hd.o z hm1).rep.len)
    (hu0p : 1 ≤ (Hd.o z hu0).rep.len) (hv0p : 1 ≤ (Hd.o z hv0).rep.len)
    (hv : KFillVal (hdVal (Hd.o z hm1)) (hdVal x1 * hdVal y1)
      (hdVal (Hd.o z hu0) * hdVal (Hd.o z hv0)) (10 ^ n)
      (kUV u v la lb) (la + lb + 1) (x1.rep.neg != y1.rep.neg)) :
    DW live S Q 0x800050d0#64 R' M' := by
  have hab := cx.above; have hW' := cx.big
  simp only [heapEnd] at hab
  have kr := post.kret hx1 hy1
  have hS : HeapOwn S := fun a h1 h2 => kr.heap.heap.own a h1 h2
  have st := pk.st.call cx 48 (by omega) post.out
  have hga : GlobAgree M' M := GlobAgree.call (by omega) (by omega) post.out
  have hfr : ∀ a, sp - 192 + 40 ≤ a → a < sp - 192 + 48 → imgM M' a = imgM M a := fun a h1 h2 =>
    post.out a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [slotBytes]; omega) (by simp only [frameIn]; omega)
  have pk3 : KM3 S M0 M' R0 R sp q W n la lb z hu1 hu0 hv1 hv0 (some x1) (some y1) hm1 (some y) fl :=
    ⟨st, pk.tr,
      (ldv_congr .ld fun j hj => hfr _ (by omega) (by simp only [widthOfM] at hj; omega)).trans pk.m1,
      kr.slot, pk.s6, pk.s10⟩
  have kz' := hga.zero kz
  have h18 := (kk.get 18 (by decide)).trans pk.s2
  have hgl := kz'.glob
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [zeroAddr] at h18 hgl
  bc_run hlive hS [h18, hgl] at 0x800050d4
  all_goals first | (simp only [LdOK, StOK, tohostAddr] at *; omega) | skip
  · exact fun b hb => cx.consts b (by
      have := of_mem_accAddrs hb; simp only [constBytes, twoAddr, zeroAddr] at this ⊢; omega)
  have hvc := kr.vc
  refine kara_m3 hlive ih cx hk ((pk3.keeps ((Keeps.refl _ _).trans kk)).keeps (ks := [12])
      (by keeps_tac Keeps.refl _ _)) kr.heap (hpm (some y))
    (hown.cons fun x e => by cases e; exact kr.owns) (hok.cons fun x e => by cases e; exact kr.refs)
    (List.mem_cons_of_mem _ hu0m) (List.mem_cons_of_mem _ hv0m)
    (by simpa only [zeroCount_some] using kz') (by bsimp []) (hga.mulBase hmb)
    hN hW hNla hn1 hm1z hfit1 (by show n + valCount y.rep ≤ _; omega) hfit3 hw1 kr.pos hu0p hv0p ?_
  show KFillVal _ (hdVal y) _ _ _ _ (x1.rep.neg != y1.rep.neg)
  rw [kr.val]; exact hv

/-- The recursive call for `m2` at `0x800050b8` (both factors nonzero):
`_bc_rec_mul (d1, n_len (d1), d2, n_len (d2), &m2)`. -/
theorem kara_m2call {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H : Heap} {F : List Blk} {fl : Bool}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hv0 hm1 : Hd} {hs : List Hd} {x1 y1 : NumObj}
    (pk : KM2 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 (some x1) (some y1) hm1 fl)
    (hb : BcHeap S M H F (KList [] hs A B z))
    (hpm : ∀ h2 h3 : Hd, (h3 :: h2 :: hs).Perm (kHs hu1 hu0 hv1 hm1 hv0 h2 h3 (some x1) (some y1)))
    (hown : HdOwned A B z hs) (hok : HdOK hs) (hu0m : hu0 ∈ hs) (hv0m : hv0 ∈ hs)
    (hx1m : some x1 ∈ hs) (hy1m : some y1 ∈ hs)
    (kz : KZero M z (zeroCount hs + 1 +
      (4 * max (x1.rep.len + y1.rep.len) ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len + 1) + 8)))
    (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hN1 : x1.rep.len + y1.rep.len ≤ N) (hW1 : rmStack (x1.rep.len + y1.rep.len) + 192 ≤ W)
    (hN : (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ N)
    (hW : rmStack ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len) + 192 ≤ W)
    (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (hx1p : 1 ≤ x1.rep.len) (hy1p : 1 ≤ y1.rep.len)
    (hm1z : fl = true → hdVal (Hd.o z hm1) = 0)
    (hfit1 : fl = false → 2 * n + valCount (Hd.o z hm1).rep ≤ la + lb + 1)
    (hfit2 : n + x1.rep.len + y1.rep.len ≤ la + lb + 1)
    (hfit3 : n + (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ la + lb + 1)
    (hw1 : fl = false → 1 ≤ (Hd.o z hm1).rep.len)
    (hu0p : 1 ≤ (Hd.o z hu0).rep.len) (hv0p : 1 ≤ (Hd.o z hv0).rep.len)
    (hv : KFillVal (hdVal (Hd.o z hm1)) (hdVal x1 * hdVal y1)
      (hdVal (Hd.o z hu0) * hdVal (Hd.o z hv0)) (10 ^ n)
      (kUV u v la lb) (la + lb + 1) (x1.rep.neg != y1.rep.neg)) :
    DW live S Q 0x800050b8#64 R M := by
  have hb' : BcHeap S M H F ((temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B) := by
    simpa only [KList, List.nil_append, List.append_assoc] using hb
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hxm : x1 ∈ (temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_filterMap.mpr ⟨some x1, hx1m, rfl⟩))
  have hym : y1 ∈ (temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_filterMap.mpr ⟨some y1, hy1m, rfl⟩))
  have hx1 := hb'.nums x1 hxm
  have hy1 := hb'.nums y1 hym
  have h2 := pk.st.rm.r2
  have h21 := pk.tr.d1
  have h23 := pk.tr.d2
  have hl1 := pk.l1
  have h17 := pk.l2
  simp only [Hd.p, Hd.o] at h21 h23 hl1 h17
  have hab := cx.above; have hW' := cx.big
  simp only [heapEnd] at hab
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h2, h21, h23, hl1, h17] at 0x800050cc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  apply st_800050cc hlive
  refine kara_child ih cx hk (pk.st.rm.keeps (by keeps_tac Keeps.refl _ _) (by bsimp [h2])) 48
    (by omega) (by decide) hN1 hW1 (KZero.withRefs (kz.mono (by omega)))
    ⟨hxm, hym, hx1p, hy1p, Nat.le_add_right _ _, Nat.le_add_right _ _,
      by omega, hmb⟩ hb' (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
    (by bsimp []) (by bsimp [h2]) ?_
  intro R' M' H' F' y kk post
  bsimp []
  exact kara_m2ret hlive ih cx hk pk hpm hown hok hu0m hv0m hx1 hy1
    ((kk.mono (fun r hr => List.mem_cons_of_mem _ hr)).trans (by keeps_tac Keeps.refl _ _))
    post (kz.mono (by omega)) hmb hN hW hNla hn1 hm1z hfit1 hfit2 hfit3 hw1 hu0p hv0p hv

/-- **`m2 = d1 · d2`** from `0x80005050`: `d1` or `d2` zero, a copy of
`_zero_`; else the recursive call; then `m3` (`kara_m3`). -/
theorem kara_m2stage {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H : Heap} {F : List Blk} {fl : Bool}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hv0 hm1 hd1 hd2 : Hd} {hs : List Hd}
    (pk : KM2 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0 hd1 hd2 hm1 fl)
    (hb : BcHeap S M H F (KList [] hs A B z))
    (hpm : ∀ h2 h3 : Hd, (h3 :: h2 :: hs).Perm (kHs hu1 hu0 hv1 hm1 hv0 h2 h3 hd1 hd2))
    (hown : HdOwned A B z hs) (hok : HdOK hs) (hu0m : hu0 ∈ hs) (hv0m : hv0 ∈ hs)
    (hd1m : hd1 ∈ hs) (hd2m : hd2 ∈ hs)
    (kz : KZero M z (zeroCount hs + 1 + (4 * max ((Hd.o z hd1).rep.len + (Hd.o z hd2).rep.len)
      ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len + 1) + 8)))
    (h12 : R 12 = BitVec.ofNat 64 z.rep.p) (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hN1 : (Hd.o z hd1).rep.len + (Hd.o z hd2).rep.len ≤ N)
    (hW1 : rmStack ((Hd.o z hd1).rep.len + (Hd.o z hd2).rep.len) + 192 ≤ W)
    (hN : (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ N)
    (hW : rmStack ((Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len) + 192 ≤ W)
    (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (hd1p : 1 ≤ (Hd.o z hd1).rep.len) (hd2p : 1 ≤ (Hd.o z hd2).rep.len)
    (hm1z : fl = true → hdVal (Hd.o z hm1) = 0)
    (hfit1 : fl = false → 2 * n + valCount (Hd.o z hm1).rep ≤ la + lb + 1)
    (hfit2 : n + (Hd.o z hd1).rep.len + (Hd.o z hd2).rep.len ≤ la + lb + 1)
    (hfit3 : n + (Hd.o z hu0).rep.len + (Hd.o z hv0).rep.len ≤ la + lb + 1)
    (hw1 : fl = false → 1 ≤ (Hd.o z hm1).rep.len)
    (hu0p : 1 ≤ (Hd.o z hu0).rep.len) (hv0p : 1 ≤ (Hd.o z hv0).rep.len)
    (hv : KFillVal (hdVal (Hd.o z hm1)) (hdVal (Hd.o z hd1) * hdVal (Hd.o z hd2))
      (hdVal (Hd.o z hu0) * hdVal (Hd.o z hv0)) (10 ^ n)
      (kUV u v la lb) (la + lb + 1) ((Hd.o z hd1).rep.neg != (Hd.o z hd2).rep.neg)) :
    DW live S Q 0x80005050#64 R M := by
  have hb' : BcHeap S M H F ((temps hs ++ A) ++ z.withRefs (z.rep.refs + zeroCount hs) :: B) := by
    simpa only [KList, List.nil_append, List.append_assoc] using hb
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hzn := hb'.nums _ (List.mem_append_right _ List.mem_cons_self)
  have hzb : z.rep.p < 2 ^ 64 := by
    have := hzn.shape.pHi; simp only [NumObj.withRefs, heapEnd] at this; omega
  have hx : ∀ h, h ∈ hs → ∀ x, h = some x → NumAt M x.rep ∧ x.rep.p ≠ z.rep.p := by
    intro h hm x e
    have hxm : x ∈ temps hs ++ A :=
      List.mem_append_left _ (List.mem_filterMap.mpr ⟨h, hm, by rw [e]; rfl⟩)
    exact ⟨hb'.nums x (List.mem_append_left _ hxm), hb'.p_ne_split hxm⟩
  have zero : ∀ R', Keeps [13, 14, 15] R' R →
      hdVal (Hd.o z hd1) * hdVal (Hd.o z hd2) = 0 → DW live S Q 0x800054a8#64 R' M := by
    intro R' kk hc
    exact kara_m2zero hlive ih cx hk (pk.keeps kk) hb hpm hown hok hu0m hv0m
      (kz.mono (by omega)) (by rw [kk.get 12]; exact h12) hmb hN hW hNla hn1 hm1z hfit1 hfit3 hw1 hu0p hv0p hc hv
  refine kzero_80005050 hlive hS pk.tr.d1 h12 hzb (hx _ hd1m) ?_ ?_
  · intro R1 kk1 hz0
    exact zero R1 kk1 (by rw [hz0.val kz.ds kz.len, Nat.zero_mul])
  intro x1 e0 _ R1 kk1
  subst e0
  refine kzero_80005080 hlive hS ((kk1.get 23).trans pk.tr.d2) ((kk1.get 12).trans h12) hzb
    (hx _ hd2m) ?_ ?_
  · intro R2 kk2 hz1
    exact zero R2 (kk2.trans kk1) (by rw [hz1.val kz.ds kz.len, Nat.mul_zero])
  intro y1 e1 _ R2 kk2
  subst e1
  exact kara_m2call hlive ih cx hk (pk.keeps (kk2.trans kk1)) hb hpm hown hok hu0m hv0m hd1m hd2m
    kz hmb hN1 hW1 hN hW hNla hn1 hd1p hd2p hm1z hfit1 hfit2 hfit3 hw1 hu0p hv0p hv

end Dc.Mach
