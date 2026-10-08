import Dc.Mach.Bc.KaraSubsSites

/-!
# `_bc_rec_mul`'s Karatsuba step: the `m1` stage

`kara_m1`: from `0x80004f70`, the two `bc_is_zero` tests on `u1`, `v1`, the
differences `d1`, `d2` (both copies), and `m1` as `_bc_rec_mul (u1, v1)` or a
copy of `_zero_`; then the `m2` stage.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- **The `m1` stage** from `0x80004f70`: `bc_is_zero (u1)`,
`bc_is_zero (v1)`; both paths take the differences, then `m1` is
`_bc_rec_mul (u1, v1)` or a copy of `_zero_`; then `m2`. -/
theorem kara_m1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {N : Nat} (ih : RmIH live S Q N)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb n : Nat} {A B : List NumObj}
    {z : NumObj} {u v : NumRep} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    {hu1 hu0 hv1 hv0 : Hd} {hs0 : List Hd}
    (pk : KM1 S M0 M R0 R sp q W n la lb z hu1 hu0 hv1 hv0)
    (hb : BcHeap S M H F (KList [] hs0 A B z))
    (hp0 : hs0.Perm [hu1, hu0, hv1, hv0])
    (hown : HdOwned A B z hs0) (hok : HdOK hs0)
    (kz : KZero M z (zeroCount hs0 + 2 + (4 * (la + lb + 2 - n) + 8)))
    (h17 : R 17 = BitVec.ofNat 64 z.rep.p)
    (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80)
    (hW : 368 ≤ W) (hNla : la + lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (sa1 : KSubArgs z hu1 hu0) (sa2 : KSubArgs z hv0 hv1)
    (ds : KDiffSpec z hu1 hu0 hv1 hv0 u v n la lb N W)
    (m3s : KM3Spec z hu0 hv0 n la lb N W)
    (m1s : ∀ x1 x2, hu1 = some x1 → hv1 = some x2 → 1 ≤ x1.rep.len → 1 ≤ x2.rep.len →
      KM1Spec z hu1 hv1 n la lb N W) :
    DW live S Q 0x80004f70#64 R M := by
  have hb' : BcHeap S M H F ((temps hs0 ++ A) ++
      z.withRefs (z.rep.refs + zeroCount hs0) :: B) := by
    simpa only [KList, List.nil_append, List.append_assoc] using hb
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hzn := hb'.nums _ (List.mem_append_right _ List.mem_cons_self)
  have hzb : z.rep.p < 2 ^ 64 := by
    have := hzn.shape.pHi; simp only [NumObj.withRefs, heapEnd] at this; omega
  have hx : ∀ h, h ∈ hs0 → ∀ x, h = some x → NumAt M x.rep ∧ x.rep.p ≠ z.rep.p := by
    intro h hm x e
    have hxm : x ∈ temps hs0 ++ A :=
      List.mem_append_left _ (List.mem_filterMap.mpr ⟨h, hm, by rw [e]; rfl⟩)
    exact ⟨hb'.nums x (List.mem_append_left _ hxm), hb'.p_ne_split hxm⟩
  have hu1m : hu1 ∈ hs0 := hp0.mem_iff.mpr (by simp)
  have hu0m : hu0 ∈ hs0 := hp0.mem_iff.mpr (by simp)
  have hv1m : hv1 ∈ hs0 := hp0.mem_iff.mpr (by simp)
  have hv0m : hv0 ∈ hs0 := hp0.mem_iff.mpr (by simp)
  have hzk : z.rep.refs + zeroCount hs0 + 2 < 2 ^ 31 := by have := kz.room; omega
  have zk : hdVal (Hd.o z hu1) * hdVal (Hd.o z hv1) = 0 →
      KSubsK live S Q M0 M R0 sp q W n la lb z hu1 hu0 hv1 hv0 hs0 A B 0x8000550c#64 := by
    intro hz0 R'' M'' H'' F'' y1 y2 ps hb2 hga
    exact kara_m1zero hlive ih cx hk ps hb2 hp0
      (((hown.cons (h3 := some y1) fun x e => by cases e; exact ps.d1.owns).cons
        (h3 := some y2) fun x e => by cases e; exact ps.d2.owns))
      ((hok.cons (h3 := some y1) fun x e => by cases e; exact ps.d1.refs).cons
        (h3 := some y2) fun x e => by cases e; exact ps.d2.refs)
      (hga.zero kz) (hga.mulBase hmb) hNla hn1 ds m3s hz0
  have zero : ∀ R', Keeps [13, 14, 15, 26] R' R →
      hdVal (Hd.o z hu1) * hdVal (Hd.o z hv1) = 0 → DW live S Q 0x800054bc#64 R' M :=
    fun R' kk hz0 => ksubs_800054bc hlive cx hk hW (pk.keeps kk) (by rw [kk.get 17]; exact h17) hb
      hu1m hu0m hv0m hv1m sa1 sa2 kz.refs (by omega) (zk hz0)
  refine kzero_80004f70 hlive hS pk.u1 h17 hzb (hx _ hu1m) ?_ ?_
  · intro R1 kk1 hz1
    exact zero R1 (kk1.mono (by decide)) (by rw [hz1.val kz.ds kz.len, Nat.zero_mul])
  intro x1 e1 hx1p R1 kk1
  subst e1
  refine kzero_80004fa0 hlive hS ((kk1.get 27).trans pk.v1) ((kk1.get 17).trans h17) hzb
    (hx _ hv1m) ?_ ?_ ?_
  · intro R2 kk2 hz2
    exact zero R2 ((kk2.mono (by decide)).trans (kk1.mono (by decide)))
      (by rw [hz2.val kz.ds kz.len, Nat.mul_zero])
  rotate_left
  · -- `v1` without digits: the third copy of the differences, then `m1 = _zero_`
    intro x2 e2 hx0 R2 kk2 h26
    subst e2
    refine ksubs_80005530 hlive cx hk hW
      (pk.keeps ((kk2.mono (ks' := [13, 14, 15, 26]) (by decide)).trans (kk1.mono (by decide))))
      (by rw [kk2.get 17 (by decide), kk1.get 17 (by decide)]; exact h17) hb
      hu1m hu0m hv0m hv1m sa1 sa2 kz.refs (by omega) h26 (zk ?_)
    show _ * dvalBE (x2.rep.ds.take x2.rep.len) = 0
    rw [show x2.rep.len = 0 by omega, List.take_zero]; exact Nat.mul_zero _
  intro x2 e2 hx2p R2 kk2
  subst e2
  refine ksubs_80004fd8 hlive cx hk hW
    (pk.keeps ((kk2.mono (ks' := [13, 14, 15, 26]) (by decide)).trans (kk1.mono (by decide))))
    (by rw [kk2.get 17 (by decide), kk1.get 17 (by decide)]; exact h17) hb
    hu1m hu0m hv0m hv1m sa1 sa2 kz.refs (by omega) ?_
  intro R'' M'' H'' F'' y1 y2 ps hb2 hga
  exact kara_m1call hlive ih cx hk ps hb2 hp0
    ((hown.cons (h3 := some y1) fun x e => by cases e; exact ps.d1.owns).cons
      (h3 := some y2) fun x e => by cases e; exact ps.d2.owns)
    ((hok.cons (h3 := some y1) fun x e => by cases e; exact ps.d1.refs).cons
      (h3 := some y2) fun x e => by cases e; exact ps.d2.refs)
    (hga.zero kz) (hga.mulBase hmb) hNla hn1 hx1p hx2p ds m3s (m1s _ _ rfl rfl hx1p hx2p)

end Dc.Mach
