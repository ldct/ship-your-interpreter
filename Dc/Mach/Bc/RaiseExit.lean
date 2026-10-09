import Dc.Mach.Bc.RaiseTail

/-!
# `bc_raise`'s result: the division, the store, the temporary's release

- `ra_freeTemp` (`0x80006760`): `temp` released, `s5` reloaded on the way.
- `ra_negDiv` (`0x80006744`): `bc_divide (_one_, temp, result, rscale)`.
- `ra_store` (`0x80006898`): `*result = temp`, its scale cut to `rscale`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The continuation at `0x80006798` after `temp` is released: the heap
freed, `s5` the word `w`. -/
def RaTempK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (L1 L2 : List NumObj)
    (x : NumObj) (w : BitVec 64) : Prop :=
  ∀ R' M' H' F' L', Keeps [1, 10, 14, 15, 21] R' R → R' 21 = w → KFreed H F L1 L2 x H' F' L' →
    BcHeap S M' H' F' L' → (∀ a, OutHeap a → imgM M' a = imgM M a) → DW live S Q 0x80006798#64 R' M'

/-- **`bc_free_num (&temp)`** from `0x80006760` (`temp` in `s4`, not `NULL`),
`s5` reloaded from `sp + 40` between the count's load and store. -/
theorem ra_freeTemp {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S M H F (L1 ++ x :: L2)) (ho : x.Owns) (hnv : ∀ y ∈ L1, y.db ≠ x.db)
    (hr : 1 ≤ x.rep.refs) (h2 : R 2 = BitVec.ofNat 64 (sp - 96))
    (h20 : R 20 = BitVec.ofNat 64 x.rep.p) {w : BitVec 64} (hw : ldv .ld M (sp - 96 + 40) = w)
    (hk : RaTempK live S Q R M H F L1 L2 x w) :
    DW live S Q 0x80006760#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hi := hb.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hxm : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums x hxm
  have hxb := hb.blocks x hxm
  num_facts hn
  have hrf := hn.refs
  have hw' : ∀ v, ldv .ld (writeLog M [(x.rep.p + 12, 4, v)]) (sp - 96 + 40) = w := fun v => by
    rw [ldv_ld_miss _ _ (by omega)]; exact hw
  bc_run hlive hS [h20, h2, hrf, hw] at 0x80006764
  all_goals try (intro hc; exact absurd ((ofNat_eq_iff (x := x.rep.p) (y := 0)
    (by omega) (by omega)).mp hc) (by omega))
  intro _
  rcases (show x.rep.refs = 1 ∨ 2 ≤ x.rep.refs from by omega) with hr1 | hr2
  · have h0 : BitVec.ofNat 64 1 + 18446744073709551615#64 = 0#64 := by decide
    bc_run hlive hS [h20, h2, hrf, hw, hr1, h0] at 0x80006798 0x80006778
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hpp : x.rep.p = x.sb.pay := hxb.sPay
    have hsz := hxb.sSz
    have hsph : x.sb.pay = x.sb.h + 16 := rfl
    refine ffree_owner_80006760 (fr := fun _ => False) (R0 := upd (upd (upd R 15 1#64) 21 w) 15
        (BitVec.signExtend 64 (BitVec.extractLsb 31 0 0#64))) hlive hb ho (fun _ => hnv) hr1 rfl
      (hi.transport fun a ha => by
        have hn := live_not_alloc hi hxb.sLive (a := a)
        refine imgM_store_miss _ _ (Classical.byContradiction fun hc => hn ⟨by omega, ?_⟩ ha)
        simp only [Blk.fin] at hc ⊢; omega)
      (by rw [ldv_ld_miss _ _ (by omega)]; exact hb.dead.head)
      (fun a ha => by simp only [OutHeap, heapStart, heapEnd] at ha; exact imgM_store_miss _ _ (by omega))
      (Keeps.refl _ _) (by bsimp [h20]) ?_
    intro R' M' H' F' L' hk' hf hb' ho'
    refine hk R' M' H' F' L' ?_ ?_ hf hb' fun a ha => ho' a ha id
    · have hk2 : Keeps [1, 10, 14, 15, 21] R' (upd (upd (upd R 15 1#64) 21 w) 15
          (BitVec.signExtend 64 (BitVec.extractLsb 31 0 0#64))) :=
        hk'.mono (fun z hz => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢; omega)
      exact hk2.trans (by keeps_tac Keeps.refl _ _)
    · rw [hk'.get 21 (by decide)]; bsimp []
  · have hpr : BitVec.ofNat 64 x.rep.refs + 18446744073709551615#64 =
        BitVec.ofNat 64 (x.rep.refs - 1) := word_pred (by omega)
    have hsx : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (x.rep.refs - 1))) =
        BitVec.ofNat 64 (x.rep.refs - 1) := sxw_ofNat (by omega)
    bc_run hlive hS [h20, h2, hrf, hw, hpr, hsx] at 0x80006798 0x80006778
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals try (intro hc; exact absurd ((ofNat_eq_iff (x := x.rep.refs - 1) (y := 0)
      (by omega) (by omega)).mp (Classical.not_not.mp hc)) (by omega))
    intro _
    refine hk _ _ H F _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (.dec hr2)
      (hb.setRefs (toNat_ofNat_mod32 (by omega)) (by omega)) fun a ha => ?_
    simp only [OutHeap, heapStart, heapEnd] at ha
    exact imgM_store_miss _ _ (by omega)

/-- **A call of `bc_divide`** from `bc_raise`'s frame (`sp - 96`) into the
result slot `q`. -/
theorem ra_divCall {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k : Nat} {n : Option Num}
    {L1 L2 : List NumObj} {x1 x2 xr z : NumObj} {H : Heap} {F : List Blk}
    (cx : RaCtx S R0 sp W q) (hoom : RaOom live S Q Mt0 sp W q)
    (houtM : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (ha : DivArgs M L1 L2 xr x1 x2 z n k) (hzm : z.rep.num.mag = 0)
    (hb : BcHeap S M H F (L1 ++ xr :: L2)) (hr : ResSlot M L1 xr q)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 x1.rep.p) (h11 : R 11 = BitVec.ofNat 64 x2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 q) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ m, n = some m → ∀ R' M' H' F' L' y, Keeps binClob R' R →
      BinPostW S M M' H' F' L1 L2 xr q (sp - 96) (W - 96) m L' y → DW live S Q (R 1) R' M')
    (hzero : n = none → ∀ R' M', Keeps binClob R' R →
      (∀ a, ¬ frameIn (sp - 96) (W - 96) a → imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000589c#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  exact bc_divide_spec hlive
    ⟨⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩,
      by simp only [heapEnd]; omega, by omega, hq, hsl.out, by omega, cx.slotZero, cx.consts,
      h2, hal⟩
    ⟨fun m hm R' M' H' F' L' y hk _ hp => hret m hm R' M' H' F' L' y hk hp,
      fun hn R' M' hk _ hf => hzero hn R' M' hk hf,
      fun R' M' sp' h1 h2 hr2 hout => hoom R' M' sp' (by omega) (by omega) hr2
        fun a ha hs hf => by
          rw [hout a ha hs (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
          exact houtM a ha hf⟩
    ha hzm hb hr h10 h11 h12 h13

end Dc.Mach
