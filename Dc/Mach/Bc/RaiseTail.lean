import Dc.Mach.Bc.RaiseBase

/-!
# `bc_raise`'s exits (`0x80006744` to `0x80006908`)

    6744 bc_divide (_one_, temp, result, rscale)        (negative exponent)
    675c power = *(sp + 8); bc_free_num (&temp)         (inlined, `s5` reloaded)
    6798 bc_free_num (&power)                           (inlined into the epilogue)
    688c bc_free_num (result); *result = temp; temp->n_scale = MIN (…, rscale)
    68cc temp is power (a power of two): the same, the shared reference dropped
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The facts of `RaCtx` the steps use, as `omega` sees them. -/
macro "ra_facts " cx:term : tactic =>
  `(tactic| (have _hsf := ($cx).frame
             have _hsl := _hsf.lo; have _hsh := _hsf.hi; have _hsa := _hsf.al
             have _hab := ($cx).above; have _hW := ($cx).big
             have _hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
             simp only [heapEnd] at _hab
             have _htx : tohostAddr = 0x8001ad00 := rfl))

/-- Through a change of registers of `raCallClob`. -/
theorem RaAt.regs {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {slots : List (Nat × Nat)} (h : RaAt S Mt0 M R0 R sp W q slots) (hk : Keeps raCallClob R' R) :
    RaAt S Mt0 M R0 R' sp W q slots :=
  { h with
    r2 := by rw [hk.get 2]; exact h.r2
    keep := (hk.mono (by decide)).trans h.keep
    r23 := by rw [hk.get 23]; exact h.r23 }

/-- Through a store into the heap. -/
theorem RaAt.heapStore {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {slots : List (Nat × Nat)} (h : RaAt S Mt0 M R0 R sp W q slots) {a w : Nat} {v : BitVec 64}
    (h1 : heapStart ≤ a) (h2 : a + w ≤ heapEnd) (hsp : heapEnd + 96 ≤ sp) :
    RaAt S Mt0 (writeLog M [(a, w, v)]) R0 R sp W q slots :=
  { h with
    saved := fun p hp => by
      rw [ldv_ld_miss _ _ (by simp only [heapStart, heapEnd] at h1 h2 hsp; omega)]; exact h.saved p hp
    out := fun b hb hf => by
      rw [imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at hb h1 h2; omega)]
      exact h.out b hb hf }

/-- The epilogue from `0x800067f4` (`s5` already back). -/
theorem ra_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} (cx : RaCtx S R0 sp W q)
    (hS : HeapOwn S) (ra : RaAt S Mt0 M R0 R sp W q raSlots1) (h21 : R 21 = R0 21)
    (hk : ∀ R', Keeps binClob R' R0 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x800067f4#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hal := cx.al
  have sv := ra.saved
  bc_run hlive hS [ra.r2, sv.get 1 88, sv.get 8 80, sv.get 9 72, sv.get 20 48, sv.get 24 16,
    sv.get 18 64, sv.get 22 32, sv.get 23 24]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (Keeps.unwind (all := raAll) (saved := [1, 2, 8, 9, 18, 20, 21, 22, 23, 24]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := ra.keep))
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, ra.r2, h21, sv.get 1 88, sv.get 8 80, sv.get 9 72, sv.get 20 48, sv.get 24 16, sv.get 18 64, sv.get 22 32, sv.get 23 24]
  all_goals (try (congr 1; omega))

/-- The continuation after `power` is freed into the epilogue: the heap
freed, nothing else off the heap changed. -/
def RaFreeK (live S : Nat → Prop) (X : Raws) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (M0 : Mem) (H : Heap) (F : List Blk) (L1 L2 : List NumObj)
    (x : NumObj) : Prop :=
  ∀ R' M' H' F' L', Keeps binClob R' R0 → KFreed H F L1 L2 x H' F' L' →
    BcHeap S X M' H' F' L' → (∀ a, OutHeap a → imgM M' a = imgM M0 a) → DW live S Q (R0 1) R' M'

/-- The epilogue's second half from `0x800067d4` (`ra`, `s0`, `s5` back). -/
theorem ra_ret2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} (cx : RaCtx S R0 sp W q)
    (hS : HeapOwn S) (sv : SavedWords M (sp - 96) raSlots1 R0)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 96)) (h1 : R 1 = R0 1) (h8 : R 8 = R0 8)
    (hkp : Keeps raAll R R0) (h21 : R 21 = R0 21)
    (hk : ∀ R', Keeps binClob R' R0 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x800067d4#64 R M := by
  ra_facts cx
  have hsf := cx.frame
  have hal := cx.al
  bc_run hlive hS [h2, h1, sv.get 9 72, sv.get 20 48, sv.get 24 16, sv.get 18 64, sv.get 22 32, sv.get 23 24]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (Keeps.unwind (all := raAll) (saved := [1, 2, 8, 9, 18, 20, 21, 22, 23, 24]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp))
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals bsimp [cx.sp0, h2, h1, h8, h21, sv.get 9 72, sv.get 20 48, sv.get 24 16, sv.get 18 64, sv.get 22 32, sv.get 23 24]
  all_goals (try (congr 1; omega))

/-- The struct of `x` pushed on `_bc_Free_list` inside the epilogue
(`0x800067b8`), then the return. -/
theorem ra_pushRet {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M1 : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H H' : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (cx : RaCtx S R0 sp W q) (hS : HeapOwn S)
    (hgl : ∀ a, bcFreeAddr ≤ a → a < bcFreeAddr + 8 → S a) (hr1 : x.rep.refs = 1)
    (hpost : BcHeap S X (writeLog (writeLog M1 [(bcFreeAddr, 8, BitVec.ofNat 64 x.rep.p)])
      [(x.rep.p + 16, 8, BitVec.ofNat 64 (deadHead F))]) H' (x.sb :: F) (L1 ++ L2))
    (hout : ∀ a, OutHeap a → imgM M1 a = imgM M0 a)
    (wg : ldv .ld M1 bcFreeAddr = BitVec.ofNat 64 (deadHead F))
    (hp : 2147603920 ≤ x.rep.p) (hp' : x.rep.p + 40 ≤ 2273312768) (hpa : x.rep.p % 8 = 0)
    (sv : SavedWords M1 (sp - 96) raSlots1 R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 96))
    (hkp : Keeps raAll R R0) (h21 : R 21 = R0 21) (h18 : R 18 = BitVec.ofNat 64 x.rep.p)
    (hk : RaFreeK live S X Q R0 M0 H F L1 L2 x) :
    DW live S Q 0x800067b8#64 R M1 := by
  ra_facts cx
  have hsf := cx.frame
  have hal := cx.al
  have hgl' : ∀ b ∈ accAddrs 2147601840 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hgl b (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega)
  simp only [bcFreeAddr] at wg hpost
  bc_run hlive hS [h18] at 0x800067bc
  apply st_800067bc hlive
  · bsimp []; bc_addr
  · bsimp []; exact hgl'
  bsimp [wg]
  bc_run hlive hS [h18, h2, sv.get 1 88, sv.get 8 80] at 0x800067d4
  all_goals first | exact hgl' | exact frame_acc hsf (by omega) (by omega) | (simp only [StOK, and_true]; omega) | skip
  refine ra_ret2 hlive cx hS (sv.transport (lo := 16) (top := 96)
    (hag := fun a h1 h2 => by rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]))
    (by bsimp [h2]) (by bsimp []) (by bsimp []) (by keeps_tac hkp) (by bsimp [h21]) fun R' hk' => ?_
  refine hk _ _ _ _ _ hk' (.rel hr1) hpost fun a ha => ?_
  have ha' := ha
  simp only [OutHeap, heapStart, heapEnd, bcFreeAddr] at ha'
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), hout a ha]

/-- `power`'s buffer freed (`jal free` at `0x800067b4`), then
`ra_pushRet`. -/
theorem ra_freePowRel {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S X M H F (L1 ++ x :: L2)) (ho : x.Owns) (hnv : ∀ y ∈ L1, y.db ≠ x.db)
    (hr1 : x.rep.refs = 1) {v : BitVec 64}
    (sv : SavedWords M (sp - 96) raSlots1 R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 96))
    (hkp : Keeps raAll R R0) (h21 : R 21 = R0 21) (h18 : R 18 = BitVec.ofNat 64 x.rep.p)
    (h10 : R 10 = BitVec.ofNat 64 x.rep.ptr)
    (hk : RaFreeK live S X Q R0 M H F L1 L2 x) :
    DW live S Q 0x800067b4#64 R (writeLog M [(x.rep.p + 12, 4, v)]) := by
  ra_facts cx
  have hi := hb.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hxm : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums x hxm
  have hxb := hb.blocks x hxm
  num_facts hn
  have hpp : x.rep.p = x.sb.pay := hxb.sPay
  have hsz := hxb.sSz
  have hsph : x.sb.pay = x.sb.h + 16 := rfl
  have hdp : x.rep.ptr = x.db.pay := hxb.dPay ho
  obtain ⟨lpre, lpost, hl⟩ := List.append_of_mem hxb.dLive
  have hi1 : HeapInv S (writeLog M [(x.rep.p + 12, 4, v)]) H := hi.transport fun a ha => by
    have hn := live_not_alloc hi hxb.sLive (a := a)
    refine imgM_store_miss _ _ (Classical.byContradiction fun hc => hn ⟨by omega, ?_⟩ ha)
    simp only [Blk.fin] at hc ⊢; omega
  apply st_800067b4 hlive
  refine free_spec hlive hi1 hl _ (by bsimp [h10, hdp]) (by bsimp []) ?_
  intro R1 Mt3 hk1 hfp
  bsimp []
  have hfr3 : ∀ a, OutHeap a → imgM Mt3 a = imgM M a := fun a ha =>
    (hfp.frame a (OutHeap.not_alloc hi ha)).trans (imgM_store_miss _ _ (by
      simp only [OutHeap, heapStart, heapEnd] at ha; omega))
  have wg3 : ldv .ld Mt3 bcFreeAddr = BitVec.ofNat 64 (deadHead F) := by
    rw [ldv_congr .ld fun j hj => hfp.frame _ fun ha => by
      rcases AllocByte.glob_or_heap hi ha with h' | h' <;>
        simp only [freeListAddr, heapStart, heapEnd, bcFreeAddr, widthOfM] at h' hj <;> omega,
      ldv_ld_miss _ _ (by simp only [bcFreeAddr]; omega)]
    exact hb.dead.head
  exact ra_pushRet hlive cx hS hb.globOwn hr1 (hb.freeOwner ho hnv hl hfp) hfr3 wg3
    (by omega) (by omega) (by omega)
    (sv.transport (lo := 16) (top := 96) (hag := fun a h1 h2 => by
      rw [hfr3 a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)]))
    (by rw [hk1.get 2]; bsimp [h2]) (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac hkp)))
    (by rw [hk1.get 21]; bsimp [h21]) (by rw [hk1.get 18]; bsimp [h18]) hk

/-- **`bc_free_num (&power)` and return** from `0x8000679c` (`power` not
`NULL`): one reference fewer, or the owner released. -/
theorem ra_freePow {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S X M H F (L1 ++ x :: L2)) (ho : x.Owns) (hnv : ∀ y ∈ L1, y.db ≠ x.db)
    (hr : 1 ≤ x.rep.refs) (ra : RaAt S Mt0 M R0 R sp W q raSlots1)
    (h21 : R 21 = R0 21) (h18 : R 18 = BitVec.ofNat 64 x.rep.p)
    (hk : RaFreeK live S X Q R0 M H F L1 L2 x) :
    DW live S Q 0x8000679c#64 R M := by
  ra_facts cx
  have hi := hb.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hxm : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums x hxm
  have hxb := hb.blocks x hxm
  num_facts hn
  have hrf := hn.refs
  have hpt := hn.ptr
  have hdp : x.rep.ptr = x.db.pay := hxb.dPay ho
  have fbd := hi.blk (List.mem_append_right _ hxb.dLive)
  have hd1 : 2147603920 ≤ x.db.h := fbd.lo
  have hdph : x.db.pay = x.db.h + 16 := rfl
  rcases (show x.rep.refs = 1 ∨ 2 ≤ x.rep.refs from by omega) with hr1 | hr2
  · have h0 : BitVec.ofNat 64 1 + 18446744073709551615#64 = 0#64 := by decide
    have hpt1 : ∀ v, ldv .ld (writeLog M [(x.rep.p + 12, 4, v)]) (x.rep.p + 24) =
        BitVec.ofNat 64 x.rep.ptr := fun v => by rw [ldv_ld_miss _ _ (by omega)]; exact hpt
    bc_run hlive hS [h18, hrf, hr1, h0, hpt1] at 0x800067b4
    all_goals try (intro hc; exact absurd ((ofNat_eq_iff (x := x.rep.ptr) (y := 0) (by omega)
      (by omega)).mp hc) (by omega))
    bc_run hlive hS [h18, hpt1] at 0x800067b4
    all_goals rw [ldv_ld_miss _ _ (by omega), hpt]
    all_goals try (intro hc; first
      | exact absurd ((ofNat_eq_iff (x := x.rep.ptr) (y := 0) (by omega) (by omega)).mp hc) (by omega)
      | exact absurd ((ofNat_eq_iff (x := x.rep.ptr) (y := 0) (by omega) (by omega)).mp
          (Classical.not_not.mp hc)) (by omega))
    intro _
    refine ra_freePowRel hlive cx hb ho hnv hr1 ra.saved ?_ ?_ ?_ ?_ ?_ hk
    · bsimp [ra.r2]
    · keeps_tac ra.keep
    · bsimp [h21]
    · bsimp [h18]
    · bsimp []
  · have hpr : BitVec.ofNat 64 x.rep.refs + 18446744073709551615#64 =
        BitVec.ofNat 64 (x.rep.refs - 1) := word_pred (by omega)
    have hsx : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (x.rep.refs - 1))) =
        BitVec.ofNat 64 (x.rep.refs - 1) := sxw_ofNat (by omega)
    bc_run hlive hS [h18, hrf, hpr, hsx] at 0x800067f4 0x800067ac
    all_goals try (intro hc; exact absurd ((ofNat_eq_iff (x := x.rep.refs - 1) (y := 0)
      (by omega) (by omega)).mp (Classical.not_not.mp hc)) (by omega))
    intro _
    refine ra_ret hlive cx hS ((ra.regs (by keeps_tac Keeps.refl _ _)).heapStore (a := x.rep.p + 12) (w := 4) (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
      (by simp only [heapEnd]; omega)) (by bsimp [h21]) fun R' hk' => ?_
    refine hk _ _ H F _ hk' (.dec hr2) (hb.setRefs (toNat_ofNat_mod32 (by omega)) (by omega))
      fun a ha => ?_
    simp only [OutHeap, heapStart, heapEnd] at ha
    exact imgM_store_miss _ _ (by omega)

/-- **`bc_free_num (&power)` and return** from `0x80006798`. -/
theorem ra_freePow0 {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (cx : RaCtx S R0 sp W q)
    (hb : BcHeap S X M H F (L1 ++ x :: L2)) (ho : x.Owns) (hnv : ∀ y ∈ L1, y.db ≠ x.db)
    (hr : 1 ≤ x.rep.refs) (ra : RaAt S Mt0 M R0 R sp W q raSlots1)
    (h21 : R 21 = R0 21) (h18 : R 18 = BitVec.ofNat 64 x.rep.p)
    (hk : RaFreeK live S X Q R0 M H F L1 L2 x) :
    DW live S Q 0x80006798#64 R M := by
  have hi := hb.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hn := hb.nums x (List.mem_append_right _ List.mem_cons_self)
  num_facts hn
  bc_run hlive hS [h18] at 0x8000679c
  all_goals try (intro hc; exact absurd ((ofNat_eq_iff (x := x.rep.p) (y := 0)
    (by omega) (by omega)).mp hc) (by omega))
  intro _
  exact ra_freePow hlive cx hb ho hnv hr ra h21 h18 hk

end Dc.Mach
