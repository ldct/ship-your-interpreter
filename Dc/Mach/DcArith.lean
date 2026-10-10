import Dc.Mach.DcBinop
import Dc.Mach.Bc.BcMul

/-!
# dc's arithmetic operations (M9)

`dc/numeric.c`'s `dc_add` … `dc_exp`, each an instance of `DcOp` for
`dc_binop_spec`:

    dc_add (a, b, kscale, result):
      bc_init_num (result); bc_add (a, b, result, 0); return DC_SUCCESS;

- `DcAt.resSlot`, `DcAt.binArgs`: a bc callee's result slot and operands
  from the dc state.
- `DcAt.kzero`, `DcAt.mulArgs`: `_zero_` and the operands as
  `bc_multiply` needs them.
- `dc_add_spec`, `dc_sub_spec`, `dc_mul_spec`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **The result slot** of a bc callee: the slot `q` holding the state's
handle `.num x.p`. -/
theorem DcAt.resSlot {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L1 L2 : List NumObj}
    {x : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {q : Nat}
    (h : DcAt S M H F (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st)
    (hw : ldv .ld M q = BitVec.ofNat 64 x.rep.p) : ResSlot M L1 x q where
  refs := by
    have := h.den.numRefs x (List.mem_append_right _ List.mem_cons_self)
    rw [count_cons_self] at this; omega
  word := hw
  noView := fun _ hox y hy => db_ne_of_owns (List.nodup_append.mp h.heap.distinct).2.1 hy
    (h.den.owns y (List.mem_append_left _ hy)) hox

/-- **Two numbers of the state** as a bc binary operation's operands. -/
theorem DcAt.binArgs {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {x1 x2 : NumObj} (h1 : x1 ∈ L) (h2 : x2 ∈ L) {smin : Nat} (hsm : smin < 2 ^ 30) :
    BinArgs L x1 x2 smin := by
  have hn1 := h.heap.nums x1 h1
  have hn2 := h.heap.nums x2 h2
  have a1 := hn1.shape.vLo; have a2 := hn1.shape.vHi
  have b1 := hn2.shape.vLo; have b2 := hn2.shape.vHi
  simp only [heapStart, heapEnd] at a1 a2 b1 b2
  have p1 := h.den.pos x1 h1; have p2 := h.den.pos x2 h2
  exact ⟨h1, h2, h.den.norm x1 h1, h.den.norm x2 h2, by omega, fun e => by omega, fun e => by omega⟩

/-- A handle's number in the heap. -/
theorem GV.Den.numObj {L : List NumObj} {ss : List StrObj} {p : Nat} {n : Num}
    (h : (GV.num p).Den ⟨L, ss⟩ (.num n)) : ∃ x ∈ L, x.rep.p = p ∧ x.rep.num = n := h

/-- **`dc_add`** at `0x80002230`: `bc_init_num (result)`, then
`bc_add (a, b, result, 0)`; a 208-byte window, no reference lost. -/
theorem dc_add_spec {live S : Nat → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    DcOp live S 0x80002230 208 0 (fun _ _ _ => True) (fun _ a b => some (Num.add a b 0)) := by
  intro Q t M H F L C G hs st pa pb na nb R sp q hin _ hret hfail hoom
  have hsf := hin.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := hin.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hqs := hin.slotHi
  have hql := hin.slot.lo; have hqh := hin.slot.hi; have hqa := hin.slot.al
  have hS : HeapOwn S := fun a e1 e2 => hin.h.heap.heap.own a e1 e2
  have h2 := hin.r2; have h10 := hin.r10; have h11 := hin.r11; have h13 := hin.r13
  bc_run hlive hS [h2, h10, h11, h13] at 0x800049bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 32) (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have l0 : ldv .ld (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) (sp - 32) = BitVec.ofNat 64 pb := ldv_store_hit _ _ _
  have l8 : ldv .ld (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) (sp - 32 + 8) = BitVec.ofNat 64 q := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have l16 : ldv .ld (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) (sp - 32 + 16) = R 8 := by
    repeat rw [ldv_ld_miss _ _ (by omega)]
    rw [ldv_store_hit]
  have l24 : ldv .ld (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) (sp - 32 + 24) = R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) = M1 at hM1 l0 l8 l16 l24 ⊢
  have hab2 : heapEnd ≤ sp - 32 := by simp only [heapEnd]; omega
  have h1 := hin.h.outWrite hM1 fun a ha =>
    ⟨(above_sp (sp := sp - 32) hab2 (a := a) (by simp only [frameIn] at ha; omega)).1,
     (above_sp (sp := sp - 32) hab2 (a := a) (by simp only [frameIn] at ha; omega)).2.1⟩
  have hlen : (GV.num pa :: GV.num pb :: hs).length ≤ 2 ^ 30 := by
    have := hin.hsLen; simp only [List.length_cons]; omega
  refine dc_init_num_spec hlive h1 hlen hin.slot (by simp only [heapEnd]; omega) _ (by bsimp [])
    (by bsimp []) fun R2 M2 L2 C2 hk2 hd2 hkeep hw2 hfr2 => ?_
  obtain ⟨x1, hx1, e1p, e1n⟩ := (hkeep _ List.mem_cons_self _ hin.da).numObj
  obtain ⟨x2, hx2, e2p, e2n⟩ := (hkeep _ (List.mem_cons_of_mem _ List.mem_cons_self) _ hin.db).numObj
  obtain ⟨L1, L2, x, rfl, hxp⟩ := hd2.handle_num
  rw [← hxp] at hd2 hw2
  have ag2 : ∀ a, sp - 32 ≤ a → a < sp → imgM M2 a = imgM M1 a := fun a h1 h2 =>
    hfr2 a (above_sp hab2 h1).1 fun hs => by simp only [slotBytes] at hs; omega
  have m0 : ldv .ld M2 (sp - 32) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact l0
  have m8 : ldv .ld M2 (sp - 32 + 8) = BitVec.ofNat 64 q := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact l8
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk2.get 2 (by decide)]; bsimp []
  have r8 : R2 8 = BitVec.ofNat 64 pa := by rw [hk2.get 8 (by decide)]; bsimp []
  have hS2 : HeapOwn S := fun a e1 e2 => hd2.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS2 [q2, r8, m0, m8] at 0x80005634
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine bc_add_spec hlive (smin := 0) ⟨hsf.within (m := 32) (n := 176) (by omega) (by decide),
      by simp only [heapEnd]; omega, hin.slot,
      fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega), .inr (by omega),
      by bsimp [q2], by bsimp []⟩
    (hd2.binArgs hx1 hx2 (by decide)) (fun _ => ⟨hd2.den.pos x1 hx1, hd2.den.pos x2 hx2⟩)
    hd2.heap (hd2.resSlot hw2) (by bsimp [e1p]) (by bsimp [e2p]) (by bsimp []) (by bsimp [])
    ⟨fun R3 Mt H3 F3 L3 y hk3 hp => ?_, fun R3 Mt sp' o1 o2 hr2 hout => ?_⟩
  · obtain ⟨C3, hd3, hkeep3⟩ := hd2.newNum hp.rest hp.heap hp.refs hp.norm hp.pos hp.owns fun a ha =>
      hp.out a ha.outHeap (fun hs => by have := ha.lt; simp only [heapStart, slotBytes] at this hs; omega)
        (fun hf => by have := ha.lt; simp only [heapStart, frameIn] at this hf; omega)
    have agT : ∀ a, sp - 32 ≤ a → a < sp → imgM Mt a = imgM M1 a := fun a e1 e2 => by
      rw [hp.out a (above_sp hab2 e1).1 (fun hs => by simp only [slotBytes] at hs; omega)
        ((above_sp hab2 e1).2.2 176)]
      exact ag2 a e1 e2
    have e16 : ldv .ld Mt (sp - 32 + 16) = R 8 := by
      rw [ldv_congr .ld fun j hj => agT _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact l16
    have e24 : ldv .ld Mt (sp - 32 + 24) = R 1 := by
      rw [ldv_congr .ld fun j hj => agT _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact l24
    have q3 : R3 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
    have hS3 : HeapOwn S := fun a e1 e2 => hd3.heap.heap.own a e1 e2
    bsimp []
    bc_run hlive hS3 [q3, e16, e24]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    · exact hin.al
    refine hret _ Mt H3 F3 (y :: L3) C3 G y.rep.p (Num.add na nb 0)
      (Keeps.restore (by rw [h2]; congr 1; omega) (Keeps.upd _ (by decide) (Keeps.restore rfl
        (by keeps_tac ((hk3.mono (by decide)).trans
          (by keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))))))
      ⟨by bsimp [], hd3, rfl, ⟨y, List.mem_cons_self, rfl, by rw [hp.num, e1n, e2n]⟩,
        by rw [hp.slot, (hp.heap.blocks y List.mem_cons_self).sPay], rfl, by omega,
        fun a ho hg hf hs => ?_⟩
    rw [hp.out a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega), hfr2 a ho hs]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
  · bc_run hlive hS2 [] at 0x80001e74
    refine hoom R3 Mt sp' ⟨by omega, by omega, hr2, fun a ho hg hf hs => ?_⟩
    rw [hout a ho fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega), hfr2 a ho hs]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

/-- **`dc_sub`** at `0x80002278`: `bc_init_num (result)`, then
`bc_sub (a, b, result, 0)`; a 208-byte window, no reference lost. -/
theorem dc_sub_spec {live S : Nat → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    DcOp live S 0x80002278 208 0 (fun _ _ _ => True) (fun _ a b => some (Num.sub a b 0)) := by
  intro Q t M H F L C G hs st pa pb na nb R sp q hin _ hret hfail hoom
  have hsf := hin.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := hin.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hqs := hin.slotHi
  have hql := hin.slot.lo; have hqh := hin.slot.hi; have hqa := hin.slot.al
  have hS : HeapOwn S := fun a e1 e2 => hin.h.heap.heap.own a e1 e2
  have h2 := hin.r2; have h10 := hin.r10; have h11 := hin.r11; have h13 := hin.r13
  bc_run hlive hS [h2, h10, h11, h13] at 0x800049bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 32) (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have l0 : ldv .ld (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) (sp - 32) = BitVec.ofNat 64 pb := ldv_store_hit _ _ _
  have l8 : ldv .ld (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) (sp - 32 + 8) = BitVec.ofNat 64 q := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have l16 : ldv .ld (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) (sp - 32 + 16) = R 8 := by
    repeat rw [ldv_ld_miss _ _ (by omega)]
    rw [ldv_store_hit]
  have l24 : ldv .ld (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) (sp - 32 + 24) = R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize (writeLog (writeLog (writeLog (writeLog M
      [(sp - 32 + 16, 8, R 8)]) [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, BitVec.ofNat 64 q)])
      [(sp - 32, 8, BitVec.ofNat 64 pb)]) = M1 at hM1 l0 l8 l16 l24 ⊢
  have hab2 : heapEnd ≤ sp - 32 := by simp only [heapEnd]; omega
  have h1 := hin.h.outWrite hM1 fun a ha =>
    ⟨(above_sp (sp := sp - 32) hab2 (a := a) (by simp only [frameIn] at ha; omega)).1,
     (above_sp (sp := sp - 32) hab2 (a := a) (by simp only [frameIn] at ha; omega)).2.1⟩
  have hlen : (GV.num pa :: GV.num pb :: hs).length ≤ 2 ^ 30 := by
    have := hin.hsLen; simp only [List.length_cons]; omega
  refine dc_init_num_spec hlive h1 hlen hin.slot (by simp only [heapEnd]; omega) _ (by bsimp [])
    (by bsimp []) fun R2 M2 L2 C2 hk2 hd2 hkeep hw2 hfr2 => ?_
  obtain ⟨x1, hx1, e1p, e1n⟩ := (hkeep _ List.mem_cons_self _ hin.da).numObj
  obtain ⟨x2, hx2, e2p, e2n⟩ := (hkeep _ (List.mem_cons_of_mem _ List.mem_cons_self) _ hin.db).numObj
  obtain ⟨L1, L2, x, rfl, hxp⟩ := hd2.handle_num
  rw [← hxp] at hd2 hw2
  have ag2 : ∀ a, sp - 32 ≤ a → a < sp → imgM M2 a = imgM M1 a := fun a h1 h2 =>
    hfr2 a (above_sp hab2 h1).1 fun hs => by simp only [slotBytes] at hs; omega
  have m0 : ldv .ld M2 (sp - 32) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact l0
  have m8 : ldv .ld M2 (sp - 32 + 8) = BitVec.ofNat 64 q := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact l8
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk2.get 2 (by decide)]; bsimp []
  have r8 : R2 8 = BitVec.ofNat 64 pa := by rw [hk2.get 8 (by decide)]; bsimp []
  have hS2 : HeapOwn S := fun a e1 e2 => hd2.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS2 [q2, r8, m0, m8] at 0x80004ac4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine bc_sub_spec hlive (smin := 0) ⟨hsf.within (m := 32) (n := 176) (by omega) (by decide),
      by simp only [heapEnd]; omega, hin.slot,
      fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega), .inr (by omega),
      by bsimp [q2], by bsimp []⟩
    (hd2.binArgs hx1 hx2 (by decide)) (fun _ => ⟨hd2.den.pos x1 hx1, hd2.den.pos x2 hx2⟩)
    hd2.heap (hd2.resSlot hw2) (by bsimp [e1p]) (by bsimp [e2p]) (by bsimp []) (by bsimp [])
    ⟨fun R3 Mt H3 F3 L3 y hk3 hp => ?_, fun R3 Mt sp' o1 o2 hr2 hout => ?_⟩
  · obtain ⟨C3, hd3, hkeep3⟩ := hd2.newNum hp.rest hp.heap hp.refs hp.norm hp.pos hp.owns fun a ha =>
      hp.out a ha.outHeap (fun hs => by have := ha.lt; simp only [heapStart, slotBytes] at this hs; omega)
        (fun hf => by have := ha.lt; simp only [heapStart, frameIn] at this hf; omega)
    have agT : ∀ a, sp - 32 ≤ a → a < sp → imgM Mt a = imgM M1 a := fun a e1 e2 => by
      rw [hp.out a (above_sp hab2 e1).1 (fun hs => by simp only [slotBytes] at hs; omega)
        ((above_sp hab2 e1).2.2 176)]
      exact ag2 a e1 e2
    have e16 : ldv .ld Mt (sp - 32 + 16) = R 8 := by
      rw [ldv_congr .ld fun j hj => agT _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact l16
    have e24 : ldv .ld Mt (sp - 32 + 24) = R 1 := by
      rw [ldv_congr .ld fun j hj => agT _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact l24
    have q3 : R3 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
    have hS3 : HeapOwn S := fun a e1 e2 => hd3.heap.heap.own a e1 e2
    bsimp []
    bc_run hlive hS3 [q3, e16, e24]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    · exact hin.al
    refine hret _ Mt H3 F3 (y :: L3) C3 G y.rep.p (Num.sub na nb 0)
      (Keeps.restore (by rw [h2]; congr 1; omega) (Keeps.upd _ (by decide) (Keeps.restore rfl
        (by keeps_tac ((hk3.mono (by decide)).trans
          (by keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))))))
      ⟨by bsimp [], hd3, rfl, ⟨y, List.mem_cons_self, rfl, by rw [hp.num, e1n, e2n]⟩,
        by rw [hp.slot, (hp.heap.blocks y List.mem_cons_self).sPay], rfl, by omega,
        fun a ho hg hf hs => ?_⟩
    rw [hp.out a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega), hfr2 a ho hs]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
  · bc_run hlive hS2 [] at 0x80001e74
    refine hoom R3 Mt sp' ⟨by omega, by omega, hr2, fun a ho hg hf hs => ?_⟩
    rw [hout a ho fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega), hfr2 a ho hs]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)


/-- **`_zero_` as the Karatsuba steps need it**: the one digit `0`, with
room for `2^30 + 8` more references while the caller holds at most `2^20`
handles. -/
theorem DcAt.kzero {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    (hhs : hs.length ≤ 2 ^ 20) : KZero M C.z (2 ^ 30 + 8) := by
  have hz := h.den.mz
  have hsh := (h.heap.nums C.z hz).shape
  have hdl := hsh.dsLen
  have hnorm := h.den.norm C.z hz
  have hpos := h.den.pos C.z hz
  have hv := h.den.zv
  simp only [NumRep.Norm] at hnorm
  simp only [NumRep.num, Num.zero, Num.mk.injEq] at hv
  obtain ⟨hneg, hd, hsc⟩ := hv
  have hds : C.z.rep.ds = [0] ∧ C.z.rep.len = 1 := by
    cases e : C.z.rep.ds with
    | nil => rw [e] at hdl; simp only [List.length_nil] at hdl; omega
    | cons d rest =>
      rw [e] at hdl hd hnorm
      rw [dval_cons] at hd
      cases rest with
      | nil =>
        simp only [List.length_nil, List.length_cons, Nat.pow_zero, Nat.mul_one, dval_nil, Nat.add_zero]
          at hdl hd
        exact ⟨by rw [hd], by omega⟩
      | cons d' rest' =>
        simp only [List.length_cons] at hdl
        rcases hnorm with h1 | h1
        · omega
        · simp only [List.getD_cons_zero] at h1
          have : 0 < d * 10 ^ (rest'.length + 1) := Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
          simp only [List.length_cons] at hd; omega
  have hr := h.den.numRefs C.z hz
  have hc := h.count_le (.num C.z.rep.p)
  have hc3 : C.cnt C.z.rep.p ≤ 3 := by
    unfold BcConsts.cnt; exact Nat.le_trans (List.countP_le_length) (by simp)
  have hc1 : 1 ≤ C.cnt C.z.rep.p := by
    unfold BcConsts.cnt; exact List.countP_pos_iff.mpr ⟨C.z, by simp, by simp⟩
  have := Nat.le_trans (List.count_le_length (a := C.z.rep.p) (l := G.lk)) h.den.lkLen
  exact ⟨h.view.zw, hds.2, hsc, hds.1, hneg, by omega, by omega⟩

/-- **Two numbers of the state as `bc_multiply`'s operands**, with `_zero_`
and `mul_base_digits`. -/
theorem DcAt.mulArgs {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {x1 x2 : NumObj} (h1 : x1 ∈ L) (h2 : x2 ∈ L) (hhs : hs.length ≤ 2 ^ 20) {k : Nat}
    (hk : k < 2 ^ 31) (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80) :
    MulArgs M L x1 x2 C.z k := by
  have hn1 := (h.heap.nums x1 h1).shape
  have hn2 := (h.heap.nums x2 h2).shape
  have a1 := hn1.vLo; have a2 := hn1.vHi; have b1 := hn2.vLo; have b2 := hn2.vHi
  simp only [heapStart, heapEnd] at a1 a2 b1 b2
  have p1 := h.den.pos x1 h1; have p2 := h.den.pos x2 h2
  exact ⟨h1, h2, h.den.mz, by omega, by omega, by omega, hk, (h.kzero hhs).mono (by omega), hmb⟩

/-- **A 48-byte operation frame** (`dc_mul`, `dc_div`, `dc_rem`, `dc_exp`):
the scale at `0`, `b` at `8`, the saved `s1`, `s0`, `ra` at `24`, `32`, `40`. -/
structure OpFrame48 (M : Mem) (sp : Nat) (R : Nat → BitVec 64) (k pb : Nat) : Prop where
  w0 : ldv .ld M (sp - 48) = BitVec.ofNat 64 k
  w8 : ldv .ld M (sp - 48 + 8) = BitVec.ofNat 64 pb
  w24 : ldv .ld M (sp - 48 + 24) = R 9
  w32 : ldv .ld M (sp - 48 + 32) = R 8
  w40 : ldv .ld M (sp - 48 + 40) = R 1

theorem OpFrame48.transport {M M' : Mem} {sp : Nat} {R : Nat → BitVec 64} {k pb : Nat}
    (h : OpFrame48 M sp R k pb) (hsp : 48 ≤ sp)
    (hag : ∀ a, sp - 48 ≤ a → a < sp → imgM M' a = imgM M a) : OpFrame48 M' sp R k pb where
  w0 := by rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact h.w0
  w8 := by rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact h.w8
  w24 := by rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact h.w24
  w32 := by rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact h.w32
  w40 := by rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact h.w40

/-- **A 48-byte operation's `bc_init_num (result)`** at `0x800049bc`, its
frame stored: the slot holds a new `_zero_` handle `x`, the operands are
`x1`, `x2` of the heap. -/
theorem op48_init {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M M1 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pa pb : Nat} {na nb : Num}
    {R : Nat → BitVec 64} {sp q N lk : Nat}
    (hin : OpIn S M H F L C G hs st pa pb na nb R sp q N lk) (hN : 48 ≤ N)
    (hM1 : MemOnly (frameIn sp 48) M1 M) (fr : OpFrame48 M1 sp R st.scale pb)
    (R1 : Nat → BitVec 64) (r10 : R1 10 = BitVec.ofNat 64 q) (hal1 : (R1 1).toNat % 4 = 0)
    (hk : ∀ R2 M2 L1 L2 x C2 x1 x2, Keeps [14, 15] R2 R1 →
      DcAt S M2 H F (L1 ++ x :: L2) C2 G (.num x.rep.p :: .num pa :: .num pb :: hs) st →
      ldv .ld M2 q = BitVec.ofNat 64 x.rep.p → x.rep.p = C.z.rep.p →
      x1 ∈ L1 ++ x :: L2 → x1.rep.p = pa → x1.rep.num = na →
      x2 ∈ L1 ++ x :: L2 → x2.rep.p = pb → x2.rep.num = nb →
      (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 48 a → imgM M2 a = imgM M a) →
      OpFrame48 M2 sp R st.scale pb → DWO live S Q t (R1 1) R2 M2) :
    DWO live S Q t 0x800049bc#64 R1 M1 := by
  have hsf := hin.frame
  have hsl := hsf.lo
  have hab := hin.above
  simp only [heapEnd] at hab
  have hqs := hin.slotHi
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have h1 := hin.h.outWrite hM1 fun a ha =>
    ⟨(above_sp (sp := sp - 48) hab2 (a := a) (by simp only [frameIn] at ha; omega)).1,
     (above_sp (sp := sp - 48) hab2 (a := a) (by simp only [frameIn] at ha; omega)).2.1⟩
  have hlen : (GV.num pa :: GV.num pb :: hs).length ≤ 2 ^ 30 := by
    have := hin.hsLen; simp only [List.length_cons]; omega
  refine dc_init_num_spec hlive h1 hlen hin.slot (by simp only [heapEnd]; omega) R1 r10 hal1
    fun R2 M2 L2 C2 hk2 hd2 hkeep hw2 hfr2 => ?_
  obtain ⟨x1, hx1, e1p, e1n⟩ := (hkeep _ List.mem_cons_self _ hin.da).numObj
  obtain ⟨x2, hx2, e2p, e2n⟩ := (hkeep _ (List.mem_cons_of_mem _ List.mem_cons_self) _ hin.db).numObj
  obtain ⟨L1, L2, x, rfl, hxp⟩ := hd2.handle_num
  rw [← hxp] at hd2 hw2
  exact hk R2 M2 L1 L2 x C2 x1 x2 hk2 hd2 hw2 hxp hx1 e1p e1n hx2 e2p e2n
    (fun a ho hs hf => by rw [hfr2 a ho hs]; exact hM1 a hf)
    (fr.transport (by omega) fun a h1 h2 =>
      hfr2 a (above_sp hab2 h1).1 fun hs => by simp only [slotBytes] at hs; omega)

/-- **An operation's success from a bc callee's result** `y` in the slot
(window `W` below `sp'`, inside the operation's `N` below `sp`). -/
theorem OpRet.of_binPost {S : Nat → Prop} {M M2 Mt : Mem} {H H3 : Heap} {F F3 : List Blk}
    {L1 L2 L3 : List NumObj} {x y : NumObj} {C2 : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb : Nat} {na nb n : Num} {f : Nat → Num → Num → Option Num} {sp q N sp' W lk : Nat}
    (hd2 : DcAt S M2 H F (L1 ++ x :: L2) C2 G (.num x.rep.p :: .num pa :: .num pb :: hs) st)
    (hp : BinPostW S (G.raws M2) M2 Mt H3 F3 L1 L2 x q sp' W n L3 y)
    (hval : f st.scale na nb = some n) (hw1 : sp' ≤ sp) (hw2 : sp - N ≤ sp' - W)
    (hab : heapEnd ≤ sp' - W) (hq : sp ≤ q)
    (hout0 : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp N a → imgM M2 a = imgM M a) :
    ∃ C3, ∀ R' : Nat → BitVec 64, R' 10 = 0#64 →
      OpRet S M Mt H3 F3 (y :: L3) C3 G G hs st pa pb na nb f R' sp q N lk y.rep.p n := by
  simp only [heapEnd] at hab
  obtain ⟨C3, hd3, -⟩ := hd2.newNum hp.rest hp.heap hp.refs hp.norm hp.pos hp.owns fun a ha =>
    hp.out a ha.outHeap (fun hs => by have := ha.lt; simp only [heapStart, slotBytes] at this hs; omega)
      (fun hf => by have := ha.lt; simp only [heapStart, frameIn] at this hf; omega)
  exact ⟨C3, fun R' ha0 => ⟨ha0, hd3, hval, ⟨y, List.mem_cons_self, rfl, hp.num⟩,
    by rw [hp.slot, (hp.heap.blocks y List.mem_cons_self).sPay], rfl, by omega,
    fun a ho _ hf hs => by
      rw [hp.out a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]
      exact hout0 a ho hs hf⟩⟩

/-- **`dc_mul` after `bc_multiply` returned** (`0x800022fc`): the slot's new
handle for the product, then the epilogue. -/
theorem mul_ret {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M M2 Mt : Mem} {H H3 : Heap} {F F3 : List Blk}
    {L1 L2 L3 : List NumObj} {x y : NumObj} {C2 : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb sp q W : Nat} {na nb n : Num}
    (hd2 : DcAt S M2 H F (L1 ++ x :: L2) C2 G (.num x.rep.p :: .num pa :: .num pb :: hs) st)
    (hp : BinPostW S (G.raws M2) M2 Mt H3 F3 L1 L2 x q (sp - 48) W n L3 y)
    (hn : n = Num.mul na nb st.scale)
    (hsf : StackFrame S sp (48 + W)) (hab : heapEnd + (48 + W) ≤ sp) (hq : sp ≤ q)
    (hout0 : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp (48 + W) a → imgM M2 a = imgM M a)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    {k0 pb0 : Nat} (fr : OpFrame48 M2 sp R k0 pb0)
    (R3 : Nat → BitVec 64) (q3 : R3 2 = BitVec.ofNat 64 (sp - 48))
    (kk : Keeps (8 :: 9 :: 2 :: opClob) R3 R)
    (hret : ∀ R' M' H' F' L' C' G' y r, Keeps opClob R' R →
      OpRet S M M' H' F' L' C' G G' hs st pa pb na nb (fun k a b => some (Num.mul a b k)) R' sp q
        (48 + W) 0 y r → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x800022fc#64 R3 Mt := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have hS3 : HeapOwn S := fun a e1 e2 => hp.heap.heap.own a e1 e2
  have agT : ∀ a, sp - 48 ≤ a → a < sp → imgM Mt a = imgM M2 a := fun a e1 e2 =>
    hp.out a (above_sp hab2 e1).1 (fun hs => by simp only [slotBytes] at hs; omega)
      ((above_sp hab2 e1).2.2 _)
  have frT := fr.transport (by omega) agT
  have e24 := frT.w24; have e32 := frT.w32; have e40 := frT.w40
  bc_run hlive hS3 [q3, e24, e32, e40]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hal
  obtain ⟨C3, hr⟩ := OpRet.of_binPost (f := fun k a b => some (Num.mul a b k)) hd2 hp
    (by rw [hn]) (by omega) (by omega) (by simp only [heapEnd]; omega) hq hout0
  exact hret _ Mt H3 F3 (y :: L3) C3 G y.rep.p n
    (Keeps.restore (by rw [h2]; congr 1; omega) (Keeps.upd _ (by decide) (Keeps.restore rfl
      (Keeps.restore rfl (by keeps_tac kk))))) (hr _ (by bsimp []))

/-- **`dc_mul`** at `0x800022c0`: `bc_init_num (result)`, then
`bc_multiply (a, b, result, kscale)`; the window holds `bc_multiply`'s
deepest recursion, no reference lost. -/
theorem dc_mul_spec {live S : Nat → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    DcOp live S 0x800022c0 (48 + (96 + rmStack (2 ^ 30))) 0 (fun _ _ _ => True) (fun k a b => some (Num.mul a b k)) := by
  intro Q t M H F L C G hs st pa pb na nb R sp q hin _ hret hfail hoom
  have hsf := hin.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := hin.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hqs := hin.slotHi
  have hql := hin.slot.lo; have hqh := hin.slot.hi; have hqa := hin.slot.al
  have hS : HeapOwn S := fun a e1 e2 => hin.h.heap.heap.own a e1 e2
  have h2 := hin.r2; have h10 := hin.r10; have h11 := hin.r11; have h12 := hin.r12
  have h13 := hin.r13
  bc_run hlive hS [h2, h10, h11, h12, h13, word_sub48] at 0x800049bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 48) (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 32, 8, R 8)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 pb)]) [(sp - 48, 8, BitVec.ofNat 64 st.scale)]) M :=
    fun a ha => by simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have l0 : ldv .ld (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 32, 8, R 8)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 pb)]) [(sp - 48, 8, BitVec.ofNat 64 st.scale)]) (sp - 48) =
      BitVec.ofNat 64 st.scale := ldv_store_hit _ _ _
  have l8 : ldv .ld (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 32, 8, R 8)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 pb)]) [(sp - 48, 8, BitVec.ofNat 64 st.scale)]) (sp - 48 + 8) =
      BitVec.ofNat 64 pb := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have l24 : ldv .ld (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 32, 8, R 8)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 pb)]) [(sp - 48, 8, BitVec.ofNat 64 st.scale)]) (sp - 48 + 24) =
      R 9 := by
    repeat rw [ldv_ld_miss _ _ (by omega)]
    rw [ldv_store_hit]
  have l32 : ldv .ld (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 32, 8, R 8)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 pb)]) [(sp - 48, 8, BitVec.ofNat 64 st.scale)]) (sp - 48 + 32) =
      R 8 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have l40 : ldv .ld (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 32, 8, R 8)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 pb)]) [(sp - 48, 8, BitVec.ofNat 64 st.scale)]) (sp - 48 + 40) =
      R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48 + 24, 8, R 9)]) [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 32, 8, R 8)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 pb)]) [(sp - 48, 8, BitVec.ofNat 64 st.scale)]) = M1
    at hM1 l0 l8 l24 l32 l40 ⊢
  have fr : OpFrame48 M1 sp R st.scale pb := by
    exact ⟨l0, l8, l24, l32, l40⟩
  refine op48_init hlive hin (by omega) hM1 fr _ (by bsimp []) (by bsimp [])
    fun R2 M2 L1 L2 x C2 x1 x2 hk2 hd2 hw2 _ hx1 e1p e1n hx2 e2p e2n hout2 fr2 => ?_
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have m0 := fr2.w0; have m8 := fr2.w8
  have hmb2 : ldv .lw M2 mulBaseAddr = BitVec.ofNat 64 80 :=
    (hin.mb.transport (M' := M2) fun a e1 e2 => by
      have ⟨o1, _, o3⟩ := mulBase_off e1 e2
      exact hout2 _ o1 (fun hs => by simp only [slotBytes, heapStart] at hs o3; omega)
        fun hf => by simp only [frameIn, heapStart] at hf o3; omega).word
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk2.get 2 (by decide)]; bsimp []
  have r8 : R2 8 = BitVec.ofNat 64 q := by rw [hk2.get 8 (by decide)]; bsimp []
  have r9 : R2 9 = BitVec.ofNat 64 pa := by rw [hk2.get 9 (by decide)]; bsimp []
  have hS2 : HeapOwn S := fun a e1 e2 => hd2.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS2 [q2, r8, r9, m0, m8] at 0x8000573c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hma := hd2.mulArgs hx1 hx2 (by have := hin.hsLen; simp only [List.length_cons]; omega)
    hd2.den.scale hmb2
  have hsz := hma.size
  refine bc_multiply_spec hlive (W := 96 + rmStack (2 ^ 30))
    ⟨hsf.within (m := 48) (n := 96 + rmStack (2 ^ 30)) (by omega) (by decide),
      by simp only [heapEnd]; omega, by omega, hin.slot,
      fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega), .inr (by omega),
      hin.mb.own, fun a ha => hd2.glob a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega),
      by bsimp [q2], by bsimp []⟩
    hma (by
      have := rmDepth_mono (show x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale) ≤ 2 ^ 30 by omega)
      unfold rmStack; omega)
    hd2.heap (hd2.resSlot hw2) (by bsimp [e1p]) (by bsimp [e2p]) (by bsimp []) (by bsimp [])
    ⟨fun R3 Mt H3 F3 L3 y hk3 hp => ?_, fun R3 Mt sp' o1 o2 hr2 hout => ?_⟩
  · refine mul_ret hlive hd2 hp (by rw [e1n, e2n]) hsf (by simp only [heapEnd]; omega) hqs
      (fun a ho hs hf => hout2 a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
      R h2 hin.al fr2 R3 (by rw [hk3.get 2 (by decide)]; bsimp [q2])
      ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))) hret
  · bc_run hlive hS2 [] at 0x80001e74
    refine hoom R3 Mt sp' ⟨by omega, by omega, hr2, fun a ho hg hf hs => ?_⟩
    rw [hout a ho fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]
    exact hout2 a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

end Dc.Mach
