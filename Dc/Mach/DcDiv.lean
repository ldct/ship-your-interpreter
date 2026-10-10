import Dc.Mach.DcArith
import Dc.Mach.Bc.DivSpec
import Dc.Mach.Bc.DivModEntry
import Dc.Size

/-!
# dc's division and remainder (M9)

    dc_div (a, b, kscale, result):
      bc_init_num (result);
      if (bc_divide (a, b, result, kscale)) {
        fprintf (stderr, "%s: divide by zero\n", progname);
        return DC_DOMAIN_ERROR;
      }
      return DC_SUCCESS;

On division by zero the `_zero_` reference `bc_init_num` stored in the
slot is lost (`DcAt.leak`).

- `NumRep.len_le_wid`: a number of the heap has at most `Num.wid` digits.
- `dc_div_spec`, `dc_rem_spec`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- A load of a word the prologue stored. -/
local macro "ld48" : tactic =>
  `(tactic| ((repeat rw [ldv_ld_miss _ _ (by omega)]); rw [ldv_store_hit]))

/-- **A handle given up**: the caller's handle `p` becomes a lost reference. -/
theorem DcAt.leak {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat}
    (h : DcAt S M H F L C G (.num p :: hs) st) (hl : G.lk.length < 2 ^ 29) :
    DcAt S M H F L C { G with lk := p :: G.lk } hs st where
  heap := h.heap
  nodup := h.nodup
  view := { h.view with }
  den :=
    { stk := h.den.stk, regs := h.den.regs, regsHi := h.den.regsHi
      hsDen := fun g hg => h.den.hsDen g (List.mem_cons_of_mem _ hg)
      owns := h.den.owns, norm := h.den.norm, pos := h.den.pos
      numRefs := fun x hx => by
        have e := h.den.numRefs x hx
        have ev : ({ G with lk := p :: G.lk } : DcG).vals = G.vals := rfl
        rw [ev]
        simp only [List.count_append, List.count_cons] at e ⊢
        by_cases ep : p = x.rep.p
        · subst ep; simp only [beq_self_eq_true, ite_true] at e ⊢; omega
        · have : (GV.num p == GV.num x.rep.p) = false := by simp [ep]
          have : (p == x.rep.p) = false := by simp [ep]
          simp only [*, Bool.false_eq_true, ite_false] at e ⊢; omega
      strRefs := fun o ho => by
        have e := h.den.strRefs o ho
        have ev : ({ G with lk := p :: G.lk } : DcG).vals = G.vals := rfl
        rw [ev]
        simp only [List.count_append, List.count_cons] at e ⊢
        simp at e ⊢; omega
      lkLen := by simp only [List.length_cons]; omega
      lkIn := fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq
        · obtain ⟨L1, L2, x, e, hx⟩ := h.handle_num
          exact ⟨x, by rw [e]; exact List.mem_append_right _ List.mem_cons_self, hx⟩
        · exact h.den.lkIn q hq
      mz := h.den.mz, mo := h.den.mo, mt := h.den.mt, zv := h.den.zv, ov := h.den.ov
      ibase := h.den.ibase, obase := h.den.obase, scale := h.den.scale, unwind := h.den.unwind
      lbuf := h.den.lbuf }
  glob := h.glob
  col := h.col

/-- **A number has at most `Num.wid` digits.** -/
theorem NumRep.len_le_wid {o : NumRep} (hs : NumShape o) (hn : o.Norm) :
    o.len + o.scale ≤ o.num.wid := by
  have := NumRep.size_le hs hn (lt_pow_decLen o.num.mag)
  have := one_le_decLen o.num.mag
  have e : o.num.scale = o.scale := rfl
  simp only [Num.wid]; omega

/-- **An operation's failure that loses the slot's handle** `p`, the
memory changed only on `P` (off the heap and the globals) since. -/
theorem OpFail.of_leak {S : Nat → Prop} {M M2 M' : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p pa pb : Nat}
    {na nb : Num} {f : Nat → Num → Num → Option Num} {sp q N : Nat} {P : Nat → Prop}
    {x1 x2 : NumObj}
    (hd2 : DcAt S M2 H F L C G (.num p :: .num pa :: .num pb :: hs) st)
    (hl : G.lk.length < 2 ^ 29)
    (hx1 : x1 ∈ L) (e1p : x1.rep.p = pa) (e1n : x1.rep.num = na)
    (hx2 : x2 ∈ L) (e2p : x2.rep.p = pb) (e2n : x2.rep.num = nb)
    (hnone : f st.scale na nb = none)
    (hm : MemOnly P M' M2) (hP : ∀ a, P a → OutHeap a ∧ ¬ DcGlob a)
    (hout : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slotBytes q a →
      imgM M' a = imgM M a)
    (R' : Nat → BitVec 64) (ha0 : R' 10 ≠ 0#64) :
    OpFail S M M' H F L C G { G with lk := p :: G.lk } hs st pa pb na nb f R' sp q N 1 where
  a0 := ha0
  h := (hd2.leak hl).outWrite hm hP
  val := hnone
  da := ⟨x1, hx1, e1p, e1n⟩
  db := ⟨x2, hx2, e2p, e2n⟩
  same := rfl
  lkLen := by simp only [List.length_cons]; omega
  out := hout

theorem divMsg : ProgMsg 0x80007cb8 17 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

/-- **`dc_div` after `bc_divide` returned `-1`** (`0x80002350`): the
message, then `1`; the slot's `_zero_` handle is lost. -/
theorem div_zero {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M M2 Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C2 : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {p pa pb : Nat} {na nb : Num} {x1 x2 : NumObj}
    (hd2 : DcAt S M2 H F L C2 G (.num p :: .num pa :: .num pb :: hs) st)
    (hl : G.lk.length < 2 ^ 29)
    (hx1 : x1 ∈ L) (e1p : x1.rep.p = pa) (e1n : x1.rep.num = na)
    (hx2 : x2 ∈ L) (e2p : x2.rep.p = pb) (e2n : x2.rep.num = nb)
    (hnone : Num.div na nb st.scale = none)
    {sp q k0 pb0 : Nat} (hsf : StackFrame S sp 352) (hab : heapEnd + 352 ≤ sp) (hq : sp ≤ q)
    (hout0 : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 48 a → imgM M2 a = imgM M a)
    (R : Nat → BitVec 64) (fr : OpFrame48 M2 sp R k0 pb0)
    (hfr : ∀ a, ¬ frameIn (sp - 48) 304 a → imgM Mt a = imgM M2 a)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (R3 : Nat → BitVec 64) (q3 : R3 2 = BitVec.ofNat 64 (sp - 48))
    (h30 : R3 10 = 0xffffffffffffffff#64)
    (kk : Keeps (8 :: 9 :: 2 :: opClob) R3 R)
    (hfail : ∀ R' M' H' F' L' C' G', Keeps opClob R' R →
      OpFail S M M' H' F' L' C' G G' hs st pa pb na nb (fun k a b => Num.div a b k) R' sp q 352 1 →
      DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80002350#64 R3 Mt := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 352 := by simp only [heapEnd]; omega
  have hd3 := hd2.outWrite (P := frameIn (sp - 48) 304) hfr fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have frT := fr.transport (by omega) fun a e1 e2 => hfr a (by simp only [frameIn]; omega)
  have hS3 : HeapOwn S := fun a e1 e2 => hd3.heap.heap.own a e1 e2
  have hpn := hd3.view.prog
  have hG := hd3.glob
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hS3 [q3, h30] at 0x80002368
  bc_run hlive hS3 [q3, hpn, stderr_word] at 0x80000774
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine fprintf_prog_spec hlive divMsg (by decide) (hsf.within (m := 48) (n := 304) (by omega) (by decide))
    (by simp only [stderrAddr]; omega) hd3.errFile _ ?_ ?_ ?_ ?_ ?_ fun R4 M4 hk4 hfr4 => ?_
  · bsimp [q3]
  · bsimp [stderrAddr]
  · bsimp []
  · bsimp []
  · bsimp []
  have frT4 := frT.transport (by omega) fun a e1 e2 => hfr4 a (.inr (by omega))
  have q4 : R4 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk4.get 2 (by decide)]; bsimp [q3]
  bsimp []
  bc_run hlive hS3 [q4, frT4.w24, frT4.w32, frT4.w40]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hal
  have hm4 : MemOnly (frameIn sp 352) M4 M2 := fun a ha => by
    have e1 := hfr4 a (by simp only [frameIn] at ha; omega)
    have hn : ¬ frameIn (sp - 48) 304 a := by
      intro h'
      simp only [frameIn] at ha h'
      omega
    exact e1.trans (hfr a hn)
  have hP4 : ∀ a, frameIn sp 352 a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have ho4 : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 352 a → ¬ slotBytes q a →
      imgM M4 a = imgM M a := fun a ho _ hf hs => by
    have e1 := hm4 a hf
    have e2 := hout0 a ho hs (by simp only [frameIn] at hf ⊢; omega)
    exact e1.trans e2
  refine hfail _ M4 H F L C2 _
    (Keeps.restore (by rw [h2]; congr 1; omega) (Keeps.upd _ (by decide) (Keeps.restore rfl
      (Keeps.restore rfl (by keeps_tac ((hk4.mono (by decide)).trans (by keeps_tac kk)))))))
    (OpFail.of_leak hd2 hl hx1 e1p e1n hx2 e2p e2n hnone hm4 hP4 ho4 _ (by bsimp []; decide))

/-- `_zero_`'s handle in the slot: the constant (so at least two references). -/
theorem DcAt.zero_refs {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {x : NumObj}
    (h : DcAt S M H F L C G (.num x.rep.p :: hs) st) (hx : x ∈ L) (hz : x.rep.p = C.z.rep.p) :
    2 ≤ x.rep.refs := by
  have hr := h.den.numRefs x hx
  have hc : 1 ≤ C.cnt x.rep.p := by
    unfold BcConsts.cnt; exact List.countP_pos_iff.mpr ⟨C.z, by simp, by simp [hz]⟩
  have : 1 ≤ (G.vals ++ GV.num x.rep.p :: hs).count (.num x.rep.p) := by
    rw [List.count_append, List.count_cons_self]; omega
  omega

/-- **`dc_div`** at `0x80002314`: `bc_init_num (result)`, then
`bc_divide (a, b, result, kscale)`; division by zero prints its message and
loses the `_zero_` reference in the slot. -/
theorem dc_div_spec {live S : Nat → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    DcOp live S 0x80002314 352 1 (fun k a b => a.wid + k + b.wid < 2 ^ 27)
      (fun k a b => Num.div a b k) := by
  intro Q t M H F L C G hs st pa pb na nb R sp q hin hok hret hfail hoom
  have hsf := hin.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := hin.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hqs := hin.slotHi
  have hql := hin.slot.lo; have hqh := hin.slot.hi; have hqa := hin.slot.al
  have hS : HeapOwn S := fun a e1 e2 => hin.h.heap.heap.own a e1 e2
  have h2 := hin.r2; have h10 := hin.r10; have h11 := hin.r11; have h12 := hin.r12
  have h13 := hin.r13
  have hzw := hin.h.view.zw
  bc_run hlive hS [h2, h10, h11, h12, h13, word_sub48] at 0x800049bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine op48_init hlive hin (by omega)
    (fun a ha => by simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)])
    ⟨?_, ?_, ?_, ?_, ?_⟩ _ (by bsimp []) (by bsimp [])
    fun R2 M2 L1 L2 x C2 x1 x2 hk2 hd2 hw2 hxz hx1 e1p e1n hx2 e2p e2n hout2 fr2 => ?_
  · ld48
  · ld48
  · ld48
  · ld48
  · ld48
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have m0 := fr2.w0; have m8 := fr2.w8
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk2.get 2 (by decide)]; bsimp []
  have r8 : R2 8 = BitVec.ofNat 64 q := by rw [hk2.get 8 (by decide)]; bsimp []
  have r9 : R2 9 = BitVec.ofNat 64 pa := by rw [hk2.get 9 (by decide)]; bsimp []
  have hS2 : HeapOwn S := fun a e1 e2 => hd2.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS2 [q2, r8, r9, m0, m8] at 0x8000589c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  -- the operands' sizes, `_zero_` in the slot
  have hn1 := hd2.heap.nums x1 hx1; have hn2 := hd2.heap.nums x2 hx2
  have hsz : x1.rep.len + x1.rep.scale + st.scale + x2.rep.len + x2.rep.scale < 2 ^ 27 := by
    have w1 := NumRep.len_le_wid hn1.shape (hd2.den.norm x1 hx1)
    have w2 := NumRep.len_le_wid hn2.shape (hd2.den.norm x2 hx2)
    rw [← e1n, ← e2n] at hok
    omega
  clear hok
  have hxm : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hz0 : ldv .ld M2 zeroAddr = ldv .ld M zeroAddr :=
    ldv_congr .ld fun j hj => hout2 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr,
        bcFreeAddr, widthOfM, dc_addrs] at hj ⊢; omega)
      (fun hs => by simp only [slotBytes, widthOfM, dc_addrs] at hs hj; omega)
      (fun hf => by simp only [frameIn, widthOfM, dc_addrs] at hf hj; omega)
  have hz2 : BitVec.ofNat 64 C2.z.rep.p = BitVec.ofNat 64 C.z.rep.p := by
    rw [← hd2.view.zw, hz0, hzw]
  have hzp : x.rep.p = C2.z.rep.p := by
    have hn0 := hd2.heap.nums C2.z hd2.den.mz
    have hnz := hin.h.heap.nums C.z hin.h.den.mz
    have a1 := hn0.shape.pLo; have a2 := hn0.shape.pHi
    have b1 := hnz.shape.pLo; have b2 := hnz.shape.pHi
    simp only [heapStart, heapEnd] at a1 a2 b1 b2
    rw [hxz]
    bv_nat at hz2
    omega
  have hr2 := hd2.zero_refs hxm hzp
  refine bc_divide_spec hlive (W := 304) (k := st.scale) (z := C2.z)
    ⟨hsf.within (m := 48) (n := 304) (by omega) (by decide), by simp only [heapEnd]; omega,
      by decide, hin.slot, fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega),
      .inr (by omega), .inr (by simp only [dc_addrs]; omega),
      fun a ha => hd2.glob a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega),
      by bsimp [q2], by bsimp []⟩
    ⟨fun m hm R3 Mt H3 F3 L3 y hk3 h30 hp => ?_, fun hnone R3 Mt hk3 h30 hfr => ?_,
      fun R3 Mt sp' o1 o2 hr2' hout => ?_⟩
    ⟨rfl, hx1, hx2, hd2.den.mz, fun e => absurd e (by omega), hsz, hd2.view.zw,
      hd2.den.pos x1 hx1⟩
    (by rw [hd2.den.zv]; rfl) hd2.heap (hd2.resSlot hw2) (by bsimp [e1p]) (by bsimp [e2p])
    (by bsimp []) (by bsimp [])
  · -- the quotient
    obtain ⟨C3, hr⟩ := OpRet.of_binPost (f := fun k a b => Num.div a b k) (na := na) (nb := nb)
      (N := 352) hd2 hp
      (by rw [← e1n, ← e2n]; exact hm) (by omega) (by omega) (by simp only [heapEnd]; omega) hqs
      fun a ho hs hf => hout2 a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
    have frT := fr2.transport (by omega) fun a e1 e2 =>
      hp.out a (above_sp hab2 e1).1 (fun hs => by simp only [slotBytes] at hs; omega)
        ((above_sp hab2 e1).2.2 _)
    have q3 : R3 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
    have hS3 : HeapOwn S := fun a e1 e2 => hp.heap.heap.own a e1 e2
    bsimp []
    bc_run hlive hS3 [q3, h30]
    all_goals (try (intro hc; exact absurd h30 hc))
    bc_run hlive hS3 [q3, frT.w24, frT.w32, frT.w40]
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    · exact hin.al
    refine hret _ Mt H3 F3 (y :: L3) C3 G y.rep.p m
      (Keeps.restore (by rw [h2]; congr 1; omega) (Keeps.restore rfl (Keeps.restore rfl
        (by keeps_tac ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
          (by keeps_tac Keeps.refl _ _))))))))
      (hr _ ?_)
    bsimp [h30]
  · -- division by zero
    exact div_zero hlive hd2 (by have := hin.lkLen; omega) hx1 e1p e1n hx2 e2p e2n
      (by rw [← e1n, ← e2n]; exact hnone) hsf (by simp only [heapEnd]; omega) hqs
      (fun a ho hs hf => hout2 a ho hs hf) R fr2 hfr h2 hin.al R3
      (by rw [hk3.get 2 (by decide)]; bsimp [q2]) h30
      ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))) hfail
  · bc_run hlive hS2 [] at 0x80001e74
    have l1 : sp - 352 ≤ sp' := by
      rw [show (352 : Nat) = 48 + 304 from rfl, ← Nat.sub_sub]; exact o1
    have l2 : sp' ≤ sp := Nat.le_trans o2 (Nat.sub_le sp 48)
    refine hoom R3 Mt sp' ⟨l1, l2, hr2', fun a ho hg hf hs => ?_⟩
    have n1 : ¬ frameIn (sp - 48) 304 a := by
      intro h'; simp only [frameIn] at hf h'; omega
    have n2 : ¬ frameIn sp 48 a := by
      intro h'; simp only [frameIn] at hf h'; omega
    rw [hout a ho hs n1]
    exact hout2 a ho hs n2

end Dc.Mach
