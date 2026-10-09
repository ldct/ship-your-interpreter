import Dc.Mach.Bc.DivSetup
import Dc.Mach.Format

/-!
# `bc_divide`'s quotient and `mval` allocation (`0x80005b94`)

- `DvBufs`: the frame, the number heap and the two operand buffers `num1`,
  `num2` (raw `malloc` blocks), before the quotient exists.
- `NewNumPost.raw`: a raw buffer survives `bc_new_num` and stays off the
  extended heap's owned blocks.
- `dvs_alloc`: `bc_new_num(qdigits - scale, scale)`, `memset` of its digits
  and `malloc(len2 + 1)` from `0x80005b94`, landing `DvBase` at `0x80005be0`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- The frame, the number heap and the operand buffers `num1` (`b1`) and
`num2` (`b2`) before the quotient and `mval` are allocated. -/
structure DvBufs (S : Nat → Prop) (Mt0 M : Mem) (R0 : Nat → BitVec 64) (sp W : Nat) (D : DvData)
    (H : Heap) (F : List Blk) (Lh : List NumObj) : Prop where
  saved : SavedWords M (sp - 208) divSlots R0
  heap : BcHeap S M H F Lh
  b1l : D.b1 ∈ H.live
  b2l : D.b2 ∈ H.live
  b1n : D.b1 ∉ F ++ objBlocks Lh
  b2n : D.b2 ∉ F ++ objBlocks Lh
  b12 : D.b1 ≠ D.b2
  pPay : D.P = D.b1.pay
  pIn : ∀ i, i < D.xs.length → D.b1.In (D.P + i)
  nIn : ∀ i, i ≤ D.L → D.b2.In (D.N + i)
  out : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a

/-- **A raw buffer survives `bc_new_num`**: still live, off the extended
heap's owned blocks, its bytes unchanged. -/
theorem NewNumPost.raw {S : Nat → Prop} {Mt Mt' : Mem} {H H' : Heap}
    {F F' : List Blk} {fr : Nat → Prop} {len scale : Nat} {x : NumObj}
    {L : List NumObj} (h : BcHeap S Mt H F L)
    (p : NewNumPost S Mt Mt' H H' F F' fr len scale x) {b : Blk} (hb : b ∈ H.live)
    (hno : b ∉ F ++ objBlocks L) :
    b ∈ H'.live ∧ b ∉ F' ++ objBlocks (x :: L) ∧ ∀ a, b.In a → imgM Mt' a = imgM Mt a := by
  have hnd := p.inv.live_nodup
  have hsb : b ≠ x.sb ∧ b ≠ x.db ∧ ∀ c, c ∈ F' → c ∈ F := by
    cases p.src with
    | reuse hf hl =>
      rw [hl] at hnd
      refine ⟨fun e => hno (List.mem_append_left _ (by rw [hf, ← e]; exact List.mem_cons_self)),
        fun e => (List.nodup_cons.mp hnd).1 (e ▸ hb), fun c hc => by
          rw [hf]; exact List.mem_cons_of_mem _ hc⟩
    | fresh _ hf' hl =>
      rw [hl] at hnd
      refine ⟨fun e => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (e ▸ hb),
        fun e => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ (e ▸ hb)),
        fun c hc => by rw [hf'] at hc; simp at hc⟩
  obtain ⟨h1, h2, h3⟩ := hsb
  refine ⟨p.src.live_mono hb, fun hm => ?_, fun a ha => p.live b hb h1 a ha⟩
  rcases List.mem_append.mp hm with hf | ho
  · exact hno (List.mem_append_left _ (h3 _ hf))
  · rw [objBlocks_cons, NumObj.blocks_own p.owns] at ho
    simp only [List.cons_append, List.mem_cons, List.nil_append] at ho
    rcases ho with e | e | e
    · exact h1 e
    · exact h2 e
    · exact hno (List.mem_append_right _ e)

/-- The registers `dvs_alloc` may change. -/
abbrev allocClob : List Nat := [1, 10, 11, 12, 13, 14, 15, 16, 21]

/-- A block `malloc` returns differs from every block live before. -/
theorem fresh_ne_live {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {b c : Blk}
    (hc : c ∈ H.live) (hsz : 1 ≤ b.sz) (hal : ∀ a, b.h ≤ a → a < b.fin → AllocByte H a) : c ≠ b :=
  fun e => live_not_alloc hi hc (show c.In c.pay by
    subst e; simp only [Blk.In, Blk.pay, Blk.fin]; omega)
    (hal _ (by rw [e]; simp only [Blk.pay]; omega) (by rw [e]; simp only [Blk.pay, Blk.fin]; omega))

/-- The quotient's integer length: `qdigits - scale`. -/
abbrev dvQlen (len1 L : Nat) : Nat := if len1 < L then 1 else len1 + 1 - L

/-- `bc_new_num(qlen, k)` at `0x80004250` (return `0x80005bb8`), `memset` of
its `qlen + k` digits, `malloc(L + 1)`. -/
theorem dvs_alloc_call {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {ql k : Nat}
    (cx : DvCtx S sp W) (bf : DvBufs S Mt0 M R0 sp W D H F Lh)
    (hql : 1 ≤ ql) (hsz : ql + k < 2 ^ 30) (hLs : D.L < 2 ^ 30)
    (s8 : ldv .ld M (sp - 208 + 8) = BitVec.ofNat 64 (ql + k))
    (s16 : ldv .ld M (sp - 208 + 16) = R 16)
    (h1 : R 1 = 0x80005bb8#64) (h2 : R 2 = BitVec.ofNat 64 (sp - 208))
    (h10 : R 10 = BitVec.ofNat 64 ql) (h11 : R 11 = BitVec.ofNat 64 k)
    (h27 : R 27 = BitVec.ofNat 64 (D.L + 1))
    (hoom : ∀ R' Mt' sp', sp - W ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
      (∀ a, OutHeap a → ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) →
      DW live S Q 0x80002bcc#64 R' Mt')
    (hnext : ∀ R' M' H' F' y b, DvBase S Mt0 M' R0 sp W { D with b3 := b, Bm := b.pay } H' F' Lh y →
      y.rep = zeroRep y.sb.pay y.db.pay ql k →
      (∀ a, D.b1.In a ∨ D.b2.In a → imgM M' a = imgM M a) →
      R' 21 = BitVec.ofNat 64 y.sb.pay → R' 16 = R 16 → Keeps allocClob R' R →
      DW live S Q 0x80005be0#64 R' M') :
    DW live S Q 0x80004250#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => bf.heap.heap.own a h1 h2
  have hsf' : StackFrame S (sp - 208) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  refine bc_new_num_spec hlive bf.heap.newHeap hsf' (len := ql) (scale := k)
    (by simp only [heapEnd]; omega) (by omega) hql _ h10 h11 h2 (by rw [h1]; decide)
    ⟨fun R1 M1 H1 F1 y hk1 hp1 hr1 => ?_, fun R' M' hr2' hout' => ?_⟩
  · rw [h1]
    have hb1 := NewNumPost.insert bf.heap hp1
    obtain ⟨r1l, r1n, r1m⟩ := NewNumPost.raw bf.heap hp1 bf.b1l bf.b1n
    obtain ⟨r2l, r2n, r2m⟩ := NewNumPost.raw bf.heap hp1 bf.b2l bf.b2n
    have hout : ∀ a, heapEnd ≤ a → OutHeap a := fun a h => by
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at h ⊢; omega
    have hm1 : ∀ a, OutHeap a → ¬ frameIn (sp - 208) 32 a → imgM M1 a = imgM M a := hp1.out
    have r1 : R1 1 = 0x80005bb8#64 := by rw [hk1.get 1]; exact h1
    have r2 : R1 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk1.get 2]; exact h2
    have l8 : ldv .lwu M1 (sp - 208 + 8) = BitVec.ofNat 64 (ql + k) := by
      rw [lwuOfLd, ldv_congr .ld fun j hj => hm1 _ (hout _ (by simp only [heapEnd]; omega))
        (by simp only [frameIn, widthOfM] at hj ⊢; omega), s8, BitVec.toNat_ofNat]
      congr 1; omega
    have hn0 := hb1.nums y List.mem_cons_self
    num_facts hn0
    have hyp := (hb1.blocks y List.mem_cons_self).sPay
    have hv0 : ldv .ld M1 (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by
      rw [← hyp]; exact hn0.value
    have hls : y.rep.len + y.rep.scale = ql + k := by rw [hp1.rep]; rfl
    bc_run hlive hS [r1, r2, hr1, hv0, l8] at 0x80000890
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hob : OwnedBytes S y.rep.val (ql + k) :=
      ⟨fun i hi => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
        by omega⟩
    refine memset_spec hlive hob _ (by bsimp [hv0]) (by bsimp []) (by bsimp []) fun R2 M2 hk2 hf => ?_
    bsimp [] at hf ⊢
    have hb2 := BcHeap.zeroAgain hb1 hp1.rep hf
    have hm2 : ∀ a, OutHeap a → imgM M2 a = imgM M1 a := fun a ha =>
      hf.rest a (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)
    have hyb := hb1.blocks y List.mem_cons_self
    have hydm : y.db ∈ F1 ++ objBlocks (y :: Lh) := List.mem_append_right _ (hb1.db_mem List.mem_cons_self)
    have hdb : ∀ a, y.rep.val ≤ a → a < y.rep.val + (ql + k) → y.db.In a := fun a h1 h2 => by
      have := hyb.dLo; have := hyb.dFit; simp only [Blk.In]; omega
    have hb2m : ∀ a, D.b1.In a ∨ D.b2.In a → imgM M2 a = imgM M1 a := fun a ha => hf.rest a (by
      rcases Nat.lt_or_ge a y.rep.val with h | h
      · exact .inl h
      refine .inr (Nat.le_of_not_lt fun h' => ?_)
      rcases ha with ha | ha
      · exact live_apart hb1.heap r1l hyb.dLive (fun e => r1n (e ▸ hydm)) ha (hdb a h h')
      · exact live_apart hb1.heap r2l hyb.dLive (fun e => r2n (e ▸ hydm)) ha (hdb a h h'))
    have q27 : R2 27 = BitVec.ofNat 64 (D.L + 1) := by rw [hk2.get 27]; bsimp [hk1.get 27, h27]
    have q2 : R2 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk2.get 2]; bsimp [r2]
    bc_run hlive hS [q27, q2] at 0x8000096c
    refine malloc_spec hlive hb2.heap (n := D.L + 1) (by omega) _ (by bsimp [q27]) (by bsimp [])
      fun R3 M3 H3 hk3 hpost => ?_
    bsimp []
    have hMall : ∀ a, OutHeap a → ¬ frameIn (sp - 208) 32 a → imgM M3 a = imgM M a := fun a ho hf =>
      (hpost.frame a (OutHeap.not_alloc hb2.heap ho)).trans ((hm2 a ho).trans (hm1 a ho hf))
    have q3 : R3 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk3.get 2]; bsimp [q2]
    have l16 : ldv .ld M3 (sp - 208 + 16) = R 16 := by
      rw [ldv_congr .ld fun j hj => hMall _ (hout _ (by simp only [heapEnd]; omega))
        (by simp only [frameIn, widthOfM] at hj ⊢; omega)]; exact s16
    cases hres : hpost.res with
    | null e1 e2 e3 =>
      iterate 2 all_goals (try bc_run hlive hS [e1, q3] at 0x80002bcc)
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      exact hoom _ _ (sp - 208) (by omega) (by omega) (by bsimp [q3]) fun a ha hf => by
        simp only [frameIn] at hf
        simp (disch := omega) only [imgM_store_miss]
        exact (hMall a ha (by simp only [frameIn]; omega)).trans (bf.out a ha (by simp only [frameIn]; omega))
    | block b e1 e2 e3 e4 e5 =>
      bc_run hlive hS [e1, q3] at 0x80005be0
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      · intro hc; exfalso
        have hbl : b ∈ H3.live := by rw [e3]; exact List.mem_cons_self
        have fbb := hpost.inv.blk (List.mem_append_right _ hbl)
        have hsl := fbb.lo
        have hbp : b.pay = b.h + 16 := rfl
        bv_nat at hc
        simp only [heapStart] at hsl
        have hsf2 := fbb.fin; have hst := fbb.top
        have hbf : b.fin = b.h + 16 + b.sz := rfl
        simp only [heapEnd] at hst
        rw [Nat.mod_eq_of_lt (by omega)] at hc
        omega
      intro _
      have hbl : b ∈ H3.live := by rw [e3]; exact List.mem_cons_self
      have hst := (hpost.inv.blk (List.mem_append_right _ hbl)).top
      simp only [heapEnd] at hst
      have hh : ∀ a, a < heapEnd → imgM (writeLog M3 [(sp - 208 + 8, 8, BitVec.ofNat 64 b.pay)]) a =
          imgM M3 a := fun a h => by
        simp only [heapEnd] at h; simp (disch := omega) only [imgM_store_miss]
      have hb3 := hb2.malloc hpost
      have hb4 := hb3.transportOwn (fun a ha => hh a (AllocByte.bound hb3.heap ha).2)
        (fun c hc a ha => hh a (live_in_heap hb3.heap (hb3.owned_live hc) ha).2)
        (fun j hj => hh _ (by simp only [bcFreeAddr, heapEnd]; omega))
      refine hnext _ _ H3 F1 y b
        { saved := bf.saved.transport (lo := 104) (top := 208) (hag := fun a h1 h2 => by
            simp (disch := omega) only [imgM_store_miss]
            exact hMall a (hout a (by simp only [heapEnd]; omega)) (by simp only [frameIn]; omega))
          s8 := ldv_store_hit _ _ _
          heap := hb4
          owns := hp1.owns
          qzero := fun j => by
            rw [hp1.rep]
            simp only [zeroRep, List.getD_eq_getElem?_getD, List.getElem?_replicate]
            split <;> rfl
          b1l := hpost.res.live_mono r1l
          b2l := hpost.res.live_mono r2l
          b3l := hbl
          b1n := r1n
          b2n := r2n
          b3n := hb2.fresh_not_owned (b := b) (by omega) e5
          b12 := bf.b12
          b13 := fresh_ne_live (b := b) hb2.heap r1l (by omega) e5
          b23 := fresh_ne_live (b := b) hb2.heap r2l (by omega) e5
          pPay := bf.pPay
          mPay := rfl
          pIn := bf.pIn
          nIn := bf.nIn
          mIn := fun i hi => by simp only [Blk.In, Blk.fin, Blk.pay] at *; omega
          out := fun a ha hf => by
            simp only [frameIn] at hf
            simp (disch := omega) only [imgM_store_miss]
            exact (hMall a ha (by simp only [frameIn]; omega)).trans
              (bf.out a ha (by simp only [frameIn]; omega)) }
        hp1.rep (fun a ha => ?_) (by bsimp [hk3.get 21, hk2.get 21, hr1]) (by bsimp [l16]) ?_
      · have hin : a < heapEnd := by
          rcases ha with ha | ha
          · exact (live_in_heap bf.heap.heap bf.b1l ha).2
          · exact (live_in_heap bf.heap.heap bf.b2l ha).2
        rw [hh a hin, hpost.frame a ?_, hb2m a ha]
        · rcases ha with ha | ha
          · exact r1m a ha
          · exact r2m a ha
        · rcases ha with ha | ha
          · exact live_not_alloc hb2.heap r1l ha
          · exact live_not_alloc hb2.heap r2l ha
      · have K1 : Keeps allocClob R1 R := hk1.mono (by decide)
        keeps_tac ((hk3.mono (by decide) : Keeps allocClob R3 _).trans (by
          keeps_tac ((hk2.mono (by decide) : Keeps allocClob R2 _).trans
            (by keeps_tac K1 : Keeps allocClob _ R)) : Keeps allocClob _ R))
  · exact hoom R' M' (sp - 208 - 32) (by omega) (by omega) hr2' fun a ha hf =>
      (hout' a ha fun h => hf (by simp only [frameIn] at *; omega)).trans (bf.out a ha hf)

end

end Dc.Mach
