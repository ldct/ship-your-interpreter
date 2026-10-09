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

/-- The frame's saved registers, the number heap, and the bytes off the heap
outside the frame: what every setup stage of `bc_divide` keeps. -/
structure DvCore (S : Nat → Prop) (Mt0 M : Mem) (R0 : Nat → BitVec 64) (sp W : Nat)
    (H : Heap) (F : List Blk) (Lh : List NumObj) : Prop where
  saved : SavedWords M (sp - 208) divSlots R0
  heap : BcHeap S M H F Lh
  out : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a

/-- `DvCore` through stores to the frame words `sp - 208 … + 104`. -/
theorem DvCore.slots {S : Nat → Prop} {Mt0 M M' : Mem} {R0 : Nat → BitVec 64} {sp W : Nat}
    {H : Heap} {F : List Blk} {Lh : List NumObj}
    (bf : DvCore S Mt0 M R0 sp W H F Lh) (hab : heapEnd + W ≤ sp) (hW : 208 ≤ W)
    (hm : ∀ a, (a < sp - 208 ∨ sp - 208 + 104 ≤ a) → imgM M' a = imgM M a) :
    DvCore S Mt0 M' R0 sp W H F Lh := by
  have hh : ∀ a, a < heapEnd → imgM M' a = imgM M a := fun a h => hm a (.inl (by omega))
  exact
    { saved := bf.saved.transport (lo := 104) (top := 208) (hag := fun a h1 _ => hm a (.inr h1))
      heap := bf.heap.transportOwn (fun a ha => hh a (AllocByte.bound bf.heap.heap ha).2)
        (fun c hc a ha => hh a (live_in_heap bf.heap.heap (bf.heap.owned_live hc) ha).2)
        (fun j hj => hh _ (by simp only [bcFreeAddr, heapEnd]; omega))
      out := fun a ho hf => (hm a (by simp only [frameIn] at hf; omega)).trans (bf.out a ho hf) }

/-- `DvCore` plus the operand buffers `num1` (`b1`) and `num2` (`b2`) before
the quotient and `mval` are allocated. -/
structure DvBufs (S : Nat → Prop) (Mt0 M : Mem) (R0 : Nat → BitVec 64) (sp W : Nat) (D : DvData)
    (H : Heap) (F : List Blk) (Lh : List NumObj) : Prop extends DvCore S Mt0 M R0 sp W H F Lh where
  b1l : D.b1 ∈ H.live
  b2l : D.b2 ∈ H.live
  b1n : D.b1 ∉ F ++ objBlocks Lh
  b2n : D.b2 ∉ F ++ objBlocks Lh
  b12 : D.b1 ≠ D.b2
  pPay : D.P = D.b1.pay
  pIn : ∀ i, i < D.xs.length → D.b1.In (D.P + i)
  nIn : ∀ i, i ≤ D.L → D.b2.In (D.N + i)

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

/-- The quotient's state after `bc_new_num` and the `memset` of its digits:
the zero number `y` heads the heap, the operand buffers and the bytes off
the heap below the callee's frame unchanged. -/
structure DvNew (S : Nat → Prop) (M M' : Mem) (sp : Nat) (D : DvData) (H' : Heap) (F' : List Blk)
    (Lh : List NumObj) (y : NumObj) (ql k : Nat) : Prop where
  heap : BcHeap S M' H' F' (y :: Lh)
  rep : y.rep = zeroRep y.sb.pay y.db.pay ql k
  owns : y.Owns
  b1l : D.b1 ∈ H'.live
  b2l : D.b2 ∈ H'.live
  b1n : D.b1 ∉ F' ++ objBlocks (y :: Lh)
  b2n : D.b2 ∉ F' ++ objBlocks (y :: Lh)
  keep : ∀ a, D.b1.In a ∨ D.b2.In a → imgM M' a = imgM M a
  out : ∀ a, OutHeap a → ¬ frameIn (sp - 208) 32 a → imgM M' a = imgM M a

/-- `bc_new_num(ql, k)` then `memset` of its digits from `DvBufs`. -/
theorem DvBufs.newNum {S : Nat → Prop} {Mt0 M M1 M2 : Mem} {R0 : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H H1 : Heap} {F F1 : List Blk} {Lh : List NumObj} {y : NumObj} {ql k : Nat}
    (bf : DvBufs S Mt0 M R0 sp W D H F Lh)
    (hp : NewNumPost S M M1 H H1 F F1 (frameIn (sp - 208) 32) ql k y)
    (hf : Filled M2 M1 y.rep.val (ql + k) fun _ => 0#8) : DvNew S M M2 sp D H1 F1 Lh y ql k := by
  have hb1 := NewNumPost.insert bf.heap hp
  obtain ⟨r1l, r1n, r1m⟩ := NewNumPost.raw bf.heap hp bf.b1l bf.b1n
  obtain ⟨r2l, r2n, r2m⟩ := NewNumPost.raw bf.heap hp bf.b2l bf.b2n
  have hn0 := hb1.nums y List.mem_cons_self
  num_facts hn0
  have hls : y.rep.len + y.rep.scale = ql + k := by rw [hp.rep]; rfl
  have hyb := hb1.blocks y List.mem_cons_self
  have hydm : y.db ∈ F1 ++ objBlocks (y :: Lh) :=
    List.mem_append_right _ (hb1.db_mem List.mem_cons_self)
  have hdb : ∀ a, y.rep.val ≤ a → a < y.rep.val + (ql + k) → y.db.In a := fun a h1 h2 => by
    have := hyb.dLo; have := hyb.dFit; simp only [Blk.In]; omega
  refine ⟨BcHeap.zeroAgain hb1 hp.rep hf, hp.rep, hp.owns, r1l, r2l, r1n, r2n, fun a ha => ?_,
    fun a ha hfr => (hf.rest a (by simp only [OutHeap, heapStart, heapEnd] at ha; omega)).trans
      (hp.out a ha hfr)⟩
  rw [hf.rest a ?_]
  · rcases ha with ha | ha
    · exact r1m a ha
    · exact r2m a ha
  rcases Nat.lt_or_ge a y.rep.val with h | h
  · exact .inl h
  refine .inr (Nat.le_of_not_lt fun h' => ?_)
  rcases ha with ha | ha
  · exact live_apart hb1.heap r1l hyb.dLive (fun e => r1n (e ▸ hydm)) ha (hdb a h h')
  · exact live_apart hb1.heap r2l hyb.dLive (fun e => r2n (e ▸ hydm)) ha (hdb a h h')

/-- A byte at or above the heap's end is off the heap. -/
theorem outHeap_of_ge {a : Nat} (h : heapEnd ≤ a) : OutHeap a := by
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at h ⊢; omega

/-- A block `malloc` returned has a nonzero payload address below `2^64`. -/
theorem MallocPost.pay_ne {S : Nat → Prop} {Mt Mt' : Mem} {H H' : Heap} {n : Nat} {b : Blk}
    (hp : MallocPost S Mt Mt' H H' n (BitVec.ofNat 64 b.pay)) (hbl : b ∈ H'.live) :
    BitVec.ofNat 64 b.pay ≠ 0#64 := fun hc => by
  have fbb := hp.inv.blk (List.mem_append_right _ hbl)
  have hsl := fbb.lo
  have hbp : b.pay = b.h + 16 := rfl
  bv_nat at hc
  simp only [heapStart] at hsl
  have hsf2 := fbb.fin; have hst := fbb.top
  have hbf : b.fin = b.h + 16 + b.sz := rfl
  simp only [heapEnd] at hst
  rw [Nat.mod_eq_of_lt (by omega)] at hc
  omega

/-- **`malloc(L + 1)` for `mval`** after `DvNew`, its address stored at
`sp - 208 + 8`: `DvBase`. -/
theorem DvNew.base {S : Nat → Prop} {Mt0 M M2 M3 : Mem} {R0 : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H H1 H3 : Heap} {F F1 : List Blk} {Lh : List NumObj} {y : NumObj} {ql k : Nat}
    {b : Blk} (bf : DvBufs S Mt0 M R0 sp W D H F Lh) (dn : DvNew S M M2 sp D H1 F1 Lh y ql k)
    (hab : heapEnd + W ≤ sp) (hW : 272 ≤ W)
    (hpost : MallocPost S M2 M3 H1 H3 (D.L + 1) (BitVec.ofNat 64 b.pay)) (e2 : D.L + 1 ≤ b.sz)
    (e3 : H3.live = b :: H1.live) (e5 : ∀ a, b.h ≤ a → a < b.fin → AllocByte H1 a) :
    DvBase S Mt0 (writeLog M3 [(sp - 208 + 8, 8, BitVec.ofNat 64 b.pay)]) R0 sp W
      { D with b3 := b, Bm := b.pay } H3 F1 Lh y ∧
    ∀ a, D.b1.In a ∨ D.b2.In a →
      imgM (writeLog M3 [(sp - 208 + 8, 8, BitVec.ofNat 64 b.pay)]) a = imgM M a := by
  have hb2 := dn.heap
  have hMall : ∀ a, OutHeap a → ¬ frameIn (sp - 208) 32 a → imgM M3 a = imgM M a := fun a ho hf =>
    (hpost.frame a (OutHeap.not_alloc hb2.heap ho)).trans (dn.out a ho hf)
  have hbl : b ∈ H3.live := by rw [e3]; exact List.mem_cons_self
  simp only [heapEnd] at hab
  have hh : ∀ a, a < heapEnd → imgM (writeLog M3 [(sp - 208 + 8, 8, BitVec.ofNat 64 b.pay)]) a =
      imgM M3 a := fun a h => by
    simp only [heapEnd] at h; simp (disch := omega) only [imgM_store_miss]
  have hb3 := hb2.malloc hpost
  have hb4 := hb3.transportOwn (fun a ha => hh a (AllocByte.bound hb3.heap ha).2)
    (fun c hc a ha => hh a (live_in_heap hb3.heap (hb3.owned_live hc) ha).2)
    (fun j hj => hh _ (by simp only [bcFreeAddr, heapEnd]; omega))
  refine ⟨{ saved := bf.saved.transport (lo := 104) (top := 208) (hag := fun a h1 h2 => by
              simp (disch := omega) only [imgM_store_miss]
              exact hMall a (outHeap_of_ge (by simp only [heapEnd]; omega))
                (by simp only [frameIn]; omega))
            s8 := ldv_store_hit _ _ _
            heap := hb4
            owns := dn.owns
            qzero := fun j => by
              rw [dn.rep]
              simp only [zeroRep, List.getD_eq_getElem?_getD, List.getElem?_replicate]
              split <;> rfl
            b1l := hpost.res.live_mono dn.b1l
            b2l := hpost.res.live_mono dn.b2l
            b3l := hbl
            b1n := dn.b1n
            b2n := dn.b2n
            b3n := hb2.fresh_not_owned (b := b) (by omega) e5
            b12 := bf.b12
            b13 := fresh_ne_live (b := b) hb2.heap dn.b1l (by omega) e5
            b23 := fresh_ne_live (b := b) hb2.heap dn.b2l (by omega) e5
            pPay := bf.pPay
            mPay := rfl
            pIn := bf.pIn
            nIn := bf.nIn
            mIn := fun i hi => by simp only [Blk.In, Blk.fin, Blk.pay] at *; omega
            out := fun a ha hf => by
              simp only [frameIn] at hf
              simp (disch := omega) only [imgM_store_miss]
              exact (hMall a ha (by simp only [frameIn]; omega)).trans
                (bf.out a ha (by simp only [frameIn]; omega)) }, fun a ha => ?_⟩
  have hin : a < heapEnd := by
    rcases ha with ha | ha
    · exact (live_in_heap bf.heap.heap bf.b1l ha).2
    · exact (live_in_heap bf.heap.heap bf.b2l ha).2
  rw [hh a hin, hpost.frame a ?_, dn.keep a ha]
  rcases ha with ha | ha
  · exact live_not_alloc hb2.heap dn.b1l ha
  · exact live_not_alloc hb2.heap dn.b2l ha

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
    have r1 : R1 1 = 0x80005bb8#64 := by rw [hk1.get 1]; exact h1
    have r2 : R1 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk1.get 2]; exact h2
    have l8 : ldv .lwu M1 (sp - 208 + 8) = BitVec.ofNat 64 (ql + k) := by
      rw [lwuOfLd, ldv_congr .ld fun j hj => hp1.out _ (outHeap_of_ge (by simp only [heapEnd]; omega))
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
    have dn := bf.newNum hp1 hf
    have q27 : R2 27 = BitVec.ofNat 64 (D.L + 1) := by rw [hk2.get 27]; bsimp [hk1.get 27, h27]
    have q2 : R2 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk2.get 2]; bsimp [r2]
    bc_run hlive hS [q27, q2] at 0x8000096c
    refine malloc_spec hlive dn.heap.heap (n := D.L + 1) (by omega) _ (by bsimp [q27]) (by bsimp [])
      fun R3 M3 H3 hk3 hpost => ?_
    bsimp []
    have hMall : ∀ a, OutHeap a → ¬ frameIn (sp - 208) 32 a → imgM M3 a = imgM M a := fun a ho hf =>
      (hpost.frame a (OutHeap.not_alloc dn.heap.heap ho)).trans (dn.out a ho hf)
    have q3 : R3 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk3.get 2]; bsimp [q2]
    have l16 : ldv .ld M3 (sp - 208 + 16) = R 16 := by
      rw [ldv_congr .ld fun j hj => hMall _ (outHeap_of_ge (by simp only [heapEnd]; omega))
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
      have hp' : MallocPost S M2 M3 H1 H3 (D.L + 1) (BitVec.ofNat 64 b.pay) := e1 ▸ hpost
      have hne := hp'.pay_ne (by rw [e3]; exact List.mem_cons_self)
      bc_run hlive hS [e1, q3] at 0x80005be0
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      · intro hc; exact absurd hc hne
      intro _
      obtain ⟨bs, hkeep⟩ := DvNew.base bf dn cx.above cx.big hp' e2 e3 e5
      refine hnext _ _ H3 F1 y b bs hp1.rep hkeep (by bsimp [hk3.get 21, hk2.get 21, hr1])
        (by bsimp [l16]) ?_
      have K1 : Keeps allocClob R1 R := hk1.mono (by decide)
      keeps_tac ((hk3.mono (by decide) : Keeps allocClob R3 _).trans (by
        keeps_tac ((hk2.mono (by decide) : Keeps allocClob R2 _).trans
          (by keeps_tac K1 : Keeps allocClob _ R)) : Keeps allocClob _ R))
  · exact hoom R' M' (sp - 208 - 32) (by omega) (by omega) hr2' fun a ha hf =>
      (hout' a ha fun h => hf (by simp only [frameIn] at *; omega)).trans (bf.out a ha hf)

/-- `DvBufs` through stores to the frame words `sp - 208 … + 104`. -/
theorem DvBufs.slots {S : Nat → Prop} {Mt0 M M' : Mem} {R0 : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj}
    (bf : DvBufs S Mt0 M R0 sp W D H F Lh) (hab : heapEnd + W ≤ sp) (hW : 208 ≤ W)
    (hm : ∀ a, (a < sp - 208 ∨ sp - 208 + 104 ≤ a) → imgM M' a = imgM M a) :
    DvBufs S Mt0 M' R0 sp W D H F Lh :=
  { bf with toDvCore := bf.toDvCore.slots hab hW hm }

/-- **The quotient and `mval`** from `0x80005b94` (`len1 + k ≥ L`): `qdigits`,
`bc_new_num(qdigits - k, k)`, `memset`, `malloc(L + 1)`. -/
theorem dvs_alloc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {D : DvData} {H : Heap} {F : List Blk}
    {Lh : List NumObj} {len1 k : Nat}
    (cx : DvCtx S sp W) (bf : DvBufs S Mt0 M R0 sp W D H F Lh)
    (hle : D.L ≤ len1 + k) (hL1 : 1 ≤ D.L) (hsz : len1 + k < 2 ^ 29)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h12 : R 12 = BitVec.ofNat 64 (k + 1))
    (h21 : R 21 = BitVec.ofNat 64 k) (h23 : R 23 = BitVec.ofNat 64 D.L)
    (h26 : R 26 = BitVec.ofNat 64 len1) (h27 : R 27 = BitVec.ofNat 64 (D.L + 1))
    (hoom : ∀ R' Mt' sp', sp - W ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
      (∀ a, OutHeap a → ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) →
      DW live S Q 0x80002bcc#64 R' Mt')
    (hnext : ∀ R' M' H' F' y b, DvBase S Mt0 M' R0 sp W { D with b3 := b, Bm := b.pay } H' F' Lh y →
      y.rep = zeroRep y.sb.pay y.db.pay (dvQlen len1 D.L) k →
      (∀ a, D.b1.In a ∨ D.b2.In a → imgM M' a = imgM M a) →
      R' 21 = BitVec.ofNat 64 y.sb.pay → R' 16 = R 16 → Keeps allocClob R' R →
      DW live S Q 0x80005be0#64 R' M') :
    DW live S Q 0x80005b94#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => bf.heap.heap.own a h1 h2
  have hin : ∀ a, D.b1.In a ∨ D.b2.In a → a + W < sp := fun a ha => by
    have : a < heapEnd := by
      rcases ha with ha | ha
      · exact (live_in_heap bf.heap.heap bf.b1l ha).2
      · exact (live_in_heap bf.heap.heap bf.b2l ha).2
    omega
  have hfin : ∀ (ql : Nat), dvQlen len1 D.L = ql → ql + k < 2 ^ 30 → 1 ≤ ql →
      ∀ R1, R1 1 = 0x80005bb8#64 → R1 2 = BitVec.ofNat 64 (sp - 208) → R1 10 = BitVec.ofNat 64 ql →
      R1 11 = BitVec.ofNat 64 k → R1 27 = BitVec.ofNat 64 (D.L + 1) → R1 16 = R 16 →
      Keeps allocClob R1 R →
      DW live S Q 0x80004250#64 R1
        (writeLog (writeLog M [(sp - 208 + 16, 8, R 16)]) [(sp - 208 + 8, 8, BitVec.ofNat 64 (ql + k))]) := by
    intro ql hq hqs hq1 R1 r1 r2 r10 r11 r27 r16 hk1
    subst hq
    refine dvs_alloc_call hlive cx (bf.slots hab (by omega) fun a ha => by
        simp (disch := omega) only [imgM_store_miss]) hq1 hqs (by omega)
      (by simp (disch := omega) only [ldv_store_hit])
      (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit, r16]) r1 r2 r10 r11 r27 hoom
      fun R' M' H' F' y b h1 h2 h3 h4 h5 h6 => hnext R' M' H' F' y b h1 h2
        (fun a ha => (h3 a ha).trans (by
          have := hin a ha
          simp (disch := omega) only [imgM_store_miss])) h4 (by rw [h5, r16]) (h6.trans hk1)
  bc_run hlive hS [h2, h12, h21, h23, h26, h27] at 0x80004250
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · intro hlt
    bc_run hlive hS [h2, h12, h21, h23, h26, h27] at 0x80004250
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hq : dvQlen len1 D.L = 1 := if_pos hlt
    rw [show k + 1 = 1 + k by omega]
    exact hfin 1 hq (by omega) (Nat.le_refl 1) _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
      (by bsimp [h21]) (by bsimp [h27]) (by bsimp []) (by keeps_tac Keeps.refl _ _)
  · intro hge
    have e1 := addw_ofNat (a := len1) (b := k + 1) (by omega)
    have e2 := subw_ofNat_le (a := len1 + (k + 1)) (b := D.L) (by omega) (by omega)
    have e3 := subw_ofNat_le (a := len1 + (k + 1) - D.L) (b := k) (by omega) (by omega)
    bc_run hlive hS [h2, h12, h21, h23, h26, h27, e1, e2, e3] at 0x80004250
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hq : dvQlen len1 D.L = len1 + 1 - D.L := if_neg hge
    rw [show len1 + (k + 1) - D.L = len1 + 1 - D.L + k by omega,
      show len1 + 1 - D.L + k - k = len1 + 1 - D.L by omega]
    exact hfin _ hq (by omega) (by omega) _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
      (by bsimp [h21]) (by bsimp [h27]) (by bsimp []) (by keeps_tac Keeps.refl _ _)

/-- **The zero quotient** from `0x80005a5c` (`len1 + k < L`): `bc_new_num(1, k)`,
`memset`, `malloc(L + 1)`, then the sign and the frees from `0x80005a90`. -/
theorem dvz_zero {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W k : Nat} {L1 L2 : List NumObj}
    {xr x1 x2 z : NumObj} {D : DvData} {H : Heap} {F : List Blk} {n : Option Num}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n)
    (hn : n = some ⟨false, 0, k⟩) (bf : DvBufs S Mt0 M R0 sp W D H F (L1 ++ xr :: L2))
    (hr0 : ResSlot Mt0 L1 xr q) (hx1 : x1 ∈ L1 ++ xr :: L2) (hx2 : x2 ∈ L1 ++ xr :: L2)
    (hz : z ∈ L1 ++ xr :: L2) (hzg : ldv .ld Mt0 zeroAddr = BitVec.ofNat 64 z.rep.p)
    (hks : k + 1 < 2 ^ 30) (hLs : D.L < 2 ^ 30)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 x1.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 x2.rep.p) (h12 : R 12 = BitVec.ofNat 64 (k + 1))
    (h18 : R 18 = BitVec.ofNat 64 D.P) (h19 : R 19 = BitVec.ofNat 64 D.b2.pay)
    (h21 : R 21 = BitVec.ofNat 64 k) (h22 : R 22 = BitVec.ofNat 64 q)
    (h27 : R 27 = BitVec.ofNat 64 (D.L + 1)) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005a5c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := cx.above; have hW := cx.big
  have dcx := cx.dv
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => bf.heap.heap.own a h1 h2
  have hal := cx.al
  have hoom := hk.oom
  bc_run hlive hS [h2, h12, h21] at 0x80004250
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hsf' : StackFrame S (sp - 208) 32 :=
    ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
  have bf' := bf.slots cx.above (by omega) (M' := writeLog M [(sp - 208 + 8, 8, BitVec.ofNat 64 (k + 1))])
    fun a ha => by simp (disch := omega) only [imgM_store_miss]
  refine bc_new_num_spec hlive bf'.heap.newHeap hsf' (len := 1) (scale := k)
    (by simp only [heapEnd]; omega) (by omega) (Nat.le_refl 1) _ (by bsimp []) (by bsimp [h21])
    (by bsimp [h2]) (by bsimp []) ⟨fun R1 M1 H1 F1 y hk1 hp1 hr1 => ?_, fun R' M' hr2' hout' => ?_⟩
  · bsimp []
    have hb1 := NewNumPost.insert bf'.heap hp1
    have r2 : R1 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk1.get 2]; bsimp [h2]
    have l8 : ldv .lwu M1 (sp - 208 + 8) = BitVec.ofNat 64 (1 + k) := by
      rw [lwuOfLd, ldv_congr .ld fun j hj => hp1.out _ (outHeap_of_ge (by simp only [heapEnd]; omega))
        (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
      simp (disch := omega) only [ldv_store_hit, BitVec.toNat_ofNat]
      congr 1; omega
    have hn0 := hb1.nums y List.mem_cons_self
    num_facts hn0
    have hyp := (hb1.blocks y List.mem_cons_self).sPay
    have hv0 : ldv .ld M1 (y.sb.pay + 32) = BitVec.ofNat 64 y.rep.val := by
      rw [← hyp]; exact hn0.value
    have hls : y.rep.len + y.rep.scale = 1 + k := by rw [hp1.rep]; rfl
    bc_run hlive hS [r2, hr1, hv0, l8] at 0x80000890
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hob : OwnedBytes S y.rep.val (1 + k) :=
      ⟨fun i hi => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
        by omega⟩
    refine memset_spec hlive hob _ (by bsimp [hv0]) (by bsimp []) (by bsimp []) fun R2 M2 hk2 hf => ?_
    bsimp [] at hf ⊢
    have dn := bf'.newNum hp1 hf
    have q27 : R2 27 = BitVec.ofNat 64 (D.L + 1) := by rw [hk2.get 27]; bsimp [hk1.get 27, h27]
    have q2 : R2 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk2.get 2]; bsimp [r2]
    bc_run hlive hS [q27, q2] at 0x8000096c
    refine malloc_spec hlive dn.heap.heap (n := D.L + 1) (by omega) _ (by bsimp [q27]) (by bsimp [])
      fun R3 M3 H3 hk3 hpost => ?_
    bsimp []
    have hMall : ∀ a, OutHeap a → ¬ frameIn (sp - 208) 32 a → imgM M3 a =
        imgM (writeLog M [(sp - 208 + 8, 8, BitVec.ofNat 64 (k + 1))]) a := fun a ho hf =>
      (hpost.frame a (OutHeap.not_alloc dn.heap.heap ho)).trans (dn.out a ho hf)
    have q3 : R3 2 = BitVec.ofNat 64 (sp - 208) := by rw [hk3.get 2]; bsimp [q2]
    cases hres : hpost.res with
    | null e1 e2 e3 =>
      iterate 2 all_goals (try bc_run hlive hS [e1, q3] at 0x80002bcc)
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      exact hoom _ _ (sp - 208) (by omega) (by omega) (by bsimp [q3]) fun a ha hf => by
        simp only [frameIn] at hf
        simp (disch := omega) only [imgM_store_miss]
        rw [hMall a ha (by simp only [frameIn]; omega)]
        simp (disch := omega) only [imgM_store_miss]
        exact bf.out a ha (by simp only [frameIn]; omega)
    | block b e1 e2 e3 e4 e5 =>
      have hp' : MallocPost S M2 M3 H1 H3 (D.L + 1) (BitVec.ofNat 64 b.pay) := e1 ▸ hpost
      have hne := hp'.pay_ne (by rw [e3]; exact List.mem_cons_self)
      bc_run hlive hS [e1, q3] at 0x80005a90
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      · intro hc; exact absurd hc hne
      intro _
      obtain ⟨bs, -⟩ := DvNew.base bf' dn cx.above cx.big hp' e2 e3 e5
      have hap := cx.slotApart
      have hzg' : ldv .ld (writeLog M3 [(sp - 208 + 8, 8, BitVec.ofNat 64 b.pay)]) zeroAddr =
          BitVec.ofNat 64 z.rep.p := by
        rw [ldv_congr .ld fun j hj => bs.out _ (constBytes_out (by
            simp only [constBytes, twoAddr, zeroAddr, widthOfM] at hj ⊢; omega))
          (by simp only [frameIn, zeroAddr, widthOfM] at hj ⊢; omega)]
        exact hzg
      have hy0 : dval y.rep.ds = 0 := by rw [dn.rep]; exact dval_replicate_zero _
      refine dvt_sign hlive cx hk hn ⟨bs.saved, by rw [bs.s8], ⟨hr0.refs, ?_, hr0.noView⟩,
          fun a ha _ hf => bs.out a ha hf, by bsimp [q3], by bsimp [hk3.get 22, hk2.get 22, hk1.get 22, h22],
          by bsimp [hk3.get 18, hk2.get 18, hk1.get 18, h18, bf.pPay],
          by bsimp [hk3.get 19, hk2.get 19, hk1.get 19, h19], ?_⟩
        bs.heap hx1 hx2 hz hzg' (by bsimp [hk3.get 8, hk2.get 8, hk1.get 8, h8])
        (by bsimp [hk3.get 9, hk2.get 9, hk1.get 9, h9]) (by bsimp [hk3.get 21, hk2.get 21, hr1])
        (fun h => absurd hy0 h) (fun _ => by rw [NumRep.num]; simp only [dn.rep, zeroRep, dval_replicate_zero])
        (by rw [dn.rep]; exact Nat.le_refl 1) (by rw [dn.rep]; rfl) bs.owns
        ⟨bs.b1l, bs.b2l, bs.b3l, bs.b1n, bs.b2n, bs.b3n, bs.b12, bs.b13, bs.b23⟩
      · rw [ldv_congr .ld fun j hj => bs.out _ (cx.slotOut _ ⟨by omega, by simp only [widthOfM] at hj; omega⟩)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
        exact hr0.word
      · have K1 : Keeps divAll R1 R0 := (hk1.mono (by decide)).trans (by keeps_tac hkp)
        keeps_tac ((hk3.mono (by decide) : Keeps divAll R3 _).trans (by
          keeps_tac ((hk2.mono (by decide) : Keeps divAll R2 _).trans
            (by keeps_tac K1 : Keeps divAll _ R0)) : Keeps divAll _ R0))
  · exact hoom R' M' (sp - 208 - 32) (by omega) (by omega) hr2' fun a ha hf => by
      rw [hout' a ha fun h => hf (by simp only [frameIn] at *; omega)]
      simp only [frameIn] at hf
      simp (disch := omega) only [imgM_store_miss]
      exact bf.out a ha (by simp only [frameIn]; omega)

/-- **`bc_divide` from `0x80005b94`** (`len1 + k ≥ L`) to its return: the
quotient's allocation, the normalisation, the loop. `D` carries the
normalised digits (`hX`, `hV`) of the raw buffers `xs0`, `vs0`. -/
theorem dvs_main {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr x1 x2 z : NumObj} {D : DvData} {H : Heap} {F : List Blk} {n : Option Num} {m : Num}
    {len1 k : Nat} {xs0 vs0 : List Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (bf : DvBufs S Mt0 M R0 sp W D H F (L1 ++ xr :: L2)) (hs : DvShape D)
    (hx0l : xs0.length = D.xs.length) (hx0d : IsDigits xs0) (hx2 : 2 ≤ xs0.length)
    (hx00 : xs0.getD 0 0 = 0) (hx0z : xs0.getD (xs0.length - 1) 0 = 0)
    (hv0l : vs0.length = D.L) (hv0d : IsDigits vs0) (hv00 : 0 < vs0.getD 0 0)
    (hX : D.xs = digBE (dvalBE xs0 * (10 / (vs0.getD 0 0 + 1))) xs0.length)
    (hV : D.vs = digBE (dvalBE vs0 * (10 / (vs0.getD 0 0 + 1))) D.L)
    (hx : ∀ i, i < xs0.length → imgM M (D.P + i) = BitVec.ofNat 8 (xs0.getD i 0))
    (hv : ∀ i, i < D.L → imgM M (D.N + i) = BitVec.ofNat 8 (vs0.getD i 0))
    (hsent : imgM M (D.N + D.L) = 0#8)
    (hoff : D.off = D.L - len1) (hkb : D.Kb + D.L = len1 + k) (hle : D.L ≤ len1 + k)
    (hsz : len1 + k < 2 ^ 29)
    (hm : m = ⟨if D.pre (D.Kb + 1) / D.V = 0 then false else x1.rep.neg != x2.rep.neg,
      D.pre (D.Kb + 1) / D.V, k⟩)
    (hr0 : ResSlot Mt0 L1 xr q) (hn1 : D.n1p = x1.rep.p) (hn2 : D.n2p = x2.rep.p) (hrs : D.rs = q)
    (hx1 : x1 ∈ L1 ++ xr :: L2) (hx2' : x2 ∈ L1 ++ xr :: L2) (hz : z ∈ L1 ++ xr :: L2)
    (hzg : ldv .ld Mt0 zeroAddr = BitVec.ofNat 64 z.rep.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 208)) (h8 : R 8 = BitVec.ofNat 64 D.n1p)
    (h9 : R 9 = BitVec.ofNat 64 D.n2p) (h12 : R 12 = BitVec.ofNat 64 (k + 1))
    (h16 : R 16 = BitVec.ofNat 64 (D.L + 1)) (h18 : R 18 = BitVec.ofNat 64 D.P)
    (h19 : R 19 = BitVec.ofNat 64 D.b2.pay) (h20 : R 20 = BitVec.ofNat 64 (len1 + k))
    (h21 : R 21 = BitVec.ofNat 64 k) (h22 : R 22 = BitVec.ofNat 64 D.rs)
    (h23 : R 23 = BitVec.ofNat 64 D.L) (h24 : R 24 = BitVec.ofNat 64 D.N)
    (h25 : R 25 = BitVec.ofNat 64 (xs0.length - 2)) (h26 : R 26 = BitVec.ofNat 64 len1)
    (h27 : R 27 = BitVec.ofNat 64 (D.L + 1)) (hkp : Keeps divAll R R0) :
    DW live S Q 0x80005b94#64 R M := by
  have hl1 := hs.l1
  have hTs := hs.small
  refine dvs_alloc hlive cx.dv bf hle hl1 hsz h2 h12 h21 h23 h26 h27 hk.oom
    fun R1 M1 H1 F1 y b bs hy hkeep r21 r16 K1 => ?_
  have hx' : ∀ i, i < xs0.length → imgM M1 (D.P + i) = BitVec.ofNat 8 (xs0.getD i 0) := fun i hi =>
    (hkeep _ (.inl (bf.pIn i (by omega)))).trans (hx i hi)
  have hv' : ∀ i, i < D.L → imgM M1 (D.N + i) = BitVec.ofNat 8 (vs0.getD i 0) := fun i hi =>
    (hkeep _ (.inr (bf.nIn i (by omega)))).trans (hv i hi)
  have hsent' : imgM M1 (D.N + D.L) = 0#8 := (hkeep _ (.inr (bf.nIn _ (Nat.le_refl _)))).trans hsent
  let D' : DvData := { D with b3 := b, Bm := b.pay, qv := y.sb.pay }
  have bs' : DvBase S Mt0 M1 R0 sp W D' H1 F1 (L1 ++ xr :: L2) y := { bs with }
  have hs' : DvShape D' := { hs with }
  have hyq : y.rep.len + y.rep.scale = dvQlen len1 D.L + k := by rw [hy]; rfl
  refine dvs_norm (D := D') hlive cx.dv bs' hx0l hx0d hx2 hx00 hx0z hv0l hv0d hv00 hX hV hl1
    (by simp only [D']; omega) (by omega) hx' hv' hsent' (by rw [K1.get 2]; exact h2) (by rw [r16]; exact h16)
    (by rw [K1.get 18]; exact h18) (by rw [K1.get 23]; exact h23) (by rw [K1.get 24]; exact h24)
    (by rw [K1.get 25]; exact h25) fun R2 M2 bs2 hx2s hv2s hsent2 r17 r16' K2 => ?_
  have g : ∀ r, r ∉ normClob → r ∉ allocClob → R2 r = R r := fun r h1 h2 => by
    rw [K2 r h1, K1 r h2]
  refine dvs_init (len1 := len1) (k := k) hlive cx.dv hs' bs2 hx2s hv2s hsent2 hoff hkb hle ?_
    (by omega) (by rw [g 2 (by decide) (by decide)]; exact h2)
    (by rw [g 8 (by decide) (by decide)]; exact h8) (by rw [g 9 (by decide) (by decide)]; exact h9)
    (by rw [g 18 (by decide) (by decide)]; exact h18)
    (by rw [g 19 (by decide) (by decide)]; exact h19)
    (by rw [K2.get 21]; exact r21) rfl
    (by rw [g 22 (by decide) (by decide)]; exact h22)
    (by rw [g 23 (by decide) (by decide)]; exact h23)
    (by rw [g 24 (by decide) (by decide)]; exact h24)
    (by rw [g 26 (by decide) (by decide)]; exact h26)
    (by rw [g 20 (by decide) (by decide)]; exact h20) r16' r17 ?_ fun R3 M3 st => ?_
  · rw [hyq]; simp only [D', dvQlen]; split <;> omega
  · exact (K2.mono (by decide)).trans ((K1.mono (by decide)).trans hkp)
  · exact dv_run hlive cx hk hn hs' st hr0 rfl hn1 hn2 hrs hx1 hx2' hz hzg
      (by rw [hm, hy]; rfl) (by rw [hy]; simp only [zeroRep, dvQlen]; split <;> omega)
      (by rw [hy]; rfl)

end

end Dc.Mach
