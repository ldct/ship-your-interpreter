import Dc.Mach.DcRegSet

/-!
# Freeing an array chain (M9)

`dc_array_free (head)` at `0x80003e20` walks a chain of array nodes that
has already left the state (`AfNodes`: each node fresh to the state, its
datum a handle the caller holds), freeing each node's datum through its
slot (`dc_free_num` / `dc_free_str`, slot inside the node, `SlotPlace.fresh`)
and then the node. The loop is `af_body` (one node) and `af_loop`
(induction); `dc_array_free_spec` adds the prologue and the epilogue.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- A chain of blocks from the pointer `p`, linked through the word at `+off`,
each block satisfying `P` with its ghost. -/
inductive PChain {α : Type} (Mt : Mem) (off : Nat) (P : Blk → α → Prop) :
    BitVec 64 → List (Blk × α) → Prop
  | nil : PChain Mt off P 0#64 []
  | cons {b : Blk} {x : α} {l : List (Blk × α)} : P b x →
      PChain Mt off P (ldv .ld Mt (b.pay + off)) l →
      PChain Mt off P (BitVec.ofNat 64 b.pay) ((b, x) :: l)

/-- A chain from a pointer word is a chain from the pointer it holds. -/
theorem LChain.toP {α : Type} {Mt : Mem} {off : Nat} {P : Blk → α → Prop} :
    ∀ {a : Nat} {l : List (Blk × α)}, LChain Mt off P a l → PChain Mt off P (ldv .ld Mt a) l
  | _, _, .nil h => by rw [h]; exact .nil
  | _, _, .cons h hp hl => by rw [h]; exact .cons hp hl.toP

/-- **Array nodes off the state**, from the pointer `p`: each node fresh to
the state, the blocks distinct. -/
structure AfNodes (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj) (G : DcG) (p : BitVec 64)
    (l : List (Blk × ANode)) : Prop where
  links : PChain M 24 (ANodeAt M) p l
  fresh : ∀ bn ∈ l, DcFresh H F L G bn.1
  nodup : (l.map (·.1)).Nodup

/-- The chain through memories agreeing on its blocks. -/
theorem PChain.frameA {M M' : Mem} :
    ∀ {p : BitVec 64} {l : List (Blk × ANode)}, PChain M 24 (ANodeAt M) p l →
      (∀ bn ∈ l, ∀ a, bn.1.In a → imgM M' a = imgM M a) → PChain M' 24 (ANodeAt M') p l
  | _, _, .nil, _ => .nil
  | _, _, .cons hp hl, hag => by
    obtain ⟨hp', hw⟩ := hp.frame (hag _ List.mem_cons_self)
    refine .cons hp' ?_
    rw [hw]; exact hl.frameA fun bn hm => hag bn (List.mem_cons_of_mem _ hm)

/-- The nodes through a step keeping them fresh and byte for byte. -/
theorem AfNodes.transport {M M' : Mem} {H H' : Heap} {F F' : List Blk} {L L' : List NumObj}
    {G G' : DcG} {p : BitVec 64} {l : List (Blk × ANode)} (h : AfNodes M H F L G p l)
    (hk : ∀ bn ∈ l, DcFresh H' F' L' G' bn.1 ∧ ∀ a, bn.1.In a → imgM M' a = imgM M a) :
    AfNodes M' H' F' L' G' p l :=
  ⟨h.links.frameA fun bn hm => (hk bn hm).2, fun bn hm => (hk bn hm).1, h.nodup⟩

/-- The first node of the chain. -/
theorem AfNodes.head {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {G : DcG}
    {p : BitVec 64} {b : Blk} {n : ANode} {l : List (Blk × ANode)}
    (h : AfNodes M H F L G p ((b, n) :: l)) :
    p = BitVec.ofNat 64 b.pay ∧ ANodeAt M b n ∧ DcFresh H F L G b ∧ b ∉ l.map (·.1) ∧
      AfNodes M H F L G (ldv .ld M (b.pay + 24)) l := by
  cases h with
  | mk hc hf hnd =>
  cases hc with
  | cons hp hl =>
  exact ⟨rfl, hp, hf _ List.mem_cons_self, (List.nodup_cons.mp hnd).1,
    ⟨hl, fun bn hm => hf bn (List.mem_cons_of_mem _ hm), (List.nodup_cons.mp hnd).2⟩⟩

/-- An empty chain starts at `NULL`. -/
theorem AfNodes.nil_ptr {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {G : DcG}
    {p : BitVec 64} (h : AfNodes M H F L G p []) : p = 0#64 := by
  cases h with
  | mk hc _ _ => cases hc; rfl

/-- A live block lies in the heap, 16-aligned. -/
theorem blk_bounds {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {b : Blk}
    (hb : b ∈ H.live) : heapStart + 16 ≤ b.pay ∧ b.pay + b.sz ≤ heapEnd ∧ b.pay % 16 = 0 := by
  have fbb := hi.blk (List.mem_append_right _ hb)
  have a1 : 2147603920 ≤ b.h := fbb.lo
  have a2 : b.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have a3 : b.h % 16 = 0 := fbb.al
  have e1 : b.pay = b.h + 16 := rfl
  have e2 : b.fin = b.h + 16 + b.sz := rfl
  simp only [heapStart, heapEnd]
  omega

/-- A nonzero pointer of a live block. -/
theorem blk_ptr_ne {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {b : Blk}
    (hb : b ∈ H.live) : BitVec.ofNat 64 b.pay ≠ 0#64 := fun hc => by
  have := blk_bounds hi hb
  have e := congrArg BitVec.toNat hc
  simp only [heapStart, heapEnd] at this
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat] at e
  omega

/-- **What `dc_array_free` leaves**: the ghost's nodes, the bytes off the heap,
the globals and the frame below `sp`, and every other fresh block. -/
structure AfPost (sp W : Nat) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj) (G : DcG)
    (bs : List Blk) (M' : Mem) (H' : Heap) (F' : List Blk) (L' : List NumObj) (G' : DcG) : Prop where
  same : SameNodes G G'
  out : StkOut sp W M' M
  fresh : ∀ c, DcFresh H F L G c → c ∉ bs →
    DcFresh H' F' L' G' c ∧ ∀ a, c.In a → imgM M' a = imgM M a

theorem AfPost.refl (sp W : Nat) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj) (G : DcG)
    (bs : List Blk) : AfPost sp W M H F L G bs M H F L G :=
  ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ hc _ => ⟨hc, fun _ _ => rfl⟩⟩

theorem AfPost.trans {sp W : Nat} {M M1 M2 : Mem} {H H1 H2 : Heap} {F F1 F2 : List Blk}
    {L L1 L2 : List NumObj} {G G1 G2 : DcG} {bs1 bs2 : List Blk}
    (h1 : AfPost sp W M H F L G bs1 M1 H1 F1 L1 G1) (h2 : AfPost sp W M1 H1 F1 L1 G1 bs2 M2 H2 F2 L2 G2) :
    AfPost sp W M H F L G (bs1 ++ bs2) M2 H2 F2 L2 G2 where
  same := ⟨h2.same.stk.trans h1.same.stk, h2.same.regs.trans h1.same.regs,
    h2.same.lbuf.trans h1.same.lbuf⟩
  out a ho hg hf := (h2.out a ho hg hf).trans (h1.out a ho hg hf)
  fresh c hc hm := by
    obtain ⟨hc1, hb1⟩ := h1.fresh c hc fun h => hm (List.mem_append_left _ h)
    obtain ⟨hc2, hb2⟩ := h2.fresh c hc1 fun h => hm (List.mem_append_right _ h)
    exact ⟨hc2, fun a ha => (hb2 a ha).trans (hb1 a ha)⟩

theorem AfPost.widen {sp W W' : Nat} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {G : DcG} {bs : List Blk} {M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj} {G' : DcG}
    (h : AfPost sp W M H F L G bs M' H' F' L' G') (hW : W ≤ W') : AfPost sp W' M H F L G bs M' H' F' L' G' :=
  { h with out := fun a ho hg hf => h.out a ho hg fun h' => hf ⟨by simp only [frameIn] at h'; omega, h'.2⟩ }

/-- **`free (b)`** of a node off the state, the rest of the chain kept. -/
theorem af_freeNode {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk} {p : BitVec 64}
    {rest : List (Blk × ANode)}
    (h : DcAt S M H F L C G hs st) (hfb : DcFresh H F L G b) (hr : AfNodes M H F L G p rest)
    (hbr : b ∉ rest.map (·.1))
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 b.pay) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H', Keeps [14, 15] R' R → DcAt S M' H' F L C G hs st →
      AfNodes M' H' F L G p rest → AfPost 0 0 M H F L G [b] M' H' F L G → DW live S Q (R 1) R' M') :
    DW live S Q 0x80000a0c#64 R M := by
  have hi := h.heap.heap
  obtain ⟨lpre, lpost, hl⟩ := List.append_of_mem hfb.live
  refine free_spec hlive hi hl R h10 hal fun R' M' hk1 hp => ?_
  have hpost : AfPost 0 0 M H F L G [b] M' ⟨H.braw, b :: H.free, lpre ++ lpost⟩ F L G :=
    ⟨⟨rfl, rfl, rfl⟩, fun a ho _ _ => hp.frame a (OutHeap.not_alloc hi ho), fun c hc hcb =>
      ⟨hc.afterFree hl (fun e => hcb (e ▸ List.mem_singleton_self _)) _ _,
        fun a ha => hp.frame a (live_not_alloc hi hc.live ha)⟩⟩
  refine hk R' M' _ hk1 (h.free hfb hl hp) (hr.transport fun bn hm => hpost.fresh bn.1 (hr.fresh bn hm)
    fun he => hbr (List.mem_map.mpr ⟨bn, hm, (List.mem_singleton.mp he)⟩)) hpost

/-- A post off every frame holds for any frame. -/
theorem AfPost.reframe {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {G : DcG} {bs : List Blk} {M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj} {G' : DcG}
    (h : AfPost 0 0 M H F L G bs M' H' F' L' G') (sp W : Nat) : AfPost sp W M H F L G bs M' H' F' L' G' :=
  { h with out := fun a ho hg _ => h.out a ho hg fun h' => by simp only [frameIn] at h'; omega }

theorem AfPost.sub {sp W : Nat} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {G : DcG} {bs bs' : List Blk} {M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj} {G' : DcG}
    (h : AfPost sp W M H F L G bs M' H' F' L' G') (hb : ∀ c ∈ bs, c ∈ bs') :
    AfPost sp W M H F L G bs' M' H' F' L' G' :=
  { h with fresh := fun c hc hm => h.fresh c hc fun h' => hm (hb c h') }

/-- The registers one node of `dc_array_free` may change past its datum. -/
abbrev afTailClob : List Nat := [1, 10, 13, 14, 15]

/-- A node's slot: inside the node, in the heap. -/
theorem af_slot {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) (hS : HeapOwn S)
    {b : Blk} (hb : b ∈ H.live) (hsz : 32 ≤ b.sz) :
    PtrSlot S (b.pay + 16) ∧ (∀ a, slotBytes (b.pay + 16) a → b.In a) := by
  have := blk_bounds hi hb
  simp only [heapStart, heapEnd] at this
  refine ⟨⟨fun i _ => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
    by simp only [tohostAddr]; omega, by omega⟩, fun a ha => ?_⟩
  simp only [slotBytes, Blk.In, Blk.pay, Blk.fin] at ha this ⊢; omega

/-- `dc_array_free` on a node holding a number (`0x80003eac`, `sp` lowered by
48, `s1` the node `b`, `s0` the next pointer): `dc_free_num` through the
node's slot, `free (b)`, then the loop test. -/
theorem af_num {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk} {n : ANode}
    {rest : List (Blk × ANode)} {p sp : Nat} {w : BitVec 64}
    (h : DcAt S M H F L C G (.num p :: (rest.map (·.2.v) ++ hs)) st) (hn : ANodeAt M b n)
    (hev : n.v = .num p) (hfb : DcFresh H F L G b) (hbr : b ∉ rest.map (·.1))
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h8 : R 8 = w) (hr : AfNodes M H F L G w rest)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h9 : R 9 = BitVec.ofNat 64 b.pay)
    (hk : ∀ R' M' H' F' L' C' G', Keeps afTailClob R' R →
      AfPost (sp - 48) 32 M H F L G [b] M' H' F' L' G' →
      DcAt S M' H' F' L' C' G' (rest.map (·.2.v) ++ hs) st → AfNodes M' H' F' L' G' w rest →
      HsKeep ⟨L, G.strs⟩ ⟨L', G'.strs⟩ (rest.map (·.2.v) ++ hs) →
      StrPin G.strs G'.strs (rest.map (·.2.v) ++ hs) →
      DW live S Q (if w = 0#64 then 0x80003e90#64 else 0x80003e5c#64) R' M') :
    DW live S Q 0x80003eac#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := h.heap.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  obtain ⟨hq, hqb⟩ := af_slot hi hS hfb.live hn.sz
  have hbb := blk_bounds hi hfb.live
  have hsz := hn.sz
  have hw : ldv .ld M (b.pay + 16) = BitVec.ofNat 64 p := by
    have := hn.dat.ptr; rw [hev] at this; simpa only [GV.ptr, Nat.add_assoc] using this
  simp only [heapEnd, heapStart] at hab hbb
  bc_run hlive hS [h2, h9] at 0x80002ba0
  refine dc_free_num_specP hlive (Pend.id G) h (q := b.pay + 16) hq (.fresh b hfb hqb) hw
    (StackFrame.sub (m := 48) (n := 32) hsf (by decide)) (by simp only [heapEnd]; omega)
    (Or.inl (by omega)) _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    fun R1 M3 H' F' L' C' hk1 h3 _ hfr hfc hkp => ?_
  have hne : ∀ bn ∈ rest, bn.1 ≠ b := fun bn hm e => hbr (List.mem_map.mpr ⟨bn, hm, e⟩)
  have hslot : ∀ c, DcFresh H F L G c → c ≠ b → ∀ a, c.In a → ¬ slotBytes (b.pay + 16) a :=
    fun c hc hcb a hca hs => live_apart hi hc.live hfb.live hcb hca (hqb a hs)
  have hp1 : AfPost (sp - 48) 32 M H F L G [b] M3 H' F' L' G :=
    ⟨⟨rfl, rfl, rfl⟩, fun a ho hg hf => hfr a ho hg hf fun hs => by
        have := (hqb a hs); have := live_in_heap hi hfb.live this; exact ho.1 this,
      fun c hc hcb => ⟨(hfc c hc).1, fun a ha => (hfc c hc).2 a ha
        (hslot c hc (fun e => hcb (e ▸ List.mem_singleton_self _)) a ha)⟩⟩
  have hr3 := hr.transport fun bn hm => hp1.fresh bn.1 (hr.fresh bn hm)
    fun he => hne bn hm (List.mem_singleton.mp he)
  have q9 : R1 9 = BitVec.ofNat 64 b.pay := by rw [hk1.get 9]; bsimp [h9]
  have q8 : R1 8 = w := by rw [hk1.get 8]; bsimp [h8]
  show DW live S Q 0x80003eb4#64 R1 M3
  bc_run hlive hS [q9] at 0x80000a0c
  refine af_freeNode hlive (M := M3) h3 (hfc b hfb).1 hr3 hbr _ ?_ ?_
    fun R2 M4 H4 hk2 h4 hr4 hp2 => ?_
  · bsimp [q9]
  · bsimp []
  have p8 : R2 8 = w := by rw [hk2.get 8]; bsimp [q8]
  have hpost := (hp1.trans (hp2.reframe (sp - 48) 32)).sub fun c hc => by
    rcases List.mem_append.mp hc with hc | hc <;> exact hc
  have hkk : Keeps afTailClob R2 R :=
    (hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  show DW live S Q 0x80003e58#64 R2 M4
  by_cases hz : w = 0#64
  · bc_run hlive hS [p8, hz] at 0x80003e90
    all_goals first | (intro hc; exact absurd hc (by decide)) | skip
    have := hk _ _ _ _ _ _ _ (by keeps_tac hkk) hpost h4 hr4 hkp (StrPin.refl _ _)
    simp only [hz, ↓reduceIte] at this; exact this
  · bc_run hlive hS [p8] at 0x80003e5c
    · intro hc; exact absurd hc hz
    intro _
    have := hk _ _ _ _ _ _ _ (by keeps_tac hkk) hpost h4 hr4 hkp (StrPin.refl _ _)
    simp only [hz, ↓reduceIte] at this; exact this

/-- `dc_array_free` on a node holding a string (`0x80003e7c`, `sp` lowered by
48, `s1` the node `b`, `s0` the next pointer): `dc_free_str` through the
node's slot, `free (b)`, then the loop test. -/
theorem af_str {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk} {n : ANode}
    {rest : List (Blk × ANode)} {p sp : Nat} {w : BitVec 64}
    (h : DcAt S M H F L C G (.str p :: (rest.map (·.2.v) ++ hs)) st) (hn : ANodeAt M b n)
    (hev : n.v = .str p) (hfb : DcFresh H F L G b) (hbr : b ∉ rest.map (·.1))
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h8 : R 8 = w) (hr : AfNodes M H F L G w rest)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h9 : R 9 = BitVec.ofNat 64 b.pay)
    (hk : ∀ R' M' H' F' L' C' G', Keeps afTailClob R' R →
      AfPost (sp - 48) 32 M H F L G [b] M' H' F' L' G' →
      DcAt S M' H' F' L' C' G' (rest.map (·.2.v) ++ hs) st → AfNodes M' H' F' L' G' w rest →
      HsKeep ⟨L, G.strs⟩ ⟨L', G'.strs⟩ (rest.map (·.2.v) ++ hs) →
      StrPin G.strs G'.strs (rest.map (·.2.v) ++ hs) →
      DW live S Q (if w = 0#64 then 0x80003e90#64 else 0x80003e5c#64) R' M') :
    DW live S Q 0x80003e7c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := h.heap.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  obtain ⟨hq, hqb⟩ := af_slot hi hS hfb.live hn.sz
  have hbb := blk_bounds hi hfb.live
  have hsz := hn.sz
  have hw : ldv .ld M (b.pay + 16) = BitVec.ofNat 64 p := by
    have := hn.dat.ptr; rw [hev] at this; simpa only [GV.ptr, Nat.add_assoc] using this
  simp only [heapEnd, heapStart] at hab hbb
  bc_run hlive hS [h2, h9] at 0x800039a4
  refine dc_free_str_specP hlive (Pend.id G) h (q := b.pay + 16) hq hw
    (StackFrame.sub (m := 48) (n := 32) hsf (by decide)) (by simp only [heapEnd]; omega)
    _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    fun R1 M3 H' G' hk1 hsn h3 hfr hfc hkp hpin => ?_
  have hne : ∀ bn ∈ rest, bn.1 ≠ b := fun bn hm e => hbr (List.mem_map.mpr ⟨bn, hm, e⟩)
  have hp1 : AfPost (sp - 48) 32 M H F L G [b] M3 H' F L G' :=
    ⟨hsn, hfr, fun c hc _ => hfc c hc⟩
  have hr3 := hr.transport fun bn hm => hp1.fresh bn.1 (hr.fresh bn hm)
    fun he => hne bn hm (List.mem_singleton.mp he)
  have q9 : R1 9 = BitVec.ofNat 64 b.pay := by rw [hk1.get 9]; bsimp [h9]
  have q8 : R1 8 = w := by rw [hk1.get 8]; bsimp [h8]
  show DW live S Q 0x80003e84#64 R1 M3
  bc_run hlive hS [q9] at 0x80000a0c
  refine af_freeNode hlive (M := M3) h3 (hfc b hfb).1 hr3 hbr _ ?_ ?_
    fun R2 M4 H4 hk2 h4 hr4 hp2 => ?_
  · bsimp [q9]
  · bsimp []
  have p8 : R2 8 = w := by rw [hk2.get 8]; bsimp [q8]
  have hpost := (hp1.trans (hp2.reframe (sp - 48) 32)).sub fun c hc => by
    rcases List.mem_append.mp hc with hc | hc <;> exact hc
  have hkk : Keeps afTailClob R2 R :=
    (hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  show DW live S Q 0x80003e8c#64 R2 M4
  have hk' := hk _ _ _ _ _ _ _ (by keeps_tac hkk) hpost h4 hr4 hkp hpin
  by_cases hz : w = 0#64
  · simp only [hz, ↓reduceIte] at hk'
    bc_run hlive hS [p8, hz] at 0x80003e90
    all_goals first | (intro hc; exact absurd (p8.symm.trans hc) hz) | skip
    all_goals first | (intro hc; exact absurd (p8.trans hz) hc) | skip
    all_goals try intro _
    all_goals exact hk'
  · simp only [hz, ↓reduceIte] at hk'
    bc_run hlive hS [p8] at 0x80003e5c
    · intro _; exact hk'
    · intro hc; exact absurd hz hc

/-- The registers the loop of `dc_array_free` may change. -/
abbrev afClob : List Nat := [1, 8, 9, 10, 11, 13, 14, 15]

/-- **One node of `dc_array_free`** (`0x80003e5c`, `sp` lowered by 48, `s0`
the node `b`, `s2 = 1`, `s3 = 2`): the datum freed by its type, the node
freed, `s0` the next pointer `w`. -/
theorem af_body {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk} {n : ANode}
    {rest : List (Blk × ANode)} {sp : Nat}
    (h : DcAt S M H F L C G (n.v :: (rest.map (·.2.v) ++ hs)) st) (hn : ANodeAt M b n)
    (hfb : DcFresh H F L G b) (hbr : b ∉ rest.map (·.1))
    (hr : AfNodes M H F L G (ldv .ld M (b.pay + 24)) rest)
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h8 : R 8 = BitVec.ofNat 64 b.pay)
    (h18 : R 18 = 1#64) (h19 : R 19 = 2#64)
    (hk : ∀ R' M' H' F' L' C' G', Keeps afClob R' R → R' 8 = ldv .ld M (b.pay + 24) →
      AfPost (sp - 48) 32 M H F L G [b] M' H' F' L' G' →
      DcAt S M' H' F' L' C' G' (rest.map (·.2.v) ++ hs) st →
      AfNodes M' H' F' L' G' (ldv .ld M (b.pay + 24)) rest →
      HsKeep ⟨L, G.strs⟩ ⟨L', G'.strs⟩ (rest.map (·.2.v) ++ hs) →
      StrPin G.strs G'.strs (rest.map (·.2.v) ++ hs) →
      DW live S Q (if ldv .ld M (b.pay + 24) = 0#64 then 0x80003e90#64 else 0x80003e5c#64) R' M') :
    DW live S Q 0x80003e5c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := h.heap.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hbb := blk_bounds hi hfb.live
  have hsz := hn.sz
  have hlw := hn.dat.lw
  generalize hw : ldv .ld M (b.pay + 24) = w at hr hk
  simp only [heapEnd, heapStart] at hab hbb
  cases hv : n.v with
  | num p =>
    rw [hv] at hlw h
    simp only [GV.tag] at hlw
    bc_run hlive hS [h2, h8, h18, h19, hlw, hw] at 0x80003eac
    all_goals first | (intro hc; exact absurd hc (by decide)) | skip
    all_goals try intro _
    refine af_num hlive h hn hv hfb hbr hsf (by simp only [heapEnd]; omega) _ ?_ hr
      ?_ ?_ fun R' M' H' F' L' C' G' hk1 hp h' hr' hkp hpin => ?_
    · bsimp [hw]
    · bsimp [h2]
    · bsimp [h8]
    exact hk R' M' H' F' L' C' G' ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
      (by rw [hk1.get 8]; bsimp [hw]) hp h' hr' hkp hpin
  | str p =>
    rw [hv] at hlw h
    simp only [GV.tag] at hlw
    bc_run hlive hS [h2, h8, h18, h19, hlw, hw] at 0x80003e7c
    all_goals first | (intro hc; exact absurd hc (by decide)) | skip
    all_goals try intro _
    all_goals try (bc_run hlive hS [h2, h8, h18, h19, hlw, hw] at 0x80003e7c)
    all_goals first | (intro hc; exact absurd hc (by decide)) | skip
    all_goals try intro _
    refine af_str hlive h hn hv hfb hbr hsf (by simp only [heapEnd]; omega) _ ?_ hr
      ?_ ?_ fun R' M' H' F' L' C' G' hk1 hp h' hr' hkp hpin => ?_
    · bsimp [hw]
    · bsimp [h2]
    · bsimp [h8]
    exact hk R' M' H' F' L' C' G' ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
      (by rw [hk1.get 8]; bsimp [hw]) hp h' hr' hkp hpin

/-- **The loop of `dc_array_free`** (`0x80003e5c`) over a nonempty chain:
every node and datum freed, `s0` `NULL` at `0x80003e90`. -/
theorem af_loop {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {hs : List GV} {st : St} {sp : Nat}
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp) :
    ∀ (rest : List (Blk × ANode)) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
      {C : BcConsts} {G : DcG} {b : Blk} {n : ANode}
      (_ : DcAt S M H F L C G (n.v :: (rest.map (·.2.v) ++ hs)) st)
      (_ : AfNodes M H F L G (BitVec.ofNat 64 b.pay) ((b, n) :: rest))
      (R : Nat → BitVec 64) (_ : R 2 = BitVec.ofNat 64 (sp - 48))
      (_ : R 8 = BitVec.ofNat 64 b.pay) (_ : R 18 = 1#64) (_ : R 19 = 2#64)
      (_ : ∀ R' M' H' F' L' C' G', Keeps afClob R' R → R' 8 = 0#64 →
        AfPost (sp - 48) 32 M H F L G (b :: rest.map (·.1)) M' H' F' L' G' →
        DcAt S M' H' F' L' C' G' hs st → HsKeep ⟨L, G.strs⟩ ⟨L', G'.strs⟩ hs →
        StrPin G.strs G'.strs hs → DW live S Q 0x80003e90#64 R' M'),
      DW live S Q 0x80003e5c#64 R M
  | rest, M, H, F, L, C, G, b, n, h, ha, R, h2, h8, h18, h19, hk => by
    obtain ⟨-, hn, hfb, hbr, hr⟩ := ha.head
    refine af_body hlive h hn hfb hbr hr hsf hab R h2 h8 h18 h19
      fun R' M' H' F' L' C' G' hk1 e8 hp h' hr' hkp hpin => ?_
    have k18 : R' 18 = 1#64 := by rw [hk1.get 18]; exact h18
    have k19 : R' 19 = 2#64 := by rw [hk1.get 19]; exact h19
    have k2 : R' 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; exact h2
    match rest, hr' with
    | [], hr' =>
      have hz := hr'.nil_ptr
      simp only [hz, ↓reduceIte]
      exact hk R' M' H' F' L' C' G' hk1 (e8.trans hz) (hp.sub fun c hc => by
        rw [List.mem_singleton.mp hc]; exact List.mem_cons_self) h'
        (hkp.mono fun g hg => List.mem_append_right _ hg)
        (hpin.mono fun g hg => List.mem_append_right _ hg)
    | (b', n') :: rest', hr' =>
      obtain ⟨e1, -, hfb', -, -⟩ := hr'.head
      have hnz : ldv .ld M (b.pay + 24) ≠ 0#64 := e1 ▸ blk_ptr_ne h'.heap.heap hfb'.live
      simp only [hnz, ↓reduceIte]
      refine af_loop hlive hsf hab rest' h' (e1 ▸ hr') R' k2 (e8.trans e1) k18 k19
        fun R'' M'' H'' F'' L'' C'' G'' hk2 e8' hp' h'' hkp' hpin' => ?_
      refine hk R'' M'' H'' F'' L'' C'' G'' (hk2.trans hk1) e8' ((hp.trans hp').sub fun c hc => ?_) h''
        ((hkp.mono fun g hg => List.mem_append_right _ hg).trans hkp')
        ((hpin.mono fun g hg => List.mem_append_right _ hg).trans hpin')
      rcases List.mem_append.mp hc with hc | hc
      · rw [List.mem_singleton.mp hc]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hc

/-- Registers restored to their entry values leave the kept set. -/
theorem Keeps.restoreAll {ks rs : List Nat} {R' R : Nat → BitVec 64} (h : Keeps (rs ++ ks) R' R)
    (he : ∀ z ∈ rs, R' z = R z) : Keeps ks R' R := fun z hz => by
  by_cases hm : z ∈ rs
  · exact he z hm
  · exact h z fun h' => (List.mem_append.mp h').elim hm hz

/-- The registers `dc_array_free` may change. -/
abbrev afFnClob : List Nat := [10, 11, 13, 14, 15]

/-- `dc_array_free`'s frame after the prologue's stores. -/
abbrev afProW (M : Mem) (sp : Nat) (R : Nat → BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 32, 8, R 8)])
    [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 8, 8, R 19)]) [(sp - 48 + 40, 8, R 1)])
    [(sp - 48 + 24, 8, R 9)]

/-- `dc_array_free`'s epilogue (`0x80003e90`, `sp` lowered by 48). -/
theorem af_epi {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp : Nat}
    (hsf : StackFrame S sp 80) {ra s0 s1 s2 s3 : BitVec 64}
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48))
    (h40 : ldv .ld M (sp - 48 + 40) = ra) (h32 : ldv .ld M (sp - 48 + 32) = s0)
    (h24 : ldv .ld M (sp - 48 + 24) = s1) (h16 : ldv .ld M (sp - 48 + 16) = s2)
    (h8 : ldv .ld M (sp - 48 + 8) = s3) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 8, 9, 18, 19] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 9 = s1 → R' 18 = s2 → R' 19 = s3 → DW live S Q ra R' M) :
    DW live S Q 0x80003e90#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h2, h40, h32, h24, h16, h8]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first | (bsimp []; exact hal) | skip
  exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp []; congr 1; omega) (by bsimp [])
    (by bsimp []) (by bsimp []) (by bsimp [])

/-- **`dc_array_free (p)`** at `0x80003e20` on a chain of array nodes off
the state, whose data are the caller's handles: every datum and node freed. -/
theorem dc_array_free_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {l : List (Blk × ANode)} {p : BitVec 64}
    {sp : Nat} (h : DcAt S M H F L C G (l.map (·.2.v) ++ hs) st) (ha : AfNodes M H F L G p l)
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = p) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps afFnClob R' R →
      AfPost sp 80 M H F L G (l.map (·.1)) M' H' F' L' G' → DcAt S M' H' F' L' C' G' hs st →
      HsKeep ⟨L, G.strs⟩ ⟨L', G'.strs⟩ hs → StrPin G.strs G'.strs hs → DW live S Q (R 1) R' M') :
    DW live S Q 0x80003e20#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := h.heap.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  simp only [heapEnd] at hab
  match l, h, ha with
  | [], h, ha =>
    have hz := ha.nil_ptr
    bc_run hlive hS [h10, hz]
    all_goals first | (intro hc; exact absurd hz hc) | skip
    all_goals try intro _
    all_goals try (bc_run hlive hS [h10, hz])
    exact hk R M H F L C G (Keeps.refl _ _) (AfPost.refl _ _ _ _ _ _ _ _) h (HsKeep.refl _ _) (StrPin.refl _ _)
  | (b, n) :: rest, h, ha =>
    obtain ⟨e1, -, hfb, -, -⟩ := ha.head
    have hnz : p ≠ 0#64 := e1 ▸ blk_ptr_ne hi hfb.live
    have hM1 : MemOnly (frameIn sp 48) (afProW M sp R) M := fun x hx => by
      simp only [frameIn] at hx
      simp only [afProW]
      repeat rw [imgM_store_miss _ _ (by omega)]
    have hfo : ∀ x, frameIn sp 48 x → OutHeap x ∧ ¬ DcGlob x := fun x hx => by
      simp only [frameIn] at hx
      exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
        have := hg.lt; simp only [heapStart] at this; omega⟩
    have h1 := h.outWrite hM1 hfo
    have ha1 := ha.transport fun bn hm => ⟨ha.fresh bn hm, fun x hx => hM1 x fun hf =>
      (hfo x hf).1.1 (live_in_heap hi (ha.fresh bn hm).live hx)⟩
    have e2 : BitVec.ofNat 64 sp + 18446744073709551568#64 = BitVec.ofNat 64 (sp - 48) := word_sub48 (by omega)
    bc_run hlive hS [h10, h2, e2] at 0x80003e5c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals first | (intro hc; exact absurd hc hnz) | skip
    all_goals try intro _
    all_goals try (bc_run hlive hS [h10, h2, e2] at 0x80003e5c)
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    show DW live S Q 0x80003e5c#64 _ (afProW M sp R)
    refine af_loop hlive hsf (by simp only [heapEnd]; omega) rest h1 (e1 ▸ ha1) _ ?_ ?_ ?_ ?_
      fun R' M' H' F' L' C' G' hk1 e8 hp h' hkp hpin => ?_
    · bsimp [e2]
    · bsimp [h10, e1]
    · bsimp []
    · bsimp []
    have k2 : R' 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp [e2]
    have hfr : ∀ k, k + 8 ≤ 48 → ldv .ld M' (sp - 48 + k) = ldv .ld (afProW M sp R) (sp - 48 + k) :=
      fun k hk' => ldv_congr .ld fun j hj => by
        have hx : frameIn sp 48 (sp - 48 + k + j) := by simp only [frameIn, widthOfM] at hj ⊢; omega
        exact hp.out _ (hfo _ hx).1 (hfo _ hx).2 (by simp only [frameIn, widthOfM] at hj ⊢; omega)
    have q32 : ldv .ld M' (sp - 48 + 32) = R 8 := by
      rw [hfr 32 (by omega)]; simp only [afProW]
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
        ldv_ld_miss _ _ (by omega), ldv_store_hit]
    have q16 : ldv .ld M' (sp - 48 + 16) = R 18 := by
      rw [hfr 16 (by omega)]; simp only [afProW]
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
        ldv_store_hit]
    have q8 : ldv .ld M' (sp - 48 + 8) = R 19 := by
      rw [hfr 8 (by omega)]; simp only [afProW]
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
    have q40 : ldv .ld M' (sp - 48 + 40) = R 1 := by
      rw [hfr 40 (by omega)]; simp only [afProW]
      rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    have q24 : ldv .ld M' (sp - 48 + 24) = R 9 := by
      rw [hfr 24 (by omega)]; simp only [afProW]; rw [ldv_store_hit]
    refine af_epi hlive hS hsf R' k2 q40 q32 q24 q16 q8 hal fun R'' hk2 e1 e2 e8' e9 e18 e19 => ?_
    refine hk R'' M' H' F' L' C' G' (Keeps.restoreAll (rs := [1, 2, 8, 9, 18, 19]) ?_ ?_) ?_ h' hkp hpin
    · exact (hk2.mono (by decide)).trans ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
      · exact e1
      · rw [e2, h2]
      · exact e8'
      · exact e9
      · exact e18
      · exact e19
    · exact ⟨hp.same, fun a ho hg hf => (hp.out a ho hg fun h' => hf (by
          simp only [frameIn] at h' ⊢; omega)).trans (hM1 a fun h' => hf (by
          simp only [frameIn] at h' ⊢; omega)),
        fun c hc hcm => ⟨(hp.fresh c hc hcm).1, fun a hca => ((hp.fresh c hc hcm).2 a hca).trans
          (hM1 a fun hf => (hfo a hf).1.1 (live_in_heap hi hc.live hca))⟩⟩

end Dc.Mach
