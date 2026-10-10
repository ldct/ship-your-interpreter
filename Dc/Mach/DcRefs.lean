import Dc.Mach.StateOps

/-!
# The reference-count bound (M9)

`n_refs` and `s_refs` are 32-bit `int`s. Every reference the dc state holds
sits in its own heap block, so the counts are bounded by the number of
pairwise-apart blocks the heap can hold, plus the caller's handles and the
constants:

- `apart_len`: a pairwise-apart list of blocks inside `[lo, hi)` has at most
  `(hi - lo) / 16` members.
- `DcAt.count_le`: no datum is referenced more than `7856803 + hs.length`
  times.
- `DcAt.numRefs_lt`/`DcAt.strRefs_lt`: one more reference still fits.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- **Apart blocks in `[lo, hi)`** number at most `(hi - lo) / 16`. -/
theorem apart_len : ∀ (n : Nat) (l : List Blk) (lo hi : Nat), l.length ≤ n →
    l.Pairwise Blk.Apart → (∀ b ∈ l, lo ≤ b.h ∧ b.fin ≤ hi) → l.length * 16 ≤ hi - lo
  | _, [], _, _, _, _, _ => by simp
  | 0, _ :: _, _, _, hn, _, _ => by simp at hn
  | n + 1, b :: t, lo, hi, hn, hp, hin => by
    rw [List.pairwise_cons] at hp
    obtain ⟨hb1, hb2⟩ := hin b List.mem_cons_self
    have hlt := List.length_eq_countP_add_countP (fun c => decide (c.fin ≤ b.h)) (l := t)
    rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at hlt
    have hf1 := List.length_filter_le (fun c => decide (c.fin ≤ b.h)) t
    have hf2 := List.length_filter_le (fun c => decide ¬ (decide (c.fin ≤ b.h) = true)) t
    simp only [List.length_cons] at hn
    have i1 := apart_len n (t.filter fun c => decide (c.fin ≤ b.h)) lo b.h (by omega)
      (hp.2.sublist List.filter_sublist) fun c hc => by
        rw [List.mem_filter] at hc
        have := hin c (List.mem_cons_of_mem _ hc.1)
        simp only [decide_eq_true_eq] at hc; omega
    have i2 := apart_len n (t.filter fun c => decide ¬ (decide (c.fin ≤ b.h) = true)) b.fin hi
      (by omega)
      (hp.2.sublist List.filter_sublist) fun c hc => by
        rw [List.mem_filter] at hc
        have := hin c (List.mem_cons_of_mem _ hc.1)
        have ha := hp.1 c hc.1
        simp only [decide_eq_true_eq] at hc
        unfold Blk.Apart at ha; omega
    simp only [List.length_cons]
    have : b.h + 16 ≤ b.fin := by simp only [Blk.fin]; omega
    omega

theorem flatMap_len_le {α β γ : Type} (f : α → List β) (g : α → List γ)
    (h : ∀ x, (f x).length ≤ (g x).length) :
    ∀ l : List α, (l.flatMap f).length ≤ (l.flatMap g).length
  | [] => by simp
  | x :: l => by
    simp only [List.flatMap_cons, List.length_append]
    have := flatMap_len_le f g h l; have := h x; omega

theorem RLev.vals_len (be : Blk × RLev) : (RLev.vals be).length ≤ (RLev.blocks be).length := by
  obtain ⟨b, ⟨v, arr⟩⟩ := be
  cases v <;> simp [RLev.vals, RLev.blocks]

theorem DcG.vals_len (G : DcG) : G.vals.length ≤ G.blocks.length := by
  unfold DcG.vals DcG.blocks
  simp only [List.length_append, List.length_map]
  have := flatMap_len_le (fun r => (G.regs r).flatMap RLev.vals)
    (fun r => (G.regs r).flatMap RLev.blocks)
    (fun r => flatMap_len_le _ _ RLev.vals_len _) (List.range 256)
  omega

/-- The ghost's blocks are pairwise apart and inside the heap: at most
`7856803` of them. -/
theorem DcAt.blocks_len {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) :
    G.blocks.length ≤ 7856803 := by
  have hi := h.heap.heap
  have hm : ∀ b ∈ G.blocks, b ∈ H.blocks := fun b hb =>
    List.mem_append_right _ (h.heap.raw.live b hb)
  have hp : G.blocks.Pairwise Blk.Apart :=
    h.nodup.imp_of_mem fun ha hb hne => apart_of_mem hi.apart (hm _ ha) (hm _ hb) hne
  have := apart_len _ G.blocks heapStart heapEnd (Nat.le_refl _) hp fun b hb => by
    have f := hi.blk (hm b hb)
    exact ⟨f.lo, Nat.le_trans f.fin f.top⟩
  simp only [heapStart, heapEnd] at this
  omega

/-- **No datum is referenced more than `7856803 + hs.length` times.** -/
theorem DcAt.count_le {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) (g : GV) :
    (G.vals ++ hs).count g ≤ 7856803 + hs.length := by
  have e1 := List.count_le_length (a := g) (l := G.vals ++ hs)
  rw [List.length_append] at e1
  have := G.vals_len; have := h.blocks_len
  omega

/-- One more reference to a number of the heap still fits `n_refs`. -/
theorem DcAt.numRefs_lt {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    (hhs : hs.length ≤ 2 ^ 30) {x : NumObj} (hx : x ∈ L) : x.rep.refs + 1 < 2 ^ 31 := by
  rw [h.den.numRefs x hx]
  have := h.count_le (.num x.rep.p)
  have : C.cnt x.rep.p ≤ 3 + 2 ^ 29 := by
    unfold BcConsts.cnt
    have := Nat.le_trans (List.count_le_length (a := x.rep.p) (l := C.lk)) h.den.lkLen
    have : [C.z, C.o, C.t].countP (·.rep.p = x.rep.p) ≤ 3 :=
      Nat.le_trans (List.countP_le_length) (by simp)
    omega
  omega

/-- One more reference to a string of the state still fits `s_refs`. -/
theorem DcAt.strRefs_lt {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    (hhs : hs.length ≤ 2 ^ 30) {o : StrObj} (ho : o ∈ G.strs) : o.refs + 1 < 2 ^ 31 := by
  rw [h.den.strRefs o ho]
  have := h.count_le (.str o.hb.pay)
  omega

end Dc.Mach
