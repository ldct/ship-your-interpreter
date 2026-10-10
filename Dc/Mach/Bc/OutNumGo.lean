import Dc.Mach.Bc.OutNumEntry
import Dc.Mach.Bc.HandleCall
import Dc.Mach.Bc.RawCells

/-! # `bc_out_num` in a base other than 10: the state

The branch at `0x800070b8` keeps its numbers as handles (`RList`) in frame
words `sp - 176 + o` (`int_part` 16, `frac_part` 24, `base` 32, `cur_dig`
40, `t_num` 48, `max_o_digit` 56), with `s0`–`s11` saved (`onSlots3`).

- `SlotWords`: each handle's pointer in its frame word.
- `OgSt`: the frame, the heap with the handles, the callback's invariant.
- `OgSt.ret`: the state after a callee (`hc_*H`) replaced one handle.
- `OnCtx.hcFrame`, `OnK.hcOom`: the handle-call frame and `out_of_memory`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open VsaIris.Interp (imgLE_inj imgLE_store4_hit)

/-- The handles `hs` at the frame words `b + o` for the offsets `os`. -/
def SlotWords (M : Mem) (b : Nat) : List RH → List Nat → Prop
  | [], [] => True
  | h :: hs, o :: os => ldv .ld M (b + o) = BitVec.ofNat 64 h.p ∧ SlotWords M b hs os
  | _, _ => False

theorem SlotWords.length {M : Mem} {b : Nat} :
    ∀ {hs : List RH} {os : List Nat}, SlotWords M b hs os → hs.length = os.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => congrArg (· + 1) (SlotWords.length h)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Through a memory agreeing on the words. -/
theorem SlotWords.transport {M M' : Mem} {b : Nat} :
    ∀ {hs : List RH} {os : List Nat}, SlotWords M b hs os →
      (∀ o ∈ os, ldv .ld M' (b + o) = ldv .ld M (b + o)) → SlotWords M' b hs os
  | [], [], h, _ => h
  | _ :: _, o :: _, ⟨h1, h2⟩, hm =>
      ⟨(hm o List.mem_cons_self).trans h1,
        SlotWords.transport h2 fun o' ho => hm o' (List.mem_cons_of_mem _ ho)⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem SlotWords.append {M : Mem} {b : Nat} :
    ∀ {hs : List RH} {os : List Nat} {hs' : List RH} {os' : List Nat}, SlotWords M b hs os →
      SlotWords M b hs' os' → SlotWords M b (hs ++ hs') (os ++ os')
  | [], [], _, _, _, h' => h'
  | _ :: _, _ :: _, _, _, ⟨h1, h2⟩, h' => ⟨h1, SlotWords.append h2 h'⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

/-- The word of the handle `h` between `hs1` and `hs2`. -/
theorem SlotWords.get {M : Mem} {b : Nat} {h : RH} {o : Nat} {hs2 : List RH} {os2 : List Nat} :
    ∀ {hs1 : List RH} {os1 : List Nat}, hs1.length = os1.length →
      SlotWords M b (hs1 ++ h :: hs2) (os1 ++ o :: os2) → ldv .ld M (b + o) = BitVec.ofNat 64 h.p
  | [], [], _, ⟨h1, _⟩ => h1
  | _ :: _, _ :: _, hl, ⟨_, h2⟩ => SlotWords.get (Nat.succ.inj hl) h2
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- The handle `h` replaced by `h'`, its word rewritten, the others kept. -/
theorem SlotWords.set {M M' : Mem} {b : Nat} {h h' : RH} {o : Nat} {hs2 : List RH}
    {os2 : List Nat} :
    ∀ {hs1 : List RH} {os1 : List Nat}, hs1.length = os1.length →
      SlotWords M b (hs1 ++ h :: hs2) (os1 ++ o :: os2) →
      (∀ o' ∈ os1 ++ os2, ldv .ld M' (b + o') = ldv .ld M (b + o')) →
      ldv .ld M' (b + o) = BitVec.ofNat 64 h'.p →
      SlotWords M' b (hs1 ++ h' :: hs2) (os1 ++ o :: os2)
  | [], [], _, ⟨_, h2⟩, hm, hw => ⟨hw, h2.transport fun o' ho => hm o' (by simpa using ho)⟩
  | _ :: _, o1 :: _, hl, ⟨h1, h2⟩, hm, hw =>
      ⟨(hm o1 List.mem_cons_self).trans h1,
        SlotWords.set (Nat.succ.inj hl) h2 (fun o' ho => hm o' (List.mem_cons_of_mem _ ho)) hw⟩
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl

/-- Inside the branch for a base other than 10: the frame with `s0`–`s11`
saved, the heap with the handles `hs` at the frame offsets `os` (distinct
words between 16 and 56), the callback's invariant with `sent` sent. -/
structure OgSt (S : Nat → Prop) (X : Raws) (G : Nat → Prop) (I : List Nat → String → Mem → Prop)
    (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat) (H : Heap) (F : List Blk) (L : List NumObj)
    (hs : List RH) (os : List Nat) (sent : List Nat) (t : String) : Prop where
  on : OnAt S G Mt0 M R0 R sp W onSlots3
  heap : BcHeap S X M H F (RList hs L)
  own : RHOwn hs L
  words : SlotWords M (sp - 176) hs os
  offs : ∀ o ∈ os, 16 ≤ o ∧ o ≤ 56 ∧ o % 8 = 0
  nd : os.Nodup
  inv : I sent t M

/-- The handle-call frame of `bc_out_num` for the word at `o`. -/
theorem OnCtx.hcFrame {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp W d : Nat}
    (cx : OnCtx S R0 sp W d) {o : Nat} (ho : o + 8 ≤ 176) (h8 : o % 8 = 0) :
    HcFrame S sp W 176 o := by
  on_facts cx
  exact ⟨cx.cc, by omega, by decide, ho, h8⟩

/-- `bc_out_num`'s `out_of_memory` continuation at the console `t`. -/
theorem OnK.hcOom {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {R0 : Nat → BitVec 64} {M0 : Mem}
    {L : List NumObj} {sp W : Nat} {target : List Nat}
    (hK : OnK live S X Q I G R0 M0 L sp W target) (t : String) :
    HcOom live S (DQ live S Q t) M0 sp W G :=
  fun R' M' sp' h1 h2 h3 h4 => hK.oom t R' M' sp' h1 h2 h3 h4

/-- **After a callee replaced the handle `h`** with a new number `y` in its
word at `o`, the callee changing besides the heap only its window below the
frame and that word. -/
theorem OgSt.ret {live S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    {sp W d : Nat} {H H' : Heap} {F F' : List Blk} {L : List NumObj}
    {hs1 hs2 : List RH} {h : RH} {os1 os2 : List Nat} {o : Nat} {y : NumObj}
    {sent : List Nat} {t : String}
    (st : OgSt S X G I Mt0 M R0 R sp W H F L (hs1 ++ h :: hs2) (os1 ++ o :: os2) sent t)
    (cx : OnCtx S R0 sp W d) (cb : CharFn live S Q (R0 12) d G I)
    (hl : hs1.length = os1.length) {ks : List Nat} (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ onAll ∧ z ≠ 2 ∧ z ≠ 9)
    (hb : BcHeap S X M' H' F' (RList (hs1 ++ .own y :: hs2) L))
    (hown : RHOwn (hs1 ++ .own y :: hs2) L)
    (hw : ldv .ld M' (sp - 176 + o) = BitVec.ofNat 64 y.rep.p)
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - 176 + o) a → ¬ frameIn (sp - 176) (W - 176) a →
      imgM M' a = imgM M a) :
    OgSt S X G I Mt0 M' R0 R' sp W H' F' L (hs1 ++ .own y :: hs2) (os1 ++ o :: os2) sent t := by
  on_facts cx
  have ho := st.offs o (by simp)
  have hsf := cx.cc.frame
  have hsl := hsf.lo
  have hfr : ∀ a, sp - 176 + o + 8 ≤ a → a < sp → imgM M' a = imgM M a := fun a h1 h2 =>
    hout a (outHeap_of_ge (by simp only [heapEnd]; omega)) (by simp only [slotBytes]; omega)
      (by simp only [frameIn]; omega)
  have hlo : ∀ a, sp - 176 ≤ a → a < sp - 176 + o → imgM M' a = imgM M a := fun a h1 h2 =>
    hout a (outHeap_of_ge (by simp only [heapEnd]; omega)) (by simp only [slotBytes]; omega)
      (by simp only [frameIn]; omega)
  have hon := st.on.regs hk hks
  refine
    { on :=
        { r2 := hon.r2
          keep := hon.keep
          cb := hon.cb
          saved := hon.saved.transport (lo := 72) (top := 176) (by decide) (by decide)
            fun a h1 h2 => hfr a (by omega) (by omega)
          out := fun a ha hg hf => by
            rw [hout a ha (fun hs => hf (by simp only [slotBytes, frameIn] at hs ⊢; omega))
              (fun hs => hf (by simp only [frameIn] at hs ⊢; omega))]
            exact hon.out a ha hg hf }
      heap := hb
      own := hown
      words := st.words.set hl (fun o' ho' => by
          have hno : o' ≠ o := fun e => by
            subst e
            have := st.nd
            rw [List.nodup_append] at this
            rcases List.mem_append.mp ho' with h1 | h1
            · exact this.2.2 _ h1 _ List.mem_cons_self rfl
            · exact (List.nodup_cons.mp this.2.1).1 h1
          have ho'' := st.offs o' (by
            rcases List.mem_append.mp ho' with h1 | h1
            · exact List.mem_append_left _ h1
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
          exact ldv_congr .ld fun j hj => by
            simp only [widthOfM] at hj
            rcases Nat.lt_or_ge o' o with hlt | hge
            · exact hlo _ (by omega) (by omega)
            · exact hfr _ (by omega) (by omega)) hw
      offs := st.offs
      nd := st.nd
      inv := cb.stab _ _ _ _ st.inv fun a hg => by
        have := (cb.off a hg).1
        simp only [heapStart] at this
        exact hout a (cb.off a hg).2.1 (by simp only [slotBytes]; omega)
          (by simp only [frameIn]; omega) }

/-- Two 4-byte stores at one address: the second's bytes. -/
theorem imgM_store4_over (M : Mem) (b : Nat) (v1 v2 : BitVec 64) (a : Nat) :
    imgM (writeLog (writeLog M [(b, 4, v1)]) [(b, 4, v2)]) a = imgM (writeLog M [(b, 4, v2)]) a := by
  by_cases ha : b ≤ a ∧ a < b + 4
  · have e := imgLE_inj ((imgLE_store4_hit (writeLog M [(b, 4, v1)]) b v2).trans (imgLE_store4_hit M b v2).symm) (a - b)
      (by omega)
    rwa [show b + (a - b) = a by omega] at e
  · rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]

/-- **Three more references** to the caller's `y` in one store of its count. -/
theorem RList.bump3 {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk}
    {hs : List RH} {L : List NumObj} {y : NumObj} (hb : BcHeap S X M H F (RList hs L)) (hy : y ∈ L)
    {v : BitVec 64} (hv : v.toNat % 2 ^ 32 = y.rep.refs + rCnt hs y.rep.p + 3)
    (hr : y.rep.refs + rCnt hs y.rep.p + 3 < 2 ^ 31) :
    BcHeap S X (writeLog M [(y.rep.p + 12, 4, v)]) H F
      (RList (hs ++ [.ref y, .ref y, .ref y]) L) := by
  have c1 : rCnt (hs ++ [.ref y]) y.rep.p = rCnt hs y.rep.p + 1 := by
    rw [rCnt_append]; simp [rCnt, RH.cnt]
  have c2 : rCnt (hs ++ [.ref y] ++ [.ref y]) y.rep.p = rCnt hs y.rep.p + 2 := by
    rw [rCnt_append, c1]; simp [rCnt, RH.cnt]
  have h1 := RList.bump hb hy (v := BitVec.ofNat 64 (y.rep.refs + rCnt hs y.rep.p + 1))
    (toNat_ofNat_mod32 (by omega)) (by omega)
  have h2 := RList.bump h1 hy (v := BitVec.ofNat 64 (y.rep.refs + rCnt hs y.rep.p + 2))
    (by rw [c1]; exact toNat_ofNat_mod32 (by omega)) (by omega)
  have h3 := RList.bump h2 hy (v := v) (by rw [c2]; omega) (by rw [c2]; omega)
  rw [show hs ++ [RH.ref y] ++ [RH.ref y] ++ [RH.ref y] = hs ++ [.ref y, .ref y, .ref y] by simp] at h3
  exact h3.congr fun a =>
    ((imgM_store4_over _ _ _ _ a).trans (imgM_store4_over _ _ _ _ a)).symm

/-- Through a store into the frame below the saved registers. -/
theorem OnAt.word {S G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {slots : List (Nat × Nat)} (h : OnAt S G Mt0 M R0 R sp W slots)
    (hs : ∀ p ∈ slots, 72 ≤ p.2 := by decide) (htop : ∀ p ∈ slots, p.2 + 8 ≤ 176 := by decide)
    {o : Nat} (ho : o + 8 ≤ 72) (hsp : 176 ≤ sp) (hW : 176 ≤ W) (v : BitVec 64) :
    OnAt S G Mt0 (writeLog M [(sp - 176 + o, 8, v)]) R0 R sp W slots :=
  { h with
    saved := h.saved.transport (lo := 72) (top := 176) hs htop fun a h1 _ =>
      imgM_store_miss _ _ (by omega)
    out := fun a ha hg hf => by
      rw [imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]; exact h.out a ha hg hf }

/-- Through a store into the heap. -/
theorem OnAt.heapStore {S G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {slots : List (Nat × Nat)} (h : OnAt S G Mt0 M R0 R sp W slots)
    (hs : ∀ p ∈ slots, 72 ≤ p.2 := by decide) (htop : ∀ p ∈ slots, p.2 + 8 ≤ 176 := by decide)
    (hab : heapEnd + W ≤ sp) (hW : 176 ≤ W) {a0 w : Nat} (hlo : heapStart ≤ a0)
    (hhi : a0 + w ≤ heapEnd) (v : BitVec 64) :
    OnAt S G Mt0 (writeLog M [(a0, w, v)]) R0 R sp W slots :=
  { h with
    saved := h.saved.transport (lo := 72) (top := 176) hs htop fun a h1 _ =>
      imgM_store_miss _ _ (by simp only [heapEnd] at hab hhi; omega)
    out := fun a ha hg hf => by
      rw [imgM_store_miss _ _ (by simp only [OutHeap, heapStart, heapEnd] at ha hlo hhi; omega)]
      exact h.out a ha hg hf }

/-- A store into the heap keeps the callback's invariant. -/
theorem CharFn.heapStore {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {f : BitVec 64} {d : Nat} {G : Nat → Prop} {I : List Nat → String → Mem → Prop}
    (h : CharFn live S Q f d G I) {cs : List Nat} {t : String} {M : Mem} (hI : I cs t M)
    {a0 w : Nat} (v : BitVec 64) (hlo : heapStart ≤ a0) : I cs t (writeLog M [(a0, w, v)]) :=
  h.stab cs t M _ hI fun a hg => imgM_store_miss _ _ (.inl (by
    have := (h.off a hg).1; omega))

/-- `OgSt` without the frame words: the state between the stores that set
up handles. -/
structure OgPre (S : Nat → Prop) (X : Raws) (G : Nat → Prop) (I : List Nat → String → Mem → Prop)
    (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat) (H : Heap) (F : List Blk) (L : List NumObj)
    (hs : List RH) (sent : List Nat) (t : String) : Prop where
  on : OnAt S G Mt0 M R0 R sp W onSlots3
  heap : BcHeap S X M H F (RList hs L)
  own : RHOwn hs L
  inv : I sent t M

theorem OgSt.pre {S : Nat → Prop} {X : Raws} {G : Nat → Prop} {I : List Nat → String → Mem → Prop}
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {hs : List RH} {os : List Nat} {sent : List Nat} {t : String}
    (st : OgSt S X G I Mt0 M R0 R sp W H F L hs os sent t) :
    OgPre S X G I Mt0 M R0 R sp W H F L hs sent t :=
  ⟨st.on, st.heap, st.own, st.inv⟩

/-- Through a store into the frame below the saved registers. -/
theorem OgPre.frame {live S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W d : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {hs : List RH} {sent : List Nat} {t : String}
    (p : OgPre S X G I Mt0 M R0 R sp W H F L hs sent t) (cx : OnCtx S R0 sp W d)
    (cb : CharFn live S Q (R0 12) d G I) {o : Nat} (ho : o + 8 ≤ 72) (v : BitVec 64) :
    OgPre S X G I Mt0 (writeLog M [(sp - 176 + o, 8, v)]) R0 R sp W H F L hs sent t := by
  on_facts cx
  exact ⟨p.on.word (by decide) (by decide) ho (by omega) (by omega) v,
    p.heap.frameStore (o := o) v (by simp only [heapEnd]; omega) (by omega), p.own,
    cb.frameStore p.inv v (by simp only [heapEnd]; omega)⟩

/-- Through one more reference to the caller's `y`, its count stored. -/
theorem OgPre.bump {live S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W d : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {hs : List RH} {sent : List Nat} {t : String}
    (p : OgPre S X G I Mt0 M R0 R sp W H F L hs sent t) (cx : OnCtx S R0 sp W d)
    (cb : CharFn live S Q (R0 12) d G I) {y : NumObj} (hy : y ∈ L) (hyo : y.Owns) {v : BitVec 64}
    (hv : v.toNat % 2 ^ 32 = y.rep.refs + rCnt hs y.rep.p + 1)
    (hr : y.rep.refs + rCnt hs y.rep.p + 1 < 2 ^ 31) :
    OgPre S X G I Mt0 (writeLog M [(y.rep.p + 12, 4, v)]) R0 R sp W H F L (hs ++ [.ref y]) sent t := by
  on_facts cx
  have hn := (p.heap.nums _ (RList.mem_caller hs hy)).shape
  have h1 : heapStart ≤ y.rep.p := hn.pLo
  have h2 : y.rep.p + 40 ≤ heapEnd := hn.pHi
  simp only [heapStart, heapEnd] at h1 h2
  exact ⟨p.on.heapStore (by decide) (by decide) (by simp only [heapEnd]; omega) (by omega)
      (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega) v,
    RList.bump p.heap hy hv hr,
    ⟨fun w hw => p.own.temps w (by simpa using hw), p.own.caller⟩,
    cb.heapStore p.inv v (by simp only [heapStart]; omega)⟩

/-- Through three more references to the caller's `y` in one store. -/
theorem OgPre.bump3 {live S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W d : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {hs : List RH} {sent : List Nat} {t : String}
    (p : OgPre S X G I Mt0 M R0 R sp W H F L hs sent t) (cx : OnCtx S R0 sp W d)
    (cb : CharFn live S Q (R0 12) d G I) {y : NumObj} (hy : y ∈ L) {v : BitVec 64}
    (hv : v.toNat % 2 ^ 32 = y.rep.refs + rCnt hs y.rep.p + 3)
    (hr : y.rep.refs + rCnt hs y.rep.p + 3 < 2 ^ 31) :
    OgPre S X G I Mt0 (writeLog M [(y.rep.p + 12, 4, v)]) R0 R sp W H F L
      (hs ++ [.ref y, .ref y, .ref y]) sent t := by
  on_facts cx
  have hn := (p.heap.nums _ (RList.mem_caller hs hy)).shape
  have h1 : heapStart ≤ y.rep.p := hn.pLo
  have h2 : y.rep.p + 40 ≤ heapEnd := hn.pHi
  simp only [heapStart, heapEnd] at h1 h2
  exact ⟨p.on.heapStore (by decide) (by decide) (by simp only [heapEnd]; omega) (by omega)
      (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega) v,
    RList.bump3 p.heap hy hv hr,
    ⟨fun w hw => p.own.temps w (by simpa using hw), p.own.caller⟩,
    cb.heapStore p.inv v (by simp only [heapStart]; omega)⟩

/-- `OgSt` again, given the words. -/
theorem OgPre.close {S : Nat → Prop} {X : Raws} {G : Nat → Prop} {I : List Nat → String → Mem → Prop}
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {hs : List RH} {sent : List Nat} {t : String}
    (p : OgPre S X G I Mt0 M R0 R sp W H F L hs sent t) {os : List Nat}
    (hw : SlotWords M (sp - 176) hs os) (ho : ∀ o ∈ os, 16 ≤ o ∧ o ≤ 56 ∧ o % 8 = 0 := by decide)
    (hn : os.Nodup := by decide) : OgSt S X G I Mt0 M R0 R sp W H F L hs os sent t :=
  ⟨p.on, p.heap, p.own, hw, ho, hn, p.inv⟩

/-- The registers `OgSt` lets change: all but `sp` and `s1` (the callback). -/
abbrev ogKs : List Nat :=
  [1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
    31]

/-- The handle's word when the handle's pointer does not change. -/
theorem SlotWords.congr {M M' : Mem} {b : Nat} {h h' : RH} {o : Nat} {hs1 hs2 : List RH}
    {os1 os2 : List Nat} (hl : hs1.length = os1.length)
    (hw : SlotWords M b (hs1 ++ h :: hs2) (os1 ++ o :: os2)) (hp : h'.p = h.p)
    (hm : ∀ o' ∈ os1 ++ o :: os2, ldv .ld M' (b + o') = ldv .ld M (b + o')) :
    SlotWords M' b (hs1 ++ h' :: hs2) (os1 ++ o :: os2) :=
  hw.set hl (fun o' ho => hm o' (by
    rcases List.mem_append.mp ho with h1 | h1
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)))
    (by rw [hm o (by simp), hw.get hl, hp])

/-- **The sign word of an owned handle's number rewritten.** -/
theorem OgSt.setSign {live S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W d : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {hs1 hs2 : List RH} {y : NumObj}
    {os : List Nat} {sent : List Nat} {t : String}
    (st : OgSt S X G I Mt0 M R0 R sp W H F L (hs1 ++ .own y :: hs2) os sent t)
    (cx : OnCtx S R0 sp W d) (cb : CharFn live S Q (R0 12) d G I) {v : BitVec 64} (b : Bool)
    (hv : v.toNat % 2 ^ 32 = b.toNat) :
    OgSt S X G I Mt0 (writeLog M [(y.rep.p, 4, v)]) R0 R sp W H F L
      (hs1 ++ .own { y with rep := { y.rep with neg := b } } :: hs2) os sent t := by
  on_facts cx
  have hb := st.heap
  have hym : y ∈ RList (hs1 ++ .own y :: hs2) L := by rw [RList.own_split]; simp
  have hn := (hb.nums y hym).shape
  have h1 : heapStart ≤ y.rep.p := hn.pLo
  have h2 : y.rep.p + 40 ≤ heapEnd := hn.pHi
  simp only [heapStart, heapEnd] at h1 h2
  rw [RList.own_split] at hb
  have hb' := hb.setSign b hv
  rw [← RList.own_split] at hb'
  have hsl := st.words.length
  obtain ⟨os1, o, os2, rfl, hl⟩ : ∃ os1 o os2, os = os1 ++ o :: os2 ∧ hs1.length = os1.length := by
    refine ⟨os.take hs1.length, os[hs1.length]'(by simp at hsl; omega), os.drop (hs1.length + 1),
      ?_, by simp at hsl ⊢; omega⟩
    simp
  exact
    { on := st.on.heapStore (by decide) (by decide) (by simp only [heapEnd]; omega) (by omega)
        (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega) v
      heap := hb'
      own := st.own.set (y := { y with rep := { y.rep with neg := b } }) (st.own.temps y (by simp))
      words := st.words.congr hl rfl fun o' ho' => by
        have := st.offs o' ho'
        exact ldv_ld_miss _ _ (by omega)
      offs := st.offs
      nd := st.nd
      inv := cb.heapStore st.inv v (by simp only [heapStart]; omega) }

end Dc.Mach
