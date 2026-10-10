import Dc.Mach.DcDump

/-!
# A dc function's frame and bc calls on its slots

A dc function that holds bc numbers in its own stack slots (`dc_getnum`)
calls the bc library with a slot as the result. `CFr` is the frame: `sp`
lowered by `fs`, the registers `sv` saved at their offsets, and off the heap
and the globals only the frame and the callees' window `cfW` below it
changed. Each `cf_*` lemma is one bc call from such a frame on the handle the
slot at offset `o` holds:

- `cf_init` (`bc_init_num`), `cf_free` (`bc_free_num`),
- `cf_i2n` (`bc_int2num`),
- `cf_mul` (`bc_multiply`), `cf_add` (`bc_add`), `cf_sub` (`bc_sub`),
  whose results replace the slot's handle (`cf_ret`).

Each continuation receives the frame again (`CFr`) and `CfOut`: off the heap
and the globals only the window and the slot changed, so the other slots keep
their words (`CfOut.word`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The callees' window below a dc function's frame: `bc_divide`'s, the
largest. -/
abbrev cfW : Nat := 176 + rmStack (2 ^ 30)

/-- **Inside a dc function's frame**: `sp` lowered by `fs`, each register
`r` of `sv` saved at `sp - fs + o` (`(o, r) ∈ sv`), off the heap and the
globals only the frame and the window below it changed. -/
structure CFr (fs : Nat) (sv : List (Nat × Nat)) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp : Nat) :
    Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - fs)
  saved : ∀ p ∈ sv, ldv .ld M (sp - fs + p.1) = R0 p.2
  keep : Keeps (2 :: sv.map Prod.snd ++ cClob) R R0
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp (fs + cfW) a → imgM M a = imgM M0 a

/-- **A callee's frame**: off the heap and the globals only the window below
the frame and the slot at `o` changed. -/
def CfOut (M M' : Mem) (sp fs o : Nat) : Prop :=
  ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn (sp - fs) cfW a → ¬ slotBytes (sp - fs + o) a →
    imgM M' a = imgM M a

/-- Another slot's word through a callee. -/
theorem CfOut.word {M M' : Mem} {sp fs o : Nat} (h : CfOut M M' sp fs o) (hab : heapEnd ≤ sp - fs)
    {o' : Nat} (hd : o' + 8 ≤ o ∨ o + 8 ≤ o') :
    ldv .ld M' (sp - fs + o') = ldv .ld M (sp - fs + o') :=
  ldv_congr .ld fun j hj => h _ (above_sp hab (by omega)).1 (above_sp hab (by omega)).2.1
    (fun hf => by simp only [frameIn] at hf; omega)
    (fun hs => by simp only [slotBytes, widthOfM] at hs hj; omega)

/-- The frame with registers a callee kept. -/
theorem CFr.regs {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp : Nat}
    (hfr : CFr fs sv M0 M R0 R sp) (k : Keeps cClob R' R) : CFr fs sv M0 M R0 R' sp where
  r2 := by rw [k.get 2 (by decide)]; exact hfr.r2
  saved := hfr.saved
  keep := (k.mono fun z hz => List.mem_cons_of_mem _ (List.mem_append_right _ hz)).trans hfr.keep
  out := hfr.out

/-- **The frame through a callee** that changed only the window and the slot
at `o`, below the saved words. -/
theorem CFr.next {fs : Nat} {sv : List (Nat × Nat)} {M0 M M' : Mem} {R0 R R' : Nat → BitVec 64}
    {sp o : Nat} (hfr : CFr fs sv M0 M R0 R sp) (hab : heapEnd ≤ sp - fs) (hfs : fs ≤ sp)
    (hsv : ∀ p ∈ sv, o + 8 ≤ p.1) (hof : o + 8 ≤ fs) (hM : CfOut M M' sp fs o)
    (k : Keeps cClob R' R) : CFr fs sv M0 M' R0 R' sp :=
  { hfr.regs k with
    saved := fun p hp => ((hM.word hab (.inr (hsv p hp))).trans (hfr.saved p hp))
    out := fun a ho hg hf =>
      (hM a ho hg (fun h => hf (by simp only [frameIn] at h ⊢; omega))
        (fun h => hf (by simp only [slotBytes, frameIn] at h ⊢; omega))).trans (hfr.out a ho hg hf) }

/-- `_bc_rec_mul`'s base word, off every byte the frame changes. -/
theorem CFr.mulBase {S : Nat → Prop} {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem}
    {R0 R : Nat → BitVec 64} {sp : Nat} (hfr : CFr fs sv M0 M R0 R sp)
    (hab : heapEnd + (fs + cfW) ≤ sp) (hmb : MulBase S M0) : MulBase S M :=
  hmb.transport fun a e1 e2 => hfr.out a
    (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, mulBaseAddr] at e1 e2 ⊢; omega)
    (by simp only [DcGlob, dc_addrs, mulBaseAddr] at e1 e2 ⊢; omega)
    (by simp only [frameIn, heapEnd, mulBaseAddr] at e1 e2 hab ⊢; omega)

/-- The frame's place: the stack frame of `fs` bytes and the window, above
the heap; `fs` a multiple of `16`. -/
structure CfCtx (S : Nat → Prop) (fs sp : Nat) : Prop where
  sf : StackFrame S sp (fs + cfW)
  ab : heapEnd + (fs + cfW) ≤ sp
  al : fs % 16 = 0

theorem CfCtx.sub {S : Nat → Prop} {fs sp : Nat} (cx : CfCtx S fs sp) : StackFrame S (sp - fs) cfW :=
  StackFrame.sub cx.sf cx.al

theorem CfCtx.slot {S : Nat → Prop} {fs sp o : Nat} (cx : CfCtx S fs sp) (ho : o + 8 ≤ fs)
    (h8 : o % 8 = 0) : PtrSlot S (sp - fs + o) := by
  have := cx.sf.al; have := cx.ab; have := cx.al
  exact cx.sf.slot (by omega) (by omega) (by omega)

theorem CfCtx.abv {S : Nat → Prop} {fs sp : Nat} (cx : CfCtx S fs sp) : heapEnd ≤ sp - fs := by
  have := cx.ab; omega

/-- `out_of_memory` from a callee: the frame's `OomAt`. -/
theorem CFr.oom {S : Nat → Prop} {fs : Nat} {sv : List (Nat × Nat)} {M0 M M' : Mem}
    {R0 R R' : Nat → BitVec 64} {sp sp' o W : Nat} (hfr : CFr fs sv M0 M R0 R sp)
    (cx : CfCtx S fs sp) (hW : W ≤ cfW) (ho : o + 8 ≤ fs) (h1 : sp - fs - W ≤ sp') (h2 : sp' ≤ sp - fs)
    (r2 : R' 2 = BitVec.ofNat 64 sp')
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - fs + o) a → ¬ frameIn (sp - fs) W a →
      imgM M' a = imgM M a) :
    OomAt S sp (fs + cfW) M0 (fun _ => False) sp' R' M' := by
  have := cx.ab
  refine ⟨by omega, by omega, r2, fun a ho' hg hf _ => ?_⟩
  rw [hout a ho' (fun h => hf (by simp only [slotBytes, frameIn] at h ⊢; omega))
    (fun h => hf (by simp only [frameIn] at h ⊢; omega))]
  exact hfr.out a ho' hg hf

/-- The window's first `n` bytes as a callee's frame. -/
theorem CfCtx.win {S : Nat → Prop} {fs sp : Nat} (cx : CfCtx S fs sp) {n : Nat} (hn : n ≤ cfW) :
    StackFrame S (sp - fs) n :=
  have sf := cx.sub
  ⟨fun a h1 h2 => sf.own a (by omega) h2, by have := sf.lo; omega, sf.hi, sf.al⟩

/-- **`bc_free_num` of the handle in the slot at `o`**. -/
theorem cf_free {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {p sp o : Nat} {R0 R : Nat → BitVec 64}
    (cx : CfCtx S fs sp) (hfr : CFr fs sv M0 M R0 R sp) (h : DcAt S M H F L C G (.num p :: hs) st)
    (hsv : ∀ q ∈ sv, o + 8 ≤ q.1) (ho : o + 8 ≤ fs) (h8 : o % 8 = 0)
    (hw : ldv .ld M (sp - fs + o) = BitVec.ofNat 64 p)
    (h10 : R 10 = BitVec.ofNat 64 (sp - fs + o)) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps cClob R' R → CFr fs sv M0 M' R0 R' sp →
      DcAt S M' H' F' L' C' G hs st → CfOut M M' sp fs o → HsKeep ⟨L, G.strs⟩ ⟨L', G.strs⟩ hs →
      DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x800048c0#64 R M := by
  have hab := cx.abv
  have hab' := cx.ab
  have hW : cfW = 176 + rmStack (2 ^ 30) := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hsl := cx.sf.lo
  simp only [heapEnd] at hab hab'
  refine bc_free_num_dcK hlive h (cx.slot ho h8) (by simp only [heapEnd]; omega) hw
    (cx.win (n := 32) (by omega)) (by simp only [heapEnd]; omega) (.inr (by omega)) R h10 hfr.r2 hal fun R' M' H' F' L' C' hk' hd hout hkp => ?_
  have hO : CfOut M M' sp fs o := fun a ho' hg hf hs' =>
    hout a ho' hg (fun h => hf (by simp only [frameIn] at h ⊢; omega)) hs'
  have k : Keeps cClob R' R := hk'.mono (by decide)
  exact hk R' M' H' F' L' C' k (hfr.next cx.abv (by omega) hsv ho hO k) hd hO hkp

/-- **`bc_init_num` of the slot at `o`**: the slot holds a new `_zero_`
handle. -/
theorem cf_init {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {sp o : Nat} {R0 R : Nat → BitVec 64}
    (cx : CfCtx S fs sp) (hfr : CFr fs sv M0 M R0 R sp) (h : DcAt S M H F L C G hs st)
    (hhs : hs.length ≤ 2 ^ 30) (hsv : ∀ q ∈ sv, o + 8 ≤ q.1) (ho : o + 8 ≤ fs) (h8 : o % 8 = 0)
    (h10 : R 10 = BitVec.ofNat 64 (sp - fs + o)) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' L' C', Keeps cClob R' R → CFr fs sv M0 M' R0 R' sp →
      DcAt S M' H F L' C' G (.num C.z.rep.p :: hs) st → C'.z.rep.p = C.z.rep.p →
      ldv .ld M' (sp - fs + o) = BitVec.ofNat 64 C.z.rep.p → CfOut M M' sp fs o →
      HsKeep ⟨L, G.strs⟩ ⟨L', G.strs⟩ hs → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x800049bc#64 R M := by
  have hab := cx.abv
  have hab' := cx.ab
  have hW : cfW = 176 + rmStack (2 ^ 30) := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hsl := cx.sf.lo
  simp only [heapEnd] at hab hab'
  refine dn_init hlive h hhs (cx.slot ho h8) (by simp only [heapEnd]; omega) R h10 hal
    fun R' M' L' C' hk' hd hz hkp hw hout => ?_
  have hO : CfOut M M' sp fs o := fun a ho' _ _ hs' => hout a ho' hs'
  have k : Keeps cClob R' R := hk'.mono (by decide)
  exact hk R' M' L' C' k (hfr.next cx.abv (by omega) hsv ho hO k) hd hz hw hO hkp

/-- **`bc_int2num` of `v` into the slot at `o`**: the slot's handle replaced
by a fresh number for `v`, or `out_of_memory`. -/
theorem cf_i2n {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {p sp o : Nat} {v : Int} {R0 R : Nat → BitVec 64}
    (cx : CfCtx S fs sp) (hfr : CFr fs sv M0 M R0 R sp) (h : DcAt S M H F L C G (.num p :: hs) st)
    (hsv : ∀ q ∈ sv, o + 8 ≤ q.1) (ho : o + 8 ≤ fs) (h8 : o % 8 = 0)
    (hw : ldv .ld M (sp - fs + o) = BitVec.ofNat 64 p)
    (h10 : R 10 = BitVec.ofNat 64 (sp - fs + o)) (h11 : R 11 = BitVec.ofInt 64 v)
    (hal : (R 1).toNat % 4 = 0) (hvlo : -2 ^ 31 < v) (hvhi : v < 2 ^ 31)
    (hk : ∀ R' M' H' F' L' C' y, Keeps cClob R' R → CFr fs sv M0 M' R0 R' sp →
      DcAt S M' H' F' (y :: L') C' G (.num y.rep.p :: hs) st → y.rep.num = Num.ofInt v →
      ldv .ld M' (sp - fs + o) = BitVec.ofNat 64 y.rep.p → CfOut M M' sp fs o →
      HsKeep ⟨L, G.strs⟩ ⟨y :: L', G.strs⟩ hs → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp (fs + cfW) M0 (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x8000690c#64 R M := by
  have hab := cx.abv
  have hab' := cx.ab
  have hW : cfW = 176 + rmStack (2 ^ 30) := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hsl := cx.sf.lo
  simp only [heapEnd] at hab hab'
  refine dc_int2num_spec hlive h (cx.slot ho h8) (by simp only [heapEnd]; omega) hw
    (cx.win (n := 128) (by omega)) (by simp only [heapEnd]; omega) (.inr (by omega)) R h10 h11 hfr.r2 hal hvlo hvhi
    (fun R' M' H' F' L' C' y hk' hd hnum hw' hout hkp => ?_) (fun R' M' r2 hout => ?_)
  · have hO : CfOut M M' sp fs o := fun a ho' _ hf hs' =>
      hout a ho' hs' fun h => hf (by simp only [frameIn] at h ⊢; omega)
    have k : Keeps cClob R' R := hk'.mono (by decide)
    exact hk R' M' H' F' L' C' y k (hfr.next cx.abv (by omega) hsv ho hO k) hd hnum hw' hO hkp
  · have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
    bc_run hlive hS [] at 0x80001e74
    exact hoom R' M' _ (hfr.oom cx (W := 128) (sp' := sp - fs - 128) (by unfold cfW rmStack; omega) ho (by omega) (by omega) r2
      fun a ho' hs' hf => hout a ho' hs' hf)

/-- **A callee's result into the slot at `o`**: the state holds the new
number's handle instead of the slot's old one, the frame is kept. -/
theorem cf_ret {S : Nat → Prop} {P : Prop} {fs : Nat} {sv : List (Nat × Nat)} {M0 M Mt : Mem}
    {H H' : Heap} {F F' : List Blk} {L1 L2 L' : List NumObj} {x y : NumObj} {C : BcConsts} {G : DcG}
    {hs : List GV} {st : St} {sp o W : Nat} {n : Num} {R0 R R' : Nat → BitVec 64}
    (cx : CfCtx S fs sp) (hfr : CFr fs sv M0 M R0 R sp)
    (h : DcAt S M H F (L1 ++ x :: L2) C G (.num x.rep.p :: hs) st)
    (hp : BinPostW S (G.raws M) M Mt H' F' L1 L2 x (sp - fs + o) (sp - fs) W n L' y)
    (hW : W ≤ cfW) (hsv : ∀ q ∈ sv, o + 8 ≤ q.1) (ho : o + 8 ≤ fs) (k : Keeps cClob R' R)
    (hk : ∀ C', CFr fs sv M0 Mt R0 R' sp → DcAt S Mt H' F' (y :: L') C' G (.num y.rep.p :: hs) st →
      ldv .ld Mt (sp - fs + o) = BitVec.ofNat 64 y.rep.p → CfOut M Mt sp fs o →
      HsKeep ⟨L1 ++ x :: L2, G.strs⟩ ⟨y :: L', G.strs⟩ hs → P) : P := by
  have hab := cx.abv
  have hab' := cx.ab
  simp only [heapEnd] at hab hab'
  obtain ⟨C', hd, hkp⟩ := h.newNum hp.rest hp.heap hp.refs hp.norm hp.pos hp.owns fun a ha =>
    hp.out a ha.outHeap (fun hs' => by have := ha.lt; simp only [heapStart, slotBytes] at this hs'; omega)
      (fun hf => by have := ha.lt; simp only [heapStart, frameIn] at this hf; omega)
  have hO : CfOut M Mt sp fs o := fun a ho' _ hf hs' =>
    hp.out a ho' hs' fun h => hf (by simp only [frameIn] at h ⊢; omega)
  exact hk C' (hfr.next cx.abv (by omega) hsv ho hO k) hd
    (by rw [hp.slot, (hp.heap.blocks y List.mem_cons_self).sPay]) hO hkp

/-- **`bc_multiply (a, b, &slot, k)`** with the slot at `o` holding a handle
of the state: its handle replaced by the product's, or `out_of_memory`. -/
theorem cf_mul {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {p p1 p2 sp o k : Nat} {n1 n2 : Num} {R0 R : Nat → BitVec 64}
    (cx : CfCtx S fs sp) (hfr : CFr fs sv M0 M R0 R sp) (h : DcAt S M H F L C G (.num p :: hs) st)
    (hmb : MulBase S M) (hhs : hs.length + 1 ≤ 2 ^ 20)
    (hsv : ∀ q ∈ sv, o + 8 ≤ q.1) (ho : o + 8 ≤ fs) (h8 : o % 8 = 0)
    (hw : ldv .ld M (sp - fs + o) = BitVec.ofNat 64 p)
    (hd1 : (GV.num p1).Den ⟨L, G.strs⟩ (.num n1)) (hd2 : (GV.num p2).Den ⟨L, G.strs⟩ (.num n2))
    (hkk : k < 2 ^ 31)
    (h10 : R 10 = BitVec.ofNat 64 p1) (h11 : R 11 = BitVec.ofNat 64 p2)
    (h12 : R 12 = BitVec.ofNat 64 (sp - fs + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' y, Keeps cClob R' R → CFr fs sv M0 M' R0 R' sp →
      DcAt S M' H' F' (y :: L') C' G (.num y.rep.p :: hs) st → y.rep.num = Num.mul n1 n2 k →
      ldv .ld M' (sp - fs + o) = BitVec.ofNat 64 y.rep.p → CfOut M M' sp fs o →
      HsKeep ⟨L, G.strs⟩ ⟨y :: L', G.strs⟩ hs → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp (fs + cfW) M0 (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x8000573c#64 R M := by
  have hab := cx.abv
  have hab' := cx.ab
  have hW : cfW = 176 + rmStack (2 ^ 30) := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hsl := cx.sf.lo
  simp only [heapEnd] at hab hab'
  obtain ⟨L1, L2, x, rfl, rfl⟩ := h.handle_num
  obtain ⟨x1, hx1, e1p, e1n⟩ := hd1.numObj
  obtain ⟨x2, hx2, e2p, e2n⟩ := hd2.numObj
  subst e1p e2p e1n e2n
  have hma := h.mulArgs hx1 hx2 (by simp only [List.length_cons]; omega) hkk hmb.word
  have hsz := hma.size
  refine bc_multiply_spec hlive (W := 96 + rmStack (2 ^ 30))
    ⟨cx.win (by omega), by simp only [heapEnd]; omega, by omega, cx.slot ho h8,
      fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega), .inr (by omega),
      hmb.own, fun a ha => h.glob a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega),
      hfr.r2, hal⟩
    hma (by
      have := rmDepth_mono (show x1.rep.len + x1.rep.scale + (x2.rep.len + x2.rep.scale) ≤ 2 ^ 30 by omega)
      unfold rmStack; omega)
    h.heap (h.resSlot hw) h10 h11 h12 h13
    ⟨fun R' Mt H' F' L' y hk' hp => ?_, fun R' Mt sp' o1 o2 r2 hout => ?_⟩
  · exact cf_ret cx hfr h hp (by omega) hsv ho (hk'.mono (by decide))
      fun C' hfr' hd hw' hO hkp => hk R' Mt H' F' L' C' y (hk'.mono (by decide)) hfr' hd hp.num hw' hO hkp
  · have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
    bc_run hlive hS [] at 0x80001e74
    exact hoom R' Mt sp' (hfr.oom cx (W := 96 + rmStack (2 ^ 30)) (by unfold cfW; omega) ho o1 o2 r2
      fun a ho' hs' hf => hout a ho' hf)

/-- **`bc_add (a, b, &slot, smin)`** with the slot at `o` holding a handle of
the state. -/
theorem cf_add {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {p p1 p2 sp o smin : Nat} {n1 n2 : Num} {R0 R : Nat → BitVec 64}
    (cx : CfCtx S fs sp) (hfr : CFr fs sv M0 M R0 R sp) (h : DcAt S M H F L C G (.num p :: hs) st)
    (hsv : ∀ q ∈ sv, o + 8 ≤ q.1) (ho : o + 8 ≤ fs) (h8 : o % 8 = 0)
    (hw : ldv .ld M (sp - fs + o) = BitVec.ofNat 64 p)
    (hd1 : (GV.num p1).Den ⟨L, G.strs⟩ (.num n1)) (hd2 : (GV.num p2).Den ⟨L, G.strs⟩ (.num n2))
    (hsm : smin < 2 ^ 30)
    (h10 : R 10 = BitVec.ofNat 64 p1) (h11 : R 11 = BitVec.ofNat 64 p2)
    (h12 : R 12 = BitVec.ofNat 64 (sp - fs + o)) (h13 : R 13 = BitVec.ofNat 64 smin)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' y, Keeps cClob R' R → CFr fs sv M0 M' R0 R' sp →
      DcAt S M' H' F' (y :: L') C' G (.num y.rep.p :: hs) st → y.rep.num = Num.add n1 n2 smin →
      ldv .ld M' (sp - fs + o) = BitVec.ofNat 64 y.rep.p → CfOut M M' sp fs o →
      HsKeep ⟨L, G.strs⟩ ⟨y :: L', G.strs⟩ hs → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp (fs + cfW) M0 (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80005634#64 R M := by
  have hab := cx.abv
  have hab' := cx.ab
  have hW : cfW = 176 + rmStack (2 ^ 30) := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hsl := cx.sf.lo
  simp only [heapEnd] at hab hab'
  obtain ⟨L1, L2, x, rfl, rfl⟩ := h.handle_num
  obtain ⟨x1, hx1, e1p, e1n⟩ := hd1.numObj
  obtain ⟨x2, hx2, e2p, e2n⟩ := hd2.numObj
  subst e1p e2p e1n e2n
  refine bc_add_spec hlive
    ⟨cx.win (by omega), by simp only [heapEnd]; omega, cx.slot ho h8,
      fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega), .inr (by omega),
      hfr.r2, hal⟩
    (h.binArgs hx1 hx2 hsm) (fun _ => ⟨h.den.pos x1 hx1, h.den.pos x2 hx2⟩)
    h.heap (h.resSlot hw) h10 h11 h12 h13
    ⟨fun R' Mt H' F' L' y hk' hp => ?_, fun R' Mt sp' o1 o2 r2 hout => ?_⟩
  · exact cf_ret cx hfr h hp (by omega) hsv ho (hk'.mono (by decide))
      fun C' hfr' hd hw' hO hkp => hk R' Mt H' F' L' C' y (hk'.mono (by decide)) hfr' hd hp.num hw' hO hkp
  · have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
    bc_run hlive hS [] at 0x80001e74
    exact hoom R' Mt sp' (hfr.oom cx (W := 176) (by unfold cfW; omega) ho o1 o2 r2
      fun a ho' hs' hf => hout a ho' hf)

/-- **`bc_sub (a, b, &slot, smin)`** with the slot at `o` holding a handle of
the state. -/
theorem cf_sub {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {p p1 p2 sp o smin : Nat} {n1 n2 : Num} {R0 R : Nat → BitVec 64}
    (cx : CfCtx S fs sp) (hfr : CFr fs sv M0 M R0 R sp) (h : DcAt S M H F L C G (.num p :: hs) st)
    (hsv : ∀ q ∈ sv, o + 8 ≤ q.1) (ho : o + 8 ≤ fs) (h8 : o % 8 = 0)
    (hw : ldv .ld M (sp - fs + o) = BitVec.ofNat 64 p)
    (hd1 : (GV.num p1).Den ⟨L, G.strs⟩ (.num n1)) (hd2 : (GV.num p2).Den ⟨L, G.strs⟩ (.num n2))
    (hsm : smin < 2 ^ 30)
    (h10 : R 10 = BitVec.ofNat 64 p1) (h11 : R 11 = BitVec.ofNat 64 p2)
    (h12 : R 12 = BitVec.ofNat 64 (sp - fs + o)) (h13 : R 13 = BitVec.ofNat 64 smin)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' y, Keeps cClob R' R → CFr fs sv M0 M' R0 R' sp →
      DcAt S M' H' F' (y :: L') C' G (.num y.rep.p :: hs) st → y.rep.num = Num.sub n1 n2 smin →
      ldv .ld M' (sp - fs + o) = BitVec.ofNat 64 y.rep.p → CfOut M M' sp fs o →
      HsKeep ⟨L, G.strs⟩ ⟨y :: L', G.strs⟩ hs → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp (fs + cfW) M0 (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80004ac4#64 R M := by
  have hab := cx.abv
  have hab' := cx.ab
  have hW : cfW = 176 + rmStack (2 ^ 30) := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hsl := cx.sf.lo
  simp only [heapEnd] at hab hab'
  obtain ⟨L1, L2, x, rfl, rfl⟩ := h.handle_num
  obtain ⟨x1, hx1, e1p, e1n⟩ := hd1.numObj
  obtain ⟨x2, hx2, e2p, e2n⟩ := hd2.numObj
  subst e1p e2p e1n e2n
  refine bc_sub_spec hlive
    ⟨cx.win (by omega), by simp only [heapEnd]; omega, cx.slot ho h8,
      fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega), .inr (by omega),
      hfr.r2, hal⟩
    (h.binArgs hx1 hx2 hsm) (fun _ => ⟨h.den.pos x1 hx1, h.den.pos x2 hx2⟩)
    h.heap (h.resSlot hw) h10 h11 h12 h13
    ⟨fun R' Mt H' F' L' y hk' hp => ?_, fun R' Mt sp' o1 o2 r2 hout => ?_⟩
  · exact cf_ret cx hfr h hp (by omega) hsv ho (hk'.mono (by decide))
      fun C' hfr' hd hw' hO hkp => hk R' Mt H' F' L' C' y (hk'.mono (by decide)) hfr' hd hp.num hw' hO hkp
  · have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
    bc_run hlive hS [] at 0x80001e74
    exact hoom R' Mt sp' (hfr.oom cx (W := 176) (by unfold cfW; omega) ho o1 o2 r2
      fun a ho' hs' hf => hout a ho' hf)

end Dc.Mach
