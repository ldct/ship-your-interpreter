import Dc.Mach.DcPop
import Dc.Mach.DcInt

/-!
# `dc_binop` (M9)

    dc_binop (int (*op)(), int kscale):
      if (dc_stack == NULL || dc_stack->link == NULL)
        { fprintf (stderr, "%s: stack empty\n", progname); return; }
      if (top two types are not both DC_NUMBER)
        { fprintf (stderr, "%s: non-numeric value\n", progname); return; }
      dc_pop (&b); dc_pop (&a);
      if ((*op)(a.v.number, b.v.number, kscale, &r.v.number) == DC_SUCCESS)
        { r.dc_type = DC_NUMBER; dc_push (r);   -- inlined: dc_malloc and four stores
          dc_free_num (&a.v.number); dc_free_num (&b.v.number); }
      else { dc_push (a); dc_push (b); }

- `DcOp`: the contract of an operation called through `op` (`dc_add` …
  `dc_exp`): from the two popped handles to a fresh handle denoting `f k a b`
  in the result slot (`OpRet`), or a nonzero return with the state kept
  (`OpFail`), or `dc_memfail` (`OomAt`). Lost references are added to the
  ghost's `lk` (`DcG`), at most `lk` per call.
- `binop_entry`: the two checks and their messages.
- `dc_binop_spec`: `binop st (f st.scale)`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The registers a C function may change: the caller-saved ones. -/
abbrev opClob : List Nat := [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- bc's `mul_base_digits`, which dc never changes: `80`, owned. -/
structure MulBase (S : Nat → Prop) (M : Mem) : Prop where
  own : ∀ a, mulBaseAddr ≤ a → a < mulBaseAddr + 4 → S a
  word : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80

theorem MulBase.transport {S : Nat → Prop} {M M' : Mem} (h : MulBase S M)
    (hag : ∀ a, mulBaseAddr ≤ a → a < mulBaseAddr + 4 → imgM M' a = imgM M a) : MulBase S M' where
  own := h.own
  word := by
    rw [ldv_congr .lw fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]
    exact h.word

/-- `mul_base_digits` is off the heap, not one of dc's globals, below every stack frame. -/
theorem mulBase_off {a : Nat} (h1 : mulBaseAddr ≤ a) (h2 : a < mulBaseAddr + 4) :
    OutHeap a ∧ ¬ DcGlob a ∧ a < heapStart := by
  refine ⟨?_, fun hg => ?_, ?_⟩
  · simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, mulBaseAddr] at h1 h2 ⊢; omega
  · simp only [DcGlob, dc_addrs, mulBaseAddr] at hg h1 h2; omega
  · simp only [heapStart, mulBaseAddr] at h1 h2 ⊢; omega

/-- `dc_memfail` reached from below `sp` within the window `W`: memory changed
only in the heap, dc's globals, the window and the bytes `P`. -/
structure OomAt (S : Nat → Prop) (sp W : Nat) (M0 : Mem) (P : Nat → Prop) (sp' : Nat)
    (R' : Nat → BitVec 64) (M' : Mem) : Prop where
  lo : sp - W ≤ sp'
  hi : sp' ≤ sp
  r2 : R' 2 = BitVec.ofNat 64 sp'
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp W a → ¬ P a → imgM M' a = imgM M0 a

/-- An operation's entry: the operand handles `pa`, `pb` (denoting `na`, `nb`)
held by the caller, the scale in `a2`, the result slot `q` above the frame. -/
structure OpIn (S : Nat → Prop) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G : DcG) (hs : List GV) (st : St) (pa pb : Nat) (na nb : Num)
    (R : Nat → BitVec 64) (sp q N lk : Nat) : Prop where
  h : DcAt S M H F L C G (.num pa :: .num pb :: hs) st
  da : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb)
  hsLen : hs.length + 3 ≤ 2 ^ 20
  lkLen : G.lk.length + lk ≤ 2 ^ 29
  frame : StackFrame S sp N
  above : heapEnd + N ≤ sp
  slot : PtrSlot S q
  slotHi : sp ≤ q
  r10 : R 10 = BitVec.ofNat 64 pa
  r11 : R 11 = BitVec.ofNat 64 pb
  r12 : R 12 = BitVec.ofNat 64 st.scale
  r13 : R 13 = BitVec.ofNat 64 q
  r2 : R 2 = BitVec.ofNat 64 sp
  al : (R 1).toNat % 4 = 0
  mb : MulBase S M

/-- An operation's success: `0`, the fresh handle `y` for `r` in the slot. -/
structure OpRet (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G0 G : DcG) (hs : List GV) (st : St) (pa pb : Nat) (na nb : Num)
    (f : Nat → Num → Num → Option Num) (R : Nat → BitVec 64) (sp q N lk y : Nat) (r : Num) :
    Prop where
  a0 : R 10 = 0#64
  h : DcAt S M H F L C G (.num y :: .num pa :: .num pb :: hs) st
  val : f st.scale na nb = some r
  den : (GV.num y).Den ⟨L, G.strs⟩ (.num r)
  word : ldv .ld M q = BitVec.ofNat 64 y
  same : G = { G0 with lk := G.lk }
  lkLen : G.lk.length ≤ G0.lk.length + lk
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slotBytes q a → imgM M a = imgM M0 a

/-- An operation's failure: nonzero, the operands kept. -/
structure OpFail (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G0 G : DcG) (hs : List GV) (st : St) (pa pb : Nat) (na nb : Num)
    (f : Nat → Num → Num → Option Num) (R : Nat → BitVec 64) (sp q N lk : Nat) : Prop where
  a0 : R 10 ≠ 0#64
  h : DcAt S M H F L C G (.num pa :: .num pb :: hs) st
  val : f st.scale na nb = none
  da : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb)
  same : G = { G0 with lk := G.lk }
  lkLen : G.lk.length ≤ G0.lk.length + lk
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slotBytes q a → imgM M a = imgM M0 a

/-- **The contract of an operation at `fa`** computing `f k a b` within the
stack window `N`, losing at most `lk` references. -/
def DcOp (live S : Nat → Prop) (fa N lk : Nat) (ok : Nat → Num → Num → Prop)
    (f : Nat → Num → Num → Option Num) : Prop :=
  ∀ (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (t : String) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs : List GV) (st : St)
    (pa pb : Nat) (na nb : Num) (R : Nat → BitVec 64) (sp q : Nat),
    OpIn S M H F L C G hs st pa pb na nb R sp q N lk → ok st.scale na nb →
    (∀ R' M' H' F' L' C' G' y r, Keeps opClob R' R →
      OpRet S M M' H' F' L' C' G G' hs st pa pb na nb f R' sp q N lk y r → DWO live S Q t (R 1) R' M') →
    (∀ R' M' H' F' L' C' G', Keeps opClob R' R →
      OpFail S M M' H' F' L' C' G G' hs st pa pb na nb f R' sp q N lk → DWO live S Q t (R 1) R' M') →
    (∀ R' M' sp', OomAt S sp N M (slotBytes q) sp' R' M' → DWO live S Q t 0x80001e74#64 R' M') →
    DWO live S Q t (BitVec.ofNat 64 fa) R M

/-! ## The model -/

/-- `binop` leaves the state when the top two are not both numbers. -/
theorem binop_of_not {st : St} {f : Num → Num → Option Num}
    (h : ∀ b a rest, st.stack ≠ .num b :: .num a :: rest) : binop st f = st := by
  unfold binop
  split
  · rename_i b a rest e; exact absurd e (h b a rest)
  · rfl

theorem binop_push_some {st : St} {a b r : Num} {g : Num → Num → Option Num} (h : g a b = some r) :
    binop ((st.push (.num a)).push (.num b)) g = st.push (.num r) := by
  simp only [binop, St.push, h]

theorem binop_push_none {st : St} {a b : Num} {g : Num → Num → Option Num} (h : g a b = none) :
    binop ((st.push (.num a)).push (.num b)) g = (st.push (.num a)).push (.num b) := by
  simp only [binop, St.push, h]

/-! ## The checks -/

/-- A stack node's payload in the heap. -/
theorem DcAt.stkPay {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {c : Blk} {g : GV} (hc : (c, g) ∈ G.stk) :
    2147603936 ≤ c.pay ∧ c.pay + 32 ≤ 2273312768 ∧ c.pay % 16 = 0 := by
  have hn := h.view.stk.forall _ hc
  have fbb := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live c (DcG.stk_mem hc)))
  have hblo : 2147603920 ≤ c.h := fbb.lo
  have hbhi : c.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : c.h % 16 = 0 := fbb.al
  have hbsz := hn.sz
  simp only [Blk.pay, Blk.fin] at *; omega

theorem ofNat_pos_ne {p : Nat} (h1 : 0 < p) (h2 : p < 2 ^ 64) : BitVec.ofNat 64 p ≠ 0#64 :=
  fun hc => by
    have := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod] at this
    rw [Nat.mod_eq_of_lt h2] at this; omega

theorem nonNumMsg : ProgMsg 0x80007de0 20 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

/-- A message tail of `dc_binop` (`0x800031f0`: non-numeric, `0x8000320c`:
stack empty): `fprintf (stderr, msg, progname)` as a tail call. -/
theorem binop_msg {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 304) (hab : heapEnd + 304 ≤ sp) {pc : BitVec 64}
    (hpc : pc = 0x800031f0#64 ∨ pc = 0x8000320c#64)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk0 : ∀ R' M', Keeps fprintfClob R' R →
      (∀ a, (a < sp - 304 ∨ sp ≤ a) → imgM M' a = imgM M a) → DWO live S Q t (R 1) R' M') :
    DWO live S Q t pc R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hpn := h.view.prog
  have hG := h.glob
  have hfd := h.errFile
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  have msg : ∀ {p n : Nat}, ProgMsg p n → n < 2 ^ 60 → ∀ R1 : Nat → BitVec 64,
      Keeps fprintfClob R1 R → R1 1 = R 1 → R1 2 = R 2 → (R1 10).toNat = stderrAddr →
      (R1 11).toNat = p → R1 12 = BitVec.ofNat 64 dcNameAddr →
      DWO live S Q t 0x80000774#64 R1 M := by
    intro p n hm hn R1 hk1 e1 e2 e10 e11 e12
    refine fprintf_prog_spec hlive hm hn hsf (by simp only [stderrAddr]; omega) hfd R1
      (by rw [e2, h2]; bsimp []) e10 e11 e12 (by rw [e1]; exact hal) fun R' M' hk2 hfr => ?_
    rw [e1]
    exact hk0 R' M' (hk2.trans hk1) hfr
  rcases hpc with rfl | rfl
  · bc_run hlive hS [h2, hpn, stderr_word] at 0x80000774
    exact msg nonNumMsg (by decide) _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
      (by bsimp []) (by bsimp []; decide) (by bsimp []) (by bsimp [])
  · bc_run hlive hS [h2, hpn, stderr_word] at 0x80000774
    exact msg stackEmptyMsg (by decide) _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
      (by bsimp []) (by bsimp []; decide) (by bsimp []) (by bsimp [])

/-- `dc_binop`'s checks with two nodes on the stack. -/
theorem binop_two {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64}
    {c1 c2 : Blk} {g1 g2 : GV}
    (h0 : ldv .ld M dcStackAddr = BitVec.ofNat 64 c1.pay)
    (h0' : ldv .ld M (c1.pay + 24) = BitVec.ofNat 64 c2.pay)
    (ht1 : ldv .lw M c1.pay = BitVec.ofNat 64 g1.tag) (ht2 : ldv .lw M c2.pay = BitVec.ofNat 64 g2.tag)
    (hc1 : 2147603936 ≤ c1.pay ∧ c1.pay + 32 ≤ 2273312768 ∧ c1.pay % 16 = 0)
    (hc2 : 2147603936 ≤ c2.pay ∧ c2.pay + 32 ≤ 2273312768 ∧ c2.pay % 16 = 0)
    (hG : ∀ a, DcGlob a → S a)
    (hno : (g1.tag ≠ 1 ∨ g2.tag ≠ 1) → ∀ R', Keeps [11, 12, 13, 14, 15] R' R →
      DWO live S Q t 0x800031f0#64 R' M)
    (hgo : g1.tag = 1 → g2.tag = 1 → ∀ R', Keeps [13, 14, 15] R' R → R' 14 = 1#64 →
      DWO live S Q t 0x80003228#64 R' M) :
    DWO live S Q t 0x800031c8#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hc0 : BitVec.ofNat 64 c1.pay ≠ 0#64 := ofNat_pos_ne (by omega) (by omega)
  have hc0' : BitVec.ofNat 64 c2.pay ≠ 0#64 := ofNat_pos_ne (by omega) (by omega)
  bc_run hlive hS [h0, h0', ht1, ht2] at 0x800031f0
  all_goals try (intro hc; exact absurd hc hc0)
  intro _
  bsimp []
  bc_run hlive hS [h0, h0', ht1, ht2] at 0x800031f0
  all_goals try (intro hc; exact absurd hc hc0')
  intro _
  bsimp []
  obtain e1 | e1 : g1.tag = 1 ∨ g1.tag = 2 := by cases g1 <;> simp [GV.tag]
  · rw [e1] at ht1
    obtain e2 | e2 : g2.tag = 1 ∨ g2.tag = 2 := by cases g2 <;> simp [GV.tag]
    · rw [e2] at ht2
      bc_run hlive hS [h0, h0', ht1, ht2] at 0x80003228
      all_goals try (intro hc; exact absurd hc (by decide))
      (try intro _); (try bsimp [])
      bc_run hlive hS [h0, h0', ht1, ht2] at 0x80003228
      all_goals try (intro hc; exact absurd hc (by decide))
      (try intro _); (try bsimp [])
      exact hgo e1 e2 _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
    · rw [e2] at ht2
      bc_run hlive hS [h0, h0', ht1, ht2] at 0x800031f0
      all_goals try (intro hc; exact absurd hc (by decide))
      (try intro _); (try bsimp [])
      bc_run hlive hS [h0, h0', ht1, ht2] at 0x800031f0
      all_goals try (intro hc; exact absurd hc (by decide))
      (try intro _); (try bsimp [])
      exact hno (.inr (by omega)) _ (by keeps_tac Keeps.refl _ _)
  · rw [e1] at ht1
    bc_run hlive hS [h0, h0', ht1, ht2] at 0x800031f0
    all_goals try (intro hc; exact absurd hc (by decide))
    (try intro _); (try bsimp [])
    exact hno (.inl (by omega)) _ (by keeps_tac Keeps.refl _ _)

/-- **`dc_binop`'s checks** at `0x800031c8`: with two numbers on top the run
goes on at `0x80003228` (`a4` the second's type `1`); otherwise one of the
two messages goes to `stderr` and `dc_binop` returns with the state kept. -/
theorem binop_entry {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 304) (hab : heapEnd + 304 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk0 : (∀ b a rest, st.stack ≠ .num b :: .num a :: rest) → ∀ R' M', Keeps fprintfClob R' R →
      (∀ a, (a < sp - 304 ∨ sp ≤ a) → imgM M' a = imgM M a) → DWO live S Q t (R 1) R' M')
    (hgo : ∀ cb ca pb pa rest, G.stk = (cb, .num pb) :: (ca, .num pa) :: rest → ∀ R',
      Keeps [13, 14, 15] R' R → R' 14 = 1#64 → DWO live S Q t 0x80003228#64 R' M) :
    DWO live S Q t 0x800031c8#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hden := h.den.stk
  have hv := h.view.stk
  have hmsg : ∀ {pc : BitVec 64}, (pc = 0x800031f0#64 ∨ pc = 0x8000320c#64) →
      (∀ b a rest, st.stack ≠ .num b :: .num a :: rest) → ∀ R1, Keeps [11, 12, 13, 14, 15] R1 R →
      DWO live S Q t pc R1 M := fun hpc hno R1 hk1 =>
    binop_msg hlive h hsf hab hpc R1 (by rw [hk1.get 2 (by decide), h2])
      (by rw [hk1.get 1 (by decide)]; exact hal) fun R' M' hk2 hfr => by
        rw [hk1.get 1 (by decide)]
        exact hk0 hno R' M' (hk2.trans ((hk1.mono (by decide)))) hfr
  cases hstk : G.stk with
  | nil =>
    rw [hstk] at hv hden
    have hno : ∀ b a rest, st.stack ≠ .num b :: .num a :: rest := fun b a rest e => by
      rw [e] at hden; cases hden
    cases hv with
    | nil h0 =>
    bc_run hlive hS [h0] at 0x8000320c
    exact hmsg (.inr rfl) hno _ (by keeps_tac Keeps.refl _ _)
  | cons n1 rest1 =>
    obtain ⟨c1, g1⟩ := n1
    have hc1 := h.stkPay (c := c1) (g := g1) (by rw [hstk]; exact List.mem_cons_self)
    rw [hstk] at hv hden
    have hc0 : BitVec.ofNat 64 c1.pay ≠ 0#64 := ofNat_pos_ne (by omega) (by omega)
    cases hv with
    | cons h0 hn1 hl1 =>
    cases rest1 with
    | nil =>
      cases hl1 with
      | nil hl0 =>
      have hno : ∀ b a rest, st.stack ≠ .num b :: .num a :: rest := fun b a rest e => by
        rw [e] at hden; cases hden with | cons _ hr => cases hr
      bc_run hlive hS [h0, hl0] at 0x8000320c
      all_goals try (intro hc; exact absurd hc hc0)
      (try intro _); (try bsimp [])
      bc_run hlive hS [h0, hl0] at 0x8000320c
      exact hmsg (.inr rfl) hno _ (by keeps_tac Keeps.refl _ _)
    | cons n2 rest2 =>
      obtain ⟨c2, g2⟩ := n2
      have hc2 := h.stkPay (c := c2) (g := g2) (by rw [hstk]; simp)
      cases hl1 with
      | cons h0' hn2 hl2 =>
      refine binop_two hlive hS h0 h0' hn1.dat.lw hn2.dat.lw hc1 hc2 hG (fun hn R1 hk1 => ?_)
        fun e1 e2 R1 hk1 e14 => ?_
      · refine hmsg (.inl rfl) (fun b a rest e => ?_) R1 hk1
        rw [e] at hden
        cases hden with
        | cons hh hr =>
        cases hr with
        | cons hh2 _ =>
        rcases hn with hn | hn
        · cases g1 with
          | num _ => exact hn rfl
          | str _ => exact hh
        · cases g2 with
          | num _ => exact hn rfl
          | str _ => exact hh2
      · cases g1 with
        | str _ => simp [GV.tag] at e1
        | num pb =>
        cases g2 with
        | str _ => simp [GV.tag] at e2
        | num pa => exact hgo c1 c2 pb pa rest2 hstk R1 hk1 e14

/-! ## The pops -/

theorem StackFrame.within {S : Nat → Prop} {sp W m n : Nat} (h : StackFrame S sp W) (hmn : m + n ≤ W)
    (hm : m % 16 = 0) : StackFrame S (sp - m) n where
  own a h1 h2 := h.own a (by omega) (by omega)
  lo := by have := h.lo; omega
  hi := by have := h.hi; omega
  al := by have := h.al; omega

theorem StackFrame.mono {S : Nat → Prop} {sp W n : Nat} (h : StackFrame S sp W) (hn : n ≤ W) :
    StackFrame S sp n where
  own a h1 h2 := h.own a (by omega) h2
  lo := by have := h.lo; omega
  hi := h.hi
  al := h.al

/-- An aligned word inside the stack frame `h` is a pointer slot. -/
theorem StackFrame.slot {S : Nat → Prop} {sp W q : Nat} (h : StackFrame S sp W) (hlo : sp - W ≤ q)
    (hhi : q + 8 ≤ sp) (hal : q % 8 = 0) : PtrSlot S q where
  own i hi := h.own _ (by omega) (by omega)
  al := hal
  lo := by have := h.lo; omega
  hi := by have := h.hi; omega

/-- A byte at or above a stack pointer over the heap: off the heap, not a global,
outside every window below `sp`. -/
theorem above_sp {sp a : Nat} (hh : heapEnd ≤ sp) (ha : sp ≤ a) :
    OutHeap a ∧ ¬ DcGlob a ∧ ∀ n, ¬ frameIn sp n a :=
  ⟨outHeap_of_ge (by omega), fun hg => by
    have := hg.lt; simp only [heapStart, heapEnd] at this hh; omega,
    fun n hf => by simp only [frameIn] at hf; omega⟩

/-- `dc_binop`'s frame words (`sp1 = sp - 112`): `op`, `kscale`, the second's
type word and the return address. -/
structure BoFrame (M : Mem) (sp1 fa k : Nat) (ra : BitVec 64) : Prop where
  wfa : ldv .ld M (sp1 + 8) = BitVec.ofNat 64 fa
  wk : ldv .ld M (sp1 + 16) = BitVec.ofNat 64 k
  wtag : ldv .ld M (sp1 + 24) = 1#64
  wra : ldv .ld M (sp1 + 104) = ra

theorem BoFrame.transport {M M' : Mem} {sp1 fa k : Nat} {ra : BitVec 64} (h : BoFrame M sp1 fa k ra)
    (hag : ∀ a, (sp1 + 8 ≤ a ∧ a < sp1 + 32) ∨ (sp1 + 104 ≤ a ∧ a < sp1 + 112) → imgM M' a = imgM M a) :
    BoFrame M' sp1 fa k ra where
  wfa := by rw [ldv_congr .ld fun j hj => hag _ (.inl (by simp only [widthOfM] at hj; omega))]; exact h.wfa
  wk := by rw [ldv_congr .ld fun j hj => hag _ (.inl (by simp only [widthOfM] at hj; omega))]; exact h.wk
  wtag := by rw [ldv_congr .ld fun j hj => hag _ (.inl (by simp only [widthOfM] at hj; omega))]; exact h.wtag
  wra := by rw [ldv_congr .ld fun j hj => hag _ (.inr (by simp only [widthOfM] at hj; omega))]; exact h.wra

/-- The state at the call of `op`: both operands popped into the slots at
`sp1 + 32` (`a`) and `sp1 + 48` (`b`), their handles held. -/
structure BoAt (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G2 : DcG) (hs : List GV) (st st2 : St) (sp W fa k : Nat) (ra : BitVec 64)
    (pa pb : Nat) (na nb : Num) : Prop where
  st : st = (st2.push (.num na)).push (.num nb)
  h : DcAt S M H F L C G2 (.num pa :: .num pb :: hs) st2
  da : (GV.num pa).Den ⟨L, G2.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G2.strs⟩ (.num nb)
  fr : BoFrame M (sp - 112) fa k ra
  sa : DatAt M (sp - 112 + 32) (.num pa)
  sb : DatAt M (sp - 112 + 48) (.num pb)
  out : StkOut sp W M M0

/-- The head of a stack whose ghost head is a number handle. -/
theorem den_num_head {O : DObjs} {p : Nat} {v : Val} (h : (GV.num p).Den O v) :
    ∃ n, v = .num n ∧ (GV.num p).Den O (.num n) := by
  cases v with
  | num n => exact ⟨n, rfl, h⟩
  | str s => exact h.elim

theorem word_sub112 {x : Nat} (h : 112 ≤ x) :
    BitVec.ofNat 64 x + 18446744073709551504#64 = BitVec.ofNat 64 (x - 112) := by
  change BitVec.ofNat 64 x + -(112#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le x 112 (by decide) h

/-- **`dc_binop`'s two pops** (`0x80003228` to the call of `op`). -/
theorem binop_pops {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp W : Nat}
    (hsf : StackFrame S sp W) (hab : heapEnd + W ≤ sp) (hW : 448 ≤ W)
    {cb ca : Blk} {pb pa : Nat} {rest : List (Blk × GV)}
    (hstk : G.stk = (cb, .num pb) :: (ca, .num pa) :: rest)
    {fa k : Nat} (hfa : fa % 4 = 0) (hfa2 : fa < 2 ^ 64)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 fa) (h11 : R 11 = BitVec.ofNat 64 k)
    (h14 : R 14 = 1#64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R1 M2 H2 G2 st2 na nb, Keeps (1 :: 2 :: popClob) R1 R → G2.lk = G.lk →
      R1 1 = 0x80003264#64 → R1 2 = BitVec.ofNat 64 (sp - 112) → R1 10 = BitVec.ofNat 64 pa →
      R1 11 = BitVec.ofNat 64 pb → R1 12 = BitVec.ofNat 64 k →
      R1 13 = BitVec.ofNat 64 (sp - 112 + 72) →
      BoAt S M M2 H2 F L C G2 hs st st2 sp W fa k (R 1) pa pb na nb →
      DWO live S Q t (BitVec.ofNat 64 fa) R1 M2) :
    DWO live S Q t 0x80003228#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  bc_run hlive hS [h2, h10, h11, h14, word_sub112 (x := sp) (by omega)] at 0x8000310c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 112) (writeLog (writeLog (writeLog (writeLog M
      [(sp - 112 + 8, 8, BitVec.ofNat 64 fa)]) [(sp - 112 + 104, 8, R 1)])
      [(sp - 112 + 16, 8, BitVec.ofNat 64 k)]) [(sp - 112 + 24, 8, 1#64)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hP : ∀ a, sp - W ≤ a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp (sp := sp - W) (by omega) ha).1, (above_sp (sp := sp - W) (by omega) ha).2.1⟩
  have h1 := h.outWrite hM1 fun a ha => hP a (by simp only [frameIn] at ha; omega)
  have hfr1 : BoFrame (writeLog (writeLog (writeLog (writeLog M
      [(sp - 112 + 8, 8, BitVec.ofNat 64 fa)]) [(sp - 112 + 104, 8, R 1)])
      [(sp - 112 + 16, 8, BitVec.ofNat 64 k)]) [(sp - 112 + 24, 8, 1#64)]) (sp - 112) fa k (R 1) :=
    ⟨by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit],
     by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit],
     by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit],
     by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]⟩
  have hslot : ∀ o, o + 16 ≤ 112 → o % 8 = 0 → DatSlot S (sp - 112) (sp - 112 + o) := fun o h1 h2 =>
    ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩
  have hden := h.den.stk
  rw [hstk] at hden
  have hne : st.stack ≠ [] := fun e => by rw [e] at hden; cases hden
  refine dc_pop_spec hlive h1 (hsf.within (m := 112) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (hslot 48 (by omega) (by omega)) _ (by bsimp []) (by bsimp [])
    (by bsimp []) (fun R2 M2 H2 G1 g v st1 est eG hk2 e10 h1' hd1 hout1 => ?_)
    (fun e => absurd e hne)
  obtain ⟨c, rfl⟩ := eG
  simp only [List.cons.injEq, Prod.mk.injEq] at hstk
  obtain ⟨⟨rfl, rfl⟩, hG1⟩ := hstk
  subst est
  obtain ⟨nb, rfl, hdb⟩ := (by cases hden with | cons hh _ => exact den_num_head hh :
    ∃ nb, v = .num nb ∧ (GV.num pb).Den ⟨L, G1.strs⟩ (.num nb))
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk2.get 2 (by decide)]; bsimp []
  have hS2 : HeapOwn S := fun a h1 h2 => h1'.heap.heap.own a h1 h2
  bsimp []
  bc_run hlive hS2 [q2] at 0x8000310c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hden1 := h1'.den.stk
  rw [hG1] at hden1
  have hne1 : st1.stack ≠ [] := fun e => by rw [e] at hden1; cases hden1
  refine dc_pop_spec hlive h1' (hsf.within (m := 112) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (hslot 32 (by omega) (by omega)) _ (by bsimp []) (by bsimp [q2])
    (by bsimp []) (fun R3 M3 H3 G2 g2 v2 st2 est2 eG2 hk3 e10' h2' hd2 hout2 => ?_)
    (fun e => absurd e hne1)
  obtain ⟨c2, rfl⟩ := eG2
  simp only [List.cons.injEq, Prod.mk.injEq] at hG1
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hG1
  subst est2
  obtain ⟨na, rfl, hda⟩ := (by cases hden1 with | cons hh _ => exact den_num_head hh :
    ∃ na, v2 = .num na ∧ (GV.num pa).Den ⟨L, G2.strs⟩ (.num na))
  have hab2 : heapEnd ≤ sp - 112 := by omega
  have hfr3 : BoFrame M3 (sp - 112) fa k (R 1) := (hfr1.transport fun a ha => by
      have ⟨o1, o2, o3⟩ := above_sp hab2 (a := a) (by omega)
      exact hout1 a o1 o2 (o3 _) (by omega)).transport fun a ha => by
    have ⟨o1, o2, o3⟩ := above_sp hab2 (a := a) (by omega)
    exact hout2 a o1 o2 (o3 _) (by omega)
  have hb3 : ldv .ld M3 (sp - 112 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => by
      have ⟨o1, o2, o3⟩ := above_sp hab2 (a := sp - 112 + 48 + 8 + j) (by omega)
      exact hout2 _ o1 o2 (o3 _) (by simp only [widthOfM] at hj; omega)]
    exact hd1.ptr
  have ha3 := hd2.ptr
  have q3 : R3 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
  have hS3 : HeapOwn S := fun a h1 h2 => h2'.heap.heap.own a h1 h2
  have wfa := hfr3.wfa
  have wk := hfr3.wk
  bsimp []
  have hfal : (BitVec.ofNat 64 fa).toNat % 4 = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfa2]; exact hfa
  bc_run hlive hS3 [q3, hb3, ha3, wfa, wk]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · rw [jalr_tgt _ hfal]; exact hfal
  rw [jalr_tgt _ hfal]
  have hsb : DatAt M3 (sp - 112 + 48) (.num pb) := by
    refine ⟨?_, hb3⟩
    rw [ldv_congr .ld fun j hj => by
      have ⟨o1, o2, o3⟩ := above_sp hab2 (a := sp - 112 + 48 + j) (by omega)
      exact hout2 _ o1 o2 (o3 _) (by simp only [widthOfM] at hj; omega)]
    exact hd1.tag
  refine hk _ M3 H3 G2 st2 na nb
    (by keeps_tac ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))))) rfl
    (by bsimp []) (by bsimp [q3]) (by bsimp []; rfl) (by bsimp []) (by bsimp []) (by bsimp [])
    ⟨rfl, h2', hda, hdb, hfr3, hd2, hsb, fun a ho hg hf => ?_⟩
  have hf1 : ¬ frameIn (sp - 112) 336 a := fun h' => hf (by simp only [frameIn] at h' ⊢; omega)
  rw [hout2 a ho hg hf1 (by simp only [frameIn] at hf; omega),
    hout1 a ho hg hf1 (by simp only [frameIn] at hf; omega)]
  exact hM1 a fun h' => hf (by simp only [frameIn] at h' ⊢; omega)

/-! ## After `op` -/

/-- **`op` failed** (`0x80003264`, `a0 ≠ 0`): `a` then `b` pushed back, the
state as before the pops. -/
theorem binop_fail {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb : Nat} {na nb : Num} (h : DcAt S M H F L C G (.num pa :: .num pb :: hs) st)
    (hda : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)) (hdb : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb))
    {sp fa k : Nat} {ra : BitVec 64} (hsf : StackFrame S sp 176) (hab : heapEnd + 176 ≤ sp)
    (hfr : BoFrame M (sp - 112) fa k ra) (hsa : DatAt M (sp - 112 + 32) (.num pa))
    (hsb : DatAt M (sp - 112 + 48) (.num pb)) (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (h10 : R 10 ≠ 0#64)
    (hk : ∀ R' M' H' G', Keeps (1 :: 2 :: pushClob) R' R → G'.lk = G.lk → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DcAt S M' H' F L C G' hs ((st.push (.num na)).push (.num nb)) → StkOut (sp - 112) 64 M' M →
      DWO live S Q t ra R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 112 - 64) → StkOut (sp - 112) 64 M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80003264#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 112 := by omega
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hfs : StackFrame S (sp - 112) 64 := hsf.within (by omega) (by decide)
  have wa0 := hsa.ptr
  refine st_80003264 hlive (fun _ => ?_) fun hc => absurd h10 hc
  bc_run hlive hS [h2, wa0] at 0x80002da4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have habv : ∀ a, sp - 112 ≤ a → ∀ M1 : Mem, StkOut (sp - 112) 64 M1 M → imgM M1 a = imgM M a :=
    fun a ha M1 ho => by
      have ⟨o1, o2, o3⟩ := above_sp hab2 ha
      exact ho a o1 o2 (o3 _)
  refine dc_push_spec hlive h hda hfs (by simp only [heapEnd]; omega) _ ⟨by bsimp []; exact hsa.tag,
    by bsimp []⟩ (by bsimp [h2]) (by bsimp [])
    (fun R1 M1 H1 c1 hk1 h1 hout1 => ?_) (fun R1 M1 e2 hout1 => hoom R1 M1 e2 hout1)
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
  have wb0 : ldv .ld M1 (sp - 112 + 48) = ldv .ld M (sp - 112 + 48) :=
    ldv_congr .ld fun j hj => habv _ (by omega) _ hout1
  have wb1 : ldv .ld M1 (sp - 112 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => habv _ (by omega) _ hout1]; exact hsb.ptr
  have wra : ldv .ld M1 (sp - 112 + 104) = ra := by
    rw [ldv_congr .ld fun j hj => habv _ (by omega) _ hout1]; exact hfr.wra
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS1 [q1, wb0, wb1] at 0x80002da4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_push_spec hlive h1 hdb hfs (by simp only [heapEnd]; omega) _ ⟨by bsimp []; exact hsb.tag,
    by bsimp []; rfl⟩ (by bsimp [q1]) (by bsimp [])
    (fun R2 M2 H2 c2 hk2 h2' hout2 => ?_) (fun R2 M2 e2 hout2 => hoom R2 M2 e2 fun a o1 o2 o3 => by
      rw [hout2 a o1 o2 o3, hout1 a o1 o2 o3])
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk2.get 2 (by decide)]; bsimp [q1]
  have wra2 : ldv .ld M2 (sp - 112 + 104) = ra := by
    rw [ldv_congr .ld fun j hj => habv _ (by omega) _ (fun a o1 o2 o3 => by
      rw [hout2 a o1 o2 o3, hout1 a o1 o2 o3])]; exact hfr.wra
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS2 [q2, wra2]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hral
  refine hk _ M2 H2 { G with stk := (c2, .num pb) :: (c1, .num pa) :: G.stk } (by keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))))) rfl (by bsimp []) (by bsimp [q2]; congr 1; omega) h2'
    fun a o1 o2 o3 => by rw [hout2 a o1 o2 o3, hout1 a o1 o2 o3]

/-- The memory after `dc_binop`'s inline push into the fresh node at `p`:
no array, the datum words, the old `dc_stack` as the link, then `dc_stack`. -/
abbrev boPushMem (M : Mem) (p : Nat) (w0 w1 : BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog M [(p + 16, 8, 0#64)]) [(p, 8, w0)]) [(p + 8, 8, w1)])
    [(p + 24, 8, ldv .ld M dcStackAddr)]) [(dcStackAddr, 8, BitVec.ofNat 64 p)]

/-- **The state after the inline push**: `b` is the new top node. -/
theorem boPush_post {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {v : Val} {b : Blk}
    {w0 w1 : BitVec 64}
    (h : DcAt S M H F L C G (g :: hs) st) (hf : DcFresh H F L G b) (hv : g.Den ⟨L, G.strs⟩ v)
    (hd : DatRegs w0 w1 g) (hsz : 32 ≤ b.sz) (hp1 : 2147603936 ≤ b.pay) :
    DcAt S (boPushMem M b.pay w0 w1) H F L C { G with stk := (b, g) :: G.stk } hs (st.push v) ∧
      MemOnly (fun a => b.In a ∨ StkWord a) (boPushMem M b.pay w0 w1) M := by
  have e1 : b.fin = b.pay + b.sz := by simp only [Blk.fin, Blk.pay]
  have hds : dcStackAddr = 2147601816 := rfl
  have hm4 : MemOnly b.In (writeLog (writeLog (writeLog (writeLog M [(b.pay + 16, 8, 0#64)])
      [(b.pay, 8, w0)]) [(b.pay + 8, 8, w1)]) [(b.pay + 24, 8, ldv .ld M dcStackAddr)]) M :=
    fun a ha => by
      simp only [Blk.In] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have h4 := h.rawWrite hf hm4
  have hn : SNodeAt (writeLog (writeLog (writeLog (writeLog M [(b.pay + 16, 8, 0#64)])
      [(b.pay, 8, w0)]) [(b.pay + 8, 8, w1)]) [(b.pay + 24, 8, ldv .ld M dcStackAddr)]) b g :=
    { dat := { tag := by
                rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]; exact hd.tag
               ptr := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit, hd.ptr] }
      arr := by
        rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
          ldv_store_hit]
      sz := hsz }
  have hl : ldv .ld (writeLog (writeLog (writeLog (writeLog M [(b.pay + 16, 8, 0#64)])
      [(b.pay, 8, w0)]) [(b.pay + 8, 8, w1)]) [(b.pay + 24, 8, ldv .ld M dcStackAddr)]) (b.pay + 24) =
      ldv .ld (writeLog (writeLog (writeLog (writeLog M [(b.pay + 16, 8, 0#64)])
      [(b.pay, 8, w0)]) [(b.pay + 8, 8, w1)]) [(b.pay + 24, 8, ldv .ld M dcStackAddr)]) dcStackAddr := by
    rw [ldv_store_hit, hds]
    repeat rw [ldv_ld_miss _ _ (by omega)]
  refine ⟨h4.pushNode hf hn hl hv, fun a ha => ?_⟩
  simp only [not_or] at ha
  rw [imgM_store_miss _ _ (by simp only [StkWord] at ha; omega)]
  exact hm4 a ha.1

/-- **The operand frees and the return** after the inline push (`0x800032b4`
onward): free the slots at `sp1 + 40` (`a`) and `sp1 + 56` (`b`), reload `ra`, return. -/
theorem binop_frees {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M3 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pa pb : Nat}
    (h3 : DcAt S M3 H F L C G (.num pa :: .num pb :: hs) st)
    {sp : Nat} {ra : BitVec 64} (hsf : StackFrame S sp 176) (hab : heapEnd + 176 ≤ sp)
    (hwa : ldv .ld M3 (sp - 112 + 32 + 8) = BitVec.ofNat 64 pa)
    (hwb : ldv .ld M3 (sp - 112 + 48 + 8) = BitVec.ofNat 64 pb)
    (hwr : ldv .ld M3 (sp - 112 + 104) = ra) (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (q1 : R 2 = BitVec.ofNat 64 (sp - 112))
    (h10 : R 10 = BitVec.ofNat 64 (sp - 112 + 32 + 8)) (h1 : R 1 = 0x800032b8#64)
    (hk : ∀ R' M' H' F' L' C', Keeps (1 :: 2 :: freeNumClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DcAt S M' H' F' L' C' G hs st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 176 a → imgM M' a = imgM M3 a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x80002ba0#64 R M3 := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 112 := by omega
  have hsf32 : StackFrame S (sp - 112) 32 := hsf.within (by omega) (by decide)
  refine dc_free_num_spec hlive h3 (q := sp - 112 + 32 + 8) (hsf.slot (by omega) (by omega) (by omega))
    (by omega) hwa hsf32 (by omega) (Or.inr (by omega)) _ h10 q1 (by rw [h1]; decide)
    (fun R4 M4 H4 F4 L4 C4 hk4 h4 _ hout4 => ?_)
  have ag4 : ∀ a, sp - 112 ≤ a → ¬ slotBytes (sp - 112 + 32 + 8) a → imgM M4 a = imgM M3 a :=
    fun a ha hn => hout4 a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 32) hn
  have q4 : R4 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk4.get 2 (by decide)]; bsimp [q1]
  have hwb4 : ldv .ld M4 (sp - 112 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => ag4 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)]
    exact hwb
  have hS4 : HeapOwn S := fun a e1 e2 => h4.heap.heap.own a e1 e2
  rw [h1]
  bc_run hlive hS4 [q4] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_free_num_spec hlive h4 (q := sp - 112 + 48 + 8) (hsf.slot (by omega) (by omega) (by omega))
    (by omega) hwb4 hsf32 (by omega) (Or.inr (by omega)) _ (by bsimp []) (by bsimp [q4]) (by bsimp [])
    (fun R5 M5 H5 F5 L5 C5 hk5 h5 _ hout5 => ?_)
  have ag5 : ∀ a, sp - 112 ≤ a → ¬ slotBytes (sp - 112 + 48 + 8) a → imgM M5 a = imgM M4 a :=
    fun a ha hn => hout5 a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 32) hn
  have q5 : R5 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk5.get 2 (by decide)]; bsimp [q4]
  have hwr5 : ldv .ld M5 (sp - 112 + 104) = ra := by
    rw [ldv_congr .ld fun j hj => ag5 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega),
      ldv_congr .ld fun j hj => ag4 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)]
    exact hwr
  have hS5 : HeapOwn S := fun a e1 e2 => h5.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS5 [q5, hwr5]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hral
  refine hk _ M5 H5 F5 L5 C5 (by keeps_tac ((hk5.mono (by decide)).trans (by keeps_tac ((hk4.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))))) (by bsimp []) (by bsimp [q5]; congr 1; omega) h5
    fun a ho hg hf => by
      have e5 := hout5 a ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
        (fun hs' => hf (by simp only [frameIn, slotBytes] at hs' ⊢; omega))
      have e4 := hout4 a ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
        (fun hs' => hf (by simp only [frameIn, slotBytes] at hs' ⊢; omega))
      rw [e5, e4]

/-- **`op` succeeded** (`0x80003264`, `a0 = 0`): the result handle `y`
(denoting `r`) pushed inline, then both operand handles freed. -/
theorem binop_ok {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb y : Nat} {r : Num} (h : DcAt S M H F L C G (.num y :: .num pa :: .num pb :: hs) st)
    (hdy : (GV.num y).Den ⟨L, G.strs⟩ (.num r))
    {sp fa k : Nat} {ra : BitVec 64} (hsf : StackFrame S sp 176) (hab : heapEnd + 176 ≤ sp)
    (hfr : BoFrame M (sp - 112) fa k ra) (hsa : DatAt M (sp - 112 + 32) (.num pa))
    (hsb : DatAt M (sp - 112 + 48) (.num pb)) (hy : ldv .ld M (sp - 112 + 72) = BitVec.ofNat 64 y)
    (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 112)) (h10 : R 10 = 0#64)
    (hk : ∀ R' M' H' F' L' C' (G' : DcG), Keeps (1 :: 2 :: opClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → G'.lk = G.lk → DcAt S M' H' F' L' C' G' hs (st.push (.num r)) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 176 a → imgM M' a = imgM M a) →
      DWO live S Q t ra R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 112 - 16) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 176 a → imgM M' a = imgM M a) →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80003264#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 112 := by omega
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  refine st_80003264 hlive (fun hc => absurd h10 hc) fun _ => ?_
  have wtag := hfr.wtag
  bc_run hlive hS [h2, wtag, hy] at 0x80001ea0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hw0 := ld_lo32_sw M (sp - 112 + 64) 1#64
  generalize ldv .ld (writeLog M [(sp - 112 + 64, 4, 1#64)]) (sp - 112 + 64) = w0 at hw0 ⊢
  have hM1 : MemOnly (fun a => sp - 112 + 64 ≤ a ∧ a < sp - 112 + 96)
      (writeLog (writeLog (writeLog M [(sp - 112 + 64, 4, 1#64)]) [(sp - 112 + 88, 8, BitVec.ofNat 64 y)])
        [(sp - 112 + 80, 8, w0)]) M := fun a ha => by
    repeat rw [imgM_store_miss _ _ (by omega)]
  have l80 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 112 + 64, 4, 1#64)])
      [(sp - 112 + 88, 8, BitVec.ofNat 64 y)]) [(sp - 112 + 80, 8, w0)]) (sp - 112 + 80) = w0 :=
    ldv_store_hit _ _ _
  have l88 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 112 + 64, 4, 1#64)])
      [(sp - 112 + 88, 8, BitVec.ofNat 64 y)]) [(sp - 112 + 80, 8, w0)]) (sp - 112 + 88) =
      BitVec.ofNat 64 y := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize (writeLog (writeLog (writeLog M [(sp - 112 + 64, 4, 1#64)])
      [(sp - 112 + 88, 8, BitVec.ofNat 64 y)]) [(sp - 112 + 80, 8, w0)]) = M1 at hM1 l80 l88 ⊢
  have h1 := h.outWrite hM1 fun a ha => ⟨(above_sp hab2 (a := a) (by omega)).1,
    (above_sp hab2 (a := a) (by omega)).2.1⟩
  have hi1 := h1.heap.heap
  refine dc_malloc_spec hlive hi1 (n := 32) (sp := sp - 112) (by omega)
    (hsf.within (m := 112) (n := 16) (by omega) (by decide)) (by simp only [heapEnd]; omega) _
    (by bsimp []) (by bsimp [h2]) (by bsimp []) (fun R1 M2 H2 b hk1 hp hr10 => ?_)
    (fun R1 M2 hr2 hfr2 => ?_)
  rotate_left
  · refine hoom R1 M2 hr2 fun a ho hg hf => ?_
    rw [hfr2 a (OutHeap.not_alloc hi1 ho) (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))]
    exact hM1 a fun ha => hf (by simp only [frameIn]; omega)
  obtain ⟨h2', hfresh⟩ := h1.malloc hp (by decide) (by simp only [heapEnd]; omega)
  have hcl := hfresh.live
  have fbb := h2'.heap.heap.blk (List.mem_append_right _ hcl)
  have hblo : 2147603920 ≤ b.h := fbb.lo
  have hbhi : b.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : b.h % 16 = 0 := fbb.al
  have hbsz := hp.size
  have hpl : 2147603936 ≤ b.pay ∧ b.pay + 32 ≤ 2273312768 ∧ b.pay % 16 = 0 := by
    simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 112) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
  have ag2 : ∀ a, sp - 112 ≤ a → imgM M2 a = imgM M1 a := fun a ha =>
    hp.frame a (OutHeap.not_alloc hi1 (above_sp hab2 ha).1) fun hf => by
      simp only [frameIn] at hf; omega
  have l80' : ldv .ld M2 (sp - 112 + 80) = w0 := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega)]; exact l80
  have l88' : ldv .ld M2 (sp - 112 + 88) = BitVec.ofNat 64 y := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega)]; exact l88
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  have hG2 := h2'.glob
  bsimp []
  bc_run hlive hS2 [q1, hr10, l80', l88'] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hd : DatRegs w0 (BitVec.ofNat 64 y) (.num y) := ⟨by rw [hw0]; rfl, rfl⟩
  obtain ⟨h3, hm3⟩ := boPush_post h2' hfresh hdy hd hp.size hpl1
  show DW _ _ _ _ _ (boPushMem M2 b.pay w0 (BitVec.ofNat 64 y))
  generalize boPushMem M2 b.pay w0 (BitVec.ofNat 64 y) = M3 at h3 hm3
  have agM : ∀ a, sp - 112 ≤ a → ¬ (sp - 112 + 64 ≤ a ∧ a < sp - 112 + 96) → imgM M3 a = imgM M a :=
    fun a ha hn => by
      rw [hm3 a (fun hb => by
        rcases hb with hb | hb
        · simp only [Blk.In] at hb; omega
        · simp only [StkWord, dcStackAddr] at hb; omega), ag2 a ha]
      exact hM1 a hn
  have hwa : ldv .ld M3 (sp - 112 + 32 + 8) = BitVec.ofNat 64 pa := by
    rw [ldv_congr .ld fun j hj => agM _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hsa.ptr
  have hwb : ldv .ld M3 (sp - 112 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => agM _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hsb.ptr
  have hwr : ldv .ld M3 (sp - 112 + 104) = ra := by
    rw [ldv_congr .ld fun j hj => agM _ (by omega) (by omega)]; exact hfr.wra
  exact binop_frees hlive h3 hsf hab hwa hwb hwr hral _ (by bsimp [q1]) (by bsimp []) (by bsimp [])
    fun R' M' H' F' L' C' hk' e1 e2 h' hout' => hk R' M' H' F' L' C' { G with stk := (b, .num y) :: G.stk }
      (by keeps_tac ((hk'.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _))))) e1 e2 rfl h' fun a ho hg hf => by
      rw [hout' a ho hg hf, hm3 a (fun hb => by
        rcases hb with hb | hb
        · simp only [Blk.In, Blk.pay, Blk.fin] at hb hbhi hpl1; simp only [OutHeap, heapStart, heapEnd] at ho; omega
        · exact hg (by simp only [StkWord, DcGlob, dc_addrs] at hb ⊢; omega)),
        hp.frame a (OutHeap.not_alloc hi1 ho) fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]
      exact hM1 a fun ha => hf (by simp only [frameIn]; omega)


/-! ## `dc_binop` -/

/-- **`dc_binop (op, kscale)`** at `0x800031c8` with `op` meeting `DcOp … f`:
the state becomes `binop st (f st.scale)`, losing at most `lk` references. -/
theorem dc_binop_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {fa N lk : Nat} {f : Nat → Num → Num → Option Num}
    {ok : Nat → Num → Num → Prop} (hop : DcOp live S fa N lk ok f) (hfa : fa % 4 = 0)
    (hfa2 : fa < 2 ^ 64)
    {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV}
    {st : St} (h : DcAt S M H F L C G hs st)
    (hok : ∀ b a rest, st.stack = .num b :: .num a :: rest → ok st.scale a b) (hsLen : hs.length + 3 ≤ 2 ^ 20) (hmb : MulBase S M)
    (hlk : G.lk.length + lk ≤ 2 ^ 29) {sp W : Nat} (hsf : StackFrame S sp W) (hab : heapEnd + W ≤ sp)
    (hW : 448 ≤ W) (hN : 112 + N ≤ W)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 fa) (h11 : R 11 = BitVec.ofNat 64 st.scale)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps (1 :: 2 :: opClob) R' R → R' 2 = R 2 →
      G'.lk.length ≤ G.lk.length + lk → DcAt S M' H' F' L' C' G' hs (binop st (f st.scale)) →
      StkOut sp W M' M → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp W M (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x800031c8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 112 := by simp only [heapEnd]; omega
  have hab176 : heapEnd + 176 ≤ sp := by simp only [heapEnd]; omega
  have hsf176 := hsf.mono (n := 176) (by omega)
  refine binop_entry hlive h (hsf.mono (by omega)) (by simp only [heapEnd]; omega) R h2 hal
    (fun hno R' M' hk' hout' => hk R' M' H F L C G (hk'.mono (by decide)) (hk'.get 2 (by decide))
      (by omega) (by
        rw [binop_of_not hno]
        exact h.outWrite (P := frameIn sp 304) (fun a ha => hout' a (by simp only [frameIn] at ha; omega))
          fun a ha => ⟨(above_sp (sp := sp - 304) (by simp only [heapEnd]; omega) ha.1).1,
            (above_sp (sp := sp - 304) (by simp only [heapEnd]; omega) ha.1).2.1⟩)
      fun a ho hg hf => hout' a (by simp only [frameIn] at hf; omega))
    fun cb ca pb pa rest hstk R0 hk0 e14 => ?_
  have r01 : R0 1 = R 1 := hk0.get 1 (by decide)
  refine binop_pops hlive h hsf hab hW hstk hfa hfa2 R0 (by rw [hk0.get 10 (by decide), h10])
    (by rw [hk0.get 11 (by decide), h11]) e14 (by rw [hk0.get 2 (by decide), h2]) (by rw [r01]; exact hal)
    fun R1 M2 H2 G2 st2 na nb hk1 hlk2 e1 e2 e10 e11 e12 e13 hb => ?_
  obtain ⟨est, h2', hda, hdb, hfr, hsa, hsb, hout2⟩ := hb
  subst est
  rw [r01] at hfr
  have hral : (R 1).toNat % 4 = 0 := hal
  have kk : Keeps (1 :: 2 :: opClob) R1 R :=
    (hk1.mono (by decide)).trans (hk0.mono (by decide))
  -- what the operation leaves of the caller's frame words
  have after : ∀ M' : Mem, (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn (sp - 112) N a →
      ¬ slotBytes (sp - 112 + 72) a → imgM M' a = imgM M2 a) →
      BoFrame M' (sp - 112) fa st2.scale (R 1) ∧ DatAt M' (sp - 112 + 32) (.num pa) ∧
        DatAt M' (sp - 112 + 48) (.num pb) := fun M' ho => by
    have ag : ∀ a, sp - 112 ≤ a → ¬ slotBytes (sp - 112 + 72) a → imgM M' a = imgM M2 a :=
      fun a ha hn => ho a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 N) hn
    refine ⟨hfr.transport fun a ha => ag a (by omega) (by simp only [slotBytes]; omega),
      DatAt.congr16 (fun x h1 h2 => ag x (by omega) (by simp only [slotBytes]; omega)) hsa,
      DatAt.congr16 (fun x h1 h2 => ag x (by omega) (by simp only [slotBytes]; omega)) hsb⟩
  have outW : ∀ M' M'' : Mem, (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn (sp - 112) N a →
      ¬ slotBytes (sp - 112 + 72) a → imgM M' a = imgM M2 a) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 176 a → imgM M'' a = imgM M' a) →
      StkOut sp W M'' M := fun M' M'' o1 o2 a ho hg hf => by
    rw [o2 a ho hg (fun h' => hf (by simp only [frameIn] at h' ⊢; omega)),
      o1 a ho hg (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))
        (fun h' => hf (by simp only [slotBytes, frameIn] at h' ⊢; omega))]
    exact hout2 a ho hg hf
  refine hop Q t M2 H2 F L C G2 hs st2 pa pb na nb R1 (sp - 112) (sp - 112 + 72)
    ⟨h2', hda, hdb, hsLen, by rw [hlk2]; exact hlk, hsf.within hN (by decide),
      by simp only [heapEnd]; omega, hsf.slot (by omega) (by omega) (by omega), by omega,
      e10, e11, e12, e13, e2, by rw [e1]; decide, hmb.transport fun a e1 e2 => by
        have ⟨o1, o2, o3⟩ := mulBase_off e1 e2
        exact hout2 a o1 o2 fun hf => by simp only [frameIn, heapStart] at hf o3; omega⟩
    (hok nb na st2.stack rfl)
    (fun R' M' H' F' L' C' G' y r hk' hr => ?_) (fun R' M' H' F' L' C' G' hk' hf => ?_)
    fun R' M' sp' ho => hoom R' M' sp' ⟨by have := ho.lo; omega, by have := ho.hi; omega, ho.r2,
      fun a o1 o2 o3 _ => by
        rw [ho.out a o1 o2 (fun h' => o3 (by simp only [frameIn] at h' ⊢; omega))
          (fun h' => o3 (by simp only [slotBytes, frameIn] at h' ⊢; omega))]
        exact hout2 a o1 o2 o3⟩
  · obtain ⟨hfr', hsa', hsb'⟩ := after M' hr.out
    rw [e1]
    refine binop_ok hlive hr.h hr.den hsf176 hab176 hfr' hsa' hsb' hr.word hral R'
      (by rw [hk'.get 2 (by decide), e2]) hr.a0
      (fun R'' M'' H'' F'' L'' C'' G'' hk'' e1'' e2'' hlk'' hd'' hout'' => ?_)
      fun R'' M'' e2'' hout'' => hoom R'' M'' (sp - 112 - 16) ⟨by omega, by omega, e2'',
        fun a o1 o2 o3 _ => outW M' M'' hr.out hout'' a o1 o2 o3⟩
    rw [binop_push_some (st := st2) (g := f ((st2.push (.num na)).push (.num nb)).scale) hr.val] at hk
    refine hk R'' M'' H'' F'' L'' C'' G'' ((hk''.trans ((hk'.mono (by decide)).trans kk)))
      (by rw [e2'', h2]) (by rw [hlk'', ← hlk2]; exact hr.lkLen) hd'' (outW M' M'' hr.out hout'')
  · obtain ⟨hfr', hsa', hsb'⟩ := after M' hf.out
    rw [e1]
    refine binop_fail hlive hf.h hf.da hf.db hsf176 hab176 hfr' hsa' hsb' hral R'
      (by rw [hk'.get 2 (by decide), e2]) hf.a0
      (fun R'' M'' H'' G'' hk'' hlk'' e1'' e2'' hd'' hout'' => ?_)
      fun R'' M'' e2'' hout'' => hoom R'' M'' (sp - 112 - 64) ⟨by omega, by omega, e2'',
        fun a o1 o2 o3 _ => outW M' M'' hf.out (fun a o1 o2 o3 => hout'' a o1 o2 fun h' => o3 (by
          simp only [frameIn] at h' ⊢; omega)) a o1 o2 o3⟩
    rw [binop_push_none (st := st2) (g := f ((st2.push (.num na)).push (.num nb)).scale) hf.val] at hk
    refine hk R'' M'' H'' F' L' C' G'' ((hk''.mono (by decide)).trans ((hk'.mono (by decide)).trans kk))
      (by rw [e2'', h2]) (by rw [hlk'', ← hlk2]; exact hf.lkLen) hd''
      (outW M' M'' hf.out fun a o1 o2 o3 => hout'' a o1 o2 fun h' => o3 (by
        simp only [frameIn] at h' ⊢; omega))

end Dc.Mach
