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
  (`OpFail`), or `dc_memfail` (`OomAt`). Lost references are counted in
  `C.lk` (`BcConsts`), at most `lk` per call.
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

/-- `dc_memfail` reached from below `sp` within the window `W`: memory changed
only in the heap, dc's globals and the window. -/
structure OomAt (S : Nat → Prop) (sp W : Nat) (M0 : Mem) (sp' : Nat) (R' : Nat → BitVec 64)
    (M' : Mem) : Prop where
  lo : sp - W ≤ sp'
  hi : sp' ≤ sp
  r2 : R' 2 = BitVec.ofNat 64 sp'
  out : StkOut sp W M' M0

/-- An operation's entry: the operand handles `pa`, `pb` (denoting `na`, `nb`)
held by the caller, the scale in `a2`, the result slot `q` above the frame. -/
structure OpIn (S : Nat → Prop) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G : DcG) (hs : List GV) (st : St) (pa pb : Nat) (na nb : Num)
    (R : Nat → BitVec 64) (sp q N lk : Nat) : Prop where
  h : DcAt S M H F L C G (.num pa :: .num pb :: hs) st
  da : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb)
  hsLen : hs.length + 3 ≤ 2 ^ 30
  lkLen : C.lk.length + lk ≤ 2 ^ 29
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

/-- An operation's success: `0`, the fresh handle `y` for `r` in the slot. -/
structure OpRet (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C0 C : BcConsts) (G : DcG) (hs : List GV) (st : St) (pa pb : Nat) (na nb : Num)
    (f : Nat → Num → Num → Option Num) (R : Nat → BitVec 64) (sp q N lk y : Nat) (r : Num) :
    Prop where
  a0 : R 10 = 0#64
  h : DcAt S M H F L C G (.num y :: .num pa :: .num pb :: hs) st
  val : f st.scale na nb = some r
  den : (GV.num y).Den ⟨L, G.strs⟩ (.num r)
  word : ldv .ld M q = BitVec.ofNat 64 y
  lkLen : C.lk.length ≤ C0.lk.length + lk
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slotBytes q a → imgM M a = imgM M0 a

/-- An operation's failure: nonzero, the operands kept. -/
structure OpFail (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C0 C : BcConsts) (G : DcG) (hs : List GV) (st : St) (pa pb : Nat) (na nb : Num)
    (f : Nat → Num → Num → Option Num) (R : Nat → BitVec 64) (sp q N lk : Nat) : Prop where
  a0 : R 10 ≠ 0#64
  h : DcAt S M H F L C G (.num pa :: .num pb :: hs) st
  val : f st.scale na nb = none
  da : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb)
  lkLen : C.lk.length ≤ C0.lk.length + lk
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slotBytes q a → imgM M a = imgM M0 a

/-- **The contract of an operation at `fa`** computing `f k a b` within the
stack window `N`, losing at most `lk` references. -/
def DcOp (live S : Nat → Prop) (fa N lk : Nat) (f : Nat → Num → Num → Option Num) : Prop :=
  ∀ (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (t : String) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs : List GV) (st : St)
    (pa pb : Nat) (na nb : Num) (R : Nat → BitVec 64) (sp q : Nat),
    OpIn S M H F L C G hs st pa pb na nb R sp q N lk →
    (∀ R' M' H' F' L' C' y r, Keeps opClob R' R →
      OpRet S M M' H' F' L' C C' G hs st pa pb na nb f R' sp q N lk y r → DWO live S Q t (R 1) R' M') →
    (∀ R' M' H' F' L' C', Keeps opClob R' R →
      OpFail S M M' H' F' L' C C' G hs st pa pb na nb f R' sp q N lk → DWO live S Q t (R 1) R' M') →
    (∀ R' M' sp', OomAt S sp N M sp' R' M' → DWO live S Q t 0x80001e74#64 R' M') →
    DWO live S Q t (BitVec.ofNat 64 fa) R M

/-! ## The model -/

/-- `binop` leaves the state when the top two are not both numbers. -/
theorem binop_of_not {st : St} {f : Num → Num → Option Num}
    (h : ∀ b a rest, st.stack ≠ .num b :: .num a :: rest) : binop st f = st := by
  unfold binop
  split
  · rename_i b a rest e; exact absurd e (h b a rest)
  · rfl

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

end Dc.Mach
