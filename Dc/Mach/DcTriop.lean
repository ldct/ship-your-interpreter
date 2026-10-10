import Dc.Mach.DcBinop2

/-!
# `dc_triop` (M9)

    dc_triop (int (*op)(), int kscale):
      the checks of dc_binop over three nodes;
      dc_pop (&c); dc_pop (&b); dc_pop (&a);
      if ((*op)(a.v.number, b.v.number, c.v.number, kscale, &r.v.number) == DC_SUCCESS)
        { dc_push (r);   -- inlined
          dc_free_num (&a.v.number); dc_free_num (&b.v.number); dc_free_num (&c.v.number); }
      else { dc_push (a); dc_push (b); dc_push (c); }

The 128-byte frame keeps `dc_binop2`'s words (`B2Frame`); the inline push
stores the node's words in another order than `boPushMem` and is carried by
`DcAt.pushAgree`.

- `DcOp3`: the contract of a three-operand operation (`dc_modexp`): entry
  `OpIn3`, results `OpRet3`/`OpFail3`, `dc_memfail` through `OomAt`.
- `dc_triop_spec`: `triop st (f st.scale)`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-! ## The contract -/

/-- A three-operand operation's entry: the operand handles `pa`, `pb`, `pc`,
the scale in `a3`, the result slot `q` above the frame. -/
structure OpIn3 (S : Nat → Prop) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G : DcG) (hs : List GV) (st : St) (pa pb pc : Nat) (na nb nc : Num)
    (R : Nat → BitVec 64) (sp q N lk : Nat) : Prop where
  h : DcAt S M H F L C G (.num pa :: .num pb :: .num pc :: hs) st
  da : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb)
  dc : (GV.num pc).Den ⟨L, G.strs⟩ (.num nc)
  hsLen : hs.length + 4 ≤ 2 ^ 20
  lkLen : G.lk.length + lk ≤ 2 ^ 29
  frame : StackFrame S sp N
  above : heapEnd + N ≤ sp
  slot : PtrSlot S q
  slotHi : sp ≤ q
  r10 : R 10 = BitVec.ofNat 64 pa
  r11 : R 11 = BitVec.ofNat 64 pb
  r12 : R 12 = BitVec.ofNat 64 pc
  r13 : R 13 = BitVec.ofNat 64 st.scale
  r14 : R 14 = BitVec.ofNat 64 q
  r2 : R 2 = BitVec.ofNat 64 sp
  al : (R 1).toNat % 4 = 0
  mb : MulBase S M

/-- A three-operand operation's success: `0`, the fresh handle `y` for `r`
in the slot. -/
structure OpRet3 (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G0 G : DcG) (hs : List GV) (st : St) (pa pb pc : Nat) (na nb nc : Num)
    (f : Nat → Num → Num → Num → Option Num) (R : Nat → BitVec 64) (sp q N lk y : Nat) (r : Num) :
    Prop where
  a0 : R 10 = 0#64
  h : DcAt S M H F L C G (.num y :: .num pa :: .num pb :: .num pc :: hs) st
  val : f st.scale na nb nc = some r
  den : (GV.num y).Den ⟨L, G.strs⟩ (.num r)
  word : ldv .ld M q = BitVec.ofNat 64 y
  same : G = { G0 with lk := G.lk }
  lkLen : G.lk.length ≤ G0.lk.length + lk
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slotBytes q a → imgM M a = imgM M0 a

/-- A three-operand operation's failure: nonzero, the operands kept. -/
structure OpFail3 (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G0 G : DcG) (hs : List GV) (st : St) (pa pb pc : Nat) (na nb nc : Num)
    (f : Nat → Num → Num → Num → Option Num) (R : Nat → BitVec 64) (sp q N lk : Nat) : Prop where
  a0 : R 10 ≠ 0#64
  h : DcAt S M H F L C G (.num pa :: .num pb :: .num pc :: hs) st
  val : f st.scale na nb nc = none
  da : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb)
  dc : (GV.num pc).Den ⟨L, G.strs⟩ (.num nc)
  same : G = { G0 with lk := G.lk }
  lkLen : G.lk.length ≤ G0.lk.length + lk
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slotBytes q a → imgM M a = imgM M0 a

/-- **The contract of a three-operand operation at `fa`** computing
`f k a b c` within the stack window `N`, losing at most `lk` references. -/
def DcOp3 (live S : Nat → Prop) (fa N lk : Nat) (ok : Nat → Num → Num → Num → Prop)
    (f : Nat → Num → Num → Num → Option Num) : Prop :=
  ∀ (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (t : String) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs : List GV) (st : St)
    (pa pb pc : Nat) (na nb nc : Num) (R : Nat → BitVec 64) (sp q : Nat),
    OpIn3 S M H F L C G hs st pa pb pc na nb nc R sp q N lk → ok st.scale na nb nc →
    (∀ R' M' H' F' L' C' G' y r, Keeps opClob R' R →
      OpRet3 S M M' H' F' L' C' G G' hs st pa pb pc na nb nc f R' sp q N lk y r →
      DWO live S Q t (R 1) R' M') →
    (∀ R' M' H' F' L' C' G', Keeps opClob R' R →
      OpFail3 S M M' H' F' L' C' G G' hs st pa pb pc na nb nc f R' sp q N lk →
      DWO live S Q t (R 1) R' M') →
    (∀ R' M' sp', OomAt S sp N M (slotBytes q) sp' R' M' → DWO live S Q t 0x80001e74#64 R' M') →
    DWO live S Q t (BitVec.ofNat 64 fa) R M

/-! ## The model -/

theorem triop_of_not {st : St} {f : Num → Num → Num → Option Num}
    (h : ∀ c b a rest, st.stack ≠ .num c :: .num b :: .num a :: rest) : triop st f = st := by
  unfold triop
  split
  · rename_i c b a rest e; exact absurd e (h c b a rest)
  · rfl

theorem triop_push_some {st : St} {a b c r : Num} {g : Num → Num → Num → Option Num}
    (h : g a b c = some r) :
    triop (((st.push (.num a)).push (.num b)).push (.num c)) g = st.push (.num r) := by
  simp only [triop, St.push, h]

theorem triop_push_none {st : St} {a b c : Num} {g : Num → Num → Num → Option Num}
    (h : g a b c = none) :
    triop (((st.push (.num a)).push (.num b)).push (.num c)) g =
      ((st.push (.num a)).push (.num b)).push (.num c) := by
  simp only [triop, St.push, h]

/-! ## The checks -/

/-- A message tail of `dc_triop` (`0x80003558`: non-numeric, `0x80003574`:
stack empty): `fprintf (stderr, msg, progname)` as a tail call. -/
theorem triop_msg {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 304) (hab : heapEnd + 304 ≤ sp) {pc : BitVec 64}
    (hpc : pc = 0x80003558#64 ∨ pc = 0x80003574#64)
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

/-- `dc_triop`'s type checks (`0x8000353c`), the three nodes' payloads in
`a5`, `a4`, `a2`. -/
theorem triop_tags {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64}
    {c1 c2 c3 : Blk} {g1 g2 g3 : GV}
    (r15 : R 15 = BitVec.ofNat 64 c1.pay) (r14 : R 14 = BitVec.ofNat 64 c2.pay)
    (r12 : R 12 = BitVec.ofNat 64 c3.pay)
    (ht1 : ldv .lw M c1.pay = BitVec.ofNat 64 g1.tag) (ht2 : ldv .lw M c2.pay = BitVec.ofNat 64 g2.tag)
    (ht3 : ldv .lw M c3.pay = BitVec.ofNat 64 g3.tag)
    (hc1 : 2147603936 ≤ c1.pay ∧ c1.pay + 32 ≤ 2273312768 ∧ c1.pay % 16 = 0)
    (hc2 : 2147603936 ≤ c2.pay ∧ c2.pay + 32 ≤ 2273312768 ∧ c2.pay % 16 = 0)
    (hc3 : 2147603936 ≤ c3.pay ∧ c3.pay + 32 ≤ 2273312768 ∧ c3.pay % 16 = 0)
    (hno : (g1.tag ≠ 1 ∨ g2.tag ≠ 1 ∨ g3.tag ≠ 1) → ∀ R', Keeps [11, 12, 13, 14, 15, 17] R' R →
      DWO live S Q t 0x80003558#64 R' M)
    (hgo : g1.tag = 1 → g2.tag = 1 → g3.tag = 1 → ∀ R', Keeps [12, 14, 15, 17] R' R →
      R' 17 = 1#64 → DWO live S Q t 0x80003590#64 R' M) :
    DWO live S Q t 0x8000353c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  obtain e1 | e1 : g1.tag = 1 ∨ g1.tag = 2 := by cases g1 <;> simp [GV.tag]
  · rw [e1] at ht1
    obtain e2 | e2 : g2.tag = 1 ∨ g2.tag = 2 := by cases g2 <;> simp [GV.tag]
    · rw [e2] at ht2
      obtain e3 | e3 : g3.tag = 1 ∨ g3.tag = 2 := by cases g3 <;> simp [GV.tag]
      · rw [e3] at ht3
        bc_run hlive hS [r15, r14, r12, ht1, ht2, ht3] at 0x80003590
        all_goals try (intro hc; exact absurd hc (by decide))
        (try intro _); (try bsimp [])
        bc_run hlive hS [r15, r14, r12, ht1, ht2, ht3] at 0x80003590
        all_goals try (intro hc; exact absurd hc (by decide))
        (try intro _); (try bsimp [])
        bc_run hlive hS [r15, r14, r12, ht1, ht2, ht3] at 0x80003590
        all_goals try (intro hc; exact absurd hc (by decide))
        (try intro _); (try bsimp [])
        exact hgo e1 e2 e3 _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
      · rw [e3] at ht3
        bc_run hlive hS [r15, r14, r12, ht1, ht2, ht3] at 0x80003558
        all_goals try (intro hc; exact absurd hc (by decide))
        (try intro _); (try bsimp [])
        bc_run hlive hS [r15, r14, r12, ht1, ht2, ht3] at 0x80003558
        all_goals try (intro hc; exact absurd hc (by decide))
        (try intro _); (try bsimp [])
        bc_run hlive hS [r15, r14, r12, ht1, ht2, ht3] at 0x80003558
        all_goals try (intro hc; exact absurd hc (by decide))
        (try intro _); (try bsimp [])
        exact hno (.inr (.inr (by omega))) _ (by keeps_tac Keeps.refl _ _)
    · rw [e2] at ht2
      bc_run hlive hS [r15, r14, r12, ht1, ht2, ht3] at 0x80003558
      all_goals try (intro hc; exact absurd hc (by decide))
      (try intro _); (try bsimp [])
      bc_run hlive hS [r15, r14, r12, ht1, ht2, ht3] at 0x80003558
      all_goals try (intro hc; exact absurd hc (by decide))
      (try intro _); (try bsimp [])
      exact hno (.inr (.inl (by omega))) _ (by keeps_tac Keeps.refl _ _)
  · rw [e1] at ht1
    bc_run hlive hS [r15, r14, r12, ht1, ht2, ht3] at 0x80003558
    all_goals try (intro hc; exact absurd hc (by decide))
    (try intro _); (try bsimp [])
    exact hno (.inl (by omega)) _ (by keeps_tac Keeps.refl _ _)

/-- `dc_triop`'s checks with three nodes on the stack. -/
theorem triop_three {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64}
    {c1 c2 c3 : Blk} {g1 g2 g3 : GV}
    (h0 : ldv .ld M dcStackAddr = BitVec.ofNat 64 c1.pay)
    (h0' : ldv .ld M (c1.pay + 24) = BitVec.ofNat 64 c2.pay)
    (h0'' : ldv .ld M (c2.pay + 24) = BitVec.ofNat 64 c3.pay)
    (ht1 : ldv .lw M c1.pay = BitVec.ofNat 64 g1.tag) (ht2 : ldv .lw M c2.pay = BitVec.ofNat 64 g2.tag)
    (ht3 : ldv .lw M c3.pay = BitVec.ofNat 64 g3.tag)
    (hc1 : 2147603936 ≤ c1.pay ∧ c1.pay + 32 ≤ 2273312768 ∧ c1.pay % 16 = 0)
    (hc2 : 2147603936 ≤ c2.pay ∧ c2.pay + 32 ≤ 2273312768 ∧ c2.pay % 16 = 0)
    (hc3 : 2147603936 ≤ c3.pay ∧ c3.pay + 32 ≤ 2273312768 ∧ c3.pay % 16 = 0)
    (hG : ∀ a, DcGlob a → S a)
    (hno : (g1.tag ≠ 1 ∨ g2.tag ≠ 1 ∨ g3.tag ≠ 1) → ∀ R', Keeps [11, 12, 13, 14, 15, 17] R' R →
      DWO live S Q t 0x80003558#64 R' M)
    (hgo : g1.tag = 1 → g2.tag = 1 → g3.tag = 1 → ∀ R', Keeps [12, 14, 15, 17] R' R →
      R' 17 = 1#64 → DWO live S Q t 0x80003590#64 R' M) :
    DWO live S Q t 0x80003520#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hc0 : BitVec.ofNat 64 c1.pay ≠ 0#64 := ofNat_pos_ne (by omega) (by omega)
  have hc0' : BitVec.ofNat 64 c2.pay ≠ 0#64 := ofNat_pos_ne (by omega) (by omega)
  have hc0'' : BitVec.ofNat 64 c3.pay ≠ 0#64 := ofNat_pos_ne (by omega) (by omega)
  bc_run hlive hS [h0, h0', h0''] at 0x8000353c
  all_goals try (intro hc; exact absurd hc hc0)
  (try intro _); (try bsimp [])
  bc_run hlive hS [h0, h0', h0''] at 0x8000353c
  all_goals try (intro hc; exact absurd hc hc0')
  (try intro _); (try bsimp [])
  bc_run hlive hS [h0, h0', h0''] at 0x8000353c
  all_goals try (intro hc; exact absurd hc hc0'')
  (try intro _); (try bsimp [])
  exact triop_tags hlive hS (by bsimp []) (by bsimp []) (by bsimp []) ht1 ht2 ht3 hc1 hc2 hc3
    (fun hn R' hk => hno hn R' (hk.trans (by keeps_tac Keeps.refl _ _)))
    fun e1 e2 e3 R' hk e17 => hgo e1 e2 e3 R' (hk.trans (by keeps_tac Keeps.refl _ _)) e17

/-- **`dc_triop`'s checks** at `0x80003520`: with three numbers on top the
run goes on at `0x80003590` (`a7` the third's type `1`); otherwise one of the
two messages goes to `stderr` and `dc_triop` returns with the state kept. -/
theorem triop_entry {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 304) (hab : heapEnd + 304 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk0 : (∀ c b a rest, st.stack ≠ .num c :: .num b :: .num a :: rest) → ∀ R' M',
      Keeps fprintfClob R' R →
      (∀ a, (a < sp - 304 ∨ sp ≤ a) → imgM M' a = imgM M a) → DWO live S Q t (R 1) R' M')
    (hgo : ∀ cc cb ca pc pb pa rest,
      G.stk = (cc, .num pc) :: (cb, .num pb) :: (ca, .num pa) :: rest → ∀ R',
      Keeps [12, 14, 15, 17] R' R → R' 17 = 1#64 → DWO live S Q t 0x80003590#64 R' M) :
    DWO live S Q t 0x80003520#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hden := h.den.stk
  have hv := h.view.stk
  have hmsg : ∀ {pc : BitVec 64}, (pc = 0x80003558#64 ∨ pc = 0x80003574#64) →
      (∀ c b a rest, st.stack ≠ .num c :: .num b :: .num a :: rest) → ∀ R1,
      Keeps [11, 12, 13, 14, 15, 17] R1 R → DWO live S Q t pc R1 M := fun hpc hno R1 hk1 =>
    triop_msg hlive h hsf hab hpc R1 (by rw [hk1.get 2 (by decide), h2])
      (by rw [hk1.get 1 (by decide)]; exact hal) fun R' M' hk2 hfr => by
        rw [hk1.get 1 (by decide)]
        exact hk0 hno R' M' (hk2.trans ((hk1.mono (by decide)))) hfr
  cases hstk : G.stk with
  | nil =>
    rw [hstk] at hv hden
    have hno : ∀ c b a rest, st.stack ≠ .num c :: .num b :: .num a :: rest := fun c b a rest e => by
      rw [e] at hden; cases hden
    cases hv with
    | nil h0 =>
    bc_run hlive hS [h0] at 0x80003574
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
      have hno : ∀ c b a rest, st.stack ≠ .num c :: .num b :: .num a :: rest :=
        fun c b a rest e => by rw [e] at hden; cases hden with | cons _ hr => cases hr
      bc_run hlive hS [h0, hl0] at 0x80003574
      all_goals try (intro hc; exact absurd hc hc0)
      (try intro _); (try bsimp [])
      bc_run hlive hS [h0, hl0] at 0x80003574
      exact hmsg (.inr rfl) hno _ (by keeps_tac Keeps.refl _ _)
    | cons n2 rest2 =>
      obtain ⟨c2, g2⟩ := n2
      have hc2 := h.stkPay (c := c2) (g := g2) (by rw [hstk]; simp)
      have hc0' : BitVec.ofNat 64 c2.pay ≠ 0#64 := ofNat_pos_ne (by omega) (by omega)
      cases hl1 with
      | cons h0' hn2 hl2 =>
      cases rest2 with
      | nil =>
        cases hl2 with
        | nil hl0 =>
        have hno : ∀ c b a rest, st.stack ≠ .num c :: .num b :: .num a :: rest :=
          fun c b a rest e => by
            rw [e] at hden; cases hden with | cons _ hr => cases hr with | cons _ hr2 => cases hr2
        bc_run hlive hS [h0, h0', hl0] at 0x80003574
        all_goals try (intro hc; exact absurd hc hc0)
        (try intro _); (try bsimp [])
        bc_run hlive hS [h0, h0', hl0] at 0x80003574
        all_goals try (intro hc; exact absurd hc hc0')
        (try intro _); (try bsimp [])
        bc_run hlive hS [h0, h0', hl0] at 0x80003574
        exact hmsg (.inr rfl) hno _ (by keeps_tac Keeps.refl _ _)
      | cons n3 rest3 =>
        obtain ⟨c3, g3⟩ := n3
        have hc3 := h.stkPay (c := c3) (g := g3) (by rw [hstk]; simp)
        cases hl2 with
        | cons h0'' hn3 _ =>
        refine triop_three hlive hS h0 h0' h0'' hn1.dat.lw hn2.dat.lw hn3.dat.lw hc1 hc2 hc3 hG
          (fun hn R1 hk1 => ?_) fun e1 e2 e3 R1 hk1 e17 => ?_
        · refine hmsg (.inl rfl) (fun c b a rest e => ?_) R1 hk1
          rw [e] at hden
          cases hden with
          | cons hh hr =>
          cases hr with
          | cons hh2 hr2 =>
          cases hr2 with
          | cons hh3 _ =>
          rcases hn with hn | hn | hn
          · cases g1 with
            | num _ => exact hn rfl
            | str _ => exact hh
          · cases g2 with
            | num _ => exact hn rfl
            | str _ => exact hh2
          · cases g3 with
            | num _ => exact hn rfl
            | str _ => exact hh3
        · cases g1 with
          | str _ => simp [GV.tag] at e1
          | num pc =>
          cases g2 with
          | str _ => simp [GV.tag] at e2
          | num pb =>
          cases g3 with
          | str _ => simp [GV.tag] at e3
          | num pa => exact hgo c1 c2 c3 pc pb pa rest3 hstk R1 hk1 e17

end Dc.Mach
