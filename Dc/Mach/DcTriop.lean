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

/-! ## The pops -/

/-- The state at the call of `op`: the three operands popped into the slots
at `sp1 + 32` (`a`), `sp1 + 48` (`b`) and `sp1 + 64` (`c`), their handles
held. -/
structure T3At (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G2 : DcG) (hs : List GV) (st st2 : St) (sp W fa k : Nat) (ra : BitVec 64)
    (pa pb pc : Nat) (na nb nc : Num) : Prop where
  st : st = ((st2.push (.num na)).push (.num nb)).push (.num nc)
  h : DcAt S M H F L C G2 (.num pa :: .num pb :: .num pc :: hs) st2
  da : (GV.num pa).Den ⟨L, G2.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G2.strs⟩ (.num nb)
  dc : (GV.num pc).Den ⟨L, G2.strs⟩ (.num nc)
  fr : B2Frame M (sp - 128) fa k ra
  sa : DatAt M (sp - 128 + 32) (.num pa)
  sb : DatAt M (sp - 128 + 48) (.num pb)
  sc : DatAt M (sp - 128 + 64) (.num pc)
  out : StkOut sp W M M0

/-- **`dc_triop`'s second and third pops** (`0x800035ac` to the call of
`op`), the top `c` popped into `sp1 + 64`. -/
theorem triop_pop23 {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 M2 : Mem} {H2 : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G1 : DcG} {hs : List GV} {st1 : St}
    {pc : Nat} {nc : Num}
    (h1' : DcAt S M2 H2 F L C G1 (.num pc :: hs) st1) {sp W : Nat}
    (hsf : StackFrame S sp W) (hab : heapEnd + W ≤ sp) (hW : 464 ≤ W)
    {cb ca : Blk} {pb pa : Nat} {rest : List (Blk × GV)}
    (hstk : G1.stk = (cb, .num pb) :: (ca, .num pa) :: rest)
    (hdc : (GV.num pc).Den ⟨L, G1.strs⟩ (.num nc))
    {fa k : Nat} {ra : BitVec 64} (hfa : fa % 4 = 0) (hfa2 : fa < 2 ^ 64)
    (hfr : B2Frame M2 (sp - 128) fa k ra) (hsc : DatAt M2 (sp - 128 + 64) (.num pc))
    (hout0 : StkOut sp W M2 M0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 128)) (h1 : R 1 = 0x800035ac#64)
    (hk : ∀ R1 M3 H3 G2 st2 na nb, Keeps (1 :: 2 :: popClob) R1 R → G2.lk = G1.lk →
      G2.strs = G1.strs →
      R1 1 = 0x800035d8#64 → R1 2 = BitVec.ofNat 64 (sp - 128) → R1 10 = BitVec.ofNat 64 pa →
      R1 11 = BitVec.ofNat 64 pb → R1 12 = BitVec.ofNat 64 pc → R1 13 = BitVec.ofNat 64 k →
      R1 14 = BitVec.ofNat 64 (sp - 128 + 88) →
      T3At S M0 M3 H3 F L C G2 hs (st1.push (.num nc)) st2 sp W fa k ra pa pb pc na nb nc →
      DWO live S Q t (BitVec.ofNat 64 fa) R1 M3) :
    DWO live S Q t 0x800035ac#64 R M2 := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hslot : ∀ o, o + 16 ≤ 128 → o % 8 = 0 → DatSlot S (sp - 128) (sp - 128 + o) := fun o h1 h2 =>
    ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩
  have hS1 : HeapOwn S := fun a e1 e2 => h1'.heap.heap.own a e1 e2
  bc_run hlive hS1 [h2] at 0x8000310c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hden := h1'.den.stk
  rw [hstk] at hden
  have hne : st1.stack ≠ [] := fun e => by rw [e] at hden; cases hden
  refine dc_pop_spec hlive h1' (hsf.within (m := 128) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (hslot 48 (by omega) (by omega)) _ (by bsimp []) (by bsimp [h2])
    (by bsimp []) (fun R2 M3 H3 G2 g v st2 est eG hk2 e10 h2' hd2 hout2 => ?_)
    (fun e => absurd e hne)
  obtain ⟨c, rfl⟩ := eG
  simp only [List.cons.injEq, Prod.mk.injEq] at hstk
  obtain ⟨⟨rfl, rfl⟩, hG2⟩ := hstk
  subst est
  obtain ⟨nb, rfl, hdb⟩ := (by cases hden with | cons hh _ => exact den_num_head hh :
    ∃ nb, v = .num nb ∧ (GV.num pb).Den ⟨L, G2.strs⟩ (.num nb))
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk2.get 2 (by decide)]; bsimp [h2]
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS2 [q2] at 0x8000310c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hden2 := h2'.den.stk
  rw [hG2] at hden2
  have hne2 : st2.stack ≠ [] := fun e => by rw [e] at hden2; cases hden2
  refine dc_pop_spec hlive h2' (hsf.within (m := 128) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (hslot 32 (by omega) (by omega)) _ (by bsimp []) (by bsimp [q2])
    (by bsimp []) (fun R3 M4 H4 G3 g3 v3 st3 est3 eG3 hk3 e10' h3' hd3 hout3 => ?_)
    (fun e => absurd e hne2)
  obtain ⟨c3, rfl⟩ := eG3
  simp only [List.cons.injEq, Prod.mk.injEq] at hG2
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hG2
  subst est3
  obtain ⟨na, rfl, hda⟩ := (by cases hden2 with | cons hh _ => exact den_num_head hh :
    ∃ na, v3 = .num na ∧ (GV.num pa).Den ⟨L, G3.strs⟩ (.num na))
  have ag : ∀ a, sp - 128 ≤ a → a < sp → ¬ (sp - 128 + 32 ≤ a ∧ a < sp - 128 + 64) →
      imgM M4 a = imgM M2 a := fun a e1 e2 hn => by
    have ⟨o1, o2, o3⟩ := above_sp hab2 (a := a) e1
    rw [hout3 a o1 o2 (o3 _) (by omega), hout2 a o1 o2 (o3 _) (by omega)]
  have ag1 : ∀ a, sp - 128 ≤ a → a < sp → ¬ (sp - 128 + 32 ≤ a ∧ a < sp - 128 + 48) →
      imgM M4 a = imgM M3 a := fun a e1 e2 hn => by
    have ⟨o1, o2, o3⟩ := above_sp hab2 (a := a) e1
    exact hout3 a o1 o2 (o3 _) (by omega)
  have hfr4 : B2Frame M4 (sp - 128) fa k ra := hfr.transport fun a ha => ag a (by omega) (by omega)
    (by omega)
  have hsc4 : DatAt M4 (sp - 128 + 64) (.num pc) :=
    DatAt.congr16 (fun x e1 e2 => ag x (by omega) (by omega) (by omega)) hsc
  have hsb4 : DatAt M4 (sp - 128 + 48) (.num pb) :=
    DatAt.congr16 (fun x e1 e2 => ag1 x (by omega) (by omega) (by omega)) hd2
  have hc4 := hsc4.ptr
  have hb4 := hsb4.ptr
  have ha4 := hd3.ptr
  have q3 : R3 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
  have hS3 : HeapOwn S := fun a e1 e2 => h3'.heap.heap.own a e1 e2
  have wfa := hfr4.wfa
  have wk := hfr4.wk
  bsimp []
  have hfal : (BitVec.ofNat 64 fa).toNat % 4 = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfa2]; exact hfa
  bc_run hlive hS3 [q3, hc4, hb4, ha4, wfa, wk]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · rw [jalr_tgt _ hfal]; exact hfal
  rw [jalr_tgt _ hfal]
  refine hk _ M4 H4 G3 st3 na nb
    (by keeps_tac ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))))) rfl rfl
    (by bsimp []) (by bsimp [q3]) (by bsimp []; rfl) (by bsimp []; rfl) (by bsimp []; rfl) (by bsimp [])
    (by bsimp []) ⟨rfl, h3', hda, hdb, hdc, hfr4, hd3, hsb4, hsc4, fun a ho hg hf => ?_⟩
  have hf1 : ¬ frameIn (sp - 128) 336 a := fun h' => hf (by simp only [frameIn] at h' ⊢; omega)
  rw [hout3 a ho hg hf1 (by simp only [frameIn] at hf; omega),
    hout2 a ho hg hf1 (by simp only [frameIn] at hf; omega)]
  exact hout0 a ho hg hf

/-- **`dc_triop`'s three pops** (`0x80003590` to the call of `op`). -/
theorem triop_pops {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp W : Nat}
    (hsf : StackFrame S sp W) (hab : heapEnd + W ≤ sp) (hW : 464 ≤ W)
    {cc cb ca : Blk} {pc pb pa : Nat} {rest : List (Blk × GV)}
    (hstk : G.stk = (cc, .num pc) :: (cb, .num pb) :: (ca, .num pa) :: rest)
    {fa k : Nat} (hfa : fa % 4 = 0) (hfa2 : fa < 2 ^ 64)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 fa) (h11 : R 11 = BitVec.ofNat 64 k)
    (h17 : R 17 = 1#64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R1 M2 H2 G2 st2 na nb nc, Keeps (1 :: 2 :: popClob) R1 R → G2.lk = G.lk → G2.strs = G.strs →
      R1 1 = 0x800035d8#64 → R1 2 = BitVec.ofNat 64 (sp - 128) → R1 10 = BitVec.ofNat 64 pa →
      R1 11 = BitVec.ofNat 64 pb → R1 12 = BitVec.ofNat 64 pc → R1 13 = BitVec.ofNat 64 k →
      R1 14 = BitVec.ofNat 64 (sp - 128 + 88) →
      T3At S M M2 H2 F L C G2 hs st st2 sp W fa k (R 1) pa pb pc na nb nc →
      DWO live S Q t (BitVec.ofNat 64 fa) R1 M2) :
    DWO live S Q t 0x80003590#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  bc_run hlive hS [h2, h10, h11, h17, word_sub128 (x := sp) (by omega)] at 0x8000310c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 128) (writeLog (writeLog (writeLog (writeLog M
      [(sp - 128 + 8, 8, BitVec.ofNat 64 fa)]) [(sp - 128 + 120, 8, R 1)])
      [(sp - 128 + 16, 8, BitVec.ofNat 64 k)]) [(sp - 128 + 24, 8, 1#64)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hP : ∀ a, sp - W ≤ a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp (sp := sp - W) (by omega) ha).1, (above_sp (sp := sp - W) (by omega) ha).2.1⟩
  have h1 := h.outWrite hM1 fun a ha => hP a (by simp only [frameIn] at ha; omega)
  have hfr1 : B2Frame (writeLog (writeLog (writeLog (writeLog M
      [(sp - 128 + 8, 8, BitVec.ofNat 64 fa)]) [(sp - 128 + 120, 8, R 1)])
      [(sp - 128 + 16, 8, BitVec.ofNat 64 k)]) [(sp - 128 + 24, 8, 1#64)]) (sp - 128) fa k (R 1) :=
    ⟨by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit],
     by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit],
     by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit],
     by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]⟩
  have hslot : DatSlot S (sp - 128) (sp - 128 + 64) :=
    ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩
  have hden := h.den.stk
  rw [hstk] at hden
  have hne : st.stack ≠ [] := fun e => by rw [e] at hden; cases hden
  refine dc_pop_spec hlive h1 (hsf.within (m := 128) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd]; omega) hslot _ (by bsimp []) (by bsimp [])
    (by bsimp []) (fun R2 M2 H2 G1 g v st1 est eG hk2 e10 h1' hd1 hout1 => ?_)
    (fun e => absurd e hne)
  obtain ⟨c, rfl⟩ := eG
  simp only [List.cons.injEq, Prod.mk.injEq] at hstk
  obtain ⟨⟨rfl, rfl⟩, hG1⟩ := hstk
  subst est
  obtain ⟨nc, rfl, hdc⟩ := (by cases hden with | cons hh _ => exact den_num_head hh :
    ∃ nc, v = .num nc ∧ (GV.num pc).Den ⟨L, G1.strs⟩ (.num nc))
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hfr2 : B2Frame M2 (sp - 128) fa k (R 1) := hfr1.transport fun a ha => by
    have ⟨o1, o2, o3⟩ := above_sp hab2 (a := a) (by omega)
    exact hout1 a o1 o2 (o3 _) (by omega)
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk2.get 2 (by decide)]; bsimp []
  bsimp []
  refine triop_pop23 hlive h1' hsf hab hW hG1 hdc hfa hfa2 hfr2 hd1 (fun a ho hg hf => ?_) R2 q2
    (by rw [hk2.get 1 (by decide)]; bsimp [])
    fun R1 M3 H3 G2 st2 na nb hk1 hlk hstr e1 e2 e10 e11 e12 e13 e14 hb =>
      hk R1 M3 H3 G2 st2 na nb nc
        ((hk1.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
          (by keeps_tac Keeps.refl _ _)))) hlk hstr e1 e2 e10 e11 e12 e13 e14 hb
  have hf1 : ¬ frameIn (sp - 128) 336 a := fun h' => hf (by simp only [frameIn] at h' ⊢; omega)
  rw [hout1 a ho hg hf1 (by simp only [frameIn] at hf; omega)]
  exact hM1 a fun h' => hf (by simp only [frameIn] at h' ⊢; omega)

/-! ## After `op` -/

/-- **`op` failed** (`0x800035d8`, `a0 ≠ 0`): `a`, `b`, `c` pushed back, the
state as before the pops. -/
theorem triop_fail {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb pc : Nat} {na nb nc : Num} (h : DcAt S M H F L C G (.num pa :: .num pb :: .num pc :: hs) st)
    (hda : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)) (hdb : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb))
    (hdc : (GV.num pc).Den ⟨L, G.strs⟩ (.num nc))
    {sp fa k : Nat} {ra : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hfr : B2Frame M (sp - 128) fa k ra) (hsa : DatAt M (sp - 128 + 32) (.num pa))
    (hsb : DatAt M (sp - 128 + 48) (.num pb)) (hsc : DatAt M (sp - 128 + 64) (.num pc))
    (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 128)) (h10 : R 10 ≠ 0#64)
    (hk : ∀ R' M' H' G', Keeps (1 :: 2 :: pushClob) R' R → G'.lk = G.lk → G'.strs = G.strs → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp →
      DcAt S M' H' F L C G' hs (((st.push (.num na)).push (.num nb)).push (.num nc)) →
      StkOut (sp - 128) 64 M' M → DWO live S Q t ra R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128 - 64) → StkOut (sp - 128) 64 M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x800035d8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hfs : StackFrame S (sp - 128) 64 := hsf.within (by omega) (by decide)
  have wa0 := hsa.ptr
  refine st_800035d8 hlive (fun hc => absurd hc h10) fun _ => ?_
  bc_run hlive hS [h2, wa0] at 0x80002da4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have habv : ∀ a, sp - 128 ≤ a → ∀ M1 : Mem, StkOut (sp - 128) 64 M1 M → imgM M1 a = imgM M a :=
    fun a ha M1 ho => by
      have ⟨o1, o2, o3⟩ := above_sp hab2 ha
      exact ho a o1 o2 (o3 _)
  refine dc_push_spec hlive h hda hfs (by simp only [heapEnd]; omega) _ ⟨by bsimp []; exact hsa.tag,
    by bsimp []⟩ (by bsimp [h2]) (by bsimp [])
    (fun R1 M1 H1 c1 hk1 h1 hout1 => ?_) (fun R1 M1 e2 hout1 => hoom R1 M1 e2 hout1)
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
  have wb0 : ldv .ld M1 (sp - 128 + 48) = ldv .ld M (sp - 128 + 48) :=
    ldv_congr .ld fun j hj => habv _ (by omega) _ hout1
  have wb1 : ldv .ld M1 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => habv _ (by omega) _ hout1]; exact hsb.ptr
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS1 [q1, wb0, wb1] at 0x80002da4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_push_spec hlive h1 hdb hfs (by simp only [heapEnd]; omega) _ ⟨by bsimp []; exact hsb.tag,
    by bsimp []; rfl⟩ (by bsimp [q1]) (by bsimp [])
    (fun R2 M2 H2 c2 hk2 h2' hout2 => ?_) (fun R2 M2 e2 hout2 => hoom R2 M2 e2 fun a o1 o2 o3 => by
      rw [hout2 a o1 o2 o3, hout1 a o1 o2 o3])
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk2.get 2 (by decide)]; bsimp [q1]
  have out12 : StkOut (sp - 128) 64 M2 M := fun a o1 o2 o3 => by
    rw [hout2 a o1 o2 o3, hout1 a o1 o2 o3]
  have wc0 : ldv .ld M2 (sp - 128 + 64) = ldv .ld M (sp - 128 + 64) :=
    ldv_congr .ld fun j hj => habv _ (by omega) _ out12
  have wc1 : ldv .ld M2 (sp - 128 + 64 + 8) = BitVec.ofNat 64 pc := by
    rw [ldv_congr .ld fun j hj => habv _ (by omega) _ out12]; exact hsc.ptr
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS2 [q2, wc0, wc1] at 0x80002da4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_push_spec hlive h2' hdc hfs (by simp only [heapEnd]; omega) _ ⟨by bsimp []; exact hsc.tag,
    by bsimp []; rfl⟩ (by bsimp [q2]) (by bsimp [])
    (fun R3 M3 H3 c3 hk3 h3' hout3 => ?_) (fun R3 M3 e2 hout3 => hoom R3 M3 e2 fun a o1 o2 o3 => by
      rw [hout3 a o1 o2 o3, out12 a o1 o2 o3])
  have q3 : R3 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
  have out3 : StkOut (sp - 128) 64 M3 M := fun a o1 o2 o3 => by
    rw [hout3 a o1 o2 o3, out12 a o1 o2 o3]
  have wra3 : ldv .ld M3 (sp - 128 + 120) = ra := by
    rw [ldv_congr .ld fun j hj => habv _ (by omega) _ out3]; exact hfr.wra
  have hS3 : HeapOwn S := fun a e1 e2 => h3'.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS3 [q3, wra3]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hral
  refine hk _ M3 H3 { G with stk := (c3, .num pc) :: (c2, .num pb) :: (c1, .num pa) :: G.stk }
    (by keeps_tac ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
      (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))))) rfl rfl
    (by bsimp []) (by bsimp [q3]; rw [show sp - 128 + 128 = sp by omega]) h3' out3

/-- **The last two operand frees and the return** (`0x8000365c` onward):
free the slots at `sp1 + 56` (`b`) and `sp1 + 72` (`c`), reload `ra`,
return. -/
theorem triop_frees23 {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M3 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pb pc : Nat}
    (h3 : DcAt S M3 H F L C G (.num pb :: .num pc :: hs) st)
    {sp : Nat} {ra : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hwb : ldv .ld M3 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb)
    (hwc : ldv .ld M3 (sp - 128 + 64 + 8) = BitVec.ofNat 64 pc)
    (hwr : ldv .ld M3 (sp - 128 + 120) = ra) (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (q1 : R 2 = BitVec.ofNat 64 (sp - 128)) (h1 : R 1 = 0x8000365c#64)
    (hk : ∀ R' M' H' F' L' C', Keeps (1 :: 2 :: freeNumClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DcAt S M' H' F' L' C' G hs st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M3 a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x8000365c#64 R M3 := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hsf32 : StackFrame S (sp - 128) 32 := hsf.within (by omega) (by decide)
  have hS3 : HeapOwn S := fun a e1 e2 => h3.heap.heap.own a e1 e2
  bc_run hlive hS3 [q1] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_free_num_spec hlive h3 (q := sp - 128 + 48 + 8) (hsf.slot (by omega) (by omega) (by omega))
    (by omega) hwb hsf32 (by omega) (Or.inr (by omega)) _ (by bsimp []) (by bsimp [q1]) (by bsimp [])
    (fun R4 M4 H4 F4 L4 C4 hk4 h4 _ hout4 => ?_)
  have ag4 : ∀ a, sp - 128 ≤ a → ¬ slotBytes (sp - 128 + 48 + 8) a → imgM M4 a = imgM M3 a :=
    fun a ha hn => hout4 a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 32) hn
  have q4 : R4 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk4.get 2 (by decide)]; bsimp [q1]
  have hwc4 : ldv .ld M4 (sp - 128 + 64 + 8) = BitVec.ofNat 64 pc := by
    rw [ldv_congr .ld fun j hj => ag4 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)]
    exact hwc
  have hS4 : HeapOwn S := fun a e1 e2 => h4.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS4 [q4] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_free_num_spec hlive h4 (q := sp - 128 + 64 + 8) (hsf.slot (by omega) (by omega) (by omega))
    (by omega) hwc4 hsf32 (by omega) (Or.inr (by omega)) _ (by bsimp []) (by bsimp [q4]) (by bsimp [])
    (fun R5 M5 H5 F5 L5 C5 hk5 h5 _ hout5 => ?_)
  have ag5 : ∀ a, sp - 128 ≤ a → ¬ slotBytes (sp - 128 + 64 + 8) a → imgM M5 a = imgM M4 a :=
    fun a ha hn => hout5 a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 32) hn
  have q5 : R5 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk5.get 2 (by decide)]; bsimp [q4]
  have hwr5 : ldv .ld M5 (sp - 128 + 120) = ra := by
    rw [ldv_congr .ld fun j hj => ag5 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega),
      ldv_congr .ld fun j hj => ag4 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)]
    exact hwr
  have hS5 : HeapOwn S := fun a e1 e2 => h5.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS5 [q5, hwr5]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hral
  refine hk _ M5 H5 F5 L5 C5 (by keeps_tac ((hk5.mono (by decide)).trans (by keeps_tac ((hk4.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))))) (by bsimp []) (by bsimp [q5]; rw [show sp - 128 + 128 = sp by omega]) h5
    fun a ho hg hf => by
      have e5 := hout5 a ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
        (fun hs' => hf (by simp only [frameIn, slotBytes] at hs' ⊢; omega))
      have e4 := hout4 a ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
        (fun hs' => hf (by simp only [frameIn, slotBytes] at hs' ⊢; omega))
      rw [e5, e4]

/-- **The operand frees and the return** after the inline push (`0x80003654`
onward): free the slots at `sp1 + 40` (`a`), `sp1 + 56` (`b`), `sp1 + 72`
(`c`), reload `ra`, return. -/
theorem triop_frees {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M3 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pa pb pc : Nat}
    (h3 : DcAt S M3 H F L C G (.num pa :: .num pb :: .num pc :: hs) st)
    {sp : Nat} {ra : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hwa : ldv .ld M3 (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa)
    (hwb : ldv .ld M3 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb)
    (hwc : ldv .ld M3 (sp - 128 + 64 + 8) = BitVec.ofNat 64 pc)
    (hwr : ldv .ld M3 (sp - 128 + 120) = ra) (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (q1 : R 2 = BitVec.ofNat 64 (sp - 128))
    (h10 : R 10 = BitVec.ofNat 64 (sp - 128 + 32 + 8)) (h1 : R 1 = 0x8000365c#64)
    (hk : ∀ R' M' H' F' L' C', Keeps (1 :: 2 :: freeNumClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DcAt S M' H' F' L' C' G hs st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M3 a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x80002ba0#64 R M3 := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hsf32 : StackFrame S (sp - 128) 32 := hsf.within (by omega) (by decide)
  refine dc_free_num_spec hlive h3 (q := sp - 128 + 32 + 8) (hsf.slot (by omega) (by omega) (by omega))
    (by omega) hwa hsf32 (by omega) (Or.inr (by omega)) _ h10 q1 (by rw [h1]; decide)
    (fun R4 M4 H4 F4 L4 C4 hk4 h4 _ hout4 => ?_)
  have ag4 : ∀ a, sp - 128 ≤ a → ¬ slotBytes (sp - 128 + 32 + 8) a → imgM M4 a = imgM M3 a :=
    fun a ha hn => hout4 a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 32) hn
  have q4 : R4 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk4.get 2 (by decide)]; bsimp [q1]
  have l : ∀ o, 48 ≤ o → o + 8 ≤ 128 → ldv .ld M4 (sp - 128 + o) = ldv .ld M3 (sp - 128 + o) :=
    fun o e1 e2 => ldv_congr .ld fun j hj =>
      ag4 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
  rw [h1]
  refine triop_frees23 hlive h4 hsf hab (by rw [show sp - 128 + 48 + 8 = sp - 128 + 56 by omega,
      l 56 (by omega) (by omega), ← show sp - 128 + 48 + 8 = sp - 128 + 56 by omega]; exact hwb)
    (by rw [show sp - 128 + 64 + 8 = sp - 128 + 72 by omega, l 72 (by omega) (by omega),
      ← show sp - 128 + 64 + 8 = sp - 128 + 72 by omega]; exact hwc)
    (by rw [l 120 (by omega) (by omega)]; exact hwr) hral R4 q4 (by rw [hk4.get 1 (by decide), h1])
    fun R' M' H' F' L' C' hk' e1 e2 h' hout' => hk R' M' H' F' L' C'
      ((hk'.mono (by decide)).trans (hk4.mono (by decide))) e1 e2 h' fun a ho hg hf => by
        rw [hout' a ho hg hf]
        exact hout4 a ho hg (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
          (fun hs' => hf (by simp only [frameIn, slotBytes] at hs' ⊢; omega))

/-- **The inline push** (after `dc_malloc` at `0x80003628` returns): the
result's handle `y` (frame words `sp1 + 96`, `sp1 + 104`) stored into the
fresh node in another order than `boPushMem` (`DcAt.pushAgree`), then the
three operands freed. -/
theorem triop_push {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M1 M2 : Mem} {H H2 : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb pc y sp : Nat} {r : Num} {b : Blk}
    (h1 : DcAt S M1 H F L C G (.num y :: .num pa :: .num pb :: .num pc :: hs) st)
    (hp : DcMallocPost S M1 M2 H H2 32 (sp - 128) b)
    (hdy : (GV.num y).Den ⟨L, G.strs⟩ (.num r))
    {ra w0 : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hwa : ldv .ld M1 (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa)
    (hwb : ldv .ld M1 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb)
    (hwc : ldv .ld M1 (sp - 128 + 64 + 8) = BitVec.ofNat 64 pc)
    (hwr : ldv .ld M1 (sp - 128 + 120) = ra) (hral : ra.toNat % 4 = 0)
    (l96 : ldv .ld M1 (sp - 128 + 96) = w0) (l104 : ldv .ld M1 (sp - 128 + 104) = BitVec.ofNat 64 y)
    (hd : DatRegs w0 (BitVec.ofNat 64 y) (.num y))
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 128)) (h10 : R 10 = BitVec.ofNat 64 b.pay)
    (h1r : R 1 = 0x8000362c#64)
    (hk : ∀ R' M' H' F' L' C' (G' : DcG), Keeps (1 :: 2 :: opClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → G'.lk = G.lk → G'.strs = G.strs → DcAt S M' H' F' L' C' G' hs (st.push (.num r)) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M1 a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x8000362c#64 R M2 := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hi1 := h1.heap.heap
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
  have ag2 : ∀ a, sp - 128 ≤ a → imgM M2 a = imgM M1 a := fun a ha =>
    hp.frame a (OutHeap.not_alloc hi1 (above_sp hab2 ha).1) fun hf => by
      simp only [frameIn] at hf; omega
  have l96' : ldv .ld M2 (sp - 128 + 96) = w0 := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega)]; exact l96
  have l104' : ldv .ld M2 (sp - 128 + 104) = BitVec.ofNat 64 y := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega)]; exact l104
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  have hG2 := h2'.glob
  generalize hold : ldv .ld M2 dcStackAddr = old
  have m0 : ldv .ld M2 2147601816 = old := hold
  bc_run hlive hS2 [h2, h10, l96', l104', m0] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals try (intro x hx; have hx' := VsaIris.Sym.of_mem_accAddrs hx; exact hG2 x (by simp only [DcGlob, dc_addrs] at hx' ⊢; omega))
  all_goals try (show StOK _ _; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)
  generalize hMx : writeLog (writeLog (writeLog (writeLog (writeLog M2
      [(b.pay + 24, 8, old)]) [(b.pay, 8, w0)]) [(b.pay + 8, 8, BitVec.ofNat 64 y)])
      [(2147601816, 8, BitVec.ofNat 64 b.pay)]) [(b.pay + 16, 8, 0#64)] = Mx
  have hds : dcStackAddr = 2147601816 := rfl
  have hag : ∀ a, ¬ (fun _ => False) a →
      imgM Mx a = imgM (boPushMem M2 b.pay w0 (BitVec.ofNat 64 y)) a := by
    intro a _
    rw [← hMx, boPushMem, hold, hds]
    by_cases c1 : b.pay ≤ a ∧ a < b.pay + 8
    · simp (disch := omega) only [imgM_store_miss]; exact imgM_store_same _ _ _ (.inr rfl) c1
    by_cases c2 : b.pay + 8 ≤ a ∧ a < b.pay + 8 + 8
    · simp (disch := omega) only [imgM_store_miss]; exact imgM_store_same _ _ _ (.inr rfl) c2
    by_cases c3 : b.pay + 16 ≤ a ∧ a < b.pay + 16 + 8
    · simp (disch := omega) only [imgM_store_miss]; exact imgM_store_same _ _ _ (.inr rfl) c3
    by_cases c4 : b.pay + 24 ≤ a ∧ a < b.pay + 24 + 8
    · simp (disch := omega) only [imgM_store_miss]; exact imgM_store_same _ _ _ (.inr rfl) c4
    by_cases c5 : 2147601816 ≤ a ∧ a < 2147601816 + 8
    · simp (disch := omega) only [imgM_store_miss]; exact imgM_store_same _ _ _ (.inr rfl) c5
    simp (disch := omega) only [imgM_store_miss]
  obtain ⟨h4, hm4⟩ := DcAt.pushAgree h2' hfresh hdy hd hbsz hpl1 (fun _ hf => hf.elim) hag
  have agx : ∀ a, sp - 128 ≤ a → imgM Mx a = imgM M1 a := fun a ha => by
    rw [hm4 a fun hb => by
      rcases hb with hb | hb | hb
      · simp only [Blk.In, Blk.pay, Blk.fin] at hb hbhi; omega
      · simp only [StkWord, hds] at hb; omega
      · exact hb]
    exact ag2 a ha
  have hwa4 : ldv .ld Mx (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa := by
    rw [ldv_congr .ld fun j hj => agx _ (by omega)]; exact hwa
  have hwb4 : ldv .ld Mx (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => agx _ (by omega)]; exact hwb
  have hwc4 : ldv .ld Mx (sp - 128 + 64 + 8) = BitVec.ofNat 64 pc := by
    rw [ldv_congr .ld fun j hj => agx _ (by omega)]; exact hwc
  have hwr4 : ldv .ld Mx (sp - 128 + 120) = ra := by
    rw [ldv_congr .ld fun j hj => agx _ (by omega)]; exact hwr
  exact triop_frees hlive h4 hsf hab hwa4 hwb4 hwc4 hwr4 hral _ (by bsimp [h2]) (by bsimp [h2])
    (by bsimp [])
    fun R' M' H' F' L' C' hk' e1 e2 h' hout' => hk R' M' H' F' L' C' { G with stk := (b, .num y) :: G.stk }
      (by keeps_tac ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) e1 e2 rfl rfl h'
      fun a ho hg hf => by
        rw [hout' a ho hg hf, hm4 a (fun hb => by
          rcases hb with hb | hb | hb
          · simp only [Blk.In, Blk.pay, Blk.fin] at hb hbhi hpl1; simp only [OutHeap, heapStart, heapEnd] at ho; omega
          · exact hg (by simp only [StkWord, DcGlob, dc_addrs] at hb ⊢; omega)
          · exact hb)]
        exact hp.frame a (OutHeap.not_alloc hi1 ho) fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)

/-- **`op` succeeded** (`0x800035d8`, `a0 = 0`): the result handle `y`
(denoting `r`) pushed inline, then the three operand handles freed. -/
theorem triop_ok {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb pc y : Nat} {r : Num}
    (h : DcAt S M H F L C G (.num y :: .num pa :: .num pb :: .num pc :: hs) st)
    (hdy : (GV.num y).Den ⟨L, G.strs⟩ (.num r))
    {sp fa k : Nat} {ra : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hfr : B2Frame M (sp - 128) fa k ra) (hsa : DatAt M (sp - 128 + 32) (.num pa))
    (hsb : DatAt M (sp - 128 + 48) (.num pb)) (hsc : DatAt M (sp - 128 + 64) (.num pc))
    (hy : ldv .ld M (sp - 128 + 88) = BitVec.ofNat 64 y) (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 128)) (h10 : R 10 = 0#64)
    (hk : ∀ R' M' H' F' L' C' (G' : DcG), Keeps (1 :: 2 :: opClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → G'.lk = G.lk → G'.strs = G.strs → DcAt S M' H' F' L' C' G' hs (st.push (.num r)) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M a) →
      DWO live S Q t ra R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128 - 16) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M a) →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x800035d8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  refine st_800035d8 hlive (fun _ => ?_) fun hc => absurd h10 hc
  have wtag := hfr.wtag
  bc_run hlive hS [h2, wtag, hy] at 0x80001ea0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hw0 := ld_lo32_sw M (sp - 128 + 80) 1#64
  generalize ldv .ld (writeLog M [(sp - 128 + 80, 4, 1#64)]) (sp - 128 + 80) = w0 at hw0 ⊢
  have hM1 : MemOnly (fun a => (sp - 128 + 80 ≤ a ∧ a < sp - 128 + 84) ∨
      (sp - 128 + 96 ≤ a ∧ a < sp - 128 + 112))
      (writeLog (writeLog (writeLog M [(sp - 128 + 80, 4, 1#64)])
        [(sp - 128 + 104, 8, BitVec.ofNat 64 y)]) [(sp - 128 + 96, 8, w0)]) M := fun a ha => by
    simp only [not_or] at ha
    repeat rw [imgM_store_miss _ _ (by omega)]
  have l96 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 128 + 80, 4, 1#64)])
      [(sp - 128 + 104, 8, BitVec.ofNat 64 y)]) [(sp - 128 + 96, 8, w0)]) (sp - 128 + 96) = w0 :=
    ldv_store_hit _ _ _
  have l104 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 128 + 80, 4, 1#64)])
      [(sp - 128 + 104, 8, BitVec.ofNat 64 y)]) [(sp - 128 + 96, 8, w0)]) (sp - 128 + 104) =
      BitVec.ofNat 64 y := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize (writeLog (writeLog (writeLog M [(sp - 128 + 80, 4, 1#64)])
      [(sp - 128 + 104, 8, BitVec.ofNat 64 y)]) [(sp - 128 + 96, 8, w0)]) = M1 at hM1 l96 l104 ⊢
  have ag1 : ∀ a, sp - 128 ≤ a → ¬ ((sp - 128 + 80 ≤ a ∧ a < sp - 128 + 84) ∨
      (sp - 128 + 96 ≤ a ∧ a < sp - 128 + 112)) → imgM M1 a = imgM M a := fun a _ hn => hM1 a hn
  have h1 := h.outWrite hM1 fun a ha => ⟨(above_sp hab2 (a := a) (by omega)).1,
    (above_sp hab2 (a := a) (by omega)).2.1⟩
  have hi1 := h1.heap.heap
  have hwa : ldv .ld M1 (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa := by
    rw [ldv_congr .ld fun j hj => ag1 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hsa.ptr
  have hwb : ldv .ld M1 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => ag1 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hsb.ptr
  have hwc : ldv .ld M1 (sp - 128 + 64 + 8) = BitVec.ofNat 64 pc := by
    rw [ldv_congr .ld fun j hj => ag1 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hsc.ptr
  have hwr : ldv .ld M1 (sp - 128 + 120) = ra := by
    rw [ldv_congr .ld fun j hj => ag1 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hfr.wra
  have out1 : ∀ M' : Mem, (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M1 a) →
      ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M a := fun M' ho a o1 o2 o3 => by
    rw [ho a o1 o2 o3]
    exact hM1 a fun ha => o3 (by simp only [frameIn]; omega)
  refine dc_malloc_spec hlive hi1 (n := 32) (sp := sp - 128) (by omega)
    (hsf.within (m := 128) (n := 16) (by omega) (by decide)) (by simp only [heapEnd]; omega) _
    (by bsimp []) (by bsimp [h2]) (by bsimp []) (fun R1 M2 H2 b hk1 hp hr10 => ?_)
    (fun R1 M2 hr2 hfr2 => ?_)
  rotate_left
  · refine hoom R1 M2 hr2 (out1 M2 fun a ho hg hf => ?_)
    exact hfr2 a (OutHeap.not_alloc hi1 ho) (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
  have e1 : R1 1 = 0x8000362c#64 := by rw [hk1.get 1 (by decide)]; bsimp []
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
  bsimp []
  exact triop_push hlive h1 hp hdy hsf hab hwa hwb hwc hwr hral l96 l104 ⟨by rw [hw0]; rfl, rfl⟩
    R1 q1 hr10 e1
    (fun R' M' H' F' L' C' G' hk' e1' e2 elk estr h' hout' => hk R' M' H' F' L' C' G'
      ((hk'.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))
      e1' e2 elk estr h' (out1 M' hout'))

/-! ## `dc_triop` -/

/-- **`dc_triop (op, kscale)`** at `0x80003520` with `op` meeting `DcOp3 … f`:
the state becomes `triop st (f st.scale)`, losing at most `lk` references. -/
theorem dc_triop_spec {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {fa N lk : Nat}
    {f : Nat → Num → Num → Num → Option Num}
    {ok : Nat → Num → Num → Num → Prop} (hop : DcOp3 live S fa N lk ok f) (hfa : fa % 4 = 0)
    (hfa2 : fa < 2 ^ 64)
    {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV}
    {st : St} (h : DcAt S M H F L C G hs st)
    (hok : ∀ c b a rest, st.stack = .num c :: .num b :: .num a :: rest → ok st.scale a b c)
    (hsLen : hs.length + 4 ≤ 2 ^ 20) (hmb : MulBase S M)
    (hlk : G.lk.length + lk ≤ 2 ^ 29) {sp W : Nat} (hsf : StackFrame S sp W) (hab : heapEnd + W ≤ sp)
    (hW : 464 ≤ W) (hN : 128 + N ≤ W)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 fa) (h11 : R 11 = BitVec.ofNat 64 st.scale)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps (1 :: 2 :: opClob) R' R → R' 2 = R 2 →
      G'.lk.length ≤ G.lk.length + lk → G'.strs = G.strs → DcAt S M' H' F' L' C' G' hs (triop st (f st.scale)) →
      StkOut sp W M' M → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp W M (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80003520#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by simp only [heapEnd]; omega
  have hab176 : heapEnd + 192 ≤ sp := by simp only [heapEnd]; omega
  have hsf176 := hsf.mono (n := 192) (by omega)
  refine triop_entry hlive h (hsf.mono (by omega)) (by simp only [heapEnd]; omega) R h2 hal
    (fun hno R' M' hk' hout' => hk R' M' H F L C G (hk'.mono (by decide)) (hk'.get 2 (by decide))
      (by omega) rfl (by
        rw [triop_of_not hno]
        exact h.outWrite (P := frameIn sp 304) (fun a ha => hout' a (by simp only [frameIn] at ha; omega))
          fun a ha => ⟨(above_sp (sp := sp - 304) (by simp only [heapEnd]; omega) ha.1).1,
            (above_sp (sp := sp - 304) (by simp only [heapEnd]; omega) ha.1).2.1⟩)
      fun a ho hg hf => hout' a (by simp only [frameIn] at hf; omega))
    fun cc cb ca pc pb pa rest hstk R0 hk0 e17 => ?_
  have r01 : R0 1 = R 1 := hk0.get 1 (by decide)
  refine triop_pops hlive h hsf hab hW hstk hfa hfa2 R0 (by rw [hk0.get 10 (by decide), h10])
    (by rw [hk0.get 11 (by decide), h11]) e17 (by rw [hk0.get 2 (by decide), h2]) (by rw [r01]; exact hal)
    fun R1 M2 H2 G2 st2 na nb nc hk1 hlk2 hstr2 e1 e2 e10 e11 e12 e13 e14 hb => ?_
  obtain ⟨est, h2', hda, hdb, hdc, hfr, hsa, hsb, hsc, hout2⟩ := hb
  subst est
  rw [r01] at hfr
  have hral : (R 1).toNat % 4 = 0 := hal
  have kk : Keeps (1 :: 2 :: opClob) R1 R :=
    (hk1.mono (by decide)).trans (hk0.mono (by decide))
  -- what the operation leaves of the caller's frame words
  have after : ∀ M' : Mem, (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn (sp - 128) N a →
      ¬ slotBytes (sp - 128 + 88) a → imgM M' a = imgM M2 a) →
      B2Frame M' (sp - 128) fa st2.scale (R 1) ∧ DatAt M' (sp - 128 + 32) (.num pa) ∧
        DatAt M' (sp - 128 + 48) (.num pb) ∧ DatAt M' (sp - 128 + 64) (.num pc) := fun M' ho => by
    have ag : ∀ a, sp - 128 ≤ a → ¬ slotBytes (sp - 128 + 88) a → imgM M' a = imgM M2 a :=
      fun a ha hn => ho a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 N) hn
    refine ⟨hfr.transport fun a ha => ag a (by omega) (by simp only [slotBytes]; omega),
      DatAt.congr16 (fun x h1 h2 => ag x (by omega) (by simp only [slotBytes]; omega)) hsa,
      DatAt.congr16 (fun x h1 h2 => ag x (by omega) (by simp only [slotBytes]; omega)) hsb,
      DatAt.congr16 (fun x h1 h2 => ag x (by omega) (by simp only [slotBytes]; omega)) hsc⟩
  have outW : ∀ M' M'' : Mem, (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn (sp - 128) N a →
      ¬ slotBytes (sp - 128 + 88) a → imgM M' a = imgM M2 a) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M'' a = imgM M' a) →
      StkOut sp W M'' M := fun M' M'' o1 o2 a ho hg hf => by
    rw [o2 a ho hg (fun h' => hf (by simp only [frameIn] at h' ⊢; omega)),
      o1 a ho hg (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))
        (fun h' => hf (by simp only [slotBytes, frameIn] at h' ⊢; omega))]
    exact hout2 a ho hg hf
  refine hop Q t M2 H2 F L C G2 hs st2 pa pb pc na nb nc R1 (sp - 128) (sp - 128 + 88)
    ⟨h2', hda, hdb, hdc, hsLen, by rw [hlk2]; exact hlk, hsf.within hN (by decide),
      by simp only [heapEnd]; omega, hsf.slot (by omega) (by omega) (by omega), by omega,
      e10, e11, e12, e13, e14, e2, by rw [e1]; decide, hmb.transport fun a e1 e2 => by
        have ⟨o1, o2, o3⟩ := mulBase_off e1 e2
        exact hout2 a o1 o2 fun hf => by simp only [frameIn, heapStart] at hf o3; omega⟩
    (hok nc nb na st2.stack rfl)
    (fun R' M' H' F' L' C' G' y r hk' hr => ?_) (fun R' M' H' F' L' C' G' hk' hf => ?_)
    fun R' M' sp' ho => hoom R' M' sp' ⟨by have := ho.lo; omega, by have := ho.hi; omega, ho.r2,
      fun a o1 o2 o3 _ => by
        rw [ho.out a o1 o2 (fun h' => o3 (by simp only [frameIn] at h' ⊢; omega))
          (fun h' => o3 (by simp only [slotBytes, frameIn] at h' ⊢; omega))]
        exact hout2 a o1 o2 o3⟩
  · obtain ⟨hfr', hsa', hsb', hsc'⟩ := after M' hr.out
    rw [e1]
    refine triop_ok hlive hr.h hr.den hsf176 hab176 hfr' hsa' hsb' hsc' hr.word hral R'
      (by rw [hk'.get 2 (by decide), e2]) hr.a0
      (fun R'' M'' H'' F'' L'' C'' G'' hk'' e1'' e2'' hlk'' hs'' hd'' hout'' => ?_)
      fun R'' M'' e2'' hout'' => hoom R'' M'' (sp - 128 - 16) ⟨by omega, by omega, e2'',
        fun a o1 o2 o3 _ => outW M' M'' hr.out hout'' a o1 o2 o3⟩
    rw [triop_push_some (st := st2)
      (g := f (((st2.push (.num na)).push (.num nb)).push (.num nc)).scale) hr.val] at hk
    refine hk R'' M'' H'' F'' L'' C'' G'' ((hk''.trans ((hk'.mono (by decide)).trans kk)))
      (by rw [e2'', h2]) (by rw [hlk'', ← hlk2]; exact hr.lkLen)
      (hs''.trans ((congrArg DcG.strs hr.same).trans hstr2)) hd'' (outW M' M'' hr.out hout'')
  · obtain ⟨hfr', hsa', hsb', hsc'⟩ := after M' hf.out
    rw [e1]
    refine triop_fail hlive hf.h hf.da hf.db hf.dc hsf176 hab176 hfr' hsa' hsb' hsc' hral R'
      (by rw [hk'.get 2 (by decide), e2]) hf.a0
      (fun R'' M'' H'' G'' hk'' hlk'' hs'' e1'' e2'' hd'' hout'' => ?_)
      fun R'' M'' e2'' hout'' => hoom R'' M'' (sp - 128 - 64) ⟨by omega, by omega, e2'',
        fun a o1 o2 o3 _ => outW M' M'' hf.out (fun a o1 o2 o3 => hout'' a o1 o2 fun h' => o3 (by
          simp only [frameIn] at h' ⊢; omega)) a o1 o2 o3⟩
    rw [triop_push_none (st := st2)
      (g := f (((st2.push (.num na)).push (.num nb)).push (.num nc)).scale) hf.val] at hk
    refine hk R'' M'' H'' F' L' C' G'' ((hk''.mono (by decide)).trans ((hk'.mono (by decide)).trans kk))
      (by rw [e2'', h2]) (by rw [hlk'', ← hlk2]; exact hf.lkLen)
      (hs''.trans ((congrArg DcG.strs hf.same).trans hstr2)) hd''
      (outW M' M'' hf.out fun a o1 o2 o3 => hout'' a o1 o2 fun h' => o3 (by
        simp only [frameIn] at h' ⊢; omega))

end Dc.Mach
