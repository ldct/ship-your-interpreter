import Dc.Mach.DcBinop

/-!
# `dc_binop2` (M9)

    dc_binop2 (int (*op)(), int kscale):
      the checks of dc_binop;
      dc_pop (&b); dc_pop (&a);
      if ((*op)(a.v.number, b.v.number, kscale, &r1.v.number, &r2.v.number) == DC_SUCCESS)
        { dc_push (r1); dc_push (r2);   -- both inlined
          dc_free_num (&a.v.number); dc_free_num (&b.v.number); }
      else { dc_push (a); dc_push (b); }

The 128-byte frame mirrors `dc_binop`'s 112-byte one with a second result
slot; the checks are `dc_binop`'s at other addresses (`binop2_entry`).

- `DcOp2`: the contract of an operation with two results (`dc_divrem`):
  entry `OpIn2`, results `OpRet2`/`OpFail2`, `dc_memfail` through `OomAt`.
- `DcAt.pushAgree`: an inline push whose node stores are interleaved with
  frame stores, by agreement with `boPushMem` off the frame.
- `dc_binop2_spec`: `binop2 st (f st.scale)`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-! ## The contract -/

/-- A two-result operation's entry: the operand handles, the scale in `a2`,
the result slots `qq` (first) and `qr` (second) above the frame. -/
structure OpIn2 (S : Nat → Prop) (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G : DcG) (hs : List GV) (st : St) (pa pb : Nat) (na nb : Num)
    (R : Nat → BitVec 64) (sp qq qr N lk : Nat) : Prop where
  h : DcAt S M H F L C G (.num pa :: .num pb :: hs) st
  da : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb)
  hsLen : hs.length + 4 ≤ 2 ^ 20
  lkLen : G.lk.length + lk ≤ 2 ^ 29
  frame : StackFrame S sp N
  above : heapEnd + N ≤ sp
  slotQ : PtrSlot S qq
  slotR : PtrSlot S qr
  hiQ : sp ≤ qq
  apart : qq + 8 ≤ qr
  r10 : R 10 = BitVec.ofNat 64 pa
  r11 : R 11 = BitVec.ofNat 64 pb
  r12 : R 12 = BitVec.ofNat 64 st.scale
  r13 : R 13 = BitVec.ofNat 64 qq
  r14 : R 14 = BitVec.ofNat 64 qr
  r2 : R 2 = BitVec.ofNat 64 sp
  al : (R 1).toNat % 4 = 0
  mb : MulBase S M

/-- The bytes of both result slots. -/
abbrev slots2 (qq qr : Nat) (a : Nat) : Prop := slotBytes qq a ∨ slotBytes qr a

/-- A two-result operation's success: `0`, fresh handles `yq`, `yr` for
`rq`, `rr` in the slots. -/
structure OpRet2 (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G0 G : DcG) (hs : List GV) (st : St) (pa pb : Nat) (na nb : Num)
    (f : Nat → Num → Num → Option (Num × Num)) (R : Nat → BitVec 64) (sp qq qr N lk yq yr : Nat)
    (rq rr : Num) : Prop where
  a0 : R 10 = 0#64
  h : DcAt S M H F L C G (.num yq :: .num yr :: .num pa :: .num pb :: hs) st
  val : f st.scale na nb = some (rq, rr)
  dq : (GV.num yq).Den ⟨L, G.strs⟩ (.num rq)
  dr : (GV.num yr).Den ⟨L, G.strs⟩ (.num rr)
  wq : ldv .ld M qq = BitVec.ofNat 64 yq
  wr : ldv .ld M qr = BitVec.ofNat 64 yr
  same : G = { G0 with lk := G.lk }
  lkLen : G.lk.length ≤ G0.lk.length + lk
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slots2 qq qr a → imgM M a = imgM M0 a

/-- A two-result operation's failure: nonzero, the operands kept. -/
structure OpFail2 (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G0 G : DcG) (hs : List GV) (st : St) (pa pb : Nat) (na nb : Num)
    (f : Nat → Num → Num → Option (Num × Num)) (R : Nat → BitVec 64) (sp qq qr N lk : Nat) :
    Prop where
  a0 : R 10 ≠ 0#64
  h : DcAt S M H F L C G (.num pa :: .num pb :: hs) st
  val : f st.scale na nb = none
  da : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb)
  same : G = { G0 with lk := G.lk }
  lkLen : G.lk.length ≤ G0.lk.length + lk
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slots2 qq qr a → imgM M a = imgM M0 a

/-- **The contract of a two-result operation at `fa`** computing `f k a b`
within the stack window `N`, losing at most `lk` references. -/
def DcOp2 (live S : Nat → Prop) (fa N lk : Nat) (ok : Nat → Num → Num → Prop)
    (f : Nat → Num → Num → Option (Num × Num)) : Prop :=
  ∀ (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (t : String) (M : Mem) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs : List GV) (st : St)
    (pa pb : Nat) (na nb : Num) (R : Nat → BitVec 64) (sp qq qr : Nat),
    OpIn2 S M H F L C G hs st pa pb na nb R sp qq qr N lk → ok st.scale na nb →
    (∀ R' M' H' F' L' C' G' yq yr rq rr, Keeps opClob R' R →
      OpRet2 S M M' H' F' L' C' G G' hs st pa pb na nb f R' sp qq qr N lk yq yr rq rr →
      DWO live S Q t (R 1) R' M') →
    (∀ R' M' H' F' L' C' G', Keeps opClob R' R →
      OpFail2 S M M' H' F' L' C' G G' hs st pa pb na nb f R' sp qq qr N lk →
      DWO live S Q t (R 1) R' M') →
    (∀ R' M' sp', OomAt S sp N M (slots2 qq qr) sp' R' M' → DWO live S Q t 0x80001e74#64 R' M') →
    DWO live S Q t (BitVec.ofNat 64 fa) R M

/-! ## The model -/

theorem binop2_of_not {st : St} {f : Num → Num → Option (Num × Num)}
    (h : ∀ b a rest, st.stack ≠ .num b :: .num a :: rest) : binop2 st f = st := by
  unfold binop2
  split
  · rename_i b a rest e; exact absurd e (h b a rest)
  · rfl

theorem binop2_push_some {st : St} {a b rq rr : Num} {g : Num → Num → Option (Num × Num)}
    (h : g a b = some (rq, rr)) :
    binop2 ((st.push (.num a)).push (.num b)) g = (st.push (.num rq)).push (.num rr) := by
  simp only [binop2, St.push, h]

theorem binop2_push_none {st : St} {a b : Num} {g : Num → Num → Option (Num × Num)}
    (h : g a b = none) :
    binop2 ((st.push (.num a)).push (.num b)) g = (st.push (.num a)).push (.num b) := by
  simp only [binop2, St.push, h]

/-! ## The checks -/

/-- A message tail of `dc_binop2` (`0x80003310`: non-numeric, `0x8000332c`:
stack empty): `fprintf (stderr, msg, progname)` as a tail call. -/
theorem binop2_msg {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 304) (hab : heapEnd + 304 ≤ sp) {pc : BitVec 64}
    (hpc : pc = 0x80003310#64 ∨ pc = 0x8000332c#64)
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

/-- `dc_binop2`'s checks with two nodes on the stack. -/
theorem binop2_two {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64}
    {c1 c2 : Blk} {g1 g2 : GV}
    (h0 : ldv .ld M dcStackAddr = BitVec.ofNat 64 c1.pay)
    (h0' : ldv .ld M (c1.pay + 24) = BitVec.ofNat 64 c2.pay)
    (ht1 : ldv .lw M c1.pay = BitVec.ofNat 64 g1.tag) (ht2 : ldv .lw M c2.pay = BitVec.ofNat 64 g2.tag)
    (hc1 : 2147603936 ≤ c1.pay ∧ c1.pay + 32 ≤ 2273312768 ∧ c1.pay % 16 = 0)
    (hc2 : 2147603936 ≤ c2.pay ∧ c2.pay + 32 ≤ 2273312768 ∧ c2.pay % 16 = 0)
    (hG : ∀ a, DcGlob a → S a)
    (hno : (g1.tag ≠ 1 ∨ g2.tag ≠ 1) → ∀ R', Keeps [11, 12, 13, 14, 15, 17] R' R →
      DWO live S Q t 0x80003310#64 R' M)
    (hgo : g1.tag = 1 → g2.tag = 1 → ∀ R', Keeps [13, 14, 15, 17] R' R → R' 17 = 1#64 →
      DWO live S Q t 0x80003348#64 R' M) :
    DWO live S Q t 0x800032e8#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hc0 : BitVec.ofNat 64 c1.pay ≠ 0#64 := ofNat_pos_ne (by omega) (by omega)
  have hc0' : BitVec.ofNat 64 c2.pay ≠ 0#64 := ofNat_pos_ne (by omega) (by omega)
  bc_run hlive hS [h0, h0', ht1, ht2] at 0x80003310
  all_goals try (intro hc; exact absurd hc hc0)
  intro _
  bsimp []
  bc_run hlive hS [h0, h0', ht1, ht2] at 0x80003310
  all_goals try (intro hc; exact absurd hc hc0')
  intro _
  bsimp []
  obtain e1 | e1 : g1.tag = 1 ∨ g1.tag = 2 := by cases g1 <;> simp [GV.tag]
  · rw [e1] at ht1
    obtain e2 | e2 : g2.tag = 1 ∨ g2.tag = 2 := by cases g2 <;> simp [GV.tag]
    · rw [e2] at ht2
      bc_run hlive hS [h0, h0', ht1, ht2] at 0x80003348
      all_goals try (intro hc; exact absurd hc (by decide))
      (try intro _); (try bsimp [])
      bc_run hlive hS [h0, h0', ht1, ht2] at 0x80003348
      all_goals try (intro hc; exact absurd hc (by decide))
      (try intro _); (try bsimp [])
      exact hgo e1 e2 _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
    · rw [e2] at ht2
      bc_run hlive hS [h0, h0', ht1, ht2] at 0x80003310
      all_goals try (intro hc; exact absurd hc (by decide))
      (try intro _); (try bsimp [])
      bc_run hlive hS [h0, h0', ht1, ht2] at 0x80003310
      all_goals try (intro hc; exact absurd hc (by decide))
      (try intro _); (try bsimp [])
      exact hno (.inr (by omega)) _ (by keeps_tac Keeps.refl _ _)
  · rw [e1] at ht1
    bc_run hlive hS [h0, h0', ht1, ht2] at 0x80003310
    all_goals try (intro hc; exact absurd hc (by decide))
    (try intro _); (try bsimp [])
    exact hno (.inl (by omega)) _ (by keeps_tac Keeps.refl _ _)

/-- **`dc_binop2`'s checks** at `0x800032e8`: with two numbers on top the run
goes on at `0x80003348` (`a7` the second's type `1`); otherwise one of the
two messages goes to `stderr` and `dc_binop2` returns with the state kept. -/
theorem binop2_entry {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 304) (hab : heapEnd + 304 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk0 : (∀ b a rest, st.stack ≠ .num b :: .num a :: rest) → ∀ R' M', Keeps fprintfClob R' R →
      (∀ a, (a < sp - 304 ∨ sp ≤ a) → imgM M' a = imgM M a) → DWO live S Q t (R 1) R' M')
    (hgo : ∀ cb ca pb pa rest, G.stk = (cb, .num pb) :: (ca, .num pa) :: rest → ∀ R',
      Keeps [13, 14, 15, 17] R' R → R' 17 = 1#64 → DWO live S Q t 0x80003348#64 R' M) :
    DWO live S Q t 0x800032e8#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hden := h.den.stk
  have hv := h.view.stk
  have hmsg : ∀ {pc : BitVec 64}, (pc = 0x80003310#64 ∨ pc = 0x8000332c#64) →
      (∀ b a rest, st.stack ≠ .num b :: .num a :: rest) → ∀ R1, Keeps [11, 12, 13, 14, 15, 17] R1 R →
      DWO live S Q t pc R1 M := fun hpc hno R1 hk1 =>
    binop2_msg hlive h hsf hab hpc R1 (by rw [hk1.get 2 (by decide), h2])
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
    bc_run hlive hS [h0] at 0x8000332c
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
      bc_run hlive hS [h0, hl0] at 0x8000332c
      all_goals try (intro hc; exact absurd hc hc0)
      (try intro _); (try bsimp [])
      bc_run hlive hS [h0, hl0] at 0x8000332c
      exact hmsg (.inr rfl) hno _ (by keeps_tac Keeps.refl _ _)
    | cons n2 rest2 =>
      obtain ⟨c2, g2⟩ := n2
      have hc2 := h.stkPay (c := c2) (g := g2) (by rw [hstk]; simp)
      cases hl1 with
      | cons h0' hn2 hl2 =>
      refine binop2_two hlive hS h0 h0' hn1.dat.lw hn2.dat.lw hc1 hc2 hG (fun hn R1 hk1 => ?_)
        fun e1 e2 R1 hk1 e17 => ?_
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
        | num pa => exact hgo c1 c2 pb pa rest2 hstk R1 hk1 e17

/-! ## The pops -/

/-- `dc_binop2`'s frame words (`sp1 = sp - 128`): `op`, `kscale`, the second's
type word and the return address. -/
structure B2Frame (M : Mem) (sp1 fa k : Nat) (ra : BitVec 64) : Prop where
  wfa : ldv .ld M (sp1 + 8) = BitVec.ofNat 64 fa
  wk : ldv .ld M (sp1 + 16) = BitVec.ofNat 64 k
  wtag : ldv .ld M (sp1 + 24) = 1#64
  wra : ldv .ld M (sp1 + 120) = ra

theorem B2Frame.transport {M M' : Mem} {sp1 fa k : Nat} {ra : BitVec 64} (h : B2Frame M sp1 fa k ra)
    (hag : ∀ a, (sp1 + 8 ≤ a ∧ a < sp1 + 32) ∨ (sp1 + 120 ≤ a ∧ a < sp1 + 128) → imgM M' a = imgM M a) :
    B2Frame M' sp1 fa k ra where
  wfa := by rw [ldv_congr .ld fun j hj => hag _ (.inl (by simp only [widthOfM] at hj; omega))]; exact h.wfa
  wk := by rw [ldv_congr .ld fun j hj => hag _ (.inl (by simp only [widthOfM] at hj; omega))]; exact h.wk
  wtag := by rw [ldv_congr .ld fun j hj => hag _ (.inl (by simp only [widthOfM] at hj; omega))]; exact h.wtag
  wra := by rw [ldv_congr .ld fun j hj => hag _ (.inr (by simp only [widthOfM] at hj; omega))]; exact h.wra

/-- The state at the call of `op`: both operands popped into the slots at
`sp1 + 32` (`a`) and `sp1 + 48` (`b`), their handles held. -/
structure B2At (S : Nat → Prop) (M0 M : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G2 : DcG) (hs : List GV) (st st2 : St) (sp W fa k : Nat) (ra : BitVec 64)
    (pa pb : Nat) (na nb : Num) : Prop where
  st : st = (st2.push (.num na)).push (.num nb)
  h : DcAt S M H F L C G2 (.num pa :: .num pb :: hs) st2
  da : (GV.num pa).Den ⟨L, G2.strs⟩ (.num na)
  db : (GV.num pb).Den ⟨L, G2.strs⟩ (.num nb)
  fr : B2Frame M (sp - 128) fa k ra
  sa : DatAt M (sp - 128 + 32) (.num pa)
  sb : DatAt M (sp - 128 + 48) (.num pb)
  out : StkOut sp W M M0

theorem word_sub128 {x : Nat} (h : 128 ≤ x) :
    BitVec.ofNat 64 x + 18446744073709551488#64 = BitVec.ofNat 64 (x - 128) := by
  change BitVec.ofNat 64 x + -(128#64) = _
  rw [BitVec.add_neg_eq_sub]
  exact BitVec.ofNat_sub_ofNat_of_le x 128 (by decide) h

/-- **`dc_binop2`'s two pops** (`0x80003348` to the call of `op`). -/
theorem binop2_pops {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp W : Nat}
    (hsf : StackFrame S sp W) (hab : heapEnd + W ≤ sp) (hW : 464 ≤ W)
    {cb ca : Blk} {pb pa : Nat} {rest : List (Blk × GV)}
    (hstk : G.stk = (cb, .num pb) :: (ca, .num pa) :: rest)
    {fa k : Nat} (hfa : fa % 4 = 0) (hfa2 : fa < 2 ^ 64)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 fa) (h11 : R 11 = BitVec.ofNat 64 k)
    (h17 : R 17 = 1#64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R1 M2 H2 G2 st2 na nb, Keeps (1 :: 2 :: popClob) R1 R → G2.lk = G.lk →
      R1 1 = 0x80003388#64 → R1 2 = BitVec.ofNat 64 (sp - 128) → R1 10 = BitVec.ofNat 64 pa →
      R1 11 = BitVec.ofNat 64 pb → R1 12 = BitVec.ofNat 64 k →
      R1 13 = BitVec.ofNat 64 (sp - 128 + 72) → R1 14 = BitVec.ofNat 64 (sp - 128 + 88) →
      B2At S M M2 H2 F L C G2 hs st st2 sp W fa k (R 1) pa pb na nb →
      DWO live S Q t (BitVec.ofNat 64 fa) R1 M2) :
    DWO live S Q t 0x80003348#64 R M := by
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
  have hslot : ∀ o, o + 16 ≤ 128 → o % 8 = 0 → DatSlot S (sp - 128) (sp - 128 + o) := fun o h1 h2 =>
    ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩
  have hden := h.den.stk
  rw [hstk] at hden
  have hne : st.stack ≠ [] := fun e => by rw [e] at hden; cases hden
  refine dc_pop_spec hlive h1 (hsf.within (m := 128) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (hslot 48 (by omega) (by omega)) _ (by bsimp []) (by bsimp [])
    (by bsimp []) (fun R2 M2 H2 G1 g v st1 est eG hk2 e10 h1' hd1 hout1 => ?_)
    (fun e => absurd e hne)
  obtain ⟨c, rfl⟩ := eG
  simp only [List.cons.injEq, Prod.mk.injEq] at hstk
  obtain ⟨⟨rfl, rfl⟩, hG1⟩ := hstk
  subst est
  obtain ⟨nb, rfl, hdb⟩ := (by cases hden with | cons hh _ => exact den_num_head hh :
    ∃ nb, v = .num nb ∧ (GV.num pb).Den ⟨L, G1.strs⟩ (.num nb))
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk2.get 2 (by decide)]; bsimp []
  have hS2 : HeapOwn S := fun a h1 h2 => h1'.heap.heap.own a h1 h2
  bsimp []
  bc_run hlive hS2 [q2] at 0x8000310c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hden1 := h1'.den.stk
  rw [hG1] at hden1
  have hne1 : st1.stack ≠ [] := fun e => by rw [e] at hden1; cases hden1
  refine dc_pop_spec hlive h1' (hsf.within (m := 128) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (hslot 32 (by omega) (by omega)) _ (by bsimp []) (by bsimp [q2])
    (by bsimp []) (fun R3 M3 H3 G2 g2 v2 st2 est2 eG2 hk3 e10' h2' hd2 hout2 => ?_)
    (fun e => absurd e hne1)
  obtain ⟨c2, rfl⟩ := eG2
  simp only [List.cons.injEq, Prod.mk.injEq] at hG1
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hG1
  subst est2
  obtain ⟨na, rfl, hda⟩ := (by cases hden1 with | cons hh _ => exact den_num_head hh :
    ∃ na, v2 = .num na ∧ (GV.num pa).Den ⟨L, G2.strs⟩ (.num na))
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hfr3 : B2Frame M3 (sp - 128) fa k (R 1) := (hfr1.transport fun a ha => by
      have ⟨o1, o2, o3⟩ := above_sp hab2 (a := a) (by omega)
      exact hout1 a o1 o2 (o3 _) (by omega)).transport fun a ha => by
    have ⟨o1, o2, o3⟩ := above_sp hab2 (a := a) (by omega)
    exact hout2 a o1 o2 (o3 _) (by omega)
  have hb3 : ldv .ld M3 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => by
      have ⟨o1, o2, o3⟩ := above_sp hab2 (a := sp - 128 + 48 + 8 + j) (by omega)
      exact hout2 _ o1 o2 (o3 _) (by simp only [widthOfM] at hj; omega)]
    exact hd1.ptr
  have ha3 := hd2.ptr
  have q3 : R3 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
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
  have hsb : DatAt M3 (sp - 128 + 48) (.num pb) := by
    refine ⟨?_, hb3⟩
    rw [ldv_congr .ld fun j hj => by
      have ⟨o1, o2, o3⟩ := above_sp hab2 (a := sp - 128 + 48 + j) (by omega)
      exact hout2 _ o1 o2 (o3 _) (by simp only [widthOfM] at hj; omega)]
    exact hd1.tag
  refine hk _ M3 H3 G2 st2 na nb
    (by keeps_tac ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))))) rfl
    (by bsimp []) (by bsimp [q3]) (by bsimp []; rfl) (by bsimp []) (by bsimp []) (by bsimp [])
    (by bsimp []) ⟨rfl, h2', hda, hdb, hfr3, hd2, hsb, fun a ho hg hf => ?_⟩
  have hf1 : ¬ frameIn (sp - 128) 336 a := fun h' => hf (by simp only [frameIn] at h' ⊢; omega)
  rw [hout2 a ho hg hf1 (by simp only [frameIn] at hf; omega),
    hout1 a ho hg hf1 (by simp only [frameIn] at hf; omega)]
  exact hM1 a fun h' => hf (by simp only [frameIn] at h' ⊢; omega)

/-! ## After `op` -/

/-- **`op` failed** (`0x80003388`, `a0 ≠ 0`): `a` then `b` pushed back, the
state as before the pops. -/
theorem binop2_fail {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb : Nat} {na nb : Num} (h : DcAt S M H F L C G (.num pa :: .num pb :: hs) st)
    (hda : (GV.num pa).Den ⟨L, G.strs⟩ (.num na)) (hdb : (GV.num pb).Den ⟨L, G.strs⟩ (.num nb))
    {sp fa k : Nat} {ra : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hfr : B2Frame M (sp - 128) fa k ra) (hsa : DatAt M (sp - 128 + 32) (.num pa))
    (hsb : DatAt M (sp - 128 + 48) (.num pb)) (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 128)) (h10 : R 10 ≠ 0#64)
    (hk : ∀ R' M' H' G', Keeps (1 :: 2 :: pushClob) R' R → G'.lk = G.lk → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DcAt S M' H' F L C G' hs ((st.push (.num na)).push (.num nb)) →
      StkOut (sp - 128) 64 M' M → DWO live S Q t ra R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128 - 64) → StkOut (sp - 128) 64 M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80003388#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hfs : StackFrame S (sp - 128) 64 := hsf.within (by omega) (by decide)
  have wa0 := hsa.ptr
  refine st_80003388 hlive (fun _ => ?_) fun hc => absurd h10 hc
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
  have wra2 : ldv .ld M2 (sp - 128 + 120) = ra := by
    rw [ldv_congr .ld fun j hj => habv _ (by omega) _ (fun a o1 o2 o3 => by
      rw [hout2 a o1 o2 o3, hout1 a o1 o2 o3])]; exact hfr.wra
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS2 [q2, wra2]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hral
  refine hk _ M2 H2 { G with stk := (c2, .num pb) :: (c1, .num pa) :: G.stk } (by keeps_tac ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))))) rfl (by bsimp []) (by bsimp [q2]; rw [show sp - 128 + 128 = sp by omega]) h2'
    fun a o1 o2 o3 => by rw [hout2 a o1 o2 o3, hout1 a o1 o2 o3]

/-- **An inline push with frame stores among the node stores**: a memory
agreeing with `boPushMem` off the frame bytes `P` holds the pushed state. -/
theorem DcAt.pushAgree {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {v : Val} {b : Blk}
    {w0 w1 : BitVec 64} {P : Nat → Prop}
    (h : DcAt S M H F L C G (g :: hs) st) (hf : DcFresh H F L G b) (hv : g.Den ⟨L, G.strs⟩ v)
    (hd : DatRegs w0 w1 g) (hsz : 32 ≤ b.sz) (hp1 : 2147603936 ≤ b.pay)
    (hP : ∀ a, P a → OutHeap a ∧ ¬ DcGlob a)
    (hag : ∀ a, ¬ P a → imgM M' a = imgM (boPushMem M b.pay w0 w1) a) :
    DcAt S M' H F L C { G with stk := (b, g) :: G.stk } hs (st.push v) ∧
      MemOnly (fun a => b.In a ∨ StkWord a ∨ P a) M' M := by
  obtain ⟨h3, hm3⟩ := boPush_post h hf hv hd hsz hp1
  refine ⟨h3.outWrite (fun a ha => hag a ha) hP, fun a ha => ?_⟩
  simp only [not_or] at ha
  rw [hag a ha.2.2]
  exact hm3 a fun hb => by
    rcases hb with hb | hb
    · exact ha.1 hb
    · exact ha.2.1 hb

/-- **The operand frees and the return** after both pushes (`0x80003428`
onward): free the slots at `sp1 + 40` (`a`) and `sp1 + 56` (`b`), reload
`ra`, return. -/
theorem binop2_frees {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M3 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pa pb : Nat}
    (h3 : DcAt S M3 H F L C G (.num pa :: .num pb :: hs) st)
    {sp : Nat} {ra : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hwa : ldv .ld M3 (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa)
    (hwb : ldv .ld M3 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb)
    (hwr : ldv .ld M3 (sp - 128 + 120) = ra) (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (q1 : R 2 = BitVec.ofNat 64 (sp - 128))
    (h10 : R 10 = BitVec.ofNat 64 (sp - 128 + 32 + 8)) (h1 : R 1 = 0x8000342c#64)
    (hk : ∀ R' M' H' F' L' C', Keeps (1 :: 2 :: freeNumClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DcAt S M' H' F' L' C' G hs st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M3 a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x80002ba0#64 R M3 := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hsf32 : StackFrame S (sp - 128) 32 := hsf.within (by omega) (by decide)
  refine dc_free_num_spec hlive h3 (q := sp - 128 + 32 + 8) (hsf.slot (by omega) (by omega) (by omega))
    (by omega) hwa hsf32 (by omega) (Or.inr (by omega)) _ h10 q1 (by rw [h1]; decide)
    (fun R4 M4 H4 F4 L4 C4 hk4 h4 _ hout4 => ?_)
  have ag4 : ∀ a, sp - 128 ≤ a → ¬ slotBytes (sp - 128 + 32 + 8) a → imgM M4 a = imgM M3 a :=
    fun a ha hn => hout4 a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 32) hn
  have q4 : R4 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk4.get 2 (by decide)]; bsimp [q1]
  have hwb4 : ldv .ld M4 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => ag4 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)]
    exact hwb
  have hS4 : HeapOwn S := fun a e1 e2 => h4.heap.heap.own a e1 e2
  rw [h1]
  bc_run hlive hS4 [q4] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_free_num_spec hlive h4 (q := sp - 128 + 48 + 8) (hsf.slot (by omega) (by omega) (by omega))
    (by omega) hwb4 hsf32 (by omega) (Or.inr (by omega)) _ (by bsimp []) (by bsimp [q4]) (by bsimp [])
    (fun R5 M5 H5 F5 L5 C5 hk5 h5 _ hout5 => ?_)
  have ag5 : ∀ a, sp - 128 ≤ a → ¬ slotBytes (sp - 128 + 48 + 8) a → imgM M5 a = imgM M4 a :=
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

/-- **The second push** (`dc_malloc` at `0x800033f8` onward): the
remainder's handle `yr` (frame words `sp1 + 96`, `sp1 + 104`) pushed
inline, then both operands freed. -/
theorem binop2_second {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb yr : Nat} {rr : Num}
    (h : DcAt S M H F L C G (.num yr :: .num pa :: .num pb :: hs) st)
    (hdr : (GV.num yr).Den ⟨L, G.strs⟩ (.num rr))
    {sp : Nat} {ra w0 : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hwa : ldv .ld M (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa)
    (hwb : ldv .ld M (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb)
    (hwr : ldv .ld M (sp - 128 + 120) = ra) (hral : ra.toNat % 4 = 0)
    (l96 : ldv .ld M (sp - 128 + 96) = w0) (l104 : ldv .ld M (sp - 128 + 104) = BitVec.ofNat 64 yr)
    (hd : DatRegs w0 (BitVec.ofNat 64 yr) (.num yr))
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 128)) (h10 : R 10 = 32#64)
    (h1 : R 1 = 0x800033fc#64)
    (hk : ∀ R' M' H' F' L' C' (G' : DcG), Keeps (1 :: 2 :: opClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → G'.lk = G.lk → DcAt S M' H' F' L' C' G' hs (st.push (.num rr)) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M a) →
      DWO live S Q t ra R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128 - 16) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M a) →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80001ea0#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hi := h.heap.heap
  refine dc_malloc_spec hlive hi (n := 32) (sp := sp - 128) (by omega)
    (hsf.within (m := 128) (n := 16) (by omega) (by decide)) (by simp only [heapEnd]; omega) _
    (by rw [h10]) h2 (by rw [h1]; decide) (fun R1 M2 H2 b hk1 hp hr10 => ?_)
    (fun R1 M2 hr2 hfr2 => ?_)
  rotate_left
  · refine hoom R1 M2 hr2 fun a ho hg hf => ?_
    exact hfr2 a (OutHeap.not_alloc hi ho) (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
  obtain ⟨h2', hfresh⟩ := h.malloc hp (by decide) (by simp only [heapEnd]; omega)
  have hcl := hfresh.live
  have fbb := h2'.heap.heap.blk (List.mem_append_right _ hcl)
  have hblo : 2147603920 ≤ b.h := fbb.lo
  have hbhi : b.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : b.h % 16 = 0 := fbb.al
  have hbsz := hp.size
  have hpl : 2147603936 ≤ b.pay ∧ b.pay + 32 ≤ 2273312768 ∧ b.pay % 16 = 0 := by
    simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk1.get 2 (by decide)]; exact h2
  have ag2 : ∀ a, sp - 128 ≤ a → imgM M2 a = imgM M a := fun a ha =>
    hp.frame a (OutHeap.not_alloc hi (above_sp hab2 ha).1) fun hf => by
      simp only [frameIn] at hf; omega
  have l96' : ldv .ld M2 (sp - 128 + 96) = w0 := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega)]; exact l96
  have l104' : ldv .ld M2 (sp - 128 + 104) = BitVec.ofNat 64 yr := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega)]; exact l104
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  have hG2 := h2'.glob
  rw [h1]
  bc_run hlive hS2 [q1, hr10, l96', l104'] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  obtain ⟨h3, hm3⟩ := boPush_post h2' hfresh hdr hd hp.size hpl1
  show DW _ _ _ _ _ (boPushMem M2 b.pay w0 (BitVec.ofNat 64 yr))
  generalize boPushMem M2 b.pay w0 (BitVec.ofNat 64 yr) = M3 at h3 hm3
  have agM : ∀ a, sp - 128 ≤ a → imgM M3 a = imgM M a :=
    fun a ha => by
      rw [hm3 a (fun hb => by
        rcases hb with hb | hb
        · simp only [Blk.In] at hb; omega
        · simp only [StkWord, dcStackAddr] at hb; omega), ag2 a ha]
  have hwa3 : ldv .ld M3 (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa := by
    rw [ldv_congr .ld fun j hj => agM _ (by omega)]; exact hwa
  have hwb3 : ldv .ld M3 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => agM _ (by omega)]; exact hwb
  have hwr3 : ldv .ld M3 (sp - 128 + 120) = ra := by
    rw [ldv_congr .ld fun j hj => agM _ (by omega)]; exact hwr
  exact binop2_frees hlive h3 hsf hab hwa3 hwb3 hwr3 hral _ (by bsimp [q1]) (by bsimp []) (by bsimp [])
    fun R' M' H' F' L' C' hk' e1 e2 h' hout' => hk R' M' H' F' L' C' { G with stk := (b, .num yr) :: G.stk }
      (by keeps_tac ((hk'.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _))))) e1 e2 rfl h' fun a ho hg hf => by
      rw [hout' a ho hg hf, hm3 a (fun hb => by
        rcases hb with hb | hb
        · simp only [Blk.In, Blk.pay, Blk.fin] at hb hbhi hpl1; simp only [OutHeap, heapStart, heapEnd] at ho; omega
        · exact hg (by simp only [StkWord, DcGlob, dc_addrs] at hb ⊢; omega)),
        hp.frame a (OutHeap.not_alloc hi ho) fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]

/-- **The first push's node stores** (`0x800033dc` to the second
`dc_malloc`): the node at `b` written around the frame stores, then
`binop2_second`. -/
theorem binop2_mid {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M2 : Mem} {H2 : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb yq yr sp : Nat} {rq rr : Num} {b : Blk}
    (h2' : DcAt S M2 H2 F L C G (.num yq :: .num yr :: .num pa :: .num pb :: hs) st)
    (hfresh : DcFresh H2 F L G b) (hbsz : 32 ≤ b.sz) (hpl1 : 2147603936 ≤ b.pay)
    (hpl2 : b.pay + 32 ≤ 2273312768) (hpl3 : b.pay % 16 = 0) (hbhi : b.fin ≤ 2273312768)
    (hdq : (GV.num yq).Den ⟨L, G.strs⟩ (.num rq)) (hdr : (GV.num yr).Den ⟨L, G.strs⟩ (.num rr))
    {ra w0 w1 old : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hwa : ldv .ld M2 (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa)
    (hwb : ldv .ld M2 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb)
    (hwr : ldv .ld M2 (sp - 128 + 120) = ra) (hral : ra.toNat % 4 = 0)
    (hd : DatRegs w0 (BitVec.ofNat 64 yq) (.num yq)) (hw1 : w1.toNat % 2 ^ 32 = (1#64).toNat % 2 ^ 32)
    (hold : ldv .ld M2 dcStackAddr = old)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 128)) (h10 : R 10 = BitVec.ofNat 64 b.pay)
    (h11 : R 11 = BitVec.ofNat 64 yq) (h12 : R 12 = old) (h13 : R 13 = w1)
    (h14 : R 14 = BitVec.ofNat 64 yr) (h15 : R 15 = BitVec.ofNat 64 b.pay)
    (h16 : R 16 = 2147601816#64)
    (hk : ∀ R' M' H' F' L' C' (G' : DcG), Keeps (1 :: 2 :: opClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → G'.lk = G.lk →
      DcAt S M' H' F' L' C' G' hs ((st.push (.num rq)).push (.num rr)) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M2 a) →
      DWO live S Q t ra R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128 - 16) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M2 a) →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x800033dc#64 R (writeLog (writeLog M2 [(b.pay, 8, w0)]) [(sp - 128 + 80, 4, 1#64)]) := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  have hG2 := h2'.glob
  bc_run hlive hS2 [h2, h10, h11, h12, h13, h14, h15, h16] at 0x80001ea0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals try (intro x hx; have hx' := VsaIris.Sym.of_mem_accAddrs hx; exact hG2 x (by simp only [DcGlob, dc_addrs] at hx' ⊢; omega))
  all_goals try (show StOK _ _; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)
  generalize hMx : writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M2
      [(b.pay, 8, w0)]) [(sp - 128 + 80, 4, 1#64)]) [(b.pay + 8, 8, BitVec.ofNat 64 yq)])
      [(b.pay + 24, 8, old)]) [(b.pay + 16, 8, 0#64)]) [(2147601816, 8, BitVec.ofNat 64 b.pay)])
      [(sp - 128 + 96, 8, w1)]) [(sp - 128 + 104, 8, BitVec.ofNat 64 yr)] = Mx
  have hds : dcStackAddr = 2147601816 := rfl
  have hag : ∀ a, ¬ ((sp - 128 + 80 ≤ a ∧ a < sp - 128 + 84) ∨ (sp - 128 + 96 ≤ a ∧ a < sp - 128 + 112)) →
      imgM Mx a = imgM (boPushMem M2 b.pay w0 (BitVec.ofNat 64 yq)) a := by
    intro a ha
    simp only [not_or] at ha
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
  have l96 : ldv .ld Mx (sp - 128 + 96) = w1 := by rw [← hMx, ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have l104 : ldv .ld Mx (sp - 128 + 104) = BitVec.ofNat 64 yr := by rw [← hMx, ldv_store_hit]
  have hPo : ∀ a, ((sp - 128 + 80 ≤ a ∧ a < sp - 128 + 84) ∨ (sp - 128 + 96 ≤ a ∧ a < sp - 128 + 112)) →
      OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp hab2 (a := a) (by omega)).1, (above_sp hab2 (a := a) (by omega)).2.1⟩
  obtain ⟨h4, hm4⟩ := DcAt.pushAgree h2' hfresh hdq hd hbsz hpl1 hPo hag
  have agx : ∀ a, sp - 128 ≤ a → a < sp - 128 + 80 → imgM Mx a = imgM M2 a := fun a e1 e2 =>
    hm4 a fun hb => by
      rcases hb with hb | hb | hb
      · simp only [Blk.In, Blk.pay, Blk.fin] at hb hbhi; omega
      · simp only [StkWord, hds] at hb; omega
      · omega
  have agr : ∀ a, sp - 128 + 112 ≤ a → a < sp - 128 + 128 → imgM Mx a = imgM M2 a := fun a e1 e2 =>
    hm4 a fun hb => by
      rcases hb with hb | hb | hb
      · simp only [Blk.In, Blk.pay, Blk.fin] at hb hbhi; omega
      · simp only [StkWord, hds] at hb; omega
      · omega
  have hwa4 : ldv .ld Mx (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa := by
    rw [ldv_congr .ld fun j hj => agx _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hwa
  have hwb4 : ldv .ld Mx (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => agx _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hwb
  have hwr4 : ldv .ld Mx (sp - 128 + 120) = ra := by
    rw [ldv_congr .ld fun j hj => agr _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hwr
  refine binop2_second hlive h4 hdr hsf hab hwa4 hwb4 hwr4 hral l96 l104 ⟨by rw [hw1]; rfl, rfl⟩ (upd (upd R 10 32#64) 1 2147496956#64)
    (by bsimp [h2]) (by bsimp []) (by bsimp [])
    (fun R' M' H' F' L' C' G' hk' e1 e2 elk h' hout' => hk R' M' H' F' L' C' G'
      ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) e1 e2 elk h' fun a ho hg hf => by
        rw [hout' a ho hg hf]
        exact hm4 a fun hb => by
          rcases hb with hb | hb | hb
          · simp only [Blk.In, Blk.pay, Blk.fin] at hb hbhi hpl1; simp only [OutHeap, heapStart, heapEnd] at ho; omega
          · exact hg (by simp only [StkWord, DcGlob, dc_addrs] at hb ⊢; omega)
          · exact hf (by simp only [frameIn]; omega))
    fun R' M' e2 hout' => hoom R' M' e2 fun a ho hg hf => by
      rw [hout' a ho hg hf]
      exact hm4 a fun hb => by
        rcases hb with hb | hb | hb
        · simp only [Blk.In, Blk.pay, Blk.fin] at hb hbhi hpl1; simp only [OutHeap, heapStart, heapEnd] at ho; omega
        · exact hg (by simp only [StkWord, DcGlob, dc_addrs] at hb ⊢; omega)
        · exact hf (by simp only [frameIn]; omega)

/-- **The first push** (after `dc_malloc` at `0x800033ac` returns): the
quotient's handle `yq` pushed inline with frame stores among the node
stores (`DcAt.pushAgree`), then the second `dc_malloc`. -/
theorem binop2_first {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M1 M2 : Mem} {H H2 : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb yq yr sp : Nat} {rq rr : Num} {b : Blk}
    (h1 : DcAt S M1 H F L C G (.num yq :: .num yr :: .num pa :: .num pb :: hs) st)
    (hp : DcMallocPost S M1 M2 H H2 32 (sp - 128) b)
    (hdq : (GV.num yq).Den ⟨L, G.strs⟩ (.num rq)) (hdr : (GV.num yr).Den ⟨L, G.strs⟩ (.num rr))
    {ra w0 : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hwa : ldv .ld M1 (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa)
    (hwb : ldv .ld M1 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb)
    (hwr : ldv .ld M1 (sp - 128 + 120) = ra) (hral : ra.toNat % 4 = 0)
    (l96 : ldv .ld M1 (sp - 128 + 96) = w0) (l104 : ldv .ld M1 (sp - 128 + 104) = BitVec.ofNat 64 yq)
    (hd : DatRegs w0 (BitVec.ofNat 64 yq) (.num yq)) (l8 : ldv .ld M1 (sp - 128 + 8) = 1#64)
    (l88 : ldv .ld M1 (sp - 128 + 88) = BitVec.ofNat 64 yr)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 128)) (h10 : R 10 = BitVec.ofNat 64 b.pay)
    (h1r : R 1 = 0x800033b0#64)
    (hk : ∀ R' M' H' F' L' C' (G' : DcG), Keeps (1 :: 2 :: opClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → G'.lk = G.lk →
      DcAt S M' H' F' L' C' G' hs ((st.push (.num rq)).push (.num rr)) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M1 a) →
      DWO live S Q t ra R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128 - 16) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M1 a) →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x800033b0#64 R M2 := by
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
  have l104' : ldv .ld M2 (sp - 128 + 104) = BitVec.ofNat 64 yq := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega)]; exact l104
  have l8' : ldv .ld M2 (sp - 128 + 8) = 1#64 := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega)]; exact l8
  have l88' : ldv .ld M2 (sp - 128 + 88) = BitVec.ofNat 64 yr := by
    rw [ldv_congr .ld fun j hj => ag2 _ (by omega)]; exact l88
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  have hG2 := h2'.glob
  bc_run hlive hS2 [h2, h10, l96', l104', l8', l88'] at 0x800033c4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have m0 : ldv .ld (writeLog M2 [(b.pay, 8, w0)]) 2147601816 = ldv .ld M2 dcStackAddr := by
    rw [ldv_ld_miss _ _ (by omega)]
  generalize hold : ldv .ld M2 dcStackAddr = old at m0
  bc_run hlive hS2 [h2, m0] at 0x800033dc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have e104 : ldv .ld (writeLog M2 [(b.pay, 8, w0)]) (sp - 128 + 104) = BitVec.ofNat 64 yq := by
    rw [ldv_ld_miss _ _ (by omega)]; exact l104'
  have e88 : ldv .ld (writeLog M2 [(b.pay, 8, w0)]) (sp - 128 + 88) = BitVec.ofNat 64 yr := by
    rw [ldv_ld_miss _ _ (by omega)]; exact l88'
  rw [e104, e88]
  have hw1 := ld_lo32_sw (writeLog M2 [(b.pay, 8, w0)]) (sp - 128 + 80) 1#64
  generalize ldv .ld (writeLog (writeLog M2 [(b.pay, 8, w0)]) [(sp - 128 + 80, 4, 1#64)])
    (sp - 128 + 80) = w1 at hw1 ⊢
  have agw : ∀ a, sp - 128 ≤ a → imgM M2 a = imgM M1 a := ag2
  have hwa2 : ldv .ld M2 (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa := by
    rw [ldv_congr .ld fun j hj => agw _ (by omega)]; exact hwa
  have hwb2 : ldv .ld M2 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => agw _ (by omega)]; exact hwb
  have hwr2 : ldv .ld M2 (sp - 128 + 120) = ra := by
    rw [ldv_congr .ld fun j hj => agw _ (by omega)]; exact hwr
  have out2 : ∀ M' : Mem, (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M2 a) →
      ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M1 a := fun M' ho a o1 o2 o3 => by
    rw [ho a o1 o2 o3]
    exact hp.frame a (OutHeap.not_alloc hi1 o1) fun hf' => o3 (by simp only [frameIn] at hf' ⊢; omega)
  exact binop2_mid hlive h2' hfresh hbsz hpl1 hpl2 hpl3 hbhi hdq hdr hsf hab hwa2 hwb2 hwr2 hral hd hw1 hold _
    (by bsimp [h2]) (by bsimp [h10]) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [h10])
    (by bsimp [])
    (fun R' M' H' F' L' C' G' hk' e1 e2 elk h' hout' => hk R' M' H' F' L' C' G'
      ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) e1 e2 elk h' (out2 M' hout'))
    fun R' M' e2 hout' => hoom R' M' e2 (out2 M' hout')

/-- **`op` succeeded** (`0x80003388`, `a0 = 0`): the results `yq` then `yr`
pushed inline, then both operand handles freed. -/
theorem binop2_ok {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb yq yr : Nat} {rq rr : Num}
    (h : DcAt S M H F L C G (.num yq :: .num yr :: .num pa :: .num pb :: hs) st)
    (hdq : (GV.num yq).Den ⟨L, G.strs⟩ (.num rq)) (hdr : (GV.num yr).Den ⟨L, G.strs⟩ (.num rr))
    {sp fa k : Nat} {ra : BitVec 64} (hsf : StackFrame S sp 192) (hab : heapEnd + 192 ≤ sp)
    (hfr : B2Frame M (sp - 128) fa k ra) (hsa : DatAt M (sp - 128 + 32) (.num pa))
    (hsb : DatAt M (sp - 128 + 48) (.num pb))
    (hyq : ldv .ld M (sp - 128 + 72) = BitVec.ofNat 64 yq)
    (hyr : ldv .ld M (sp - 128 + 88) = BitVec.ofNat 64 yr) (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 128)) (h10 : R 10 = 0#64)
    (hk : ∀ R' M' H' F' L' C' (G' : DcG), Keeps (1 :: 2 :: opClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → G'.lk = G.lk →
      DcAt S M' H' F' L' C' G' hs ((st.push (.num rq)).push (.num rr)) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M a) →
      DWO live S Q t ra R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128 - 16) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 192 a → imgM M' a = imgM M a) →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80003388#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa' := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 128 := by omega
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  refine st_80003388 hlive (fun hc => absurd h10 hc) fun _ => ?_
  have wtag := hfr.wtag
  bc_run hlive hS [h2, wtag, hyq] at 0x80001ea0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hw0 := ld_lo32_sw M (sp - 128 + 64) 1#64
  generalize ldv .ld (writeLog M [(sp - 128 + 64, 4, 1#64)]) (sp - 128 + 64) = w0 at hw0 ⊢
  have hM1 : MemOnly (fun a => (sp - 128 + 8 ≤ a ∧ a < sp - 128 + 16) ∨ (sp - 128 + 64 ≤ a ∧ a < sp - 128 + 68) ∨
      (sp - 128 + 96 ≤ a ∧ a < sp - 128 + 112))
      (writeLog (writeLog (writeLog (writeLog M [(sp - 128 + 64, 4, 1#64)]) [(sp - 128 + 8, 8, 1#64)])
        [(sp - 128 + 104, 8, BitVec.ofNat 64 yq)]) [(sp - 128 + 96, 8, w0)]) M := fun a ha => by
    simp only [not_or] at ha
    repeat rw [imgM_store_miss _ _ (by omega)]
  have l96 : ldv .ld (writeLog (writeLog (writeLog (writeLog M [(sp - 128 + 64, 4, 1#64)])
      [(sp - 128 + 8, 8, 1#64)]) [(sp - 128 + 104, 8, BitVec.ofNat 64 yq)]) [(sp - 128 + 96, 8, w0)])
      (sp - 128 + 96) = w0 := ldv_store_hit _ _ _
  have l104 : ldv .ld (writeLog (writeLog (writeLog (writeLog M [(sp - 128 + 64, 4, 1#64)])
      [(sp - 128 + 8, 8, 1#64)]) [(sp - 128 + 104, 8, BitVec.ofNat 64 yq)]) [(sp - 128 + 96, 8, w0)])
      (sp - 128 + 104) = BitVec.ofNat 64 yq := by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have l8 : ldv .ld (writeLog (writeLog (writeLog (writeLog M [(sp - 128 + 64, 4, 1#64)])
      [(sp - 128 + 8, 8, 1#64)]) [(sp - 128 + 104, 8, BitVec.ofNat 64 yq)]) [(sp - 128 + 96, 8, w0)])
      (sp - 128 + 8) = 1#64 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize (writeLog (writeLog (writeLog (writeLog M [(sp - 128 + 64, 4, 1#64)])
      [(sp - 128 + 8, 8, 1#64)]) [(sp - 128 + 104, 8, BitVec.ofNat 64 yq)]) [(sp - 128 + 96, 8, w0)]) = M1
    at hM1 l96 l104 l8 ⊢
  have ag1 : ∀ a, sp - 128 ≤ a → ¬ ((sp - 128 + 8 ≤ a ∧ a < sp - 128 + 16) ∨
      (sp - 128 + 64 ≤ a ∧ a < sp - 128 + 68) ∨ (sp - 128 + 96 ≤ a ∧ a < sp - 128 + 112)) →
      imgM M1 a = imgM M a := fun a _ hn => hM1 a hn
  have h1 := h.outWrite hM1 fun a ha => ⟨(above_sp hab2 (a := a) (by omega)).1,
    (above_sp hab2 (a := a) (by omega)).2.1⟩
  have hi1 := h1.heap.heap
  have l88 : ldv .ld M1 (sp - 128 + 88) = BitVec.ofNat 64 yr := by
    rw [ldv_congr .ld fun j hj => ag1 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hyr
  have hwa : ldv .ld M1 (sp - 128 + 32 + 8) = BitVec.ofNat 64 pa := by
    rw [ldv_congr .ld fun j hj => ag1 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hsa.ptr
  have hwb : ldv .ld M1 (sp - 128 + 48 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => ag1 _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hsb.ptr
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
  have e1 : R1 1 = 0x800033b0#64 := by rw [hk1.get 1 (by decide)]; bsimp []
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 128) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
  have hpc : ((upd (upd (upd (upd (upd R 17 1#64) 15 (BitVec.ofNat 64 yq)) 10 32#64) 14 w0) 1
      2147496880#64) 1) = 0x800033b0#64 := by bsimp []
  rw [hpc]
  exact binop2_first hlive h1 hp hdq hdr hsf hab hwa hwb hwr hral l96 l104 ⟨by rw [hw0]; rfl, rfl⟩ l8 l88
    R1 q1 hr10 e1
    (fun R' M' H' F' L' C' G' hk' e1' e2 elk h' hout' => hk R' M' H' F' L' C' G'
      ((hk'.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))))
      e1' e2 elk h' (out1 M' hout'))
    fun R' M' e2 hout' => hoom R' M' e2 (out1 M' hout')

end Dc.Mach
