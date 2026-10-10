import Dc.Mach.EvalFuel

/-!
# `evalstr`'s loop head: the call of `dc_func` (M10)

From the loop head (`0x800014f8`, `EvAt` over the frame `c :: rest`): the
`interrupt_seen` test, the command byte `c` and the lookahead byte (or `EOF`
at the string's end) read from the string's text, the lookahead word stored
at `sp + 28`, and the call `dc_func (c, peekc, next_negcmp)` under
`FnSpecH`. Its return (`0x80001528`, or `0x80001728` after the last
character) is the caller-supplied `EvRet`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- A string object's byte `j` read by `lbu`. -/
theorem StrAt.lbu {M : Mem} {o : StrObj} (h : StrAt M o) {j : Nat} (hj : j < o.s.length) :
    ldv .lbu M (o.tb.pay + j) = BitVec.ofNat 64 (o.s.getD j 0) := by
  rw [ldv_lbu, h.bytes j hj]
  have hc := h.byte (o.s.getD j 0) (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj)
  generalize o.s.getD j 0 = b at hc ⊢
  apply BitVec.eq_of_toNat_eq
  simp [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
  omega

/-- A string object's byte `j`. -/
theorem StrAt.img {M : Mem} {o : StrObj} (h : StrAt M o) {j : Nat} (hj : j < o.s.length) :
    imgM M (o.tb.pay + j) = BitVec.ofNat 8 (o.s.getD j 0) ∧ o.s.getD j 0 < 256 :=
  ⟨h.bytes j hj, h.byte (o.s.getD j 0) (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj)⟩

/-- **What follows `dc_func`'s return** in `evalstr` (return address `pc`):
for every outcome `code`/`st'` of the call, from the registers `R` at the
call (all but `cClob` kept) and the memory `Mc` at the call. -/
def EvRet (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (sp W : Nat) (G : DcG) (hs : List GV) (st : St) (c : Nat) (r : Res)
    (R : Nat → BitVec 64) (Mc : Mem) (pc : Nat) : Prop :=
  ∀ R' M' H' F' L' C' G' code st' ex, Keeps cClob R' R → R' 2 = R 2 →
    R' 10 = BitVec.ofNat 64 code → FnOut st r code st' →
    FnPost S (leakAllow c) (sp - 176) (W - 176) Mc G hs M' H' F' L' C' G' st' ex →
    DWO live S Q (t0 ++ Dc.outStr st'.out) (BitVec.ofNat 64 pc) R' M'



/-- The memory at `dc_func`'s call: the loop-head memory with the lookahead
word at `sp - 176 + 28`. -/
structure EvCallMem (sp : Nat) (M Mc : Mem) (w : BitVec 64) : Prop where
  only : MemOnly (fun a => sp - 176 + 28 ≤ a ∧ a < sp - 176 + 32) Mc M
  peek : ldv .lw Mc (sp - 176 + 28) = w

/-- The lookahead word `evalstr` stores (`peekc`, `EOF` at the end). -/
def peekWord : Option Nat → BitVec 64
  | some c => BitVec.ofNat 64 c
  | none => 0xFFFFFFFFFFFFFFFF#64

/-- **The call of `dc_func`** from `evalstr` (registers `Rc`, memory `Mc`
at the call): `dc_func`'s contract (`FnSpecH`) under the loop's state and
frame, its return `ret` continuing as `EvRet`. -/
theorem ev_enter {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hfn : FnSpecH live S Q) {t0 : String} {sp W d k q : Nat}
    {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs xs : List GV} {st : St} {c : Nat} {rest : List Nat} {td : Nat}
    {neg : Bool} {o : StrObj} (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨c :: rest, td, neg⟩ o)
    (hcall : CallOK st) (hoom : EvOom live S Q sp W q M0) {Rc : Nat → BitVec 64} {Mc : Mem}
    {ret : Nat} (hmem : EvCallMem sp M Mc (peekWord rest.head?))
    (h2 : Rc 2 = R 2) (h10 : Rc 10 = BitVec.ofNat 64 c) (h11 : Rc 11 = chW rest.head?)
    (h12 : Rc 12 = boolWord neg) (h1 : Rc 1 = BitVec.ofNat 64 ret) (hra : ret % 4 = 0 ∧ ret < 2 ^ 64)
    (hc : c < 256) (hpk : ∀ r, rest.head? = some r → r < 256)
    (hret : EvRet live S Q t0 sp W G (xs ++ hs) st c (dcFunc 70 st c rest.head? neg) Rc Mc ret) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000b9c#64 Rc Mc := by
  have hmc := hmem.only
  have hP : ∀ a, (sp - 176 + 28 ≤ a ∧ a < sp - 176 + 32) → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    have := above_sp (sp := sp - 176) (a := a) (by have := ev.stk; have := ev.room; simp only [heapEnd] at *; omega)
      (by omega)
    ⟨this.1, this.2.1⟩
  have hdc := ev.dc.outWrite hmc hP
  have hstk := ev.stk; have hstkPr := ev.stkPr; have hstkDn := ev.stkDn
  have hab := ev.room
  have hW1 : 176 ≤ W := by omega
  refine hfn t0 (sp - 176) (W - 176) Mc H F L C G (xs ++ hs) st c rest.head? neg _
    ⟨hdc, ev.frame.within (m := 176) (n := W - 176) (by omega) (by decide), by simp only [heapEnd] at *; omega,
      by omega, by omega, by omega, by have := ev.budget; simp only [List.length_append]; omega,
      by have := ev.budget; omega,
      ev.mb.transport fun a e1 e2 => hmc a (by simp only [mulBaseAddr, heapEnd] at e1 e2 hab; omega),
      ev.err, ev.globs.laOwn,
      by rw [ldv_congr .lw fun j hj => hmc _ (by simp only [widthOfM, heapEnd] at hj hab; omega)]
         exact ev.globs.la,
      hcall.1, hc, hpk⟩
    ⟨h2.trans ev.r2, h10, h11, h12, by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hra.2]; exact hra.1⟩ ?_ ?_
  · intro t' R' M' sp' o'
    have := o'.lo; have := o'.hi
    exact hoom t' R' M' sp' ⟨by omega, by omega, o'.r2, fun a e1 e2 e3 e4 => by
      have hq : ¬ (q ≤ a ∧ a < q + 16) := fun h => e4 (.inr h)
      have hoc : ¬ ocG a := fun h => e4 (.inl h)
      rw [o'.out a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)) hoc]
      by_cases hw : sp - 176 + 28 ≤ a ∧ a < sp - 176 + 32
      · exact absurd (by simp only [frameIn]; omega) e3
      · rw [hmc a hw]
        exact ev.out a e1 e2 hoc (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))
          (fun hf => e3 (by simp only [frameIn]; omega)) hq⟩
  · intro R' M' H' F' L' C' G' code st' ex k e2' e10 hf hp
    rw [h1]
    exact hret R' M' H' F' L' C' G' code st' ex k e2' e10 hf hp

/-- **`dc_func (c, peekc, next_negcmp)` from the loop head** of a frame
`c :: rest` with a lookahead character: the run reaches the call's return
`0x80001528` as `EvRet`, from the registers at the call (`s7 = s + 1`) and
the memory with the lookahead word stored. -/
theorem ev_call_mid {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hfn : FnSpecH live S Q) {t0 : String} {sp W d k q : Nat}
    {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs xs : List GV} {st : St} {c : Nat} {rest : List Nat} {td : Nat}
    {neg : Bool} {o : StrObj} (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨c :: rest, td, neg⟩ o)
    (h12 : R 12 = boolWord neg) (hne : rest ≠ []) (hcall : CallOK st) (hoom : EvOom live S Q sp W q M0)
    (hret : ∀ Rc Mc, Keeps [1, 10, 11, 15, 23] Rc R → Rc 23 = R 8 + 1#64 →
      EvCallMem sp M Mc (peekWord rest.head?) →
      EvRet live S Q t0 sp W G (xs ++ hs) st c (dcFunc 70 st c rest.head? neg) Rc Mc 0x80001528) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800014f8#64 R M := by
  obtain ⟨i, hi, hdrop, h8⟩ := ev.pos
  have hsf : StackFrame S sp 176 := ev.frame.mono (by have := ev.stk; omega)
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := ev.room; simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hso := ev.dc.view.strs o ev.strIn
  have bt := blk_bounds ev.dc.heap.heap (ev.dc.heap.raw.live o.tb
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ev.strIn, by simp⟩))))
  have htz := hso.tsz
  simp only [heapStart, heapEnd] at bt
  have hS : HeapOwn S := fun a e1 e2 => ev.dc.heap.heap.own a e1 e2
  have hlen : i + 1 < o.s.length := by
    have e1 : (o.s.drop i).length = rest.length + 1 := by rw [hdrop]; rfl
    have e2 : rest.length ≠ 0 := by intro h0; exact hne (List.eq_nil_of_length_eq_zero h0)
    rw [List.length_drop] at e1; omega
  have hb0 := hso.lbu (j := i) (by omega)
  have hb1 := hso.lbu (j := i + 1) hlen
  have hia : ∀ b ∈ accAddrs 2147601796 4, S b := fun b hb => by
    have := of_mem_accAddrs hb; exact ev.globs.intrOwn b (by omega) (by omega)
  have hin := ev.globs.intr
  have e2 := ev.r2
  have e9 := ev.s1
  have cs := ev.cs
  have hb1' : ldv .lbu M (o.tb.pay + i + 1) = BitVec.ofNat 64 (o.s.getD (i + 1) 0) := by
    rw [Nat.add_assoc]; exact hb1
  obtain ⟨hi1, hc1⟩ := hso.img (j := i + 1) hlen
  have hi1' : imgM (writeLog M [(sp - 176 + 28, 4, 18446744073709551615#64)]) (o.tb.pay + i + 1) =
      BitVec.ofNat 8 (o.s.getD (i + 1) 0) := by
    have hlt : o.tb.pay + i + 1 < sp - 176 := by have := bt.2.1; have := ev.stk; omega
    rw [imgM_store_miss _ _ (by omega), Nat.add_assoc]; exact hi1
  have hz1 := zext8_ofNat hc1
  have hsh := shl_shr32 (n := o.s.getD (i + 1) 0) (by omega)
  bc_run hlive hS [e2, h8, e9, hin, cs.s5] at 0x80000b9c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [e2, h8, e9, hin, cs.s5, hb0, hb1'] at 0x80000b9c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first | (intro hc; exact absurd hc (by omega)) | intro _
  bc_run hlive hS [e2, h8, e9, hin, cs.s5, hb0, hb1', hi1', hz1, hsh] at 0x80000b9c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  -- the command and the lookahead
  obtain ⟨p, rest', rfl⟩ : ∃ p rest', rest = p :: rest' := by
    cases rest with
    | nil => exact absurd rfl hne
    | cons p rest' => exact ⟨p, rest', rfl⟩
  have hgc : o.s.getD i 0 = c := by
    have := congrArg (fun l => l.getD 0 0) hdrop
    simpa [List.getD_eq_getElem?_getD] using this
  have hgp : o.s.getD (i + 1) 0 = p := by
    have := congrArg (fun l => l.getD 1 0) hdrop
    simpa [List.getD_eq_getElem?_getD, Nat.add_comm] using this
  obtain ⟨_, hc0⟩ := hso.img (j := i) (by omega)
  rw [hgc] at hc0
  rw [hgp] at hc1
  simp only [hgc, hgp]
  generalize hMc : writeLog (writeLog M [(sp - 176 + 28, 4, 18446744073709551615#64)])
    [(sp - 176 + 28, 4, BitVec.ofNat 64 p)] = Mc
  have hmc : MemOnly (fun a => sp - 176 + 28 ≤ a ∧ a < sp - 176 + 32) Mc M := fun a ha => by
    rw [← hMc, imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hpk : ldv .lw Mc (sp - 176 + 28) = BitVec.ofNat 64 p := by
    rw [← hMc]
    exact ldv_lw_hitN _ rfl (by simp only [BitVec.toNat_ofNat]; omega) (by omega)
  exact ev_enter hfn ev hcall hoom (ret := 0x80001528) ⟨hmc, hpk⟩ (by bsimp []) (by bsimp []) (by bsimp []; rfl)
    (by bsimp [h12]) (by bsimp []) (by decide) hc0 (fun r hr => by cases hr; exact hc1)
    (hret _ Mc (by keeps_tac Keeps.refl _ _) (by bsimp [h8]) ⟨hmc, hpk⟩)

/-- **`dc_func (c, EOF, next_negcmp)` from the loop head** of the last
character `c`: the return `0x80001728` as `EvRet`. -/
theorem ev_call_last {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hfn : FnSpecH live S Q) {t0 : String} {sp W d k q : Nat}
    {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs xs : List GV} {st : St} {c : Nat} {td : Nat}
    {neg : Bool} {o : StrObj} (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨[c], td, neg⟩ o)
    (h12 : R 12 = boolWord neg) (hcall : CallOK st) (hoom : EvOom live S Q sp W q M0)
    (hret : ∀ Rc Mc, Keeps [1, 10, 11, 15, 23] Rc R → Rc 23 = R 8 + 1#64 →
      EvCallMem sp M Mc (peekWord none) →
      EvRet live S Q t0 sp W G (xs ++ hs) st c (dcFunc 70 st c none neg) Rc Mc 0x80001728) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800014f8#64 R M := by
  obtain ⟨i, hi, hdrop, h8⟩ := ev.pos
  have hsf : StackFrame S sp 176 := ev.frame.mono (by have := ev.stk; omega)
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := ev.room; simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hso := ev.dc.view.strs o ev.strIn
  have bt := blk_bounds ev.dc.heap.heap (ev.dc.heap.raw.live o.tb
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ev.strIn, by simp⟩))))
  have htz := hso.tsz
  simp only [heapStart, heapEnd] at bt
  have hS : HeapOwn S := fun a e1 e2 => ev.dc.heap.heap.own a e1 e2
  have hlen : i + 1 = o.s.length := by
    have e1 : (o.s.drop i).length = 1 := by rw [hdrop]; rfl
    rw [List.length_drop] at e1; omega
  have hb0 := hso.lbu (j := i) (by omega)
  have hia : ∀ b ∈ accAddrs 2147601796 4, S b := fun b hb => by
    have := of_mem_accAddrs hb; exact ev.globs.intrOwn b (by omega) (by omega)
  have hin := ev.globs.intr
  have e2 := ev.r2
  have e9 := ev.s1
  have cs := ev.cs
  bc_run hlive hS [e2, h8, e9, hin, cs.s5] at 0x80000b9c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [e2, h8, e9, hin, cs.s5, hb0] at 0x80000b9c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first | (intro hc; exact absurd hc (by omega)) | intro _
  bc_run hlive hS [e2, h8, e9, hin, cs.s5, hb0] at 0x80000b9c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hgc : o.s.getD i 0 = c := by
    have := congrArg (fun l => l.getD 0 0) hdrop
    simpa [List.getD_eq_getElem?_getD] using this
  obtain ⟨_, hc0⟩ := hso.img (j := i) (by omega)
  rw [hgc] at hc0
  simp only [hgc]
  generalize hMc : writeLog M [(sp - 176 + 28, 4, 18446744073709551615#64)] = Mc
  have hmc : MemOnly (fun a => sp - 176 + 28 ≤ a ∧ a < sp - 176 + 32) Mc M := fun a ha => by
    rw [← hMc, imgM_store_miss _ _ (by omega)]
  have hpk : ldv .lw Mc (sp - 176 + 28) = peekWord none := by
    rw [← hMc, ldv_lw_hit _ _ rfl]; decide
  exact ev_enter hfn ev hcall hoom (ret := 0x80001728) ⟨hmc, hpk⟩ (by bsimp []) (by bsimp []) (by bsimp []; rfl)
    (by bsimp [h12]) (by bsimp []) (by decide) hc0 (fun r hr => by cases hr)
    (hret _ Mc (by keeps_tac Keeps.refl _ _) (by bsimp [h8]) ⟨hmc, hpk⟩)

end Dc.Mach
