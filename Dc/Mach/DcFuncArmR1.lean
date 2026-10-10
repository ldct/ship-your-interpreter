import Dc.Mach.DcFuncPop
import Dc.Mach.DcNum2Int

/-!
# `dc_func`'s arms that pop an integer into a scalar (M10)

`i`, `k`, `o` and `Q` pop a datum (`fn_pop`); a number goes through
`dc_num2int` (`fn_n2i`) and, when in range, into `dc_ibase`, `dc_scale`,
`dc_obase` or `unwind_depth` (`DcAt.setScalars`); out of range, or a string
(whose handle the arm loses: `ex = [g]`), the message goes to `stderr`
(`fn_msg`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `dc_num2int`'s value is an `int`. -/
theorem Num.toInt_range (n : Num) : -2 ^ 31 ≤ (Num.toInt n).1 ∧ (Num.toInt n).1 < 2 ^ 31 := by
  simp only [Num.toInt, Num.toInt32]
  split
  · decide
  · split <;> omega

/-- A popped handle denoting `v`: a number of `L` or a string of `ss`. -/
theorem GV.den_cases {O : DObjs} {g : GV} {v : Val} (h : g.Den O v) :
    (∃ x ∈ O.L, g = .num x.rep.p ∧ v = .num x.rep.num) ∨
      (∃ o ∈ O.ss, g = .str o.hb.pay ∧ v = .str o.s) := by
  cases g <;> cases v <;> simp only [GV.Den] at h
  · obtain ⟨x, hx, rfl, rfl⟩ := h; exact .inl ⟨x, hx, rfl, rfl⟩
  · obtain ⟨o, ho, rfl, rfl⟩ := h; exact .inr ⟨o, ho, rfl, rfl⟩

theorem ite_T {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} : (if c then a else b) = a := by
  simp [h]

theorem ite_F {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} : (if c then a else b) = b := by
  simp [h]

theorem St.push_pop (st : St) (v : Val) : { st.push v with stack := st.stack } = st := by
  cases st; rfl

/-- `bltz`/`blez` on `dc_num2int`'s word. -/
theorem toInt_n2i (n : Num) : (BitVec.ofInt 64 n.toInt.1).toInt = n.toInt.1 :=
  BitVec.toInt_ofInt_eq_self (by decide) (by have := Num.toInt_range n; omega)
    (by have := Num.toInt_range n; omega)

/-- `sw` of a nonnegative `int`. -/
theorem ofInt_mod32 {t : Int} (h0 : 0 ≤ t) (h1 : t < 2 ^ 31) :
    (BitVec.ofInt 64 t).toNat % 2 ^ 32 = t.toNat := by
  rw [BitVec.toNat_ofInt]; omega

/-- `dc_scale` stored. -/
theorem DcAt.setScale {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {v : BitVec 64} {k : Nat} (hv : v.toNat % 2 ^ 32 = k) (hk : k < 2 ^ 31) :
    DcAt S (writeLog M [(scaleAddr, 4, v)]) H F L C G hs { st with scale := k } := by
  have hm : MemOnly ScalarWord (writeLog M [(scaleAddr, 4, v)]) M := fun a ha => by
    simp only [ScalarWord, dc_addrs, not_or] at ha
    exact imgM_store_miss _ _ (by simp only [dc_addrs]; omega)
  have w := h.view
  have h' := h.setScalars hm (i := st.ibase) (o := st.obase) (k := k) (u := st.unwind) (n := st.noexit)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.ibase)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.obase)
    (ldv_lw_hitN _ rfl hv hk)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.unwind)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.noexit)
    h.den.ibase h.den.obase hk h.den.unwind
  cases st; exact h'

/-- `dc_ibase` stored. -/
theorem DcAt.setIbase {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {v : BitVec 64} {k : Nat} (hv : v.toNat % 2 ^ 32 = k) (hk : 2 ≤ k ∧ k ≤ 16) :
    DcAt S (writeLog M [(ibaseAddr, 4, v)]) H F L C G hs { st with ibase := k } := by
  have hm : MemOnly ScalarWord (writeLog M [(ibaseAddr, 4, v)]) M := fun a ha => by
    simp only [ScalarWord, dc_addrs, not_or] at ha
    exact imgM_store_miss _ _ (by simp only [dc_addrs]; omega)
  have w := h.view
  have h' := h.setScalars hm (i := k) (o := st.obase) (k := st.scale) (u := st.unwind) (n := st.noexit)
    (ldv_lw_hitN _ rfl hv (by omega))
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.obase)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.scale)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.unwind)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.noexit)
    hk h.den.obase h.den.scale h.den.unwind
  cases st; exact h'

/-- `dc_obase` stored. -/
theorem DcAt.setObase {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {v : BitVec 64} {k : Nat} (hv : v.toNat % 2 ^ 32 = k) (hk : 2 ≤ k ∧ k < 2 ^ 31) :
    DcAt S (writeLog M [(obaseAddr, 4, v)]) H F L C G hs { st with obase := k } := by
  have hm : MemOnly ScalarWord (writeLog M [(obaseAddr, 4, v)]) M := fun a ha => by
    simp only [ScalarWord, dc_addrs, not_or] at ha
    exact imgM_store_miss _ _ (by simp only [dc_addrs]; omega)
  have w := h.view
  have h' := h.setScalars hm (i := st.ibase) (o := k) (k := st.scale) (u := st.unwind) (n := st.noexit)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.ibase)
    (ldv_lw_hitN _ rfl hv hk.2)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.scale)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.unwind)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.noexit)
    h.den.ibase hk h.den.scale h.den.unwind
  cases st; exact h'

/-- `i`'s message `"%s: input base must be a number between 2 and %d (inclusive)\n"`
at `0x800079f8`, as pieces. -/
def iPieces : List Piece :=
  .conv false false .s :: (lits (msgBytes 0x800079fa 44) ++ .conv false false .d :: lits (msgBytes 0x80007a28 13))

/-- `i`'s arguments: `progname` and `16`. -/
def iArgs : List FArg := [progArg, ⟨16#64, []⟩]

theorem argStrs_lits_append (bs : List (BitVec 8)) (ps : List Piece) (args : List FArg)
    (h : ArgStrs ps args) : ArgStrs (lits bs ++ ps) args := by
  induction bs with
  | nil => exact h
  | cons b bs ih => simp only [lits, List.map_cons, List.cons_append, ArgStrs]; exact ih

theorem lits_ok (bs : List (BitVec 8)) (h : ∀ b ∈ bs, b ≠ 0#8 ∧ b ≠ 37#8) : ∀ pc ∈ lits bs, pc.ok := by
  intro pc hpc
  simp only [lits, List.mem_map] at hpc
  obtain ⟨b, hb, rfl⟩ := hpc
  exact h b hb

set_option maxRecDepth 100000 in
theorem iPieces_ro : RoBytes 0x800079f8 (fmtBytes iPieces ++ [0#8]) := by
  rw [show fmtBytes iPieces = msgBytes 0x800079f8 61 by decide +kernel]
  exact roBytes_msg 61 _ (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem iPieces_ok : ∀ pc ∈ iPieces, pc.ok := by
  intro pc hpc
  simp only [iPieces, List.mem_cons, List.mem_append] at hpc
  rcases hpc with rfl | hpc | rfl | hpc
  · trivial
  · exact lits_ok _ (by decide) pc hpc
  · trivial
  · exact lits_ok _ (by decide) pc hpc

theorem iPieces_args : ArgStrs iPieces iArgs :=
  ⟨dcName_str, argStrs_lits_append _ _ _ (argStrs_lits _ _)⟩

set_option maxRecDepth 100000 in
theorem iPieces_len : (fmt iPieces iArgs).length + 1 < 2 ^ 62 := by decide +kernel

/-- `unwind_depth` stored. -/
theorem DcAt.setUnwind {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {v : BitVec 64} {k : Nat} (hv : v.toNat % 2 ^ 32 = k) (hk : k < 2 ^ 31) :
    DcAt S (writeLog M [(unwindAddr, 4, v)]) H F L C G hs { st with unwind := k } := by
  have hm : MemOnly ScalarWord (writeLog M [(unwindAddr, 4, v)]) M := fun a ha => by
    simp only [ScalarWord, dc_addrs, not_or] at ha
    exact imgM_store_miss _ _ (by simp only [dc_addrs]; omega)
  have w := h.view
  have h' := h.setScalars hm (i := st.ibase) (o := st.obase) (k := st.scale) (u := k) (n := st.noexit)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.ibase)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.obase)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.scale)
    (ldv_lw_hitN _ rfl hv hk)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.noexit)
    h.den.ibase h.den.obase h.den.scale hk
  cases st; exact h'

/-- `unwind_depth` rewritten by stores confined to its word. -/
theorem DcAt.setUnwind' {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    (hm : MemOnly (fun a => unwindAddr ≤ a ∧ a < unwindAddr + 4) M' M) {k : Nat}
    (hv : ldv .lw M' unwindAddr = BitVec.ofNat 64 k) (hk : k < 2 ^ 31) :
    DcAt S M' H F L C G hs { st with unwind := k } := by
  have hm' : MemOnly ScalarWord M' M := fun a ha => hm a fun hw => ha (by
    simp only [ScalarWord]; omega)
  have w := h.view
  have gw : ∀ (a : Nat), a + 4 ≤ unwindAddr ∨ unwindAddr + 4 ≤ a → ldv .lw M' a = ldv .lw M a :=
    fun a ha => ldv_congr .lw fun j hj => hm _ (by simp only [widthOfM] at hj; omega)
  have h' := h.setScalars hm' (i := st.ibase) (o := st.obase) (k := st.scale) (u := k) (n := st.noexit)
    ((gw _ (by simp only [dc_addrs]; omega)).trans w.ibase)
    ((gw _ (by simp only [dc_addrs]; omega)).trans w.obase)
    ((gw _ (by simp only [dc_addrs]; omega)).trans w.scale) hv
    ((gw _ (by simp only [dc_addrs]; omega)).trans w.noexit)
    h.den.ibase h.den.obase h.den.scale hk
  cases st; exact h'

/-- `unwind_noexit` stored. -/
theorem DcAt.setNoexit {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {v : BitVec 64} {n : Bool} (hv : v.toNat % 2 ^ 32 = n.toNat) :
    DcAt S (writeLog M [(noexitAddr, 4, v)]) H F L C G hs { st with noexit := n } := by
  have hm : MemOnly ScalarWord (writeLog M [(noexitAddr, 4, v)]) M := fun a ha => by
    simp only [ScalarWord, dc_addrs, not_or] at ha
    exact imgM_store_miss _ _ (by simp only [dc_addrs]; omega)
  have w := h.view
  have h' := h.setScalars hm (i := st.ibase) (o := st.obase) (k := st.scale) (u := st.unwind) (n := n)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.ibase)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.obase)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.scale)
    (by rw [ldv_store_miss _ _ _ (by simp only [dc_addrs, widthOfM]; omega)]; exact w.unwind)
    (by rw [ldv_lw_hitN _ rfl hv (by cases n <;> decide)]; try (cases n <;> rfl))
    h.den.ibase h.den.obase h.den.scale h.den.unwind
  cases st; exact h'

/-- A doubleword stored at `o` of `dc_func`'s frame (below the saved `ra`). -/
theorem FnAt.store {S : Nat → Prop} {sp W : Nat} {M0 M : Mem} {R0 R : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) {o : Nat} (ho : o + 8 ≤ 184) (v : BitVec 64) :
    FnAt S sp W M0 R0 R (writeLog M [(sp - 192 + o, 8, v)]) := by
  have hl := hc.frame.lo; have hb := hc.big
  refine { hc with ra := ?_, out := fun a e1 e2 e3 e4 => ?_ }
  · rw [ldv_ld_miss _ _ (by omega)]; exact hc.ra
  · rw [imgM_store_miss _ _ (by simp only [frameIn] at e4; omega)]; exact hc.out a e1 e2 e3 e4

/-- The state through a store into `dc_func`'s frame. -/
theorem DcAt.fnStore {S : Nat → Prop} {sp W : Nat} {M0 M : Mem} {R0 R : Nat → BitVec 64}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (o : Nat) (v : BitVec 64) :
    DcAt S (writeLog M [(sp - 192 + o, 8, v)]) H F L C G hs st :=
  h.outWrite (MemOnly.store M _ 8 v) fun a ha =>
    have hh := hc.room
    have hb := hc.big
    have := above_sp (sp := sp - 192) (by simp only [heapEnd] at hh ⊢; omega) (a := a) (by omega)
    ⟨this.1, this.2.1⟩

/-- A frame word above `sp - 192` through a callee's `StkOut`. -/
theorem FnAt.ldKeep {S : Nat → Prop} {sp W : Nat} {M0 M M' : Mem} {R0 R : Nat → BitVec 64}
    (hc : FnAt S sp W M0 R0 R M) {Wc o : Nat} (hout : StkOut (sp - 192) Wc M' M) :
    ldv .ld M' (sp - 192 + o) = ldv .ld M (sp - 192 + o) := by
  have hh := hc.room
  have hb := hc.big
  have hab : heapEnd ≤ sp - 192 := by simp only [heapEnd] at hh ⊢; omega
  exact ldv_congr .ld fun j _ => by
    have := above_sp hab (a := sp - 192 + o + j) (by omega)
    exact hout _ this.1 this.2.1 (this.2.2 _)

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 t : String} {st : St} {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
  {G : DcG} {hs : List GV} {sp W : Nat} {R0 R : Nat → BitVec 64} {peek : Option Nat} {neg : Bool}

/-- **`dc_num2int (datum.v.number, DC_TOSS)`** from `dc_func`'s frame: the
handle at the head of the handles released, `a0` the value. -/
theorem fn_n2i (hlive : ∀ p ∈ dcText, live p.1) {x : NumObj}
    (h : DcAt S M H F L C G (.num x.rep.p :: hs) st) (hx : x ∈ L)
    (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (h10 : R 10 = BitVec.ofNat 64 x.rep.p) (h11 : R 11 = 0#64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps cClob R' R → FnAt S sp W M0 R0 R' M' →
      R' 10 = BitVec.ofInt 64 x.rep.num.toInt.1 → DcAt S M' H' F' L' C' G hs st →
      StkOut (sp - 192) 336 M' M → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80002648#64 R M :=
  dc_num2int_spec (keep := false) hlive h (fun _ => rfl) hx (hc.cf (by omega)) (hc.cab (by omega))
    R hc.r2 h10 (by rw [h11]; rfl) hal fun R' M' H' F' L' C' k e2 e10 h' hout =>
    hk R' M' H' F' L' C' k (hc.callS (Wc := 336) (by omega) (k.mono (by decide)) e2 hout) e10 h' hout

/-- **`fprintf (stderr, msg, progname)`** from `dc_func`'s frame (`msg` a
`ProgMsg`): the state and the frame kept. -/
theorem fn_msg (hlive : ∀ p ∈ dcText, live p.1) {p n : Nat} (hm : ProgMsg p n) (hn : n < 2 ^ 60)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 304 ≤ W)
    (h10 : (R 10).toNat = stderrAddr) (h11 : (R 11).toNat = p)
    (h12 : R 12 = BitVec.ofNat 64 dcNameAddr) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps fprintfClob R' R → FnAt S sp W M0 R0 R' M' → DcAt S M' H F L C G hs st →
      DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80000774#64 R M := by
  have hab := hc.cab (Wc := 304) hW
  have hsl := hc.frame.lo
  have hsh := hc.frame.hi
  refine fprintf_prog_spec hlive hm hn (hc.cf hW) (by simp only [stderrAddr, heapEnd] at hab ⊢; omega)
    h.errFile R (by rw [hc.r2, BitVec.toNat_ofNat]; omega) h10 h11 h12 hal fun R' M' k hout => ?_
  have hm' : MemOnly (frameIn (sp - 192) 304) M' M := fun a ha =>
    hout a (by simp only [frameIn] at ha; omega)
  refine hk R' M' k (hc.call (Wc := 304) hW (k.mono (by decide)) (k.get 2 (by decide))
    fun a _ _ _ e4 => hm' a e4) (h.outWrite hm' fun a ha => ?_)
  have := above_sp (sp := sp - 192 - 304) (a := a) (by simp only [heapEnd] at hab ⊢; omega)
    (by simp only [frameIn] at ha; omega)
  exact ⟨this.1, this.2.1⟩

/-- **`i`'s `fprintf (stderr, msg, progname, 16)`** from `dc_func`'s frame. -/
theorem fn_msgI (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 304 ≤ W)
    (h10 : (R 10).toNat = stderrAddr) (h11 : (R 11).toNat = 0x800079f8)
    (h12 : R 12 = BitVec.ofNat 64 dcNameAddr) (h13 : R 13 = 16#64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps fprintfClob R' R → FnAt S sp W M0 R0 R' M' → DcAt S M' H F L C G hs st →
      DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80000774#64 R M := by
  have hab := hc.cab (Wc := 304) hW
  have hsl := hc.frame.lo
  have hsh := hc.frame.hi
  refine fprintf_spec (ps := iPieces) (args := iArgs) hlive (hc.cf hW) h.errFile
    (.inl (by simp only [stderrAddr, heapEnd] at hab ⊢; omega)) iPieces_ok iPieces_ro iPieces_args
    iPieces_len R (by decide) (fun i hi => by
      simp only [iArgs, List.length_cons, List.length_nil] at hi
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl
      · exact h12.symm
      · exact h13.symm)
    (by rw [hc.r2, BitVec.toNat_ofNat]; omega) h10 h11 hal fun R' M' k _ hout => ?_
  rw [show t ++ fdOut 2 (bytesStr (fmt iPieces iArgs)) = t by simp [fdOut]]
  have hm' : MemOnly (frameIn (sp - 192) 304) M' M := fun a ha =>
    hout a (by simp only [frameIn] at ha; omega)
  refine hk R' M' k (hc.call (Wc := 304) hW (k.mono (by decide)) (k.get 2 (by decide))
    fun a _ _ _ e4 => hm' a e4) (h.outWrite hm' fun a ha => ?_)
  have := above_sp (sp := sp - 192 - 304) (a := a) (by simp only [heapEnd] at hab ⊢; omega)
    (by simp only [frameIn] at ha; omega)
  exact ⟨this.1, this.2.1⟩

/-- **A message, then `DC_OKAY`**: `fprintf` returning to a `j 0x80000c10`
at `ret`. -/
theorem fn_msg_ok (hlive : ∀ p ∈ dcText, live p.1) {p n ret code : Nat} (hm : ProgMsg p n)
    (hn : n < 2 ^ 60) {st' : St} {G' : DcG} {ex : List GV} {r : Res}
    (h : DcAt S M H F L C G' (ex ++ hs) st') (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 304 ≤ W)
    (hk : FnK live S Q t0 st r G hs sp W M0 R0) (hf : FnOut st r code st') (hc0 : code = 0)
    (hex : ex.length ≤ 2) (hlk : G'.lk.length ≤ G.lk.length + 2) (hpin : StrPin G.strs G'.strs hs)
    (h10 : (R 10).toNat = stderrAddr) (h11 : (R 11).toNat = p)
    (h12 : R 12 = BitVec.ofNat 64 dcNameAddr) (h1 : R 1 = BitVec.ofNat 64 ret)
    (hret : ret % 4 = 0 ∧ ret < 2 ^ 64) (hj : JAt live S Q ret 0x80000c10) :
    DWO live S Q (t0 ++ Dc.outStr st'.out) 0x80000774#64 R M := by
  subst hc0
  refine fn_msg hlive hm hn h hc hW h10 h11 h12
    (by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hret.2]; exact hret.1) fun R' M' _ hc' h' => ?_
  rw [h1]
  exact hj _ R' M' (fa_ok hlive h' hc' hk hf hex hlk hpin)

set_option hygiene false in
/-- The `jal dc_pop` / `bnez a0, 0x80000c10` pair of an arm (`q` the address after the branch). -/
macro "fr_pop_sites " q:num : tactic =>
  `(tactic| (
    · intro t R M k
      have htx : tohostAddr = 0x8001ad00 := rfl
      bc_run hlive hlive [] at 0x8000310c
      exact k _ (by keeps_tac Keeps.refl _ _) (by bsimp [])
    · refine BnezAt.of_step fun t R M k1 k2 => ?_
      simp only [Nat.reduceAdd] at k1 k2 ⊢
      have htx : tohostAddr = 0x8001ad00 := rfl
      bc_run hlive hlive [] at 0x80000c10 $q
      all_goals first | exact k1 | exact k2))

/-- A `j 0x80000c10` site. -/
theorem jat_c10 {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {p : Nat}
    (hp : (p = 0x80000e74 ∨ p = 0x80000eb0 ∨ p = 0x80001124 ∨ p = 0x800010a4)) :
    JAt live S Q p 0x80000c10 := fun t R M k => by
  have htx : tohostAddr = 0x8001ad00 := rfl
  rcases hp with rfl | rfl | rfl | rfl <;> (bc_run hlive hlive [] at 0x80000c10; exact k)

theorem kMsg : ProgMsg 0x80007a38 37 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

/-- **A popping arm's number route** at `pc` (after the `bnez`): the
number `x` popped from `st` into the slot, its handle held. -/
def PopNumK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (st : St) (r : Res) (G : DcG) (hs : List GV) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (sp W : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (pc : BitVec 64) : Prop :=
  ∀ R' M' H' (G' : DcG) (x : NumObj) st', st = st'.push (.num x.rep.num) →
    G.lk = G'.lk → G.strs = G'.strs → x ∈ L → FnAt S sp W M0 R0 R' M' →
    DcAt S M' H' F L C G' (.num x.rep.p :: hs) st' →
    ldv .lw M' (sp - 192 + 16) = BitVec.ofNat 64 1 →
    ldv .ld M' (sp - 192 + 24) = BitVec.ofNat 64 x.rep.p →
    FnK live S Q t0 st r G hs sp W M0 R0 →
    DWO live S Q (t0 ++ Dc.outStr st.out) pc R' M'

/-- **A popping arm's string route** at `pc`: the string `o` popped. -/
def PopStrK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t0 : String) (st : St) (r : Res) (G : DcG) (hs : List GV) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (sp W : Nat) (M0 : Mem) (R0 : Nat → BitVec 64) (pc : BitVec 64) : Prop :=
  ∀ R' M' H' (G' : DcG) (o : StrObj) st', st = st'.push (.str o.s) →
    G.lk = G'.lk → G.strs = G'.strs → o ∈ G'.strs → FnAt S sp W M0 R0 R' M' →
    DcAt S M' H' F L C G' (.str o.hb.pay :: hs) st' →
    ldv .lw M' (sp - 192 + 16) = BitVec.ofNat 64 2 →
    ldv .ld M' (sp - 192 + 24) = BitVec.ofNat 64 o.hb.pay →
    FnK live S Q t0 st r G hs sp W M0 R0 →
    DWO live S Q (t0 ++ Dc.outStr st.out) pc R' M'

/-- **An arm that pops a datum** (`dc_pop` called at `p`, `bnez` to
`DC_OKAY`): the empty stack returns `DC_OKAY` with the state; a number or
a string popped continues at `p + 8` with the datum's words in the slot. -/
theorem fn_pop_arm (hlive : ∀ p ∈ dcText, live p.1) {p : Nat} {r : Res}
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (h10 : R 10 = BitVec.ofNat 64 (fnSlot sp)) (hp : (p + 4) % 4 = 0 ∧ p + 4 < 2 ^ 64)
    (hj : JalAt live S Q p 0x8000310c) (hb : BnezAt live S Q (p + 4) 0x80000c10)
    (hnil : st.stack = [] → r = .ok st) (hk : FnK live S Q t0 st r G hs sp W M0 R0)
    (hnum : PopNumK live S Q t0 st r G hs F L C sp W M0 R0 (BitVec.ofNat 64 (p + 8)))
    (hstr : PopStrK live S Q t0 st r G hs F L C sp W M0 R0 (BitVec.ofNat 64 (p + 8))) :
    DWO live S Q (t0 ++ Dc.outStr st.out) (BitVec.ofNat 64 p) R M := by
  refine fn_pop hlive h hc hW h10 hp hj hb (fun he R' M' hc' h' => ?_)
    fun R' M' H' G' g v st' est eG hc' h' hv hd => ?_
  · rw [hnil he] at hk
    exact fa_ok hlive (ex := []) h' hc' hk (.ok _) (by simp) (by omega) (StrPin.refl _ _)
  · obtain ⟨c, rfl⟩ := eG
    have htg := hd.lw
    have hpt := hd.ptr
    rcases GV.den_cases hv with ⟨x, hx, rfl, rfl⟩ | ⟨o, ho, rfl, rfl⟩
    · exact hnum R' M' H' G' x st' est rfl rfl hx hc' h' htg hpt hk
    · exact hstr R' M' H' G' o st' est rfl rfl ho hc' h' htg hpt hk

/-- Stores to a scalar word only. -/
theorem scalar_store (M : Mem) (v : BitVec 64) {a : Nat}
    (ha : a = ibaseAddr ∨ a = obaseAddr ∨ a = scaleAddr ∨ a = unwindAddr ∨ a = noexitAddr) :
    MemOnly ScalarWord (writeLog M [(a, 4, v)]) M := fun b hb => by
  simp only [ScalarWord, not_or] at hb
  exact imgM_store_miss _ _ (by rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega)

set_option hygiene false in
/-- An arm's start: the frame's bounds, then `a0 = sp + 16` up to the call. -/
macro "fr_pre " q:num : tactic =>
  `(tactic| (
    have htx : tohostAddr = 0x8001ad00 := rfl
    have hsl := hc.frame.lo; have hsh := hc.frame.hi; have hbig := hc.big; have hroom := hc.room
    have e2 := hc.r2
    bc_run hlive hlive [e2] at $q))

set_option hygiene false in
/-- The facts a popped arm's straight-line code needs. -/
macro "fr_ctx" : tactic =>
  `(tactic| (
    have hS : HeapOwn S := fun a e1 e2 => h'.heap.heap.own a e1 e2
    have hpn := h'.view.prog
    have hG := h'.glob
    have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
    have e2' := hc'.r2
    have hsf : StackFrame S sp 192 := hc'.frame.mono hc'.big
    have htx : tohostAddr = 0x8001ad00 := rfl
    have hsl := hc'.frame.lo; have hsh := hc'.frame.hi; have hbig := hc'.big
    have hroom := hc'.room))

set_option hygiene false in
/-- The facts after `dc_num2int`. -/
macro "fr_n2i_ctx" : tactic =>
  `(tactic| (
    have hti := toInt_n2i x.rep.num
    have hrg := Num.toInt_range x.rep.num
    have hpn2 := h2.view.prog
    have hg2 := h2.glob))

set_option hygiene false in
/-- Global stores' ownership side conditions. -/
macro "fr_glob" : tactic =>
  `(tactic| (all_goals first
    | (intro b hb; have := of_mem_accAddrs hb; exact hg2 b (by simp only [DcGlob, dc_addrs]; omega))
    | skip))

theorem dcFunc_k_nil (he : st.stack = []) : dcFunc 70 st 107 peek neg = .ok st := by
  obtain ⟨stk⟩ := st; simp only at he; subst he; rfl

theorem dcFunc_k_cons (st : St) (v : Val) : dcFunc 70 (st.push v) 107 peek neg =
    .ok (if 0 ≤ valInt (-1) v then { st with scale := (valInt (-1) v).toNat } else st) := by
  cases st; rfl

theorem fk_num (hlive : ∀ p ∈ dcText, live p.1) (hW : 192 + 336 ≤ W) :
    PopNumK live S Q t0 st (dcFunc 70 st 107 peek neg) G hs F L C sp W M0 R0 0x80000e4c#64 := by
  intro R' M' H' G' x st' est elk estr hx hc' h' htg hpt hk
  subst est
  rw [dcFunc_k_cons] at hk
  fr_ctx
  bc_run hlive hS [e2', htg, hpt] at 0x80002648
  all_goals try exact frame_acc hsf (by omega) (by omega)
  bc_run hlive hS [e2', htg, hpt] at 0x80002648
  all_goals try exact frame_acc hsf (by omega) (by omega)
  refine fn_n2i hlive h' hx (hc'.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by bsimp [])
    (by bsimp []) (by bsimp []) fun R2 M2 H2 F2 L2 C2 k2 hc2 e10 h2 _ => ?_
  bsimp []
  fr_n2i_ctx
  bc_run hlive hS [e10, hti, BitVec.toInt_zero] at 0x80000e58 0x80000c10
  · intro hlt
    rw [ite_F (by simp only [valInt]; omega)] at hk
    bc_run hlive hS [hpn2, stderr_word] at 0x80000774
    exact fn_msg_ok (st' := st') (ret := 0x80000e74) hlive kMsg (by decide) (ex := []) h2
      (hc2.mod (by keeps_tac Keeps.refl _ _)) (by omega) hk (.ok _) rfl (by simp) (by simp [elk])
      (StrPin.of_eq estr.symm _) (by bsimp []; decide) (by bsimp []) (by bsimp []) (by bsimp []) (by decide)
      (jat_c10 hlive (by decide))
  · intro hge
    rw [ite_T (by simp only [valInt]; omega)] at hk
    bc_run hlive hS [e10] at 0x80000c10
    fr_glob
    exact fa_ok (st' := { st' with scale := x.rep.num.toInt.1.toNat }) hlive (ex := [])
      (h2.setScale (ofInt_mod32 (by omega) hrg.2) (by omega)) (hc2.scalars (by keeps_tac Keeps.refl _ _)
        (scalar_store _ _ (by decide))) hk (.ok _) (by simp) (by simp [elk]) (StrPin.of_eq estr.symm _)

theorem fk_str (hlive : ∀ p ∈ dcText, live p.1) (hW : 192 + 336 ≤ W) :
    PopStrK live S Q t0 st (dcFunc 70 st 107 peek neg) G hs F L C sp W M0 R0 0x80000e4c#64 := by
  intro R' M' H' G' o st' est elk estr ho hc' h' htg _ hk
  subst est
  rw [dcFunc_k_cons] at hk
  fr_ctx
  bc_run hlive hS [e2', htg, hpn, stderr_word] at 0x80000774
  all_goals try exact frame_acc hsf (by omega) (by omega)
  bc_run hlive hS [e2', htg, hpn, stderr_word] at 0x80000774
  all_goals try exact frame_acc hsf (by omega) (by omega)
  rw [ite_F (by simp only [valInt]; omega)] at hk
  exact fn_msg_ok (st' := st') (ret := 0x80000e74) hlive kMsg (by decide) (ex := [_]) h'
    (hc'.mod (by keeps_tac Keeps.refl _ _)) (by omega) hk (.ok _) rfl (by simp) (by simp [elk])
    (StrPin.of_eq estr.symm _) (by bsimp []; decide) (by bsimp []) (by bsimp []) (by bsimp []) (by decide)
    (jat_c10 hlive (by decide))

/-- `k` (`0x80000e40`): pop, `dc_num2int`, `dc_scale` when nonnegative. -/
theorem fa_k (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (hk : FnK live S Q t0 st (dcFunc 70 st 107 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000e40#64 R M := by
  fr_pre 0x80000e44
  refine fn_pop_arm (p := 0x80000e44) hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hW (by bsimp [])
    (by decide) ?_ ?_ dcFunc_k_nil hk (fk_num hlive hW) (fk_str hlive hW)
  fr_pop_sites 0x80000e4c

/-- `addi`/`addiw` of a negative immediate `-k` (the word `K`) to an `int`. -/
theorem ofInt_addK {t : Int} {K k : Nat} (hK : K + k = 2 ^ 64) :
    BitVec.ofInt 64 t + BitVec.ofNat 64 K = BitVec.ofInt 64 (t - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-- `i`'s range test (`addiw a4, a0, -2; bltu 14, a4`). -/
theorem i_range {t : Int} (h1 : -2 ^ 31 ≤ t) (h2 : t < 2 ^ 31) :
    14 < (BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (BitVec.ofInt 64 t + 18446744073709551614#64))).toNat ↔ ¬ (2 ≤ t ∧ t ≤ 16) := by
  rw [ofInt_addK (k := 2) (by decide), sxw_ofInt, BitVec.toNat_ofInt]
  simp only [Dc.Num.toInt32]
  split <;> omega

theorem dcFunc_i_nil (he : st.stack = []) : dcFunc 70 st 105 peek neg = .ok st := by
  obtain ⟨stk⟩ := st; simp only at he; subst he; rfl

theorem dcFunc_i_cons (st : St) (v : Val) : dcFunc 70 (st.push v) 105 peek neg =
    .ok (if 2 ≤ valInt 0 v && valInt 0 v ≤ 16 then { st with ibase := (valInt 0 v).toNat } else st) := by
  cases st; rfl

theorem fi_num (hlive : ∀ p ∈ dcText, live p.1) (hW : 192 + 336 ≤ W) :
    PopNumK live S Q t0 st (dcFunc 70 st 105 peek neg) G hs F L C sp W M0 R0 0x80000e84#64 := by
  intro R' M' H' G' x st' est elk estr hx hc' h' htg hpt hk
  subst est
  rw [dcFunc_i_cons] at hk
  fr_ctx
  bc_run hlive hS [e2', htg, hpt] at 0x80002648
  all_goals try exact frame_acc hsf (by omega) (by omega)
  bc_run hlive hS [e2', htg, hpt] at 0x80002648
  all_goals try exact frame_acc hsf (by omega) (by omega)
  refine fn_n2i hlive h' hx (hc'.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by bsimp [])
    (by bsimp []) (by bsimp []) fun R2 M2 H2 F2 L2 C2 k2 hc2 e10 h2 _ => ?_
  bsimp []
  fr_n2i_ctx
  bc_run hlive hS [e10] at 0x80000e90 0x80000c10
  · intro hlt
    rw [i_range hrg.1 hrg.2] at hlt
    rw [ite_F (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hlt)] at hk
    generalize BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (BitVec.ofInt 64 x.rep.num.toInt.1 + 18446744073709551614#64)) = w14
    bc_run hlive hS [hpn2, stderr_word] at 0x80000774
    refine fn_msgI hlive h2 (hc2.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by bsimp []; decide)
      (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) fun R3 M3 k3 hc3 h3 => ?_
    bsimp []
    exact jat_c10 hlive (by decide) _ R3 M3 (fa_ok (st' := st') hlive (ex := []) h3 hc3 hk (.ok _)
      (by simp) (by simp [elk]) (StrPin.of_eq estr.symm _))
  · intro hge
    rw [i_range hrg.1 hrg.2, Classical.not_not] at hge
    rw [ite_T (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hge)] at hk
    generalize BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (BitVec.ofInt 64 x.rep.num.toInt.1 + 18446744073709551614#64)) = w14
    bc_run hlive hS [e10] at 0x80000c10
    fr_glob
    exact fa_ok (st' := { st' with ibase := x.rep.num.toInt.1.toNat }) hlive (ex := [])
      (h2.setIbase (ofInt_mod32 (by omega) (by omega)) (by omega)) (hc2.scalars
        (by keeps_tac Keeps.refl _ _) (scalar_store _ _ (by decide))) hk (.ok _) (by simp)
        (by simp [elk]) (StrPin.of_eq estr.symm _)

theorem fi_str (hlive : ∀ p ∈ dcText, live p.1) (hW : 192 + 336 ≤ W) :
    PopStrK live S Q t0 st (dcFunc 70 st 105 peek neg) G hs F L C sp W M0 R0 0x80000e84#64 := by
  intro R' M' H' G' o st' est elk estr ho hc' h' htg _ hk
  subst est
  rw [dcFunc_i_cons] at hk
  fr_ctx
  bc_run hlive hS [e2', htg, hpn, stderr_word] at 0x80000774
  all_goals try exact frame_acc hsf (by omega) (by omega)
  bc_run hlive hS [e2', htg, hpn, stderr_word] at 0x80000774
  all_goals try exact frame_acc hsf (by omega) (by omega)
  rw [ite_F (by simp [valInt])] at hk
  refine fn_msgI hlive h' (hc'.mod (by keeps_tac Keeps.refl _ _)) (by omega) (by bsimp []; decide)
    (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) fun R3 M3 k3 hc3 h3 => ?_
  bsimp []
  exact jat_c10 hlive (by decide) _ R3 M3 (fa_ok (st' := st') hlive (ex := [_]) h3 hc3 hk (.ok _)
    (by simp) (by simp [elk]) (StrPin.of_eq estr.symm _))

/-- `i` (`0x80000e78`): pop, `dc_num2int`, `dc_ibase` when in `2..16`. -/
theorem fa_i (hlive : ∀ p ∈ dcText, live p.1)
    (h : DcAt S M H F L C G hs st) (hc : FnAt S sp W M0 R0 R M) (hW : 192 + 336 ≤ W)
    (hk : FnK live S Q t0 st (dcFunc 70 st 105 peek neg) G hs sp W M0 R0) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x80000e78#64 R M := by
  fr_pre 0x80000e7c
  refine fn_pop_arm (p := 0x80000e7c) hlive h (hc.mod (by keeps_tac Keeps.refl _ _)) hW (by bsimp [])
    (by decide) ?_ ?_ dcFunc_i_nil hk (fi_num hlive hW) (fi_str hlive hW)
  fr_pop_sites 0x80000e84

end

end Dc.Mach
