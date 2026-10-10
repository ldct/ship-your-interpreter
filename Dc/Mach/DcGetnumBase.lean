import Dc.Mach.DcFrame

/-!
# `dc_getnum`: the reader and the model (M9)

    static int input_str (void)       -- the reader evalstr passes
    {
      if (*input_str_string == '\0') return EOF;
      return *input_str_string++;
    }

`dc_getnum (input, ibase, &readahead)` reads its number with `input`; the
input is the text `w` from `src`, up to the first `'\0'` (`Rd`). After
reading the character at `j` the pointer is `src + min (j + 1) |w|` and the
character is `chW w[j]?` (`EOF` past the end).

- `inPtrAddr`, `InP`: `input_str_string`, the word the reader advances.
- `Rd`, `StrAt.rd`: the text from a string object's byte `j0`.
- `input_str_spec`: one read.
- The model: `readNum` over the indices the machine visits
  (`takeDigits_drop_digit`, `takeDigits_drop_stop`, `dropSpace_drop_*`),
  integer arithmetic (`num_mul_int`, `num_add_int`, `ofInt_nat`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-! ## The reader -/

/-- `input_str_string`. -/
abbrev inPtrAddr : Nat := 0x8001cd70

/-- The bytes of `input_str_string`. -/
def InP (a : Nat) : Prop := inPtrAddr ≤ a ∧ a < inPtrAddr + 8

theorem InP.off {a : Nat} (h : InP a) : OutHeap a ∧ ¬ DcGlob a := by
  simp only [InP] at h
  refine ⟨?_, fun hg => ?_⟩
  · simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  · simp only [DcGlob, dc_addrs, stdFilesAddr] at hg; omega

/-- **The text `w` at `src`**: nonzero bytes in the heap, then `'\0'`. -/
structure Rd (M : Mem) (src : Nat) (w : List Nat) : Prop where
  byte : ∀ i, i < w.length → imgM M (src + i) = BitVec.ofNat 8 (w.getD i 0)
  pos : ∀ c ∈ w, 0 < c
  lt : ∀ c ∈ w, c < 256
  nul : imgM M (src + w.length) = 0#8
  lo : heapStart ≤ src
  hi : src + w.length < heapEnd

/-- The text a string object holds from byte `j0`, up to its first `'\0'`. -/
def rdW (o : StrObj) (j0 : Nat) : List Nat := (o.s.drop j0).takeWhile (· ≠ 0)

theorem takeWhile_getD {p : Nat → Bool} :
    ∀ (l : List Nat) (i : Nat), i < (l.takeWhile p).length → (l.takeWhile p).getD i 0 = l.getD i 0
  | [], _, h => by simp at h
  | c :: l, i, h => by
    by_cases hc : p c
    · simp only [List.takeWhile_cons, hc, ↓reduceIte, List.length_cons] at h ⊢
      cases i with
      | zero => rfl
      | succ i => simpa using takeWhile_getD l i (by omega)
    · simp [List.takeWhile_cons, hc] at h

theorem takeWhile_stop {p : Nat → Bool} :
    ∀ (l : List Nat), (l.takeWhile p).length < l.length → p (l.getD (l.takeWhile p).length 0) = false
  | [], h => by simp at h
  | c :: l, h => by
    by_cases hc : p c
    · simp only [List.takeWhile_cons, hc, ↓reduceIte, List.length_cons] at h ⊢
      simpa using takeWhile_stop l (by omega)
    · simp [List.takeWhile_cons, hc]

/-- **A string object's text from byte `j0`**, for a string in the heap. -/
theorem StrAt.rd {M : Mem} {o : StrObj} (h : StrAt M o) {j0 : Nat} (hj : j0 ≤ o.s.length)
    (hlo : heapStart ≤ o.tb.pay) (hhi : o.tb.pay + o.s.length < heapEnd) :
    Rd M (o.tb.pay + j0) (rdW o j0) := by
  have hl : (rdW o j0).length ≤ o.s.length - j0 := by
    unfold rdW; exact (List.takeWhile_sublist _).length_le.trans (by simp)
  refine ⟨fun i hi => ?_, fun c hc => ?_, fun c hc => ?_, ?_, by omega, by omega⟩
  · rw [Nat.add_assoc, h.bytes _ (by omega)]
    unfold rdW at hi ⊢
    rw [takeWhile_getD _ _ hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  · have := List.mem_takeWhile_imp hc; simp at this; omega
  · exact h.byte c (List.mem_of_mem_drop (List.mem_of_mem_takeWhile hc))
  · rw [Nat.add_assoc]
    rcases Nat.lt_or_ge (j0 + (rdW o j0).length) o.s.length with hlt | hge
    · rw [h.bytes _ hlt]
      have hs := takeWhile_stop (p := fun c => decide (c ≠ 0)) (o.s.drop j0)
        (by simp only [List.length_drop]; unfold rdW at hlt ⊢; omega)
      unfold rdW at hlt ⊢
      simp only [decide_eq_false_iff_not, ne_eq, Decidable.not_not] at hs
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at hs
      simp only [List.getD_eq_getElem?_getD, hs]; rfl
    · rw [show j0 + (rdW o j0).length = o.s.length by omega]; exact h.nul

/-- The character the reader returns: a byte, or `EOF`. -/
def chW : Option Nat → BitVec 64
  | some c => BitVec.ofNat 64 c
  | none => BitVec.ofInt 64 (-1)

theorem Rd.getD_lt {M : Mem} {src : Nat} {w : List Nat} (hr : Rd M src w) {j : Nat}
    (hj : j < w.length) : 0 < w.getD j 0 ∧ w.getD j 0 < 256 := by
  have hm : w.getD j 0 ∈ w := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  exact ⟨hr.pos _ hm, hr.lt _ hm⟩

theorem getElem?_of_lt {w : List Nat} {j : Nat} (hj : j < w.length) : w[j]? = some (w.getD j 0) := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem?_eq_getElem hj

/-- **`input_str ()`** at `0x80000b70`, reading the character at `j`: the
pointer moves past it unless it is the end; clobbers `a4`, `a5`. -/
theorem input_str_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) (hP : ∀ a, InP a → S a) {M : Mem}
    {src j : Nat} {w : List Nat} (hr : Rd M src w) (hj : j ≤ w.length)
    (hp : ldv .ld M inPtrAddr = BitVec.ofNat 64 (src + j))
    (R : Nat → BitVec 64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps [10, 14, 15] R' R → R' 10 = chW w[j]? → MemOnly InP M' M →
      ldv .ld M' inPtrAddr = BitVec.ofNat 64 (src + min (j + 1) w.length) → DW live S Q (R 1) R' M') :
    DW live S Q 0x80000b70#64 R M := by
  have hlo := hr.lo; have hhi := hr.hi
  simp only [heapStart, heapEnd] at hlo hhi
  have hpa : ∀ b ∈ accAddrs inPtrAddr 8, S b := fun b hb => by
    have := of_mem_accAddrs hb; exact hP b (by simp only [InP]; omega)
  rcases Nat.lt_or_ge j w.length with hlt | hge
  · obtain ⟨c0, c1⟩ := hr.getD_lt hlt
    have hb : ldv .lbu M (src + j) = BitVec.ofNat 64 (w.getD j 0) := by
      rw [ldv_lbu, hr.byte j hlt]
      apply BitVec.eq_of_toNat_eq; simp [zero_extend]; omega
    have wq := sxw_ofNat (k := w.getD j 0) (by omega)
    have ws : BitVec.ofNat 64 (src + j) + 1#64 = BitVec.ofNat 64 (src + j + 1) := by
      rw [show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
    bc_run hlive hS [hp, hb, wq, ws]
    all_goals first | exact hpa | exact acc_heap hS (by omega) (by omega) | skip
    · intro hc; exfalso
      have := congrArg BitVec.toNat hc; simp at this; omega
    · intro _
      bc_run hlive hS [hp, hb, wq, ws]
      all_goals first | exact hpa | exact hal | skip
      refine hk _ _ (by keeps_tac Keeps.refl _ _) (by bsimp [getElem?_of_lt hlt]; rfl)
        (fun a ha => imgM_store_miss _ _ (by simp only [InP] at ha; omega)) ?_
      rw [ldv_store_hit, Nat.min_eq_left (by omega)]
  · have hjw : j = w.length := by omega
    subst hjw
    have hb : ldv .lbu M (src + w.length) = 0#64 := by rw [ldv_lbu, hr.nul]; rfl
    bc_run hlive hS [hp, hb]
    all_goals first | exact hpa | exact acc_heap hS (by omega) (by omega) | exact hal | skip
    refine hk _ _ (by keeps_tac Keeps.refl _ _) (by bsimp [List.getElem?_eq_none (Nat.le_refl _)]; rfl)
      (MemOnly.refl _ _) ?_
    rw [hp, Nat.min_eq_right (by omega)]

/-! ## The model over indices -/

theorem num_mul_int (a b : Nat) : Num.mul ⟨false, a, 0⟩ ⟨false, b, 0⟩ 0 = ⟨false, a * b, 0⟩ := by
  simp [Num.mul]

theorem num_add_int (a b : Nat) : Num.add ⟨false, a, 0⟩ ⟨false, b, 0⟩ 0 = ⟨false, a + b, 0⟩ := by
  simp [Num.add, Num.align]

theorem ofInt_nat (d : Nat) : Num.ofInt d = ⟨false, d, 0⟩ := by
  simp [Num.ofInt]

theorem drop_cons_getD {w : List Nat} {j : Nat} (hj : j < w.length) :
    w.drop j = w.getD j 0 :: w.drop (j + 1) := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.drop_eq_getElem_cons hj

/-- A digit at `j`: `takeDigits` takes it. -/
theorem takeDigits_drop_digit {w : List Nat} {j d : Nat} (hj : j < w.length)
    (hd : digitVal (w.getD j 0) = some d) :
    takeDigits (w.drop j) = (d :: (takeDigits (w.drop (j + 1))).1, (takeDigits (w.drop (j + 1))).2) := by
  rw [drop_cons_getD hj]; simp only [takeDigits, hd]

/-- No digit at `j` (or the end): `takeDigits` stops. -/
theorem takeDigits_drop_stop {w : List Nat} {j : Nat}
    (hd : ∀ c, w[j]? = some c → digitVal c = none) : takeDigits (w.drop j) = ([], w.drop j) := by
  rcases Nat.lt_or_ge j w.length with hj | hj
  · rw [drop_cons_getD hj]; simp only [takeDigits, hd _ (getElem?_of_lt hj)]
  · rw [List.drop_eq_nil_of_le hj]; rfl

/-- A space at `j`: `dropWhile isSpace` drops it. -/
theorem dropSpace_drop_space {w : List Nat} {j : Nat} (hj : j < w.length)
    (hs : isSpace (w.getD j 0) = true) :
    (w.drop j).dropWhile isSpace = (w.drop (j + 1)).dropWhile isSpace := by
  rw [drop_cons_getD hj]; simp [List.dropWhile_cons, hs]

/-- No space at `j`: `dropWhile isSpace` stops. -/
theorem dropSpace_drop_stop {w : List Nat} {j : Nat}
    (hs : ∀ c, w[j]? = some c → isSpace c = false) : (w.drop j).dropWhile isSpace = w.drop j := by
  rcases Nat.lt_or_ge j w.length with hj | hj
  · rw [drop_cons_getD hj]; simp [List.dropWhile_cons, hs _ (getElem?_of_lt hj)]
  · rw [List.drop_eq_nil_of_le hj]; rfl

/-! ## The reader from a dc function's frame -/

/-- **A string of the state as the reader's text.** -/
theorem DcAt.rd {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {o : StrObj} (ho : o ∈ G.strs) {j0 : Nat} (hj0 : j0 ≤ o.s.length) :
    Rd M (o.tb.pay + j0) (rdW o j0) := by
  have hso := h.view.strs o ho
  have fbb := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live _ (G.str_mem ho).2))
  have := fbb.lo; have := fbb.fin; have := fbb.top; have := hso.tsz
  exact hso.rd hj0 (by simp only [Blk.pay] at *; omega) (by simp only [Blk.pay, Blk.fin] at *; omega)

/-- Words at or above `heapEnd` through a read. -/
theorem ldv_inP {M M' : Mem} (hm : MemOnly InP M' M) {a : Nat} (ha : heapEnd ≤ a) (k : MKind) :
    ldv k M' a = ldv k M a :=
  ldv_congr k fun j _ => hm _ fun hp => by simp only [InP, heapEnd] at hp ha; omega

/-- **`input_str ()` from a dc function's frame**, reading the character at
`j` of a string object's text from byte `j0`: the state and the frame kept. -/
theorem cf_read {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {fs : Nat} {sv : List (Nat × Nat)} {M0 M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {R0 R : Nat → BitVec 64} {sp : Nat} {o : StrObj} {j0 j : Nat}
    (hfr : CFr InP fs sv M0 M R0 R sp) (hab : heapEnd ≤ sp - fs) (h : DcAt S M H F L C G hs st)
    (hP : ∀ a, InP a → S a) (ho : o ∈ G.strs) (hj0 : j0 ≤ o.s.length) (hj : j ≤ (rdW o j0).length)
    (hp : ldv .ld M inPtrAddr = BitVec.ofNat 64 (o.tb.pay + j0 + j)) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps [10, 14, 15] R' R → R' 10 = chW (rdW o j0)[j]? →
      CFr InP fs sv M0 M' R0 R' sp → DcAt S M' H F L C G hs st → MemOnly InP M' M →
      ldv .ld M' inPtrAddr = BitVec.ofNat 64 (o.tb.pay + j0 + min (j + 1) (rdW o j0).length) →
      DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80000b70#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  refine input_str_spec hlive hS hP (h.rd ho hj0) hj hp R hal fun R' M' hk' e10 hm hp' => ?_
  refine hk R' M' hk' e10 { hfr.regs (hk'.mono (by decide)) with
      saved := fun q hq => (ldv_inP hm (by omega) .ld).trans (hfr.saved q hq)
      out := fun a ho' hg hf hn => (hm a hn).trans (hfr.out a ho' hg hf hn) }
    (h.outWrite hm fun a ha => ha.off) hm hp'

/-! ## Copies and `bc_int2num` into an empty slot -/

/-- **`bc_copy_num (x)`** at `0x800049ac` on the dc state: one more reference
to `x`, its handle joins the handles, the other handles keep their values;
only heap bytes change. -/
theorem dc_copy_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    (hhs : hs.length ≤ 2 ^ 30) {x : NumObj} (hx : x ∈ L)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 x.rep.p) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' L' C', Keeps [15] R' R → DcAt S M' H F L' C' G (.num x.rep.p :: hs) st →
      (GV.num x.rep.p).Den ⟨L', G.strs⟩ (.num x.rep.num) → HsKeep ⟨L, G.strs⟩ ⟨L', G.strs⟩ hs →
      (∀ a, OutHeap a → imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x800049ac#64 R M := by
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hx
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hb := h.heap.blocks x hx
  have hsz := hb.sSz; have hsp := hb.sPay
  have fbb := h.heap.heap.blk (List.mem_append_right _ hb.sLive)
  have hblo : 2147603920 ≤ x.sb.h := fbb.lo
  have hbhi : x.sb.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hpl : 2147603936 ≤ x.rep.p ∧ x.rep.p + 40 ≤ 2273312768 := by
    rw [hsp]; simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2⟩ := hpl
  have hrl := h.numRefs_lt hhs hx
  have hrf := (h.heap.nums x hx).refs
  have wp := word_succ x.rep.refs
  have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (x.rep.refs + 1))) =
      BitVec.ofNat 64 (x.rep.refs + 1) := sxw_ofNat hrl
  bc_run hlive hS [h10, hrf, wp, wq]
  all_goals first | exact hal | skip
  have hv : (BitVec.ofNat 64 (x.rep.refs + 1)).toNat % 2 ^ 32 = x.rep.refs + 1 :=
    toNat_ofNat_mod32 (by omega)
  refine hk _ _ _ _ (by keeps_tac Keeps.refl _ _) (h.bumpNum hhs hv)
    ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩ (HsKeep.withRefs _ hs) fun a ho => ?_
  have := ho.1; simp only [heapStart, heapEnd] at this
  exact imgM_store_miss _ _ (by omega)

/-- **A fresh number with one reference**: a callee added `y` to the heap
without freeing a handle; the state holds the handle `.num y.p`. -/
theorem DcAt.addNum {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F F' : List Blk}
    {L : List NumObj} {y : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) (hb : BcHeap S (G.raws M) M' H' F' (y :: L))
    (h1 : y.rep.refs = 1) (hno : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (how : y.Owns)
    (hgl : ∀ a, DcGlob a → imgM M' a = imgM M a) :
    DcAt S M' H' F' (y :: L) C G (.num y.rep.p :: hs) st ∧
      HsKeep ⟨L, G.strs⟩ ⟨y :: L, G.strs⟩ hs := by
  have hag : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a := fun a ⟨c, hc, ha⟩ =>
    hb.raw.img c hc a ha
  have hb0 : BcHeap S (G.raws M) M' H' F' ([] ++ y :: L) := hb
  have hne : ∀ z ∈ L, z.rep.p ≠ y.rep.p := fun z hz => hb0.p_ne_all z (by simpa using hz)
  have hb' : BcHeap S (G.raws M') M' H' F' (y :: L) :=
    hb.subRaw (X' := G.raws M') (fun c hc => hc) fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm
  exact ⟨⟨hb', h.nodup, h.view.frame hag hgl, h.den.addNum hne h1 hno hpos how, h.glob, h.col⟩,
    HsKeep.cons hs⟩

/-- **`bc_int2num(num, val)`** at `0x8000690c` on the dc state into a `NULL`
stack slot `q`: the slot holds a fresh number for `val` and its handle joins
the handles, or `out_of_memory`. -/
theorem dc_int2num_null_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {q sp : Nat} {v : Int} (hq : PtrSlot S q)
    (hqh : heapEnd ≤ q) (hw : ldv .ld M q = 0#64) (hsf : StackFrame S sp 128)
    (hab : heapEnd + 128 ≤ sp) (hqf : q + 8 ≤ sp - 128 ∨ sp ≤ q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h11 : R 11 = BitVec.ofInt 64 v)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0) (hvlo : -2 ^ 31 < v)
    (hvhi : v < 2 ^ 31)
    (hk : ∀ R' M' H' F' C' y, Keeps i2nClob R' R →
      DcAt S M' H' F' (y :: L) C' G (.num y.rep.p :: hs) st → y.rep.num = Num.ofInt v →
      ldv .ld M' q = BitVec.ofNat 64 y.rep.p →
      (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 128 a → imgM M' a = imgM M a) →
      HsKeep ⟨L, G.strs⟩ ⟨y :: L, G.strs⟩ hs → DW live S Q (R 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 128) →
      (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 128 a → imgM M' a = imgM M a) →
      DW live S Q 0x80002bcc#64 R' M') :
    DW live S Q 0x8000690c#64 R M := by
  have hqh' := hqh; have hab' := hab
  simp only [heapEnd] at hqh' hab'
  have hsl := hsf.lo
  have hsl' : ∀ a, slotBytes q a → OutHeap a := fun a ha => outHeap_of_ge (by simp only [heapEnd]; omega)
  refine bc_int2num_specS hlive (Fr := (· = L)) ⟨hsf, hab, hq, hsl', hqf, h2, hal, hvlo, hvhi⟩
    (.null h.heap hw) h10 h11
    ⟨fun R' Mt' H' F' L' y hk1 hp => ?_, fun R' Mt' h2' hm => hoom R' Mt' h2' hm⟩
  have e := hp.rest
  subst e
  obtain ⟨hd, hkp⟩ := h.addNum hp.heap hp.refs hp.norm hp.pos hp.owns fun a ha =>
    hp.out a ha.outHeap (fun hs => by have := ha.lt; simp only [heapStart] at this; omega)
      (fun hf => by have := ha.lt; simp only [heapStart, frameIn] at this hf; omega)
  refine hk R' Mt' H' F' C y hk1 hd hp.num ?_ hp.out hkp
  rw [hp.slot, (hp.heap.blocks y List.mem_cons_self).sPay]

/-- **`bc_int2num` of `v` into the slot at `o`**, which holds the handle `og`
or `NULL`: the slot's handle (if any) replaced by a fresh number for `v`, or
`out_of_memory`. -/
theorem cf_i2nO {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {P : Nat → Prop} {fs : Nat} {sv : List (Nat × Nat)}
    {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV}
    {st : St} {og : Option Nat} {sp o : Nat} {v : Int} {R0 R : Nat → BitVec 64}
    (cx : CfCtx S fs sp) (hfr : CFr P fs sv M0 M R0 R sp) (h : DcAt S M H F L C G (slotHs og ++ hs) st)
    (hsv : ∀ q ∈ sv, o + 8 ≤ q.1) (ho : o + 8 ≤ fs) (h8 : o % 8 = 0)
    (hw : ldv .ld M (sp - fs + o) = BitVec.ofNat 64 (og.getD 0))
    (h10 : R 10 = BitVec.ofNat 64 (sp - fs + o)) (h11 : R 11 = BitVec.ofInt 64 v)
    (hal : (R 1).toNat % 4 = 0) (hvlo : -2 ^ 31 < v) (hvhi : v < 2 ^ 31)
    (hk : ∀ R' M' H' F' L' C' y, Keeps cClob R' R → CFr P fs sv M0 M' R0 R' sp →
      DcAt S M' H' F' (y :: L') C' G (.num y.rep.p :: hs) st → y.rep.num = Num.ofInt v →
      ldv .ld M' (sp - fs + o) = BitVec.ofNat 64 y.rep.p → CfOut M M' sp fs o →
      HsKeep ⟨L, G.strs⟩ ⟨y :: L', G.strs⟩ hs → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp (fs + cfW) M0 P sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x8000690c#64 R M := by
  cases og with
  | some p => exact cf_i2n hlive cx hfr h hsv ho h8 hw h10 h11 hal hvlo hvhi hk hoom
  | none =>
    have hab := cx.abv
    have hab' := cx.ab
    have hW : cfW = 176 + rmStack (2 ^ 30) := rfl
    have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
    have hsl := cx.sf.lo
    simp only [heapEnd] at hab hab'
    refine dc_int2num_null_spec hlive h (cx.slot ho h8) (by simp only [heapEnd]; omega) hw
      (cx.win (n := 128) (by omega)) (by simp only [heapEnd]; omega) (.inr (by omega)) R h10 h11 hfr.r2 hal
      hvlo hvhi (fun R' M' H' F' C' y hk' hd hnum hw' hout hkp => ?_) (fun R' M' r2 hout => ?_)
    · have hO : CfOut M M' sp fs o := fun a ho' _ hf hs' =>
        hout a ho' hs' fun h => hf (by simp only [frameIn] at h ⊢; omega)
      have k : Keeps cClob R' R := hk'.mono (by decide)
      exact hk R' M' H' F' L C' y k (hfr.next cx.abv (by omega) hsv ho hO k) hd hnum hw' hO hkp
    · have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
      bc_run hlive hS [] at 0x80001e74
      exact hoom R' M' _ (hfr.oom cx (W := 128) (sp' := sp - fs - 128) (by unfold cfW rmStack; omega) ho
        (by omega) (by omega) r2 fun a ho' hs' hf => hout a ho' hs' hf)

/-- **`bc_divide (a, b, &slot, k)`** with the slot at `o` holding a handle of
the state (possibly `a`'s own): its handle replaced by the quotient's, or
`out_of_memory`. A divisor `1` (whose detour frees the slot before reading
the operands again) needs the slot's handle to be `_zero_`'s. -/
theorem cf_div {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {P : Nat → Prop} {fs : Nat} {sv : List (Nat × Nat)}
    {M0 M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV}
    {st : St} {p p1 p2 sp o k : Nat} {n1 n2 m : Num} {R0 R : Nat → BitVec 64}
    (cx : CfCtx S fs sp) (hfr : CFr P fs sv M0 M R0 R sp) (h : DcAt S M H F L C G (.num p :: hs) st)
    (hsv : ∀ q ∈ sv, o + 8 ≤ q.1) (ho : o + 8 ≤ fs) (h8 : o % 8 = 0)
    (hw : ldv .ld M (sp - fs + o) = BitVec.ofNat 64 p)
    (hd1 : (GV.num p1).Den ⟨L, G.strs⟩ (.num n1)) (hd2 : (GV.num p2).Den ⟨L, G.strs⟩ (.num n2))
    (hm : Num.div n1 n2 k = some m) (hsz : n1.wid + k + n2.wid < 2 ^ 27)
    (hone : n2.mag = 1 → p = C.z.rep.p)
    (h10 : R 10 = BitVec.ofNat 64 p1) (h11 : R 11 = BitVec.ofNat 64 p2)
    (h12 : R 12 = BitVec.ofNat 64 (sp - fs + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' y, Keeps cClob R' R → CFr P fs sv M0 M' R0 R' sp →
      DcAt S M' H' F' (y :: L') C' G (.num y.rep.p :: hs) st → y.rep.num = m →
      ldv .ld M' (sp - fs + o) = BitVec.ofNat 64 y.rep.p → CfOut M M' sp fs o →
      HsKeep ⟨L, G.strs⟩ ⟨y :: L', G.strs⟩ hs → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp (fs + cfW) M0 P sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x8000589c#64 R M := by
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
  have hxm : x ∈ L1 ++ x :: L2 := List.mem_append_right _ List.mem_cons_self
  have hn1 := h.heap.nums x1 hx1; have hn2 := h.heap.nums x2 hx2
  have hsz' : x1.rep.len + x1.rep.scale + k + x2.rep.len + x2.rep.scale < 2 ^ 27 := by
    have w1 := NumRep.len_le_wid hn1.shape (h.den.norm x1 hx1)
    have w2 := NumRep.len_le_wid hn2.shape (h.den.norm x2 hx2)
    omega
  have hap : IsOneRep x2.rep → x.rep.refs = 1 → False := fun h1 hr => by
    have := h.zero_refs hxm (hone (IsOneRep.mag hn2.shape h1)); omega
  refine bc_divide_specF hlive (W := 304) (k := k) (z := C.z)
    ⟨cx.win (by omega), by simp only [heapEnd]; omega, by decide, cx.slot ho h8,
      fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega), .inr (by omega),
      .inr (by simp only [dc_addrs]; omega),
      fun a ha => h.glob a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega),
      hfr.r2, hal⟩
    ⟨fun m' hm' R' Mt H' F' L' y hk' _ hp => ?_, fun hnone => absurd (hm.symm.trans hnone) (by simp),
      fun R' Mt sp' o1 o2 r2 hout => ?_⟩
    ⟨rfl, hx1, hx2, h.den.mz, fun h1 _ hf => hf.keep hx1 fun hr => absurd hr (fun e => hap h1 e),
      fun h1 _ hf => hf.keep hx2 fun hr => absurd hr (fun e => hap h1 e),
      fun h1 _ hf => hf.keep h.den.mz fun hr => absurd hr (fun e => hap h1 e),
      hsz', h.view.zw, h.den.pos x1 hx1⟩
    (by rw [h.den.zv]; rfl) h.heap (.num (h.resSlot hw)) h10 h11 h12 h13
  · have e : m' = m := Option.some.inj (hm'.symm.trans hm)
    subst e
    exact cf_ret cx hfr h ⟨hp.heap, hp.rest, hp.num, hp.norm, hp.pos, hp.refs, hp.owns, hp.slot, hp.out⟩
      (by omega) hsv ho (hk'.mono (by decide))
      fun C' hfr' hd hw' hO hkp => hk R' Mt H' F' L' C' y (hk'.mono (by decide)) hfr' hd hp.num hw' hO hkp
  · have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
    bc_run hlive hS [] at 0x80001e74
    exact hoom R' Mt sp' (hfr.oom cx (W := 304) (by unfold cfW; omega) ho o1 o2 r2
      fun a ho' hs' hf => hout a ho' hs' hf)

end Dc.Mach
