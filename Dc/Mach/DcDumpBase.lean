import Dc.Mach.DcDivrem
import Dc.Mach.DcPrint

/-!
# `dc_dump_num`'s state (M9)

    dc_dump_num (dcvalue, discard):
      bc_init_num (&value); bc_init_num (&obase); bc_init_num (&digit);
      bc_divide (dcvalue, _one_, &value, 0); value->n_sign = PLUS;
      if (discard == DC_TOSS) dc_free_num (&dcvalue);
      bc_int2num (&obase, 256);
      do { bc_divmod (value, obase, &value, &digit, 0);
           cur = dc_malloc (16); cur->digit = bc_num2long (digit);
           cur->link = top; top = cur; } while (!bc_is_zero (value));
      for (cur = top; cur; cur = next) { putchar (cur->digit); next = cur->link; free (cur); }
      bc_free_num (&digit); bc_free_num (&obase); bc_free_num (&value);

The three numbers are handles of the dc state (`hs`), so the bc callees run
through the `DcAt` wrappers. The digit cells are `malloc (16)` blocks fresh to
the state; a bc callee gets them as raw blocks beside the state's
(`DcAt.withCells`), and keeps their bytes.

- `DcDen.perm`, `DcAt.perm`: the handles in another order.
- `DcAt.refs2`: a number with two handles has two references.
- `CellsK`: a stack of `[word, next]` cells with the word read as `k`.
- `DnStk`: the digit cells, fresh to the state.
- `DcAt.withCells`, `DnStk.ofRaw`: the cells as a callee's raw blocks.
- `bc_free_num_dcK`: `bc_free_num_dc` keeping the other handles' values.
- `dumpDs`, `DumpInv`: the digit loop's model (`.start`, `.step`, `.exit`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## Handles -/

/-- **The handles in another order.** -/
theorem DcDen.perm {L : List NumObj} {C : BcConsts} {G : DcG} {hs hs' : List GV} {st : St}
    (d : DcDen L C G hs st) (hp : hs.Perm hs') : DcDen L C G hs' st :=
  { d with
    hsDen := fun g hg => d.hsDen g (hp.mem_iff.mpr hg)
    numRefs := fun x hx => by
      rw [d.numRefs x hx, ((List.Perm.append_left G.vals hp).count_eq (.num x.rep.p))]
    strRefs := fun o ho => by
      rw [d.strRefs o ho, ((List.Perm.append_left G.vals hp).count_eq (.str o.hb.pay))] }

theorem DcAt.perm {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs hs' : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    (hp : hs.Perm hs') : DcAt S M H F L C G hs' st :=
  { h with den := h.den.perm hp }

/-- **Two handles, two references.** -/
theorem DcAt.refs2 {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {x : NumObj} (hx : x ∈ L) (h2 : 2 ≤ hs.count (.num x.rep.p)) : 2 ≤ x.rep.refs := by
  rw [h.den.numRefs x hx, List.count_append]; omega

/-! ## Cells -/

/-- **A stack of `[word, next]` cells** from `p` at the image `M`, each word
read as `k` (`dc_dump_num`'s `int` digit is `.lw`): each cell a block of at
least 16 bytes holding its word at the payload and the next cell's address
at `+8`, distinct from the later cells and from `Xb`; `0` ends the stack.
(`Cells` of `RawCells.lean` is the `.ld` case.) -/
def CellsK (k : MKind) (M : Mem) (Xb : List Blk) : List Blk → List Nat → Nat → Prop
  | [], [], p => p = 0
  | c :: cs, d :: ds, p =>
      p = c.pay ∧ 16 ≤ c.sz ∧ ldv k M c.pay = BitVec.ofNat 64 d ∧ c ∉ cs ++ Xb ∧
        CellsK k M Xb cs ds (ldv .ld M (c.pay + 8)).toNat
  | _, _, _ => False

/-- The cells at an image agreeing on their bytes. -/
theorem CellsK.transport {k : MKind} (hk : widthOfM k ≤ 8) {M M' : Mem} {Xb : List Blk} :
    ∀ {cs : List Blk} {ds : List Nat} {p : Nat}, CellsK k M Xb cs ds p →
      (∀ c ∈ cs, ∀ a, c.In a → imgM M' a = imgM M a) → CellsK k M' Xb cs ds p
  | [], [], _, h, _ => h
  | c :: cs, d :: ds, _, ⟨hp, hsz, hd, hn, hr⟩, hm => by
      have hc : ∀ j, j < 16 → imgM M' (c.pay + j) = imgM M (c.pay + j) := fun j hj =>
        hm c List.mem_cons_self _ (by simp only [Blk.In, Blk.pay, Blk.fin]; omega)
      have e0 : ldv k M' c.pay = ldv k M c.pay := ldv_congr k fun j hj => hc j (by omega)
      have e8 : ldv .ld M' (c.pay + 8) = ldv .ld M (c.pay + 8) :=
        ldv_congr .ld fun j hj => by
          rw [Nat.add_assoc]; exact hc _ (by simp only [widthOfM] at hj; omega)
      exact ⟨hp, hsz, e0 ▸ hd, hn,
        e8 ▸ CellsK.transport hk hr fun c' hc' => hm c' (List.mem_cons_of_mem _ hc')⟩
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim

/-- The head cell, by name. -/
structure CellKHead (k : MKind) (M : Mem) (Xb : List Blk) (c : Blk) (cs : List Blk) (d : Nat)
    (ds : List Nat) (p : Nat) : Prop where
  p : p = c.pay
  sz : 16 ≤ c.sz
  word : ldv k M c.pay = BitVec.ofNat 64 d
  fresh : c ∉ cs ++ Xb
  rest : CellsK k M Xb cs ds (ldv .ld M (c.pay + 8)).toNat

theorem CellsK.head {k : MKind} {M : Mem} {Xb : List Blk} {c : Blk} {cs : List Blk} {d : Nat}
    {ds : List Nat} {p : Nat} (h : CellsK k M Xb (c :: cs) (d :: ds) p) :
    CellKHead k M Xb c cs d ds p :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem CellsK.length {k : MKind} {M : Mem} {Xb : List Blk} :
    ∀ {cs : List Blk} {ds : List Nat} {p : Nat}, CellsK k M Xb cs ds p → cs.length = ds.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, _, ⟨_, _, _, _, hr⟩ => congrArg (· + 1) (CellsK.length hr)
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- An empty stack's address is `0`; a nonempty one's is its head's payload. -/
theorem CellsK.zero_iff {k : MKind} {M : Mem} {Xb : List Blk} {cs : List Blk} {ds : List Nat}
    {p : Nat} (h : CellsK k M Xb cs ds p) : p = 0 ↔ cs = [] := by
  match cs, ds, h with
  | [], [], h => exact ⟨fun _ => rfl, fun _ => h⟩
  | _ :: _, _ :: _, ⟨hp, _⟩ =>
    exact ⟨fun e => by simp only [Blk.pay] at hp; omega, fun e => by cases e⟩

/-- **`dc_dump_num`'s digit cells** from `p`: blocks fresh to the state
holding the digits `ds` (bytes) as `int`s. -/
structure DnStk (H : Heap) (F : List Blk) (L : List NumObj) (G : DcG) (M : Mem)
    (cells : List Blk) (ds : List Nat) (p : Nat) : Prop where
  fresh : ∀ c ∈ cells, DcFresh H F L G c
  stk : CellsK .lw M G.blocks cells ds p
  dig : ∀ d ∈ ds, d < 256
  lt : p < 2 ^ 64

/-- No cells. -/
theorem DnStk.nil (H : Heap) (F : List Blk) (L : List NumObj) (G : DcG) (M : Mem) :
    DnStk H F L G M [] [] 0 := ⟨fun _ h => (nomatch h), rfl, fun _ h => (nomatch h), by decide⟩

/-- **The cells as raw blocks beside the state's**, imaged at the current
memory. -/
theorem DcAt.withCells {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {cells : List Blk} {ds : List Nat} {p : Nat}
    (h : DcAt S M H F L C G hs st) (sk : DnStk H F L G M cells ds p) :
    BcHeap S ⟨cells ++ G.blocks, M⟩ M H F L :=
  { h.heap with
    raw :=
      ⟨fun b hb => (List.mem_append.mp hb).elim (fun hc => (sk.fresh b hc).live)
          (fun hc => h.heap.raw.live b hc),
        fun b hb => (List.mem_append.mp hb).elim (fun hc => (sk.fresh b hc).notNum)
          (fun hc => h.heap.raw.out b hc),
        fun _ _ _ _ => rfl⟩ }

/-- The state's own raws from the raws with the cells. -/
theorem BcHeap.dropCells {S : Nat → Prop} {G : DcG} {cells : List Blk} {M M' : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} (h : BcHeap S ⟨cells ++ G.blocks, M⟩ M' H F L) :
    BcHeap S (G.raws M) M' H F L :=
  h.subRaw (fun b hb => List.mem_append_right _ hb) fun _ _ _ _ => rfl

/-- **The cells after a callee** that kept them as raw blocks. -/
theorem DnStk.ofRaw {S : Nat → Prop} {G : DcG} {cells : List Blk} {ds : List Nat} {p : Nat}
    {M M' : Mem} {H H' : Heap} {F F' : List Blk} {L L' : List NumObj}
    (sk : DnStk H F L G M cells ds p) (hb : BcHeap S ⟨cells ++ G.blocks, M⟩ M' H' F' L') :
    DnStk H' F' L' G M' cells ds p where
  fresh := fun c hc =>
    ⟨hb.raw.live c (List.mem_append_left _ hc), (sk.fresh c hc).notG,
      hb.raw.out c (List.mem_append_left _ hc)⟩
  stk := sk.stk.transport (by decide) fun c hc a ha => hb.raw.img c (List.mem_append_left _ hc) a ha
  dig := sk.dig
  lt := sk.lt

/-- **The cells through `dc_malloc`**: still fresh, their bytes kept. -/
theorem DnStk.malloc {S : Nat → Prop} {H H' : Heap} {F : List Blk} {L : List NumObj} {G : DcG}
    {M M' : Mem} {cells : List Blk} {ds : List Nat} {p n sp : Nat} {c : Blk}
    (sk : DnStk H F L G M cells ds p) (hi : HeapInv S M H) (hp : DcMallocPost S M M' H H' n sp c)
    (hsp : heapEnd + 16 ≤ sp) : DnStk H' F L G M' cells ds p where
  fresh := fun c' hc' => ⟨by rw [hp.live]; exact List.mem_cons_of_mem _ (sk.fresh c' hc').live,
    (sk.fresh c' hc').notG, (sk.fresh c' hc').notNum⟩
  stk := sk.stk.transport (by decide) fun c' hc' a ha =>
    hp.frame a (live_not_alloc hi (sk.fresh c' hc').live ha) fun hf => by
      have := live_in_heap hi (sk.fresh c' hc').live ha
      simp only [frameIn, heapEnd] at hf this hsp; omega
  dig := sk.dig
  lt := sk.lt

/-- The block `dc_malloc` returned is none of the cells. -/
theorem DnStk.not_mem {S : Nat → Prop} {H H' : Heap} {F : List Blk} {L : List NumObj} {G : DcG}
    {M M' : Mem} {cells : List Blk} {ds : List Nat} {p n sp : Nat} {c : Blk}
    (sk : DnStk H F L G M cells ds p) (hi : HeapInv S M H) (hp : DcMallocPost S M M' H H' n sp c)
    (hn : 1 ≤ n) : c ∉ cells := fun hc => by
  have hsz := hp.size
  exact live_not_alloc hi (sk.fresh c hc).live (a := c.pay) ⟨Nat.le_refl _, by simp only [Blk.pay, Blk.fin]; omega⟩
    (hp.alloc _ (by simp only [Blk.pay]; omega) (by simp only [Blk.pay, Blk.fin]; omega))

/-- **A cell pushed**: the fresh block `c`, written only in its bytes, holds
the digit `d` and the old top `p`. -/
theorem DnStk.push {S : Nat → Prop} {H : Heap} {F : List Blk} {L : List NumObj} {G : DcG}
    {M M' : Mem} {cells : List Blk} {ds : List Nat} {p d : Nat} {c : Blk}
    (sk : DnStk H F L G M cells ds p) (hi : HeapInv S M H) (hc : DcFresh H F L G c)
    (hcs : c ∉ cells) (hsz : 16 ≤ c.sz) (hd : d < 256) (hm : MemOnly c.In M' M)
    (hw : ldv .lw M' c.pay = BitVec.ofNat 64 d) (hl : ldv .ld M' (c.pay + 8) = BitVec.ofNat 64 p) :
    DnStk H F L G M' (c :: cells) (d :: ds) c.pay where
  fresh := List.forall_mem_cons.mpr ⟨hc, sk.fresh⟩
  stk := ⟨rfl, hsz, hw, fun hm' => (List.mem_append.mp hm').elim hcs hc.notG, by
    rw [hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sk.lt]
    exact sk.stk.transport (by decide) fun c' hc' a ha => hm a fun hca =>
      live_apart hi hc.live (sk.fresh c' hc').live (fun e => hcs (e ▸ hc')) hca ha⟩
  dig := List.forall_mem_cons.mpr ⟨hd, sk.dig⟩
  lt := by
    have := live_in_heap hi hc.live (a := c.pay) ⟨Nat.le_refl _, by simp only [Blk.pay, Blk.fin]; omega⟩
    simp only [heapEnd] at this; omega

/-- **The top cell freed**: the rest from the top's link. -/
theorem DnStk.free {S : Nat → Prop} {H H' : Heap} {F : List Blk} {L : List NumObj} {G : DcG}
    {M M' : Mem} {c : Blk} {cells lpre lpost : List Blk} {d : Nat} {ds : List Nat} {p : Nat}
    (sk : DnStk H F L G M (c :: cells) (d :: ds) p) (hi : HeapInv S M H)
    (hl : H.live = lpre ++ c :: lpost) (hp : FreePost S M M' H H' c lpre lpost) :
    DnStk H' F L G M' cells ds (ldv .ld M (c.pay + 8)).toNat where
  fresh := fun c' hc' => by
    have hf := sk.fresh c' (List.mem_cons_of_mem _ hc')
    have hne : c' ≠ c := fun e => sk.stk.head.fresh (List.mem_append_left _ (e ▸ hc'))
    refine ⟨?_, hf.notG, hf.notNum⟩
    have := hf.live
    rw [hl, List.mem_append, List.mem_cons] at this
    rw [hp.live, List.mem_append]
    rcases this with h | h | h
    · exact .inl h
    · exact absurd h hne
    · exact .inr h
  stk := sk.stk.head.rest.transport (by decide) fun c' hc' a ha =>
    hp.frame a (live_not_alloc hi (sk.fresh c' (List.mem_cons_of_mem _ hc')).live ha)
  dig := fun d' hd' => sk.dig d' (List.mem_cons_of_mem _ hd')
  lt := BitVec.isLt _

/-- **`bc_free_num` on a handle of the state**, the other handles keeping
their values. -/
theorem bc_free_num_dcK {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat}
    (h : DcAt S M H F L C G (.num p :: hs) st) {q sp : Nat} (hq : PtrSlot S q) (hqh : heapEnd ≤ q)
    (hw : ldv .ld M q = BitVec.ofNat 64 p) (hsf : StackFrame S sp 32) (hab : heapEnd + 32 ≤ sp)
    (hqf : q + 8 ≤ sp - 32 ∨ sp ≤ q)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 q) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps freeNumClob R' R → DcAt S M' H' F' L' C' G hs st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 32 a → ¬ slotBytes q a → imgM M' a = imgM M a) →
      HsKeep ⟨L, G.strs⟩ ⟨L', G.strs⟩ hs → DW live S Q (R 1) R' M') :
    DW live S Q 0x800048c0#64 R M :=
  bc_free_num_dcP hlive (Pend.id G) (M := M) h hq (.above hqh) hw hsf hab hqf R h10 h2 hal
    fun R' M' H' F' L' C' k1 k2 _ k4 _ k6 => hk R' M' H' F' L' C' k1 k2 k4 k6

/-! ## The model -/

/-- The bytes `dc_dump_num` prints for the integer part `k`: its base-256
digits, at least one. -/
def dumpDs (k : Nat) : List Nat :=
  match Dc.Num.digits 256 k with
  | [] => [0]
  | ds => ds

theorem dump_eq (n : Dc.Num) : n.dump = dumpDs n.intPart := rfl

/-- **The digit loop's invariant** at its head, `v` the quotient left and
`ds` the digits pushed (top first): nothing pushed yet, or the bytes are the
digits still to compute followed by the pushed ones. -/
def DumpInv (n0 v : Nat) (ds : List Nat) : Prop :=
  (ds = [] ∧ v = n0) ∨ (ds ≠ [] ∧ dumpDs n0 = Dc.Num.digits 256 v ++ ds)

theorem DumpInv.start (n0 : Nat) : DumpInv n0 n0 [] := .inl ⟨rfl, rfl⟩

theorem digits_zero (b : Nat) : Dc.Num.digits b 0 = [] := rfl

/-- One turn: `v % 256` pushed, `v / 256` left. -/
theorem DumpInv.step {n0 v : Nat} {ds : List Nat} (h : DumpInv n0 v ds) (hc : ds ≠ [] → v ≠ 0) :
    DumpInv n0 (v / 256) (v % 256 :: ds) := by
  refine .inr ⟨List.cons_ne_nil _ _, ?_⟩
  rcases h with ⟨rfl, hv⟩ | ⟨hne, he⟩
  · subst hv
    by_cases h0 : v = 0
    · subst h0; rfl
    · rw [dumpDs, Dc.BcModel.digits_step 256 (by decide) v h0]
      cases Dc.Num.digits 256 (v / 256) <;> rfl
  · rw [he, Dc.BcModel.digits_step 256 (by decide) v (hc hne), List.append_assoc]; rfl

/-- A smaller magnitude has no more decimal digits. -/
theorem decLen_mono : ∀ {a b : Nat}, a ≤ b → decLen a ≤ decLen b := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    intro hab
    rw [decLen.eq_1 a, decLen.eq_1 b]
    split
    · split <;> omega
    · rename_i ha
      have hb : ¬ b < 10 := by omega
      rw [if_neg hb]
      have := ih (b / 10) (by omega) (a := a / 10) (Nat.div_le_div_right hab)
      omega

/-- The loop's exit: the digits pushed are the bytes. -/
theorem DumpInv.exit {n0 : Nat} {ds : List Nat} (h : DumpInv n0 0 ds) (hne : ds ≠ []) :
    dumpDs n0 = ds := by
  rcases h with ⟨e, _⟩ | ⟨_, he⟩
  · exact absurd e hne
  · rw [he, digits_zero, List.nil_append]

end Dc.Mach
