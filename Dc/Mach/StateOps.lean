import Dc.Mach.DcAlloc
import Dc.Mach.Bc.DivAlloc
import Dc.Mach.Printf

/-!
# The dc state through allocation and stores (M9)

- `DcGlob.outHeap`: dc's globals lie below the heap, off the allocator's and
  `_bc_Free_list`'s words.
- `DcAt.malloc`: the state survives `dc_malloc`; the fresh block is none of
  the state's or the number heap's blocks (`DcFresh`).
- `DcAt.rawWrite`: the state survives stores into a fresh block.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

theorem DcGlob.lt {a : Nat} (h : DcGlob a) : 0x8001ad14 ≤ a ∧ a < heapStart := by
  simp only [DcGlob, dc_addrs, heapStart] at h ⊢; omega

theorem DcGlob.outHeap {a : Nat} (h : DcGlob a) : OutHeap a := by
  simp only [DcGlob, OutHeap, dc_addrs, heapStart, heapEnd, freeListAddr] at h ⊢; omega

/-- The type word of a datum, as `lw` reads it. -/
theorem DatAt.lw {Mt : Mem} {a : Nat} {g : GV} (h : DatAt Mt a g) :
    ldv .lw Mt a = BitVec.ofNat 64 g.tag :=
  VsaIris.Interp.ldv_lw_kind (by rw [← VsaIris.Interp.ldv_ld_imgW]; exact h.tag)
    (by cases g <;> simp [GV.tag])

/-- A byte of the ghost's blocks is a live payload byte. -/
theorem DcAt.inBlocks {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) {a : Nat}
    (ha : InBlocks G.blocks a) : ∃ b ∈ H.live, b.In a ∧ b ∈ G.blocks := by
  obtain ⟨b, hb, hba⟩ := ha
  exact ⟨b, h.heap.raw.live b hb, hba, hb⟩

/-- A byte of the ghost's blocks: in the heap, no allocator byte. -/
theorem DcAt.inBlocks_heap {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) {a : Nat}
    (ha : InBlocks G.blocks a) : (heapStart ≤ a ∧ a < heapEnd) ∧ ¬ AllocByte H a := by
  obtain ⟨b, hb, hba, -⟩ := h.inBlocks ha
  exact ⟨live_in_heap h.heap.heap hb hba, live_not_alloc h.heap.heap hb hba⟩

/-- A block `malloc` handed out is new to the state. -/
structure DcFresh (H' : Heap) (F : List Blk) (L : List NumObj) (G : DcG) (b : Blk) : Prop where
  live : b ∈ H'.live
  notG : b ∉ G.blocks
  notNum : b ∉ F ++ objBlocks L

/-- **The state through `dc_malloc`**, the frame `[sp - 16, sp)` above the heap. -/
theorem DcAt.malloc {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {n sp : Nat} {b : Blk}
    (h : DcAt S M H F L C G hs st) (hp : DcMallocPost S M M' H H' n sp b) (hn : 1 ≤ n)
    (hab : heapEnd + 16 ≤ sp) :
    DcAt S M' H' F L C G hs st ∧ DcFresh H' F L G b := by
  have hi := h.heap.heap
  simp only [heapEnd] at hab
  have hlive : ∀ c ∈ H.live, c ∈ H'.live := fun c hc => by rw [hp.live]; exact List.mem_cons_of_mem _ hc
  have hown : ∀ c ∈ F ++ objBlocks L ++ G.blocks, ∀ a, c.In a → imgM M' a = imgM M a :=
    fun c hc a ha => by
      have hcl := h.heap.owned_live hc
      have := live_in_heap hi hcl ha
      exact hp.frame a (live_not_alloc hi hcl ha) fun hf => by
        simp only [frameIn, heapEnd] at hf this; omega
  have hg8 : ∀ j, j < 8 → imgM M' (bcFreeAddr + j) = imgM M (bcFreeAddr + j) := fun j hj =>
    hp.frame _ (fun ha => not_bcFree_of_alloc hi ha (by simp only [bcFreeBytes]; omega))
      fun hf => by simp only [frameIn, bcFreeAddr] at hf; omega
  have hb1 : BcHeap S (G.raws M) M' H' F L :=
    h.heap.rebase hp.inv (fun c hc => hlive c (h.heap.owned_live hc)) hown hg8
  have hb2 : BcHeap S (G.raws M') M' H' F L :=
    hb1.subRaw (fun c hc => hc) fun c hc a ha =>
      (hown c (List.mem_append_right _ hc) a ha).symm
  have hgl : ∀ a, DcGlob a → imgM M' a = imgM M a := fun a ha =>
    hp.frame a (OutHeap.not_alloc hi ha.outHeap) fun hf => by
      have := ha.lt; simp only [frameIn, heapStart] at hf this; omega
  have hbl : b ∈ H'.live := by rw [hp.live]; exact List.mem_cons_self
  have hfr := h.heap.fresh_not_owned (b := b) (by have := hp.size; omega) hp.alloc
  refine ⟨{ h with
      heap := hb2
      view := h.view.frame (fun a ha => by
        obtain ⟨c, hc, hca⟩ := ha
        exact hown c (List.mem_append_right _ hc) a hca) hgl },
    hbl, fun hm => hfr (List.mem_append_right _ hm), fun hm => hfr (List.mem_append_left _ hm)⟩

/-- **Stores into a fresh block** keep the state. -/
theorem DcAt.rawWrite {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk}
    (h : DcAt S M H F L C G hs st) (hf : DcFresh H F L G b) (hm : MemOnly b.In M' M) :
    DcAt S M' H F L C G hs st := by
  have hi := h.heap.heap
  have hno : b ∉ F ++ objBlocks L ++ (G.raws M).bs := fun hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact hf.notNum hc
    · exact hf.notG hc
  have hblk : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a := fun a ha => by
    obtain ⟨c, hcl, hca, hcG⟩ := h.inBlocks ha
    exact hm a fun hba => live_apart hi hf.live hcl (fun e => hf.notG (e ▸ hcG)) hba hca
  have hb1 := h.heap.rawWrite hf.live hno hm
  refine { h with
    heap := hb1.subRaw (fun c hc => hc) fun c hc a ha => (hblk a ⟨c, hc, ha⟩).symm
    view := h.view.frame hblk fun a ha => hm a fun hba => by
      have := live_in_heap hi hf.live hba; have := ha.lt; omega }

/-- **Stores off the heap and off dc's globals** keep the state. -/
theorem DcAt.outWrite {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {P : Nat → Prop}
    (h : DcAt S M H F L C G hs st) (hm : MemOnly P M' M) (hP : ∀ a, P a → OutHeap a ∧ ¬ DcGlob a) :
    DcAt S M' H F L C G hs st := by
  have hb1 := h.heap.out_frame hm fun a ha => (hP a ha).1
  have hblk : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a := fun a ha =>
    hm a fun hp => (hP a hp).1.1 (h.inBlocks_heap ha).1
  exact { h with
    heap := hb1.subRaw (fun c hc => hc) fun c hc a ha => (hblk a ⟨c, hc, ha⟩).symm
    view := h.view.frame hblk fun a ha => hm a fun hp => (hP a hp).2 ha }

/-- A chain read from another word holding the same pointer. -/
theorem LChain.reword {α : Type} {Mt : Mem} {off : Nat} {P : Blk → α → Prop} {a a' : Nat}
    {l : List (Blk × α)} (h : LChain Mt off P a l) (ha : ldv .ld Mt a' = ldv .ld Mt a) :
    LChain Mt off P a' l := by
  cases h with
  | nil h0 => exact .nil (ha.trans h0)
  | cons h0 hp hl => exact .cons (ha.trans h0) hp hl

theorem DcG.blocks_pushStk (G : DcG) (bg : Blk × GV) :
    ({ G with stk := bg :: G.stk } : DcG).blocks = bg.1 :: G.blocks := by
  simp only [DcG.blocks, List.map_cons, List.cons_append]

theorem DcG.vals_pushStk (G : DcG) (bg : Blk × GV) :
    ({ G with stk := bg :: G.stk } : DcG).vals = bg.2 :: G.vals := by
  simp only [DcG.vals, List.map_cons, List.cons_append]

/-- A handle moved into the state leaves every count unchanged. -/
theorem count_move (g x : GV) (vs hs : List GV) :
    (g :: vs ++ hs).count x = (vs ++ g :: hs).count x := by
  simp only [List.count_cons, List.count_append, List.cons_append]; omega

/-- The bytes of `dc_stack`. -/
abbrev StkWord (a : Nat) : Prop := dcStackAddr ≤ a ∧ a < dcStackAddr + 8

/-- **A node pushed**: the fresh block `c` holds the handle `g` (denoting `v`)
and the old head, and `dc_stack` now points to it. -/
theorem DcAt.pushNode {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {c : Blk} {v : Val}
    (h : DcAt S M H F L C G (g :: hs) st) (hf : DcFresh H F L G c) (hn : SNodeAt M c g)
    (hl : ldv .ld M (c.pay + 24) = ldv .ld M dcStackAddr) (hv : g.Den ⟨L, G.strs⟩ v) :
    DcAt S (writeLog M [(dcStackAddr, 8, BitVec.ofNat 64 c.pay)]) H F L C
      { G with stk := (c, g) :: G.stk } hs (st.push v) := by
  have hi := h.heap.heap
  have hm : MemOnly StkWord (writeLog M [(dcStackAddr, 8, BitVec.ofNat 64 c.pay)]) M :=
    MemOnly.store M _ 8 _
  have hstk : ∀ a, StkWord a → OutHeap a ∧ ¬ InBlocks G.blocks a := fun a ha =>
    ⟨DcGlob.outHeap (by simp only [StkWord, DcGlob, dc_addrs] at ha ⊢; omega), fun hb => by
      have := (h.inBlocks_heap hb).1; simp only [StkWord, dc_addrs, heapStart] at ha this; omega⟩
  have hcIn : ∀ a, c.In a → ¬ StkWord a := fun a hca hs => by
    have := live_in_heap hi hf.live hca; simp only [StkWord, dc_addrs, heapStart] at hs this; omega
  have hblk : ∀ a, InBlocks G.blocks a → imgM (writeLog M [(dcStackAddr, 8, BitVec.ofNat 64 c.pay)]) a =
      imgM M a := fun a ha => hm a fun hs => (hstk a hs).2 ha
  have hb1 := (h.heap.out_frame hm fun a ha => (hstk a ha).1).addRaw hf.live hf.notNum
  have hsz := hn.sz
  have hcw : ∀ o w, o + w ≤ 32 → ∀ j, j < w →
      imgM (writeLog M [(dcStackAddr, 8, BitVec.ofNat 64 c.pay)]) (c.pay + o + j) = imgM M (c.pay + o + j) :=
    fun o w ho j hj => hm _ (hcIn _ (by simp only [Blk.In, Blk.pay, Blk.fin]; omega))
  refine
    { heap := hb1.subRaw (fun b hb => by
          change b ∈ ({ G with stk := (c, g) :: G.stk } : DcG).blocks at hb
          rw [G.blocks_pushStk] at hb; exact hb) fun _ _ _ _ => rfl
      nodup := by rw [G.blocks_pushStk]; exact List.nodup_cons.mpr ⟨hf.notG, h.nodup⟩
      view := h.view.withChains rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun o ho x hx => hblk x (hx.elim (fun hx => ⟨o.hb, (G.str_mem ho).1, hx⟩)
          fun hx => ⟨o.tb, (G.str_mem ho).2, hx⟩))
        (fun a ha hc => hm a fun hs => hc (.inl hs)) ?_ fun r hr => ?_
      den := ?_
      glob := h.glob
      col := h.col }
  · refine .cons (ldv_store_hit _ _ _) ⟨?_, ?_, hsz⟩ ?_
    · exact ⟨by rw [ldv_congr .ld fun j hj => hcw 0 8 (by omega) j hj]; exact hn.dat.tag,
        (ldv_congr .ld fun j hj => hcw 8 8 (by omega) j hj).trans hn.dat.ptr⟩
    · exact (ldv_congr .ld fun j hj => hcw 16 8 (by omega) j hj).trans hn.arr
    · refine stkChain_frame (h.view.stk.reword hl) (ldv_congr .ld fun j hj => hcw 24 8 (by omega) j hj)
        fun bg hmm x hx => hblk x ⟨bg.1, G.stk_mem hmm, hx⟩
  · refine regChain_frame (h.view.regs r hr)
      (ldv_congr .ld fun j hj => hm _ fun hs => by
        simp only [StkWord, widthOfM, regAddr, dc_addrs] at hj hs; omega)
      fun be hmm b hb x hx => hblk x ⟨b, by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact G.reg_mem hr hmm
        · obtain ⟨bn, hn, rfl⟩ := List.mem_map.mp hb
          exact G.arr_mem hr hmm hn, hx⟩
  · have hd := h.den
    exact
      { hd with
        stk := List.Forall₂.cons hv hd.stk
        hsDen := fun g' hg' => hd.hsDen g' (List.mem_cons_of_mem _ hg')
        numRefs := fun x hx => by
          rw [G.vals_pushStk, count_move]; exact hd.numRefs x hx
        strRefs := fun o ho => by
          rw [G.vals_pushStk, count_move]; exact hd.strRefs o ho }

/-- **The top node popped**: `dc_stack` takes the node's link; the handle
`g` (denoting `v`) passes to the caller, and the node `c` leaves the state
(`DcFresh`, still live). -/
theorem DcAt.popNode {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {c : Blk} {v : Val}
    (h : DcAt S M H F L C { G with stk := (c, g) :: G.stk } hs (st.push v)) :
    DcAt S (writeLog M [(dcStackAddr, 8, ldv .ld M (c.pay + 24))]) H F L C G (g :: hs) st ∧
      DcFresh H F L G c ∧ SNodeAt M c g ∧ g.Den ⟨L, G.strs⟩ v := by
  have hi := h.heap.heap
  have hm : MemOnly StkWord (writeLog M [(dcStackAddr, 8, ldv .ld M (c.pay + 24))]) M :=
    MemOnly.store M _ 8 _
  have hcG : c ∈ ({ G with stk := (c, g) :: G.stk } : DcG).blocks := by
    rw [G.blocks_pushStk]; exact List.mem_cons_self
  have hnd := h.nodup
  rw [G.blocks_pushStk] at hnd
  have hnotG : c ∉ G.blocks := (List.nodup_cons.mp hnd).1
  have hcl : c ∈ H.live := h.heap.raw.live c hcG
  have hbG : ∀ b ∈ G.blocks, b ∈ ({ G with stk := (c, g) :: G.stk } : DcG).blocks := fun b hb => by
    rw [G.blocks_pushStk]; exact List.mem_cons_of_mem _ hb
  have hstk : ∀ a, StkWord a → OutHeap a ∧ ¬ InBlocks G.blocks a := fun a ha =>
    ⟨DcGlob.outHeap (by simp only [StkWord, DcGlob, dc_addrs] at ha ⊢; omega), fun ⟨b, hb, hba⟩ => by
      have hbl : b ∈ H.live := h.heap.raw.live b (hbG b hb)
      have := live_in_heap hi hbl hba; simp only [StkWord, dc_addrs, heapStart] at ha this; omega⟩
  have hcIn : ∀ a, c.In a → ¬ StkWord a := fun a hca hs => by
    have := live_in_heap hi hcl hca; simp only [StkWord, dc_addrs, heapStart] at hs this; omega
  have hblk : ∀ a, InBlocks G.blocks a →
      imgM (writeLog M [(dcStackAddr, 8, ldv .ld M (c.pay + 24))]) a = imgM M a :=
    fun a ha => hm a fun hs => (hstk a hs).2 ha
  have hv0 := h.view.stk
  cases hv0 with
  | cons h0 hn hl =>
  have hd := h.den
  have hds := hd.stk
  cases hds with
  | cons hv hrest =>
  have hb1 := h.heap.out_frame hm fun a ha => (hstk a ha).1
  have hsz := hn.sz
  refine ⟨
    { heap := hb1.subRaw (fun b hb => hbG b hb)
          fun b hb a ha => (hblk a ⟨b, hb, ha⟩).symm
      nodup := (List.nodup_cons.mp hnd).2
      view := h.view.withChains rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun o ho x hx => hblk x (hx.elim (fun hx => ⟨o.hb, (G.str_mem ho).1, hx⟩)
          fun hx => ⟨o.tb, (G.str_mem ho).2, hx⟩))
        (fun a ha hc => hm a fun hs => hc (.inl hs)) ?_ fun r hr => ?_
      den := ?_
      glob := h.glob
      col := h.col },
    ⟨hcl, hnotG, h.heap.raw.out c hcG⟩, hn, hv⟩
  · have hcw : ldv .ld (writeLog M [(dcStackAddr, 8, ldv .ld M (c.pay + 24))]) (c.pay + 24) =
        ldv .ld M (c.pay + 24) :=
      ldv_congr .ld fun j hj => hm _ (hcIn _ (by simp only [Blk.In, Blk.pay, Blk.fin, widthOfM] at hj ⊢; omega))
    exact (stkChain_frame hl hcw fun bg hmm x hx => hblk x ⟨bg.1, G.stk_mem hmm, hx⟩).reword
      ((ldv_store_hit _ _ _).trans hcw.symm)
  · refine regChain_frame (h.view.regs r hr)
      (ldv_congr .ld fun j hj => hm _ fun hs => by
        simp only [StkWord, widthOfM, regAddr, dc_addrs] at hj hs; omega)
      fun be hmm b hb x hx => hblk x ⟨b, by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact G.reg_mem hr hmm
        · obtain ⟨bn, hn, rfl⟩ := List.mem_map.mp hb
          exact G.arr_mem hr hmm hn, hx⟩
  · exact
      { hd with
        stk := hrest
        hsDen := fun g' hg' => (List.mem_cons.mp hg').elim (fun e => e ▸ ⟨v, hv⟩)
          fun hg' => hd.hsDen g' hg'
        numRefs := fun x hx => by
          have e := hd.numRefs x hx; rw [G.vals_pushStk] at e; rw [← count_move]; exact e
        strRefs := fun o ho => by
          have e := hd.strRefs o ho; rw [G.vals_pushStk] at e; rw [← count_move]; exact e }

/-- **A block outside the state freed** (`free`'s `FreePost`). -/
theorem DcAt.free {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {c : Blk} {lpre lpost : List Blk}
    (h : DcAt S M H F L C G hs st) (hf : DcFresh H F L G c) (hl : H.live = lpre ++ c :: lpost)
    (hp : FreePost S M M' H H' c lpre lpost) : DcAt S M' H' F L C G hs st := by
  have hi := h.heap.heap
  have hno : c ∉ F ++ objBlocks L ++ (G.raws M).bs := fun hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact hf.notNum hc
    · exact hf.notG hc
  have hblk : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a := fun a ha =>
    hp.frame a (h.inBlocks_heap ha).2
  have hb1 := h.heap.freeRaw hl hno hp
  exact { h with
    heap := hb1.subRaw (fun b hb => hb) fun b hb a ha => (hblk a ⟨b, hb, ha⟩).symm
    view := h.view.frame hblk fun a ha => hp.frame a (OutHeap.not_alloc hi ha.outHeap) }

/-- The `dc_stack` word is readable and writable under `S`. -/
theorem DcAt.stkAcc {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S Mt H F L C G hs st) :
    ∀ b ∈ accAddrs dcStackAddr 8, S b := fun b hb => by
  have := of_mem_accAddrs hb
  exact h.glob b (by simp only [DcGlob, dc_addrs] at this ⊢; omega)

theorem ldOK_dcStack : LdOK dcStackAddr 8 := by
  simp only [LdOK, dc_addrs, tohostAddr]; omega

theorem stOK_dcStack : StOK dcStackAddr 8 := by
  simp only [StOK, dc_addrs, tohostAddr]
  refine ⟨by omega, by omega, by omega, ?_⟩
  decide

end Dc.Mach

/-! ## Side conditions of dc runs

`dx_run` cannot close an access to dc's globals, owned through
`hG : ∀ a, DcGlob a → S a` in context (`dc_glob_side`), or a side condition
given as a hypothesis (a `.rodata` word's
`∀ b ∈ accAddrs a 8, (b, dcROImg b) ∈ dcRO`, by `decide +kernel`). A file
running dc code adds `dc_side` (both) as its own rule, so it is tried first:

    local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)
-/

namespace Dc.Mach

/-- An access to dc's globals, owned through `hG : ∀ a, DcGlob a → S a`. -/
macro "dc_glob_side" : tactic =>
  `(tactic| (intro b hb; have hb' := VsaIris.Sym.of_mem_accAddrs hb; apply ‹∀ a, DcGlob a → _›; simp only [DcGlob, dc_addrs] at hb' ⊢; omega))

/-- `dc_glob_side` or a hypothesis. -/
macro "dc_side" : tactic => `(tactic| first | assumption | dc_glob_side)

end Dc.Mach
