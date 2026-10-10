import Dc.Mach.DcArray

/-!
# Storing into a register array (M9)

`dc_array_set (r, i, value)` at `0x80003c7c` replaces the datum of the node
with index `i` in register `r`'s top array, or inserts a fresh node before
the first node with a larger index (`arrSet`).

- `DcAt.setArr`: register `r`'s head level gets a new array chain `arr'`,
  built from the old nodes and fresh blocks `N`; the stores touch only those
  blocks and the level's array word. Both the replacement (viewed through a
  pending datum window) and the insertion are instances.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- Register `r`'s head level `be` shares no block with the rest of the state. -/
structure LevOnly (G : DcG) (r : Nat) (be : Blk × RLev) (l : List (Blk × RLev)) : Prop where
  stk : ∀ bg ∈ G.stk, bg.1 ∉ RLev.blocks be
  regs : ∀ r', r' < 256 → r' ≠ r → ∀ be' ∈ G.regs r', ∀ c ∈ RLev.blocks be', c ∉ RLev.blocks be
  tail : ∀ be' ∈ l, ∀ c ∈ RLev.blocks be', c ∉ RLev.blocks be
  strs : ∀ o ∈ G.strs, o.hb ∉ RLev.blocks be ∧ o.tb ∉ RLev.blocks be
  nodup : (RLev.blocks be).Nodup

theorem DcG.levOnly {G : DcG} {r : Nat} {be : Blk × RLev} {l : List (Blk × RLev)}
    (hnd : G.blocks.Nodup) (hr : r < 256) (hl : G.regs r = be :: l) : LevOnly G r be l := by
  obtain ⟨P, Q, hPQ, hf, -⟩ := flatMap_range_upd (f := fun r' => (G.regs r').flatMap RLev.blocks)
    (g := fun r' => (G.regs r').flatMap RLev.blocks) hr fun _ _ => rfl
  have hcount : ∀ c, (G.stk.map (·.1)).count c +
      (P.flatMap fun r' => (G.regs r').flatMap RLev.blocks).count c + (RLev.blocks be).count c +
      (l.flatMap RLev.blocks).count c + (Q.flatMap fun r' => (G.regs r').flatMap RLev.blocks).count c +
      (G.strs.flatMap fun o => [o.hb, o.tb]).count c ≤ 1 := fun c => by
    have h1 := nodup_count_le_one hnd c
    unfold DcG.blocks at h1
    rw [hf, hl] at h1
    simp only [List.count_append, List.flatMap_cons] at h1
    omega
  have z : ∀ (l' : List Blk) (c : Blk), l'.count c = 0 → ∀ c' ∈ l', c' ≠ c := fun l' c h0 c' hcl e => by
    subst e; exact List.count_eq_zero.mp h0 hcl
  have pos : ∀ c ∈ RLev.blocks be, 1 ≤ (RLev.blocks be).count c := fun c hc =>
    List.count_pos_iff.mpr hc
  refine ⟨fun bg hbg hc => z (G.stk.map (·.1)) bg.1 (by have := hcount bg.1; have := pos _ hc; omega) _
      (List.mem_map.mpr ⟨bg, hbg, rfl⟩) rfl,
    fun r' hr' hne be' hbe c hcm hc => ?_,
    fun be' hbe c hcm hc => z (l.flatMap RLev.blocks) c (by have := hcount c; have := pos _ hc; omega) _
      (List.mem_flatMap.mpr ⟨be', hbe, hcm⟩) rfl,
    fun o ho => ⟨fun hc => z (G.strs.flatMap fun o => [o.hb, o.tb]) o.hb (by have := hcount o.hb; have := pos _ hc; omega) _
        (List.mem_flatMap.mpr ⟨o, ho, by simp⟩) rfl,
      fun hc => z (G.strs.flatMap fun o => [o.hb, o.tb]) o.tb (by have := hcount o.tb; have := pos _ hc; omega) _
        (List.mem_flatMap.mpr ⟨o, ho, by simp⟩) rfl⟩,
    List.nodup_iff_count.mpr fun c => by have := hcount c; omega⟩
  have hm : r' ∈ P ++ r :: Q := hPQ ▸ List.mem_range.mpr hr'
  rcases List.mem_append.mp hm with hm | hm
  · exact z (P.flatMap fun r' => (G.regs r').flatMap RLev.blocks) c (by have := hcount c; have := pos _ hc; omega) _
      (List.mem_flatMap.mpr ⟨r', hm, List.mem_flatMap.mpr ⟨be', hbe, hcm⟩⟩) rfl
  · rcases List.mem_cons.mp hm with e | hm
    · exact hne e
    · exact z (Q.flatMap fun r' => (G.regs r').flatMap RLev.blocks) c (by have := hcount c; have := pos _ hc; omega) _
        (List.mem_flatMap.mpr ⟨r', hm, List.mem_flatMap.mpr ⟨be', hbe, hcm⟩⟩) rfl

/-- A datum through a memory agreeing on its 16 bytes. -/
theorem DatAt.congr16 {Mt Mt' : Mem} {a : Nat} {g : GV}
    (hag : ∀ x, a ≤ x → x < a + 16 → imgM Mt' x = imgM Mt x) (h : DatAt Mt a g) : DatAt Mt' a g :=
  ⟨by rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact h.tag,
    by rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact h.ptr⟩

/-- **Register `r`'s top array replaced**: the new chain `arr'` from the
level's array word, its blocks the old array's and the fresh blocks `N`, its
data the old array's data with `hs0` traded for `hs`. The memory changes
only inside `N`, the old array's nodes and the level's array word. -/
theorem DcAt.setArr {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs0 hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {en : Entry} {es : List Entry} {arr' : List (Blk × ANode)}
    {am : List (Nat × Val)} {N : List Blk}
    (h : DcAt S M H F L C G hs0 st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hst : st.regs r = en :: es) (hN : ∀ c ∈ N, DcFresh H F L G c) (hNd : N.Nodup)
    (hperm : (arr'.map (·.1)).Perm (N ++ e.arr.map (·.1)))
    (hcnt : ∀ y, (arr'.map (·.2.v) ++ hs).count y = (e.arr.map (·.2.v) ++ hs0).count y)
    (hm : MemOnly (fun x => InBlocks (N ++ e.arr.map (·.1)) x ∨ (b.pay + 16 ≤ x ∧ x < b.pay + 24)) M' M)
    (hch : LChain M' 24 (ANodeAt M') (b.pay + 16) arr')
    (hden : List.Forall₂ (fun (be : Blk × ANode) (iv : Nat × Val) => be.2.idx = iv.1 ∧
      be.2.v.Den ⟨L, G.strs⟩ iv.2) arr' am)
    (hsd : ∀ g ∈ hs, ∃ v, g.Den ⟨L, G.strs⟩ v) :
    DcAt S M' H F L C (G.setReg r ((b, { e with arr := arr' }) :: l)) hs
      (st.setReg r ({ en with arr := am } :: es)) := by
  have hi := h.heap.heap
  have lo := G.levOnly h.nodup hr hl
  have hbe : (b, e) ∈ G.regs r := by rw [hl]; exact List.mem_cons_self
  have hlevG : ∀ c ∈ RLev.blocks (b, e), c ∈ G.blocks := fun c hc => G.lev_mem hr hbe hc
  have hbG : b ∈ G.blocks := hlevG b List.mem_cons_self
  have hbl := h.heap.raw.live b hbG
  have hchg : ∀ x, InBlocks (N ++ e.arr.map (·.1)) x ∨ (b.pay + 16 ≤ x ∧ x < b.pay + 24) →
      ∃ c, (c ∈ N ∨ c ∈ RLev.blocks (b, e)) ∧ c ∈ H.live ∧ c.In x := fun x hx => by
    rcases hx with ⟨c, hc, hcx⟩ | hw
    · rcases List.mem_append.mp hc with hc | hc
      · exact ⟨c, .inl hc, (hN c hc).live, hcx⟩
      · have hc' : c ∈ RLev.blocks (b, e) := List.mem_cons_of_mem _ hc
        exact ⟨c, .inr hc', h.heap.raw.live c (hlevG c hc'), hcx⟩
    · have hv0 := h.view.regs r hr
      rw [hl] at hv0
      have hsz : 32 ≤ b.sz := by cases hv0 with | cons _ hp _ => exact hp.sz
      exact ⟨b, .inr List.mem_cons_self, hbl, by simp only [Blk.In, Blk.pay, Blk.fin] at hw ⊢; omega⟩
  -- bytes of other live blocks are unchanged
  have hoff : ∀ c' ∈ H.live, c' ∉ N → c' ∉ RLev.blocks (b, e) → ∀ x, c'.In x →
      imgM M' x = imgM M x := fun c' hc' hn hlv x hx => hm x fun hP => by
    obtain ⟨c, hc, hcl, hcx⟩ := hchg x hP
    exact live_apart hi hc' hcl (fun e => hc.elim (fun hc => hn (e ▸ hc)) fun hc => hlv (e ▸ hc)) hx hcx
  have hGoff : ∀ c' ∈ G.blocks, c' ∉ RLev.blocks (b, e) → ∀ x, c'.In x → imgM M' x = imgM M x :=
    fun c' hc' hlv => hoff c' (h.heap.raw.live c' hc') (fun hn => (hN c' hn).notG hc') hlv
  have hnheap : ∀ x, ¬ (heapStart ≤ x ∧ x < heapEnd) → imgM M' x = imgM M x := fun x hx =>
    hm x fun hP => by
      obtain ⟨c, -, hcl, hcx⟩ := hchg x hP
      exact hx (live_in_heap hi hcl hcx)
  have hglob : ∀ x, DcGlob x → imgM M' x = imgM M x := fun x hx =>
    hnheap x fun h' => by have := hx.lt; omega
  -- the new block list
  have hperm' : (G.setReg r ((b, { e with arr := arr' }) :: l)).blocks.Perm (N ++ G.blocks) := by
    rw [List.perm_iff_count]
    intro y
    have h1 := G.setReg_blocks_count hr ((b, { e with arr := arr' }) :: l) y
    have h2 := List.perm_iff_count.mp hperm y
    rw [hl] at h1
    simp only [List.flatMap_cons, RLev.blocks, List.count_append, List.count_cons] at h1 h2 ⊢
    omega
  have hnd' : (N ++ G.blocks).Nodup := List.nodup_append.mpr ⟨hNd, h.nodup,
    fun c hc c' hc' e => (hN c hc).notG (e ▸ hc')⟩
  -- the number heap
  have hb0 : BcHeap S (G.rawsOff (RLev.blocks (b, e)) M) M H F L :=
    h.heap.subRaw (fun c hc => (DcG.mem_rawsOff.mp hc).1) fun _ _ _ _ => rfl
  have hb1 : BcHeap S (G.rawsOff (RLev.blocks (b, e)) M) M' H F L :=
    hb0.transportOwn (fun x hx => hm x fun hP => by
        obtain ⟨c, -, hcl, hcx⟩ := hchg x hP
        exact live_not_alloc hi hcl hcx hx)
      (fun c hc x hx => by
        rcases List.mem_append.mp hc with hc | hc
        · exact hoff c (h.heap.owned_live (List.mem_append_left _ hc))
            (fun hn => (hN c hn).notNum hc) (fun hlv => h.heap.raw.out c (hlevG c hlv) hc) x hx
        · obtain ⟨hcG, hcE⟩ := DcG.mem_rawsOff.mp hc
          exact hGoff c hcG hcE x hx)
      fun j hj => hnheap _ fun h' => by simp only [bcFreeAddr, heapStart] at h'; omega
  have hb2 := hb1.addRaws (bs := N ++ RLev.blocks (b, e))
    (fun c hc => (List.mem_append.mp hc).elim (fun hc => (hN c hc).live)
      fun hc => h.heap.raw.live c (hlevG c hc))
    fun c hc => (List.mem_append.mp hc).elim (fun hc => (hN c hc).notNum)
      fun hc => h.heap.raw.out c (hlevG c hc)
  -- the old register chain and denotation
  have hv0 := h.view.regs r hr
  rw [hl] at hv0
  have hd0 := h.den.regs r hr
  rw [hl, hst] at hd0
  cases hv0 with
  | cons hw0 hp0 hrest0 =>
  cases hd0 with
  | cons hen hdrest =>
  have hsz := hp0.sz
  refine
    { heap := hb2.subRaw (fun c hc => ?_) fun _ _ _ _ => rfl
      nodup := hperm'.nodup_iff.mpr hnd'
      view := h.view.withChains rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun o ho x hx => hx.elim (fun hx => hGoff _ (G.str_mem ho).1 (lo.strs o ho).1 x hx)
          fun hx => hGoff _ (G.str_mem ho).2 (lo.strs o ho).2 x hx)
        (fun x hx _ => hglob x hx)
        (stkChain_frame h.view.stk (ldv_congr .ld fun j hj => hglob _ (by
          simp only [widthOfM, DcGlob, dc_addrs] at hj ⊢; omega))
          fun bg hmm x hx => hGoff _ (G.stk_mem hmm) (lo.stk bg hmm) x hx) fun r' hr' => ?_
      den := ?_
      glob := h.glob
      col := h.col }
  · rcases List.mem_append.mp (hperm'.mem_iff.mp hc) with hc | hc
    · exact List.mem_append_left _ (List.mem_append_left _ hc)
    · by_cases hcE : c ∈ RLev.blocks (b, e)
      · exact List.mem_append_left _ (List.mem_append_right _ hcE)
      · exact List.mem_append_right _ (DcG.mem_rawsOff.mpr ⟨hc, hcE⟩)
  · have e1 : (G.setReg r ((b, { e with arr := arr' }) :: l)).regs r' =
        if r' = r then (b, { e with arr := arr' }) :: l else G.regs r' := rfl
    rw [e1]
    split
    · subst_vars
      have hdat : ∀ x, b.pay ≤ x → x < b.pay + 16 → imgM M' x = imgM M x := fun x h1 h2 =>
        hm x fun hP => by
          rcases hP with ⟨c, hc, hcx⟩ | hw
          · rcases List.mem_append.mp hc with hc | hc
            · exact live_apart hi (hN c hc).live hbl (fun e => (hN c hc).notG (e ▸ hbG)) hcx
                (by simp only [Blk.In, Blk.pay, Blk.fin] at h1 h2 hcx hsz ⊢; omega)
            · obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hc
              have hne : bn.1 ≠ b := fun e => List.nodup_cons.mp lo.nodup |>.1
                (e ▸ List.mem_map.mpr ⟨bn, hbn, rfl⟩)
              exact live_apart hi (h.heap.raw.live _ (G.arr_mem hr' hbe hbn)) hbl hne hcx
                (by simp only [Blk.In, Blk.pay, Blk.fin] at h1 h2 hcx hsz ⊢; omega)
          · omega
      refine .cons ((ldv_congr .ld fun j hj => hglob _ (by
          simp only [widthOfM, DcGlob, regAddr, dc_addrs] at hj ⊢; omega)).trans hw0)
        ⟨?_, hch, hsz⟩ (regChain_frame hrest0 (ldv_congr .ld fun j hj => hm _ fun hP => by
          rcases hP with ⟨c, hc, hcx⟩ | hw
          · rcases List.mem_append.mp hc with hc | hc
            · exact live_apart hi (hN c hc).live hbl (fun e => (hN c hc).notG (e ▸ hbG)) hcx
                (by simp only [widthOfM, Blk.In, Blk.pay, Blk.fin] at hj hcx hsz ⊢; omega)
            · obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hc
              have hne : bn.1 ≠ b := fun e => List.nodup_cons.mp lo.nodup |>.1
                (e ▸ List.mem_map.mpr ⟨bn, hbn, rfl⟩)
              exact live_apart hi (h.heap.raw.live _ (G.arr_mem hr' hbe hbn)) hbl hne hcx
                (by simp only [widthOfM, Blk.In, Blk.pay, Blk.fin] at hj hcx hsz ⊢; omega)
          · simp only [widthOfM] at hj; omega)
          fun be hmm c hc x hx => hGoff c (G.lev_mem hr' (by rw [hl]; exact List.mem_cons_of_mem _ hmm) hc)
            (lo.tail be hmm c hc) x hx)
      have hd := hp0.dat
      revert hd
      cases e.v with
      | some g => exact fun hd => DatAt.congr16 hdat hd
      | none =>
        intro hd
        simp only at hd ⊢
        rw [ldv_congr .lw fun j hj => hdat _ (by omega) (by simp only [widthOfM] at hj; omega)]
        exact hd
    · exact regChain_frame (h.view.regs r' hr') (ldv_congr .ld fun j hj => hglob _ (by
        simp only [widthOfM, DcGlob, regAddr, dc_addrs] at hj ⊢; omega))
        fun be hmm c hc x hx => hGoff c (G.lev_mem hr' hmm hc) (lo.regs r' hr' ‹_› be hmm c hc) x hx
  · have hd := h.den
    have hcount : ∀ y, ((G.setReg r ((b, { e with arr := arr' }) :: l)).vals ++ hs).count y =
        (G.vals ++ hs0).count y := fun y => by
      have h1 := G.setReg_vals_count hr ((b, { e with arr := arr' }) :: l) y
      have h2 := hcnt y
      rw [hl] at h1
      simp only [List.flatMap_cons, RLev.vals, List.count_append] at h1 h2 ⊢
      omega
    refine { hd with
      regs := fun r' hr' => ?_
      regsHi := fun r' hr' => ?_
      hsDen := hsd
      numRefs := fun x hx => by rw [hcount]; exact hd.numRefs x hx
      strRefs := fun o ho => by rw [hcount]; exact hd.strRefs o ho }
    · simp only [DcG.setReg, St.setReg]
      split
      · subst_vars; exact .cons ⟨hen.val, hden⟩ hdrest
      · exact hd.regs r' hr'
    · have hne : r' ≠ r := by omega
      simp only [DcG.setReg, St.setReg, hne, ite_false]; exact hd.regsHi r' hr'

/-! ## The search loop -/

/-- The word naming the last node of `pre`, or `0`. -/
def lastPtr (pre : List (Blk × ANode)) : BitVec 64 :=
  match pre.getLast? with
  | none => 0#64
  | some bx => BitVec.ofNat 64 bx.1.pay

/-- The word naming the first node of `post`, or `0`. -/
def headPtr : List (Blk × ANode) → BitVec 64
  | [] => 0#64
  | bx :: _ => BitVec.ofNat 64 bx.1.pay

theorem lastPtr_concat (pre : List (Blk × ANode)) (bx : Blk × ANode) :
    lastPtr (pre ++ [bx]) = BitVec.ofNat 64 bx.1.pay := by
  simp [lastPtr]

/-- `dc_array_set`'s search loop (`0x80003cc4`, `s0` the node `b`, `a4` the
node before, `s1` the index `i`): it stops at the node with index `i`
(`0x80003d20`) or before the first node with a larger index (`0x80003cd0`). -/
theorem as_walk {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {i : Nat} (hi : i < 2 ^ 31)
    {all : List (Blk × ANode)} :
    ∀ {b : Blk} {x : ANode} {l pre0 : List (Blk × ANode)},
    all = pre0 ++ (b, x) :: l →
    PChain M 24 (ANodeAt M) (BitVec.ofNat 64 b.pay) ((b, x) :: l) →
    (∀ bx ∈ (b, x) :: l, heapStart + 16 ≤ bx.1.pay ∧ bx.1.pay + 32 ≤ heapEnd ∧ bx.1.pay % 16 = 0) →
    (∀ bx ∈ pre0, bx.2.idx < i) →
    ∀ (R : Nat → BitVec 64), R 8 = BitVec.ofNat 64 b.pay → R 9 = BitVec.ofNat 64 i →
    R 14 = lastPtr pre0 →
    (∀ R' pre c y post, all = pre ++ (c, y) :: post → (∀ bx ∈ pre, bx.2.idx < i) → y.idx = i →
      Keeps [8, 14, 15] R' R → R' 8 = BitVec.ofNat 64 c.pay → DW live S Q 0x80003d20#64 R' M) →
    (∀ R' pre post, all = pre ++ post → (∀ bx ∈ pre, bx.2.idx < i) →
      (∀ bx ∈ post.head?, i < bx.2.idx) → Keeps [8, 14, 15] R' R → R' 8 = headPtr post →
      R' 14 = lastPtr pre → DW live S Q 0x80003cd0#64 R' M) →
    DW live S Q 0x80003cc4#64 R M := by
  intro b x l
  induction l generalizing b x with
  | nil => ?_
  | cons y l ih => ?_
  all_goals
    intro pre0 hall hc hb hpre R h8 h9 h14 hfd hins
    have htx : tohostAddr = 0x8001ad00 := rfl
    obtain ⟨hb1, hb2, hb3⟩ := hb (b, x) List.mem_cons_self
    simp only [heapStart, heapEnd] at hb1 hb2
    obtain ⟨hn, hl⟩ := hc.uncons
    have hidx := hn.idx
    have hil := hn.idxLt
    have ci : (BitVec.ofNat 64 x.idx).toInt = x.idx := toInt_ofNat_small (by omega)
    have cj : (BitVec.ofNat 64 i).toInt = i := toInt_ofNat_small (by omega)
    bc_run hlive hS [h8, h9, hidx, ci, cj] at 0x80003ccc
    all_goals first | (intro hlt; bc_run hlive hS [h8, h9, hidx, ci, cj] at 0x80003cb4) | skip
  -- the empty rest: the link is null, insert at the end
  · intro hlt
    have hlt' : x.idx < i := by
      have c1 : (BitVec.ofNat 64 x.idx).toInt = x.idx := toInt_ofNat_small (by omega)
      have c2 : (BitVec.ofNat 64 i).toInt = i := toInt_ofNat_small (by omega)
      omega
    have hz := hl.nil_eq
    bc_run hlive hS [h8, hz] at 0x80003cd0
    all_goals try (intro hc; exact (hc rfl).elim)
    try intro _
    bc_run hlive hS [] at 0x80003cd0
    refine hins _ (pre0 ++ [(b, x)]) [] (by rw [hall, List.append_nil]) (fun bx hm => (List.mem_append.mp hm).elim
      (hpre bx) fun hm => by rw [List.mem_singleton.mp hm]; exact hlt') (fun _ h => (by cases h))
      ?_ ?_ ?_
    · keeps_tac Keeps.refl _ _
    · bsimp []; rfl
    · rw [lastPtr_concat]; bsimp []
  · intro heq
    have e : x.idx = i := by
      have := congrArg BitVec.toNat heq; simp only [BitVec.toNat_ofNat] at this; omega
    refine hfd _ pre0 b x [] hall hpre e ?_ ?_
    · keeps_tac Keeps.refl _ _
    · bsimp [h8]
  · intro hne
    have hge : ¬ x.idx < i := fun h => by
      have c1 : (BitVec.ofNat 64 x.idx).toInt = x.idx := toInt_ofNat_small (by omega)
      have c2 : (BitVec.ofNat 64 i).toInt = i := toInt_ofNat_small (by omega)
      omega
    have e : x.idx ≠ i := fun e => hne (by rw [e])
    refine hins _ pre0 ((b, x) :: []) hall hpre (fun bx hm => ?_) ?_ ?_ ?_
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm; subst hm
      show i < x.idx; omega
    · keeps_tac Keeps.refl _ _
    · bsimp [h8]; rfl
    · bsimp [h14]
  -- a next node: around the loop
  · intro hlt
    have hlt' : x.idx < i := by
      have c1 : (BitVec.ofNat 64 x.idx).toInt = x.idx := toInt_ofNat_small (by omega)
      have c2 : (BitVec.ofNat 64 i).toInt = i := toInt_ofNat_small (by omega)
      omega
    obtain ⟨b', x'⟩ := y
    have he := hl.head_eq
    obtain ⟨hb1', hb2', -⟩ := hb (b', x') (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [heapStart, heapEnd] at hb1' hb2'
    have hnz : BitVec.ofNat 64 b'.pay ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    bc_run hlive hS [h8, he] at 0x80003cc4
    all_goals try (intro hc; exact (hnz hc).elim)
    try intro _
    bc_run hlive hS [] at 0x80003cc4
    rw [he] at hl
    refine ih (pre0 := pre0 ++ [(b, x)]) (by rw [hall, List.append_assoc]; rfl) hl
      (fun bx hm => hb bx (List.mem_cons_of_mem _ hm))
      (fun bx hm => (List.mem_append.mp hm).elim (hpre bx) fun hm => by
        rw [List.mem_singleton.mp hm]; exact hlt') _ ?_ ?_ ?_
      (fun R' pre c y post e1 e2 e3 hk1 e4 => ?_) fun R' pre post e1 e2 e3 hk1 e4 e5 => ?_
    · bsimp []
    · bsimp [h9]
    · rw [lastPtr_concat]; bsimp []
    · exact hfd R' pre c y post e1 e2 e3 (hk1.trans (by keeps_tac Keeps.refl _ _)) e4
    · exact hins R' pre post e1 e2 e3 (hk1.trans (by keeps_tac Keeps.refl _ _)) e4 e5
  · intro heq
    have e : x.idx = i := by
      have := congrArg BitVec.toNat heq; simp only [BitVec.toNat_ofNat] at this; omega
    refine hfd _ pre0 b x _ hall hpre e ?_ ?_
    · keeps_tac Keeps.refl _ _
    · bsimp [h8]
  · intro hne
    have e : x.idx ≠ i := fun e => hne (by rw [e])
    refine hins _ pre0 ((b, x) :: _) hall hpre (fun bx hm => ?_) ?_ ?_ ?_
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm; subst hm
      show i < x.idx
      have c1 : (BitVec.ofNat 64 x.idx).toInt = x.idx := toInt_ofNat_small (by omega)
      have c2 : (BitVec.ofNat 64 i).toInt = i := toInt_ofNat_small (by omega)
      omega
    · keeps_tac Keeps.refl _ _
    · bsimp [h8]; rfl
    · bsimp [h14]

/-! ## Splicing a chain -/

/-- The address of the link word after the nodes `pre` of a chain from `a`. -/
def lend {α : Type} (off a : Nat) : List (Blk × α) → Nat
  | [] => a
  | bx :: l => lend off (bx.1.pay + off) l

/-- The link words of a chain from `a`: `a` and each node's. -/
abbrev links {α : Type} (off a : Nat) (l : List (Blk × α)) : List Nat :=
  a :: l.map (fun bx => bx.1.pay + off)

theorem lend_mem {α : Type} (off : Nat) :
    ∀ (a : Nat) (pre : List (Blk × α)), lend off a pre ∈ links off a pre
  | a, [] => List.mem_cons_self
  | a, bx :: l => List.mem_cons_of_mem _ (lend_mem off (bx.1.pay + off) l)

theorem lend_append {α : Type} (off : Nat) :
    ∀ (a : Nat) (pre : List (Blk × α)) (bx : Blk × α),
      lend off a (pre ++ [bx]) = bx.1.pay + off
  | a, [], bx => rfl
  | a, _ :: l, bx => lend_append off _ l bx

/-- A chain whose first word moved: read from `a'` at the new memory. -/
theorem LChain.move {α : Type} {Mt Mt' : Mem} {off : Nat} {P P' : Blk → α → Prop} {a a' : Nat}
    {l : List (Blk × α)} (h : LChain Mt off P a l) (ha : ldv .ld Mt' a' = ldv .ld Mt a)
    (hb : ∀ bx ∈ l, P bx.1 bx.2 → P' bx.1 bx.2 ∧
      ldv .ld Mt' (bx.1.pay + off) = ldv .ld Mt (bx.1.pay + off)) :
    LChain Mt' off P' a' l := by
  cases h with
  | nil h0 => exact .nil (ha.trans h0)
  | cons h0 hp hl =>
    obtain ⟨hp', hw⟩ := hb _ List.mem_cons_self hp
    exact .cons (ha.trans h0) hp' (hl.frame hw fun bx hm => hb bx (List.mem_cons_of_mem _ hm))

/-- **A node spliced in** after the nodes `pre`: the link word there names
`c`, `c`'s link holds the old one, every other link word is kept. -/
theorem LChain.insert {α : Type} {Mt Mt' : Mem} {off : Nat} {P P' : Blk → α → Prop} {c : Blk}
    {y : α} : ∀ {a : Nat} {pre post : List (Blk × α)}, LChain Mt off P a (pre ++ post) →
    (links off a (pre ++ post)).Nodup →
    (∀ bx ∈ pre ++ post, P bx.1 bx.2 → P' bx.1 bx.2) →
    (∀ a' ∈ links off a (pre ++ post), a' ≠ lend off a pre → ldv .ld Mt' a' = ldv .ld Mt a') →
    ldv .ld Mt' (lend off a pre) = BitVec.ofNat 64 c.pay → P' c y →
    ldv .ld Mt' (c.pay + off) = ldv .ld Mt (lend off a pre) →
    LChain Mt' off P' a (pre ++ (c, y) :: post)
  | a, [], post, h, hnd, hp, hw, hl, hc, hc24 => by
    refine .cons hl hc (h.move hc24 fun bx hm hq => ⟨hp bx hm hq, hw _ ?_ ?_⟩)
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨bx, hm, rfl⟩)
    · intro e
      exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨bx, hm, e⟩)
  | a, (b, x) :: pre, post, h, hnd, hp, hw, hl, hc, hc24 => by
    cases h with
    | cons h0 hq hrest =>
    have hnd' := (List.nodup_cons.mp hnd).2
    have hne : a ≠ lend off a ((b, x) :: pre) := fun e => (List.nodup_cons.mp hnd).1 (by
      rw [e]
      have hm := lend_mem off (b.pay + off) pre
      rcases List.mem_cons.mp hm with h1 | h1
      · rw [show lend off a ((b, x) :: pre) = lend off (b.pay + off) pre from rfl, h1]
        exact List.mem_map.mpr ⟨(b, x), List.mem_cons_self, rfl⟩
      · obtain ⟨bx, hbx, h2⟩ := List.mem_map.mp h1
        exact List.mem_map.mpr ⟨bx, List.mem_cons_of_mem _ (List.mem_append_left _ hbx), h2⟩)
    refine .cons ((hw a List.mem_cons_self hne).trans h0) (hp _ List.mem_cons_self hq) ?_
    exact LChain.insert hrest hnd' (fun bx hm => hp bx (List.mem_cons_of_mem _ hm))
      (fun a' ha' hne' => hw a' (List.mem_cons_of_mem _ ha') hne') hl hc hc24

/-- **A node's ghost replaced** in place, every link word kept. -/
theorem LChain.update {α : Type} {Mt Mt' : Mem} {off : Nat} {P P' : Blk → α → Prop} {c : Blk}
    {y y' : α} : ∀ {a : Nat} {pre post : List (Blk × α)}, LChain Mt off P a (pre ++ (c, y) :: post) →
    (∀ bx ∈ pre ++ post, P bx.1 bx.2 → P' bx.1 bx.2) → (P c y → P' c y') →
    (∀ a' ∈ links off a (pre ++ (c, y) :: post), ldv .ld Mt' a' = ldv .ld Mt a') →
    LChain Mt' off P' a (pre ++ (c, y') :: post)
  | a, [], post, h, hp, hc, hw => by
    cases h with
    | cons h0 hq hrest =>
    refine .cons ((hw a List.mem_cons_self).trans h0) (hc hq) (hrest.frame
      (hw _ (List.mem_cons_of_mem _ List.mem_cons_self)) fun bx hm hq' =>
        ⟨hp bx hm hq', hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨bx, hm, rfl⟩)))⟩)
  | a, (b, x) :: pre, post, h, hp, hc, hw => by
    cases h with
    | cons h0 hq hrest =>
    exact .cons ((hw a List.mem_cons_self).trans h0) (hp _ List.mem_cons_self hq)
      (LChain.update hrest (fun bx hm => hp bx (List.mem_cons_of_mem _ hm)) hc
        fun a' ha' => hw a' (List.mem_cons_of_mem _ ha'))

/-- A pairwise relation over an appended left list splits. -/
theorem forall₂_split {α β : Type} {R : α → β → Prop} :
    ∀ {l1 l2 : List α} {m : List β}, List.Forall₂ R (l1 ++ l2) m →
      ∃ m1 m2, m = m1 ++ m2 ∧ List.Forall₂ R l1 m1 ∧ List.Forall₂ R l2 m2
  | [], _, m, h => ⟨[], m, rfl, .nil, h⟩
  | _ :: l1, l2, _ :: m, .cons h t => by
    obtain ⟨m1, m2, e, h1, h2⟩ := forall₂_split (l1 := l1) t
    exact ⟨_ :: m1, m2, by rw [e]; rfl, .cons h h1, h2⟩

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l1 l2 : List α} {m1 m2 : List β}, List.Forall₂ R l1 m1 → List.Forall₂ R l2 m2 →
      List.Forall₂ R (l1 ++ l2) (m1 ++ m2)
  | [], _, [], _, .nil, h2 => h2
  | _ :: _, _, _ :: _, _, .cons h t, h2 => .cons h (forall₂_append t h2)

/-- An array node through a memory agreeing on its first 24 bytes. -/
theorem ANodeAt.congr24 {Mt Mt' : Mem} {c : Blk} {n : ANode} (hq : ANodeAt Mt c n)
    (hag : ∀ x, c.pay ≤ x → x < c.pay + 24 → imgM Mt' x = imgM Mt x) : ANodeAt Mt' c n :=
  ⟨by rw [ldv_congr .lw fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]; exact hq.idx,
    hq.idxLt, DatAt.congr16 (fun x h1 h2 => hag x (by omega) (by omega)) hq.dat, hq.sz⟩

/-- An array node denotes an index and value. -/
abbrev ARel (O : DObjs) (be : Blk × ANode) (iv : Nat × Val) : Prop :=
  be.2.idx = iv.1 ∧ be.2.v.Den O iv.2

/-- **A datum window inside a block is pending**. -/
theorem pend_datIn {G : DcG} {b : Blk} (hb : b ∈ G.blocks) (hns : ∀ o ∈ G.strs, o.hb ≠ b ∧ o.tb ≠ b)
    {a : Nat} (ha : b.pay ≤ a ∧ a + 16 ≤ b.pay + b.sz) (w0 w1 : BitVec 64) :
    Pend G [b] (datWin a) (fun M => datW M a w0 w1) where
  out M x hx := by
    simp only [datWin] at hx
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  fix M M' x hx := by
    simp only [datWin] at hx
    by_cases h8 : x < a + 8
    · have hm : x < a + 8 ∨ a + 8 + 8 ≤ x := .inl h8
      rw [imgM_store_miss (writeLog M [(a, 8, w0)]) w1 hm,
        imgM_store_miss (writeLog M' [(a, 8, w0)]) w1 hm]
      exact imgM_store_same _ _ w0 (.inr rfl) ⟨hx.1, h8⟩
    · exact imgM_store_same _ _ w1 (.inr rfl) ⟨by omega, by omega⟩
  sub e he := by rw [List.mem_singleton.mp he]; exact hb
  win x hx := ⟨b, List.mem_singleton_self _, by
    simp only [datWin, Blk.In, Blk.pay, Blk.fin] at hx ha ⊢; omega⟩
  nstr e he o ho := by
    rw [List.mem_singleton.mp he]; exact ⟨(hns o ho).1.symm, (hns o ho).2.symm⟩

/-- **A node's value replaced, before the old one is released**: viewed at
the memory with the new datum stored over node `c`'s datum, the node holds
`g` (denoting `v`) and the old datum is a handle; the machine memory is
pending on the node's datum window. -/
theorem DcAt.setNode {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {en : Entry} {es : List Entry} {pre post : List (Blk × ANode)}
    {c : Blk} {x : ANode} {m1 m2 : List (Nat × Val)} {v : Val} {w0 w1 : BitVec 64}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hst : st.regs r = en :: es) (harr : e.arr = pre ++ (c, x) :: post)
    (hm1 : List.Forall₂ (ARel ⟨L, G.strs⟩) pre m1) (hm2 : List.Forall₂ (ARel ⟨L, G.strs⟩) post m2)
    (hd : DatRegs w0 w1 g) (hv : g.Den ⟨L, G.strs⟩ v) (hxv : ∃ w, x.v.Den ⟨L, G.strs⟩ w) :
    DcAt S (datW M (c.pay + 8) w0 w1) H F L C
        (G.setReg r ((b, { e with arr := pre ++ (c, ⟨x.idx, g⟩) :: post }) :: l)) (x.v :: hs)
        (st.setReg r ({ en with arr := m1 ++ (x.idx, v) :: m2 } :: es)) ∧
      Pend (G.setReg r ((b, { e with arr := pre ++ (c, ⟨x.idx, g⟩) :: post }) :: l)) [c]
        (datWin (c.pay + 8)) (fun M => datW M (c.pay + 8) w0 w1) := by
  have hi := h.heap.heap
  have lo := G.levOnly h.nodup hr hl
  have hbe : (b, e) ∈ G.regs r := by rw [hl]; exact List.mem_cons_self
  have hcA : (c, x) ∈ e.arr := by rw [harr]; exact List.mem_append_right _ List.mem_cons_self
  have hcG : c ∈ G.blocks := G.arr_mem hr hbe hcA
  have hcl := h.heap.raw.live c hcG
  obtain ⟨hw0, hp0⟩ := h.regWord hr hl
  have hch0 := hp0.arr
  rw [harr] at hch0
  have hnc := hch0.forall (c, x) (List.mem_append_right _ List.mem_cons_self)
  have hcsz := hnc.sz
  have hcb : c ∈ RLev.blocks (b, e) := RLev.mem_blocks_arr (be := (b, e)) (bn := (c, x)) hcA
  -- the stores touch only `c`'s datum
  have hwin : ∀ y, ¬ (c.pay + 8 ≤ y ∧ y < c.pay + 24) → imgM (datW M (c.pay + 8) w0 w1) y = imgM M y :=
    fun y hy => by rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hoth : ∀ c' ∈ H.live, c' ≠ c → ∀ y, c'.In y → imgM (datW M (c.pay + 8) w0 w1) y = imgM M y :=
    fun c' hc' hne y hy => hwin y fun hw => live_apart hi hc' hcl hne hy (by
      simp only [Blk.In, Blk.pay, Blk.fin] at hw hcsz ⊢; omega)
  have hn : (pre.map (·.1) ++ c :: post.map (·.1)).Nodup := by
    have := (List.nodup_cons.mp lo.nodup).2
    simpa [RLev.blocks, harr] using this
  have hpre : ∀ bx ∈ pre ++ post, bx.1 ≠ c := fun bx hm e1 => by
    obtain ⟨-, hB, hdis⟩ := List.nodup_append.mp hn
    rcases List.mem_append.mp hm with hm | hm
    · exact hdis _ (List.mem_map.mpr ⟨bx, hm, rfl⟩) _ List.mem_cons_self e1
    · exact (List.nodup_cons.mp hB).1 (e1 ▸ List.mem_map.mpr ⟨bx, hm, rfl⟩)
  have hmemA : ∀ bx ∈ pre ++ post, bx ∈ e.arr := fun bx hm => by
    rw [harr]
    rcases List.mem_append.mp hm with hm | hm
    · exact List.mem_append_left _ hm
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
  have hbl := h.heap.raw.live b (G.reg_mem hr hbe)
  have hbsz := hp0.sz
  have hbc : b ≠ c := fun e1 => (List.nodup_cons.mp lo.nodup).1 (e1 ▸ List.mem_map.mpr ⟨_, hcA, rfl⟩)
  have h1 := h.setArr (N := []) (hs := x.v :: hs) (arr' := pre ++ (c, ⟨x.idx, g⟩) :: post)
    (am := m1 ++ (x.idx, v) :: m2) hr hl hst (fun _ h => (by cases h)) List.nodup_nil
    (List.Perm.of_eq (by simp [harr]))
    (fun y => by
      rw [harr]
      simp only [List.map_append, List.map_cons, List.count_append, List.count_cons]
      omega)
    (fun y hy => hwin y fun hw => hy (.inl ⟨c, by simp [harr], by
      simp only [Blk.In, Blk.pay, Blk.fin] at hw hcsz ⊢; omega⟩))
    (hch0.update (P' := ANodeAt (datW M (c.pay + 8) w0 w1))
      (fun bx hm hq => hq.congr24 fun y h1 h2 => hoth bx.1
        (h.heap.raw.live _ (G.arr_mem hr hbe (hmemA bx hm))) (hpre bx hm) y (by
          have := hq.sz; simp only [Blk.In, Blk.pay, Blk.fin] at h1 h2 this ⊢; omega))
      (fun hq => ⟨by
          rw [ldv_congr .lw fun j hj => hwin _ (by simp only [widthOfM] at hj; omega)]; exact hq.idx,
        hq.idxLt, slotMem_dat hd, hq.sz⟩)
      fun a' ha' => ldv_congr .ld fun j hj => hwin _ fun hw => by
        simp only [widthOfM] at hj
        simp only [links, List.mem_cons, List.mem_map] at ha'
        rcases ha' with rfl | ⟨bx, hbx, rfl⟩
        · exact live_apart hi hbl hcl hbc (a := b.pay + 16 + j)
            (by simp only [Blk.In, Blk.pay, Blk.fin] at hbsz ⊢; omega)
            (by simp only [Blk.In, Blk.pay, Blk.fin] at hw hcsz ⊢; omega)
        · by_cases hbc' : bx.1 = c
          · rw [hbc'] at hw; omega
          · have hbm : bx ∈ e.arr := by rw [harr]; exact hbx
            have hq := hp0.arr.forall bx hbm
            have := hq.sz
            exact live_apart hi (h.heap.raw.live _ (G.arr_mem hr hbe hbm)) hcl hbc'
              (a := bx.1.pay + 24 + j) (by simp only [Blk.In, Blk.pay, Blk.fin] at this ⊢; omega)
              (by simp only [Blk.In, Blk.pay, Blk.fin] at hw hcsz ⊢; omega))
    (forall₂_append hm1 (.cons ⟨rfl, hv⟩ hm2))
    (fun g' hg' => (List.mem_cons.mp hg').elim (fun e1 => e1 ▸ hxv)
      fun hg' => h.den.hsDen g' (List.mem_cons_of_mem _ hg'))
  refine ⟨h1, pend_datIn (G := G.setReg r ((b, { e with arr := pre ++ (c, ⟨x.idx, g⟩) :: post }) :: l))
    (a := c.pay + 8) ?_ (fun o ho => ⟨fun e1 => (lo.strs o ho).1 (e1 ▸ hcb),
    fun e1 => (lo.strs o ho).2 (e1 ▸ hcb)⟩) (by simp only at hcsz; omega) w0 w1⟩
  exact DcG.arr_mem hr (be := (b, { e with arr := pre ++ (c, ⟨x.idx, g⟩) :: post }))
    (by simp [DcG.setReg]) (bn := (c, ⟨x.idx, g⟩)) (by simp)

theorem nodup_map_on {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hf, hn => by
    obtain ⟨ha, hn'⟩ := List.nodup_cons.mp hn
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_map_on (fun x hx y hy => hf x
      (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hn'⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact ha (hf b (List.mem_cons_of_mem _ hb) a List.mem_cons_self he ▸ hb)

/-- The link words of a level's array are distinct. -/
theorem links_nodup {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H) {b : Blk}
    (hb : b ∈ H.live) (hbsz : 32 ≤ b.sz) {l : List (Blk × ANode)}
    (hl : ∀ bx ∈ l, bx.1 ∈ H.live ∧ 32 ≤ bx.1.sz) (hnd : (b :: l.map (·.1)).Nodup) :
    (links 24 (b.pay + 16) l).Nodup := by
  obtain ⟨hbn, hnd'⟩ := List.nodup_cons.mp hnd
  have e : l.map (fun bx => bx.1.pay + 24) = (l.map (·.1)).map (fun d => d.pay + 24) := by
    simp [List.map_map]
  refine List.nodup_cons.mpr ⟨fun hm => ?_, ?_⟩
  · obtain ⟨bx, hbx, he⟩ := List.mem_map.mp hm
    obtain ⟨hl1, hl2⟩ := hl bx hbx
    exact live_apart hi hb hl1 (fun e1 => hbn (e1 ▸ List.mem_map.mpr ⟨bx, hbx, rfl⟩))
      (a := b.pay + 16) (by simp only [Blk.In, Blk.pay, Blk.fin] at hbsz ⊢; omega)
      (by simp only [Blk.In, Blk.pay, Blk.fin] at he hl2 ⊢; omega)
  · rw [e]
    refine nodup_map_on (fun d1 h1 d2 h2 he => Classical.byContradiction fun hne => ?_) hnd'
    obtain ⟨bx1, hb1, rfl⟩ := List.mem_map.mp h1
    obtain ⟨bx2, hb2, rfl⟩ := List.mem_map.mp h2
    obtain ⟨l1, s1⟩ := hl bx1 hb1
    obtain ⟨l2, s2⟩ := hl bx2 hb2
    exact live_apart hi l1 l2 hne (a := bx1.1.pay)
      (by simp only [Blk.In, Blk.pay, Blk.fin] at s1 ⊢; omega)
      (by simp only [Blk.In, Blk.pay, Blk.fin] at he s2 ⊢; omega)

/-- **A node inserted** into register `r`'s top array after the nodes `pre`:
the fresh node `c` holds index `i` and the handle `g` (denoting `v`), the
link word after `pre` names it. -/
theorem DcAt.insNode {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {en : Entry} {es : List Entry} {pre post : List (Blk × ANode)}
    {c : Blk} {i : Nat} {m1 m2 : List (Nat × Val)} {v : Val}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hst : st.regs r = en :: es) (harr : e.arr = pre ++ post)
    (hm1 : List.Forall₂ (ARel ⟨L, G.strs⟩) pre m1) (hm2 : List.Forall₂ (ARel ⟨L, G.strs⟩) post m2)
    (hf : DcFresh H F L G c)
    (hm : MemOnly (fun y => c.In y ∨
      (lend 24 (b.pay + 16) pre ≤ y ∧ y < lend 24 (b.pay + 16) pre + 8)) M' M)
    (hw : ldv .ld M' (lend 24 (b.pay + 16) pre) = BitVec.ofNat 64 c.pay)
    (hn : ANodeAt M' c ⟨i, g⟩)
    (h24 : ldv .ld M' (c.pay + 24) = ldv .ld M (lend 24 (b.pay + 16) pre))
    (hv : g.Den ⟨L, G.strs⟩ v) :
    DcAt S M' H F L C (G.setReg r ((b, { e with arr := pre ++ (c, ⟨i, g⟩) :: post }) :: l)) hs
      (st.setReg r ({ en with arr := m1 ++ (i, v) :: m2 } :: es)) := by
  have hi := h.heap.heap
  have lo := G.levOnly h.nodup hr hl
  have hbe : (b, e) ∈ G.regs r := by rw [hl]; exact List.mem_cons_self
  obtain ⟨hw0, hp0⟩ := h.regWord hr hl
  have hbl := h.heap.raw.live b (G.reg_mem hr hbe)
  have hbsz := hp0.sz
  have hch0 := hp0.arr
  rw [harr] at hch0
  have hmemA : ∀ bx ∈ pre ++ post, bx ∈ e.arr := fun bx hm => by rw [harr]; exact hm
  have hlv : ∀ bx ∈ pre ++ post, bx.1 ∈ H.live ∧ 32 ≤ bx.1.sz := fun bx hm =>
    ⟨h.heap.raw.live _ (G.arr_mem hr hbe (hmemA bx hm)), (hch0.forall bx hm).sz⟩
  have hbx : ∀ bx ∈ pre ++ post, bx.1 ≠ b := fun bx hm e1 =>
    (List.nodup_cons.mp lo.nodup).1 (e1 ▸ List.mem_map.mpr ⟨bx, hmemA bx hm, rfl⟩)
  have hcx : ∀ d ∈ H.live, d ≠ c → ∀ y, d.In y → ¬ c.In y := fun d hd hne y h1 h2 =>
    live_apart hi hd hf.live hne h1 h2
  have hcb : b ≠ c := fun e1 => hf.notG (e1 ▸ G.reg_mem hr hbe)
  have hcn : ∀ bx ∈ pre ++ post, bx.1 ≠ c := fun bx hm e1 =>
    hf.notG (e1 ▸ G.arr_mem hr hbe (hmemA bx hm))
  -- the link word after `pre` lies in `b` or in the last node of `pre`
  have hlend := lend_mem 24 (b.pay + 16) pre
  have hwrd : ∀ y, lend 24 (b.pay + 16) pre ≤ y → y < lend 24 (b.pay + 16) pre + 8 →
      (b.In y ∧ b.pay + 16 ≤ y) ∨ ∃ bx ∈ pre, bx.1.In y ∧ bx.1.pay + 24 ≤ y := fun y h1 h2 => by
    rcases List.mem_cons.mp hlend with he | he
    · exact .inl ⟨by simp only [Blk.In, Blk.pay, Blk.fin] at he h1 h2 hbsz ⊢; omega, by omega⟩
    · obtain ⟨bx, hm, he⟩ := List.mem_map.mp he
      have := (hlv bx (List.mem_append_left _ hm)).2
      exact .inr ⟨bx, hm, by simp only [Blk.In, Blk.pay, Blk.fin] at he h1 h2 this ⊢; omega, by omega⟩
  have hnd := links_nodup hi hbl hbsz hlv (by
    have := lo.nodup; simpa [RLev.blocks, harr] using this)
  have hal : ∀ d ∈ G.blocks, 32 ≤ d.sz → d.pay % 16 = 0 := fun d hd hsz =>
    (h.node_bounds hd hsz).2.2
  have hm' : ∀ bx ∈ pre ++ post, ∀ y, bx.1.pay ≤ y → y < bx.1.pay + 24 → imgM M' y = imgM M y :=
    fun bx hmb y h1 h2 => by
      obtain ⟨hl1, hl2⟩ := hlv bx hmb
      have hin : bx.1.In y := by simp only [Blk.In, Blk.pay, Blk.fin] at h1 h2 hl2 ⊢; omega
      refine hm y fun hc => hc.elim (hcx bx.1 hl1 (hcn bx hmb) y hin) fun ⟨w1, w2⟩ => ?_
      rcases hwrd y w1 w2 with ⟨hb1, -⟩ | ⟨bx', hbx', hb1, hb2⟩
      · exact live_apart hi hbl hl1 (Ne.symm (hbx bx hmb)) hb1 hin
      · by_cases he : bx'.1 = bx.1
        · rw [he] at hb2; omega
        · exact live_apart hi (hlv bx' (List.mem_append_left _ hbx')).1 hl1 he hb1 hin
  have hlk : ∀ a' ∈ links 24 (b.pay + 16) (pre ++ post), a' % 8 = 0 ∧ ∀ j, j < 8 → ¬ c.In (a' + j) :=
    fun a' ha' => by
      rcases List.mem_cons.mp ha' with rfl | ha'
      · have := hal b (G.reg_mem hr hbe) hbsz
        exact ⟨by omega, fun j hj => hcx b hbl hcb _
          (by simp only [Blk.In, Blk.pay, Blk.fin] at hbsz ⊢; omega)⟩
      · obtain ⟨bx, hm, rfl⟩ := List.mem_map.mp ha'
        obtain ⟨hl1, hl2⟩ := hlv bx hm
        have := hal bx.1 (G.arr_mem hr hbe (hmemA bx hm)) hl2
        exact ⟨by omega, fun j hj => hcx bx.1 hl1 (hcn bx hm) _
          (by simp only [Blk.In, Blk.pay, Blk.fin] at hl2 ⊢; omega)⟩
  have hlend8 : lend 24 (b.pay + 16) pre % 8 = 0 := (hlk _ (by
    rcases List.mem_cons.mp hlend with he | he
    · rw [he]; exact List.mem_cons_self
    · obtain ⟨bx, hm, he⟩ := List.mem_map.mp he
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨bx, List.mem_append_left _ hm, he⟩))).1
  refine h.setArr (N := [c]) (hs := hs) (arr' := pre ++ (c, ⟨i, g⟩) :: post)
    (am := m1 ++ (i, v) :: m2) hr hl hst (fun d hd => by rw [List.mem_singleton.mp hd]; exact hf)
    (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
    (by rw [harr]; simp only [List.map_append, List.map_cons, List.singleton_append]; exact List.perm_middle)
    (fun y => by
      rw [harr]
      simp only [List.map_append, List.map_cons, List.count_append, List.count_cons]
      omega)
    (fun y hy => hm y fun hc => hy (by
      rcases hc with hc | ⟨h1, h2⟩
      · exact .inl ⟨c, List.mem_cons_self, hc⟩
      · rcases hwrd y h1 h2 with ⟨hb1, hb2⟩ | ⟨bx, hbx, hb1, -⟩
        · exact .inr ⟨by omega, by
            rcases List.mem_cons.mp hlend with he | he
            · omega
            · obtain ⟨bx, hm, he⟩ := List.mem_map.mp he
              exfalso
              have := (hlv bx (List.mem_append_left _ hm)).1
              exact live_apart hi hbl this (Ne.symm (hbx bx (List.mem_append_left _ hm))) hb1
                (by simp only [Blk.In, Blk.pay, Blk.fin] at he h1 h2 ⊢
                    have := (hlv bx (List.mem_append_left _ hm)).2; omega)⟩
        · have hmA : bx.1 ∈ e.arr.map (·.1) := by
            rw [harr]; exact List.mem_map.mpr ⟨bx, List.mem_append_left _ hbx, rfl⟩
          exact .inl ⟨bx.1, List.mem_cons_of_mem _ hmA, hb1⟩))
    (hch0.insert hnd
      (fun bx hm hq => hq.congr24 fun y h1 h2 => hm' bx hm y h1 h2)
      (fun a' ha' hne => ldv_congr .ld fun j hj => hm _ fun hc => by
        simp only [widthOfM] at hj
        obtain ⟨ha8, hac⟩ := hlk a' ha'
        rcases hc with hc | ⟨w1, w2⟩
        · exact hac j hj hc
        · omega) hw hn h24)
    (forall₂_append hm1 (.cons ⟨rfl, hv⟩ hm2))
    (fun g' hg' => h.den.hsDen g' (List.mem_cons_of_mem _ hg'))

/-! ## The model -/

theorem arrSet_hit {i : Nat} {v w : Val} :
    ∀ {m1 m2 : List (Nat × Val)}, (∀ jw ∈ m1, jw.1 < i) →
      arrSet i v (m1 ++ (i, w) :: m2) = m1 ++ (i, v) :: m2
  | [], m2, _ => by simp [arrSet]
  | (j, w') :: m1, m2, h => by
    have hj : j < i := h _ List.mem_cons_self
    simp only [List.cons_append, arrSet, hj, ↓reduceIte]
    rw [arrSet_hit fun jw hm => h jw (List.mem_cons_of_mem _ hm)]

theorem arrSet_ins {i : Nat} {v : Val} :
    ∀ {m1 m2 : List (Nat × Val)}, (∀ jw ∈ m1, jw.1 < i) → (∀ jw ∈ m2.head?, i < jw.1) →
      arrSet i v (m1 ++ m2) = m1 ++ (i, v) :: m2
  | [], [], _, _ => rfl
  | [], (j, w) :: m2, _, h2 => by
    have hj : i < j := h2 _ rfl
    simp only [List.nil_append, arrSet, show ¬ j < i by omega, show (j == i) = false by
      simp only [beq_eq_false_iff_ne]; omega, ↓reduceIte, Bool.false_eq_true]
  | (j, w') :: m1, m2, h, h2 => by
    have hj : j < i := h _ List.mem_cons_self
    simp only [List.cons_append, arrSet, hj, ↓reduceIte]
    rw [arrSet_ins (fun jw hm => h jw (List.mem_cons_of_mem _ hm)) h2]

/-- Indices below `i` on the ghost side are below `i` on the model side. -/
theorem forall₂_idx_lt {O : DObjs} {i : Nat} :
    ∀ {l : List (Blk × ANode)} {m : List (Nat × Val)}, List.Forall₂ (ARel O) l m →
      (∀ bx ∈ l, bx.2.idx < i) → ∀ jw ∈ m, jw.1 < i
  | [], [], .nil, _, _, h => absurd h List.not_mem_nil
  | _ :: _, _ :: _, .cons hr t, hl, jw, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [← hr.1]; exact hl _ List.mem_cons_self
    · exact forall₂_idx_lt t (fun bx h => hl bx (List.mem_cons_of_mem _ h)) jw hm

theorem St.setReg_setReg (st : St) (r : Nat) (l1 l2 : List Entry) :
    (st.setReg r l1).setReg r l2 = st.setReg r l2 := by
  simp only [St.setReg]; congr 1; funext q; split <;> rfl

theorem DcG.setReg_setReg (G : DcG) (r : Nat) (l1 l2 : List (Blk × RLev)) :
    (G.setReg r l1).setReg r l2 = G.setReg r l2 := by
  simp only [DcG.setReg]; congr 1; funext q; split <;> rfl

/-- A block stays fresh to the state through another `dc_malloc`. -/
theorem DcFresh.afterMalloc {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F : List Blk}
    {L : List NumObj} {G : DcG} {b c : Blk} {n sp : Nat} (h : DcFresh H F L G c)
    (hp : DcMallocPost S M M' H H' n sp b) : DcFresh H' F L G c :=
  ⟨by rw [hp.live]; exact List.mem_cons_of_mem _ h.live, h.notG, h.notNum⟩

/-! ## The machine -/

/-- `dc_array_set`'s datum stores and return (`0x80003d44`, `sp` lowered by
64, `s0` the node at `a`). -/
theorem as_tail {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp a : Nat}
    {w0 w1 ra s0 s1 s2 : BitVec 64} (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp)
    (ha : heapStart ≤ a ∧ a + 32 ≤ heapEnd ∧ a % 8 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64)) (h8 : R 8 = BitVec.ofNat 64 a)
    (l16 : ldv .ld M (sp - 64 + 16) = w0) (l24 : ldv .ld M (sp - 64 + 24) = w1)
    (l56 : ldv .ld M (sp - 64 + 56) = ra) (l48 : ldv .ld M (sp - 64 + 48) = s0)
    (l40 : ldv .ld M (sp - 64 + 40) = s1) (l32 : ldv .ld M (sp - 64 + 32) = s2)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 8, 9, 14, 15, 18] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 9 = s1 → R' 18 = s2 → DW live S Q ra R' (datW M (a + 8) w0 w1)) :
    DW live S Q 0x80003d44#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  obtain ⟨ha1, ha2, ha3⟩ := ha
  simp only [heapEnd, heapStart] at hab ha1 ha2
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h2, h8, l16, l24, l56, l48, l40, l32]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first | (bsimp []; exact hal) | skip
  have e : datW M (a + 8) w0 w1 = writeLog (writeLog M [(a + 8, 8, w0)]) [(a + 16, 8, w1)] := by
    simp only [datW]
  have m48 : ldv .ld (writeLog (writeLog M [(a + 8, 8, w0)]) [(a + 16, 8, w1)]) (sp - 64 + 48) = s0 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), l48]
  have m40 : ldv .ld (writeLog (writeLog M [(a + 8, 8, w0)]) [(a + 16, 8, w1)]) (sp - 64 + 40) = s1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), l40]
  have m32 : ldv .ld (writeLog (writeLog M [(a + 8, 8, w0)]) [(a + 16, 8, w1)]) (sp - 64 + 32) = s2 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), l32]
  rw [m48, m40, m32]
  have hk' := hk; rw [e] at hk'
  refine hk' _ ?_ ?_ ?_ ?_ ?_ ?_
  · keeps_tac Keeps.refl _ _
  · bsimp []
  · bsimp [h2]; congr 1; omega
  · bsimp []
  · bsimp []
  · bsimp []

theorem asFrame_out {sp a : Nat} (hab : heapEnd + 112 ≤ sp) (ha : frameIn sp 112 a) :
    OutHeap a ∧ ¬ DcGlob a := by
  simp only [frameIn] at ha
  exact ⟨outHeap_of_ge (by simp only [heapEnd] at *; omega), fun hg => by
    have := hg.lt; simp only [heapStart, heapEnd] at *; omega⟩

/-- The registers the replacing path of `dc_array_set` may change. -/
abbrev foundClob : List Nat := [1, 2, 8, 9, 18, 10, 13, 14, 15]

/-- `dc_array_set` on an existing index holding a number (`0x80003d20`, `sp`
lowered by 64, `s0` the node `c`): `dc_free_num` of the old value through the
node's pointer word, then the new datum and the return. -/
theorem as_found_num {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {en : Entry} {es : List Entry} {pre post : List (Blk × ANode)}
    {c : Blk} {x : ANode} {m1 m2 : List (Nat × Val)} {v : Val} {w0 w1 ra s0 s1 s2 : BitVec 64}
    {p sp : Nat}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hst : st.regs r = en :: es) (harr : e.arr = pre ++ (c, x) :: post)
    (hm1 : List.Forall₂ (ARel ⟨L, G.strs⟩) pre m1) (hm2 : List.Forall₂ (ARel ⟨L, G.strs⟩) post m2)
    (hxv : x.v = .num p) (hxw : ∃ w, x.v.Den ⟨L, G.strs⟩ w) (hd : DatRegs w0 w1 g)
    (hv : g.Den ⟨L, G.strs⟩ v) (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64)) (h8 : R 8 = BitVec.ofNat 64 c.pay)
    (l16 : ldv .ld M (sp - 64 + 16) = w0) (l24 : ldv .ld M (sp - 64 + 24) = w1)
    (l56 : ldv .ld M (sp - 64 + 56) = ra) (l48 : ldv .ld M (sp - 64 + 48) = s0)
    (l40 : ldv .ld M (sp - 64 + 40) = s1) (l32 : ldv .ld M (sp - 64 + 32) = s2)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps foundClob R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = s0 → R' 9 = s1 → R' 18 = s2 →
      DcAt S M' H' F' L' C' G' hs (st.setReg r ({ en with arr := m1 ++ (x.idx, v) :: m2 } :: es)) →
      StkOut sp 112 M' M → DW live S Q ra R' M') :
    DW live S Q 0x80003d20#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hbe : (b, e) ∈ G.regs r := by rw [hl]; exact List.mem_cons_self
  have hcA : (c, x) ∈ e.arr := by rw [harr]; exact List.mem_append_right _ List.mem_cons_self
  have hcG : c ∈ G.blocks := G.arr_mem hr hbe hcA
  obtain ⟨-, hp0⟩ := h.regWord hr hl
  have hnc : ANodeAt M c x := hp0.arr.forall (c, x) hcA
  have hsz := hnc.sz
  obtain ⟨hb1, hb2, hb3⟩ := h.node_bounds hcG hsz
  have htag : ldv .lw M (c.pay + 8) = BitVec.ofNat 64 1 := by
    have := hnc.dat.lw; rw [hxv] at this; exact this
  have hptr : ldv .ld M (c.pay + 16) = BitVec.ofNat 64 p := by
    have := hnc.dat.ptr; rw [hxv] at this; exact this
  obtain ⟨h1, hpd⟩ := h.setNode hr hl hst harr hm1 hm2 hd hv hxw
  rw [hxv] at h1
  simp only [heapEnd, heapStart] at hab hb1 hb2
  bc_run hlive hS [h2, h8, htag] at 0x80002ba0
  bc_run hlive hS [h2, h8] at 0x80002ba0
  refine dc_free_num_specP hlive hpd h1 (q := c.pay + 16)
    ⟨fun i _ => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
      by omega, by omega⟩
    (.win fun y hy => by simp only [datWin, slotBytes] at hy ⊢; omega) hptr
    (StackFrame.shrink (StackFrame.sub (m := 64) (n := 48) hsf (by decide)) (by decide))
    (by simp only [heapEnd]; omega) (Or.inl (by omega)) _ (by bsimp [h8]) (by bsimp [h2]) (by bsimp [])
    fun R1 M3 H' F' L' C' hk1 h3 _ hfr _ _ => ?_
  have hfs : ∀ k, k + 8 ≤ 64 → ldv .ld M3 (sp - 64 + k) = ldv .ld M (sp - 64 + k) :=
    fun k hk => ldv_congr .ld fun j hj => by
      have hin : frameIn sp 112 (sp - 64 + k + j) := by simp only [frameIn, widthOfM] at hj ⊢; omega
      have ho := asFrame_out (by simp only [heapEnd]; omega) hin
      exact hfr _ ho.1 ho.2 (by simp only [frameIn, widthOfM] at hj ⊢; omega)
        (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk1.get 2]; bsimp [h2]
  have q8 : R1 8 = BitVec.ofNat 64 c.pay := by rw [hk1.get 8]; bsimp [h8]
  show DW live S Q 0x80003da0#64 R1 M3
  bc_run hlive hS [] at 0x80003d44
  refine as_tail hlive hS hsf (by simp only [heapEnd]; omega)
    ⟨by simp only [heapStart]; omega, by simp only [heapEnd]; omega, by omega⟩ R1 q2 q8
    ((hfs 16 (by omega)).trans l16) ((hfs 24 (by omega)).trans l24) ((hfs 56 (by omega)).trans l56)
    ((hfs 48 (by omega)).trans l48) ((hfs 40 (by omega)).trans l40) ((hfs 32 (by omega)).trans l32)
    hal fun R' hk2 e1 e2 e8 e9 e18 => ?_
  refine hk R' _ H' F' L' C' _ ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
    (by keeps_tac Keeps.refl _ _)))) e1 e2 e8 e9 e18 h3 fun y ho hg hf => ?_
  have hnw : y < c.pay + 8 ∨ c.pay + 24 ≤ y := by
    have := ho.1; simp only [heapStart, heapEnd] at this; omega
  simp only [datW]
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    hfr y ho hg (by simp only [frameIn] at hf ⊢; omega) (by simp only [slotBytes]; omega)]

/-- `dc_array_set` on an existing index holding a string (`0x80003d20`, `sp`
lowered by 64, `s0` the node `c`): `dc_free_str` of the old value through the
node's pointer word, then the new datum and the return. -/
theorem as_found_str {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {en : Entry} {es : List Entry} {pre post : List (Blk × ANode)}
    {c : Blk} {x : ANode} {m1 m2 : List (Nat × Val)} {v : Val} {w0 w1 ra s0 s1 s2 : BitVec 64}
    {p sp : Nat}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hst : st.regs r = en :: es) (harr : e.arr = pre ++ (c, x) :: post)
    (hm1 : List.Forall₂ (ARel ⟨L, G.strs⟩) pre m1) (hm2 : List.Forall₂ (ARel ⟨L, G.strs⟩) post m2)
    (hxv : x.v = .str p) (hxw : ∃ w, x.v.Den ⟨L, G.strs⟩ w) (hd : DatRegs w0 w1 g)
    (hv : g.Den ⟨L, G.strs⟩ v) (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64)) (h8 : R 8 = BitVec.ofNat 64 c.pay)
    (l16 : ldv .ld M (sp - 64 + 16) = w0) (l24 : ldv .ld M (sp - 64 + 24) = w1)
    (l56 : ldv .ld M (sp - 64 + 56) = ra) (l48 : ldv .ld M (sp - 64 + 48) = s0)
    (l40 : ldv .ld M (sp - 64 + 40) = s1) (l32 : ldv .ld M (sp - 64 + 32) = s2)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps foundClob R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = s0 → R' 9 = s1 → R' 18 = s2 →
      DcAt S M' H' F' L' C' G' hs (st.setReg r ({ en with arr := m1 ++ (x.idx, v) :: m2 } :: es)) →
      StkOut sp 112 M' M → DW live S Q ra R' M') :
    DW live S Q 0x80003d20#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hbe : (b, e) ∈ G.regs r := by rw [hl]; exact List.mem_cons_self
  have hcA : (c, x) ∈ e.arr := by rw [harr]; exact List.mem_append_right _ List.mem_cons_self
  have hcG : c ∈ G.blocks := G.arr_mem hr hbe hcA
  obtain ⟨-, hp0⟩ := h.regWord hr hl
  have hnc : ANodeAt M c x := hp0.arr.forall (c, x) hcA
  have hsz := hnc.sz
  obtain ⟨hb1, hb2, hb3⟩ := h.node_bounds hcG hsz
  have htag : ldv .lw M (c.pay + 8) = BitVec.ofNat 64 2 := by
    have := hnc.dat.lw; rw [hxv] at this; exact this
  have hptr : ldv .ld M (c.pay + 16) = BitVec.ofNat 64 p := by
    have := hnc.dat.ptr; rw [hxv] at this; exact this
  obtain ⟨h1, hpd⟩ := h.setNode hr hl hst harr hm1 hm2 hd hv hxw
  rw [hxv] at h1
  simp only [heapEnd, heapStart] at hab hb1 hb2
  bc_run hlive hS [h2, h8, htag] at 0x80002ba0
  bc_run hlive hS [h2, h8] at 0x800039a4
  refine dc_free_str_specP hlive hpd h1 (q := c.pay + 16)
    ⟨fun i _ => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
      by omega, by omega⟩
    hptr
    (StackFrame.shrink (StackFrame.sub (m := 64) (n := 48) hsf (by decide)) (by decide))
    (by simp only [heapEnd]; omega) _ (by bsimp [h8]) (by bsimp [h2]) (by bsimp [])
    fun R1 M3 H' G' hk1 _ h3 hfr _ _ => ?_
  have hfs : ∀ k, k + 8 ≤ 64 → ldv .ld M3 (sp - 64 + k) = ldv .ld M (sp - 64 + k) :=
    fun k hk => ldv_congr .ld fun j hj => by
      have hin : frameIn sp 112 (sp - 64 + k + j) := by simp only [frameIn, widthOfM] at hj ⊢; omega
      have ho := asFrame_out (by simp only [heapEnd]; omega) hin
      exact hfr _ ho.1 ho.2 (by simp only [frameIn, widthOfM] at hj ⊢; omega)
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk1.get 2]; bsimp [h2]
  have q8 : R1 8 = BitVec.ofNat 64 c.pay := by rw [hk1.get 8]; bsimp [h8]
  show DW live S Q 0x80003d74#64 R1 M3
  bc_run hlive hS [] at 0x80003d44
  refine as_tail hlive hS hsf (by simp only [heapEnd]; omega)
    ⟨by simp only [heapStart]; omega, by simp only [heapEnd]; omega, by omega⟩ R1 q2 q8
    ((hfs 16 (by omega)).trans l16) ((hfs 24 (by omega)).trans l24) ((hfs 56 (by omega)).trans l56)
    ((hfs 48 (by omega)).trans l48) ((hfs 40 (by omega)).trans l40) ((hfs 32 (by omega)).trans l32)
    hal fun R' hk2 e1 e2 e8 e9 e18 => ?_
  refine hk R' _ H' F L C G' ((hk2.mono (by decide)).trans (by keeps_tac ((hk1.mono (by decide)).trans
    (by keeps_tac Keeps.refl _ _)))) e1 e2 e8 e9 e18 h3 fun y ho hg hf => ?_
  have hnw : y < c.pay + 8 ∨ c.pay + 24 ≤ y := by
    have := ho.1; simp only [heapStart, heapEnd] at this; omega
  simp only [datW]
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    hfr y ho hg (by simp only [frameIn] at hf ⊢; omega)]

/-- A fresh array node's stores: index, link, datum. -/
abbrev nodeW (M : Mem) (a i : Nat) (nx w0 w1 : BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog M [(a, 4, BitVec.ofNat 64 i)]) [(a + 24, 8, nx)])
    [(a + 8, 8, w0)]) [(a + 16, 8, w1)]

/-- `dc_array_set`'s stores into the fresh node `a` on the insert path
(`0x80003cdc`, `sp` lowered by 64, `s0` the next node word `nx`). -/
theorem as_nstore {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp a i : Nat}
    {w0 w1 pv nx : BitVec 64} (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp)
    (ha : heapStart ≤ a ∧ a + 32 ≤ heapEnd ∧ a % 8 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64)) (h10 : R 10 = BitVec.ofNat 64 a)
    (h9 : R 9 = BitVec.ofNat 64 i) (h8 : R 8 = nx)
    (l16 : ldv .ld M (sp - 64 + 16) = w0) (l24 : ldv .ld M (sp - 64 + 24) = w1)
    (l8 : ldv .ld M (sp - 64 + 8) = pv)
    (hk : ∀ R', Keeps [13, 14, 15] R' R → R' 14 = pv →
      DW live S Q 0x80003cf8#64 R' (nodeW M a i nx w0 w1)) :
    DW live S Q 0x80003cdc#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  obtain ⟨ha1, ha2, ha3⟩ := ha
  simp only [heapEnd, heapStart] at hab ha1 ha2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have haw : (BitVec.ofNat 64 a).toNat = a := by simp only [BitVec.toNat_ofNat]; omega
  have haS : ∀ k, k + 8 ≤ 32 → ∀ b ∈ accAddrs (a + k) 8, S b := fun k hk b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have haS4 : ∀ b ∈ accAddrs a 4, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  bc_run hlive hS [h2, h10, h9, h8, haw, l16, l24, l8] at 0x80003cf8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact haS4 | exact haS 8 (by omega) | exact haS 16 (by omega) | exact haS 24 (by omega) | (simp only [StOK, htx]; omega) | skip
  refine hk _ ?_ ?_
  · keeps_tac Keeps.refl _ _
  · bsimp []

/-- The same stores on the empty path (`0x80003dac`, link `0`), on to the
tail at `0x80003d7c`. -/
theorem as_nstore0 {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp a i : Nat}
    {w0 w1 : BitVec 64} (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp)
    (ha : heapStart ≤ a ∧ a + 32 ≤ heapEnd ∧ a % 8 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64)) (h10 : R 10 = BitVec.ofNat 64 a)
    (h9 : R 9 = BitVec.ofNat 64 i)
    (l16 : ldv .ld M (sp - 64 + 16) = w0) (l24 : ldv .ld M (sp - 64 + 24) = w1)
    (hk : ∀ R', Keeps [14, 15] R' R → DW live S Q 0x80003d7c#64 R' (nodeW M a i 0#64 w0 w1)) :
    DW live S Q 0x80003dac#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  obtain ⟨ha1, ha2, ha3⟩ := ha
  simp only [heapEnd, heapStart] at hab ha1 ha2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have haw : (BitVec.ofNat 64 a).toNat = a := by simp only [BitVec.toNat_ofNat]; omega
  have haS : ∀ k, k + 8 ≤ 32 → ∀ b ∈ accAddrs (a + k) 8, S b := fun k hk b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have haS4 : ∀ b ∈ accAddrs a 4, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  bc_run hlive hS [h2, h10, h9, haw, l16, l24] at 0x80003d7c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact haS4 | exact haS 8 (by omega) | exact haS 16 (by omega) | exact haS 24 (by omega) | (simp only [StOK, htx]; omega) | skip
  refine hk _ ?_
  · keeps_tac Keeps.refl _ _

/-- `dc_array_set` linking the fresh node after the node at `q` and
returning (`0x80003cf8`, `a4 = q`, `a0` the fresh node). -/
theorem as_link {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp q : Nat}
    {ra s0 s1 s2 : BitVec 64} (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp)
    (hq : heapStart ≤ q ∧ q + 32 ≤ heapEnd ∧ q % 8 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64)) (h14 : R 14 = BitVec.ofNat 64 q)
    (l56 : ldv .ld M (sp - 64 + 56) = ra) (l48 : ldv .ld M (sp - 64 + 48) = s0)
    (l40 : ldv .ld M (sp - 64 + 40) = s1) (l32 : ldv .ld M (sp - 64 + 32) = s2)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 8, 9, 18] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 9 = s1 → R' 18 = s2 → DW live S Q ra R' (writeLog M [(q + 24, 8, R 10)])) :
    DW live S Q 0x80003cf8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  obtain ⟨hq1, hq2, hq3⟩ := hq
  simp only [heapEnd, heapStart] at hab hq1 hq2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hqw : (BitVec.ofNat 64 q).toNat = q := by simp only [BitVec.toNat_ofNat]; omega
  have hnz : BitVec.ofNat 64 q ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
  have hqS : ∀ b ∈ accAddrs (q + 24) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  bc_run hlive hS [h2, h14, hqw, l56, l48]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hqS | (simp only [StOK, htx]; omega) | skip
  all_goals try (intro hc; exact (hnz hc).elim)
  intro _
  bc_run hlive hS [h2, h14, hqw, l56, l48]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hqS | (simp only [StOK, htx]; omega) | skip
  all_goals first | (bsimp []; exact hal) | skip
  have m40 : ldv .ld (writeLog M [(q + 24, 8, R 10)]) (sp - 64 + 40) = s1 := by
    rw [ldv_ld_miss _ _ (by omega), l40]
  have m32 : ldv .ld (writeLog M [(q + 24, 8, R 10)]) (sp - 64 + 32) = s2 := by
    rw [ldv_ld_miss _ _ (by omega), l32]
  rw [m40, m32]
  refine hk _ ?_ ?_ ?_ ?_ ?_ ?_
  · keeps_tac Keeps.refl _ _
  · bsimp []
  · bsimp [h2]; congr 1; omega
  · bsimp []
  · bsimp []
  · bsimp []

/-- `dc_array_set`'s tail call `dc_set_stacked_array (s2, a0)`
(`0x80003d7c`, `sp` lowered by 64). -/
theorem as_ss {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp : Nat}
    {ra s1 s2 : BitVec 64} (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64))
    (l56 : ldv .ld M (sp - 64 + 56) = ra) (l40 : ldv .ld M (sp - 64 + 40) = s1)
    (l32 : ldv .ld M (sp - 64 + 32) = s2)
    (hk : ∀ R', Keeps [1, 2, 9, 10, 11, 18] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 9 = s1 → R' 18 = s2 → R' 10 = R 18 → R' 11 = R 10 → DW live S Q 0x8000391c#64 R' M) :
    DW live S Q 0x80003d7c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h2, l56, l40, l32] at 0x8000391c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine hk _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · keeps_tac Keeps.refl _ _
  · bsimp []
  · bsimp [h2]; congr 1; omega
  · bsimp []
  · bsimp []
  · bsimp []
  · bsimp []

/-- The insert path's branch with no node before (`0x80003cf8`, `a4 = 0`):
`s0` restored, then the tail call. -/
theorem as_ss0 {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp : Nat}
    {ra s0 s1 s2 : BitVec 64} (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64)) (h14 : R 14 = 0#64)
    (l56 : ldv .ld M (sp - 64 + 56) = ra) (l48 : ldv .ld M (sp - 64 + 48) = s0)
    (l40 : ldv .ld M (sp - 64 + 40) = s1) (l32 : ldv .ld M (sp - 64 + 32) = s2)
    (hk : ∀ R', Keeps [1, 2, 8, 9, 10, 11, 18] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 9 = s1 → R' 18 = s2 → R' 10 = R 18 → R' 11 = R 10 →
      DW live S Q 0x8000391c#64 R' M) :
    DW live S Q 0x80003cf8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h2, h14, l48] at 0x80003d7c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals try (intro hc; exact (hc rfl).elim)
  all_goals try intro _
  bc_run hlive hS [h2, l48] at 0x80003d7c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine as_ss hlive hS hsf (by simp only [heapEnd]; omega) _ (by bsimp [h2]) l56 l40 l32
    fun R' hk1 e1 e2 e9 e18 e10 e11 => hk R' ?_ e1 e2 ?_ e9 e18 ?_ ?_
  · keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
  · rw [hk1.get 8]; bsimp []
  · rw [e10]; bsimp []
  · rw [e11]; bsimp []

/-- `dc_set_stacked_array (r, a1)` at `0x8000391c` with a level at `p`: the
array head word set. -/
theorem ss_lev {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) (hG : ∀ a, DcGlob a → S a) {M : Mem}
    {r p : Nat} (hr : r < 256) (hw : ldv .ld M (regAddr r) = BitVec.ofNat 64 p)
    (hp : heapStart ≤ p ∧ p + 32 ≤ heapEnd ∧ p % 8 = 0)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 r) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [10, 15] R' R → DW live S Q (R 1) R' (writeLog M [(p + 16, 8, R 11)])) :
    DW live S Q 0x8000391c#64 R M := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  simp only [heapEnd, heapStart] at hp1 hp2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  have hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs, regAddr] at this ⊢; omega)
  have hpw : (BitVec.ofNat 64 p).toNat = p := by simp only [BitVec.toNat_ofNat]; omega
  have hnz : BitVec.ofNat 64 p ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
  have hpS : ∀ b ∈ accAddrs (p + 16) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  bc_run hlive hS [h10, regWord_addr hr, hra8, hw, hpw]
  all_goals first | exact hrown | exact hpS | (simp only [LdOK, StOK, regAddr, dcRegAddr, htx]; omega) | skip
  all_goals try (intro hc; exact (hnz hc).elim)
  all_goals try intro _
  bc_run hlive hS [hpw]
  all_goals first | exact hpS | (simp only [StOK, htx]; omega) | exact hal | skip
  refine hk _ ?_
  · keeps_tac Keeps.refl _ _

/-- The new level's stores in `dc_set_stacked_array`. -/
abbrev levW (M : Mem) (b : Blk) (r : Nat) (w : BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog M [(b.pay, 4, 0#64)]) [(b.pay + 24, 8, 0#64)])
    [(regAddr r, 8, BitVec.ofNat 64 b.pay)]) [(b.pay + 16, 8, w)]

/-- `dc_set_stacked_array (r, a1)` at `0x8000391c` on a register with no
level: a fresh level holding the array head `a1`, or `dc_memfail`. -/
theorem ss_new {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} (hi : HeapInv S M H)
    (hG : ∀ a, DcGlob a → S a) {sp r : Nat} (hr : r < 256) (hw : ldv .ld M (regAddr r) = 0#64)
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 r) (h2 : R 2 = BitVec.ofNat 64 sp)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Ms M1 H' b, Keeps (1 :: 2 :: 11 :: mallocClob) R' R → R' 2 = BitVec.ofNat 64 sp →
      MemOnly (frameIn sp 48) Ms M → DcMallocPost S Ms M1 H H' 32 (sp - 32) b →
      DW live S Q (R 1) R' (levW M1 b r (R 11)))
    (hoom : ∀ R' M', (∀ a, ¬ AllocByte H a → ¬ frameIn sp 48 a → imgM M' a = imgM M a) →
      DW live S Q 0x80001e74#64 R' M') :
    DW live S Q 0x8000391c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  have hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs, regAddr] at this ⊢; omega)
  bc_run hlive hS [h10, h2, regWord_addr hr, hra8, hw]
  all_goals first | exact hrown | (simp only [LdOK, StOK, regAddr, dcRegAddr, htx]; omega) | skip
  all_goals try (intro hc; exact (hc rfl).elim)
  all_goals try intro _
  bc_run hlive hS [h2, hra8] at 0x80001ea0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  generalize hMs : writeLog (writeLog (writeLog M [(sp - 32 + 24, 8, R 1)]) [(sp - 32 + 8, 8, R 11)])
    [(sp - 32, 8, BitVec.ofNat 64 (regAddr r))] = Ms
  have hM2 : MemOnly (frameIn sp 48) Ms M := fun x hx => by
    rw [← hMs]; simp only [frameIn] at hx; repeat rw [imgM_store_miss _ _ (by omega)]
  have hi2 : HeapInv S Ms H := hi.transport fun a ha => hM2 a fun hf => by
    rcases AllocByte.glob_or_heap hi ha with h1 | h1 <;>
      simp only [frameIn, freeListAddr, heapStart, heapEnd] at hf h1 <;> omega
  refine dc_malloc_spec hlive hi2 (n := 32) (by decide)
    (StackFrame.sub (m := 32) (n := 16) hsf (by decide))
    (by simp only [heapEnd]; omega) _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    (fun R1 M1 H' b hk1 hp e10 => ?_) fun R1 M1 _ hfr => hoom R1 M1 fun x hx hf => ?_
  rotate_left
  · rw [hfr x hx (by simp only [frameIn] at hf ⊢; omega)]
    exact hM2 x hf
  have hbb := blk_bounds hp.inv (by rw [hp.live]; exact List.mem_cons_self)
  have hsz := hp.size
  simp only [heapStart, heapEnd] at hbb
  obtain ⟨hb1, hb2, hb3⟩ := hbb
  have hfm : ∀ k, k + 8 ≤ 32 → ldv .ld M1 (sp - 32 + k) = ldv .ld Ms (sp - 32 + k) :=
    fun k hk => ldv_congr .ld fun j hj => hp.frame _
      (OutHeap.not_alloc hi2 (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega)))
      (by simp only [frameIn, widthOfM] at hj ⊢; omega)
  have l0 : ldv .ld M1 (sp - 32) = BitVec.ofNat 64 (regAddr r) := by
    have := hfm 0 (by omega); simp only [Nat.add_zero] at this
    rw [this, ← hMs]; exact ldv_store_hit _ _ _
  have l8 : ldv .ld M1 (sp - 32 + 8) = R 11 := by
    rw [hfm 8 (by omega), ← hMs, ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have l24 : ldv .ld M1 (sp - 32 + 24) = R 1 := by
    rw [hfm 24 (by omega), ← hMs, ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_store_hit]
  have hbw : (BitVec.ofNat 64 b.pay).toNat = b.pay := by simp only [BitVec.toNat_ofNat]; omega
  have hbS : ∀ k, k + 8 ≤ 32 → ∀ x ∈ accAddrs (b.pay + k) 8, S x := fun k hk x hx => by
    have := of_mem_accAddrs hx
    exact hS x (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hbS4 : ∀ x ∈ accAddrs b.pay 4, S x := fun x hx => by
    have := of_mem_accAddrs hx
    exact hS x (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by rw [hk1.get 2]; bsimp [h2]
  show DW live S Q 0x80003958#64 R1 M1
  bc_run hlive hS [q2, e10, l0, l8, l24, hbw, hra8]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | exact hbS4 | exact hbS 16 (by omega) | exact hbS 24 (by omega) | (simp only [StOK, LdOK, regAddr, dcRegAddr, htx]; omega) | exact hal | skip
  refine hk _ Ms M1 H' b ?_ ?_ hM2 hp
  · keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
  · bsimp [q2]; congr 1; omega

/-! ## Inserting: the state -/

/-- The link word after `pre` names the first node of `post`. -/
theorem LChain.lend_word {Mt : Mem} {P : Blk → ANode → Prop} {post : List (Blk × ANode)} :
    ∀ {a : Nat} {pre : List (Blk × ANode)}, LChain Mt 24 P a (pre ++ post) →
      ldv .ld Mt (lend 24 a pre) = headPtr post
  | a, [], h => by
    cases post with
    | nil => cases h with | nil h0 => exact h0
    | cons bx post => cases h with | cons h0 _ _ => exact h0
  | a, bx :: pre, h => by
    cases h with
    | cons _ _ hl => exact LChain.lend_word (pre := pre) hl

/-- The link word after `pre` in register `r`'s top array: an aligned heap
word outside any fresh block. -/
theorem DcAt.lendOut {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {pre post : List (Blk × ANode)} {c : Blk}
    (h : DcAt S M H F L C G hs st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (harr : e.arr = pre ++ post) (hf : DcFresh H F L G c) :
    heapStart ≤ lend 24 (b.pay + 16) pre ∧ lend 24 (b.pay + 16) pre + 8 ≤ heapEnd ∧
      lend 24 (b.pay + 16) pre % 8 = 0 ∧
      ∀ y, lend 24 (b.pay + 16) pre ≤ y → y < lend 24 (b.pay + 16) pre + 8 → ¬ c.In y := by
  have hi := h.heap.heap
  have hbe : (b, e) ∈ G.regs r := by rw [hl]; exact List.mem_cons_self
  obtain ⟨-, hp0⟩ := h.regWord hr hl
  have hbG : b ∈ G.blocks := G.reg_mem hr hbe
  have hbsz := hp0.sz
  have hcl := hf.live
  rcases List.mem_cons.mp (lend_mem 24 (b.pay + 16) pre) with he | he
  · rw [he]
    obtain ⟨hb1, hb2, hb3⟩ := h.node_bounds hbG hbsz
    refine ⟨by omega, by omega, by omega, fun y h1 h2 hc => live_apart hi
      (h.heap.raw.live b hbG) hcl (fun e1 => hf.notG (e1 ▸ hbG))
      (by simp only [Blk.In, Blk.pay, Blk.fin] at hbsz h1 h2 ⊢; omega) hc⟩
  · obtain ⟨bx, hm, he⟩ := List.mem_map.mp he
    rw [← he]
    have hbm : bx ∈ e.arr := by rw [harr]; exact List.mem_append_left _ hm
    have hxG := G.arr_mem hr hbe hbm
    have hxsz := (hp0.arr.forall bx hbm).sz
    obtain ⟨hb1, hb2, hb3⟩ := h.node_bounds hxG hxsz
    refine ⟨by omega, by omega, by omega, fun y h1 h2 hc => live_apart hi
      (h.heap.raw.live _ hxG) hcl (fun e1 => hf.notG (e1 ▸ hxG))
      (by simp only [Blk.In, Blk.pay, Blk.fin] at hxsz h1 h2 ⊢; omega) hc⟩

/-- **A fresh node stored and linked** after the nodes `pre` (the machine's
stores: `nodeW`, then the link word). -/
theorem DcAt.insNodeW {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {en : Entry} {es : List Entry} {pre post : List (Blk × ANode)}
    {c : Blk} {i : Nat} {m1 m2 : List (Nat × Val)} {v : Val} {w0 w1 : BitVec 64}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hst : st.regs r = en :: es) (harr : e.arr = pre ++ post)
    (hm1 : List.Forall₂ (ARel ⟨L, G.strs⟩) pre m1) (hm2 : List.Forall₂ (ARel ⟨L, G.strs⟩) post m2)
    (hf : DcFresh H F L G c) (hcsz : 32 ≤ c.sz) (hi : i < 2 ^ 31) (hd : DatRegs w0 w1 g)
    (hv : g.Den ⟨L, G.strs⟩ v) :
    DcAt S (writeLog (nodeW M c.pay i (headPtr post) w0 w1)
        [(lend 24 (b.pay + 16) pre, 8, BitVec.ofNat 64 c.pay)]) H F L C
      (G.setReg r ((b, { e with arr := pre ++ (c, ⟨i, g⟩) :: post }) :: l)) hs
      (st.setReg r ({ en with arr := m1 ++ (i, v) :: m2 } :: es)) := by
  obtain ⟨hw0, hp0⟩ := h.regWord hr hl
  have hch := hp0.arr
  rw [harr] at hch
  have hnx := hch.lend_word
  obtain ⟨hl1, hl2, hl3, hlc⟩ := h.lendOut hr hl harr hf
  have hcb := blk_bounds h.heap.heap hf.live
  obtain ⟨hc1, hc2, hc3⟩ := hcb
  have hq : lend 24 (b.pay + 16) pre + 8 ≤ c.pay ∨ c.pay + 32 ≤ lend 24 (b.pay + 16) pre := by
    rcases Nat.lt_or_ge (lend 24 (b.pay + 16) pre) c.pay with h1 | h1
    · omega
    · refine Or.inr (Classical.byContradiction fun h2 => hlc _ (Nat.le_refl _) (by omega) ?_)
      simp only [Blk.In, Blk.pay, Blk.fin] at hcsz h1 h2 ⊢; omega
  have hqi : ∀ k, k + 8 ≤ 32 → c.pay + k + 8 ≤ lend 24 (b.pay + 16) pre ∨
      lend 24 (b.pay + 16) pre + 8 ≤ c.pay + k := fun k hk => by omega
  refine h.insNode (M' := writeLog (nodeW M c.pay i (headPtr post) w0 w1)
    [(lend 24 (b.pay + 16) pre, 8, BitVec.ofNat 64 c.pay)]) (i := i)
    hr hl hst harr hm1 hm2 hf (fun y hy => ?_) (ldv_store_hit _ _ _) ?_ ?_ hv
  · have e1c : c.fin = c.pay + c.sz := rfl
    simp only [Blk.In, e1c, not_or] at hy
    simp only [nodeW]
    repeat rw [imgM_store_miss _ _ (by omega)]
  · refine ⟨?_, hi, ⟨?_, ?_⟩, hcsz⟩
    · simp only [nodeW]
      rw [ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega),
        ldv_lw_miss _ _ (by omega)]
      exact ldv_lw_hitN _ rfl (toNat_ofNat_mod32 (by omega)) hi
    · simp only [nodeW]
      rw [ldv_ld_miss _ _ (hqi 8 (by omega)), ldv_ld_miss _ _ (by omega), ldv_store_hit]
      exact hd.tag
    · simp only [nodeW]
      rw [show c.pay + 8 + 8 = c.pay + 16 by omega, ldv_ld_miss _ _ (hqi 16 (by omega)),
        ldv_store_hit]
      exact hd.ptr
  · simp only [nodeW]
    rw [ldv_ld_miss _ _ (hqi 24 (by omega)), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_store_hit, hnx]

/-- The fresh node's stores make an array node with link `nx`. -/
theorem nodeW_node {M : Mem} {c : Blk} {i : Nat} {nx w0 w1 : BitVec 64} {g : GV}
    (hi : i < 2 ^ 31) (hd : DatRegs w0 w1 g) (hcsz : 32 ≤ c.sz) :
    ANodeAt (nodeW M c.pay i nx w0 w1) c ⟨i, g⟩ ∧
      ldv .ld (nodeW M c.pay i nx w0 w1) (c.pay + 24) = nx := by
  refine ⟨⟨?_, hi, ⟨?_, ?_⟩, hcsz⟩, ?_⟩
  · simp only [nodeW]
    rw [ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega)]
    exact ldv_lw_hitN _ rfl (toNat_ofNat_mod32 (by omega)) hi
  · simp only [nodeW]
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    exact hd.tag
  · simp only [nodeW]
    rw [show c.pay + 8 + 8 = c.pay + 16 by omega, ldv_store_hit]
    exact hd.ptr
  · simp only [nodeW]
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]

/-- **A first array on a register with no level**: the fresh node `c`
(stored by `nodeW`), the stack frame written, a second `dc_malloc` for the
level `b`, and the level's stores naming `c` as the array head. -/
theorem DcAt.newArr {S : Nat → Prop} {M Ms M1 : Mem} {H H' : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat}
    {c b : Blk} {i sp : Nat} {v : Val} {w0 w1 : BitVec 64}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = [])
    (hf : DcFresh H F L G c) (hcsz : 32 ≤ c.sz) (hi : i < 2 ^ 31) (hd : DatRegs w0 w1 g)
    (hv : g.Den ⟨L, G.strs⟩ v) (hab : heapEnd + 48 ≤ sp)
    (hMs : MemOnly (frameIn sp 48) Ms (nodeW M c.pay i 0#64 w0 w1))
    (hp : DcMallocPost S Ms M1 H H' 32 (sp - 32) b) :
    DcAt S (levW M1 b r (BitVec.ofNat 64 c.pay)) H' F L C
      (G.setReg r [(b, ⟨none, [(c, ⟨i, g⟩)]⟩)]) hs (st.setReg r [⟨none, [(i, v)]⟩]) := by
  have hi0 := h.heap.heap
  have e1c : c.fin = c.pay + c.sz := rfl
  have hst : st.regs r = [] := by
    have := h.den.regs r hr; rw [hl] at this
    revert this; generalize st.regs r = m; intro this; cases this; rfl
  have h1 := h.rawWrite hf (M' := nodeW M c.pay i 0#64 w0 w1) fun y hy => by
    simp only [Blk.In, e1c] at hy
    simp only [nodeW]
    repeat rw [imgM_store_miss _ _ (by omega)]
  have h2 := h1.outWrite hMs fun a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd] at *; omega), fun hg => by
      have := hg.lt; simp only [heapStart, heapEnd] at *; omega⟩
  obtain ⟨h3, hfb⟩ := h2.malloc hp (by decide) (by simp only [heapEnd] at *; omega)
  have hfc := hf.afterMalloc hp
  have hbsz := hp.size
  have hbb := blk_bounds hp.inv hfb.live
  obtain ⟨hb1, hb2, hb3⟩ := hbb
  have hcb := blk_bounds hi0 hf.live
  obtain ⟨hc1, hc2, hc3⟩ := hcb
  have hcne : c ≠ b := fun e1 => live_not_alloc hi0 hf.live (a := c.pay)
    ⟨Nat.le_refl _, by rw [e1c]; omega⟩ (hp.alloc _ (by rw [e1]; simp only [Blk.pay]; omega)
      (by rw [e1]; simp only [Blk.fin, Blk.pay] at hbsz ⊢; omega))
  have hcbd : ∀ y, c.In y → ¬ b.In y := fun y h1 h2 =>
    live_apart hp.inv hfc.live hfb.live hcne h1 h2
  have e1b : b.fin = b.pay + b.sz := rfl
  -- the level with an empty array
  have hm0 : MemOnly (fun a => b.In a ∨ RegWord r a) (levW M1 b r 0#64) M1 := fun y hy => by
    simp only [Blk.In, RegWord, e1b, not_or] at hy
    simp only [levW]
    repeat rw [imgM_store_miss _ _ (by omega)]
  have hrb : regAddr r + 8 ≤ b.pay := by simp only [regAddr, dcRegAddr, heapStart] at *; omega
  have h4 := h3.newLevel hr hl hfb hm0 (by
      simp only [levW]; rw [ldv_ld_miss _ _ (by omega), ldv_store_hit])
    (by simp only [levW]
        rw [ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega)]
        exact ldv_lw_hitN _ rfl (by decide) (by decide))
    (by simp only [levW]; rw [ldv_store_hit])
    (by simp only [levW]; rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit])
    hbsz
  -- `c` is fresh to the new state
  have hfc2 : DcFresh H' F L (G.setReg r [(b, RLev.empty)]) c := by
    refine ⟨hfc.live, fun hc => ?_, hfc.notNum⟩
    have hcnt := G.setReg_blocks_count hr [(b, RLev.empty)] c
    rw [hl] at hcnt
    have h0 : G.blocks.count c = 0 := List.count_eq_zero.mpr hf.notG
    have h1 : 0 < (G.setReg r [(b, RLev.empty)]).blocks.count c := List.count_pos_iff.mpr hc
    simp only [List.flatMap_cons, List.flatMap_nil, RLev.blocks, List.map_nil, List.append_nil,
      List.count_cons, List.count_nil] at hcnt
    have : (b == c) = false := by simp [Ne.symm hcne]
    rw [this] at hcnt
    simp at hcnt; omega
  -- the node
  obtain ⟨hn, hn24⟩ := nodeW_node (M := M) (nx := 0#64) hi hd hcsz
  have hcM : ∀ y, c.In y → imgM (levW M1 b r (BitVec.ofNat 64 c.pay)) y =
      imgM (nodeW M c.pay i 0#64 w0 w1) y := fun y hy => by
    have hyb := hcbd y hy
    have hna : ¬ AllocByte H y := live_not_alloc hi0 hf.live hy
    simp only [Blk.In, e1b] at hyb
    simp only [Blk.In, e1c] at hy
    have hrc : regAddr r + 8 ≤ c.pay := by
      have := hc1; simp only [regAddr, dcRegAddr, heapStart] at this ⊢; omega
    simp only [levW]
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega),
      hp.frame y hna (by simp only [frameIn]; simp only [heapEnd] at hab hc2; omega)]
    exact hMs y (by simp only [frameIn]; simp only [heapEnd] at hab hc2; omega)
  have h5 := h4.insNode (pre := []) (post := []) (m1 := []) (m2 := []) (i := i) (v := v)
    (b := b) (e := RLev.empty) (l := []) (en := ⟨none, []⟩) (es := [])
    (M' := levW M1 b r (BitVec.ofNat 64 c.pay)) hr (by simp [DcG.setReg])
    (by simp [St.setReg]) rfl .nil .nil hfc2
    (fun y hy => by
      simp only [lend, not_or] at hy
      have hy' : y < b.pay + 16 ∨ b.pay + 16 + 8 ≤ y := by omega
      simp only [levW]
      rw [imgM_store_miss _ (BitVec.ofNat 64 c.pay) hy', imgM_store_miss _ (0#64) hy'])
    (by simp only [lend, levW]; rw [ldv_store_hit])
    (hn.congr24 fun y h1 h2 => hcM y ⟨h1, by rw [e1c]; omega⟩)
    (by simp only [lend]
        rw [ldv_congr .ld fun j hj => hcM _ ⟨by omega, by simp only [widthOfM] at hj; rw [e1c]; omega⟩,
          hn24]
        simp only [levW]; rw [ldv_store_hit]) hv
  rw [DcG.setReg_setReg, St.setReg_setReg] at h5
  exact h5

/-! ## Inserting: the machine paths -/

/-- The registers `dc_array_set` may change. -/
abbrev arrClob : List Nat := [1, 2, 8, 9, 18, 10, 11, 12, 13, 14, 15]

/-- `dc_set_stacked_array (r, c)` on register `r`'s level `b` after the
fresh node `c` was stored with link `headPtr post`: `c` becomes the array
head. -/
theorem as_lev_link {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {en : Entry} {es : List Entry} {post : List (Blk × ANode)}
    {c : Blk} {i : Nat} {m2 : List (Nat × Val)} {v : Val} {w0 w1 : BitVec 64}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hst : st.regs r = en :: es) (harr : e.arr = post)
    (hm2 : List.Forall₂ (ARel ⟨L, G.strs⟩) post m2)
    (hf : DcFresh H F L G c) (hcsz : 32 ≤ c.sz) (hi : i < 2 ^ 31) (hd : DatRegs w0 w1 g)
    (hv : g.Den ⟨L, G.strs⟩ v)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 r) (h11 : R 11 = BitVec.ofNat 64 c.pay)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps [10, 15] R' R →
      DcAt S M' H F L C (G.setReg r ((b, { e with arr := (c, ⟨i, g⟩) :: post }) :: l)) hs
        (st.setReg r ({ en with arr := (i, v) :: m2 } :: es)) →
      (∀ a, OutHeap a → ¬ DcGlob a → imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000391c#64 R (nodeW M c.pay i (headPtr post) w0 w1) := by
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hbe : (b, e) ∈ G.regs r := by rw [hl]; exact List.mem_cons_self
  have hbG : b ∈ G.blocks := G.reg_mem hr hbe
  obtain ⟨hw0, hp0⟩ := h.regWord hr hl
  obtain ⟨hb1, hb2, hb3⟩ := h.node_bounds hbG hp0.sz
  obtain ⟨hc1, hc2, hc3⟩ := blk_bounds h.heap.heap hf.live
  have hrc : regAddr r + 8 ≤ c.pay := by
    have := hc1; simp only [regAddr, dcRegAddr, heapStart] at this ⊢; omega
  have hw : ldv .ld (nodeW M c.pay i (headPtr post) w0 w1) (regAddr r) = BitVec.ofNat 64 b.pay := by
    simp only [nodeW]
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_ld_miss _ _ (by omega)]
    exact hw0
  refine ss_lev hlive hS h.glob hr hw ⟨by omega, by omega, by omega⟩ R h10 hal fun R' hk1 => ?_
  rw [h11]
  have h1 := h.insNodeW (pre := []) (m1 := []) hr hl hst (by rw [harr]; rfl) .nil hm2 hf hcsz hi hd hv
  refine hk R' _ hk1 h1 fun a ho hg => ?_
  have hx := ho.1
  simp only [heapStart, heapEnd] at hx hb1 hb2 hc1 hc2
  simp only [lend, nodeW]
  repeat rw [imgM_store_miss _ _ (by omega)]

/-- The insert path's end with no node before (`0x80003cf8`, `a4 = 0`):
the fresh node becomes the array head. -/
theorem as_ins_head {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {en : Entry} {es : List Entry} {post : List (Blk × ANode)}
    {c : Blk} {i sp : Nat} {m2 : List (Nat × Val)} {v : Val} {w0 w1 ra s0 s1 s2 : BitVec 64}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hst : st.regs r = en :: es) (harr : e.arr = post)
    (hm2 : List.Forall₂ (ARel ⟨L, G.strs⟩) post m2)
    (hf : DcFresh H F L G c) (hcsz : 32 ≤ c.sz) (hi : i < 2 ^ 31) (hd : DatRegs w0 w1 g)
    (hv : g.Den ⟨L, G.strs⟩ v) (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64)) (h14 : R 14 = 0#64)
    (h18 : R 18 = BitVec.ofNat 64 r) (h10 : R 10 = BitVec.ofNat 64 c.pay)
    (l56 : ldv .ld M (sp - 64 + 56) = ra) (l48 : ldv .ld M (sp - 64 + 48) = s0)
    (l40 : ldv .ld M (sp - 64 + 40) = s1) (l32 : ldv .ld M (sp - 64 + 32) = s2)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M', Keeps arrClob R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 8 = s0 → R' 9 = s1 → R' 18 = s2 →
      DcAt S M' H F L C (G.setReg r ((b, { e with arr := (c, ⟨i, g⟩) :: post }) :: l)) hs
        (st.setReg r ({ en with arr := (i, v) :: m2 } :: es)) →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 112 a → imgM M' a = imgM M a) →
      DW live S Q ra R' M') :
    DW live S Q 0x80003cf8#64 R (nodeW M c.pay i (headPtr post) w0 w1) := by
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  obtain ⟨hc1, hc2, hc3⟩ := blk_bounds h.heap.heap hf.live
  have hsl := hsf.lo
  simp only [heapStart, heapEnd] at hc1 hc2 hab
  have hmf : ∀ k, k + 8 ≤ 64 → ldv .ld (nodeW M c.pay i (headPtr post) w0 w1) (sp - 64 + k) =
      ldv .ld M (sp - 64 + k) := fun k hk => by
    simp only [nodeW]
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_ld_miss _ _ (by omega)]
  refine as_ss0 hlive hS hsf (by simp only [heapEnd]; omega) R h2 h14
    ((hmf 56 (by omega)).trans l56) ((hmf 48 (by omega)).trans l48)
    ((hmf 40 (by omega)).trans l40) ((hmf 32 (by omega)).trans l32)
    fun R1 hk1 e1 e2 e8 e9 e18 e10 e11 => ?_
  refine as_lev_link hlive h hr hl hst harr hm2 hf hcsz hi hd hv R1 (e10.trans h18)
    (e11.trans h10) (by rw [e1]; exact hal) fun R' M' hk2 h1 hfr => ?_
  rw [e1]
  refine hk R' M' ((hk2.mono (by decide)).trans (hk1.mono (by decide))) ?_ ?_ ?_ ?_ ?_ h1
    fun a ho hg _ => hfr a ho hg
  · rw [hk2.get 1]; exact e1
  · rw [hk2.get 2]; exact e2
  · rw [hk2.get 8]; exact e8
  · rw [hk2.get 9]; exact e9
  · rw [hk2.get 18]; exact e18

end Dc.Mach
