import Dc.Mach.DcRegGet

/-!
# Setting a register's top value (M9)

`dc_register_set (r, value)` at `0x80002fd8` replaces the value of register
`r`'s top level (`regSet`): an empty register gets a fresh level; otherwise
the old value is freed through its slot inside the level's node and the new
datum is stored over it.

- `DcAt.setHead`: the state with the new datum, viewed at the memory with
  the datum stored (`datW`), the old value a handle; the machine memory is
  pending on the node's datum window (`Pend`), so `dc_free_num_specP` /
  `dc_free_str_specP` release the old value before the stores.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `M` with the datum words `w0`, `w1` stored at `a`. -/
abbrev datW (M : Mem) (a : Nat) (w0 w1 : BitVec 64) : Mem :=
  writeLog (writeLog M [(a, 8, w0)]) [(a + 8, 8, w1)]

/-- The ghost with register `r`'s levels `l`. -/
def DcG.setReg (G : DcG) (r : Nat) (l : List (Blk × RLev)) : DcG :=
  { G with regs := fun r' => if r' = r then l else G.regs r' }

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr' fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem nodup_count_le_one {α : Type} [DecidableEq α] :
    ∀ {l : List α}, l.Nodup → ∀ a, l.count a ≤ 1
  | [], _, a => by simp
  | x :: l, h, a => by
    rw [List.nodup_cons] at h
    rw [List.count_cons]
    by_cases hx : x = a
    · subst hx; rw [List.count_eq_zero.mpr h.1]; simp
    · have := nodup_count_le_one h.2 a; simp [hx]; omega

/-- `range 256` split at `r`: a function changed only at `r` changes only
the middle of its `flatMap`. -/
theorem flatMap_range_upd {β : Type} {f g : Nat → List β} {r : Nat} (hr : r < 256)
    (hg : ∀ r', r' ≠ r → g r' = f r') : ∃ P Q : List Nat, List.range 256 = P ++ r :: Q ∧
      (List.range 256).flatMap f = P.flatMap f ++ (f r ++ Q.flatMap f) ∧
      (List.range 256).flatMap g = P.flatMap f ++ (g r ++ Q.flatMap f) := by
  obtain ⟨P, Q, hPQ⟩ := List.append_of_mem (List.mem_range.mpr hr)
  have hnd := List.nodup_range (n := 256)
  rw [hPQ] at hnd
  have hP : r ∉ P := fun h => (List.nodup_append.mp hnd).2.2 _ h _ List.mem_cons_self rfl
  have hQ : r ∉ Q := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  refine ⟨P, Q, hPQ, by rw [hPQ, List.flatMap_append, List.flatMap_cons], ?_⟩
  rw [hPQ, List.flatMap_append, List.flatMap_cons,
    flatMap_congr' (l := P) fun r' h => hg r' fun e => hP (e ▸ h),
    flatMap_congr' (l := Q) fun r' h => hg r' fun e => hQ (e ▸ h)]

/-- Register `r`'s head node `b` is no other block of the state. -/
structure HeadOnly (G : DcG) (r : Nat) (b : Blk) (e : RLev) (l : List (Blk × RLev)) : Prop where
  stk : ∀ bg ∈ G.stk, bg.1 ≠ b
  regs : ∀ r', r' < 256 → r' ≠ r → ∀ be ∈ G.regs r', ∀ c ∈ RLev.blocks be, c ≠ b
  arr : ∀ bn ∈ e.arr, bn.1 ≠ b
  tail : ∀ be ∈ l, ∀ c ∈ RLev.blocks be, c ≠ b
  strs : ∀ o ∈ G.strs, o.hb ≠ b ∧ o.tb ≠ b

theorem DcG.headOnly {G : DcG} {r : Nat} {b : Blk} {e : RLev} {l : List (Blk × RLev)}
    (hnd : G.blocks.Nodup) (hr : r < 256) (hl : G.regs r = (b, e) :: l) : HeadOnly G r b e l := by
  obtain ⟨P, Q, hPQ, hf, -⟩ := flatMap_range_upd (f := fun r' => (G.regs r').flatMap RLev.blocks)
    (g := fun r' => (G.regs r').flatMap RLev.blocks) hr fun _ _ => rfl
  have hc := nodup_count_le_one hnd b
  unfold DcG.blocks at hc
  rw [hf, hl] at hc
  simp only [List.count_append, List.flatMap_cons, RLev.blocks, List.count_cons, beq_self_eq_true,
    ite_true] at hc
  have z : ∀ (l' : List Blk), l'.count b = 0 → ∀ c ∈ l', c ≠ b := fun l' h0 c hcl e => by
    subst e; exact List.count_eq_zero.mp h0 hcl
  refine ⟨fun bg hbg => z (G.stk.map (fun x => x.1)) (by omega) _ (List.mem_map.mpr ⟨bg, hbg, rfl⟩),
    fun r' hr' hne be hbe c hcm => ?_,
    fun bn hbn => z (e.arr.map (fun x => x.1)) (by omega) _ (List.mem_map.mpr ⟨bn, hbn, rfl⟩),
    fun be hbe c hcm => z (l.flatMap RLev.blocks) (by omega) _ (List.mem_flatMap.mpr ⟨be, hbe, hcm⟩),
    fun o ho => ⟨z (G.strs.flatMap fun o => [o.hb, o.tb]) (by omega) _
      (List.mem_flatMap.mpr ⟨o, ho, by simp⟩),
      z (G.strs.flatMap fun o => [o.hb, o.tb]) (by omega) _ (List.mem_flatMap.mpr ⟨o, ho, by simp⟩)⟩⟩
  have hm : r' ∈ P ++ r :: Q := hPQ ▸ List.mem_range.mpr hr'
  rcases List.mem_append.mp hm with hm | hm
  · exact z (P.flatMap fun r' => (G.regs r').flatMap RLev.blocks) (by omega) _
      (List.mem_flatMap.mpr ⟨r', hm, List.mem_flatMap.mpr ⟨be, hbe, hcm⟩⟩)
  · rcases List.mem_cons.mp hm with e | hm
    · exact absurd e hne
    · exact z (Q.flatMap fun r' => (G.regs r').flatMap RLev.blocks) (by omega) _
        (List.mem_flatMap.mpr ⟨r', hm, List.mem_flatMap.mpr ⟨be, hbe, hcm⟩⟩)

/-- A level's block is a block of the state. -/
theorem DcG.lev_mem {G : DcG} {r : Nat} (hr : r < 256) {be : Blk × RLev} (hbe : be ∈ G.regs r)
    {c : Blk} (hc : c ∈ RLev.blocks be) : c ∈ G.blocks := by
  rcases List.mem_cons.mp hc with rfl | hc
  · exact G.reg_mem hr hbe
  · obtain ⟨bn, hn, rfl⟩ := List.mem_map.mp hc
    exact G.arr_mem hr hbe hn

/-- The head level with the datum `g`. -/
abbrev RLev.withV (e : RLev) (g : GV) : RLev := { e with v := some g }

theorem DcG.setHead_blocks {G : DcG} {r : Nat} {b : Blk} {e : RLev} {l : List (Blk × RLev)}
    (g : GV) (hl : G.regs r = (b, e) :: l) : (G.setReg r ((b, e.withV g) :: l)).blocks = G.blocks := by
  have hf : (fun r' => ((G.setReg r ((b, e.withV g) :: l)).regs r').flatMap RLev.blocks) =
      fun r' => (G.regs r').flatMap RLev.blocks := by
    funext r'
    simp only [DcG.setReg]
    split
    · subst_vars; rw [hl]; simp [RLev.blocks]
    · rfl
  show G.stk.map (·.1) ++ (List.range 256).flatMap
      (fun r' => ((G.setReg r ((b, e.withV g) :: l)).regs r').flatMap RLev.blocks) ++
      G.strs.flatMap (fun o => [o.hb, o.tb]) ++ G.lbuf.toList = G.blocks
  rw [hf]; rfl

theorem DcG.setHead_count {G : DcG} {r : Nat} {b : Blk} {e : RLev} {l : List (Blk × RLev)}
    (g : GV) (hs : List GV) (hr : r < 256) (hl : G.regs r = (b, e) :: l) (y : GV) :
    ((G.setReg r ((b, e.withV g) :: l)).vals ++ (e.v.toList ++ hs)).count y =
      (G.vals ++ g :: hs).count y := by
  obtain ⟨P, Q, -, hf, hf'⟩ := flatMap_range_upd (f := fun r' => (G.regs r').flatMap RLev.vals)
    (g := fun r' => ((G.setReg r ((b, e.withV g) :: l)).regs r').flatMap RLev.vals) hr
    fun r' hne => by simp [DcG.setReg, hne]
  have e1 : (G.setReg r ((b, e.withV g) :: l)).vals = G.stk.map (·.2) ++ (List.range 256).flatMap
      (fun r' => ((G.setReg r ((b, e.withV g) :: l)).regs r').flatMap RLev.vals) := rfl
  have e2 : G.vals = G.stk.map (·.2) ++ (List.range 256).flatMap
      (fun r' => (G.regs r').flatMap RLev.vals) := rfl
  rw [e1, e2, hf, hf']
  simp only [DcG.setReg, ite_true, hl, List.flatMap_cons, RLev.vals, List.count_append, List.count_cons,
    Option.toList_some, List.count_singleton, List.nil_append]
  simp only [List.count_nil]
  omega

/-- **The ghost side of a new top value**: the datum `g` (denoting `v`) moves
from the handles into register `r`'s top level; the old datum, if any,
becomes a handle. -/
theorem DcDen.setHead {L : List NumObj} {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St}
    {r : Nat} {b : Blk} {e : RLev} {l : List (Blk × RLev)} {v : Val}
    (d : DcDen L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hv : g.Den ⟨L, G.strs⟩ v) :
    DcDen L C (G.setReg r ((b, e.withV g) :: l)) (e.v.toList ++ hs) (regSet st r v) := by
  have hd2 := d.regs r hr
  rw [hl] at hd2
  generalize hsr : st.regs r = sl at hd2
  cases hd2 with
  | @cons _ en _ es hen hrest =>
  have hst : regSet st r v = st.setReg r ({ en with val := some v } :: es) := by
    unfold regSet; rw [hsr]
  rw [hst]
  have hc := DcG.setHead_count g hs hr hl
  refine { d with
    regs := fun r' hr' => ?_
    regsHi := fun r' hr' => ?_
    hsDen := fun g' hg' => ?_
    numRefs := fun x hx => by rw [hc]; exact d.numRefs x hx
    strRefs := fun o ho => by rw [hc]; exact d.strRefs o ho }
  · simp only [DcG.setReg, St.setReg]
    split
    · subst_vars; exact .cons ⟨.some hv, hen.arr⟩ hrest
    · exact d.regs r' hr'
  · have hne : r' ≠ r := by omega
    simp only [DcG.setReg, St.setReg, hne, ite_false]; exact d.regsHi r' hr'
  · rcases List.mem_append.mp hg' with hg' | hg'
    · have hval := hen.val
      revert hval hg'
      generalize e.v = ov; generalize en.val = ow
      intro hg' hval
      cases ov with
      | none => exact absurd hg' List.not_mem_nil
      | some go =>
        have hg2 : g' = go := List.mem_singleton.mp hg'
        subst hg2
        cases ow with
        | none => cases hval
        | some vo => cases hval with | some hr2 => exact ⟨vo, hr2⟩
    · exact d.hsDen g' (List.mem_cons_of_mem _ hg')

/-- An array node through a memory agreeing on its block. -/
theorem ANodeAt.frame {Mt Mt' : Mem} {c : Blk} {n : ANode} (hq : ANodeAt Mt c n)
    (hag : ∀ x, c.In x → imgM Mt' x = imgM Mt x) :
    ANodeAt Mt' c n ∧ ldv .ld Mt' (c.pay + 24) = ldv .ld Mt (c.pay + 24) := by
  have hb' : ∀ x, InBlocks [c] x → imgM Mt' x = imgM Mt x := fun x ⟨c', hc, hcx⟩ => by
    rw [List.mem_singleton.mp hc] at hcx; exact hag x hcx
  have hcm : c ∈ [c] := List.mem_singleton_self _
  have hcs := hq.sz
  refine ⟨⟨?_, hq.idxLt, DatAt.frame hcm hb' (by omega) hq.dat, hcs⟩,
    ldv_blk hcm hb' .ld (by simp only [widthOfM]; omega)⟩
  have := ldv_blk (o := 0) hcm hb' .lw (by simp only [widthOfM]; omega)
  simp only [Nat.add_zero] at this; rw [this]; exact hq.idx

/-- `regSet` keeps the scalar state. -/
theorem regSet_scalars (st : St) (r : Nat) (v : Val) :
    (regSet st r v).ibase = st.ibase ∧ (regSet st r v).obase = st.obase ∧
      (regSet st r v).scale = st.scale ∧ (regSet st r v).unwind = st.unwind ∧
      (regSet st r v).noexit = st.noexit := by
  unfold regSet; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The memory side of a new top value**: the datum words stored over the
head node's datum. -/
theorem DcAt.setHeadView {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st st' : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {g : GV} {w0 w1 : BitVec 64} (h : DcAt S M H F L C G hs st)
    (hr : r < 256) (hl : G.regs r = (b, e) :: l) (hd : DatRegs w0 w1 g)
    (hst : st'.ibase = st.ibase ∧ st'.obase = st.obase ∧ st'.scale = st.scale ∧
      st'.unwind = st.unwind ∧ st'.noexit = st.noexit) :
    DcView (datW M b.pay w0 w1) (G.setReg r ((b, e.withV g) :: l)) C st' := by
  have hi := h.heap.heap
  have ho := G.headOnly h.nodup hr hl
  have hbG : b ∈ G.blocks := G.reg_mem hr (by rw [hl]; exact List.mem_cons_self)
  have hbl := h.heap.raw.live b hbG
  have hv0 := h.view.regs r hr
  rw [hl] at hv0
  cases hv0 with
  | cons h0 hp hrest =>
  have hsz := hp.sz
  have hoff : ∀ c ∈ G.blocks, c ≠ b → ∀ x, c.In x → imgM (datW M b.pay w0 w1) x = imgM M x :=
    fun c hc hne x hx => by
      have hn : ¬ (b.pay ≤ x ∧ x < b.pay + 16) := fun hw => live_apart hi (h.heap.raw.live c hc) hbl
        hne hx (by simp only [Blk.In, Blk.pay, Blk.fin] at hw ⊢; omega)
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hbin := live_in_heap hi hbl (show b.In b.pay by simp only [Blk.In, Blk.pay, Blk.fin]; omega)
  have hglob : ∀ x, DcGlob x → imgM (datW M b.pay w0 w1) x = imgM M x := fun x hx => by
    have := hx.lt
    rw [imgM_store_miss _ _ (by simp only [heapStart] at *; omega),
      imgM_store_miss _ _ (by simp only [heapStart] at *; omega)]
  have hword : ∀ k, b.pay + 16 ≤ k → k + 8 ≤ b.fin →
      ldv .ld (datW M b.pay w0 w1) k = ldv .ld M k := fun k h1 h2 => by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
  have hreg : ∀ r', r' < 256 → ldv .ld (datW M b.pay w0 w1) (regAddr r') = ldv .ld M (regAddr r') :=
    fun r' hr' => ldv_congr .ld fun j hj => hglob _ (by
      simp only [widthOfM, DcGlob, regAddr, dc_addrs] at hj ⊢; omega)
  refine h.view.withChains rfl rfl hst (fun o hom x hx => ?_) (fun x hx _ => hglob x hx) ?_
    fun r' hr' => ?_
  · obtain ⟨n1, n2⟩ := ho.strs o hom
    rcases hx with hx | hx
    · exact hoff _ (G.str_mem hom).1 n1 x hx
    · exact hoff _ (G.str_mem hom).2 n2 x hx
  · exact stkChain_frame h.view.stk (ldv_congr .ld fun j hj => hglob _ (by
      simp only [widthOfM, DcGlob, dc_addrs] at hj ⊢; omega))
      fun bg hm x hx => hoff _ (G.stk_mem hm) (ho.stk bg hm) x hx
  · have e1 : (G.setReg r ((b, e.withV g) :: l)).regs r' =
        if r' = r then (b, e.withV g) :: l else G.regs r' := rfl
    rw [e1]
    split
    · subst_vars
      refine .cons ((hreg _ hr').trans h0) ⟨slotMem_dat hd, ?_, hsz⟩ ?_
      · refine hp.arr.frame (hword _ (by omega) (by simp only [Blk.fin, Blk.pay] at *; omega)) fun bn hbn hq => ?_
        exact ANodeAt.frame hq fun x hx => hoff _ (G.arr_mem hr' (by rw [hl]; exact List.mem_cons_self) hbn)
          (ho.arr bn hbn) x hx
      · exact regChain_frame hrest (hword _ (by omega) (by simp only [Blk.fin, Blk.pay] at *; omega))
          fun be hm c hc x hx => hoff c (G.lev_mem hr' (by rw [hl]; exact List.mem_cons_of_mem _ hm) hc)
            (ho.tail be hm c hc) x hx
    · exact regChain_frame (h.view.regs r' hr') (hreg r' hr')
        fun be hm c hc x hx => hoff c (G.lev_mem hr' hm hc) (ho.regs r' hr' ‹_› be hm c hc) x hx

/-- The datum window of a node. -/
abbrev datWin (a x : Nat) : Prop := a ≤ x ∧ x < a + 16

/-- **A node's datum window is pending**. -/
theorem pend_datW {G : DcG} {b : Blk} (hb : b ∈ G.blocks) (hns : ∀ o ∈ G.strs, o.hb ≠ b ∧ o.tb ≠ b)
    (hsz : 16 ≤ b.sz) (w0 w1 : BitVec 64) :
    Pend G [b] (datWin b.pay) (fun M => datW M b.pay w0 w1) where
  out M x hx := by
    simp only [datWin] at hx
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  fix M M' x hx := by
    simp only [datWin] at hx
    by_cases h8 : x < b.pay + 8
    · have hm : x < b.pay + 8 ∨ b.pay + 8 + 8 ≤ x := .inl h8
      rw [imgM_store_miss (writeLog M [(b.pay, 8, w0)]) w1 hm,
        imgM_store_miss (writeLog M' [(b.pay, 8, w0)]) w1 hm]
      exact imgM_store_same _ _ w0 (.inr rfl) ⟨hx.1, h8⟩
    · exact imgM_store_same _ _ w1 (.inr rfl) ⟨by omega, by omega⟩
  sub e he := by rw [List.mem_singleton.mp he]; exact hb
  win x hx := .inl ⟨b, List.mem_singleton_self _, by
    simp only [datWin, Blk.In, Blk.pay, Blk.fin] at hx ⊢; omega⟩
  nstr e he o ho := by
    rw [List.mem_singleton.mp he]; exact ⟨(hns o ho).1.symm, (hns o ho).2.symm⟩

/-- **A new top value, before the old one is released**: viewed at the
memory with the new datum stored, register `r`'s top level holds `g`
(denoting `v`), the old datum is a handle, and the machine memory is pending
on the node's datum window. -/
theorem DcAt.setHead {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {v : Val} {w0 w1 : BitVec 64}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hd : DatRegs w0 w1 g) (hv : g.Den ⟨L, G.strs⟩ v) :
    DcAt S (datW M b.pay w0 w1) H F L C (G.setReg r ((b, e.withV g) :: l)) (e.v.toList ++ hs)
        (regSet st r v) ∧
      Pend (G.setReg r ((b, e.withV g) :: l)) [b] (datWin b.pay) (fun M => datW M b.pay w0 w1) := by
  have hB := DcG.setHead_blocks g hl
  have hbG : b ∈ G.blocks := G.reg_mem hr (by rw [hl]; exact List.mem_cons_self)
  have ho := G.headOnly h.nodup hr hl
  have hv0 := h.view.regs r hr
  rw [hl] at hv0
  have hsz : 32 ≤ b.sz := by cases hv0 with | cons _ hp _ => exact hp.sz
  have hpd : Pend (G.setReg r ((b, e.withV g) :: l)) [b] (datWin b.pay) (fun M => datW M b.pay w0 w1) :=
    pend_datW (G := G.setReg r ((b, e.withV g) :: l)) (hB ▸ hbG) ho.strs (by omega) w0 w1
  refine ⟨⟨?_, hB ▸ h.nodup, h.setHeadView hr hl hd (regSet_scalars st r v), h.den.setHead hr hl hv,
    h.glob, h.col⟩, hpd⟩
  have hb1 : BcHeap S ((G.setReg r ((b, e.withV g) :: l)).rawsOff [b] M) M H F L :=
    h.heap.subRaw (fun c hc => by
      have := (DcG.mem_rawsOff.mp hc).1; rw [hB] at this; exact this) fun _ _ _ _ => rfl
  exact hb1.ofMach hpd (fun c hc => by rw [List.mem_singleton.mp hc]; exact h.heap.raw.live b hbG)
    fun c hc => by rw [List.mem_singleton.mp hc]; exact h.heap.raw.out b hbG

/-! ## A new level -/

/-- The empty level. -/
abbrev RLev.empty : RLev := ⟨none, []⟩

/-- Counts over the register chains with register `r`'s levels replaced. -/
theorem DcG.setReg_flat_count {β : Type} [BEq β] [LawfulBEq β] (G : DcG) {r : Nat} (hr : r < 256)
    (l' : List (Blk × RLev)) (f : Blk × RLev → List β) (y : β) :
    ((List.range 256).flatMap (fun r' => ((G.setReg r l').regs r').flatMap f)).count y +
        ((G.regs r).flatMap f).count y =
      ((List.range 256).flatMap (fun r' => (G.regs r').flatMap f)).count y + (l'.flatMap f).count y := by
  obtain ⟨P, Q, -, hf, hf'⟩ := flatMap_range_upd (f := fun r' => (G.regs r').flatMap f)
    (g := fun r' => ((G.setReg r l').regs r').flatMap f) hr fun r' hne => by simp [DcG.setReg, hne]
  rw [hf, hf']
  simp only [DcG.setReg, ite_true, List.count_append]
  omega

theorem DcG.setReg_blocks_count (G : DcG) {r : Nat} (hr : r < 256) (l' : List (Blk × RLev)) (y : Blk) :
    (G.setReg r l').blocks.count y + ((G.regs r).flatMap RLev.blocks).count y =
      G.blocks.count y + (l'.flatMap RLev.blocks).count y := by
  have e1 : (G.setReg r l').blocks = G.stk.map (·.1) ++ (List.range 256).flatMap
      (fun r' => ((G.setReg r l').regs r').flatMap RLev.blocks) ++
      G.strs.flatMap (fun o => [o.hb, o.tb]) ++ G.lbuf.toList := rfl
  have e2 : G.blocks = G.stk.map (·.1) ++ (List.range 256).flatMap
      (fun r' => (G.regs r').flatMap RLev.blocks) ++
      G.strs.flatMap (fun o => [o.hb, o.tb]) ++ G.lbuf.toList := rfl
  have := G.setReg_flat_count hr l' RLev.blocks y
  rw [e1, e2]
  simp only [List.count_append] at this ⊢
  omega

theorem DcG.setReg_vals_count (G : DcG) {r : Nat} (hr : r < 256) (l' : List (Blk × RLev)) (y : GV) :
    (G.setReg r l').vals.count y + ((G.regs r).flatMap RLev.vals).count y =
      G.vals.count y + (l'.flatMap RLev.vals).count y := by
  have e1 : (G.setReg r l').vals = G.stk.map (·.2) ++ (List.range 256).flatMap
      (fun r' => ((G.setReg r l').regs r').flatMap RLev.vals) := rfl
  have e2 : G.vals = G.stk.map (·.2) ++ (List.range 256).flatMap
      (fun r' => (G.regs r').flatMap RLev.vals) := rfl
  have := G.setReg_flat_count hr l' RLev.vals y
  rw [e1, e2]
  simp only [List.count_append] at this ⊢
  omega

/-- The bytes of register `r`'s word. -/
abbrev RegWord (r a : Nat) : Prop := regAddr r ≤ a ∧ a < regAddr r + 8

/-- **A level pushed** on register `r`: the fresh node `c` holds the datum
`ov` (a handle leaving `hs`) and no array, its link the old head. -/
theorem DcAt.consLev {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {r : Nat} {c : Blk} {ov : Option GV}
    {ovv : Option Val}
    (h : DcAt S M H F L C G (ov.toList ++ hs) st) (hr : r < 256) (hf : DcFresh H F L G c)
    (hm : MemOnly (fun a => c.In a ∨ RegWord r a) M' M)
    (hw : ldv .ld M' (regAddr r) = BitVec.ofNat 64 c.pay) (hn : RLevAt M' c ⟨ov, []⟩)
    (h24 : ldv .ld M' (c.pay + 24) = ldv .ld M (regAddr r))
    (hv : Option.Rel (GV.Den ⟨L, G.strs⟩) ov ovv) :
    DcAt S M' H F L C (G.setReg r ((c, ⟨ov, []⟩) :: G.regs r)) hs
      (st.setReg r (⟨ovv, []⟩ :: st.regs r)) := by
  have hi := h.heap.heap
  have hperm : (G.setReg r ((c, ⟨ov, []⟩) :: G.regs r)).blocks.Perm (c :: G.blocks) := by
    rw [List.perm_iff_count]
    intro y
    have := G.setReg_blocks_count hr ((c, ⟨ov, []⟩) :: G.regs r) y
    simp only [List.flatMap_cons, RLev.blocks, List.map_nil, List.count_append, List.count_cons,
      List.count_nil] at this ⊢
    omega
  have hcount : ∀ y, ((G.setReg r ((c, ⟨ov, []⟩) :: G.regs r)).vals ++ hs).count y =
      (G.vals ++ (ov.toList ++ hs)).count y := fun y => by
    have := G.setReg_vals_count hr ((c, ⟨ov, []⟩) :: G.regs r) y
    simp only [List.flatMap_cons, RLev.vals, List.map_nil, List.append_nil, List.count_append] at this ⊢
    omega
  have hrw : ∀ a, RegWord r a → OutHeap a ∧ DcGlob a := fun a ha => by
    simp only [RegWord, regAddr, dc_addrs] at ha
    exact ⟨DcGlob.outHeap (by simp only [DcGlob, dc_addrs]; omega),
      by simp only [DcGlob, dc_addrs]; omega⟩
  have hoff : ∀ c' ∈ H.live, c' ≠ c → ∀ a, c'.In a → imgM M' a = imgM M a := fun c' hc' hne a ha =>
    hm a fun h' => h'.elim (fun hca => live_apart hi hc' hf.live hne ha hca)
      fun hrg => (hrw a hrg).1.1 (live_in_heap hi hc' ha)
  have hglob : ∀ a, DcGlob a → ¬ RegWord r a → imgM M' a = imgM M a := fun a ha hn =>
    hm a fun h' => h'.elim (fun hca => by
      have := live_in_heap hi hf.live hca; have := ha.lt; simp only [heapStart] at *; omega) hn
  have hGoff : ∀ c' ∈ G.blocks, ∀ a, c'.In a → imgM M' a = imgM M a := fun c' hc' =>
    hoff c' (h.heap.raw.live c' hc') fun e => hf.notG (e ▸ hc')
  have hb1 : BcHeap S (G.raws M) M' H F L :=
    h.heap.transportOwn (fun a ha => hm a fun h' => h'.elim
        (fun hca => live_not_alloc hi hf.live hca ha) fun hrg => OutHeap.not_alloc hi (hrw a hrg).1 ha)
      (fun c' hc' a ha => hoff c' (h.heap.owned_live hc') (fun e => by
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact hf.notNum (e ▸ hc')
        · exact hf.notG (e ▸ hc')) a ha)
      fun j hj => hm _ fun h' => h'.elim (fun hca => by
        have := live_in_heap hi hf.live hca; simp only [bcFreeAddr, heapStart] at *; omega)
        fun hrg => by simp only [RegWord, regAddr, bcFreeAddr, dc_addrs] at hrg; omega
  have hd := h.den
  have hcin := live_in_heap hi hf.live (show c.In (c.pay + 24) by
    have := hn.sz; simp only [Blk.In, Blk.pay, Blk.fin]; omega)
  -- the old chain, anchored at the new node's link word
  have hold : LChain M' 24 (RLevAt M') (c.pay + 24) (G.regs r) := by
    have hlev : ∀ be ∈ G.regs r, ∀ c' ∈ RLev.blocks be, ∀ x, c'.In x → c' ≠ c ∧ c' ∈ G.blocks :=
      fun be hbe c' hc' _ _ => ⟨fun e => hf.notG (e ▸ G.lev_mem hr hbe hc'), G.lev_mem hr hbe hc'⟩
    have hM2 : MemOnly (fun a => c.In a) (writeLog M [(c.pay + 24, 8, ldv .ld M (regAddr r))]) M :=
      fun a ha => MemOnly.store M _ 8 _ a fun hh => ha (by
        have := hn.sz; simp only [Blk.In, Blk.pay, Blk.fin] at hh ⊢; omega)
    have c1 := regChain_frame (Mt' := writeLog M [(c.pay + 24, 8, ldv .ld M (regAddr r))])
      (h.view.regs r hr) (ldv_congr .ld fun j hj => hM2 _ fun hca => by
        have := live_in_heap hi hf.live hca
        simp only [regAddr, dc_addrs, heapStart, widthOfM] at hj this; omega)
      fun be hbe c' hc' x hx => hM2 x fun hca =>
        live_apart hi (h.heap.raw.live c' (hlev be hbe c' hc' x hx).2) hf.live
          (hlev be hbe c' hc' x hx).1 hx hca
    have c2 := c1.reword (a' := c.pay + 24) (by
      rw [ldv_store_hit, ldv_ld_miss _ _ (by simp only [regAddr, dc_addrs, heapStart] at hcin ⊢; omega)])
    refine regChain_frame c2 (by
      rw [h24, ldv_store_hit]) fun be hbe c' hc' x hx => ?_
    rw [hGoff c' (hlev be hbe c' hc' x hx).2 x hx]
    exact (hM2 x fun hca => live_apart hi (h.heap.raw.live c' (hlev be hbe c' hc' x hx).2) hf.live
      (hlev be hbe c' hc' x hx).1 hx hca).symm
  refine
    { heap := (hb1.addRaw hf.live hf.notNum).subRaw (fun b hb => hperm.mem_iff.mp hb) fun _ _ _ _ => rfl
      nodup := hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hf.notG, h.nodup⟩)
      view := h.view.withChains rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun o ho x hx => hx.elim (fun hx => hGoff _ (G.str_mem ho).1 x hx)
          fun hx => hGoff _ (G.str_mem ho).2 x hx)
        (fun a ha hc => hglob a ha fun hrg => hc (.inr (by
          simp only [RegWord, regAddr] at hrg; omega)))
        (stkChain_frame h.view.stk (ldv_congr .ld fun j hj => hglob _ (by
          simp only [widthOfM, DcGlob, dc_addrs] at hj ⊢; omega) (by
          simp only [widthOfM, RegWord, regAddr, dc_addrs] at hj ⊢; omega))
          fun bg hmm x hx => hGoff _ (G.stk_mem hmm) x hx) fun r' hr' => ?_
      den := ?_
      glob := h.glob
      col := h.col }
  · have e1 : (G.setReg r ((c, ⟨ov, []⟩) :: G.regs r)).regs r' =
        if r' = r then (c, ⟨ov, []⟩) :: G.regs r else G.regs r' := rfl
    rw [e1]
    split
    · subst_vars
      exact .cons hw hn hold
    · exact regChain_frame (h.view.regs r' hr') (ldv_congr .ld fun j hj => hglob _ (by
        simp only [widthOfM, DcGlob, regAddr, dc_addrs] at hj ⊢; omega) (by
        simp only [widthOfM, RegWord, regAddr, dc_addrs] at hj ⊢; omega))
        fun be hmm c' hc' x hx => hGoff c' (G.lev_mem hr' hmm hc') x hx
  · refine { hd with
      regs := fun r' hr' => ?_
      regsHi := fun r' hr' => ?_
      hsDen := fun g hg => hd.hsDen g (List.mem_append_right _ hg)
      numRefs := fun x hx => by rw [hcount]; exact hd.numRefs x hx
      strRefs := fun o ho => by rw [hcount]; exact hd.strRefs o ho }
    · simp only [DcG.setReg, St.setReg]
      split
      · subst_vars; exact .cons ⟨hv, .nil⟩ (hd.regs r' hr')
      · exact hd.regs r' hr'
    · have hne : r' ≠ r := by omega
      simp only [DcG.setReg, St.setReg, hne, ite_false]; exact hd.regsHi r' hr'

/-- **A new empty level**: register `r` (empty) now holds the fresh node `c`
with type `0` and no array. -/
theorem DcAt.newLevel {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {r : Nat} {c : Blk}
    (h : DcAt S M H F L C G hs st) (hr : r < 256) (hl : G.regs r = []) (hf : DcFresh H F L G c)
    (hm : MemOnly (fun a => c.In a ∨ RegWord r a) M' M)
    (hw : ldv .ld M' (regAddr r) = BitVec.ofNat 64 c.pay) (h0 : ldv .lw M' c.pay = 0#64)
    (h16 : ldv .ld M' (c.pay + 16) = 0#64) (h24 : ldv .ld M' (c.pay + 24) = 0#64)
    (hsz : 32 ≤ c.sz) :
    DcAt S M' H F L C (G.setReg r [(c, RLev.empty)]) hs (st.setReg r [⟨none, []⟩]) := by
  have hv0 := h.view.regs r hr
  rw [hl] at hv0
  have hz : ldv .ld M (regAddr r) = 0#64 := by cases hv0; assumption
  have hst : st.regs r = [] := by
    have := h.den.regs r hr; rw [hl] at this
    revert this; generalize st.regs r = m; intro this; cases this; rfl
  have e := DcAt.consLev (ov := none) (ovv := none) (M' := M') h hr hf hm hw ⟨h0, .nil h16, hsz⟩
    (h24.trans hz.symm) .none
  rw [hl, hst] at e
  exact e

/-! ## The machine -/

/-- The registers `dc_register_set` may change. -/
abbrev setClob : List Nat := [10, 11, 12, 13, 14, 15]

/-- `dc_register_set`'s datum stores and return on a level with no value (`0x8000301c`, `sp` lowered by 48, `a0` the node at `a`). -/
theorem reg_set_tail0 {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp a : Nat}
    {w0 w1 ra : BitVec 64} (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (ha : heapStart ≤ a ∧ a + 16 ≤ heapEnd ∧ a % 8 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h10 : R 10 = BitVec.ofNat 64 a)
    (h16 : ldv .ld M (sp - 48 + 16) = w0) (h24 : ldv .ld M (sp - 48 + 24) = w1)
    (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps (1 :: 2 :: setClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      DW live S Q ra R' (datW M a w0 w1)) :
    DW live S Q 0x8000301c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  obtain ⟨ha1, ha2, ha3⟩ := ha
  simp only [heapEnd, heapStart] at hab ha1 ha2
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h2, h10, h16, h24, hra]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first | (bsimp []; exact hal) | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp []; congr 1; omega)
/-- `dc_register_set`'s datum stores and return on a level with no value or a
new level (`0x80003090`, `sp` lowered by 48, `a0` the node at `a`). -/
theorem reg_set_tailN {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp a : Nat}
    {w0 w1 ra : BitVec 64} (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (ha : heapStart ≤ a ∧ a + 16 ≤ heapEnd ∧ a % 8 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h10 : R 10 = BitVec.ofNat 64 a)
    (h16 : ldv .ld M (sp - 48 + 16) = w0) (h24 : ldv .ld M (sp - 48 + 24) = w1)
    (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps (1 :: 2 :: setClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      DW live S Q ra R' (datW M a w0 w1)) :
    DW live S Q 0x80003090#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  obtain ⟨ha1, ha2, ha3⟩ := ha
  simp only [heapEnd, heapStart] at hab ha1 ha2
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h2, h10, h16, h24, hra]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals first | (bsimp []; exact hal) | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp []; congr 1; omega)

/-- `dc_register_set`'s datum stores and return after `dc_free_num` of the
old value (`0x800030b8`, `sp` lowered by 48, the register's word saved at
`8(sp)`, holding the node at `a`). -/
theorem reg_set_tailF {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp a r : Nat}
    {w0 w1 ra : BitVec 64} (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (ha : heapStart ≤ a ∧ a + 16 ≤ heapEnd ∧ a % 8 = 0) (hr : r < 256)
    (hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48))
    (h8 : ldv .ld M (sp - 48 + 8) = BitVec.ofNat 64 (regAddr r))
    (hw : ldv .ld M (regAddr r) = BitVec.ofNat 64 a)
    (h16 : ldv .ld M (sp - 48 + 16) = w0) (h24 : ldv .ld M (sp - 48 + 24) = w1)
    (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps (1 :: 2 :: setClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      DW live S Q ra R' (datW M a w0 w1)) :
    DW live S Q 0x800030b8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  obtain ⟨ha1, ha2, ha3⟩ := ha
  simp only [heapEnd, heapStart] at hab ha1 ha2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  bc_run hlive hS [h2, h8, hra8, hw, h16, h24, hra]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [LdOK, regAddr, dcRegAddr]; omega) | skip
  all_goals first | (bsimp []; exact hal) | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp []; congr 1; omega)

/-- `dc_register_set`'s datum stores and return after `dc_free_str` of the
old value (`0x800030e8`, `sp` lowered by 48, the register's word saved at
`8(sp)`, holding the node at `a`). -/
theorem reg_set_tailS {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {sp a r : Nat}
    {w0 w1 ra : BitVec 64} (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (ha : heapStart ≤ a ∧ a + 16 ≤ heapEnd ∧ a % 8 = 0) (hr : r < 256)
    (hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48))
    (h8 : ldv .ld M (sp - 48 + 8) = BitVec.ofNat 64 (regAddr r))
    (hw : ldv .ld M (regAddr r) = BitVec.ofNat 64 a)
    (h16 : ldv .ld M (sp - 48 + 16) = w0) (h24 : ldv .ld M (sp - 48 + 24) = w1)
    (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps (1 :: 2 :: setClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      DW live S Q ra R' (datW M a w0 w1)) :
    DW live S Q 0x800030e8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  obtain ⟨ha1, ha2, ha3⟩ := ha
  simp only [heapEnd, heapStart] at hab ha1 ha2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  bc_run hlive hS [h2, h8, hra8, hw, h16, h24, hra]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [LdOK, regAddr, dcRegAddr]; omega) | skip
  all_goals first | (bsimp []; exact hal) | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp []; congr 1; omega)

/-- Register `r`'s word points to its top level's node. -/
theorem DcAt.regWord {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} (h : DcAt S M H F L C G hs st) (hr : r < 256)
    (hl : G.regs r = (b, e) :: l) : ldv .ld M (regAddr r) = BitVec.ofNat 64 b.pay ∧ RLevAt M b e := by
  have hv := h.view.regs r hr
  rw [hl] at hv
  cases hv with
  | cons h0 hp _ => exact ⟨h0, hp⟩

/-- A node of the state lies in the heap, 16-aligned. -/
theorem DcAt.node_bounds {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk} (h : DcAt S M H F L C G hs st)
    (hb : b ∈ G.blocks) (hsz : 32 ≤ b.sz) :
    heapStart + 16 ≤ b.pay ∧ b.pay + 32 ≤ heapEnd ∧ b.pay % 16 = 0 := by
  have fbb := h.heap.heap.blk (List.mem_append_right _ (h.heap.raw.live b hb))
  have a1 : 2147603920 ≤ b.h := fbb.lo
  have a2 : b.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have a3 : b.h % 16 = 0 := fbb.al
  have e1 : b.pay = b.h + 16 := rfl
  have e2 : b.fin = b.h + 16 + b.sz := rfl
  simp only [heapStart, heapEnd]
  omega

/-- The stack bytes of `dc_register_set` and its callees. -/
theorem setFrame_out {sp a : Nat} (hab : heapEnd + 80 ≤ sp) (ha : frameIn sp 80 a) :
    OutHeap a ∧ ¬ DcGlob a := by
  simp only [frameIn] at ha
  exact ⟨outHeap_of_ge (by simp only [heapEnd] at *; omega), fun hg => by
    have := hg.lt; simp only [heapStart, heapEnd] at *; omega⟩

/-- `dc_register_set` on a level holding a number (`0x800030ac`, `sp`
lowered by 48, `a0` the node, `a5` the register's word): `dc_free_num` of
the old value through its slot, then the new datum. -/
theorem reg_set_num {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {v : Val} {w0 w1 ra : BitVec 64} {p sp : Nat}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hev : e.v = some (.num p)) (hd : DatRegs w0 w1 g) (hv : g.Den ⟨L, G.strs⟩ v)
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h10 : R 10 = BitVec.ofNat 64 b.pay)
    (h15 : R 15 = BitVec.ofNat 64 (regAddr r))
    (h16 : ldv .ld M (sp - 48 + 16) = w0) (h24 : ldv .ld M (sp - 48 + 24) = w1)
    (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps (1 :: 2 :: setClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DcAt S M' H' F' L' C' G' hs (regSet st r v) →
      StkOut sp 80 M' M → StrPin G.strs G'.strs hs → G'.lk = G.lk → DW live S Q ra R' M') :
    DW live S Q 0x800030ac#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hbG : b ∈ G.blocks := G.reg_mem hr (by rw [hl]; exact List.mem_cons_self)
  obtain ⟨hw0, hn⟩ := h.regWord hr hl
  have hsz := hn.sz
  obtain ⟨hb1, hb2, hb3⟩ := h.node_bounds hbG hsz
  have hdat := hn.dat
  rw [hev] at hdat
  have hptr : ldv .ld M (b.pay + 8) = BitVec.ofNat 64 p := hdat.ptr
  obtain ⟨h1, hpd⟩ := h.setHead hr hl hd hv
  rw [hev] at h1
  simp only [Option.toList_some, List.singleton_append] at h1
  simp only [heapEnd, heapStart] at hab hb1 hb2
  bc_run hlive hS [h2, h10, h15] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM2 : MemOnly (frameIn sp 80) (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 (regAddr r))]) M :=
    fun x hx => by simp only [frameIn] at hx; rw [imgM_store_miss _ _ (by omega)]
  have h2' := h1.outWriteP hpd hM2 fun x hx => setFrame_out (by simp only [heapEnd]; omega) hx
  refine dc_free_num_specP hlive hpd h2' (q := b.pay + 8)
    ⟨fun i _ => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
      by omega, by omega⟩
    (.win (fun x hx => by simp only [datWin, slotBytes] at hx ⊢; omega)
      (by simp only [heapStart]; omega))
    (by rw [ldv_ld_miss _ _ (by omega)]; exact hptr)
    (StackFrame.sub (m := 48) (n := 32) hsf (by decide)) (by simp only [heapEnd]; omega)
    (Or.inl (by omega)) _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    fun R1 M3 H' F' L' C' hk1 h3 _ hfr _ _ => ?_
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp [h2]
  have hfs : ∀ k, k + 8 ≤ 48 → ldv .ld M3 (sp - 48 + k) =
      ldv .ld (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 (regAddr r))]) (sp - 48 + k) :=
    fun k hk => ldv_congr .ld fun j hj => by
      have hin : frameIn sp 80 (sp - 48 + k + j) := by simp only [frameIn, widthOfM] at hj ⊢; omega
      have ho := setFrame_out (by simp only [heapEnd]; omega) hin
      exact hfr _ ho.1 ho.2 (by simp only [frameIn, widthOfM] at hj ⊢; omega)
        (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
  have hsn : ldv .ld M3 (sp - 48 + 8) = BitVec.ofNat 64 (regAddr r) := by
    rw [hfs 8 (by omega), ldv_store_hit]
  have hs16 : ldv .ld M3 (sp - 48 + 16) = w0 := by
    rw [hfs 16 (by omega), ldv_ld_miss _ _ (by omega), h16]
  have hs24 : ldv .ld M3 (sp - 48 + 24) = w1 := by
    rw [hfs 24 (by omega), ldv_ld_miss _ _ (by omega), h24]
  have hs40 : ldv .ld M3 (sp - 48 + 40) = ra := by
    rw [hfs 40 (by omega), ldv_ld_miss _ _ (by omega), hra]
  have hreg : ldv .ld M3 (regAddr r) = BitVec.ofNat 64 b.pay := by
    have := (h3.regWord hr (show (G.setReg r ((b, e.withV g) :: l)).regs r = (b, e.withV g) :: l by simp [DcG.setReg])).1
    rwa [ldv_ld_miss _ _ (by simp only [regAddr, dc_addrs]; omega),
      ldv_ld_miss _ _ (by simp only [regAddr, dc_addrs]; omega)] at this
  refine reg_set_tailF hlive hS hsf (by simp only [heapEnd]; omega)
    ⟨by simp only [heapStart]; omega, by simp only [heapEnd]; omega, by omega⟩ hr
    (fun x hx => hG x (by have := of_mem_accAddrs hx; simp only [DcGlob, regAddr, dc_addrs] at this ⊢; omega))
    R1 q2 hsn hreg hs16 hs24 hs40 hal fun R' hk2 e1 e2 => ?_
  refine hk R' _ H' F' L' C' _ (hk2.trans (by keeps_tac ((hk1.mono (by decide)).trans
    (by keeps_tac Keeps.refl _ _)))) e1 e2 h3 (fun x ho hg hf => ?_) (StrPin.refl _ _) rfl
  have hnw : x < b.pay ∨ b.pay + 16 ≤ x := by
    have := ho.1; simp only [heapStart, heapEnd] at this; omega
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    hfr x ho hg (by simp only [frameIn] at hf ⊢; omega) (by simp only [slotBytes]; omega)]
  exact hM2 x hf

/-- `dc_register_set` on a level holding a string (`0x800030dc`, `sp`
lowered by 48, `a0` the node, `a5` the register's word): `dc_free_str` of
the old value through its slot, then the new datum. -/
theorem reg_set_str {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {v : Val} {w0 w1 ra : BitVec 64} {p sp : Nat}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hev : e.v = some (.str p)) (hd : DatRegs w0 w1 g) (hv : g.Den ⟨L, G.strs⟩ v)
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h10 : R 10 = BitVec.ofNat 64 b.pay)
    (h15 : R 15 = BitVec.ofNat 64 (regAddr r))
    (h16 : ldv .ld M (sp - 48 + 16) = w0) (h24 : ldv .ld M (sp - 48 + 24) = w1)
    (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps (1 :: 2 :: setClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DcAt S M' H' F' L' C' G' hs (regSet st r v) →
      StkOut sp 80 M' M → StrPin G.strs G'.strs hs → G'.lk = G.lk → DW live S Q ra R' M') :
    DW live S Q 0x800030dc#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hbG : b ∈ G.blocks := G.reg_mem hr (by rw [hl]; exact List.mem_cons_self)
  obtain ⟨hw0, hn⟩ := h.regWord hr hl
  have hsz := hn.sz
  obtain ⟨hb1, hb2, hb3⟩ := h.node_bounds hbG hsz
  have hdat := hn.dat
  rw [hev] at hdat
  have hptr : ldv .ld M (b.pay + 8) = BitVec.ofNat 64 p := hdat.ptr
  obtain ⟨h1, hpd⟩ := h.setHead hr hl hd hv
  rw [hev] at h1
  simp only [Option.toList_some, List.singleton_append] at h1
  simp only [heapEnd, heapStart] at hab hb1 hb2
  bc_run hlive hS [h2, h10, h15] at 0x800039a4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM2 : MemOnly (frameIn sp 80) (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 (regAddr r))]) M :=
    fun x hx => by simp only [frameIn] at hx; rw [imgM_store_miss _ _ (by omega)]
  have h2' := h1.outWriteP hpd hM2 fun x hx => setFrame_out (by simp only [heapEnd]; omega) hx
  refine dc_free_str_specP hlive hpd h2' (q := b.pay + 8)
    ⟨fun i _ => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega), by omega,
      by omega, by omega⟩
    (by rw [ldv_ld_miss _ _ (by omega)]; exact hptr)
    (StackFrame.sub (m := 48) (n := 32) hsf (by decide)) (by simp only [heapEnd]; omega)
    _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    fun R1 M3 H' G' hk1 hsn3 h3 hfr _ _ hpin => ?_
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp [h2]
  have hfs : ∀ k, k + 8 ≤ 48 → ldv .ld M3 (sp - 48 + k) =
      ldv .ld (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 (regAddr r))]) (sp - 48 + k) :=
    fun k hk => ldv_congr .ld fun j hj => by
      have hin : frameIn sp 80 (sp - 48 + k + j) := by simp only [frameIn, widthOfM] at hj ⊢; omega
      have ho := setFrame_out (by simp only [heapEnd]; omega) hin
      exact hfr _ ho.1 ho.2 (by simp only [frameIn, widthOfM] at hj ⊢; omega)
  have hsn : ldv .ld M3 (sp - 48 + 8) = BitVec.ofNat 64 (regAddr r) := by
    rw [hfs 8 (by omega), ldv_store_hit]
  have hs16 : ldv .ld M3 (sp - 48 + 16) = w0 := by
    rw [hfs 16 (by omega), ldv_ld_miss _ _ (by omega), h16]
  have hs24 : ldv .ld M3 (sp - 48 + 24) = w1 := by
    rw [hfs 24 (by omega), ldv_ld_miss _ _ (by omega), h24]
  have hs40 : ldv .ld M3 (sp - 48 + 40) = ra := by
    rw [hfs 40 (by omega), ldv_ld_miss _ _ (by omega), hra]
  have hreg : ldv .ld M3 (regAddr r) = BitVec.ofNat 64 b.pay := by
    have := (h3.regWord hr (show G'.regs r = (b, e.withV g) :: l by
      rw [hsn3.regs]; simp [DcG.setReg])).1
    rwa [ldv_ld_miss _ _ (by simp only [regAddr, dc_addrs]; omega),
      ldv_ld_miss _ _ (by simp only [regAddr, dc_addrs]; omega)] at this
  refine reg_set_tailS hlive hS hsf (by simp only [heapEnd]; omega)
    ⟨by simp only [heapStart]; omega, by simp only [heapEnd]; omega, by omega⟩ hr
    (fun x hx => hG x (by have := of_mem_accAddrs hx; simp only [DcGlob, regAddr, dc_addrs] at this ⊢; omega))
    R1 q2 hsn hreg hs16 hs24 hs40 hal fun R' hk2 e1 e2 => ?_
  refine hk R' _ H' F L C _ (hk2.trans (by keeps_tac ((hk1.mono (by decide)).trans
    (by keeps_tac Keeps.refl _ _)))) e1 e2 h3 (fun x ho hg hf => ?_) hpin hsn3.lk
  have hnw : x < b.pay ∨ b.pay + 16 ≤ x := by
    have := ho.1; simp only [heapStart, heapEnd] at this; omega
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    hfr x ho hg (by simp only [frameIn] at hf ⊢; omega)]
  exact hM2 x hf

theorem regSet_new {st : St} {r : Nat} (hst : st.regs r = []) (v : Val) :
    regSet (st.setReg r [⟨none, []⟩]) r v = regSet st r v := by
  have e1 : (st.setReg r [⟨none, []⟩]).regs r = [⟨none, []⟩] := by simp [St.setReg]
  unfold regSet; rw [e1, hst]
  simp only [St.setReg]
  congr 1; funext q; split <;> rfl

/-- `dc_register_set` on a register without levels (`0x80003070`, `sp`
lowered by 48, `a5` the register's word): a fresh 32-byte node with type `0`
and no array becomes the top level, then the new datum. -/
theorem reg_set_new {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {v : Val}
    {w0 w1 ra : BitVec 64} {sp : Nat}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = [])
    (hd : DatRegs w0 w1 g) (hv : g.Den ⟨L, G.strs⟩ v)
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48))
    (h15 : R 15 = BitVec.ofNat 64 (regAddr r))
    (h16 : ldv .ld M (sp - 48 + 16) = w0) (h24 : ldv .ld M (sp - 48 + 24) = w1)
    (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps (1 :: 2 :: setClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DcAt S M' H' F' L' C' G' hs (regSet st r v) →
      StkOut sp 80 M' M → StrPin G.strs G'.strs hs → G'.lk = G.lk → DW live S Q ra R' M')
    (hoom : StkOom (DW live S Q) 0x80001e74#64 sp 80 (StkOut sp 80 · M)) :
    DW live S Q 0x80003070#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hst : st.regs r = [] := by
    have := h.den.regs r hr; rw [hl] at this
    revert this; generalize st.regs r = m; intro this; cases this; rfl
  simp only [heapEnd, heapStart] at hab
  bc_run hlive hS [h2, h15] at 0x80001ea0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM2 : MemOnly (frameIn sp 80) (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 (regAddr r))]) M :=
    fun x hx => by simp only [frameIn] at hx; rw [imgM_store_miss _ _ (by omega)]
  have h2' := h.outWrite hM2 fun x hx => setFrame_out (by simp only [heapEnd]; omega) hx
  refine dc_malloc_spec hlive h2'.heap.heap (n := 32) (by decide)
    (StackFrame.sub (m := 48) (n := 16) (hsf.shrink (m := 64) (by omega)) (by decide))
    (by simp only [heapEnd]; omega) _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    (fun R1 Mm H' c hk1 hp e10 => ?_) fun R1 Mm e2 hfr =>
      hoom R1 Mm (sp - 48 - 16) (by omega) (by omega) e2 fun x ho hg hf => ?_
  rotate_left
  · rw [hfr x (OutHeap.not_alloc h2'.heap.heap ho) (by simp only [frameIn] at hf ⊢; omega)]
    exact hM2 x hf
  obtain ⟨h3, hf⟩ := h2'.malloc hp (by decide) (by simp only [heapEnd]; omega)
  have hi3 := hp.inv
  have hcsz : 32 ≤ c.sz := hp.size
  have fbb := hi3.blk (List.mem_append_right _ hf.live)
  have hc : 2147603936 ≤ c.pay ∧ c.pay + 32 ≤ 2273312768 ∧ c.pay % 16 = 0 := by
    have a1 : 2147603920 ≤ c.h := fbb.lo
    have a2 : c.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
    have a3 : c.h % 16 = 0 := fbb.al
    have e1 : c.pay = c.h + 16 := rfl
    have e2 : c.fin = c.h + 16 + c.sz := rfl
    omega
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hfm : ∀ k, k + 8 ≤ 48 → ldv .ld Mm (sp - 48 + k) =
      ldv .ld (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 (regAddr r))]) (sp - 48 + k) :=
    fun k hk => ldv_congr .ld fun j hj => hp.frame _
      (OutHeap.not_alloc h2'.heap.heap (outHeap_of_ge (by simp only [heapEnd, widthOfM] at *; omega)))
      (by simp only [frameIn, widthOfM] at hj ⊢; omega)
  have hsn : ldv .ld Mm (sp - 48 + 8) = BitVec.ofNat 64 (regAddr r) := by
    rw [hfm 8 (by omega), ldv_store_hit]
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2]; bsimp [h2]
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  have hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b := fun x hx => hG x (by
    have := of_mem_accAddrs hx; simp only [DcGlob, regAddr, dc_addrs] at this ⊢; omega)
  bsimp []
  bc_run hlive hS [q2, e10, hsn, hra8] at 0x80003090
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [LdOK, StOK, regAddr, dcRegAddr]; omega) | skip
  have hra4 : regAddr r + 8 ≤ c.pay := by simp only [regAddr, dc_addrs]; omega
  have hm4 : MemOnly (fun a => c.In a ∨ RegWord r a) (writeLog (writeLog (writeLog (writeLog Mm
      [(c.pay, 4, 0#64)]) [(c.pay + 16, 8, 0#64)]) [(c.pay + 24, 8, 0#64)])
      [(regAddr r, 8, BitVec.ofNat 64 c.pay)]) Mm := fun x hx => by
    have e1 : c.fin = c.pay + c.sz := rfl
    simp only [Blk.In, RegWord, e1] at hx
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]
  have h4 := h3.newLevel hr hl hf hm4 (ldv_store_hit _ _ _)
    (by rw [ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega),
      ldv_lw_hit _ _ rfl]; decide)
    (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit])
    (by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]) hcsz
  obtain ⟨h5, -⟩ := h4.setHead hr (show (G.setReg r [(c, RLev.empty)]).regs r = [(c, RLev.empty)] by
    simp [DcG.setReg]) hd hv
  rw [regSet_new hst] at h5
  have hfk : ∀ k, k + 8 ≤ 48 → ldv .ld (writeLog (writeLog (writeLog (writeLog Mm
      [(c.pay, 4, 0#64)]) [(c.pay + 16, 8, 0#64)]) [(c.pay + 24, 8, 0#64)])
      [(regAddr r, 8, BitVec.ofNat 64 c.pay)]) (sp - 48 + k) =
      ldv .ld (writeLog M [(sp - 48 + 8, 8, BitVec.ofNat 64 (regAddr r))]) (sp - 48 + k) := fun k hk => by
    rw [ldv_ld_miss _ _ (by simp only [regAddr, dc_addrs]; omega), ldv_ld_miss _ _ (by omega),
      ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), hfm k hk]
  refine reg_set_tailN hlive hS (a := c.pay) hsf (by simp only [heapEnd]; omega)
    ⟨by simp only [heapStart]; omega, by simp only [heapEnd]; omega, by omega⟩ _ (by bsimp [q2])
    (by bsimp [e10]) (by rw [hfk 16 (by omega), ldv_ld_miss _ _ (by omega), h16])
    (by rw [hfk 24 (by omega), ldv_ld_miss _ _ (by omega), h24])
    (by rw [hfk 40 (by omega), ldv_ld_miss _ _ (by omega), hra]) hal fun R' hk2 e1 e2 => ?_
  refine hk R' _ H' F L C _ (hk2.trans (by keeps_tac ((hk1.mono (by decide)).trans
    (by keeps_tac Keeps.refl _ _)))) e1 e2 h5 (fun x ho hg hf => ?_) (StrPin.refl _ _) rfl
  have hx := ho.1
  have hrx : x < regAddr r ∨ regAddr r + 8 ≤ x := Classical.byContradiction fun hc =>
    hg (by simp only [DcGlob, regAddr, dc_addrs] at hc ⊢; omega)
  simp only [heapStart, heapEnd] at hx
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ hrx,
    imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    hp.frame x (OutHeap.not_alloc h2'.heap.heap ho) (by simp only [frameIn] at hf ⊢; omega)]
  exact hM2 x hf

/-- `dc_register_set`'s type dispatch on a level's node (`0x80003000`, `a0`
the node at `a`, type `k` at it). -/
theorem reg_set_disp {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {a : Nat} (k : Nat)
    (ha : heapStart ≤ a ∧ a + 16 ≤ heapEnd ∧ a % 8 = 0) (hk3 : k < 3)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 a) (hlw : ldv .lw M a = BitVec.ofNat 64 k)
    (hk : ∀ R', Keeps [12, 13] R' R →
      DW live S Q (if k = 0 then 0x8000301c#64 else if k = 1 then 0x800030ac#64 else 0x800030dc#64) R' M) :
    DW live S Q 0x80003000#64 R M := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  simp only [heapEnd, heapStart] at ha1 ha2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hc0 : BitVec.ofNat 64 a ≠ 0#64 := fun hc => by
    have := congrArg BitVec.toNat hc
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat] at this
    omega
  bc_run hlive hS [h10, hlw]
  all_goals try (intro hc; exact absurd hc hc0)
  intro _
  have hk' := hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · bc_run hlive hS [h10, hlw] at 0x8000301c
    all_goals try (intro hc; exact absurd hc (by decide))
    all_goals try intro _
    all_goals try (bc_run hlive hS [h10, hlw] at 0x8000301c)
    all_goals try (intro hc; exact absurd hc (by decide))
    all_goals try intro _
    all_goals try (bc_run hlive hS [h10, hlw] at 0x8000301c)
    all_goals try (intro hc; exact absurd hc (by decide))
    all_goals try intro _
    exact hk _ (by keeps_tac Keeps.refl _ _)
  · bc_run hlive hS [h10, hlw] at 0x800030ac
    all_goals try (intro hc; exact absurd hc (by decide))
    all_goals try intro _
    exact hk _ (by keeps_tac Keeps.refl _ _)
  · bc_run hlive hS [h10, hlw] at 0x800030dc
    all_goals try (intro hc; exact absurd hc (by decide))
    all_goals try intro _
    all_goals try (bc_run hlive hS [h10, hlw] at 0x800030dc)
    all_goals try (intro hc; exact absurd hc (by decide))
    all_goals try intro _
    exact hk _ (by keeps_tac Keeps.refl _ _)

/-- `dc_register_set` on a register with levels (`0x80003000`, `sp` lowered
by 48, `a0` the top level's node, `a5` the register's word): the old value,
if any, released, then the new datum. -/
theorem reg_set_lev {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {r : Nat} {b : Blk} {e : RLev}
    {l : List (Blk × RLev)} {v : Val} {w0 w1 ra : BitVec 64} {sp : Nat}
    (h : DcAt S M H F L C G (g :: hs) st) (hr : r < 256) (hl : G.regs r = (b, e) :: l)
    (hd : DatRegs w0 w1 g) (hv : g.Den ⟨L, G.strs⟩ v)
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h10 : R 10 = BitVec.ofNat 64 b.pay)
    (h15 : R 15 = BitVec.ofNat 64 (regAddr r))
    (h16 : ldv .ld M (sp - 48 + 16) = w0) (h24 : ldv .ld M (sp - 48 + 24) = w1)
    (hra : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps (1 :: 2 :: setClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → DcAt S M' H' F' L' C' G' hs (regSet st r v) →
      StkOut sp 80 M' M → StrPin G.strs G'.strs hs → G'.lk = G.lk → DW live S Q ra R' M') :
    DW live S Q 0x80003000#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hbG : b ∈ G.blocks := G.reg_mem hr (by rw [hl]; exact List.mem_cons_self)
  obtain ⟨-, hn⟩ := h.regWord hr hl
  obtain ⟨hb1, hb2, hb3⟩ := h.node_bounds hbG hn.sz
  have hba : heapStart ≤ b.pay ∧ b.pay + 16 ≤ heapEnd ∧ b.pay % 8 = 0 := by
    simp only [heapStart, heapEnd] at *; omega
  have hdat := hn.dat
  revert hdat
  cases hev : e.v with
  | none =>
    intro hdat
    refine reg_set_disp hlive hS 0 hba (by decide) R h10 hdat fun R1 hk1 => ?_
    obtain ⟨h5, -⟩ := h.setHead hr hl hd hv
    rw [hev] at h5
    refine reg_set_tail0 hlive hS (a := b.pay) hsf hab hba R1 (by rw [hk1.get 2]; exact h2)
      (by rw [hk1.get 10]; exact h10) h16 h24 hra hal fun R' hk2 e1 e2 => ?_
    refine hk R' _ H F L C _ (hk2.trans ((hk1.mono (by decide)).trans (Keeps.refl _ _))) e1 e2 h5
      (fun x ho _ _ => ?_) (StrPin.refl _ _) rfl
    have hx := ho.1
    simp only [heapStart, heapEnd] at hx hba
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  | some g0 =>
    intro hdat
    cases g0 with
    | num p =>
      refine reg_set_disp hlive hS 1 hba (by decide) R h10 hdat.lw fun R1 hk1 => ?_
      exact reg_set_num hlive h hr hl hev hd hv hsf hab R1 (by rw [hk1.get 2]; exact h2)
        (by rw [hk1.get 10]; exact h10) (by rw [hk1.get 15]; exact h15) h16 h24 hra hal
        fun R' M' H' F' L' C' G' hk2 => hk R' M' H' F' L' C' G'
          (hk2.trans ((hk1.mono (by decide)).trans (Keeps.refl _ _)))
    | str p =>
      refine reg_set_disp hlive hS 2 hba (by decide) R h10 hdat.lw fun R1 hk1 => ?_
      exact reg_set_str hlive h hr hl hev hd hv hsf hab R1 (by rw [hk1.get 2]; exact h2)
        (by rw [hk1.get 10]; exact h10) (by rw [hk1.get 15]; exact h15) h16 h24 hra hal
        fun R' M' H' F' L' C' G' hk2 => hk R' M' H' F' L' C' G'
          (hk2.trans ((hk1.mono (by decide)).trans (Keeps.refl _ _)))

/-- **`dc_register_set(regid, value)`** at `0x80002fd8`, `r = regid`, the
handle `g` (denoting `v`) in `a1`/`a2`: register `r`'s top value becomes `v`
(`regSet`), the old value released; a new level may run out of memory. -/
theorem dc_register_set_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {g : GV} {hs : List GV} {st : St} {v : Val} {sp r : Nat}
    (h : DcAt S M H F L C G (g :: hs) st) (hv : g.Den ⟨L, G.strs⟩ v) (hr : r < 256)
    (hsf : StackFrame S sp 80) (hab : heapEnd + 80 ≤ sp)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 r) (hd : DatRegs (R 11) (R 12) g)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps setClob R' R → DcAt S M' H' F' L' C' G' hs (regSet st r v) →
      StkOut sp 80 M' M → StrPin G.strs G'.strs hs → G'.lk = G.lk → DW live S Q (R 1) R' M')
    (hoom : StkOom (DW live S Q) 0x80001e74#64 sp 80 (StkOut sp 80 · M)) :
    DW live S Q 0x80002fd8#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have hra8 : (BitVec.ofNat 64 (regAddr r)).toNat = regAddr r := by
    simp only [BitVec.toNat_ofNat, regAddr, dcRegAddr]; omega
  have hrown : ∀ b ∈ accAddrs (regAddr r) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs, regAddr] at this ⊢; omega)
  have hM1 : MemOnly (frameIn sp 80) (writeLog (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 16, 8, R 11)]) [(sp - 48 + 24, 8, R 12)]) M := fun x hx => by
    simp only [frameIn] at hx
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hM1 fun x hx => setFrame_out (by simp only [heapEnd]; omega) hx
  have q16 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 16, 8, R 11)]) [(sp - 48 + 24, 8, R 12)]) (sp - 48 + 16) = R 11 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have q24 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 16, 8, R 11)]) [(sp - 48 + 24, 8, R 12)]) (sp - 48 + 24) = R 12 := ldv_store_hit _ _ _
  have q40 : ldv .ld (writeLog (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 16, 8, R 11)]) [(sp - 48 + 24, 8, R 12)]) (sp - 48 + 40) = R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have hout : ∀ M', StkOut sp 80 M' (writeLog (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 16, 8, R 11)]) [(sp - 48 + 24, 8, R 12)]) → StkOut sp 80 M' M :=
    fun M' hm x ho hg hf => (hm x ho hg hf).trans (hM1 x hf)
  have hv0 := h.view.regs r hr
  have hmem : ∀ b e, (b, e) ∈ G.regs r → b ∈ G.blocks := fun b e hbe => G.reg_mem hr hbe
  generalize hl : G.regs r = l at hv0 hmem
  cases hv0 with
  | nil h0 =>
    bc_run hlive hS [h2, h10, regWord_addr hr, hra8, h0, word_sub48] at 0x80003070
    all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [LdOK, regAddr, dcRegAddr]; omega) | skip
    refine reg_set_new hlive h1 hr hl hd hv hsf (by simp only [heapEnd]; omega) _
      (by bsimp [h2])
      (by bsimp [regWord_addr hr]) (by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit])
      (ldv_store_hit _ _ _)
      (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]) hal (fun R' M' H' F' L' C' G' hk1 e1 e2 h' hfr hpin hlk => ?_)
      fun R' M' sp' e1 e2 e3 hfr => hoom R' M' sp' e1 e2 e3 (hout M' hfr)
    exact hk R' M' H' F' L' C' G' (hk1.restore2 (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2])) h'
      (hout M' hfr) hpin hlk
  | @cons _ b e l' h0 hn hl' =>
    bc_run hlive hS [h2, h10, regWord_addr hr, hra8, h0, word_sub48] at 0x80003000
    all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrown | (simp only [LdOK, regAddr, dcRegAddr]; omega) | skip
    refine reg_set_lev hlive h1 hr hl hd hv hsf (by simp only [heapEnd]; omega) _ (by bsimp [h2])
      (by bsimp []) (by bsimp [regWord_addr hr]) (by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit])
      (ldv_store_hit _ _ _)
      (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_store_hit]) hal
      fun R' M' H' F' L' C' G' hk1 e1 e2 h' hfr hpin hlk => ?_
    exact hk R' M' H' F' L' C' G' (hk1.restore2 (by keeps_tac Keeps.refl _ _) e1 (by rw [e2, h2])) h'
      (hout M' hfr) hpin hlk
end Dc.Mach
