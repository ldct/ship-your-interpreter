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
  win x hx := ⟨b, List.mem_singleton_self _, by simp only [datWin, Blk.In, Blk.pay, Blk.fin] at hx ⊢; omega⟩
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

theorem DcG.newLevel_perm {G : DcG} {r : Nat} (hr : r < 256) (hl : G.regs r = []) (c : Blk) :
    (G.setReg r [(c, RLev.empty)]).blocks.Perm (c :: G.blocks) := by
  obtain ⟨P, Q, -, hf, hf'⟩ := flatMap_range_upd (f := fun r' => (G.regs r').flatMap RLev.blocks)
    (g := fun r' => ((G.setReg r [(c, RLev.empty)]).regs r').flatMap RLev.blocks) hr
    fun r' hne => by simp [DcG.setReg, hne]
  have e1 : (G.setReg r [(c, RLev.empty)]).blocks = G.stk.map (·.1) ++ (List.range 256).flatMap
      (fun r' => ((G.setReg r [(c, RLev.empty)]).regs r').flatMap RLev.blocks) ++
      G.strs.flatMap (fun o => [o.hb, o.tb]) ++ G.lbuf.toList := rfl
  have e2 : G.blocks = G.stk.map (·.1) ++ (List.range 256).flatMap
      (fun r' => (G.regs r').flatMap RLev.blocks) ++
      G.strs.flatMap (fun o => [o.hb, o.tb]) ++ G.lbuf.toList := rfl
  rw [List.perm_iff_count]
  intro y
  rw [e1, e2, hf, hf']
  simp only [DcG.setReg, ite_true, hl, List.flatMap_cons, List.flatMap_nil, RLev.blocks,
    List.count_append, List.count_cons, List.map_nil, List.count_nil, List.append_nil]
  omega

theorem DcG.newLevel_vals {G : DcG} {r : Nat} (hl : G.regs r = []) (c : Blk) :
    (G.setReg r [(c, RLev.empty)]).vals = G.vals := by
  have hf : (fun r' => ((G.setReg r [(c, RLev.empty)]).regs r').flatMap RLev.vals) =
      fun r' => (G.regs r').flatMap RLev.vals := by
    funext r'
    simp only [DcG.setReg]
    split
    · subst_vars; rw [hl]; simp [RLev.vals]
    · rfl
  show G.stk.map (·.2) ++ (List.range 256).flatMap
      (fun r' => ((G.setReg r [(c, RLev.empty)]).regs r').flatMap RLev.vals) = G.vals
  rw [hf]; rfl

/-- The bytes of register `r`'s word. -/
abbrev RegWord (r a : Nat) : Prop := regAddr r ≤ a ∧ a < regAddr r + 8

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
  have hi := h.heap.heap
  have hperm := DcG.newLevel_perm hr hl c
  have hcin := live_in_heap hi hf.live (show c.In c.pay by simp only [Blk.In, Blk.pay, Blk.fin]; omega)
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
  have hst : st.regs r = [] := by
    have := hd.regs r hr; rw [hl] at this
    revert this; generalize st.regs r = m; intro this; cases this; rfl
  have hv := h.den
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
  · have e1 : (G.setReg r [(c, RLev.empty)]).regs r' = if r' = r then [(c, RLev.empty)] else G.regs r' :=
      rfl
    rw [e1]
    split
    · subst_vars
      exact .cons hw ⟨h0, .nil h16, hsz⟩ (.nil h24)
    · exact regChain_frame (h.view.regs r' hr') (ldv_congr .ld fun j hj => hglob _ (by
        simp only [widthOfM, DcGlob, regAddr, dc_addrs] at hj ⊢; omega) (by
        simp only [widthOfM, RegWord, regAddr, dc_addrs] at hj ⊢; omega))
        fun be hmm c' hc' x hx => hGoff c' (G.lev_mem hr' hmm hc') x hx
  · have hvals := DcG.newLevel_vals hl c
    refine { hd with
      regs := fun r' hr' => ?_
      regsHi := fun r' hr' => ?_
      numRefs := fun x hx => by rw [hvals]; exact hd.numRefs x hx
      strRefs := fun o ho => by rw [hvals]; exact hd.strRefs o ho }
    · simp only [DcG.setReg, St.setReg]
      split
      · exact .cons ⟨.none, .nil⟩ .nil
      · exact hd.regs r' hr'
    · have hne : r' ≠ r := by omega
      simp only [DcG.setReg, St.setReg, hne, ite_false]; exact hd.regsHi r' hr'

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
      StkOut sp 80 M' M → DW live S Q ra R' M') :
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
    (.inl fun x hx => by simp only [datWin, slotBytes] at hx ⊢; omega)
    (by rw [ldv_ld_miss _ _ (by omega)]; exact hptr)
    (StackFrame.sub (m := 48) (n := 32) hsf (by decide)) (by simp only [heapEnd]; omega)
    (Or.inl (by omega)) _ (by bsimp []) (by bsimp [h2]) (by bsimp [])
    fun R1 M3 H' F' L' C' hk1 h3 _ hfr => ?_
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
    (by keeps_tac Keeps.refl _ _)))) e1 e2 h3 fun x ho hg hf => ?_
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
      StkOut sp 80 M' M → DW live S Q ra R' M') :
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
    fun R1 M3 H' G' hk1 hsn3 h3 hfr => ?_
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
    (by keeps_tac Keeps.refl _ _)))) e1 e2 h3 fun x ho hg hf => ?_
  have hnw : x < b.pay ∨ b.pay + 16 ≤ x := by
    have := ho.1; simp only [heapStart, heapEnd] at this; omega
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    hfr x ho hg (by simp only [frameIn] at hf ⊢; omega)]
  exact hM2 x hf

end Dc.Mach
