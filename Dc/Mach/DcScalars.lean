import Dc.Mach.StateOps

/-!
# Stores to dc's scalar globals (M10)

`dc_func`'s `i`, `o`, `k`, `q` and `Q` store `dc_ibase`, `dc_obase`,
`dc_scale`, `unwind_depth` and `unwind_noexit`. `DcAt.setScalars`: memory
changed only in those words (`ScalarWord`) holds the state with the
scalars the words now read.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- The bytes of `dc_ibase`, `dc_obase`, `dc_scale`, `unwind_depth` and
`unwind_noexit`. -/
def ScalarWord (a : Nat) : Prop :=
  (ibaseAddr ≤ a ∧ a < ibaseAddr + 4) ∨ (obaseAddr ≤ a ∧ a < obaseAddr + 4) ∨
    (scaleAddr ≤ a ∧ a < scaleAddr + 4) ∨ (unwindAddr ≤ a ∧ a < unwindAddr + 4) ∨
    (noexitAddr ≤ a ∧ a < noexitAddr + 4)

theorem ScalarWord.glob {a : Nat} (h : ScalarWord a) : DcGlob a := by
  simp only [ScalarWord, DcGlob, dc_addrs] at h ⊢; omega

/-- **The scalar globals stored**: memory changed only in their words holds
the state with the values the words now read. -/
theorem DcAt.setScalars {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    (hm : MemOnly ScalarWord M' M) {i o k u : Nat} {n : Bool}
    (hi : ldv .lw M' ibaseAddr = BitVec.ofNat 64 i) (ho : ldv .lw M' obaseAddr = BitVec.ofNat 64 o)
    (hk : ldv .lw M' scaleAddr = BitVec.ofNat 64 k) (hu : ldv .lw M' unwindAddr = BitVec.ofNat 64 u)
    (hn : ldv .lw M' noexitAddr = boolWord n)
    (hir : 2 ≤ i ∧ i ≤ 16) (hor : 2 ≤ o ∧ o < 2 ^ 31) (hkr : k < 2 ^ 31) (hur : u < 2 ^ 31) :
    DcAt S M' H F L C G hs { st with ibase := i, obase := o, scale := k, unwind := u, noexit := n } := by
  have hb1 := h.heap.out_frame hm fun a ha => ha.glob.outHeap
  have hblk : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a := fun a ha =>
    hm a fun hp => hp.glob.outHeap.1 (h.inBlocks_heap ha).1
  have hg : ∀ a, DcGlob a → ¬ ScalarWord a → imgM M' a = imgM M a := fun a _ hw => hm a hw
  have gw : ∀ (k : MKind) a, (∀ j, j < widthOfM k → DcGlob (a + j) ∧ ¬ ScalarWord (a + j)) →
      ldv k M' a = ldv k M a := fun k a ha =>
    ldv_congr k fun j hj => hg _ (ha j hj).1 (ha j hj).2
  have v := h.view
  have d := h.den
  refine
    { heap := hb1.subRaw (fun c hc => hc) fun c hc a ha => (hblk a ⟨c, hc, ha⟩).symm
      nodup := h.nodup
      view :=
        { stk := stkChain_frame v.stk
            (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, ScalarWord, dc_addrs] at hj ⊢; omega)
            fun bg hm' x hx => hblk x ⟨bg.1, G.stk_mem hm', hx⟩
          regs := fun r hr => regChain_frame (v.regs r hr)
            (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, ScalarWord, regAddr, dc_addrs] at hj ⊢; omega)
            fun be hm' c hc x hx => hblk x ⟨c, by
              rcases List.mem_cons.mp hc with rfl | hc
              · exact G.reg_mem hr hm'
              · obtain ⟨bn, hn', rfl⟩ := List.mem_map.mp hc
                exact G.arr_mem hr hm' hn', hx⟩
          strs := fun o ho => (v.strs o ho).frame (bs := G.blocks) (G.str_mem ho).1 (G.str_mem ho).2 hblk
          zw := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, ScalarWord, dc_addrs] at hj ⊢; omega).trans v.zw
          ow := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, ScalarWord, dc_addrs] at hj ⊢; omega).trans v.ow
          tw := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, ScalarWord, dc_addrs] at hj ⊢; omega).trans v.tw
          ibase := hi
          obase := ho
          scale := hk
          unwind := hu
          noexit := hn
          lineMax := by
            rw [gw .lw _ fun j hj => by simp only [widthOfM, DcGlob, ScalarWord, dc_addrs] at hj ⊢; omega]
            exact v.lineMax
          lbuf := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, ScalarWord, dc_addrs] at hj ⊢; omega).trans v.lbuf
          lbufLen := fun b e => (gw .ld _ fun j hj => by
            simp only [widthOfM, DcGlob, ScalarWord, dc_addrs] at hj ⊢; omega).trans (v.lbufLen b e)
          outFd := (gw .lw _ fun j hj => by simp only [widthOfM, DcGlob, ScalarWord, dc_addrs] at hj ⊢; omega).trans v.outFd
          errFd := (gw .lw _ fun j hj => by simp only [widthOfM, DcGlob, ScalarWord, dc_addrs] at hj ⊢; omega).trans v.errFd
          prog := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, ScalarWord, dc_addrs] at hj ⊢; omega).trans v.prog }
      den := { d with ibase := hir, obase := hor, scale := hkr, unwind := hur }
      glob := h.glob
      col := h.col }

end Dc.Mach
