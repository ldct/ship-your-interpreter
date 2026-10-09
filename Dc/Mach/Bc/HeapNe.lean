import Dc.Mach.Bc.Heap

/-!
# Distinct structs on the number heap

`BcHeap.p_ne`: two objects of a `BcHeap` have different struct payloads (a
fresh result is never `_zero_` or an operand).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- A struct of the heap is not `_zero_`'s: their payloads differ. -/
theorem BcHeap.p_ne {S : Nat → Prop} {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {x z : NumObj} (h : BcHeap S Mt H F (x :: L)) (hz : z ∈ L) :
    x.rep.p ≠ z.rep.p := by
  have hx := h.blocks x List.mem_cons_self
  have hzb := h.blocks z (List.mem_cons_of_mem _ hz)
  have hd := h.distinct
  rw [List.nodup_append] at hd
  have hne : x.sb ≠ z.sb := by
    intro e
    have hd2 : (x.blocks ++ objBlocks L).Nodup := hd.2.1
    exact (List.nodup_append.mp hd2).2.2 x.sb x.sb_mem_blocks z.sb (mem_objBlocks hz) e
  intro e
  have hsx := hx.sSz; have hsz := hzb.sSz
  rw [hx.sPay, hzb.sPay] at e
  exact live_apart h.heap hx.sLive hzb.sLive hne (a := x.sb.pay)
    ⟨Nat.le_refl _, by simp only [Blk.fin, Blk.pay] at hsx ⊢; omega⟩
    ⟨by omega, by simp only [Blk.fin, Blk.pay] at hsx hsz e ⊢; omega⟩

end Dc.Mach
