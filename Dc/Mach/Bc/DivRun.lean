import Dc.Mach.Bc.DivTail
import Dc.BcModel.DivValue

/-!
# `bc_divide` from the loop head to its return

- `DvShape.pre_lt`: the prefix entering iteration `k` is below `V · 10^k`.
- `DvExit.value`: the quotient array at the loop's exit is `pre (Kb+1) / V`.
- `dv_run`: from `DvAt` at the first iteration through the loop
  (`dv_loop`), the exit (`dvt_exit`), the tail, to `DivKW.ret`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

/-- The prefix entering iteration `k` is below `V · 10^k`. -/
theorem DvShape.pre_lt {D : DvData} (hs : DvShape D) :
    ∀ k, k ≤ D.Kb + 1 → D.pre k < D.V * 10 ^ k
  | 0, _ => by rw [Nat.pow_zero, Nat.mul_one]; exact hs.first
  | k + 1, hk => by
    have ih := hs.pre_lt k (by omega)
    have hx : D.xs.getD (k + D.L) 0 < 10 := hs.xd.getD _
    rw [hs.pre_succ (by omega), Nat.pow_succ, ← Nat.mul_assoc]
    generalize D.V * 10 ^ k = Y at ih ⊢
    omega

/-- **The quotient's value** at the loop's exit. -/
theorem DvExit.value {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {D : DvData} {H : Heap} {F : List Blk} {Lh : List NumObj} {y : NumObj} {ds : List Nat}
    (hs : DvShape D) (ex : DvExit S Mt0 M R0 R sp W D H F Lh y ds) :
    dval ds = D.pre (D.Kb + 1) / D.V := by
  have fx := ex.fix
  refine quot_digits_val (off := D.off) (K := D.Kb) (by rw [fx.qlen, ← fx.qend]) fx.qdig fx.qzero
    (fun j hj => by rw [ex.win.quot j hj]; congr 3) ?_
  exact (Nat.div_lt_iff_lt_mul hs.vpos).mpr (by rw [Nat.mul_comm]; exact hs.pre_lt _ (Nat.le_refl _))

/-- **`bc_divide` from the loop head**: the loop, the exit, the sign, the
trim, the frees and the epilogue. -/
theorem dv_run {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat} {L1 L2 : List NumObj}
    {xr y x1 x2 z : NumObj} {H : Heap} {F : List Blk} {n : Option Num} {m : Num}
    {D : DvData} {ds : List Nat}
    (cx : DivCtx S R0 sp q W) (hk : DivKW live S Q R0 Mt0 L1 L2 xr q sp W n) (hn : n = some m)
    (hs : DvShape D) (st : DvAt S Mt0 M R0 R sp W D H F (L1 ++ xr :: L2) y ds 0)
    (hr0 : ResSlot Mt0 L1 xr q) (hqv : D.qv = y.sb.pay) (hn1 : D.n1p = x1.rep.p)
    (hn2 : D.n2p = x2.rep.p) (hrs : D.rs = q)
    (hx1 : x1 ∈ L1 ++ xr :: L2) (hx2 : x2 ∈ L1 ++ xr :: L2) (hz : z ∈ L1 ++ xr :: L2)
    (hzg : ldv .ld Mt0 zeroAddr = BitVec.ofNat 64 z.rep.p)
    (hm : m = ⟨if D.pre (D.Kb + 1) / D.V = 0 then false else x1.rep.neg != x2.rep.neg,
      D.pre (D.Kb + 1) / D.V, y.rep.scale⟩)
    (hpos : 1 ≤ y.rep.len) (hrefs : y.rep.refs = 1) :
    DW live S Q 0x80005d4c#64 R M := by
  have hab := cx.above; have hW := cx.big
  have hsl := cx.frame.lo
  refine dv_loop hlive cx.dv hs (fun R' M' ds' ex => ?_) _ 0 R M ds rfl st
  have hv := ex.value hs
  refine dvt_exit hlive cx hk hn ex hr0 hqv hn1 hn2 hrs hx1 hx2 hz ?_ (fun h0 => ?_) (fun h0 => ?_)
    hpos hrefs
  · rw [ldv_congr .ld fun j hj => ex.fix.out _ (constBytes_out (by
        simp only [constBytes, twoAddr, zeroAddr, widthOfM] at hj ⊢; omega))
      (by simp only [frameIn, zeroAddr, heapEnd, widthOfM] at hj hab ⊢; omega)]
    exact hzg
  · rw [hm]
    show (⟨_, dval ds', _⟩ : Dc.Num) = _
    rw [hv] at h0 ⊢
    simp only [h0, if_false]
  · rw [hm]
    show (⟨_, dval ds', _⟩ : Dc.Num) = _
    rw [hv] at h0 ⊢
    simp only [h0, if_true]

end Dc.Mach
