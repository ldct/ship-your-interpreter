import Dc.Mach.DcDiv
import Dc.Mach.Bc.RaiseEntry
import Dc.Mach.Bc.SqrtInit

/-!
# dc's exponentiation (M9)

    dc_exp (a, b, kscale, result):
      bc_init_num (result); bc_raise (a, b, result, kscale); return DC_SUCCESS;

`bc_raise` leaves in the slot a new number, the base or `_one_` with one
more reference, or the old number (`RaPost`):

- `DcDen.swap`: two handles exchanged.
- `BcConsts.SameP`: constants at the same addresses (`DcView.sameP`).
- `DcDen.raPost`, `DcAt.raNum`: the slot's handle after `bc_raise`.
- `dc_exp_spec`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **Two handles exchanged.** -/
theorem DcDen.swap {L : List NumObj} {C : BcConsts} {G : DcG} {a b : GV} {hs : List GV} {st : St}
    (d : DcDen L C G (a :: b :: hs) st) : DcDen L C G (b :: a :: hs) st :=
  { d with
    hsDen := fun g hg => d.hsDen g (by
      simp only [List.mem_cons] at hg ⊢; rcases hg with h | h | h <;> simp [h])
    numRefs := fun x hx => by
      rw [d.numRefs x hx]; simp only [List.count_append, List.count_cons]; omega
    strRefs := fun o ho => by
      rw [d.strRefs o ho]; simp only [List.count_append, List.count_cons]; omega }

/-- Constants at the same addresses. -/
structure BcConsts.SameP (C C' : BcConsts) : Prop where
  z : C'.z.rep.p = C.z.rep.p
  o : C'.o.rep.p = C.o.rep.p
  t : C'.t.rep.p = C.t.rep.p

theorem BcConsts.SameP.refl (C : BcConsts) : C.SameP C := ⟨rfl, rfl, rfl⟩

theorem BcConsts.SameP.trans {C1 C2 C3 : BcConsts} (h1 : C1.SameP C2) (h2 : C2.SameP C3) :
    C1.SameP C3 := ⟨h2.z.trans h1.z, h2.o.trans h1.o, h2.t.trans h1.t⟩

theorem BcConsts.sameP_subst (C : BcConsts) {x x' : NumObj} (hp : x'.rep.p = x.rep.p)
    (hn : x'.rep.num = x.rep.num) : C.SameP (C.subst x x') := by
  classical
  exact ⟨(ite_rep hp hn _ _).1, (ite_rep hp hn _ _).1, (ite_rep hp hn _ _).1⟩

/-- The constants' words read the same for constants at the same addresses. -/
theorem DcView.sameP {M : Mem} {G : DcG} {C C' : BcConsts} {st : St} (v : DcView M G C st)
    (h : C.SameP C') : DcView M G C' st :=
  { v with zw := by rw [h.z]; exact v.zw, ow := by rw [h.o]; exact v.ow, tw := by rw [h.t]; exact v.tw }

/-- A handle's number has a reference. -/
theorem DcDen.refs_pos {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {x : NumObj} (d : DcDen L C G (.num x.rep.p :: hs) st) (hx : x ∈ L) : 1 ≤ x.rep.refs := by
  rw [d.numRefs x hx, count_cons_self]; omega

/-- **The slot's handle after `bc_raise`** on the ghost side: one reference
added to `y` (fresh, or a number of the heap), then the slot's old number
`xr` dropped; the handle `.num y.p` replaces `.num xr.p`. -/
theorem DcDen.raPost {L Lm Lf : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {xr y : NumObj} (d : DcDen L C G (.num xr.rep.p :: hs) st) (hd : PDist L) (hxr : xr ∈ L)
    (hadd : AddRef L y Lm) (hdrop : DropAt Lm xr.rep.p Lf) (hdf : PDist Lf)
    (hno : y.rep.Norm) (hpos : 1 ≤ y.rep.len) (how : y.Owns) :
    ∃ C', DcDen Lf C' G (.num y.rep.p :: hs) st ∧ C.SameP C' := by
  cases hadd with
  | fresh hy1 =>
    rcases DropAt.cons_cases hdrop with ⟨hyp, hfr⟩ | ⟨L'', hd', e⟩
    · cases hfr with
      | dec h2 => omega
      | rel _ => exact ⟨C, by rw [hyp]; exact d, .refl C⟩
    · subst e
      obtain ⟨L1, L2, x, rfl, hxp, hfr⟩ := hd'
      have hx : x = xr := hd.eq (List.mem_append_right _ List.mem_cons_self) hxr hxp
      subst hx
      have hdf' : PDist ([] ++ y :: L'') := hdf
      cases hfr with
      | dec _ =>
        exact ⟨_, (d.dec hd.ne).addNum (fun z hz => hdf'.ne z hz) hy1 hno hpos how,
          C.sameP_subst rfl rfl⟩
      | rel h1 =>
        exact ⟨C, (d.rel hd.ne h1).addNum (fun z hz => hdf'.ne z hz) hy1 hno hpos how, .refl C⟩
  | @share A B c =>
    have hdm : PDist (A ++ c.withRefs (c.rep.refs + 1) :: B) :=
      hd.congr (by simp only [List.map_append, List.map_cons]; rfl)
    by_cases hcx : c.rep.p = xr.rep.p
    · have hc : c = xr := hd.eq (List.mem_append_right _ List.mem_cons_self) hxr hcx
      subst hc
      have hr1 := d.refs_pos hxr
      have hfr := DropAt.unique hdm hdrop
      cases hfr with
      | rel h => simp only [NumObj.withRefs_refs] at h; omega
      | dec _ =>
        refine ⟨C, ?_, .refl C⟩
        rw [NumObj.decRef_eq, NumObj.withRefs_withRefs, NumObj.withRefs_refs,
          show c.rep.refs + 1 - 1 = c.rep.refs by omega, NumObj.withRefs_self]
        exact d
    · have d1 := (d.bump hd.ne).swap
      obtain ⟨L1, L2, x, e, hxp, hfr⟩ := hdrop
      rw [e] at d1 hdm
      rw [← hxp] at d1
      cases hfr with
      | dec _ =>
        exact ⟨_, d1.dec hdm.ne, (C.sameP_subst (x := c) (x' := c.withRefs (c.rep.refs + 1)) rfl rfl).trans
          (BcConsts.sameP_subst _ (x := x) (x' := x.decRef) rfl rfl)⟩
      | rel h1 => exact ⟨_, d1.rel hdm.ne h1, C.sameP_subst rfl rfl⟩

/-- **The slot's handle after `bc_raise`**: the state holds `.num y.p`
instead of `.num xr.p`. -/
theorem DcAt.raNum {S : Nat → Prop} {M Mt : Mem} {H H' : Heap} {F F' : List Blk} {L Lf : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {xr y : NumObj} {ps : List Nat} {q sp W : Nat}
    {n : Num} (h : DcAt S M H F L C G (.num xr.rep.p :: hs) st) (hxr : xr ∈ L)
    (hp : RaPost S (G.raws M) M Mt H' F' L xr ps q sp W n Lf y)
    (hgl : ∀ a, DcGlob a → imgM Mt a = imgM M a) :
    ∃ C', DcAt S Mt H' F' Lf C' G (.num y.rep.p :: hs) st := by
  obtain ⟨Lm, hadd, hdrop⟩ := hp.mid
  obtain ⟨C', d', hsp⟩ := h.den.raPost h.heap.pdist hxr hadd hdrop hp.heap.pdist hp.norm hp.pos
    hp.owns
  have hag : ∀ a, InBlocks G.blocks a → imgM Mt a = imgM M a := fun a ⟨c, hc, ha⟩ =>
    hp.heap.raw.img c hc a ha
  exact ⟨C', hp.heap.subRaw (fun c hc => hc) (fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm), h.nodup,
    (h.view.frame hag hgl).sameP hsp, d', h.glob, h.col⟩

end Dc.Mach
