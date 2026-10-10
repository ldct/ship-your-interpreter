import Dc.Mach.DcTriop
import Dc.Mach.DcDivrem
import Dc.Mach.Bc.RaiseModEntry

/-!
# dc's modular exponentiation (M9)

    dc_modexp (base, expo, mod, kscale, result):
      bc_init_num (result);
      if (bc_raisemod (base, expo, mod, result, kscale)) {
        if (bc_is_zero (mod)) fprintf (stderr, "%s: remainder by zero\n", progname);
        return DC_DOMAIN_ERROR;
      }
      return DC_SUCCESS;

`bc_raisemod` leaks `parity` (`RxMid`): its reference goes on `DcG.lk`.
On failure the slot's `_zero_` reference is lost.

- `AddRef.pdist_of`, `AddRef.mem_p`, `DropAt.mem_src`: list facts.
- `DcDen.addRef`: one reference added as a new handle.
- `DcDen.rxPost`, `DcAt.rxNum`: the slot's handle after `bc_raisemod`.
- `OpRet3.of_rxPost`, `OpFail3.of_leak`.
- `DcDen.refs_pos_mem`, `DcAt.rxArgs`: `bc_raisemod`'s operands from the state.
- `mx_init`, `mx_out`, `mx_fail`, `mx_ret`: the spans; `dc_modexp_spec`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-! ## The ghost moves -/

/-- The heap before one more reference has its numbers apart. -/
theorem AddRef.pdist_of {L Lw : List NumObj} {w : NumObj} (h : AddRef L w Lw) (hd : PDist Lw) :
    PDist L := by
  cases h with
  | fresh _ => exact hd.sublist (List.sublist_cons_self _ _)
  | share => exact hd.congr (by simp only [List.map_append, List.map_cons]; rfl)

/-- A number before one more reference is still there, at its address. -/
theorem AddRef.mem_p {L Lw : List NumObj} {w x : NumObj} (h : AddRef L w Lw) (hx : x ∈ L) :
    ∃ x' ∈ Lw, x'.rep.p = x.rep.p := by
  cases h with
  | fresh _ => exact ⟨x, List.mem_cons_of_mem _ hx, rfl⟩
  | @share A B c =>
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with h | rfl | h
    · exact ⟨x, by simp [h], rfl⟩
    · exact ⟨x.withRefs (x.rep.refs + 1), by simp, rfl⟩
    · exact ⟨x, by simp [h], rfl⟩

/-- The number given one more reference is in the heap. -/
theorem AddRef.mem {L Lw : List NumObj} {w : NumObj} (h : AddRef L w Lw) : w ∈ Lw := by
  cases h with
  | fresh _ => exact List.mem_cons_self
  | share => simp

/-- A number left by a drop was in the heap before, at its address with its value. -/
theorem DropAt.mem_src {Lm Lf : List NumObj} {p : Nat} (h : DropAt Lm p Lf) {x : NumObj}
    (hx : x ∈ Lf) : ∃ z ∈ Lm, z.rep.p = x.rep.p ∧ z.rep.num = x.rep.num := by
  obtain ⟨L1, L2, z0, rfl, -, hf⟩ := h
  cases hf with
  | dec _ =>
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with h | rfl | h
    · exact ⟨x, by simp [h], rfl, rfl⟩
    · exact ⟨z0, by simp, rfl, rfl⟩
    · exact ⟨x, by simp [h], rfl, rfl⟩
  | rel _ =>
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · exact ⟨x, by simp [h], rfl, rfl⟩
    · exact ⟨x, by simp [h], rfl, rfl⟩

/-- **One reference added** (`AddRef`) on the ghost side, as a new handle. -/
theorem DcDen.addRef {L Lw : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {w : NumObj} (d : DcDen L C G hs st) (hd : PDist L) (hadd : AddRef L w Lw) (hdw : PDist Lw)
    (hno : w.rep.Norm) (hpos : 1 ≤ w.rep.len) (how : w.Owns) :
    ∃ C', DcDen Lw C' G (.num w.rep.p :: hs) st ∧ C.SameP C' := by
  cases hadd with
  | fresh h1 =>
    have hd' : PDist ([] ++ w :: L) := hdw
    exact ⟨C, d.addNum (fun z hz => hd'.ne z hz) h1 hno hpos how, .refl C⟩
  | share => exact ⟨_, d.bump hd.ne, C.sameP_subst rfl rfl⟩

/-- **The slot's handle after `bc_raisemod`** on the ghost side: `parity`'s
reference lost, the result's handle `.num y.p` for the slot's `.num xr.p`. -/
theorem DcDen.rxPost {L Lw Lm Lf : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {xr w y : NumObj} (d : DcDen L C G (.num xr.rep.p :: hs) st) (hxr : xr ∈ L)
    (hm : RxMid L w Lw y Lm xr.rep.p Lf) (hdf : PDist Lf) (hno : y.rep.Norm)
    (hpos : 1 ≤ y.rep.len) (how : y.Owns) (hl : G.lk.length < 2 ^ 29) :
    ∃ C', DcDen Lf C' { G with lk := w.rep.p :: G.lk } (.num y.rep.p :: hs) st ∧ C.SameP C' := by
  have hdw := hm.addY.pdist_of hm.pdist
  have hdl := hm.addW.pdist_of hdw
  obtain ⟨C1, d1, s1⟩ := d.addRef hdl hm.addW hdw hm.normW hm.posW hm.ownsW
  have d2 := d1.leak hl
  obtain ⟨xr', hx', ep⟩ := hm.addW.mem_p hxr
  have d2' : DcDen Lw C1 { G with lk := w.rep.p :: G.lk } (.num xr'.rep.p :: hs) st := by
    rw [ep]; exact d2
  have hdrop : DropAt Lm xr'.rep.p Lf := by rw [ep]; exact hm.drop
  obtain ⟨C2, d3, s2⟩ := d2'.raPost hdw hx' hm.addY hdrop hdf hno hpos how
  exact ⟨C2, d3, s1.trans s2⟩

/-- **The slot's handle after `bc_raisemod`**: the state holds `.num y.p`
instead of `.num xr.p`, `parity`'s reference lost; the heap holds `y`'s value
at `y.p`. -/
theorem DcAt.rxNum {S : Nat → Prop} {M Mt : Mem} {H H' : Heap} {F F' : List Blk}
    {L Lf : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {xr y : NumObj}
    {q sp W : Nat} {n : Num} (h : DcAt S M H F L C G (.num xr.rep.p :: hs) st) (hxr : xr ∈ L)
    (hp : RxPost S (G.raws M) M Mt H' F' L xr q sp W n Lf y)
    (hgl : ∀ a, DcGlob a → imgM Mt a = imgM M a) (hl : G.lk.length < 2 ^ 29) :
    ∃ C' pw, DcAt S Mt H' F' Lf C' { G with lk := pw :: G.lk } (.num y.rep.p :: hs) st ∧
      ∃ y' ∈ Lf, y'.rep.p = y.rep.p ∧ y'.rep.num = y.rep.num := by
  obtain ⟨w, Lw, Lm, hm⟩ := hp.mid
  obtain ⟨C', d', hsp⟩ := h.den.rxPost hxr hm hp.heap.pdist hp.norm hp.pos hp.owns hl
  have hag : ∀ a, InBlocks G.blocks a → imgM Mt a = imgM M a := fun a ⟨c, hc, ha⟩ =>
    hp.heap.raw.img c hc a ha
  refine ⟨C', w.rep.p, ⟨hp.heap.subRaw (fun c hc => hc) (fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm),
    h.nodup, { (h.view.frame hag hgl).sameP hsp with }, d', h.glob, h.col⟩, ?_⟩
  obtain ⟨v, hv⟩ := d'.hsDen _ List.mem_cons_self
  cases v with
  | str s => exact hv.elim
  | num nv =>
    obtain ⟨x, hx, ex, -⟩ := hv
    obtain ⟨z, hz, ezp, ezn⟩ := hm.drop.mem_src hx
    have hzy : z = y := hm.pdist.eq hz hm.addY.mem (ezp.trans ex)
    subst hzy
    exact ⟨x, hx, ex, ezn.symm⟩

/-- **A three-operand operation's success from `bc_raisemod`'s result** `y`
in the slot (window `W` below `sp'`, inside the operation's `N` below `sp`),
`parity`'s reference lost. -/
theorem OpRet3.of_rxPost {S : Nat → Prop} {M M2 Mt : Mem} {H H3 : Heap} {F F3 : List Blk}
    {L Lf : List NumObj} {x y : NumObj} {C2 : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb pc : Nat} {na nb nc n : Num} {f : Nat → Num → Num → Num → Option Num}
    {sp q N sp' W lk : Nat}
    (hd2 : DcAt S M2 H F L C2 G (.num x.rep.p :: .num pa :: .num pb :: .num pc :: hs) st)
    (hx : x ∈ L) (hp : RxPost S (G.raws M2) M2 Mt H3 F3 L x q sp' W n Lf y)
    (hval : f st.scale na nb nc = some n) (hw1 : sp' ≤ sp) (hw2 : sp - N ≤ sp' - W)
    (hab : heapEnd ≤ sp' - W) (hq : sp ≤ q) (hl : G.lk.length < 2 ^ 29) (hlk : 1 ≤ lk)
    (hout0 : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp N a → imgM M2 a = imgM M a) :
    ∃ C3 G3, ∀ R' : Nat → BitVec 64, R' 10 = 0#64 →
      OpRet3 S M Mt H3 F3 Lf C3 G G3 hs st pa pb pc na nb nc f R' sp q N lk y.rep.p n := by
  simp only [heapEnd] at hab
  obtain ⟨C3, pw, hd3, y', hy', ep, en⟩ := hd2.rxNum hx hp (fun a ha =>
    hp.out a ha.outHeap (fun hs => by have := ha.lt; simp only [heapStart, slotBytes] at this hs; omega)
      (fun hf => by have := ha.lt; simp only [heapStart, frameIn] at this hf; omega)) hl
  exact ⟨C3, _, fun R' ha0 => ⟨ha0, hd3, hval, ⟨y', hy', ep, by rw [en]; exact hp.num⟩, hp.slot,
    rfl, by simp only [List.length_cons]; omega,
    fun a ho _ hf hs => by
      rw [hp.out a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]
      exact hout0 a ho hs hf⟩⟩

/-- **A three-operand operation's failure that loses the slot's handle**
`p`, the memory changed only on `P` (off the heap and the globals). -/
theorem OpFail3.of_leak {S : Nat → Prop} {M M2 M' : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p pa pb pc : Nat}
    {na nb nc : Num} {f : Nat → Num → Num → Num → Option Num} {sp q N : Nat} {P : Nat → Prop}
    {x1 x2 x3 : NumObj}
    (hd2 : DcAt S M2 H F L C G (.num p :: .num pa :: .num pb :: .num pc :: hs) st)
    (hl : G.lk.length < 2 ^ 29)
    (hx1 : x1 ∈ L) (e1p : x1.rep.p = pa) (e1n : x1.rep.num = na)
    (hx2 : x2 ∈ L) (e2p : x2.rep.p = pb) (e2n : x2.rep.num = nb)
    (hx3 : x3 ∈ L) (e3p : x3.rep.p = pc) (e3n : x3.rep.num = nc)
    (hnone : f st.scale na nb nc = none)
    (hm : MemOnly P M' M2) (hP : ∀ a, P a → OutHeap a ∧ ¬ DcGlob a)
    (hout : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slotBytes q a →
      imgM M' a = imgM M a)
    (R' : Nat → BitVec 64) (ha0 : R' 10 ≠ 0#64) :
    OpFail3 S M M' H F L C G { G with lk := p :: G.lk } hs st pa pb pc na nb nc f R' sp q N 1 where
  a0 := ha0
  h := (hd2.leak hl).outWrite hm hP
  val := hnone
  da := ⟨x1, hx1, e1p, e1n⟩
  db := ⟨x2, hx2, e2p, e2n⟩
  dc := ⟨x3, hx3, e3p, e3n⟩
  same := rfl
  lkLen := by simp only [List.length_cons]; omega
  out := hout

/-! ## `dc_modexp` -/

/-- A number the handles name has a reference. -/
theorem DcDen.refs_pos_mem {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {x : NumObj} (d : DcDen L C G hs st) (hx : x ∈ L) (hm : GV.num x.rep.p ∈ hs) :
    1 ≤ x.rep.refs := by
  rw [d.numRefs x hx]
  have := List.count_pos_iff.mpr (List.mem_append_right G.vals hm)
  omega

/-- **Three numbers of the state as `bc_raisemod`'s operands**, with the
constants `_zero_`, `_one_` and `_two_`. -/
theorem DcAt.rxArgs {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {x1 x2 x3 : NumObj} (h1 : x1 ∈ L) (h2 : x2 ∈ L) (h3 : x3 ∈ L) (hhs : hs.length ≤ 2 ^ 20)
    {k : Nat} (r1 : 1 ≤ x1.rep.refs) (r2 : 1 ≤ x2.rep.refs)
    (hsz : 8 * (x1.rep.len + x1.rep.scale + x3.rep.len + x3.rep.scale + k + 1) +
      (x2.rep.len + x2.rep.scale) < 2 ^ 24)
    (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80) : RxArgs S M L x1 x2 x3 C.z C.o C.t k where
  mb := h1
  me := h2
  mm := h3
  mz := h.den.mz
  mo := h.den.mo
  mt := h.den.mt
  lenb := h.den.pos x1 h1
  ne := h.den.norm x2 h2
  lene := h.den.pos x2 h2
  nm := h.den.norm x3 h3
  size := hsz
  refs := fun y hy => by have := h.refs_le hy; omega
  rb := r1
  re := r2
  ro := by
    have hr := h.den.numRefs _ h.den.mo
    have hc : 1 ≤ C.cnt C.o.rep.p := by
      unfold BcConsts.cnt; exact List.countP_pos_iff.mpr ⟨C.o, by simp, by simp⟩
    omega
  zero := (h.kzero hhs).mono (by omega)
  one := h.view.ow
  oneNum := h.den.ov
  oneNorm := h.den.norm _ h.den.mo
  oneLen := h.den.pos _ h.den.mo
  two := h.view.tw
  twoNum := h.den.tv
  twoNorm := h.den.norm _ h.den.mt
  mulBase := hmb
  owns := h.den.owns
  fd := h.errFile

/-- **`dc_modexp`'s `bc_init_num (result)`** at `0x800049bc`, its frame
stored: the slot holds a new `_zero_` handle, the operands are `x1`, `x2`,
`x3` of the heap. -/
theorem mx_init {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M M1 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pa pb pc : Nat}
    {na nb nc : Num} {R : Nat → BitVec 64} {sp q N lk : Nat}
    (hin : OpIn3 S M H F L C G hs st pa pb pc na nb nc R sp q N lk) (hN : 48 ≤ N)
    (hM1 : MemOnly (frameIn sp 48) M1 M) (fr : DrFrame M1 sp R st.scale pb)
    (R1 : Nat → BitVec 64) (r10 : R1 10 = BitVec.ofNat 64 q) (hal1 : (R1 1).toNat % 4 = 0)
    (hk : ∀ R2 M2 L2 C2 x1 x2 x3, Keeps [14, 15] R2 R1 →
      DcAt S M2 H F L2 C2 G (.num C2.z.rep.p :: .num pa :: .num pb :: .num pc :: hs) st →
      ldv .ld M2 q = BitVec.ofNat 64 C2.z.rep.p →
      x1 ∈ L2 → x1.rep.p = pa → x1.rep.num = na →
      x2 ∈ L2 → x2.rep.p = pb → x2.rep.num = nb →
      x3 ∈ L2 → x3.rep.p = pc → x3.rep.num = nc →
      (∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 48 a → imgM M2 a = imgM M a) →
      DrFrame M2 sp R st.scale pb → DWO live S Q t (R1 1) R2 M2) :
    DWO live S Q t 0x800049bc#64 R1 M1 := by
  have hsf := hin.frame
  have hsl := hsf.lo
  have hab := hin.above
  simp only [heapEnd] at hab
  have hqs := hin.slotHi
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have h1 := hin.h.outWrite hM1 fun a ha =>
    ⟨(above_sp (sp := sp - 48) hab2 (a := a) (by simp only [frameIn] at ha; omega)).1,
     (above_sp (sp := sp - 48) hab2 (a := a) (by simp only [frameIn] at ha; omega)).2.1⟩
  have hlen : (GV.num pa :: GV.num pb :: GV.num pc :: hs).length ≤ 2 ^ 30 := by
    have := hin.hsLen; simp only [List.length_cons]; omega
  refine dc_init_num_spec hlive h1 hlen hin.slot (by simp only [heapEnd]; omega) R1 r10 hal1
    fun R2 M2 L2 C2 hk2 hd2 hkeep hw2 hfr2 => ?_
  have e1 : C2.z.rep.p = C.z.rep.p := h1.zeroP_eq hd2 (ldv_congr .ld fun j hj =>
    hfr2 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, widthOfM,
        dc_addrs] at hj ⊢; omega)
      (fun hs => by simp only [slotBytes, widthOfM, dc_addrs] at hs hj; omega))
  rw [← e1] at hd2 hw2
  obtain ⟨x1, hx1, e1p, e1n⟩ := (hkeep _ List.mem_cons_self _ hin.da).numObj
  obtain ⟨x2, hx2, e2p, e2n⟩ :=
    (hkeep _ (List.mem_cons_of_mem _ List.mem_cons_self) _ hin.db).numObj
  obtain ⟨x3, hx3, e3p, e3n⟩ :=
    (hkeep _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ hin.dc).numObj
  exact hk R2 M2 L2 C2 x1 x2 x3 hk2 hd2 hw2 hx1 e1p e1n hx2 e2p e2n hx3 e3p e3n
    (fun a ho hs hf => by rw [hfr2 a ho hs]; exact hM1 a hf)
    (fr.transport (by omega) fun a h1 h2 =>
      hfr2 a (above_sp hab2 h1).1 fun hs => by simp only [slotBytes] at hs; omega)

/-- **`dc_modexp`'s failure exit** at `0x8000253c`: `1`, the epilogue; the
slot's `_zero_` handle is lost. -/
theorem mx_out {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M M2 M5 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C2 : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {p pa pb pc : Nat} {na nb nc : Num} {x1 x2 x3 : NumObj}
    (hd2 : DcAt S M2 H F L C2 G (.num p :: .num pa :: .num pb :: .num pc :: hs) st)
    (hl : G.lk.length < 2 ^ 29)
    (hx1 : x1 ∈ L) (e1p : x1.rep.p = pa) (e1n : x1.rep.num = na)
    (hx2 : x2 ∈ L) (e2p : x2.rep.p = pb) (e2n : x2.rep.num = nb)
    (hx3 : x3 ∈ L) (e3p : x3.rep.p = pc) (e3n : x3.rep.num = nc)
    (hnone : Num.raisemod na nb nc st.scale = none)
    {sp q k0 pb0 N : Nat} (hsf : StackFrame S sp N) (hab : heapEnd + N ≤ sp) (hN : 48 ≤ N)
    (hout0 : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 48 a → imgM M2 a = imgM M a)
    (R : Nat → BitVec 64) (hm5 : MemOnly (frameIn sp N) M5 M2) (fr : DrFrame M5 sp R k0 pb0)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (R5 : Nat → BitVec 64) (q5 : R5 2 = BitVec.ofNat 64 (sp - 48)) (h50 : R5 10 = 1#64)
    (kk : Keeps (8 :: 9 :: 18 :: 2 :: opClob) R5 R)
    (hfail : ∀ R' M' H' F' L' C' G', Keeps opClob R' R →
      OpFail3 S M M' H' F' L' C' G G' hs st pa pb pc na nb nc
        (fun k a b c => Num.raisemod a b c k) R' sp q N 1 → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x8000253c#64 R5 M5 := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - N := by simp only [heapEnd]; omega
  have hP : ∀ a, frameIn sp N a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have hS : HeapOwn S := fun a e1 e2 => hd2.heap.heap.own a e1 e2
  bc_run hlive hS [q5, fr.w24, fr.w32, fr.w40, fr.w16]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hal
  have ho : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slotBytes q a →
      imgM M5 a = imgM M a := fun a ho _ hf hs => by
    rw [hm5 a hf]
    exact hout0 a ho hs (by simp only [frameIn] at hf ⊢; omega)
  refine hfail _ M5 H F L C2 _
    (Keeps.restore (by rw [h2]; congr 1; omega) (Keeps.restore rfl (Keeps.restore rfl
      (Keeps.restore rfl (by keeps_tac kk)))))
    (OpFail3.of_leak hd2 hl hx1 e1p e1n hx2 e2p e2n hx3 e3p e3n hnone hm5 hP ho _ ?_)
  bsimp [h50]; decide

/-- **`dc_modexp` after `bc_raisemod` returned `-1`** (`0x80002510`):
`bc_is_zero (mod)`, the message for a zero modulus, then `1`. -/
theorem mx_fail {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M M2 Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C2 : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {p pa pb pc : Nat} {na nb nc : Num} {x1 x2 x3 : NumObj}
    (hd2 : DcAt S M2 H F L C2 G (.num p :: .num pa :: .num pb :: .num pc :: hs) st)
    (hl : G.lk.length < 2 ^ 29)
    (hx1 : x1 ∈ L) (e1p : x1.rep.p = pa) (e1n : x1.rep.num = na)
    (hx2 : x2 ∈ L) (e2p : x2.rep.p = pb) (e2n : x2.rep.num = nb)
    (hx3 : x3 ∈ L) (e3p : x3.rep.p = pc) (e3n : x3.rep.num = nc)
    (hnone : Num.raisemod na nb nc st.scale = none)
    {sp q k0 pb0 N W : Nat} (hsf : StackFrame S sp N) (hab : heapEnd + N ≤ sp) (hNW : N = 48 + W)
    (hN : 304 ≤ W)
    (hout0 : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 48 a → imgM M2 a = imgM M a)
    (R : Nat → BitVec 64) (fr : DrFrame M2 sp R k0 pb0)
    (hfr : ∀ a, ¬ frameIn (sp - 48) W a → imgM Mt a = imgM M2 a)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (R3 : Nat → BitVec 64) (q3 : R3 2 = BitVec.ofNat 64 (sp - 48))
    (h30 : R3 10 = 0xffffffffffffffff#64) (r9 : R3 9 = BitVec.ofNat 64 pc)
    (kk : Keeps (8 :: 9 :: 18 :: 2 :: opClob) R3 R)
    (hfail : ∀ R' M' H' F' L' C' G', Keeps opClob R' R →
      OpFail3 S M M' H' F' L' C' G G' hs st pa pb pc na nb nc
        (fun k a b c => Num.raisemod a b c k) R' sp q N 1 → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80002510#64 R3 Mt := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - N := by simp only [heapEnd]; omega
  have hd3 := hd2.outWrite (P := frameIn (sp - 48) W) hfr fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have frT := fr.transport (by omega) fun a e1 e2 => hfr a (by simp only [frameIn]; omega)
  have hm3 : MemOnly (frameIn sp N) Mt M2 := fun a ha =>
    hfr a fun h' => by simp only [frameIn] at ha h'; omega
  have hS3 : HeapOwn S := fun a e1 e2 => hd3.heap.heap.own a e1 e2
  have hn3 := hd3.heap.nums x3 hx3
  num_facts hn3
  bc_run hlive hS3 [q3, h30, r9] at 0x80004a10
  bc_run hlive hS3 [q3, r9] at 0x80004a10
  refine bc_is_zero_spec hlive hS3 hn3 (hd3.den.pos x3 hx3)
    (fun b h1 h2 => hd3.glob b (by unfold DcGlob; simp only [dc_addrs] at *; omega)) ?_ _
    ?_ ?_ fun R4 hk4 h40 => ?_
  rotate_left
  · bsimp [r9, e3p]
  · bsimp []
  rotate_left
  · intro hz
    rw [hd3.view.zw] at hz
    have hzn := hd3.heap.nums C2.z hd3.den.mz
    have a1 := hzn.shape.pLo; have a2 := hzn.shape.pHi
    simp only [heapStart, heapEnd] at a1 a2
    have hzp : C2.z.rep.p = x3.rep.p := by bv_nat at hz; omega
    have e := hd3.heap.pdist.eq hd3.den.mz hx3 hzp
    rw [← e, hd3.den.zv]; rfl
  have q4 : R4 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk4.get 2 (by decide)]; bsimp [q3]
  have kk4 : Keeps (8 :: 9 :: 18 :: 2 :: opClob) R4 R :=
    (hk4.mono (by decide)).trans (by keeps_tac kk)
  bsimp []
  have hpn := hd3.view.prog
  have hG := hd3.glob
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hS3 [q4] at 0x80000774 0x8000253c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · intro _
    bc_run hlive hS3 [q4, hpn, stderr_word] at 0x80000774
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine fprintf_prog_spec hlive remMsg (by decide)
      (hsf.within (m := 48) (n := 304) (by omega) (by decide))
      (by simp only [stderrAddr]; omega) hd3.errFile _ ?_ ?_ ?_ ?_ ?_ fun R5 M5 hk5 hfr5 => ?_
    · bsimp [q4]
    · bsimp [stderrAddr]
    · bsimp []
    · bsimp []
    · bsimp []
    have q5 : R5 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk5.get 2 (by decide)]; bsimp [q4]
    bsimp []
    bc_run hlive hS3 [q5] at 0x8000253c
    refine mx_out hlive hd2 hl hx1 e1p e1n hx2 e2p e2n hx3 e3p e3n hnone hsf hab (by omega)
      hout0 R (fun a ha => (hfr5 a (by simp only [frameIn] at ha; omega)).trans (hm3 a ha))
      (frT.transport (by omega) fun a e1 e2 => hfr5 a (.inr (by omega))) h2 hal _
      ?_ ?_ (by keeps_tac ((hk5.mono (by decide)).trans (by keeps_tac kk4))) hfail
    · bsimp [q5]
    · bsimp []
  · intro _
    bc_run hlive hS3 [q4] at 0x8000253c
    refine mx_out hlive hd2 hl hx1 e1p e1n hx2 e2p e2n hx3 e3p e3n hnone hsf hab (by omega)
      hout0 R hm3 frT h2 hal _ ?_ ?_ (by keeps_tac kk4) hfail
    · bsimp [q4]
    · bsimp []

/-- **`dc_modexp` after `bc_raisemod` returned `0`** (`0x80002510`): the
slot's new handle for the result, then the epilogue. -/
theorem mx_ret {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M M2 Mt : Mem} {H H4 : Heap}
    {F F4 : List Blk} {L Lf : List NumObj} {C2 : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pa pb pc : Nat} {na nb nc n : Num} {y : NumObj} {sp q k0 pb0 : Nat}
    (hd2 : DcAt S M2 H F L C2 G
      (.num C2.z.rep.p :: .num pa :: .num pb :: .num pc :: hs) st)
    (hp : RxPost S (G.raws M2) M2 Mt H4 F4 L C2.z q (sp - 48) (640 + rmStack (2 ^ 30)) n Lf y)
    (hn : Num.raisemod na nb nc st.scale = some n) (hl : G.lk.length < 2 ^ 29)
    (hsf : StackFrame S sp (48 + (640 + rmStack (2 ^ 30))))
    (hab : heapEnd + (48 + (640 + rmStack (2 ^ 30))) ≤ sp) (hqs : sp ≤ q)
    (hout2 : ∀ a, OutHeap a → ¬ slotBytes q a → ¬ frameIn sp 48 a → imgM M2 a = imgM M a)
    (R : Nat → BitVec 64) (fr2 : DrFrame M2 sp R k0 pb0)
    (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (R4 : Nat → BitVec 64) (q4 : R4 2 = BitVec.ofNat 64 (sp - 48)) (h40 : R4 10 = 0#64)
    (kk : Keeps (8 :: 9 :: 18 :: 2 :: opClob) R4 R)
    (hret : ∀ R' M' H' F' L' C' G' y r, Keeps opClob R' R →
      OpRet3 S M M' H' F' L' C' G G' hs st pa pb pc na nb nc
        (fun k a b c => Num.raisemod a b c k) R' sp q (48 + (640 + rmStack (2 ^ 30))) 1 y r →
      DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80002510#64 R4 Mt := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  obtain ⟨C4, G4, hr⟩ := OpRet3.of_rxPost (f := fun k a b c => Num.raisemod a b c k) (na := na)
    (nb := nb) (nc := nc) (N := 48 + (640 + rmStack (2 ^ 30))) (lk := 1) hd2 hd2.den.mz hp hn
    (by omega) (by omega) (by simp only [heapEnd]; omega) hqs hl (Nat.le_refl _)
    fun a ho hs hf => hout2 a ho hs fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
  have frT := fr2.transport (by omega) fun a e1 e2 =>
    hp.out a (above_sp hab2 e1).1 (fun hs => by simp only [slotBytes] at hs; omega)
      ((above_sp hab2 e1).2.2 _)
  have hS4 : HeapOwn S := fun a e1 e2 => hp.heap.heap.own a e1 e2
  bc_run hlive hS4 [q4, h40]
  all_goals (try (intro hc; exact absurd h40 hc))
  bc_run hlive hS4 [q4, frT.w24, frT.w32, frT.w40, frT.w16]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hal
  refine hret _ Mt H4 F4 Lf C4 G4 y.rep.p n
    (Keeps.restore (by rw [h2]; congr 1; omega) (Keeps.restore rfl (Keeps.restore rfl
      (Keeps.restore rfl (by keeps_tac kk))))) (hr _ ?_)
  bsimp [h40]

/-- **`dc_modexp`** at `0x800024c8`: `bc_init_num (result)`, then
`bc_raisemod (base, expo, mod, result, kscale)`; a zero modulus or a negative
exponent fails (with a message for the zero modulus) and loses the slot's
`_zero_` reference; success loses `parity`'s. -/
theorem dc_modexp_spec {live S : Nat → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    DcOp3 live S 0x800024c8 (48 + (640 + rmStack (2 ^ 30))) 1
      (fun k a b c => 8 * (a.wid + c.wid + k + 1) + b.wid < 2 ^ 24)
      (fun k a b c => Num.raisemod a b c k) := by
  intro Q t M H F L C G hs st pa pb pc na nb nc R sp q hin hok hret hfail hoom
  have hsf := hin.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := hin.above
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hqs := hin.slotHi
  have hql := hin.slot.lo; have hqh := hin.slot.hi; have hqa := hin.slot.al
  have hS : HeapOwn S := fun a e1 e2 => hin.h.heap.heap.own a e1 e2
  have h2 := hin.r2; have h10 := hin.r10; have h11 := hin.r11; have h12 := hin.r12
  have h13 := hin.r13; have h14 := hin.r14
  bc_run hlive hS [h2, h10, h11, h12, h13, h14, word_sub48] at 0x800049bc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine mx_init hlive hin (by omega)
    (fun a ha => by simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)])
    ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ _ (by bsimp []) (by bsimp [])
    fun R2 M2 L2 C2 x1 x2 x3 hk2 hd2 hw2 hx1 e1p e1n hx2 e2p e2n hx3 e3p e3n hout2 fr2 => ?_
  · ld48
  · ld48
  · ld48
  · ld48
  · ld48
  · ld48
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have m0 := fr2.w0; have m8 := fr2.w8
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk2.get 2 (by decide)]; bsimp []
  have r8 : R2 8 = BitVec.ofNat 64 q := by rw [hk2.get 8 (by decide)]; bsimp []
  have r9 : R2 9 = BitVec.ofNat 64 pc := by rw [hk2.get 9 (by decide)]; bsimp []
  have r18 : R2 18 = BitVec.ofNat 64 pa := by rw [hk2.get 18 (by decide)]; bsimp []
  have hS2 : HeapOwn S := fun a e1 e2 => hd2.heap.heap.own a e1 e2
  have hmb2 : ldv .lw M2 mulBaseAddr = BitVec.ofNat 64 80 :=
    (hin.mb.transport (M' := M2) fun a e1 e2 => by
      have ⟨o1, _, o3⟩ := mulBase_off e1 e2
      exact hout2 _ o1 (fun hs => by simp only [slotBytes, heapStart] at hs o3; omega)
        fun hf => by simp only [frameIn, heapStart] at hf o3; omega).word
  bsimp []
  bc_run hlive hS2 [q2, r8, r9, r18, m0, m8] at 0x800061c4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  -- the operands' sizes and references, `_zero_` in the slot
  have hsz : 8 * (x1.rep.len + x1.rep.scale + x3.rep.len + x3.rep.scale + st.scale + 1) +
      (x2.rep.len + x2.rep.scale) < 2 ^ 24 := by
    have w1 := NumRep.len_le_wid (hd2.heap.nums x1 hx1).shape (hd2.den.norm x1 hx1)
    have w2 := NumRep.len_le_wid (hd2.heap.nums x2 hx2).shape (hd2.den.norm x2 hx2)
    have w3 := NumRep.len_le_wid (hd2.heap.nums x3 hx3).shape (hd2.den.norm x3 hx3)
    rw [← e1n, ← e2n, ← e3n] at hok
    omega
  clear hok
  have hr1 : 1 ≤ x1.rep.refs := hd2.den.refs_pos_mem hx1 (by rw [e1p]; simp)
  have hr2 : 1 ≤ x2.rep.refs := hd2.den.refs_pos_mem hx2 (by rw [e2p]; simp)
  have hrz := hd2.zero_refs hd2.den.mz rfl
  have hlen : (GV.num C2.z.rep.p :: GV.num pa :: GV.num pb :: GV.num pc :: hs).length ≤ 2 ^ 20 := by
    have := hin.hsLen; simp only [List.length_cons]; omega
  have hl : G.lk.length < 2 ^ 29 := by have := hin.lkLen; omega
  refine bc_raisemod_spec hlive (W := 640 + rmStack (2 ^ 30)) (k := st.scale)
    ⟨hsf.within (m := 48) (n := 640 + rmStack (2 ^ 30)) (by omega) (by decide),
      by simp only [heapEnd]; omega, Nat.le_refl _, by simp only [stderrAddr]; omega, hin.mb.own,
      fun a ha => hd2.glob a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega),
      by bsimp [q2], by bsimp [],
      ⟨hin.slot, fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega),
        .inr (by omega)⟩⟩
    (hd2.rxArgs hx1 hx2 hx3 hlen hr1 hr2 hsz hmb2) ⟨hd2.den.mz, by omega, hw2⟩ hd2.heap
    ⟨fun r hr R4 Mt H4 F4 Lf y hk4 h40 hp => ?_, fun hnone R4 Mt hk4 h40 hfr => ?_,
      fun R4 Mt sp' o1 o2 hr2' hout => ?_⟩
    (by bsimp [e1p]) (by bsimp [e2p]) (by bsimp [e3p]) (by bsimp []) (by bsimp [])
  · -- the result
    have q4 : R4 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk4.get 2 (by decide)]; bsimp [q2]
    bsimp []
    exact mx_ret hlive hd2 hp (by rw [← e1n, ← e2n, ← e3n]; exact hr) hl hsf
      (by simp only [heapEnd]; omega) hqs hout2 R fr2 h2 hin.al R4 q4 h40
      ((hk4.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))) hret
  · -- a zero modulus or a negative exponent
    have q4 : R4 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk4.get 2 (by decide)]; bsimp [q2]
    have r49 : R4 9 = BitVec.ofNat 64 pc := by rw [hk4.get 9 (by decide)]; bsimp [r9]
    bsimp []
    exact mx_fail hlive hd2 hl hx1 e1p e1n hx2 e2p e2n hx3 e3p e3n
      (by rw [← e1n, ← e2n, ← e3n]; exact hnone) hsf (by simp only [heapEnd]; omega) rfl
      (by omega) hout2 R fr2 hfr h2 hin.al R4 q4 h40 r49
      ((hk4.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))) hfail
  · bc_run hlive hS2 [] at 0x80001e74
    have l1 : sp - (48 + (640 + rmStack (2 ^ 30))) ≤ sp' := by
      rw [← Nat.sub_sub]; exact o1
    have l2 : sp' ≤ sp := Nat.le_trans o2 (Nat.sub_le sp 48)
    refine hoom R4 Mt sp' ⟨l1, l2, hr2', fun a ho hg hf hs => ?_⟩
    have n1 : ¬ frameIn (sp - 48) (640 + rmStack (2 ^ 30)) a := by
      intro h'; simp only [frameIn] at hf h'; omega
    have n2 : ¬ frameIn sp 48 a := by
      intro h'; simp only [frameIn] at hf h'; omega
    rw [hout a ho hs n1]
    exact hout2 a ho hs n2

end Dc.Mach
