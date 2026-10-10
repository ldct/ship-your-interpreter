import Dc.Mach.DcModexp
import Dc.Mach.Bc.SqrtEntry

/-!
# `dc_sqrt` (M9)

    dc_sqrt (value, kscale, &result):
      tmp = bc_copy_num (value);
      if (!bc_sqrt (&tmp, kscale))
        { fprintf (stderr, "%s: square root of negative number\n", progname);
          bc_free_num (&tmp); return DC_FAIL; }
      *result = tmp; return DC_SUCCESS;

- `DcDen.sqLeak`: `bc_sqrt`'s possible extra reference to `_zero_`, lost
  (`DcG.lk`).
- `DcDen.sqPost`, `DcAt.sqNum`: the copy's handle replaced by the result's.
- `DcAt.sqArgs`: the state's numbers as `bc_sqrt`'s operands.
- `dc_sqrt_spec`: the result for `SqOut x k (some r)`, the message and `1`
  for a negative `x`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

theorem SqLeak.pdist {L Lw : List NumObj} {z : NumObj} (hl : SqLeak L z Lw) (hd : PDist L) :
    PDist Lw := by
  rcases hl with rfl | ⟨A, B, rfl, rfl⟩
  · exact hd
  · exact hd.congr (by simp only [List.map_append, List.map_cons]; rfl)

/-- A number before the leak is still there, at its address. -/
theorem SqLeak.mem_p {L Lw : List NumObj} {z x : NumObj} (hl : SqLeak L z Lw) (hx : x ∈ L) :
    ∃ x' ∈ Lw, x'.rep.p = x.rep.p := by
  rcases hl with rfl | ⟨A, B, rfl, rfl⟩
  · exact ⟨x, hx, rfl⟩
  · exact (AddRef.share (A := A) (B := B) (x := z)).mem_p hx

/-- **`bc_sqrt`'s extra reference to `_zero_`** (`0 < x < 1`), lost: it goes
on the ghost's `lk`. -/
theorem DcDen.sqLeak {L Lw : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (d : DcDen L C G hs st) (hd : PDist L) (hl : SqLeak L C.z Lw)
    (hlk : G.lk.length < 2 ^ 29) :
    ∃ C', ∃ pl : List Nat, pl.length ≤ 1 ∧ DcDen Lw C' { G with lk := pl ++ G.lk } hs st ∧
      C.SameP C' := by
  rcases hl with rfl | ⟨A, B, rfl, rfl⟩
  · exact ⟨C, [], by simp, d, .refl C⟩
  · have hz : C.z ∈ A ++ C.z :: B := List.mem_append_right _ List.mem_cons_self
    have hdw : PDist (A ++ C.z.withRefs (C.z.rep.refs + 1) :: B) :=
      hd.congr (by simp only [List.map_append, List.map_cons]; rfl)
    obtain ⟨C1, d1, s1⟩ := d.addRef hd .share hdw (d.norm C.z hz) (d.pos C.z hz) (d.owns C.z hz)
    exact ⟨C1, [C.z.rep.p], by simp, d1.leak hlk, s1⟩

/-- **The copy's handle after `bc_sqrt`** on the ghost side: the copy at `p`
dropped, then one reference added to the result `y`. -/
theorem DcDen.sqPost {Lw Ld Lf : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {p : Nat} {y : NumObj} (d : DcDen Lw C G (.num p :: hs) st) (hd : PDist Lw)
    (hdrop : DropAt Lw p Ld) (hadd : AddRef Ld y Lf) (hdf : PDist Lf) (hno : y.rep.Norm)
    (hpos : 1 ≤ y.rep.len) (how : y.Owns) :
    ∃ C', DcDen Lf C' G (.num y.rep.p :: hs) st ∧ C.SameP C' := by
  obtain ⟨L1, L2, x, rfl, rfl, hfr⟩ := hdrop
  cases hfr with
  | dec h2 =>
    obtain ⟨C2, d2, s2⟩ := (d.dec hd.ne h2).addRef (hadd.pdist_of hdf) hadd hdf hno hpos how
    exact ⟨C2, d2, (C.sameP_subst (x := x) (x' := x.decRef) rfl rfl).trans s2⟩
  | rel h1 =>
    obtain ⟨C2, d2, s2⟩ := (d.rel hd.ne h1).addRef (hadd.pdist_of hdf) hadd hdf hno hpos how
    exact ⟨C2, d2, s2⟩

/-- **The copy's handle after `bc_sqrt`**: the state holds `.num y.p` instead
of the copy's `.num x.p`, with at most one lost reference (`_zero_`'s). -/
theorem DcAt.sqNum {S : Nat → Prop} {M Mt : Mem} {H H' : Heap} {F F' : List Blk}
    {L Lf : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {x y : NumObj}
    {q sp W : Nat} {n : Num} (h : DcAt S M H F L C G (.num x.rep.p :: hs) st)
    (hp : SqPost S (G.raws M) M Mt H' F' L x C.z q sp W n Lf y)
    (hgl : ∀ a, DcGlob a → imgM Mt a = imgM M a) (hl : G.lk.length < 2 ^ 29) :
    ∃ C' pl, pl.length ≤ 1 ∧
      DcAt S Mt H' F' Lf C' { G with lk := pl ++ G.lk } (.num y.rep.p :: hs) st ∧
      ∃ y' ∈ Lf, y'.rep.p = y.rep.p ∧ y'.rep.num = n := by
  obtain ⟨Lw, Ld, hlk, hdrop, hadd⟩ := hp.mid
  have hdw := hlk.pdist h.heap.pdist
  obtain ⟨C1, pl, hpl, d1, s1⟩ := h.den.sqLeak h.heap.pdist hlk hl
  obtain ⟨C2, d2, s2⟩ := d1.sqPost hdw hdrop hadd hp.heap.pdist hp.norm hp.pos hp.owns
  have hag : ∀ a, InBlocks G.blocks a → imgM Mt a = imgM M a := fun a ⟨c, hc, ha⟩ =>
    hp.heap.raw.img c hc a ha
  exact ⟨C2, pl, hpl, ⟨hp.heap.subRaw (fun c hc => hc) (fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm),
    h.nodup, { (h.view.frame hag hgl).sameP (s1.trans s2) with }, d2, h.glob, h.col⟩,
    y, hadd.mem, rfl, hp.num⟩

/-- **A number of the state as `bc_sqrt`'s operand** in the slot `q`, with
the constants `_zero_` and `_one_`; the operand holds a second reference (the
copy's). -/
theorem DcAt.sqArgs {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    {x : NumObj} (hx : x ∈ L) (hr2 : 2 ≤ x.rep.refs) (hhs : hs.length ≤ 2 ^ 20) {q k : Nat}
    (hw : ldv .ld M q = BitVec.ofNat 64 x.rep.p) (hsz : x.rep.len + x.rep.scale + k < 2 ^ 20)
    (hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80) : SqArgs S M L x C.z C.o q k where
  mx := hx
  nx := h.den.norm x hx
  lenx := h.den.pos x hx
  rx := by omega
  wx := hw
  mz := h.den.mz
  mo := h.den.mo
  size := hsz
  refs := fun y hy => by have := h.refs_le hy; omega
  live := h.den.live
  zero := h.kzero hhs
  one := h.view.ow
  oneNum := h.den.ov
  oneNorm := h.den.norm _ h.den.mo
  oneLen := h.den.pos _ h.den.mo
  oneRefs := h.den.live _ h.den.mo
  mulBase := hmb
  owns := h.den.owns
  fd := h.errFile
  zeroRef := fun _ => hr2
  oneRef := fun _ => hr2

/-- `dc_sqrt` after `bc_sqrt` returned `1` (`0x800025f0`): the copy's slot
word stored through `result`, then `0`. -/
theorem sqrt_ret {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {Mt : Mem} {sp rq yp : Nat}
    (hsf : StackFrame S sp 48) (hrq : PtrSlot S rq) {ra : BitVec 64} (hal : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h10 : R 10 = 1#64)
    (f0 : ldv .ld Mt (sp - 48) = BitVec.ofNat 64 rq)
    (f24 : ldv .ld Mt (sp - 48 + 24) = BitVec.ofNat 64 yp) (f40 : ldv .ld Mt (sp - 48 + 40) = ra)
    (hk : ∀ R', Keeps [1, 2, 10, 12, 15] R' R → R' 2 = BitVec.ofNat 64 sp → R' 10 = 0#64 →
      DWO live S Q t ra R' (writeLog Mt [(rq, 8, BitVec.ofNat 64 yp)])) :
    DWO live S Q t 0x800025f0#64 R Mt := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hq1 := hrq.lo; have hq2 := hrq.hi; have hq3 := hrq.al
  have hrqw : (BitVec.ofNat 64 rq).toNat = rq := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  bc_run hlive hS [h2, h10, f0, f24, f40]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [h2, h10, f0, f24, f40, hrqw]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hrq.acc | (rw [hrqw]; exact hrq.acc) | (simp only [StOK, htx, hrqw]; omega) | exact hal | skip
  exact hk _ (by keeps_tac Keeps.refl _ _)
    (show BitVec.ofNat 64 (sp - 48 + 48) = _ by congr 1; omega) rfl

theorem sqrtMsg : ProgMsg 0x80007ce8 33 :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide⟩, by decide⟩

/-- `dc_sqrt` after `bc_sqrt` returned `0` (`0x800025f0`, a negative
operand): the message, the copy freed, then `1`. -/
theorem sqrt_neg {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {Mt : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p : Nat}
    (h : DcAt S Mt H F L C G (.num p :: hs) st) {sp : Nat} (hsf : StackFrame S sp 352)
    (hab : heapEnd + 352 ≤ sp) {ra : BitVec 64} (hal : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h10 : R 10 = 0#64)
    (f24 : ldv .ld Mt (sp - 48 + 24) = BitVec.ofNat 64 p) (f40 : ldv .ld Mt (sp - 48 + 40) = ra)
    (hk : ∀ R' M' H' F' L' C', Keeps (1 :: 2 :: opClob) R' R → R' 2 = BitVec.ofNat 64 sp →
      R' 10 = 1#64 → DcAt S M' H' F' L' C' G hs st → StkOut sp 352 M' Mt →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x800025f0#64 R Mt := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hpn := h.view.prog
  have hG := h.glob
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hS [h2, h10, hpn, stderr_word] at 0x80000774
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [h2, h10, hpn, stderr_word] at 0x80000774
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine fprintf_prog_spec hlive sqrtMsg (by decide) (hsf.within (m := 48) (n := 304) (by omega) (by decide))
    (by simp only [stderrAddr]; omega) h.errFile _ ?_ ?_ ?_ ?_ ?_ fun R4 M4 hk4 hfr4 => ?_
  · bsimp [h2]
  · bsimp [stderrAddr]
  · bsimp []
  · bsimp []
  · bsimp []
  have hab2 : heapEnd ≤ sp - 352 := by simp only [heapEnd]; omega
  have hm4 : MemOnly (frameIn (sp - 48) 304) M4 Mt := fun a ha =>
    hfr4 a (by simp only [frameIn] at ha; omega)
  have h4 := h.outWrite hm4 fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have g24 : ldv .ld M4 (sp - 48 + 24) = BitVec.ofNat 64 p :=
    (ldv_congr .ld fun j hj => hfr4 _ (.inr (by simp only [widthOfM] at hj; omega))).trans f24
  have g40 : ldv .ld M4 (sp - 48 + 40) = ra :=
    (ldv_congr .ld fun j hj => hfr4 _ (.inr (by simp only [widthOfM] at hj; omega))).trans f40
  have q4 : R4 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk4.get 2 (by decide)]; bsimp [h2]
  have hS4 : HeapOwn S := fun a e1 e2 => h4.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS4 [q4] at 0x800048c0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine bc_free_num_dc hlive h4 (hsf.slot (by omega) (by omega) (by omega))
    (by simp only [heapEnd] at hab2 ⊢; omega) g24
    (hsf.within (m := 48) (n := 32) (by omega) (by decide)) (by simp only [heapEnd] at hab2 ⊢; omega)
    (.inr (by omega)) _ (by bsimp [q4]) (by bsimp [q4]) (by bsimp [])
    fun R6 M6 H6 F6 L6 C6 hk6 hd6 hz6 hout6 => ?_
  have hab3 : heapEnd ≤ sp - 48 := by simp only [heapEnd] at hab2 ⊢; omega
  have g40' : ldv .ld M6 (sp - 48 + 40) = ra :=
    (ldv_congr .ld fun j hj => hout6 _ (above_sp hab3 (by omega)).1 (above_sp hab3 (by omega)).2.1
      ((above_sp hab3 (by omega)).2.2 _)
      (fun hs' => by simp only [slotBytes, widthOfM] at hs' hj; omega)).trans g40
  have q6 : R6 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk6.get 2 (by decide)]; bsimp [q4]
  have hS6 : HeapOwn S := fun a e1 e2 => hd6.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS6 [q6, g40']
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ M6 H6 F6 L6 C6 ?_ (show BitVec.ofNat 64 (sp - 48 + 48) = _ by congr 1; omega) rfl hd6
    fun a ho hg hf => ?_
  · exact by keeps_tac ((hk6.mono (by decide)).trans (by keeps_tac ((hk4.mono (by decide)).trans
      (by keeps_tac Keeps.refl _ _))))
  · have e1 := hout6 a ho hg (fun h' => hf (by simp only [frameIn, Nat.sub_sub] at h' ⊢; omega))
      (fun hs' => hf (by simp only [slotBytes, frameIn] at hs' ⊢; omega))
    exact e1.trans (hm4 a fun h' => hf (by simp only [frameIn, Nat.sub_sub] at h' ⊢; omega))

/-- `dc_sqrt`'s stack need: its 48 bytes and `bc_sqrt`'s. -/
abbrev sqN : Nat := 48 + (160 + 512 + rmStack (2 ^ 30))

/-- **`bc_sqrt`'s continuations inside `dc_sqrt`**: from the state after
the copy (`Mt0`, the copy's handle `.num x.p` held twice), the result's
store through `result`, the negative operand's message and free, and
`out_of_memory`. -/
theorem sqrt_k {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M Mt0 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {x : NumObj}
    {rq sp : Nat} {n : Option Num}
    (h5 : DcAt S Mt0 H F L C G (.num x.rep.p :: .num x.rep.p :: hs) st) (hlk : G.lk.length < 2 ^ 29)
    (hsf : StackFrame S sp sqN) (hab : heapEnd + sqN ≤ sp) (hrq : PtrSlot S rq) (hrqs : sp ≤ rq)
    (R R0 : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (k0 : Keeps (1 :: 2 :: opClob) R0 R) (r02 : R0 2 = BitVec.ofNat 64 (sp - 48))
    (r01 : R0 1 = 0x800025f0#64)
    (m0 : ldv .ld Mt0 (sp - 48) = BitVec.ofNat 64 rq)
    (m24 : ldv .ld Mt0 (sp - 48 + 24) = BitVec.ofNat 64 x.rep.p) (m40 : ldv .ld Mt0 (sp - 48 + 40) = R 1)
    (hm5 : ∀ a, OutHeap a → ¬ frameIn sp 48 a → imgM Mt0 a = imgM M a)
    (hret : ∀ r, n = some r → ∀ R' M' H' F' L' C' pl y, Keeps (1 :: 2 :: opClob) R' R →
      R' 2 = R 2 → R' 10 = 0#64 → pl.length ≤ 1 →
      DcAt S M' H' F' L' C' { G with lk := pl ++ G.lk } (.num y :: .num x.rep.p :: hs) st →
      (GV.num y).Den ⟨L', G.strs⟩ (.num r) → ldv .ld M' rq = BitVec.ofNat 64 y →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp sqN a → ¬ slotBytes rq a → imgM M' a = imgM M a) →
      DWO live S Q t (R 1) R' M')
    (hfail : n = none → ∀ R' M' H' F' L' C', Keeps (1 :: 2 :: opClob) R' R → R' 2 = R 2 →
      R' 10 = 1#64 → DcAt S M' H' F' L' C' G (.num x.rep.p :: hs) st → StkOut sp sqN M' M →
      DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp sqN M (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    SqK live S (G.raws Mt0) Q t R0 Mt0 L x C.z (sp - 48 + 24) (sp - 48) (160 + 512 + rmStack (2 ^ 30))
      n := by
  have hN : sqN = 48 + (160 + 512 + rmStack (2 ^ 30)) := rfl
  rw [hN] at hsf hab
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have hS : HeapOwn S := fun a e1 e2 => h5.heap.heap.own a e1 e2
  refine ⟨fun r hr R' Mt' H' F' Lf y hk h1 hp => ?_, fun hn R' Mt' hk h0 hout => ?_, ?_⟩
  · have q2 : R' 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk.get 2 (by decide)]; exact r02
    have hT : ∀ a, sp - 48 ≤ a → a + 8 ≤ sp → (a + 8 ≤ sp - 48 + 24 ∨ sp - 48 + 32 ≤ a) →
        ldv .ld Mt' a = ldv .ld Mt0 a := fun a e1 e2 e3 =>
      ldv_congr .ld fun j hj => hp.out _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj hab2 ⊢; omega))
        (fun hs' => by simp only [slotBytes, widthOfM] at hs' hj; omega)
        (fun hf => by simp only [frameIn, widthOfM] at hf hj; omega)
    have f0 := (hT _ (by omega) (by omega) (.inl (by omega))).trans m0
    have f40 := (hT _ (by omega) (by omega) (.inr (by omega))).trans m40
    have hS' : HeapOwn S := fun a e1 e2 => hp.heap.heap.own a e1 e2
    obtain ⟨C3, pl, hpl, hd3, y', hy', hyp, hyn⟩ := h5.sqNum (x := x) hp (fun a ha => hp.out a ha.outHeap
      (fun hs' => by have := ha.lt; simp only [slotBytes, heapStart] at hs' this; omega)
      (fun hf => by have := ha.lt; simp only [frameIn, heapStart] at hf this; omega)) hlk
    have hab4 : heapEnd ≤ rq := by simp only [heapEnd] at hab2 ⊢; omega
    have hd4 := hd3.outWrite (MemOnly.store Mt' rq 8 (BitVec.ofNat 64 y.rep.p)) fun a ha =>
      ⟨(above_sp hab4 ha.1).1, (above_sp hab4 ha.1).2.1⟩
    rw [r01]
    refine sqrt_ret hlive hS' (hsf.within (m := 0) (n := 48) (by omega) (by decide)) hrq hal R' q2 h1
      f0 hp.slot f40 fun R'' hk' r2 r10 => ?_
    refine hret r hr R'' _ H' F' Lf C3 pl y.rep.p ?_ (r2.trans h2.symm) r10 hpl hd4 ⟨y', hy', hyp, hyn⟩
      (ldv_store_hit _ _ _) fun a ho hg hf hs' => ?_
    · exact (hk'.mono (by decide)).trans ((hk.mono (by decide)).trans k0)
    · rw [show sqN = 48 + (160 + 512 + rmStack (2 ^ 30)) from rfl] at hf
      simp only [frameIn] at hf
      simp only [slotBytes] at hs'
      rw [imgM_store_miss _ _ (by omega)]
      exact (hp.out a ho (fun h' => hf (by simp only [slotBytes] at h'; omega))
        (fun h' => hf (by simp only [frameIn] at h'; omega))).trans
        (hm5 a ho fun h' => hf (by simp only [frameIn] at h'; omega))
  · have q2 : R' 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk.get 2 (by decide)]; exact r02
    have hab4 : heapEnd ≤ sp - 48 - (160 + 512 + rmStack (2 ^ 30)) := by
      simp only [heapEnd] at hab2 ⊢; omega
    have hd' := h5.outWrite (P := frameIn (sp - 48) (160 + 512 + rmStack (2 ^ 30))) hout fun a ha =>
      ⟨(above_sp hab4 (by simp only [frameIn] at ha; omega)).1,
        (above_sp hab4 (by simp only [frameIn] at ha; omega)).2.1⟩
    have g : ∀ a, sp - 48 ≤ a → ldv .ld Mt' a = ldv .ld Mt0 a := fun a e1 =>
      ldv_congr .ld fun j hj => hout _ fun hf => by simp only [frameIn] at hf; omega
    rw [r01]
    refine sqrt_neg hlive hd' (hsf.within (m := 0) (n := 352) (by omega) (by decide))
      (by simp only [heapEnd] at hab2 ⊢; omega) hal R' q2 h0 ((g _ (by omega)).trans m24)
      ((g _ (by omega)).trans m40) fun R'' M'' H'' F'' L'' C'' hk' r2 r10 hd'' hso => ?_
    refine hfail hn R'' M'' H'' F'' L'' C'' ?_ (r2.trans h2.symm) r10 hd'' fun a ho hg hf => ?_
    · exact (hk'.mono (by decide)).trans ((hk.mono (by decide)).trans k0)
    · rw [show sqN = 48 + (160 + 512 + rmStack (2 ^ 30)) from rfl] at hf
      simp only [frameIn] at hf
      exact (hso a ho hg fun h' => hf (by simp only [frameIn] at h'; omega)).trans
        ((hout a fun h' => hf (by simp only [frameIn, Nat.sub_sub] at h'; omega)).trans
          (hm5 a ho fun h' => hf (by simp only [frameIn] at h'; omega)))
  · intro R'' Mt'' sp' e1 e2 r2 hout
    bc_run hlive hS [] at 0x80001e74
    have hN' : sqN = 48 + (160 + 512 + rmStack (2 ^ 30)) := rfl
    refine hoom R'' Mt'' sp' ⟨by rw [hN']; omega, by omega, r2, fun a ho hg hf _ => ?_⟩
    rw [show sqN = 48 + (160 + 512 + rmStack (2 ^ 30)) from rfl] at hf
    simp only [frameIn] at hf
    exact (hout a ho (fun h' => hf (by simp only [slotBytes] at h'; omega))
      (fun h' => hf (by simp only [frameIn, Nat.sub_sub] at h'; omega))).trans
      (hm5 a ho fun h' => hf (by simp only [frameIn] at h'; omega))

/-- **`dc_sqrt (x, k, &result)`** at `0x800025cc` on a handle `.num x.p` the
caller holds: for `SqOut x k (some r)` a new handle to `r` in `result` and
`0`, at most one reference lost; for a negative `x` the message and `1`, the
state kept. -/
theorem dc_sqrt_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {x : NumObj}
    {k rq sp : Nat} {n : Option Num}
    (h : DcAt S M H F L C G (.num x.rep.p :: hs) st) (hx : x ∈ L) (hhs : hs.length + 2 ≤ 2 ^ 20)
    (hlk : G.lk.length < 2 ^ 29) (hsz : x.rep.len + x.rep.scale + k < 2 ^ 20)
    (hO : SqOut x.rep.num k n) (hmb : MulBase S M)
    (hsf : StackFrame S sp sqN) (hab : heapEnd + sqN ≤ sp) (hrq : PtrSlot S rq) (hrqs : sp ≤ rq)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 x.rep.p) (h11 : R 11 = BitVec.ofNat 64 k)
    (h12 : R 12 = BitVec.ofNat 64 rq) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hret : ∀ r, n = some r → ∀ R' M' H' F' L' C' pl y, Keeps (1 :: 2 :: opClob) R' R →
      R' 2 = R 2 → R' 10 = 0#64 → pl.length ≤ 1 →
      DcAt S M' H' F' L' C' { G with lk := pl ++ G.lk } (.num y :: .num x.rep.p :: hs) st →
      (GV.num y).Den ⟨L', G.strs⟩ (.num r) → ldv .ld M' rq = BitVec.ofNat 64 y →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp sqN a → ¬ slotBytes rq a → imgM M' a = imgM M a) →
      DWO live S Q t (R 1) R' M')
    (hfail : n = none → ∀ R' M' H' F' L' C', Keeps (1 :: 2 :: opClob) R' R → R' 2 = R 2 →
      R' 10 = 1#64 → DcAt S M' H' F' L' C' G (.num x.rep.p :: hs) st → StkOut sp sqN M' M →
      DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp sqN M (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x800025cc#64 R M := by
  have hN : sqN = 48 + (160 + 512 + rmStack (2 ^ 30)) := rfl
  rw [hN] at hsf hab
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hb := h.heap.blocks x hx
  have hsz' := hb.sSz; have hsp := hb.sPay
  have fbb := h.heap.heap.blk (List.mem_append_right _ hb.sLive)
  have hblo : 2147603920 ≤ x.sb.h := fbb.lo
  have hbhi : x.sb.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbal : x.sb.h % 16 = 0 := fbb.al
  have hpl : 2147603936 ≤ x.rep.p ∧ x.rep.p + 40 ≤ 2273312768 ∧ x.rep.p % 16 = 0 := by
    rw [hsp]; simp only [Blk.pay, Blk.fin] at *; omega
  obtain ⟨hpl1, hpl2, hpl3⟩ := hpl
  have hrl := h.numRefs_lt (by simp only [List.length_cons]; omega) hx
  have hrf := (h.heap.nums x hx).refs
  have wp := word_succ x.rep.refs
  have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (x.rep.refs + 1))) =
      BitVec.ofNat 64 (x.rep.refs + 1) := sxw_ofNat hrl
  bc_run hlive hS [h10, h11, h12, h2, word_sub48 (show 48 ≤ sp by omega)] at 0x80006a1c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hrf1 : ldv .lw (writeLog (writeLog (writeLog M [(sp - 48, 8, BitVec.ofNat 64 rq)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 8, 8, BitVec.ofNat 64 k)]) (x.rep.p + 12) =
      BitVec.ofNat 64 x.rep.refs := by
    simp only [heapEnd] at hab2
    rw [ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega), ldv_lw_miss _ _ (by omega)]
    exact hrf
  have hk1 : ∀ v : BitVec 64, ldv .ld (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48, 8, BitVec.ofNat 64 rq)]) [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 k)]) [(x.rep.p + 12, 4, v)]) (sp - 48 + 8) =
      BitVec.ofNat 64 k := fun v => by
    simp only [heapEnd] at hab2
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  rw [hrf1, wp, wq, hk1]
  have hP : ∀ a, frameIn sp 48 a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have hm3 : MemOnly (frameIn sp 48) (writeLog (writeLog (writeLog M [(sp - 48, 8, BitVec.ofNat 64 rq)])
      [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 8, 8, BitVec.ofNat 64 k)]) M :=
    (((MemOnly.store _ _ _ _).mono fun a ha => by simp only [frameIn]; omega).trans
      ((MemOnly.store _ _ _ _).mono fun a ha => by simp only [frameIn]; omega)).trans
      ((MemOnly.store _ _ _ _).mono fun a ha => by simp only [frameIn]; omega)
  have h3 := h.outWrite hm3 hP
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hx
  have hlv := h.den.live x hx
  have h4 := h3.bumpNum (by simp only [List.length_cons]; omega)
    (v := BitVec.ofNat 64 (x.rep.refs + 1)) (by simp only [BitVec.toNat_ofNat]; omega)
  have h5 := h4.outWrite (MemOnly.store _ (sp - 48 + 24) 8 (BitVec.ofNat 64 x.rep.p))
    fun a ha => hP a (by simp only [frameIn]; omega)
  have hx' : x.withRefs (x.rep.refs + 1) ∈ L1 ++ x.withRefs (x.rep.refs + 1) :: L2 :=
    List.mem_append_right _ List.mem_cons_self
  have hmb5 := hmb.transport (M' := writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48, 8, BitVec.ofNat 64 rq)]) [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 k)]) [(x.rep.p + 12, 4, BitVec.ofNat 64 (x.rep.refs + 1))])
      [(sp - 48 + 24, 8, BitVec.ofNat 64 x.rep.p)]) fun a e1 e2 => by
    have ⟨o1, _, o3⟩ := mulBase_off e1 e2
    simp only [heapStart] at o3
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
    exact hm3 a fun hf => by simp only [frameIn] at hf; omega
  have m0 : ldv .ld (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48, 8, BitVec.ofNat 64 rq)]) [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 k)]) [(x.rep.p + 12, 4, BitVec.ofNat 64 (x.rep.refs + 1))])
      [(sp - 48 + 24, 8, BitVec.ofNat 64 x.rep.p)]) (sp - 48) = BitVec.ofNat 64 rq := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_ld_miss _ _ (by omega), ldv_store_hit]
  have m40 : ldv .ld (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48, 8, BitVec.ofNat 64 rq)]) [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 k)]) [(x.rep.p + 12, 4, BitVec.ofNat 64 (x.rep.refs + 1))])
      [(sp - 48 + 24, 8, BitVec.ofNat 64 x.rep.p)]) (sp - 48 + 40) = R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_store_hit]
  have m24 : ldv .ld (writeLog (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48, 8, BitVec.ofNat 64 rq)]) [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 k)]) [(x.rep.p + 12, 4, BitVec.ofNat 64 (x.rep.refs + 1))])
      [(sp - 48 + 24, 8, BitVec.ofNat 64 x.rep.p)]) (sp - 48 + 24) = BitVec.ofNat 64 x.rep.p :=
    ldv_store_hit _ _ _
  have hm5 : ∀ a, OutHeap a → ¬ frameIn sp 48 a → imgM (writeLog (writeLog (writeLog (writeLog
      (writeLog M [(sp - 48, 8, BitVec.ofNat 64 rq)]) [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 k)]) [(x.rep.p + 12, 4, BitVec.ofNat 64 (x.rep.refs + 1))])
      [(sp - 48 + 24, 8, BitVec.ofNat 64 x.rep.p)]) a = imgM M a := fun a ho hf => by
    simp only [frameIn] at hf
    have ho' := ho
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ho'
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
    exact hm3 a fun hf' => hf (by simp only [frameIn] at hf'; omega)
  refine bc_sqrt_spec hlive (W := 160 + 512 + rmStack (2 ^ 30)) (q := sp - 48 + 24) (k := k)
    ⟨⟨hsf.within (m := 48) (n := 160 + 512 + rmStack (2 ^ 30)) (by omega) (by decide),
      by simp only [heapEnd]; omega, hmb.own,
      fun a ha => h.glob a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega)⟩,
      Nat.le_refl _, by simp only [stderrAddr]; omega, by bsimp [], by bsimp [],
      ⟨hsf.slot (by omega) (by omega) (by omega),
        fun a ha => outHeap_of_ge (by simp only [slotBytes, heapEnd] at ha ⊢; omega), .inr (by omega)⟩,
      .inr (by simp only [dc_addrs]; omega), .inr (by simp only [dc_addrs]; omega)⟩
    (h5.sqArgs hx' (by simp only [NumObj.withRefs]; omega)
      (by simp only [List.length_cons]; omega) (ldv_store_hit _ _ _) hsz hmb5.word)
    h5.heap hO (sqrt_k (x := x.withRefs (x.rep.refs + 1)) hlive h5 hlk hsf hab hrq hrqs R _ h2 hal
      (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp []) m0 m24 m40 hm5 hret hfail hoom)
    (by bsimp []) (by bsimp [])

end Dc.Mach
