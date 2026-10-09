import Dc.Mach.Bc.SqrtScan

/-!
# `bc_sqrt`'s Newton loop (`0x80006b74` to `0x80006d68`)

    6b74 bc_free_num (&guess1)                       (guess1 in s10, maybe NULL)
    6ba0 guess1 = copy (guess); bc_divide (*num, guess, &guess, cscale)
    6bc0 bc_add (guess, guess1, &guess, 0); bc_multiply (guess, point5, &guess, cscale)
    6be8 bc_sub (guess, guess1, &diff, cscale + 1)
    6c04 near zero (`sq_scan`)? 6d44: rscale < cscale: done (6d68), else
         cscale = MIN (3 cscale, rscale + 1); 6c44 back to 6b74

- `SqEnv`: the loop's fixed facts; `SqCst`: the constants it reads.
- `SqF`: the fixed registers and frame words; `SqP`: the handles
  `[point5, diff, guess] ++ T` with `guess` holding `g`; `SqL`: at the head,
  `T` the `guess1` (`s10`).
- `sq_free1`: the head's free; `sq_step`: one iteration to the scan's two
  exits (`SqN`); `sq_loop`: the loop against `Dc.SqrtLoop`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The ceiling of the working scales for `x` at scale `k`. -/
abbrev sqc (x : NumObj) (k : Nat) : Nat := Dc.BcModel.sqC x.rep.num k

/-- The digits of the loop's numbers at most. -/
abbrev sqB (x : NumObj) (k : Nat) : Nat := x.rep.len + 3 * sqc x k + 5

/-- A loop number's digits: a magnitude below `10 ^ E` at a scale at most
`sqc + 1`. -/
theorem sq_size {y : NumRep} (hs : NumShape y) (hn : y.Norm) {x : NumObj} {k : Nat}
    (hm : y.num.mag < 10 ^ (x.rep.len + 2 * sqc x k + 3)) (hsc : y.scale ≤ sqc x k + 1) :
    y.len + y.scale ≤ sqB x k := by
  have := NumRep.size_le hs hn hm
  show y.len + y.scale ≤ x.rep.len + 3 * sqc x k + 5
  omega

/-- `_zero_` (as the loop's heap holds it), `_one_` and the multiplication
base as the loop reads them. -/
structure SqCst (M : Mem) (zb o : NumObj) : Prop where
  zero : KZero M zb (2 ^ 30 + 4)
  one : ldv .ld M oneAddr = BitVec.ofNat 64 o.rep.p
  mulBase : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80

/-- The constants survive a run that changes only the heap and the window. -/
theorem SqCst.transport {S : Nat → Prop} {Mt0 M : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {zb o : NumObj} (cx : SqCtx S R0 sp W q) (ha : SqCst Mt0 zb o)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) : SqCst M zb o := by
  have hab := cx.cc.above
  simp only [heapEnd] at hab
  have hc : ∀ a, 0x8001cd40 ≤ a → a < 0x8001cdd0 → ¬ (0x8001cd48 ≤ a ∧ a < 0x8001cd58) →
      ¬ (0x8001cdb0 ≤ a ∧ a < 0x8001cdb8) → imgM M a = imgM Mt0 a := fun a h1 h2 h3 h4 =>
    hout a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [frameIn]; omega)
  have hz := ha.zero
  refine ⟨⟨?_, hz.len, hz.scale, hz.ds, hz.neg, hz.refs, hz.room⟩, ?_, ?_⟩
  · rw [ldv_congr .ld fun j hj => hc _ (by simp only [widthOfM, zeroAddr] at hj ⊢; omega)
      (by simp only [widthOfM, zeroAddr] at hj ⊢; omega) (by simp only [widthOfM, zeroAddr] at hj ⊢; omega)
      (by simp only [widthOfM, zeroAddr] at hj ⊢; omega)]
    exact hz.glob
  · rw [ldv_congr .ld fun j hj => hc _ (by simp only [widthOfM, oneAddr] at hj ⊢; omega)
      (by simp only [widthOfM, oneAddr] at hj ⊢; omega) (by simp only [widthOfM, oneAddr] at hj ⊢; omega)
      (by simp only [widthOfM, oneAddr] at hj ⊢; omega)]
    exact ha.one
  · rw [ldv_congr .lw fun j hj => hc _ (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)
      (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)
      (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)
      (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)]
    exact ha.mulBase

/-- The loop's fixed facts: the context, the caller's heap `Lb` (the leak
taken) of owners with `x` (positive, normalized) and `_zero_` (`zb`) in it,
`rscale` (`rs`), `point5` (`p5`). -/
structure SqEnv (S : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64) (sp W q : Nat)
    (Lb : List NumObj) (x zb o p5 : NumObj) (k rs : Nat) : Prop where
  cx : SqCtx S R0 sp W q
  cst : SqCst Mt0 zb o
  owns : ∀ y ∈ Lb, y.Owns
  mx : x ∈ Lb
  mz : zb ∈ Lb
  nx : x.rep.Norm
  lenx : 1 ≤ x.rep.len
  xneg : x.rep.num.neg = false
  size : x.rep.len + x.rep.scale + k < 2 ^ 20
  rsk : rs = max k x.rep.scale
  refs : ∀ y ∈ Lb, y.rep.refs + 8 < 2 ^ 31
  p5num : p5.rep.num = Num.half
  p5len : p5.rep.len = 1
  p5scale : p5.rep.scale = 1
  p5norm : p5.rep.Norm
  p5ok : RHOK Lb (.own p5)

/-! ## The frame of the loop -/

/-- The loop's fixed registers inside the frame: `s1` (`&guess`), `s3`
(`num`), `s4` (`point5`), `s5` (`1`), `s6` (`rscale + 1`), `s7`
(`&_bc_Free_list`), `s8` (`rscale`); `*num` and `&_one_` at `sp - 160 + 8`. -/
structure SqF (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (x p5 : NumObj) (rs : Nat) : Prop where
  sa : SqAt S Mt0 M R0 R sp W sqSlots1
  r9 : R 9 = BitVec.ofNat 64 (sp - 160 + 24)
  r19 : R 19 = BitVec.ofNat 64 q
  r20 : R 20 = BitVec.ofNat 64 p5.rep.p
  r21 : R 21 = 1#64
  r22 : R 22 = BitVec.ofNat 64 (rs + 1)
  r23 : R 23 = BitVec.ofNat 64 bcFreeAddr
  r24 : R 24 = BitVec.ofNat 64 rs
  wq : ldv .ld M q = BitVec.ofNat 64 x.rep.p
  w8 : ldv .ld M (sp - 160 + 8) = BitVec.ofNat 64 oneAddr

/-- The registers the loop's steps may change. -/
abbrev sqFree : List Nat :=
  [1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 25, 26, 27, 28, 29, 30, 31]

/-- Through register changes off the fixed ones. -/
theorem SqF.regs {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {x p5 : NumObj} {rs : Nat} (h : SqF S Mt0 M R0 R sp W q x p5 rs) {ks : List Nat}
    (hk : Keeps ks R' R) (hks : ∀ z ∈ ks, z ∈ sqFree := by decide) :
    SqF S Mt0 M R0 R' sp W q x p5 rs where
  sa := h.sa.regs hk fun z hz => by
    have := hks z hz
    simp only [sqFree, sqAll, List.mem_cons, List.not_mem_nil, or_false] at this ⊢; omega
  r9 := by rw [hk.get 9 fun hm => by have := hks 9 hm; simp at this]; exact h.r9
  r19 := by rw [hk.get 19 fun hm => by have := hks 19 hm; simp at this]; exact h.r19
  r20 := by rw [hk.get 20 fun hm => by have := hks 20 hm; simp at this]; exact h.r20
  r21 := by rw [hk.get 21 fun hm => by have := hks 21 hm; simp at this]; exact h.r21
  r22 := by rw [hk.get 22 fun hm => by have := hks 22 hm; simp at this]; exact h.r22
  r23 := by rw [hk.get 23 fun hm => by have := hks 23 hm; simp at this]; exact h.r23
  r24 := by rw [hk.get 24 fun hm => by have := hks 24 hm; simp at this]; exact h.r24
  wq := h.wq
  w8 := h.w8

/-- Through a change of the heap alone. -/
theorem SqF.heap {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {x p5 : NumObj} {rs : Nat} (cx : SqCtx S R0 sp W q) (h : SqF S Mt0 M R0 R sp W q x p5 rs)
    (hag : ∀ a, OutHeap a → imgM M' a = imgM M a) : SqF S Mt0 M' R0 R sp W q x p5 rs := by
  sq_facts cx
  have hsl := cx.slot
  exact
    { h with
      sa := h.sa.heap cx (hag := hag)
      wq := by
        rw [ldv_congr .ld fun j hj => hag _ (hsl.out _ (by simp only [slotBytes, widthOfM] at hj ⊢; omega))]
        exact h.wq
      w8 := by
        rw [ldv_congr .ld fun j hj => hag _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))]
        exact h.w8 }

/-- Through a callee that changes the caller-saved registers and, off the
heap, the frame word at `o` (`16 ≤ o`) and the bytes below the frame. -/
theorem SqF.call {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {x p5 : NumObj} {rs o : Nat} (cx : SqCtx S R0 sp W q) (h : SqF S Mt0 M R0 R sp W q x p5 rs)
    (ho : 16 ≤ o) (ho' : o + 8 ≤ 48) (hk' : Keeps raCallClob R' R)
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - 160 + o) a → ¬ frameIn (sp - 160) (W - 160) a →
      imgM M' a = imgM M a) :
    SqF S Mt0 M' R0 R' sp W q x p5 rs := by
  sq_facts cx
  have hsl := cx.slot
  have hap := hsl.apart
  have hag : ∀ a, OutHeap a → ¬ (sp - 160 ≤ a ∧ a < sp - 112) →
      ¬ frameIn (sp - 160) (W - 160) a → imgM M' a = imgM M a := fun a h1 h2 h3 =>
    hout a h1 (by simp only [slotBytes]; omega) h3
  exact
    { sa := h.sa.call (hsp := by omega) (hW := by omega) (hkp := hk') (hag := hag)
        (hst := fun a h1 _ => outHeap_of_ge (by simp only [heapEnd]; omega))
      r9 := by rw [hk'.get 9 (by decide)]; exact h.r9
      r19 := by rw [hk'.get 19 (by decide)]; exact h.r19
      r20 := by rw [hk'.get 20 (by decide)]; exact h.r20
      r21 := by rw [hk'.get 21 (by decide)]; exact h.r21
      r22 := by rw [hk'.get 22 (by decide)]; exact h.r22
      r23 := by rw [hk'.get 23 (by decide)]; exact h.r23
      r24 := by rw [hk'.get 24 (by decide)]; exact h.r24
      wq := by
        rw [ldv_congr .ld fun j hj => hout _ (hsl.out _ (by simp only [slotBytes, widthOfM] at hj ⊢; omega)) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
        exact h.wq
      w8 := by
        rw [ldv_congr .ld fun j hj => hout _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega)) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
          (by simp only [frameIn, widthOfM] at hj ⊢; omega)]
        exact h.w8 }

/-- A frame word apart from a callee's slot. -/
theorem sq_word2 {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp W q : Nat} {M M' : Mem}
    (cx : SqCtx S R0 sp W q) {o o' : Nat} (ho : o ≤ 40) (hoo : o + 8 ≤ o' ∨ o' + 8 ≤ o)
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - 160 + o') a → ¬ frameIn (sp - 160) (W - 160) a →
      imgM M' a = imgM M a) :
    ldv .ld M' (sp - 160 + o) = ldv .ld M (sp - 160 + o) := by
  sq_facts cx
  exact ldv_congr .ld fun j hj => hout _ (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))
    (by simp only [slotBytes, widthOfM] at hj ⊢; omega) (by simp only [frameIn, widthOfM] at hj ⊢; omega)

/-! ## The loop's state -/

/-- The handles `[point5, diff, guess] ++ T`, `guess` holding the model's
guess `g` at the working scale `cs` (`SqG`), `diff` and `guess` in their
frame words, `guess` in `s0`, `cscale` in `s11` and `cscale + 1` in `s2`. -/
structure SqP (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (Lb : List NumObj) (x zb p5 : NumObj) (k rs cs : Nat)
    (D G : RH) (T : List RH) (g : Num) : Prop where
  f : SqF S Mt0 M R0 R sp W q x p5 rs
  heap : BcHeap S M H F (RList ([.own p5, D, G] ++ T) Lb)
  own : RHOwn ([.own p5, D, G] ++ T) Lb
  okD : RHOK Lb D
  okG : RHOK Lb G
  okT : ∀ h ∈ T, RHOK Lb h
  vG : G.base.rep.num = g
  nG : G.base.rep.Norm
  lG : 1 ≤ G.base.rep.len
  gx : G.p ≠ x.rep.p
  gz : G.p ≠ zb.rep.p
  model : Dc.BcModel.SqG x.rep.num (sqc x k) g cs
  w24 : ldv .ld M (sp - 160 + 24) = BitVec.ofNat 64 G.p
  w40 : ldv .ld M (sp - 160 + 40) = BitVec.ofNat 64 D.p
  r8 : R 8 = BitVec.ofNat 64 G.p
  r18 : R 18 = BitVec.ofNat 64 (cs + 1)
  r27 : R 27 = BitVec.ofNat 64 cs

/-- The state at the loop's head: `T` is `guess1` (`s10`, `NULL` for none). -/
structure SqL (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (Lb : List NumObj) (x zb p5 : NumObj) (k rs cs : Nat)
    (D G : RH) (G1 : Option RH) (g : Num) : Prop
    extends SqP S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G G1.toList g where
  r26 : R 26 = BitVec.ofNat 64 ((G1.map RH.p).getD 0)

/-- Through register changes off the state's. -/
theorem SqP.regs {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {T : List RH} {g : Num}
    (h : SqP S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G T g) {ks : List Nat}
    (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] :=
      by decide) :
    SqP S Mt0 M R0 R' sp W q H F Lb x zb p5 k rs cs D G T g :=
  { h with
    f := h.f.regs hk fun z hz => by
      have := hks z hz
      simp only [sqFree, List.mem_cons, List.not_mem_nil, or_false] at this ⊢; omega
    r8 := by rw [hk.get 8 fun hm => by have := hks 8 hm; simp at this]; exact h.r8
    r18 := by rw [hk.get 18 fun hm => by have := hks 18 hm; simp at this]; exact h.r18
    r27 := by rw [hk.get 27 fun hm => by have := hks 27 hm; simp at this]; exact h.r27 }

/-! ## The head's free (`0x80006b74`) -/

/-- **`bc_free_num (&guess1)`** at the head: on to `0x80006ba0` with the
handles `[point5, diff, guess]`. -/
theorem sq_free1 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb o p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {G1 : Option RH} {g : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs)
    (st : SqL S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G G1 g)
    (hnext : ∀ R' M' H' F', SqP S Mt0 M' R0 R' sp W q H' F' Lb x zb p5 k rs cs D G [] g →
      DW live S Q 0x80006ba0#64 R' M') :
    DW live S Q 0x80006b74#64 R M := by
  have cx := env.cx
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  cases G1 with
  | none =>
    exact fnull_80006b74 hlive hS (by rw [st.r26]; rfl) (hnext R M H F st.toSqP)
  | some h1 =>
    have hok := st.okT h1 (by simp)
    obtain ⟨L1, L2, xo, e, hp, hr, hnv, _, _, hfr⟩ :=
      RList.slot (hs1 := [.own p5, D, G]) (h := h1) (hs2 := []) hb hok st.own
    have hb' : BcHeap S M H F (L1 ++ xo :: L2) := by rw [← e]; exact hb
    have hx : R 26 = BitVec.ofNat 64 xo.rep.p := by rw [hp, st.r26]; rfl
    have k : FreeK [1, 10, 14, 15] live S Q 0x80006ba0#64 R M (fun _ => False) H F L1 L2 xo :=
      fun R' M' H' F' L' hk hkf hb1 hof => by
        have hL : L' = RList ([.own p5, D, G] ++ []) Lb := hfr L' hkf.rest
        subst hL
        have hag : ∀ a, OutHeap a → imgM M' a = imgM M a := fun a ha => hof a ha id
        have own' : RHOwn ([.own p5, D, G] ++ []) Lb :=
          (show RHOwn ([.own p5, D, G] ++ h1 :: []) Lb from st.own).drop
        have sq := cx.cc
        sq_facts cx
        exact hnext R' M' H' F'
          { (st.toSqP.regs hk) with
            f := (st.f.heap cx hag).regs hk
            heap := hb1
            own := own'
            okT := fun _ h => by simp at h
            w24 := by rw [sq_word cx (by omega) fun a ha _ _ => hag a ha]; exact st.w24
            w40 := by rw [sq_word cx (by omega) fun a ha _ _ => hag a ha]; exact st.w40 }
    exact ffree_80006b74 hlive hb' hr hnv hx st.f.r23 k k k

/-! ## Bounds -/

/-- A handle's object holds at most four references more than its own. -/
theorem RH.obj_refs_le {hs : List RH} {h : RH} {L : List NumObj} (hok : RHOK L h)
    (hL : ∀ y ∈ L, y.rep.refs + 8 < 2 ^ 31) (hl : hs.length ≤ 4) :
    (RH.obj hs h).rep.refs + 4 < 2 ^ 31 := by
  cases h with
  | own y => have := hok.1; simp only [RH.obj]; omega
  | ref y =>
    obtain ⟨A, B, e, _⟩ := hok
    have hy := hL y (by rw [e]; simp)
    have := rCnt_le hs y.rep.p
    simp only [RH.obj, NumObj.withRefs_refs]
    unfold rCnt at this
    omega

/-- The ceiling of the working scales. -/
theorem SqEnv.sqc_eq {S : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {Lb : List NumObj} {x zb o p5 : NumObj} {k rs : Nat}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) : sqc x k = max 3 (rs + 1) := by
  simp only [sqc, Dc.BcModel.sqC, NumRep.num_scale, env.rsk]

/-- `x` below `10 ^ (n_len + n_scale)`. -/
theorem sq_xmag {x : NumObj} (hs : NumShape x.rep) :
    x.rep.num.mag < 10 ^ (x.rep.len + x.rep.num.scale) :=
  NumRep.mag_lt hs

/-- A guess's digits. -/
theorem SqEnv.gsize {S : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {Lb : List NumObj} {x zb o p5 : NumObj} {k rs : Nat}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs)
    (hxs : x.rep.num.mag < 10 ^ (x.rep.len + x.rep.num.scale)) {y : NumRep}
    (hy : NumShape y) (hn : y.Norm) {g : Num} {cs : Nat} (hv : y.num = g)
    (hm : Dc.BcModel.SqG x.rep.num (sqc x k) g cs) : y.len + y.scale ≤ sqB x k := by
  have hc := env.sqc_eq
  have hxsc : x.rep.num.scale ≤ sqc x k := by
    rw [hc, NumRep.num_scale, env.rsk]; omega
  refine sq_size hy hn ?_ ?_
  · rw [hv]; exact hm.toSqInv.mag_lt hxsc hxs
  · rw [← NumRep.num_scale, hv]; have := hm.scale; have := hm.le; omega

/-- A step's number's digits: below `10 ^ E` at scale at most `cs + 1`. -/
theorem SqEnv.ssize {S : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {Lb : List NumObj} {x zb o p5 : NumObj} {k rs : Nat}
    (_env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) {y : NumRep} (hy : NumShape y) (hn : y.Norm)
    {cs : Nat} (hcs : cs ≤ sqc x k) (hm : y.num.mag < 10 ^ (x.rep.len + 2 * sqc x k + 3))
    (hsc : y.num.scale ≤ cs + 1) : y.len + y.scale ≤ sqB x k :=
  sq_size hy hn hm (by rw [← NumRep.num_scale]; omega)

/-- The digits of the loop's numbers, for the callees. -/
theorem SqEnv.bsmall {S : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {Lb : List NumObj} {x zb o p5 : NumObj} {k rs : Nat}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) : sqB x k + sqc x k < 2 ^ 23 := by
  have hc := env.sqc_eq
  have := env.size; have := env.rsk
  simp only [sqB] at *
  omega

/-- The step's values from the quotient. -/
theorem sqrtStep_of_div {x g q : Num} {cs : Nat} (hq : Num.div x g cs = some q) :
    Num.sqrtStep x g cs = (Num.mul (Num.add q g 0) Num.half cs,
      Num.sub (Num.mul (Num.add q g 0) Num.half cs) g (cs + 1)) := by
  simp only [Num.sqrtStep, hq, Option.getD_some]

/-! ## One iteration -/

/-- The state between the step's callees: the handles `[point5, diff, y,
guess1]`, `y` in `guess`'s word, `guess1` (the old `guess`) in `s0`. -/
structure SqM (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (Lb : List NumObj) (x zb p5 : NumObj) (k rs cs : Nat)
    (D G : RH) (y : NumObj) (g : Num) : Prop where
  f : SqF S Mt0 M R0 R sp W q x p5 rs
  heap : BcHeap S M H F (RList [.own p5, D, .own y, G] Lb)
  own : RHOwn [.own p5, D, .own y, G] Lb
  okD : RHOK Lb D
  okG : RHOK Lb G
  oky : RHOK Lb (.own y)
  vG : G.base.rep.num = g
  nG : G.base.rep.Norm
  lG : 1 ≤ G.base.rep.len
  gx : G.p ≠ x.rep.p
  gz : G.p ≠ zb.rep.p
  model : Dc.BcModel.SqG x.rep.num (sqc x k) g cs
  ny : y.rep.Norm
  ly : 1 ≤ y.rep.len
  w24 : ldv .ld M (sp - 160 + 24) = BitVec.ofNat 64 y.rep.p
  w40 : ldv .ld M (sp - 160 + 40) = BitVec.ofNat 64 D.p
  r8 : R 8 = BitVec.ofNat 64 G.p
  r18 : R 18 = BitVec.ofNat 64 (cs + 1)
  r27 : R 27 = BitVec.ofNat 64 cs

/-- **`guess1 = copy (guess)` and the quotient** from `0x80006ba0`: on to
`0x80006bc0` with the quotient in `guess`. -/
theorem sq_div {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb o p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {g : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) (hoom : RaOom live S Q Mt0 sp W q)
    (st : SqP S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G [] g)
    (hnext : ∀ R' M' H' F' y m, Num.div x.rep.num g cs = some m → y.rep.num = m →
      SqM S Mt0 M' R0 R' sp W q H' F' Lb x zb p5 k rs cs D G y g →
      DW live S Q 0x80006bc0#64 R' M') :
    DW live S Q 0x80006ba0#64 R M := by
  have cx := env.cx
  sq_facts cx
  have hsf := cx.cc.frame
  have hb : BcHeap S M H F (RList [.own p5, D, G] Lb) := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.f.sa
  have h2 := ra.r2
  have hcs := env.cst.transport cx ra.out
  have objG : RH.obj [.own p5, D, G] G ∈ RList [.own p5, D, G] Lb := RH.obj_mem (by simp) st.okG
  have hGn := hb.nums _ objG
  num_facts hGn
  have hGp : (RH.obj [.own p5, D, G] G).rep.p = G.p := RH.obj_p _ _
  have hrf : ldv .lw M (G.p + 12) = BitVec.ofNat 64 (RH.obj [.own p5, D, G] G).rep.refs := by
    rw [← hGp]; exact hGn.refs
  have hroom := RH.obj_refs_le (hs := [.own p5, D, G]) st.okG env.refs (by simp)
  have hxm := RList.mem_caller [.own p5, D, G] env.mx
  have hxn := hb.nums _ hxm
  have hxs : x.rep.num.mag < 10 ^ (x.rep.len + x.rep.num.scale) := by
    have := NumRep.mag_lt hxn.shape; exact this
  have hGs := env.gsize hxs hGn.shape ((RH.obj_norm _ _).mpr st.nG)
    (by rw [RH.obj_num]; exact st.vG) st.model
  have hbs := env.bsmall
  have hsz := env.size
  have hcl := st.model.le
  have hlen := RH.obj_len [.own p5, D, G] G
  have hscl := RH.obj_scale [.own p5, D, G] G
  have hq := cx.slot.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hsx := sxw_ofNat (show (RH.obj [.own p5, D, G] G).rep.refs + 1 < 2 ^ 31 by omega)
  bc_run hlive hS [h2, st.r8, st.f.r19, st.f.wq, st.r27, st.f.r9, hrf, hsx] at 0x8000589c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hq.acc | skip
  refine sq_divH hlive (P := .own p5) (D := D) (G := G) (u := rBump [.own p5, D, G] x)
    (z := rBump [.own p5, D, G] zb) (k := cs) cx hoom (fun a ha _ hf => ra.out a ha hf) hb st.own
    st.okG (by omega) hxm (fun e => st.gx e.symm) (RList.mem_caller _ env.mz)
    (fun e => st.gz e.symm) (by
      have e1 : (rBump [.own p5, D, G] x).rep.len = x.rep.len := rfl
      have e2 : (rBump [.own p5, D, G] x).rep.scale = x.rep.scale := rfl
      rw [e1, e2]; omega)
    hcs.zero.glob (by show dval zb.rep.ds = 0; rw [hcs.zero.ds]; rfl) env.lenx
    (by rw [st.vG]; exact st.model.nz) st.w24 (by bsimp [h2]) (by bsimp []; try decide)
    (by bsimp [st.f.wq]; rfl) (by bsimp [st.r8]) (by bsimp [st.f.r9]) (by bsimp [st.r27]) ?_
  intro m hm R1 M1 H1 F1 y hk1 _ hb1 hown1 hres hout1
  bsimp []
  exact hnext R1 M1 H1 F1 y m (by rw [← st.vG]; exact hm) hres.num
    { f := st.f.call cx (o := 24) (by omega) (by omega)
        (((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps raCallClob _ _)))
        hout1
      heap := hb1
      own := hown1
      okD := st.okD
      okG := st.okG
      oky := ⟨hres.refs, hres.owns⟩
      vG := st.vG
      nG := st.nG
      lG := st.lG
      gx := st.gx
      gz := st.gz
      model := st.model
      ny := hres.norm
      ly := hres.pos
      w24 := hres.slot
      w40 := by rw [sq_word2 cx (o' := 24) (by omega) (by omega) hout1]; exact st.w40
      r8 := by rw [hk1.get 8 (by decide)]; bsimp [st.r8]
      r18 := by rw [hk1.get 18 (by decide)]; bsimp [st.r18]
      r27 := by rw [hk1.get 27 (by decide)]; bsimp [st.r27] }

/-- Through a callee on `guess`'s word: its new number `y'` in the word. -/
theorem SqM.next {S : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H H' : Heap} {F F' : List Blk} {Lb : List NumObj} {x zb p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {y y' : NumObj} {g n : Num} (cx : SqCtx S R0 sp W q)
    (st : SqM S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G y g) (hk : Keeps raCallClob R' R)
    (hb : BcHeap S M' H' F' (RList [.own p5, D, .own y', G] Lb))
    (hown : RHOwn [.own p5, D, .own y', G] Lb) (hres : MulRes M' (sp - 160 + 24) n y')
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - 160 + 24) a → ¬ frameIn (sp - 160) (W - 160) a →
      imgM M' a = imgM M a) :
    SqM S Mt0 M' R0 R' sp W q H' F' Lb x zb p5 k rs cs D G y' g :=
  { st with
    f := st.f.call cx (o := 24) (by omega) (by omega) hk hout
    heap := hb
    own := hown
    oky := ⟨hres.refs, hres.owns⟩
    ny := hres.norm
    ly := hres.pos
    w24 := hres.slot
    w40 := by rw [sq_word2 cx (o' := 24) (by omega) (by omega) hout]; exact st.w40
    r8 := by rw [hk.get 8 (by decide)]; exact st.r8
    r18 := by rw [hk.get 18 (by decide)]; exact st.r18
    r27 := by rw [hk.get 27 (by decide)]; exact st.r27 }

/-- **`bc_add (guess, guess1, &guess, 0)`** from `0x80006bc0`. -/
theorem sq_add {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb o p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {y : NumObj} {g : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) (hoom : RaOom live S Q Mt0 sp W q)
    (st : SqM S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G y g)
    (hsy : y.rep.len + y.rep.scale ≤ sqB x k) (hsg : G.base.rep.len + G.base.rep.scale ≤ sqB x k)
    (hnext : ∀ R' M' H' F' y', y'.rep.num = Num.add y.rep.num g 0 →
      SqM S Mt0 M' R0 R' sp W q H' F' Lb x zb p5 k rs cs D G y' g →
      DW live S Q 0x80006bd4#64 R' M') :
    DW live S Q 0x80006bc0#64 R M := by
  have cx := env.cx
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.f.sa
  have h2 := ra.r2
  have objG : RH.obj [.own p5, D, .own y, G] G ∈ RList [.own p5, D, .own y, G] Lb :=
    RH.obj_mem (by simp) st.okG
  have objy : y ∈ RList [.own p5, D, .own y, G] Lb :=
    RH.obj_mem (h := .own y) (by simp) st.oky
  have hlen := RH.obj_len [.own p5, D, .own y, G] G
  have hscl := RH.obj_scale [.own p5, D, .own y, G] G
  have hbs := env.bsmall
  have hly := st.ly; have hlG := st.lG
  bc_run hlive hS [h2, st.r8, st.f.r9, st.w24] at 0x80005634
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine sq_addH hlive (hs1 := [.own p5, D]) (h := .own y) (hs2 := [G]) (o := 24) (k := 0)
    (u1 := y) (u2 := RH.obj [.own p5, D, .own y, G] G) cx hoom (by omega) (by decide)
    (fun a ha _ hf => ra.out a ha hf) hb st.own st.oky
    { m1 := objy, m2 := objG, n1 := st.ny, n2 := (RH.obj_norm _ _).mpr st.nG
      size := by rw [hlen, hscl]; omega
      e1 := fun h => absurd h (by omega)
      e2 := fun h => absurd h (by omega) }
    hly (by rw [hlen]; exact hlG) st.w24 (by bsimp [h2]) (by bsimp []; try decide)
    (by bsimp [st.w24]) (by bsimp [st.r8, RH.obj_p]) (by bsimp [st.f.r9]) (by bsimp []) ?_
  intro R1 M1 H1 F1 y' hk1 hb1 hown1 hres hout1
  bsimp []
  refine hnext R1 M1 H1 F1 y' (by rw [hres.num, RH.obj_num, st.vG])
    (st.next cx ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps raCallClob _ _))
      hb1 hown1 hres hout1)

/-- **`bc_multiply (guess, point5, &guess, cscale)`** from `0x80006bd4`. -/
theorem sq_mul {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb o p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {y : NumObj} {g : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) (hoom : RaOom live S Q Mt0 sp W q)
    (st : SqM S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G y g)
    (hsy : y.rep.len + y.rep.scale ≤ sqB x k)
    (hnext : ∀ R' M' H' F' y', y'.rep.num = Num.mul y.rep.num Num.half cs →
      SqM S Mt0 M' R0 R' sp W q H' F' Lb x zb p5 k rs cs D G y' g →
      DW live S Q 0x80006be8#64 R' M') :
    DW live S Q 0x80006bd4#64 R M := by
  have cx := env.cx
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.f.sa
  have h2 := ra.r2
  have hcs := env.cst.transport cx ra.out
  have objy : y ∈ RList [.own p5, D, .own y, G] Lb :=
    RH.obj_mem (h := .own y) (by simp) st.oky
  have objp : p5 ∈ RList [.own p5, D, .own y, G] Lb :=
    RH.obj_mem (h := .own p5) (by simp) env.p5ok
  have hbs := env.bsmall
  have hly := st.ly; have hcl := st.model.le
  have hp5l := env.p5len; have hp5s := env.p5scale
  bc_run hlive hS [h2, st.r27, st.f.r9, st.f.r20, st.w24] at 0x8000573c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine sq_mulH hlive (hs1 := [.own p5, D]) (h := .own y) (hs2 := [G]) (o := 24) (k := cs)
    (u1 := y) (u2 := p5) (z := rBump [.own p5, D, .own y, G] zb) cx hoom (by omega) (by decide)
    (fun a ha _ hf => ra.out a ha hf) hb st.own st.oky
    { m1 := objy, m2 := objp, mz := RList.mem_caller _ env.mz
      p1 := by omega
      p2 := by omega
      size := by omega
      scale := by omega
      zero := KZero.rBump _ (by simp) (hcs.zero.mono (by omega))
      mulBase := hcs.mulBase }
    st.w24 (by bsimp [h2]) (by bsimp []; try decide)
    (by bsimp [st.w24]) (by bsimp [st.f.r20]) (by bsimp [st.f.r9]) (by bsimp [st.r27]) ?_
  intro R1 M1 H1 F1 y' hk1 hb1 hown1 hres hout1
  bsimp []
  refine hnext R1 M1 H1 F1 y' (by rw [hres.num, env.p5num])
    (st.next cx ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps raCallClob _ _))
      hb1 hown1 hres hout1)

/-- Through register changes off the state's. -/
theorem SqM.regs {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {y : NumObj} {g : Num}
    (h : SqM S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G y g) {ks : List Nat}
    (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 28, 29, 30, 31] :=
      by decide) :
    SqM S Mt0 M R0 R' sp W q H F Lb x zb p5 k rs cs D G y g :=
  { h with
    f := h.f.regs hk fun z hz => by
      have := hks z hz
      simp only [sqFree, List.mem_cons, List.not_mem_nil, or_false] at this ⊢; omega
    r8 := by rw [hk.get 8 fun hm => by have := hks 8 hm; simp at this]; exact h.r8
    r18 := by rw [hk.get 18 fun hm => by have := hks 18 hm; simp at this]; exact h.r18
    r27 := by rw [hk.get 27 fun hm => by have := hks 27 hm; simp at this]; exact h.r27 }

/-- The state at the scan's exits: the handles `[point5, d, y, guess1]`, the
difference `d` in `diff`'s word and `s10`, the new guess `y` in `guess`'s
word and `s9`. -/
structure SqN (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (Lb : List NumObj) (x zb p5 : NumObj) (k rs cs : Nat)
    (G : RH) (d y : NumObj) (g : Num) : Prop
    extends SqM S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs (.own d) G y g where
  r25 : R 25 = BitVec.ofNat 64 y.rep.p
  r26 : R 26 = BitVec.ofNat 64 d.rep.p

/-- **`bc_sub (guess, guess1, &diff, cscale + 1)` and the near-zero test**
from `0x80006be8`. -/
theorem sq_sub {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb o p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {y : NumObj} {g : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) (hoom : RaOom live S Q Mt0 sp W q)
    (st : SqM S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G y g)
    (hsy : y.rep.len + y.rep.scale ≤ sqB x k) (hsg : G.base.rep.len + G.base.rep.scale ≤ sqB x k)
    (hnear : ∀ R' M' H' F' d, d.rep.num = Num.sub y.rep.num g (cs + 1) →
      SqN S Mt0 M' R0 R' sp W q H' F' Lb x zb p5 k rs cs G d y g →
      d.rep.num.isNearZero cs = true → DW live S Q 0x80006d44#64 R' M')
    (hfar : ∀ R' M' H' F' d, d.rep.num = Num.sub y.rep.num g (cs + 1) →
      SqN S Mt0 M' R0 R' sp W q H' F' Lb x zb p5 k rs cs G d y g →
      d.rep.num.isNearZero cs = false → DW live S Q 0x80006c44#64 R' M') :
    DW live S Q 0x80006be8#64 R M := by
  have cx := env.cx
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.f.sa
  have h2 := ra.r2
  have objG : RH.obj [.own p5, D, .own y, G] G ∈ RList [.own p5, D, .own y, G] Lb :=
    RH.obj_mem (by simp) st.okG
  have objy : y ∈ RList [.own p5, D, .own y, G] Lb :=
    RH.obj_mem (h := .own y) (by simp) st.oky
  have hlen := RH.obj_len [.own p5, D, .own y, G] G
  have hscl := RH.obj_scale [.own p5, D, .own y, G] G
  have hbs := env.bsmall
  have hly := st.ly; have hlG := st.lG; have hcl := st.model.le
  bc_run hlive hS [h2, st.r8, st.r18, st.w24] at 0x80004ac4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine sq_subH hlive (hs1 := [.own p5]) (h := D) (hs2 := [.own y, G]) (o := 40) (k := cs + 1)
    (u1 := y) (u2 := RH.obj [.own p5, D, .own y, G] G) cx hoom (by omega) (by decide)
    (fun a ha _ hf => ra.out a ha hf) hb st.own st.okD
    { m1 := objy, m2 := objG, n1 := st.ny, n2 := (RH.obj_norm _ _).mpr st.nG
      size := by rw [hlen, hscl]; omega
      e1 := fun h => absurd h (by omega)
      e2 := fun h => absurd h (by omega) }
    hly (by rw [hlen]; exact hlG) st.w40 (by bsimp [h2]) (by bsimp []; try decide)
    (by bsimp [st.w24]) (by bsimp [st.r8, RH.obj_p]) (by bsimp [h2]) (by bsimp [st.r18]) ?_
  intro R1 M1 H1 F1 d hk1 hb1 hown1 hres hout1
  bsimp []
  have hk1' : Keeps raCallClob R1 (upd R 25 (BitVec.ofNat 64 y.rep.p)) :=
    (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _ : Keeps raCallClob _ _)
  have m1 : SqM S Mt0 M1 R0 R1 sp W q H1 F1 Lb x zb p5 k rs cs (.own d) G y g :=
    { st with
      f := (st.f.regs (by keeps_tac Keeps.refl _ _ :
          Keeps [25] (upd R 25 (BitVec.ofNat 64 y.rep.p)) R)).call cx (o := 40) (by omega) (by omega)
        hk1' hout1
      heap := hb1
      own := hown1
      okD := ⟨hres.refs, hres.owns⟩
      w24 := by rw [sq_word2 cx (o' := 40) (by omega) (by omega) hout1]; exact st.w24
      w40 := hres.slot
      r8 := by rw [hk1'.get 8 (by decide)]; bsimp [st.r8]
      r18 := by rw [hk1'.get 18 (by decide)]; bsimp [st.r18]
      r27 := by rw [hk1'.get 27 (by decide)]; bsimp [st.r27] }
  have h2' : R1 2 = BitVec.ofNat 64 (sp - 160) := m1.f.sa.r2
  have h25 : R1 25 = BitVec.ofNat 64 y.rep.p := by rw [hk1'.get 25 (by decide)]; bsimp []
  have objd : d ∈ RList [.own p5, .own d, .own y, G] Lb :=
    RH.obj_mem (h := .own d) (by simp) ⟨hres.refs, hres.owns⟩
  have hdn := hb1.nums _ objd
  have hdl := hres.pos
  have hS1 : HeapOwn S := fun a h1 h2 => hb1.heap.own a h1 h2
  have hv : d.rep.num = Num.sub y.rep.num g (cs + 1) := by
    rw [hres.num, RH.obj_num, st.vG]
  bc_run hlive hS1 [h2', hres.slot] at 0x80006c04
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine sq_scan hlive hS1 hdn hdl (s := cs) (by omega) _ (by bsimp []) (by bsimp [m1.r27])
    (by bsimp [m1.f.r21]) (fun R' hk hn => ?_) (fun R' hk hn => ?_)
  · have hk' : Keeps [13, 14, 15, 26] R' R1 :=
      (hk.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
    exact hnear R' M1 H1 F1 d hv
      { toSqM := m1.regs hk'
        r25 := by rw [hk'.get 25 (by decide)]; exact h25
        r26 := by rw [hk.get 26 (by decide)]; bsimp [] } hn
  · have hk' : Keeps [13, 14, 15, 26] R' R1 :=
      (hk.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
    exact hfar R' M1 H1 F1 d hv
      { toSqM := m1.regs hk'
        r25 := by rw [hk'.get 25 (by decide)]; exact h25
        r26 := by rw [hk.get 26 (by decide)]; bsimp [] } hn

/-! ## The near-zero branch (`0x80006d44`) -/

/-- **`rscale < cscale`: done; else `cscale = MIN (3 cscale, rscale + 1)`**
from `0x80006d44`. -/
theorem sq_near {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb o p5 : NumObj} {k rs cs : Nat}
    {G : RH} {d y : NumObj} {g : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs)
    (st : SqN S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs G d y g)
    (hexit : rs < cs → DW live S Q 0x80006d68#64 R M)
    (hrefine : cs ≤ rs → ∀ R',
      SqN S Mt0 M R0 R' sp W q H F Lb x zb p5 k rs (min (cs * 3) (rs + 1)) G d y g →
      DW live S Q 0x80006c44#64 R' M) :
    DW live S Q 0x80006d44#64 R M := by
  have hc := env.sqc_eq; have hbs := env.bsmall; have hcl := st.model.le
  have hp := st.model.pos
  simp only [sqB] at hbs
  dx_run hlive at 0x80006d68 0x80006c44
  all_goals bsimp [st.f.r24, st.r27, st.f.r22]
  · intro hlt
    rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hlt
    exact hexit (by omega)
  · intro hge
    rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hge
    have hcr : cs ≤ rs := by omega
    have tail : ∀ R', R' 18 = BitVec.ofNat 64 (min (cs * 3) (rs + 1)) → Keeps [15, 18] R' R →
        DW live S Q 0x80006d5c#64 R' M := by
      intro R' h18 hk
      have hk' : Keeps [15, 18, 27] R' R := hk.mono (by decide)
      have hx1 := sxw_ofNat (show min (cs * 3) (rs + 1) < 2 ^ 31 by omega)
      have hx2 := sxw_ofNat (show min (cs * 3) (rs + 1) + 1 < 2 ^ 31 by omega)
      dx_run hlive at 0x80006c44
      all_goals bsimp [h18, hx1, hx2]
      have hk2 : Keeps [15, 18, 27] (upd (upd R' 27 (BitVec.ofNat 64 (min (cs * 3) (rs + 1)))) 18
          (BitVec.ofNat 64 (min (cs * 3) (rs + 1) + 1))) R := by keeps_tac hk'
      exact hrefine hcr _
        { st with
          f := st.f.regs hk2
          model := st.model.mono (by omega) (by omega)
          r8 := by rw [hk2.get 8 (by decide)]; exact st.r8
          r18 := by bsimp []
          r27 := by bsimp []
          r25 := by rw [hk2.get 25 (by decide)]; exact st.r25
          r26 := by rw [hk2.get 26 (by decide)]; exact st.r26 }
    have hsl := slliw_ofNat (a := cs) (k := 1) (by omega)
    have haw := addw_ofNat (a := cs * 2 ^ 1) (b := cs) (by omega)
    dx_run hlive at 0x80006d68 0x80006c44 0x80006d5c
    all_goals bsimp [st.f.r24, st.r27, st.f.r22, hsl, haw]
    · intro h1
      rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at h1
      exact tail _ (by bsimp []; rw [Nat.min_eq_right (by omega)]) (by keeps_tac Keeps.refl _ _)
    · intro h1
      rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at h1
      dx_run hlive at 0x80006d5c
      exact tail _ (by bsimp []; rw [Nat.min_eq_left (by omega), show cs * 2 ^ 1 + cs = cs * 3 by omega])
        (by keeps_tac Keeps.refl _ _)

/-! ## One iteration and the loop -/

/-- `x`'s scale under the ceiling. -/
theorem SqEnv.xsc {S : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {Lb : List NumObj} {x zb o p5 : NumObj} {k rs : Nat}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) : x.rep.num.scale ≤ sqc x k := by
  rw [env.sqc_eq, NumRep.num_scale, env.rsk]; omega

/-- `x` below `10 ^ (n_len + n_scale)`, from any heap of the loop. -/
theorem SqEnv.xmag {S : Nat → Prop} {Mt0 M : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {Lb : List NumObj} {x zb o p5 : NumObj} {k rs : Nat} {H : Heap} {F : List Blk} {hs : List RH}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) (hb : BcHeap S M H F (RList hs Lb)) :
    x.rep.num.mag < 10 ^ (x.rep.len + x.rep.num.scale) := by
  have hxn := hb.nums _ (RList.mem_caller hs env.mx)
  have := NumRep.mag_lt hxn.shape; exact this

/-- The new number's digits between the step's callees. -/
theorem SqM.ysize {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb o p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {y : NumObj} {g n : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs)
    (st : SqM S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G y g) (hy : y.rep.num = n)
    (hm : n.mag < 10 ^ (x.rep.len + 2 * sqc x k + 3)) (hs : n.scale ≤ cs + 1) :
    y.rep.len + y.rep.scale ≤ sqB x k :=
  env.ssize (st.heap.nums _ (RH.obj_mem (h := .own y) (by simp) st.oky)).shape st.ny st.model.le
    (by rw [hy]; exact hm) (by rw [hy]; exact hs)

/-- The guess's digits between the step's callees. -/
theorem SqM.gsize {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb o p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {y : NumObj} {g : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs)
    (st : SqM S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G y g) :
    G.base.rep.len + G.base.rep.scale ≤ sqB x k := by
  have hGn := st.heap.nums _ (RH.obj_mem (hs := [.own p5, D, .own y, G]) (by simp) st.okG)
  have := env.gsize (env.xmag st.heap) hGn.shape ((RH.obj_norm _ _).mpr st.nG)
    (by rw [RH.obj_num]; exact st.vG) st.model
  rwa [RH.obj_len, RH.obj_scale] at this

/-- **One iteration** from the head `0x80006b74` to the near-zero test's
exits, the new guess `y` and difference `d` those of `Num.sqrtStep`. -/
theorem sq_step {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb o p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {G1 : Option RH} {g : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) (hoom : RaOom live S Q Mt0 sp W q)
    (st : SqL S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G G1 g)
    (hnear : ∀ R' M' H' F' d y, y.rep.num = (Num.sqrtStep x.rep.num g cs).1 →
      d.rep.num = (Num.sqrtStep x.rep.num g cs).2 →
      SqN S Mt0 M' R0 R' sp W q H' F' Lb x zb p5 k rs cs G d y g →
      d.rep.num.isNearZero cs = true → DW live S Q 0x80006d44#64 R' M')
    (hfar : ∀ R' M' H' F' d y, y.rep.num = (Num.sqrtStep x.rep.num g cs).1 →
      d.rep.num = (Num.sqrtStep x.rep.num g cs).2 →
      SqN S Mt0 M' R0 R' sp W q H' F' Lb x zb p5 k rs cs G d y g →
      d.rep.num.isNearZero cs = false → DW live S Q 0x80006c44#64 R' M') :
    DW live S Q 0x80006b74#64 R M := by
  refine sq_free1 hlive env st fun R1 M1 H1 F1 st1 => ?_
  refine sq_div hlive env hoom st1 fun R2 M2 H2 F2 y2 m hm hy2 st2 => ?_
  have hB := Dc.BcModel.sqStepB env.xneg env.xsc (env.xmag st2.heap) st2.model hm
  have hst := sqrtStep_of_div hm
  have hsg := st2.gsize env
  refine sq_add hlive env hoom st2 (st2.ysize env hy2 hB.qmag (by rw [hB.qscale]; omega)) hsg
    fun R3 M3 H3 F3 y3 hy3 st3 => ?_
  rw [hy2] at hy3
  refine sq_mul hlive env hoom st3 (st3.ysize env hy3 hB.amag (by rw [hB.ascale]; omega))
    fun R4 M4 H4 F4 y4 hy4 st4 => ?_
  rw [hy3] at hy4
  refine sq_sub hlive env hoom st4 (st4.ysize env hy4 hB.mmag (by rw [hB.mscale]; omega))
    (st4.gsize env) (fun R5 M5 H5 F5 d hd st5 hn => ?_) (fun R5 M5 H5 F5 d hd st5 hn => ?_)
  · rw [hy4] at hd
    exact hnear R5 M5 H5 F5 d y4 (by rw [hst, hy4]) (by rw [hst, hd]) st5 hn
  · rw [hy4] at hd
    exact hfar R5 M5 H5 F5 d y4 (by rw [hst, hy4]) (by rw [hst, hd]) st5 hn

/-- **The back edge** at `0x80006c44`: `guess1 = guess`, `guess = y`, on to
the head with the model's guess for `y`. -/
theorem sq_back {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {Lb : List NumObj} {x zb o p5 : NumObj} {k rs cs : Nat}
    {G : RH} {d y : NumObj} {g : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs)
    (st : SqN S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs G d y g)
    (hm : Dc.BcModel.SqG x.rep.num (sqc x k) y.rep.num cs)
    (hnext : ∀ R', SqL S Mt0 M R0 R' sp W q H F Lb x zb p5 k rs cs (.own d) (.own y) (some G)
      y.rep.num → DW live S Q 0x80006b74#64 R' M) :
    DW live S Q 0x80006c44#64 R M := by
  dx_run hlive at 0x80006b74
  bsimp [st.r8, st.r25]
  have hk : Keeps [8, 26] (upd (upd R 26 (BitVec.ofNat 64 G.p)) 8 (BitVec.ofNat 64 y.rep.p)) R := by
    keeps_tac Keeps.refl _ _
  have hd := st.heap.pdist
  exact hnext _
    { f := st.f.regs hk
      heap := st.heap
      own := st.own
      okD := st.okD
      okG := st.oky
      okT := fun h hh => by simp only [Option.toList, List.mem_singleton] at hh; subst hh; exact st.okG
      vG := rfl
      nG := st.ny
      lG := st.ly
      gx := RList.own_ne_caller hd (by simp) env.mx
      gz := RList.own_ne_caller hd (by simp) env.mz
      model := hm
      w24 := st.w24
      w40 := st.w40
      r8 := by bsimp []; rfl
      r18 := by rw [hk.get 18 (by decide)]; exact st.r18
      r27 := by rw [hk.get 27 (by decide)]; exact st.r27
      r26 := by bsimp []; rfl }

/-- **The Newton loop** against `Dc.SqrtLoop`: from the head with the
model's guess `g` at `cs`, out at `0x80006d68` with the last guess `y`,
`rscale < cs'`, and the loop's result `Num.sqrtFinish y rscale`. -/
theorem sq_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {Lb : List NumObj} {x zb o p5 : NumObj} {k rs : Nat}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) (hoom : RaOom live S Q Mt0 sp W q)
    {g : Num} {cs : Nat} {r : Num} (hL : Dc.SqrtLoop x.rep.num rs g cs r)
    (hexit : ∀ R' M' H' F' cs' G d y g',
      SqN S Mt0 M' R0 R' sp W q H' F' Lb x zb p5 k rs cs' G d y g' → rs < cs' →
      r = Num.sqrtFinish y.rep.num rs → DW live S Q 0x80006d68#64 R' M') :
    ∀ R M H F D G G1, SqL S Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G G1 g →
      DW live S Q 0x80006b74#64 R M := by
  have hrs : rs = max k x.rep.num.scale := by rw [NumRep.num_scale]; exact env.rsk
  revert hexit
  induction hL with
  | @finish g cs hn hc =>
    intro hexit R M H F D G G1 st
    refine sq_step hlive env hoom st (fun R' M' H' F' d y hy hd st' hz => ?_)
      (fun R' M' H' F' d y hy hd st' hz => ?_)
    · exact sq_near hlive env st' (fun hlt => hexit _ _ _ _ _ _ _ _ _ st' hlt (by rw [hy]))
        (fun hle => absurd hle (by omega))
    · rw [hd, hn] at hz; exact absurd hz (by decide)
  | @refine g cs r hn hc _ ih =>
    intro hexit R M H F D G G1 st
    refine sq_step hlive env hoom st (fun R' M' H' F' d y hy hd st' hz => ?_)
      (fun R' M' H' F' d y hy hd st' hz => ?_)
    · have h1 : Dc.BcModel.SqG x.rep.num (sqc x k) y.rep.num cs := by
        rw [hy]; exact Dc.BcModel.sqG_step env.xneg env.xsc st'.model
      refine sq_near hlive env st' (fun hlt => absurd hlt (by omega)) fun _ R'' st'' => ?_
      have h2 : Dc.BcModel.SqG x.rep.num (sqc x k) y.rep.num (min (cs * 3) (rs + 1)) := by
        rw [hrs]; exact Dc.BcModel.sqG_refine h1 (by omega)
      refine sq_back hlive env st'' h2 fun R3 st3 => ?_
      rw [hy] at st3
      exact ih hexit R3 _ _ _ _ _ _ st3
    · rw [hd, hn] at hz; exact absurd hz (by decide)
  | @iterate g cs r hn _ ih =>
    intro hexit R M H F D G G1 st
    refine sq_step hlive env hoom st (fun R' M' H' F' d y hy hd st' hz => ?_)
      (fun R' M' H' F' d y hy hd st' hz => ?_)
    · rw [hd, hn] at hz; exact absurd hz (by decide)
    · have h1 : Dc.BcModel.SqG x.rep.num (sqc x k) y.rep.num cs := by
        rw [hy]; exact Dc.BcModel.sqG_step env.xneg env.xsc st'.model
      refine sq_back hlive env st' h1 fun R3 st3 => ?_
      rw [hy] at st3
      exact ih hexit R3 _ _ _ _ _ _ st3

end Dc.Mach
