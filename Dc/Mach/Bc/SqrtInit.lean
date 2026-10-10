import Dc.Mach.Bc.SqrtExit
import Dc.BcModel.SqrtInit

/-!
# `bc_sqrt`'s first guess (`0x80006ad4`, `0x80006d04`)

```
80006ad4 addi s1,sp,24 ; 80006ad8 mv a0,s1 ; 80006adc li a1,10 ; 80006ae0 jal bc_int2num
80006ae4 ld a5,0(s3) ; 80006ae8 addi a0,sp,32 ; 80006aec lw a1,4(a5) ; 80006af0 jal bc_int2num
80006af4 ld a0,32(sp) ; 80006af8 addi a2,sp,32 ; 80006afc mv a1,s4 ; 80006b00 li a3,0
80006b04 jal bc_multiply ; 80006b08 ld s0,32(sp) ; 80006b0c ld a0,24(sp) ; 80006b10 mv a2,s1
80006b14 sw zero,8(s0) ; 80006b18 mv a1,s0 ; 80006b1c li a3,0 ; 80006b20 jal bc_raise
80006b24 (bc_free_num (&guess1) inlined) ; 80006b54 ld s0,24(sp) ; 80006b58 li s11,3
80006b5c li s10,0 ; 80006b60 addiw s2,s11,1 ; 80006b64 auipc s7 ; 80006b68 addi s7 (&_bc_Free_list)
80006b6c addiw s6,s8,1 ; 80006b70 li s5,1

80006d04 ld a5,8(sp) ; 80006d08 ld a4,0(s3) ; 80006d0c addi s1,sp,24 ; 80006d10 ld s0,0(a5)
80006d14 lw s11,8(a4) ; 80006d18 auipc s7 ; 80006d1c addi s7 ; 80006d20 lw a5,12(s0)
80006d24 sd s0,24(sp) ; 80006d28 addiw s2,s11,1 ; 80006d2c addiw a5,a5,1 ; 80006d30 sw a5,12(s0)
80006d34 addiw s6,s8,1 ; 80006d38 li s5,1 ; 80006d3c j 80006b74
```

Above one the guess is `bc_raise (10, n_len * 0.5 cut to scale 0)`, into
the guess's handle (`raPost_handle`: a new number, the old guess, or one more
reference to `_one_`); below one it is one more reference to `_one_`, and the
guess slot's `_zero_` reference is the one `bc_sqrt` leaks (`RList.leak`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## Numbers of the heap by pointer -/

/-- Two numbers of a list of distinct pointers at one pointer are one. -/
theorem PDist.eq {L : List NumObj} (hd : PDist L) {a b : NumObj} (ha : a ∈ L) (hb : b ∈ L)
    (hp : a.rep.p = b.rep.p) : a = b := by
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem ha
  rcases List.mem_append.mp hb with h | h
  · exact absurd hp.symm (hd.ne b (List.mem_append_left _ h))
  rcases List.mem_cons.mp h with h | h
  · exact h.symm
  · exact absurd hp.symm (hd.ne b (List.mem_append_right _ h))

/-- Lists with the same pointers. -/
theorem PDist.congr {L L' : List NumObj} (hd : PDist L) (h : L.map (·.rep.p) = L'.map (·.rep.p)) :
    PDist L' := by
  unfold PDist at *; rw [← h]; exact hd

/-- Dropping at `p` from `y :: L`: `y` itself, or a number of `L`. -/
theorem DropAt.cons_cases {L L' : List NumObj} {y : NumObj} {p : Nat} (h : DropAt (y :: L) p L') :
    (y.rep.p = p ∧ FreedRest [] L y L') ∨ ∃ L'', DropAt L p L'' ∧ L' = y :: L'' := by
  obtain ⟨L1, L2, x, e, hp, hf⟩ := h
  cases L1 with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact .inl ⟨hp, hf⟩
  | cons w L1 =>
    simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    cases hf with
    | dec h2 => exact .inr ⟨_, ⟨L1, L2, x, rfl, hp, .dec h2⟩, rfl⟩
    | rel h1 => exact .inr ⟨_, ⟨L1, L2, x, rfl, hp, .rel h1⟩, rfl⟩

/-- A reference handle anywhere among the handles: the counts are sums. -/
theorem RList.ref_last (hs1 hs2 : List RH) (y : NumObj) (L : List NumObj) :
    RList (hs1 ++ .ref y :: hs2) L = RList (hs1 ++ hs2 ++ [.ref y]) L := by
  have ht : rTemps (hs1 ++ .ref y :: hs2) = rTemps (hs1 ++ hs2 ++ [.ref y]) := by
    simp only [rTemps_append, rTemps_ref, rTemps_nil, List.append_nil]
  have hb : rBump (hs1 ++ .ref y :: hs2) = rBump (hs1 ++ hs2 ++ [.ref y]) := by
    funext w
    simp only [rBump, rCnt_mid, rCnt_append, rCnt_cons, show rCnt [] w.rep.p = 0 from rfl]
    congr 2; omega
  simp only [RList, ht, hb]

/-! ## `bc_raise`'s result into the guess's handle -/

/-- `bc_raise`'s result `y` for the handle `h` that was the owned number `g`
(base and result slot both): the heap with `h` for `g`, `h` naming `y`'s
number (its count aside), a new number or one more reference to `_one_`. -/
structure RaH (S : Nat → Prop) (X : Raws) (Mt : Mem) (H : Heap) (F : List Blk) (hs1 hs2 : List RH)
    (Lb : List NumObj) (o y : NumObj) (h : RH) : Prop where
  heap : BcHeap S X Mt H F (RList (hs1 ++ h :: hs2) Lb)
  own : RHOwn (hs1 ++ h :: hs2) Lb
  ok : RHOK Lb h
  p : h.p = y.rep.p
  base : ∃ k, h.base = y.withRefs k
  src : (∃ t, h = .own t) ∨ h = .ref o

theorem raPost_handle {S : Nat → Prop} {X : Raws} {Mt0 Mt : Mem} {H : Heap} {F : List Blk}
    {hs1 hs2 : List RH} {Lb Lf : List NumObj} {g o y : NumObj} {q sp W : Nat} {n : Num}
    (hd : PDist (RList (hs1 ++ .own g :: hs2) Lb)) (hown : RHOwn (hs1 ++ .own g :: hs2) Lb)
    (hg : g.rep.refs = 1) (hpos : ∀ c ∈ RList (hs1 ++ .own g :: hs2) Lb, 1 ≤ c.rep.refs)
    (hmo : o ∈ Lb) (hor : 1 ≤ o.rep.refs)
    (hp : RaPost S X Mt0 Mt H F (RList (hs1 ++ .own g :: hs2) Lb) g [g.rep.p, o.rep.p] q sp W n
      Lf y) :
    ∃ h, RaH S X Mt H F hs1 hs2 Lb o y h := by
  have hb := hp.heap
  have hgo : g.Owns := hown.temps g (List.mem_append_right _ List.mem_cons_self)
  obtain ⟨Lm, hadd, hdrop⟩ := hp.mid
  obtain ⟨k, hk⟩ := hp.res
  have hsrc := hp.src
  have eL := RList.own_split hs1 hs2 g Lb
  have hdL := hd; rw [eL] at hdL
  -- the heap unchanged: the handle names `g`, which is `y` (its count aside)
  have keep : Lf = RList (hs1 ++ .own g :: hs2) Lb → g = y.withRefs g.rep.refs →
      ∃ h, RaH S X Mt H F hs1 hs2 Lb o y h := fun e eg => by
    subst e
    exact ⟨.own g, hb, hown, ⟨hg, hgo⟩, by rw [eg]; rfl, ⟨_, eg⟩, .inl ⟨g, rfl⟩⟩
  -- the old guess dropped from `y :: L`: the new number's handle
  have fresh : y.rep.refs = 1 → ∀ L'', DropAt (RList (hs1 ++ .own g :: hs2) Lb) g.rep.p L'' →
      Lf = y :: L'' → ∃ h, RaH S X Mt H F hs1 hs2 Lb o y h := fun hy1 L'' hd' e => by
    rw [eL] at hd'
    have hfr := DropAt.unique hdL hd'
    have e2 := RList.freed_own hg hfr
    subst e2; subst e
    have own' := hown.set (h := .own g) hp.owns
    exact ⟨.own y, hb.perm (RList.cons_perm hs1 hs2 y Lb) own'.all, own', ⟨hy1, hp.owns⟩, rfl,
      ⟨y.rep.refs, (NumObj.withRefs_self y).symm⟩, .inl ⟨y, rfl⟩⟩
  generalize eLL : RList (hs1 ++ .own g :: hs2) Lb = L at hadd hd hpos keep fresh
  cases hadd with
  | fresh hy1 =>
    rcases DropAt.cons_cases hdrop with ⟨hyp, hfr⟩ | ⟨L'', hd', e⟩
    · cases hfr with
      | dec h2 => omega
      | rel _ =>
        simp only [List.nil_append] at hk
        refine keep (by rw [List.nil_append])  ?_
        have hgm : g ∈ L := by rw [← eLL, eL]; exact List.mem_append_right _ List.mem_cons_self
        have := hd.eq hgm hk (by rw [NumObj.withRefs_p]; exact hyp.symm)
        rw [this, NumObj.withRefs_refs]
    · exact fresh hy1 L'' hd' e
  | @share A B c =>
    have hcm : c ∈ A ++ c :: B := List.mem_append_right _ List.mem_cons_self
    have hc1 := hpos c hcm
    have hdm : PDist (A ++ c.withRefs (c.rep.refs + 1) :: B) :=
      hd.congr (by simp only [List.map_append, List.map_cons]; rfl)
    have hcp : c.rep.p = g.rep.p ∨ c.rep.p = o.rep.p := by
      rcases hsrc with h1 | h1 | h1
      · simp only [NumObj.withRefs_refs] at h1; omega
      · exact .inl h1
      · simpa only [List.mem_cons, List.not_mem_nil, or_false, NumObj.withRefs_p] using h1
    by_cases hcg : c.rep.p = g.rep.p
    · -- `c` is `g`
      obtain ⟨rfl, rfl, rfl⟩ := split_unique (x := g) (x' := c) hcg hdL.ne (by rw [← eL, eLL])
      have hfr := DropAt.unique hdm hdrop
      cases hfr with
      | rel h => simp only [NumObj.withRefs_refs] at h; omega
      | dec _ =>
        refine keep ?_ ?_
        · rw [NumObj.decRef_eq, NumObj.withRefs_withRefs, NumObj.withRefs_refs,
            show g.rep.refs + 1 - 1 = g.rep.refs by omega, NumObj.withRefs_self]
        · rw [NumObj.withRefs_withRefs, NumObj.withRefs_self]
    · -- `c` is `_one_`
      have hco : c.rep.p = o.rep.p := hcp.resolve_left hcg
      obtain ⟨Ao, Bo, rfl⟩ := List.append_of_mem hmo
      have eo := RList.ref_split (hs1 ++ .own g :: hs2) (A := Ao) (B := Bo) o
      have hdo : PDist ((rTemps (hs1 ++ .own g :: hs2) ++ Ao.map (rBump (hs1 ++ .own g :: hs2))) ++
          rBump (hs1 ++ .own g :: hs2) o :: Bo.map (rBump (hs1 ++ .own g :: hs2))) := by
        rw [← eo, eLL]; exact hd
      obtain ⟨rfl, rfl, rfl⟩ := split_unique (x := rBump (hs1 ++ .own g :: hs2) o) (x' := c) hco
        hdo.ne (by rw [← eo, eLL])
      have hdc : PDist (Ao ++ o :: Bo) := PDist.caller (hs := hs1 ++ .own g :: hs2) (by rw [eLL]; exact hd)
      have ea := RList.addRef (hs1 ++ .own g :: hs2) (A := Ao) (B := Bo) (y := o) hdc.ne
      have ehs : hs1 ++ .own g :: hs2 ++ [.ref o] = hs1 ++ .own g :: (hs2 ++ [.ref o]) := by
        simp only [List.append_assoc, List.cons_append]
      rw [ea, ehs, RList.own_split] at hdrop hdm
      have hfr := DropAt.unique hdm hdrop
      have e2 := RList.freed_own hg hfr
      rw [← List.append_assoc, ← RList.ref_last] at e2
      subst e2
      refine ⟨.ref o, hb, ⟨fun t ht => ?_, hown.caller⟩, ⟨Ao, Bo, rfl, hor⟩, rfl,
        ⟨o.rep.refs, ?_⟩, .inr rfl⟩
      · rcases List.mem_append.mp ht with ht | ht
        · exact hown.temps t (List.mem_append_left _ ht)
        rcases List.mem_cons.mp ht with ht | ht
        · cases ht
        · exact hown.temps t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))
      · show o = ((rBump (hs1 ++ .own g :: hs2) o).withRefs _).withRefs o.rep.refs
        simp only [rBump, NumObj.withRefs_withRefs, NumObj.withRefs_self]

/-! ## The loop's fixed facts -/

/-- `x`'s integer digits. -/
theorem NumRep.intLen_eq {o : NumRep} (hs : NumShape o) (hn : o.Norm) (hl : 1 ≤ o.len) :
    o.num.intLen = o.len := by
  have hp : 0 < 10 ^ o.scale := Nat.pow_pos (by decide)
  refine Dc.BcModel.intLen_eq hl ?_ ?_
  · rcases Nat.lt_or_ge 1 o.len with h1 | h1
    · refine .inr ?_
      have := NumRep.mag_ge hs hn h1
      unfold Num.intPart
      rw [NumRep.num_mag, NumRep.num_scale, Nat.le_div_iff_mul_le hp, ← Nat.pow_add]
      exact this
    · exact .inl (by omega)
  · have := NumRep.mag_lt hs
    unfold Num.intPart
    rw [NumRep.num_mag, NumRep.num_scale, Nat.div_lt_iff_lt_mul hp, ← Nat.pow_add]
    exact this

/-- Above one, `10 ^ (n_len / 2 + scale)` at most the magnitude. -/
theorem NumRep.hi_bound {o : NumRep} (hs : NumShape o) (hn : o.Norm) (hl : 1 ≤ o.len)
    (hg : 10 ^ o.scale ≤ o.num.mag) : 10 ^ (o.len / 2 + o.num.scale) ≤ o.num.mag := by
  rw [NumRep.num_scale]
  rcases Nat.lt_or_ge 1 o.len with h1 | h1
  · exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (NumRep.mag_ge hs hn h1)
  · rw [show o.len / 2 = 0 by omega, Nat.zero_add]; exact hg

@[simp] theorem NumObj.withRefs_scale (x : NumObj) (k : Nat) :
    (x.withRefs k).rep.scale = x.rep.scale := rfl

/-- `_one_`'s object has at most two digits. -/
theorem NumRep.one_size {o : NumRep} (hs : NumShape o) (hn : o.Norm) (h : o.num = Num.one) :
    o.len + o.scale ≤ 2 := by
  have hsc : o.scale = 0 := by rw [← NumRep.num_scale, h]; rfl
  have hm : dval o.ds = 1 := by rw [← NumRep.num_mag, h]; rfl
  rcases Nat.lt_or_ge 1 o.len with h1 | h1
  · have := NumRep.mag_ge hs hn h1
    rw [hm, hsc, Nat.add_zero] at this
    have : 10 ≤ 10 ^ (o.len - 1) := Nat.le_self_pow (by omega) 10
    omega
  · omega

/-- The caller's numbers with `_zero_` leaked: owners, room for counts. -/
theorem SqLeak.facts {L Lb : List NumObj} {z : NumObj} (hl : SqLeak L z Lb) (hz : z ∈ L)
    (ho : ∀ y ∈ L, y.Owns) (hr : ∀ y ∈ L, y.rep.refs + 16 < 2 ^ 31) :
    (∀ y ∈ Lb, y.Owns) ∧ (∀ y ∈ Lb, y.rep.refs + 8 < 2 ^ 31) ∧
      (∀ y ∈ L, y.rep.p ≠ z.rep.p → y ∈ Lb) ∧ ∃ zb ∈ Lb, zb.rep.p = z.rep.p ∧
        (zb = z ∨ zb = z.withRefs (z.rep.refs + 1)) := by
  rcases hl with rfl | ⟨A, B, rfl, rfl⟩
  · exact ⟨ho, fun y hy => by have := hr y hy; omega, fun y hy _ => hy, z, hz, rfl, .inl rfl⟩
  · have hz' : ∀ y ∈ A ++ z.withRefs (z.rep.refs + 1) :: B, y ∈ A ++ z :: B ∨
        y = z.withRefs (z.rep.refs + 1) := fun y hy => by
      simp only [List.mem_append, List.mem_cons] at hy ⊢
      rcases hy with h | h | h
      · exact .inl (.inl h)
      · exact .inr h
      · exact .inl (.inr (.inr h))
    refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy hne => ?_, _, List.mem_append_right _
      List.mem_cons_self, rfl, .inr rfl⟩
    · rcases hz' y hy with h | rfl
      · exact ho y h
      · exact ho z hz
    · rcases hz' y hy with h | rfl
      · have := hr y h; omega
      · have := hr z hz; simp only [NumObj.withRefs_refs]; omega
    · simp only [List.mem_append, List.mem_cons] at hy ⊢
      rcases hy with h | h | h
      · exact .inl h
      · exact absurd (by rw [h]) hne
      · exact .inr (.inr h)

/-- **The loop's fixed facts** from `bc_sqrt`'s arguments: the caller's
numbers `Lb` after the leak, `_zero_` (`zb`) among them. -/
theorem SqArgs.env {S : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {L Lb : List NumObj} {x z o p5 zb : NumObj} {k rs : Nat}
    (cx : SqCtx S R0 sp W q) (ha : SqArgs S Mt0 L x z o q k) (hl : SqLeak L z Lb)
    (hzb : zb ∈ Lb) (hzr : zb = z ∨ zb = z.withRefs (z.rep.refs + 1))
    (hxz : x.rep.p ≠ z.rep.p) (hoz : o.rep.p ≠ z.rep.p) (hxo : x.rep.p ≠ o.rep.p)
    (hxneg : x.rep.neg = false) (hrs : rs = max k x.rep.scale)
    (h5n : p5.rep.num = Num.half) (h5l : p5.rep.len = 1) (h5s : p5.rep.scale = 1)
    (h5N : p5.rep.Norm) (h5ok : RHOK Lb (.own p5)) (hos : o.rep.len + o.rep.scale ≤ 2) :
    SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs := by
  obtain ⟨hown, hrefs, hmem, -⟩ := hl.facts ha.mz ha.owns ha.refs
  have hzp : zb.rep.p = z.rep.p := by rcases hzr with rfl | rfl <;> rfl
  have hz := ha.zero
  refine ⟨cx, ⟨?_, ha.one, ha.mulBase⟩, hown, hmem x ha.mx hxz, hzb, ha.nx, ha.lenx, hxneg,
    by have := ha.size; omega, hrs, hrefs, h5n, h5l, h5s, h5N, h5ok, ha.rx, hmem o ha.mo hoz,
    ha.oneNum, hos, hxo, by rw [hzp]; exact hxz⟩
  rcases hzr with rfl | rfl
  · exact hz.mono (by omega)
  · exact ⟨hz.glob, hz.len, hz.scale, hz.ds, hz.neg, by simp only [NumObj.withRefs_refs]; omega,
      by have := hz.room; simp only [NumObj.withRefs_refs]; omega⟩

/-- **The Newton loop and the exit** from the head with the model's guess. -/
theorem sq_run {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    {H : Heap} {F : List Blk} {L Lb : List NumObj} {x z zb o p5 : NumObj} {k rs cs : Nat}
    {D G : RH} {G1 : Option RH} {g r : Num}
    (env : SqEnv S Mt0 R0 sp W q Lb x zb o p5 k rs) (hoom : RaOom live S Q Mt0 sp W q)
    (hl : SqLeak L z Lb) (hL : Dc.SqrtLoop x.rep.num rs g cs r)
    (st : SqL S X Mt0 M R0 R sp W q H F Lb x zb p5 k rs cs D G G1 g)
    (hret : ∀ R' M' H' F' Lf y', Keeps binClob R' R0 → R' 10 = 1#64 →
      SqPost S X Mt0 M' H' F' L x z q sp W r Lf y' → DW live S Q (R0 1) R' M') :
    DW live S Q 0x80006b74#64 R M :=
  sq_loop hlive env hoom hL (fun _ _ _ _ _ _ _ _ _ st' _ hsy hr =>
    sq_exit hlive env hoom hl st' hsy (hr ▸ hret)) R M H F D G G1 st

/-- After the setup, at `0x80006ad4`/`0x80006d04`: `point5` (`s4`) and three
references to `_zero_` (`guess`, `guess1`, `diff` at `+24`, `+32`, `+40`;
`s10` holds `_zero_`), `rscale` in `s8`. -/
structure SqS (S : Nat → Prop) (X : Raws) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat)
    (H : Heap) (F : List Blk) (L : List NumObj) (x z p5 : NumObj) (rs : Nat) : Prop where
  fr : SqFr S X Mt0 M R0 R sp W H F L [.own p5, .ref z, .ref z, .ref z]
  r19 : R 19 = BitVec.ofNat 64 q
  r20 : R 20 = BitVec.ofNat 64 p5.rep.p
  r24 : R 24 = BitVec.ofNat 64 rs
  r26 : R 26 = BitVec.ofNat 64 z.rep.p
  wq : ldv .ld M q = BitVec.ofNat 64 x.rep.p
  w8 : ldv .ld M (sp - 160 + 8) = BitVec.ofNat 64 oneAddr
  w24 : ldv .ld M (sp - 160 + 24) = BitVec.ofNat 64 z.rep.p
  w32 : ldv .ld M (sp - 160 + 32) = BitVec.ofNat 64 z.rep.p
  w40 : ldv .ld M (sp - 160 + 40) = BitVec.ofNat 64 z.rep.p

/-- `_zero_`'s three references with `guess`'s leaked: two handles over the
caller's numbers with one more reference to `_zero_`, then `_one_`'s. -/
theorem RList.leak (p5 : NumObj) {A B : List NumObj} {z o : NumObj}
    (hd : ∀ w ∈ A ++ B, w.rep.p ≠ z.rep.p) (hoz : o.rep.p ≠ z.rep.p) :
    RList [.own p5, .ref z, .ref z, .ref z, .ref o] (A ++ z :: B) =
      RList [.own p5, .ref (z.withRefs (z.rep.refs + 1)), .ref o,
        .ref (z.withRefs (z.rep.refs + 1))] (A ++ z.withRefs (z.rep.refs + 1) :: B) := by
  have hc : ∀ w ∈ A ++ B, rBump [.own p5, .ref z, .ref z, .ref z, .ref o] w =
      rBump [.own p5, .ref (z.withRefs (z.rep.refs + 1)), .ref o,
        .ref (z.withRefs (z.rep.refs + 1))] w := fun w hw => by
    have h1 := hd w hw
    simp only [rBump, rCnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RH.cnt,
      NumObj.withRefs_p, if_neg (Ne.symm h1), Nat.zero_add, Nat.add_zero]
  simp only [RList, rTemps_own, rTemps_ref, rTemps_nil, List.map_append, List.map_cons]
  rw [map_rBump_congr fun w hw => hc w (List.mem_append_left _ hw),
    map_rBump_congr fun w hw => hc w (List.mem_append_right _ hw)]
  congr 3
  simp only [rBump, rCnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RH.cnt,
    NumObj.withRefs_p, if_neg (Ne.symm hoz), if_pos rfl, NumObj.withRefs_withRefs,
    NumObj.withRefs_refs, ite_true, Nat.zero_add, Nat.add_zero]
  congr 1; omega

/-- At the loop head after the below-one setup: `_one_`'s count raised and
stored as `guess`, `cscale = x`'s scale. -/
theorem sq_loHead {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z o p5 : NumObj} {r : Num}
    (cx : SqCtx S R0 sp W q) (ha : SqArgs S Mt0 L x z o q k) (hoom : RaOom live S Q Mt0 sp W q)
    (st : SqS S X Mt0 M R0 R sp W q H F L x z p5 rs)
    (h5n : p5.rep.num = Num.half) (h5l : p5.rep.len = 1) (h5s : p5.rep.scale = 1)
    (h5N : p5.rep.Norm) (hrs : rs = max k x.rep.scale)
    (hxneg : x.rep.neg = false) (hlt : Num.cmp x.rep.num Num.one = .lt)
    (hx0 : x.rep.num.mag ≠ 0) (hxz : x.rep.p ≠ z.rep.p) (hxo : x.rep.p ≠ o.rep.p)
    (hoz : o.rep.p ≠ z.rep.p) (hL : Dc.SqrtLoop x.rep.num rs Num.one x.rep.scale r)
    {R1 : Nat → BitVec 64} (hk : Keeps [15, 14, 9, 8, 27, 23, 18, 22, 21] R1 R)
    (r9 : R1 9 = BitVec.ofNat 64 (sp - 160 + 24)) (r21 : R1 21 = 1#64)
    (r22 : R1 22 = BitVec.ofNat 64 (rs + 1)) (r23 : R1 23 = BitVec.ofNat 64 bcFreeAddr)
    (r8 : R1 8 = BitVec.ofNat 64 o.rep.p) (r18 : R1 18 = BitVec.ofNat 64 (x.rep.scale + 1))
    (r27 : R1 27 = BitVec.ofNat 64 x.rep.scale)
    (hret : ∀ R' M' H' F' Lf y', Keeps binClob R' R0 → R' 10 = 1#64 →
      SqPost S X Mt0 M' H' F' L x z q sp W r Lf y' → DW live S Q (R0 1) R' M') :
    DW live S Q 0x80006b74#64 R1 (writeLog (writeLog M [(sp - 160 + 24, 8, BitVec.ofNat 64 o.rep.p)])
      [(o.rep.p + 12, 4, BitVec.ofNat 64 (o.rep.refs + 1))]) := by
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.fr.heap
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hon := hb.nums _ (RList.mem_caller _ ha.mo)
  num_facts hon
  have hc0 : rCnt [.own p5, .ref z, .ref z, .ref z] o.rep.p = 0 := by
    simp only [rCnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RH.cnt,
      if_neg (Ne.symm hoz), Nat.add_zero]
  have hro' := ha.refs o ha.mo
  simp only [rBump, NumObj.withRefs_p] at *
  have hqo := hsl.out q (by simp only [slotBytes]; omega)
  simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hqo
  -- the heap: `_one_`'s reference added, then `guess`'s `_zero_` leaked
  have hor := ha.oneRefs
  have hos0 := NumRep.one_size hon.shape (by exact ha.oneNorm) (by exact ha.oneNum)
  have hos : o.rep.len + o.rep.scale ≤ 2 := hos0
  obtain ⟨A, B, rfl⟩ := List.append_of_mem ha.mz
  have hd : ∀ w ∈ A ++ B, w.rep.p ≠ z.rep.p := fun w hw => (PDist.caller hb.pdist).ne w hw
  have hP : ∀ a, (sp - 160 + 24 ≤ a ∧ a < sp - 160 + 24 + 8) → OutHeap a := fun a h => by
    simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have hb2 := RList.bump (hb.out_frame (MemOnly.store M (sp - 160 + 24) 8
    (BitVec.ofNat 64 o.rep.p)) hP) ha.mo (v := BitVec.ofNat 64 (o.rep.refs + 1))
    (by rw [hc0, Nat.add_zero]; exact toNat_ofNat_mod32 (by omega)) (by rw [hc0]; omega)
  simp only [List.cons_append, List.nil_append] at hb2
  rw [RList.leak p5 hd hoz] at hb2
  have hl : SqLeak (A ++ z :: B) z (A ++ z.withRefs (z.rep.refs + 1) :: B) := .inr ⟨A, B, rfl, rfl⟩
  obtain ⟨hown, -, hmem, -⟩ := hl.facts ha.mz ha.owns ha.refs
  have hzb : z.withRefs (z.rep.refs + 1) ∈ A ++ z.withRefs (z.rep.refs + 1) :: B :=
    List.mem_append_right _ List.mem_cons_self
  have hmo := hmem o ha.mo hoz
  have h5ok : RHOK (A ++ z.withRefs (z.rep.refs + 1) :: B) (.own p5) := by
    have h := st.fr.ok (.own p5) (by simp); exact ⟨h.1, h.2⟩
  have env := SqArgs.env cx ha hl hzb (.inr rfl) hxz hoz hxo hxneg hrs h5n h5l h5s h5N h5ok hos
  have hcmp := Dc.BcModel.cmp_one (x := x.rep.num) hxneg
  rw [hlt] at hcmp
  have hsc1 : 1 ≤ x.rep.scale := by
    rcases Nat.eq_zero_or_pos x.rep.scale with h0 | h0
    · have := Nat.compare_eq_lt.mp hcmp.symm
      rw [NumRep.num_scale, h0, Nat.pow_zero] at this
      exact absurd (by omega) hx0
    · exact h0
  have hzr : ∃ A' B', A ++ z.withRefs (z.rep.refs + 1) :: B = A' ++ z.withRefs (z.rep.refs + 1) :: B'
    ∧ 1 ≤ (z.withRefs (z.rep.refs + 1)).rep.refs := ⟨A, B, rfl, by simp⟩
  obtain ⟨Ao, Bo, hoe⟩ := List.append_of_mem hmo
  refine sq_run hlive env hoom hl (D := .ref (z.withRefs (z.rep.refs + 1))) (G := .ref o)
    (G1 := some (.ref (z.withRefs (z.rep.refs + 1)))) hL
    { f :=
        { sa := (((st.fr.sa.call (M' := writeLog M [(sp - 160 + 24, 8, BitVec.ofNat 64 o.rep.p)])
            (hsp := by omega) (hW := by omega) (hkp := Keeps.refl _ _)
            (hag := fun a _ h2 _ => imgM_store_miss _ _ (by omega))
            (hst := fun a h1 _ => outHeap_of_ge (by simp only [heapEnd]; omega))).heap cx
            (M' := writeLog (writeLog M [(sp - 160 + 24, 8, BitVec.ofNat 64 o.rep.p)])
              [(o.rep.p + 12, 4, BitVec.ofNat 64 (o.rep.refs + 1))])
            (hag := fun a ha' => imgM_store_miss _ _ (by
              simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at ha'; omega))).regs
            hk)
          r9 := r9
          r19 := by rw [hk.get 19 (by decide)]; exact st.r19
          r20 := by rw [hk.get 20 (by decide)]; exact st.r20
          r21 := r21
          r22 := r22
          r23 := r23
          r24 := by rw [hk.get 24 (by decide)]; exact st.r24
          wq := by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact st.wq
          w8 := by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact st.w8 }
      heap := hb2
      own := ⟨fun y hy => by
          rw [show y = p5 by simpa using hy]; exact st.fr.own.temps _ (by simp), hown⟩
      okD := hzr
      okG := ⟨Ao, Bo, hoe, hor⟩
      okT := fun h hh => by
        simp only [Option.toList_some, List.mem_singleton] at hh; subst hh; exact hzr
      vG := ha.oneNum
      nG := ha.oneNorm
      lG := ha.oneLen
      gx := Ne.symm hxo
      gz := hoz
      model := Dc.BcModel.sqG_initLo hsc1 hx0
      w24 := by rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _
      w40 := by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact st.w40
      r8 := r8
      r18 := r18
      r27 := r27
      r26 := by rw [hk.get 26 (by decide)]; exact st.r26 }
    hret

/-- `_one_`'s raised count stored, from `0x80006d30`, on to `sq_loHead`. -/
theorem sq_loStore {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z o p5 : NumObj} {r : Num}
    (cx : SqCtx S R0 sp W q) (ha : SqArgs S Mt0 L x z o q k) (hoom : RaOom live S Q Mt0 sp W q)
    (st : SqS S X Mt0 M R0 R sp W q H F L x z p5 rs)
    (h5n : p5.rep.num = Num.half) (h5l : p5.rep.len = 1) (h5s : p5.rep.scale = 1)
    (h5N : p5.rep.Norm) (hrs : rs = max k x.rep.scale)
    (hxneg : x.rep.neg = false) (hlt : Num.cmp x.rep.num Num.one = .lt)
    (hx0 : x.rep.num.mag ≠ 0) (hxz : x.rep.p ≠ z.rep.p) (hxo : x.rep.p ≠ o.rep.p)
    (hoz : o.rep.p ≠ z.rep.p) (hL : Dc.SqrtLoop x.rep.num rs Num.one x.rep.scale r)
    {R2 : Nat → BitVec 64} (hk : Keeps [15, 14, 9, 8, 27, 23, 18] R2 R)
    (r9 : R2 9 = BitVec.ofNat 64 (sp - 160 + 24)) (r23 : R2 23 = BitVec.ofNat 64 bcFreeAddr)
    (r8 : R2 8 = BitVec.ofNat 64 o.rep.p) (r18 : R2 18 = BitVec.ofNat 64 (x.rep.scale + 1))
    (r27 : R2 27 = BitVec.ofNat 64 x.rep.scale) (r15 : R2 15 = BitVec.ofNat 64 (o.rep.refs + 1))
    (hret : ∀ R' M' H' F' Lf y', Keeps binClob R' R0 → R' 10 = 1#64 →
      SqPost S X Mt0 M' H' F' L x z q sp W r Lf y' → DW live S Q (R0 1) R' M') :
    DW live S Q 0x80006d30#64 R2 (writeLog M [(sp - 160 + 24, 8, BitVec.ofNat 64 o.rep.p)]) := by
  sq_facts cx
  have hb := st.fr.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hon := hb.nums _ (RList.mem_caller _ ha.mo)
  num_facts hon
  simp only [rBump, NumObj.withRefs_p] at *
  have hro' := ha.refs o ha.mo
  have hx3 := sxw_ofNat (show rs + 1 < 2 ^ 31 by have := ha.size; omega)
  have h24 : R2 24 = BitVec.ofNat 64 rs := by rw [hk.get 24 (by decide)]; exact st.r24
  bc_run hlive hS [r8, r15, hx3, h24] at 0x80006b74
  refine sq_loHead hlive cx ha hoom st h5n h5l h5s h5N hrs hxneg hlt hx0 hxz hxo hoz hL
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hret
  · keeps_tac (hk.mono (by decide))
  all_goals bsimp [r9, r23, r8, r18, r27]

/-- **The first guess below one** from `0x80006d04`: `guess = _one_` with
one more reference (the slot's `_zero_` leaked), `cscale = x`'s scale, on to
the loop and its exit. -/
theorem sq_lo {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k rs : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {x z o p5 : NumObj} {r : Num}
    (cx : SqCtx S R0 sp W q) (ha : SqArgs S Mt0 L x z o q k) (hoom : RaOom live S Q Mt0 sp W q)
    (st : SqS S X Mt0 M R0 R sp W q H F L x z p5 rs)
    (h5n : p5.rep.num = Num.half) (h5l : p5.rep.len = 1) (h5s : p5.rep.scale = 1)
    (h5N : p5.rep.Norm) (hrs : rs = max k x.rep.scale)
    (hxneg : x.rep.neg = false) (hlt : Num.cmp x.rep.num Num.one = .lt)
    (hx0 : x.rep.num.mag ≠ 0) (hxz : x.rep.p ≠ z.rep.p) (hxo : x.rep.p ≠ o.rep.p)
    (hoz : o.rep.p ≠ z.rep.p) (hL : Dc.SqrtLoop x.rep.num rs Num.one x.rep.scale r)
    (hret : ∀ R' M' H' F' Lf y', Keeps binClob R' R0 → R' 10 = 1#64 →
      SqPost S X Mt0 M' H' F' L x z q sp W r Lf y' → DW live S Q (R0 1) R' M') :
    DW live S Q 0x80006d04#64 R M := by
  sq_facts cx
  have hsf := cx.cc.frame
  have hb := st.fr.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have sa := st.fr.sa
  have h2 := sa.r2
  have hsl := cx.slot
  have hq := hsl.slot
  have hql := hq.lo; have hqh := hq.hi; have hqa := hq.al
  have hap := hsl.apart
  have hcs := (SqCst.mk (ha.zero.mono (by omega)) ha.one ha.mulBase).transport cx sa.out
  have hxn := hb.nums _ (RList.mem_caller _ ha.mx)
  num_facts hxn
  have hon := hb.nums _ (RList.mem_caller _ ha.mo)
  have hcst : ∀ b ∈ accAddrs oneAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.cc.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  num_facts hon
  have hxsc := hxn.scale
  simp only [rBump, NumObj.withRefs_p, NumObj.withRefs_scale] at *
  have hc0 : rCnt [.own p5, .ref z, .ref z, .ref z] o.rep.p = 0 := by
    simp only [rCnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RH.cnt,
      if_neg (Ne.symm hoz), Nat.add_zero]
  have hro := RList.refsAt hb ha.mo
  rw [hc0, Nat.add_zero] at hro
  have hro' := ha.refs o ha.mo
  have hsz := ha.size
  have hx1 := sxw_ofNat (show o.rep.refs + 1 < 2 ^ 31 by omega)
  have hx2 := sxw_ofNat (show x.rep.scale + 1 < 2 ^ 31 by omega)
  have hx3 := sxw_ofNat (show rs + 1 < 2 ^ 31 by omega)
  have hx4 := sxw_ofNat (show x.rep.scale < 2 ^ 31 by omega)
  have hto : (BitVec.ofNat 64 oneAddr).toNat = oneAddr := rfl
  bc_run hlive hS [h2, st.w8, st.r19, st.wq, hto, hcs.one, hxsc, hro, hx1, hx2, hx3, hx4,
    st.r24] at 0x80006d30
  all_goals first
    | exact frame_acc hsf (by omega) (by omega)
    | exact hq.acc
    | exact acc_heap hS (by omega) (by omega)
    | (simp only [LdOK, oneAddr, tohostAddr]; omega)
    | (guard_target =~ ∀ b ∈ accAddrs oneAddr 8, S b; exact hcst)
    | skip
  refine sq_loStore hlive cx ha hoom st h5n h5l h5s h5N hrs hxneg hlt hx0 hxz hxo hoz hL
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hret
  · keeps_tac Keeps.refl _ _
  all_goals bsimp []

end Dc.Mach
