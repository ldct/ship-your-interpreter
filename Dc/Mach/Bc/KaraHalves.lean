import Dc.Mach.Bc.KaraRoute
import Dc.Mach.Bc.KaraM1Stage

/-!
# `_bc_rec_mul`'s Karatsuba step: the four halves

From the step's entry at `0x80004db0` to the `m1` stage at `0x80004f70`: the
half `n`, the `u` and `v` routes (`kara_uhigh`/`kara_uzero`,
`kara_vhigh`/`kara_vzero`), and the four leading-zero trims (`ktrims`). Each
trimmed half is described by `KHalf`: the digit string of the operand it
denotes.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- **A trimmed half**: the handle's object is the non-negative integer of
the digits `ds`, normalised; it has an integer digit when `ds` does. -/
structure KHalf (z : NumObj) (h : Hd) (ds : List Nat) : Prop where
  num : (Hd.o z h).rep.num = ⟨false, dvalBE ds, 0⟩
  norm : (Hd.o z h).rep.Norm
  len : (Hd.o z h).rep.len ≤ max 1 ds.length
  pos : ds ≠ [] → 1 ≤ (Hd.o z h).rep.len
  /-- a half that is not `_zero_` has at most its digits -/
  lenS : ∀ x, h = some x → x.rep.len ≤ ds.length

theorem KHalf.neg {z : NumObj} {h : Hd} {ds : List Nat} (k : KHalf z h ds) :
    (Hd.o z h).rep.neg = false := congrArg Num.neg k.num

theorem KHalf.scale {z : NumObj} {h : Hd} {ds : List Nat} (k : KHalf z h ds) :
    (Hd.o z h).rep.scale = 0 := congrArg Num.scale k.num

/-- `_zero_` is the half of no digits. -/
theorem khalf_zero {M : Mem} {z : NumObj} {k : Nat} (kz : KZero M z k) : KHalf z none [] where
  num := by simp only [Hd.o, NumRep.num, kz.neg, kz.ds, kz.scale]; rfl
  norm := .inl (by simp only [Hd.o, kz.len]; exact Nat.le_refl 1)
  len := by simp only [Hd.o, kz.len]; exact Nat.le_max_left 1 _
  pos := fun h => absurd rfl h
  lenS := fun _ e => nomatch e

/-- A view's handle after `_bc_rm_leading_zeros`. -/
theorem Hd.o_trim_view (z w : NumObj) (sb : Blk) (off k : Nat) :
    Hd.o z (Hd.trim (Hd.lz (some (viewObj sb w off k))) (some (viewObj sb w off k))) =
      ⟨(viewRep sb.pay w.rep off k).rmLeadingZeros, sb, w.db⟩ := rfl

/-- **A trimmed view** of `k` digits of `w` from `off` is the half of those
digits. -/
theorem khalf_view {z w : NumObj} {sb : Blk} {off k : Nat} (hw : NumShape w.rep)
    (hfit : off + k ≤ w.rep.len + w.rep.scale) :
    KHalf z (Hd.trim (Hd.lz (some (viewObj sb w off k))) (some (viewObj sb w off k)))
      ((w.rep.ds.drop off).take k) := by
  have hl : ((w.rep.ds.drop off).take k).length = k := by
    simp only [List.length_take, List.length_drop, hw.dsLen]; omega
  suffices h : KHalf z (some ⟨(viewRep sb.pay w.rep off k).rmLeadingZeros, sb, w.db⟩)
      ((w.rep.ds.drop off).take k) from h
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨?_, .inl ?_, ?_, fun h => absurd List.take_zero h, fun x e => ?_⟩ <;>
      try (cases e)
    all_goals
      simp only [Hd.o, NumRep.rmLeadingZeros, NumRep.drop, viewRep, NumRep.num, List.take_zero,
        List.drop_nil] <;> first | rfl | omega
  · obtain ⟨hnum, hnorm, -, hpos⟩ := NumRep.rmLeadingZeros_spec (o := viewRep sb.pay w.rep off k)
      (by simp only [viewRep]; omega) (by simp only [viewRep]; omega)
    refine ⟨hnum.trans rfl, hnorm, ?_, fun _ => hpos, fun x e => ?_⟩
    · simp only [Hd.o, NumRep.rmLeadingZeros, NumRep.drop, viewRep]
      omega
    · cases e
      simp only [NumRep.rmLeadingZeros, NumRep.drop, viewRep]
      omega

/-- `KAt` through a scratch run on the heap and the allocator's words. -/
theorem KAt.touch {S : Nat → Prop} {M0 M M' : Mem} {R0 R : Nat → BitVec 64} {sp q W : Nat}
    (cx : RmCtx S R0 sp q W) (st : KAt S M0 M R0 R sp q W) (h : MemOnly KTouch M' M) :
    KAt S M0 M' R0 R sp q W :=
  st.stack cx (fun a h1 _ => touch_above h (by
      have := cx.above; have := cx.big; simp only [heapEnd] at *; omega))
    fun a ha _ _ => h a fun hk => by
      simp only [KTouch, OutHeap, bcFreeBytes] at hk ha; omega

/-- **An untrimmed half**: a view of `k` digits of `w` from `off`, or a
reference to `_zero_` for no digits. -/
inductive KRaw (w : NumObj) (off k : Nat) : Hd → Prop
  | view (sb : Blk) : KRaw w off k (some (viewObj sb w off k))
  | zero : k = 0 → KRaw w off k none

/-- The trimmed half of an untrimmed one. -/
theorem KRaw.trim {M : Mem} {z w : NumObj} {off k j : Nat} {h : Hd} (kz : KZero M z j)
    (hw : NumShape w.rep) (hfit : off + k ≤ w.rep.len + w.rep.scale) :
    KRaw w off k h → KHalf z (h.trim h.lz) ((w.rep.ds.drop off).take k)
  | .view _ => khalf_view hw hfit
  | .zero hk => by subst hk; simpa only [List.take_zero, Hd.trim_none] using khalf_zero kz

/-- A heap-only frame is a scratch frame. -/
theorem MemOnly.touch_of_heap {M' M : Mem} (h : MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M' M) :
    MemOnly KTouch M' M := h.mono fun _ ha => .inr (.inl ha)

/-- **The `v` side and the trims**, from either route of the second length
test: `v1`, `v0` from `vo`'s first `lb` digits, then all four halves trimmed,
to the `m1` stage at `0x80004f70`. -/
theorem kara_vside {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk}
    {A B : List NumObj} {z vo : NumObj} {hu1 hu0 : Hd} {n lb : Nat}
    (hb : BcHeap S M H F (KList [] [hu0, hu1] A B z)) (hvo : vo ∈ temps [hu0, hu1] ++ A ++ B)
    (hfit : lb ≤ vo.rep.len + vo.rep.scale) (hn1 : 1 ≤ n) (hlb1 : 1 ≤ lb) (hlbb : lb < 2 ^ 30)
    (hz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p) (hzo : ∀ a, constBytes a → S a)
    (hz1 : z.rep.len = 1) (hrefs : z.rep.refs + zeroCount [hu0, hu1] + 1 < 2 ^ 31)
    (hh : R 15 = BitVec.ofNat 64 (deadHead F)) (h25 : R 25 = BitVec.ofNat 64 bcFreeAddr)
    (h21 : R 21 = BitVec.ofNat 64 lb) (h8 : R 8 = BitVec.ofNat 64 n)
    (h23 : R 23 = BitVec.ofNat 64 vo.rep.val) (h18 : R 18 = BitVec.ofNat 64 vo.rep.p)
    (h24 : R 24 = BitVec.ofNat 64 (Hd.p z hu1)) (h19 : R 19 = BitVec.ofNat 64 (Hd.p z hu0))
    (hoom : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps kvClob R' R → MemOnly KTouch M' M →
      DW live S Q 0x80002bcc#64 R' M')
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem) (H' : Heap) (F' : List Blk) (hv1 hv0 : Hd),
      Keeps kvClob R' R →
      BcHeap S M' H' F' (KList [] [hv0.trim hv0.lz, hv1.trim hv1.lz, hu0.trim hu0.lz,
        hu1.trim hu1.lz] A B z) →
      KRaw vo 0 (lb - n) hv1 → KRaw vo (lb - n) (lb - (lb - n)) hv0 →
      R' 27 = BitVec.ofNat 64 (Hd.p z hv1) → R' 20 = BitVec.ofNat 64 (Hd.p z hv0) →
      R' 18 = BitVec.ofNat 64 zeroAddr → R' 17 = BitVec.ofNat 64 z.rep.p →
      MemOnly KTouch M' M → DW live S Q 0x80004f70#64 R' M') :
    (n ≤ lb → DW live S Q 0x800053c0#64 R M) ∧ (lb < n → DW live S Q 0x80004e68#64 R M) := by
  constructor
  · intro hle
    refine kara_vhigh hlive hb hvo hfit hle hn1 hlbb hz hzo hh h25 h21 h8 h23 h18 hoom ?_
    intro R1 M1 H1 F1 sb1 sb2 kk1 hb1 h27 h20 h18' h17 t1
    refine ktrims hlive hb1 hz1 ((kk1.get 24).trans h24) ((kk1.get 19).trans h19) h27 h20 ?_
    intro R2 M2 kk2 hb2 hmo2
    exact hnext R2 M2 H1 F1 _ _ ((kk2.mono (by decide)).trans kk1) hb2 (.view sb1)
      (by rw [show lb - (lb - n) = n by omega]; exact .view sb2)
      ((kk2.get 27).trans h27) ((kk2.get 20).trans h20) ((kk2.get 18).trans h18')
      ((kk2.get 17).trans h17) (hmo2.touch_of_heap.trans t1)
  · intro hlt
    refine kara_vzero hlive hb hvo hfit hlb1 hlbb hz hzo hrefs hh h25 h21 h23 hoom ?_
    intro R1 M1 H1 F1 sb kk1 hb1 h27 h20 h18' h17 t1
    refine ktrims hlive hb1 hz1 ((kk1.get 24).trans h24) ((kk1.get 19).trans h19) h27 h20 ?_
    intro R2 M2 kk2 hb2 hmo2
    exact hnext R2 M2 H1 F1 none _ ((kk2.mono (by decide)).trans kk1) hb2 (.zero (by omega))
      (by rw [show lb - n = 0 by omega, Nat.sub_zero]; exact .view sb)
      ((kk2.get 27).trans h27) ((kk2.get 20).trans h20) ((kk2.get 18).trans h18')
      ((kk2.get 17).trans h17) (hmo2.touch_of_heap.trans t1)

/-- The registers the halves change. -/
abbrev kuvClob : List Nat := [1, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 23, 24, 27]

/-- **The step at the `m1` stage** (`0x80004f70`): the four trimmed halves
head the handles, `u1`, `u0` from `uo`'s first `la` digits and `v1`, `v0`
from `vo`'s first `lb`, split at `n`; off the heap and the allocator's words
memory is the spilled entry memory `Ms`. -/
structure KHalvesAt (S : Nat → Prop) (M0 Ms M : Mem) (R0 R : Nat → BitVec 64)
    (sp q W n la lb : Nat) (A B : List NumObj) (z uo vo : NumObj) (H : Heap) (F : List Blk)
    (hu1 hu0 hv1 hv0 : Hd) : Prop where
  pk : KM1 S M0 M R0 R sp q W n la lb z (hu1.trim hu1.lz) (hu0.trim hu0.lz) (hv1.trim hv1.lz)
    (hv0.trim hv0.lz)
  r17 : R 17 = BitVec.ofNat 64 z.rep.p
  heap : BcHeap S M H F (KList [] [hv0.trim hv0.lz, hv1.trim hv1.lz, hu0.trim hu0.lz,
    hu1.trim hu1.lz] A B z)
  u1 : KRaw uo 0 (la - n) hu1
  u0 : KRaw uo (la - n) (la - (la - n)) hu0
  v1 : KRaw vo 0 (lb - n) hv1
  v0 : KRaw vo (lb - n) (lb - (lb - n)) hv0
  touch : MemOnly KTouch M Ms

/-- **From the step's entry at `0x80004db0` to the `m1` stage**: the spills,
the half `n = ⌈max la lb / 2⌉`, both operands split (a `_zero_` high half
when the operand is not longer than `n`), and the trims. -/
theorem kara_halves {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {A B L' : List NumObj}
    {z uo vo : NumObj} {u v : NumRep} {la' lb' : Nat} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L' u v la' lb' q sp W)
    (st : RmAt S M0 M R0 R sp q W) (kp : RmKept R R0)
    (hb : BcHeap S M H F (A ++ z :: B)) (huA : uo ∈ A ++ B) (hvA : vo ∈ A ++ B)
    (hfu : la ≤ uo.rep.len + uo.rep.scale) (hfv : lb ≤ vo.rep.len + vo.rep.scale)
    (hN : la + lb < 2 ^ 30) (hla : 20 ≤ la) (hlb : 20 ≤ lb) (kz : KZero M z 2)
    (h0 : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p)
    (h22 : R 22 = BitVec.ofNat 64 (la + lb)) (h20 : R 20 = BitVec.ofNat 64 la)
    (h21 : R 21 = BitVec.ofNat 64 lb) (h18 : R 18 = BitVec.ofNat 64 vo.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 q)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem) (H' : Heap) (F' : List Blk)
      (hu1 hu0 hv1 hv0 : Hd),
      KHalvesAt S M0 (kSpillMem M R0 (sp - 192)) M' R0 R' sp q W ((max la lb + 1) / 2) la lb
        A B z uo vo H' F' hu1 hu0 hv1 hv0 →
      DW live S Q 0x80004f70#64 R' M') :
    DW live S Q 0x80004db0#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hab := cx.above; have hWb := cx.big
  simp only [heapEnd] at hab
  have hmx := Nat.le_max_left la lb; have hmy := Nat.le_max_right la lb
  have hmz : max la lb ≤ la + lb := Nat.max_le.2 ⟨by omega, by omega⟩
  have hun : uo ∈ A ++ z :: B := by
    simp only [List.mem_append, List.mem_cons] at huA ⊢
    rcases huA with h | h
    · exact .inl h
    · exact .inr (.inr h)
  have hzs : ldv .ld (kSpillMem M R0 (sp - 192)) zeroAddr = BitVec.ofNat 64 z.rep.p :=
    (kSpillMem_ldv M R0 (by simp only [zeroAddr]; omega)).trans kz.glob
  have hKL : ∀ (M' : Mem), BcHeap S M' H F (A ++ z :: B) → BcHeap S M' H F (KList [] [] A B z) :=
    fun M' h => by rw [KList_nil, List.nil_append]; exact h
  have hmem : ∀ {hs : List Hd} {x : NumObj}, x ∈ A ++ B → x ∈ temps hs ++ A ++ B := by
    intro hs x hx
    simp only [List.mem_append] at hx ⊢
    rcases hx with h | h
    · exact .inl (.inr h)
    · exact .inr h
  refine kara_entry hlive cx st kp hb hun hN hla hlb h0 h22 h20 h21 h18 h9 ?_ ?_
  all_goals intro Re Me ke hc hbe hMe
  all_goals subst hMe
  all_goals
    have oomOf : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps kuvClob R' Re →
        MemOnly KTouch M' (kSpillMem M R0 (sp - 192)) → DW live S Q 0x80002bcc#64 R' M' :=
      fun R' M' kk t => hk.oom R' M' (sp - 192) (by omega) (by omega)
        ((kk.get 2).trans ke.st.rm.r2) fun a ha hs hf =>
          (t a fun hk' => by simp only [KTouch, OutHeap, bcFreeBytes] at hk' ha; omega).trans
            (ke.st.rm.out a ha hs hf)
    have fin : ∀ (R' : Nat → BitVec 64) (M' : Mem) (H' : Heap) (F' : List Blk)
        (hu1 hu0 hv1 hv0 : Hd), Keeps kuvClob R' Re →
        BcHeap S M' H' F' (KList [] [hv0.trim hv0.lz, hv1.trim hv1.lz, hu0.trim hu0.lz,
          hu1.trim hu1.lz] A B z) →
        KRaw uo 0 (la - (max la lb + 1) / 2) hu1 →
        KRaw uo (la - (max la lb + 1) / 2) (la - (la - (max la lb + 1) / 2)) hu0 →
        KRaw vo 0 (lb - (max la lb + 1) / 2) hv1 →
        KRaw vo (lb - (max la lb + 1) / 2) (lb - (lb - (max la lb + 1) / 2)) hv0 →
        R' 24 = BitVec.ofNat 64 (Hd.p z hu1) → R' 19 = BitVec.ofNat 64 (Hd.p z hu0) →
        R' 27 = BitVec.ofNat 64 (Hd.p z hv1) → R' 20 = BitVec.ofNat 64 (Hd.p z hv0) →
        R' 18 = BitVec.ofNat 64 zeroAddr → R' 17 = BitVec.ofNat 64 z.rep.p →
        MemOnly KTouch M' (kSpillMem M R0 (sp - 192)) → DW live S Q 0x80004f70#64 R' M' := by
      intro R' M' H' F' hu1 hu0 hv1 hv0 kk hb' r1 r0 s1 s0 h24 h19 h27 h20' h18' h17 t
      have kt := ke.st.touch cx t
      refine hnext R' M' H' F' hu1 hu0 hv1 hv0 ⟨⟨⟨kt.rm.keeps (kk.mono (by decide)) (kk.get 2),
        kt.saved2⟩, ?_, ?_, ?_, ?_, (kk.get 25).trans ke.fl, (kk.get 9).trans ke.slot,
        (kk.get 8).trans ke.half, (kk.get 22).trans ke.s6, h18'⟩, h17, hb', r1, r0, s1, s0, t⟩
      · rw [Hd.p_trim]; exact h24
      · rw [Hd.p_trim]; exact h19
      · rw [Hd.p_trim]; exact h27
      · rw [Hd.p_trim]; exact h20'
  · -- `la < n`: `u1` is `_zero_`
    refine kara_uzero hlive (hKL _ hbe) (hmem huA) (hmem hvA) hfu (by omega) (by omega) hzs
      cx.consts (by have := kz.room; simp only [zeroCount]; omega) ke.head ke.fl ke.s4 ke.s10
      ke.s2 (fun R' M' kk t => oomOf R' M' (kk.mono (by decide)) t) ?_
    intro R1 M1 H1 F1 sb kk1 hb1 h24 h19 h23 h15 t1
    have vs := kara_vside hlive hb1 (hmem hvA) hfv (by omega) (by omega) (by omega)
      ((ldv_zero_touch t1).trans hzs) cx.consts kz.len
      (by have := kz.room; simp only [zeroCount]; omega) h15 ((kk1.get 25).trans ke.fl)
      ((kk1.get 21).trans ke.s5) ((kk1.get 8).trans ke.half) h23 ((kk1.get 18).trans ke.s2)
      h24 h19 (fun R' M' kk t => oomOf R' M' ((kk.mono (by decide)).trans (kk1.mono (by decide)))
        (t.trans t1)) ?_
    · exact kdisp_800053bc hlive hS ((kk1.get 21).trans ke.s5) ((kk1.get 8).trans ke.half)
        (by omega) (by omega) vs.1 vs.2
    intro R2 M2 H2 F2 hv1 hv0 kk2 hb2 r1 r0 h27 h20' h18' h17 t2
    exact fin R2 M2 H2 F2 none _ hv1 hv0 ((kk2.mono (by decide)).trans (kk1.mono (by decide))) hb2
      (.zero (by omega)) (by rw [show la - (max la lb + 1) / 2 = 0 by omega, Nat.sub_zero]; exact .view sb)
      r1 r0 ((kk2.get 24).trans h24) ((kk2.get 19).trans h19) h27 h20' h18' h17 (t2.trans t1)
  · -- `n ≤ la`: both `u` halves are views
    refine kara_uhigh hlive cx (hKL _ hbe) (hmem huA) (hmem hvA) hfu hc (by omega) (by omega)
      ke.u ke.st.rm.r2 ke.head ke.fl ke.s4 ke.half ke.s10 ke.s2
      (fun R' M' kk t => oomOf R' M' (kk.mono (by decide)) t) ?_
    intro R1 M1 H1 F1 sb1 sb2 kk1 hb1 h24 h19 h23 h15 t1
    have vs := kara_vside hlive hb1 (hmem hvA) hfv (by omega) (by omega) (by omega)
      ((ldv_zero_touch t1).trans hzs) cx.consts kz.len
      (by have := kz.room; simp only [zeroCount]; omega) h15 ((kk1.get 25).trans ke.fl)
      ((kk1.get 21).trans ke.s5) ((kk1.get 8).trans ke.half) h23 ((kk1.get 18).trans ke.s2)
      h24 h19 (fun R' M' kk t => oomOf R' M' ((kk.mono (by decide)).trans (kk1.mono (by decide)))
        (t.trans t1)) ?_
    · exact kdisp_80004e64 hlive hS ((kk1.get 21).trans ke.s5) ((kk1.get 8).trans ke.half)
        (by omega) (by omega) vs.1 vs.2
    intro R2 M2 H2 F2 hv1 hv0 kk2 hb2 r1 r0 h27 h20' h18' h17 t2
    have hsub : la - (la - (max la lb + 1) / 2) = (max la lb + 1) / 2 := by omega
    have hk0 : KRaw uo (la - (max la lb + 1) / 2) (la - (la - (max la lb + 1) / 2))
        (some (viewObj sb2 uo (la - (max la lb + 1) / 2) ((max la lb + 1) / 2))) := by
      rw [hsub]; exact .view sb2
    exact fin R2 M2 H2 F2 _ _ hv1 hv0 ((kk2.mono (by decide)).trans (kk1.mono (by decide))) hb2
      (.view sb1) hk0
      r1 r0 ((kk2.get 24).trans h24) ((kk2.get 19).trans h19) h27 h20' h18' h17 (t2.trans t1)

end Dc.Mach
