import Dc.Mach.Bc.KaraZeroRef
import Dc.Mach.Bc.KaraTrimChain

/-!
# `_bc_rec_mul`'s Karatsuba step: the second length dispatch

Both `u` routes reach the same test of `lb` against the half `n`: at
`0x80004e64` when `u1` is a view (`bge s5, s0`), at `0x800053bc` when `u1` is
a reference to `_zero_` (`blt s5, s0`). Both select the struct source of
`v`'s high half at `0x800053c0` (`n ≤ lb`) or the `_zero_` reference at
`0x80004e68` (`lb < n`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-! ## The step's scratch region

Every struct source and view of the step changes only the allocator's own
words, the number heap and `_bc_Free_list`. One `MemOnly KTouch` composes
those frames, and the step's globals and stack frame are off it. -/

/-- The bytes a struct source or a view may change. -/
def KTouch (a : Nat) : Prop :=
  (freeListAddr ≤ a ∧ a < freeListAddr + 16) ∨ (heapStart ≤ a ∧ a < heapEnd) ∨ bcFreeBytes a

theorem not_alloc_of_not_touch {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {a : Nat} (h : ¬ KTouch a) : ¬ AllocByte H a := fun hal => by
  rcases AllocByte.glob_or_heap hi hal with h' | h'
  · exact h (.inl h')
  · exact h (.inr (.inl h'))

/-- An allocator-relative frame is a scratch frame. -/
theorem memOnly_touch_of_alloc {S : Nat → Prop} {Mt M : Mem} {H : Heap} (hi : HeapInv S Mt H)
    (h : ∀ a, ¬ AllocByte H a → imgM M a = imgM Mt a) : MemOnly KTouch M Mt :=
  fun a ha => h a (not_alloc_of_not_touch hi ha)

/-- **Any frame of a view site's shape is a scratch frame**: the site's
struct is a block of the number heap. -/
theorem ViewStruct.touchOf {S : Nat → Prop} {Mt M M'' : Mem} {H H' : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} (hvs : ViewStruct S Mt M H H' F F' sb L)
    (hb : BcHeap S Mt H F L)
    (hfr : ∀ a, ¬ AllocByte H a → ¬ sb.In a → ¬ bcFreeBytes a → imgM M'' a = imgM Mt a) :
    MemOnly KTouch M'' Mt := by
  intro a ha
  have hbf := hvs.inv.blk (List.mem_append_right _ hvs.live)
  have hlo := hbf.lo; have htop := hbf.top; have hfin := hbf.fin
  simp only [heapStart] at hlo
  simp only [heapEnd] at htop
  have hpl : 2147603920 ≤ sb.pay := by
    have e1 : sb.pay = sb.h + 16 := rfl
    omega
  refine hfr a (not_alloc_of_not_touch hb.heap ha) (fun hin => ?_)
    (fun hg => ha (.inr (.inr hg)))
  simp only [Blk.In] at hin
  exact ha (.inr (.inl (by simp only [heapStart, heapEnd]; omega)))

/-- A view site's own frame is a scratch frame. -/
theorem ViewStruct.touch {S : Nat → Prop} {Mt M : Mem} {H H' : Heap} {F F' : List Blk}
    {L : List NumObj} {sb : Blk} (hvs : ViewStruct S Mt M H H' F F' sb L)
    (hb : BcHeap S Mt H F L) : MemOnly KTouch M Mt := hvs.touchOf hb hvs.base

/-- A doubleword at `_zero_`'s slot survives the scratch. -/
theorem ldv_zero_touch {M Mt : Mem} (h : MemOnly KTouch M Mt) :
    ldv .ld M zeroAddr = ldv .ld Mt zeroAddr :=
  ldv_congr .ld fun j hj => h _ (by
    simp only [KTouch, bcFreeBytes, bcFreeAddr, freeListAddr, heapStart, heapEnd, zeroAddr,
      widthOfM] at hj ⊢
    omega)

/-- A word at `mulBase`'s slot survives the scratch. -/
theorem ldv_mulBase_touch {M Mt : Mem} (h : MemOnly KTouch M Mt) :
    ldv .lw M mulBaseAddr = ldv .lw Mt mulBaseAddr :=
  ldv_congr .lw fun j hj => h _ (by
    simp only [KTouch, bcFreeBytes, bcFreeAddr, freeListAddr, heapStart, heapEnd, mulBaseAddr,
      widthOfM] at hj ⊢
    omega)

/-- Bytes above the heap survive the scratch. -/
theorem touch_above {M Mt : Mem} (h : MemOnly KTouch M Mt) {a : Nat} (ha : heapEnd ≤ a) :
    imgM M a = imgM Mt a :=
  h a (by simp only [KTouch, bcFreeBytes, bcFreeAddr, freeListAddr, heapStart, heapEnd] at ha ⊢
          omega)

/-- One view pushed onto the step's object list. -/
theorem KList_push (x : NumObj) (hs : List Hd) (A B : List NumObj) (z : NumObj) :
    x :: KList [] hs A B z = KList [] (some x :: hs) A B z := by
  rw [KList, KList, zeroCount_some, temps_some]
  simp only [List.nil_append, List.cons_append, List.append_assoc]

/-- **The length dispatch at `0x80004e64`**, reached with `u1` a view. -/
theorem kdisp_80004e64 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64} {n lb : Nat}
    (h21 : R 21 = BitVec.ofNat 64 lb) (h8 : R 8 = BitVec.ofNat 64 n)
    (hlbb : lb < 2 ^ 31) (hnb : n < 2 ^ 31)
    (hge : n ≤ lb → DW live S Q 0x800053c0#64 R M)
    (hlt : lb < n → DW live S Q 0x80004e68#64 R M) :
    DW live S Q 0x80004e64#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h21, h8, toInt_ofNat_small] at 0x800053c0 0x80004e68
  · intro hc
    exact hge (by omega)
  · intro hc
    exact hlt (by omega)

/-- **The length dispatch at `0x800053bc`**, reached with `u1` a reference to
`_zero_`. -/
theorem kdisp_800053bc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    (hS : HeapOwn S) {M : Mem} {R : Nat → BitVec 64} {n lb : Nat}
    (h21 : R 21 = BitVec.ofNat 64 lb) (h8 : R 8 = BitVec.ofNat 64 n)
    (hlbb : lb < 2 ^ 31) (hnb : n < 2 ^ 31)
    (hge : n ≤ lb → DW live S Q 0x800053c0#64 R M)
    (hlt : lb < n → DW live S Q 0x80004e68#64 R M) :
    DW live S Q 0x800053bc#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h21, h8, toInt_ofNat_small] at 0x80004e68 0x800053c0
  · intro hc
    exact hlt (by omega)
  · intro hc
    exact hge (by omega)

/-- An object of the caller's list or of the temporaries is in the step's
object list, whatever `_zero_`'s count. -/
theorem mem_KList {hs : List Hd} {A B : List NumObj} {z vo : NumObj}
    (h : vo ∈ temps hs ++ A ++ B) : vo ∈ KList [] hs A B z := by
  rw [KList]
  rcases List.mem_append.mp h with h' | h'
  · exact List.mem_append_left _ h'
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')

/-! ## The `v` halves -/

/-- The registers the `v`-side route changes. -/
abbrev kvClob : List Nat := [1, 10, 12, 13, 14, 15, 17, 18, 20, 21, 23, 27]

/-- **The `v` halves at `0x800053c0`** (`n ≤ lb`): two struct sources and two
views, `v1` the first `lb - n` digits and `v0` the last `n`. -/
theorem kara_vhigh {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk}
    {A B : List NumObj} {z vo : NumObj} {hs : List Hd} {n lb : Nat}
    (hb : BcHeap S M H F (KList [] hs A B z)) (hvo : vo ∈ temps hs ++ A ++ B)
    (hfit : lb ≤ vo.rep.len + vo.rep.scale) (hn : n < lb) (hn1 : 1 ≤ n) (hlbb : lb < 2 ^ 30)
    (hz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p) (hzo : ∀ a, constBytes a → S a)
    (hh : R 15 = BitVec.ofNat 64 (deadHead F)) (h25 : R 25 = BitVec.ofNat 64 bcFreeAddr)
    (h21 : R 21 = BitVec.ofNat 64 lb) (h8 : R 8 = BitVec.ofNat 64 n)
    (h23 : R 23 = BitVec.ofNat 64 vo.rep.val) (h18 : R 18 = BitVec.ofNat 64 vo.rep.p)
    (hoom : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps kvClob R' R → MemOnly KTouch M' M →
      DW live S Q 0x80002bcc#64 R' M')
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem) (H' : Heap) (F' : List Blk) (sb1 sb2 : Blk),
      Keeps kvClob R' R →
      BcHeap S M' H' F' (KList [] (some (viewObj sb2 vo (lb - n) n) ::
        some (viewObj sb1 vo 0 (lb - n)) :: hs) A B z) →
      R' 27 = BitVec.ofNat 64 sb1.pay → R' 20 = BitVec.ofNat 64 sb2.pay →
      R' 18 = BitVec.ofNat 64 zeroAddr → R' 17 = BitVec.ofNat 64 z.rep.p →
      MemOnly KTouch M' M →
      DW live S Q 0x80004eb0#64 R' M') :
    DW live S Q 0x800053c0#64 R M := by
  refine ksplit_800053c0 hlive hb hh h25
    (fun R1 M1 kk1 hfr1 => hoom _ _ (kk1.mono (by decide))
      (memOnly_touch_of_alloc hb.heap hfr1)) ?_
  intro R1 M1 H1 F1 sb1 kk1 hvs1 hp1 hd1
  have hvL : vo ∈ KList [] hs A B z := mem_KList hvo
  refine kview_800053d0 hlive hb hvs1 hvL (Nat.le_of_lt hn) hfit (by omega) (by omega) hp1
    ((kk1.get 21).trans h21) ((kk1.get 8).trans h8) ((kk1.get 23).trans h23)
    ((kk1.get 18).trans h18) ?_
  intro R2 M2 kk2 hb2 h23' hfr2
  have t1 : MemOnly KTouch M2 M := hvs1.touchOf hb hfr2
  have hvL2 : vo ∈ viewObj sb1 vo 0 (lb - n) :: KList [] hs A B z := List.mem_cons_of_mem _ hvL
  have kk21 : Keeps kvClob R2 R := (kk2.mono (by decide)).trans (kk1.mono (by decide))
  refine ksplit_800053f4 hlive hb2 ((kk2.get 20).trans hd1) ((kk2.get 25).trans
      ((kk1.get 25).trans h25))
    (fun R3 M3 kk3 hfr3 => hoom _ _ ((kk3.mono (by decide)).trans kk21)
      ((memOnly_touch_of_alloc hb2.heap hfr3).trans t1)) ?_
  intro R3 M3 H2 F2 sb2 kk3 hvs2 hp2
  refine kview_80005400 hlive hb2 hvs2 hvL2 (Nat.le_of_lt hn) hfit (by omega) hn1
    ((ldv_zero_touch (hvs2.touch hb2)).trans ((ldv_zero_touch t1).trans hz)) hzo hp2
    ((kk3.get 21).trans ((kk2.get 21).trans ((kk1.get 21).trans h21)))
    ((kk3.get 8).trans ((kk2.get 8).trans ((kk1.get 8).trans h8)))
    ((kk3.get 23).trans h23') ?_
  intro R4 M4 kk4 hb4 h21' h23'' h18' h17' hfr4
  refine hnext _ _ H2 F2 sb1 sb2 ((kk4.mono (by decide)).trans ((kk3.mono (by decide)).trans kk21))
    ?_ ((kk4.get 27).trans ((kk3.get 27).trans ((kk2.get 27).trans hp1))) ?_ h18' h17' ?_
  · rw [← KList_push, ← KList_push]; exact hb4
  · exact (kk4.get 20).trans hp2
  · exact ((hvs2.touchOf hb2 hfr4).trans t1)

/-- A number object's struct lies inside the number heap. -/
theorem BcHeap.struct_in_heap {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {x : NumObj} (hb : BcHeap S M H F L) (hx : x ∈ L) :
    heapStart ≤ x.rep.p ∧ x.rep.p + 40 ≤ heapEnd := by
  have hxb := hb.blocks x hx
  have hxp := hxb.sPay; have hxsz := hxb.sSz
  have hbf := hb.heap.blk (List.mem_append_right _ hxb.sLive)
  have hlo := hbf.lo; have hfin := hbf.fin; have htop := hbf.top
  simp only [heapStart] at hlo ⊢
  simp only [heapEnd] at htop ⊢
  have e1 : x.sb.pay = x.sb.h + 16 := rfl
  have e2 : x.sb.fin = x.sb.h + 16 + x.sb.sz := rfl
  simp only [Blk.pay, Blk.fin] at hxp hxsz
  omega

/-- **The `v` halves at `0x80004e68`** (`lb < n`): `v1` is a reference to
`_zero_` and `v0` a view of all `lb` digits. -/
theorem kara_vzero {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk}
    {A B : List NumObj} {z vo : NumObj} {hs : List Hd} {lb : Nat}
    (hb : BcHeap S M H F (KList [] hs A B z)) (hvo : vo ∈ temps hs ++ A ++ B)
    (hfit : lb ≤ vo.rep.len + vo.rep.scale) (hlb1 : 1 ≤ lb) (hlbb : lb < 2 ^ 30)
    (hz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p) (hzo : ∀ a, constBytes a → S a)
    (hrefs : z.rep.refs + zeroCount hs + 1 < 2 ^ 31)
    (hh : R 15 = BitVec.ofNat 64 (deadHead F)) (h25 : R 25 = BitVec.ofNat 64 bcFreeAddr)
    (h21 : R 21 = BitVec.ofNat 64 lb) (h23 : R 23 = BitVec.ofNat 64 vo.rep.val)
    (hoom : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps kvClob R' R → MemOnly KTouch M' M →
      DW live S Q 0x80002bcc#64 R' M')
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem) (H' : Heap) (F' : List Blk) (sb : Blk),
      Keeps kvClob R' R →
      BcHeap S M' H' F' (KList [] (some (viewObj sb vo 0 lb) :: none :: hs) A B z) →
      R' 27 = BitVec.ofNat 64 z.rep.p → R' 20 = BitVec.ofNat 64 sb.pay →
      R' 18 = BitVec.ofNat 64 zeroAddr → R' 17 = BitVec.ofNat 64 z.rep.p →
      MemOnly KTouch M' M →
      DW live S Q 0x80004eb0#64 R' M') :
    DW live S Q 0x80004e68#64 R M := by
  have hzL : z.withRefs (z.rep.refs + zeroCount hs) ∈ KList [] hs A B z :=
    List.mem_append_right _ List.mem_cons_self
  have hzb := hb.struct_in_heap hzL
  have hzlo := hzb.1; have hzhi := hzb.2
  simp only [heapStart] at hzlo
  simp only [heapEnd] at hzhi
  have hb' : BcHeap S M H F ((temps hs ++ A) ++
      z.withRefs (z.rep.refs + zeroCount hs) :: B) := by
    simpa only [KList, List.nil_append, List.append_assoc] using hb
  refine kzeroref_80004e68 hlive hb' hz hzo (by simp only [NumObj.withRefs]; omega) ?_
  intro R1 M1 kk1 hb1 hp1 h18' hfr1
  have t1 : MemOnly KTouch M1 M := fun a ha => hfr1 a (by
    simp only [KTouch, bcFreeBytes, bcFreeAddr, freeListAddr, heapStart, heapEnd] at ha ⊢
    omega)
  have ek : KList [] (none :: hs) A B z
      = temps hs ++ A ++ z.withRefs (z.rep.refs + (zeroCount hs + 1)) :: B := by
    simp only [KList, temps_none, zeroCount_none, List.nil_append, Nat.add_assoc]
  have hb1' : BcHeap S M1 H F (KList [] (none :: hs) A B z) := by
    rw [ek]
    simpa only [NumObj.withRefs_withRefs, NumObj.withRefs, Nat.add_assoc] using hb1
  have hz1 : ldv .ld M1 zeroAddr = BitVec.ofNat 64 z.rep.p :=
    (ldv_zero_touch t1).trans hz
  have hvL1 : vo ∈ KList [] (none :: hs) A B z := mem_KList hvo
  refine ksplit_80004e80 hlive hb1' ((kk1.get 15).trans hh) ((kk1.get 25).trans h25) h18' hp1
    hz1 hzo
    (fun R2 M2 kk2 hfr2 => hoom _ _ ((kk2.mono (by decide)).trans (kk1.mono (by decide)))
      ((memOnly_touch_of_alloc hb1'.heap hfr2).trans t1)) ?_
  intro R2 M2 H' F' sb kk2 hvs hp2 h17'
  refine kview_80004e94 hlive hb1' hvs hvL1 hlb1 hfit (by omega) hp2
    ((kk2.get 21).trans ((kk1.get 21).trans h21))
    ((kk2.get 23).trans ((kk1.get 23).trans h23)) ?_
  intro R3 M3 kk3 hb3 hfr3
  refine hnext _ _ H' F' sb ((kk3.mono (by decide)).trans
      ((kk2.mono (by decide)).trans (kk1.mono (by decide)))) ?_
    ((kk3.get 27).trans ((kk2.get 27).trans hp1)) ((kk3.get 20).trans hp2)
    ((kk3.get 18).trans ((kk2.get 18).trans h18'))
    ((kk3.get 17).trans h17') ((hvs.touchOf hb1' hfr3).trans t1)
  rw [← KList_push]; exact hb3

/-! ## A reachable zero-length half

`kara_half` computes the split `n = (max la lb + 1) / 2`, and the dispatch at
`0x80004df4` (`blt s4, s0`) takes the splitting route whenever `n ≤ la`. That
route stores `n_len = la - n` (`subw` at `0x80004e04`, `sw` at `0x80004e10`),
so `la = n` makes a `new_sub_num` of length `0`, and the witnesses below show
the Karatsuba case's own entry conditions admit it (the same holds of `lb` at
the second dispatch).

Such an object is representable: `NumShape` carries `emptyScale` instead of a
positive length, `kview_80004e08` takes `n ≤ la`, and `BcHeap.pushView` takes
any count. The empty half reaches `bc_sub` as the minuend-side argument of
`m1 = u1 - u0` (the zero-scan route `0x8000561c` → `0x80004fa4` →
`0x800054bc`), which is why `_bc_do_compare` takes the two nonzero premises
and `_bc_do_sub` proves its `c = 0` route. -/

/-- The Karatsuba case's entry conditions admit a zero-length half. -/
theorem kara_emptyHalf_reachable :
    ∃ la lb : Nat, 20 ≤ la ∧ 20 ≤ lb ∧ 80 ≤ la + lb ∧ (max la lb + 1) / 2 = la :=
  ⟨27, 53, by decide, by decide, by decide, by decide⟩

/-- And a zero-length `v` half. -/
theorem kara_emptyHalfV_reachable :
    ∃ la lb : Nat, 20 ≤ la ∧ 20 ≤ lb ∧ 80 ≤ la + lb ∧ (max la lb + 1) / 2 = lb :=
  ⟨53, 27, by decide, by decide, by decide, by decide⟩

end Dc.Mach
