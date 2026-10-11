import Dc.Mach.Bc.KaraTrimSites

/-!
# `_bc_rec_mul`'s Karatsuba step: the four leading-zero trims

From `0x80004eb0` the step trims the four halves in turn (`x24`, `x19`,
`x27`, `x20`) and arrives at `0x80004f70`. The four spans
(`KaraTrimSites.lean`) differ only in the register and the span, so they are
packaged as one `KTrim` site; `ktrimHd` applies a site to one handle of a
`KList`, and `ktrims` chains all four.

A `none` handle is a reference to `_zero_`, whose single digit is `0`: the
trim keeps at least one digit, so it changes nothing.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- **A leading-zero trim site**: the object named by the register `r` has its
`n_value` advanced past its leading zeros and `n_len` shrunk, reaching `N`. -/
structure KTrim (live S : Nat → Prop) (X : Raws) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (pc N : BitVec 64) (r : Nat) : Prop where
  run : ∀ (M : Mem) (R : Nat → BitVec 64) (H : Heap) (F : List Blk) (L1 L2 : List NumObj)
    (x : NumObj), BcHeap S X M H F (L1 ++ x :: L2) → R r = BitVec.ofNat 64 x.rep.p →
    (∀ (R' : Nat → BitVec 64) (M' : Mem) (j : Nat), Keeps [12, 13, 14, 15] R' R →
      BcHeap S X M' H F (L1 ++ { x with rep := x.rep.drop j } :: L2) →
      lzCount (x.rep.len - 1) x.rep.ds = j →
      MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M' M →
      DW live S Q N R' M') →
    DW live S Q pc R M

/-- The trim of `u1` at `0x80004eb0`. -/
theorem ktrimSite_80004eb0 {live S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    KTrim live S X Q 0x80004eb0#64 0x80004ee0#64 24 :=
  ⟨fun _ _ _ _ _ _ _ hb hr hk => ktrim_80004eb0 hlive hb hr hk⟩

/-- The trim of `u0` at `0x80004ee0`. -/
theorem ktrimSite_80004ee0 {live S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    KTrim live S X Q 0x80004ee0#64 0x80004f10#64 19 :=
  ⟨fun _ _ _ _ _ _ _ hb hr hk => ktrim_80004ee0 hlive hb hr hk⟩

/-- The trim of `v1` at `0x80004f10`. -/
theorem ktrimSite_80004f10 {live S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    KTrim live S X Q 0x80004f10#64 0x80004f40#64 27 :=
  ⟨fun _ _ _ _ _ _ _ hb hr hk => ktrim_80004f10 hlive hb hr hk⟩

/-- The trim of `v0` at `0x80004f40`. -/
theorem ktrimSite_80004f40 {live S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1) :
    KTrim live S X Q 0x80004f40#64 0x80004f70#64 20 :=
  ⟨fun _ _ _ _ _ _ _ hb hr hk => ktrim_80004f40 hlive hb hr hk⟩

/-- A handle with its leading zeros dropped. -/
def Hd.trim (j : Nat) : Hd → Hd
  | some x => some { x with rep := x.rep.drop j }
  | none => none

/-- A handle's leading-zero count (`_zero_` keeps its one digit). -/
def Hd.lz : Hd → Nat
  | some x => lzCount (x.rep.len - 1) x.rep.ds
  | none => 0

@[simp] theorem Hd.trim_none (j : Nat) : Hd.trim j none = none := rfl

@[simp] theorem Hd.p_trim (z : NumObj) (j : Nat) (h : Hd) : Hd.p z (h.trim j) = Hd.p z h := by
  cases h <;> rfl

theorem temps_append (a b : List Hd) : temps (a ++ b) = temps a ++ temps b :=
  List.filterMap_append

theorem temps_some (x : NumObj) (t : List Hd) : temps (some x :: t) = x :: temps t := rfl

theorem temps_none (t : List Hd) : temps (none :: t) = temps t := rfl

theorem zeroCount_append : ∀ (a b : List Hd), zeroCount (a ++ b) = zeroCount a + zeroCount b
  | [], _ => by simp only [List.nil_append, zeroCount_nil, Nat.zero_add]
  | none :: a, b => by
    simp only [List.cons_append, zeroCount_none, zeroCount_append a b]; omega
  | some _ :: a, b => by
    simp only [List.cons_append, zeroCount_some, zeroCount_append a b]

/-- Replacing one handle by its trim leaves the references to `_zero_`. -/
theorem zeroCount_trim (pre post : List Hd) (h : Hd) (j : Nat) :
    zeroCount (pre ++ h.trim j :: post) = zeroCount (pre ++ h :: post) := by
  cases h with
  | none => rfl
  | some x => simp only [Hd.trim, zeroCount_append, zeroCount_some]

/-- **One handle trimmed**: the site's span applied to the handle `h` of
`KList [] (pre ++ h :: post) A B z`. -/
theorem ktrimHd {live S : Nat → Prop} {X : Raws} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {pc N : BitVec 64} {r : Nat} (site : KTrim live S X Q pc N r)
    {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {pre post : List Hd}
    {A B : List NumObj} {z : NumObj} {h : Hd}
    (hb : BcHeap S X M H F (KList [] (pre ++ h :: post) A B z)) (hz : z.rep.len = 1)
    (hr : R r = BitVec.ofNat 64 (Hd.p z h))
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [12, 13, 14, 15] R' R →
      BcHeap S X M' H F (KList [] (pre ++ h.trim h.lz :: post) A B z) →
      MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M' M →
      DW live S Q N R' M') :
    DW live S Q pc R M := by
  cases h with
  | some x =>
    have e : ∀ y : NumObj, KList [] (pre ++ some y :: post) A B z =
        temps pre ++ y :: (temps post ++ A ++
          z.withRefs (z.rep.refs + zeroCount (pre ++ some x :: post)) :: B) := by
      intro y
      rw [KList, zeroCount_append, zeroCount_append, zeroCount_some, zeroCount_some,
        temps_append, temps_some]
      simp only [List.nil_append, List.append_assoc, List.cons_append]
    rw [e x] at hb
    refine site.run _ _ _ _ _ _ _ hb hr ?_
    intro R' M' j kk hb' hj hmo
    refine hnext _ _ kk ?_ hmo
    rw [show Hd.lz (some x) = j from hj,
      show Hd.trim j (some x) = some { x with rep := x.rep.drop j } from rfl, e]
    exact hb'
  | none =>
    have e : KList [] (pre ++ none :: post) A B z =
        (temps pre ++ temps post ++ A) ++
          z.withRefs (z.rep.refs + zeroCount (pre ++ none :: post)) :: B := by
      rw [KList, temps_append, temps_none]
      simp only [List.nil_append, List.append_assoc]
    rw [e] at hb
    refine site.run _ _ _ _ _ _ _ hb hr ?_
    intro R' M' j kk hb' hj hmo
    have hj0 : j = 0 := by
      rw [← hj]
      have : (z.withRefs (z.rep.refs + zeroCount (pre ++ none :: post))).rep.len = 1 := hz
      rw [this]
      rfl
    subst hj0
    refine hnext _ _ kk ?_ hmo
    rw [Hd.trim_none, e, NumRep.drop_zero] at *
    exact hb'

/-- **The four trims** from `0x80004eb0` to `0x80004f70`: `u1`, `u0`, `v1`
and `v0` in turn. The handles are listed in the order the step pushed them
(`v0` last), so `x24` names the last of the list. -/
theorem ktrims {live S : Nat → Prop} {X : Raws} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk}
    {A B : List NumObj} {z : NumObj} {h1 h2 h3 h4 : Hd}
    (hb : BcHeap S X M H F (KList [] [h4, h3, h2, h1] A B z)) (hz : z.rep.len = 1)
    (hr24 : R 24 = BitVec.ofNat 64 (Hd.p z h1)) (hr19 : R 19 = BitVec.ofNat 64 (Hd.p z h2))
    (hr27 : R 27 = BitVec.ofNat 64 (Hd.p z h3)) (hr20 : R 20 = BitVec.ofNat 64 (Hd.p z h4))
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [12, 13, 14, 15] R' R →
      BcHeap S X M' H F (KList [] [h4.trim h4.lz, h3.trim h3.lz, h2.trim h2.lz, h1.trim h1.lz]
        A B z) →
      MemOnly (fun a => heapStart ≤ a ∧ a < heapEnd) M' M →
      DW live S Q 0x80004f70#64 R' M') :
    DW live S Q 0x80004eb0#64 R M := by
  refine ktrimHd (pre := [h4, h3, h2]) (post := []) (ktrimSite_80004eb0 hlive) hb hz hr24 ?_
  intro R1 M1 kk1 hb1 hmo1
  refine ktrimHd (pre := [h4, h3]) (post := [h1.trim h1.lz]) (ktrimSite_80004ee0 hlive) hb1 hz
    ((kk1.get 19).trans hr19) ?_
  intro R2 M2 kk2 hb2 hmo2
  refine ktrimHd (pre := [h4]) (post := [h2.trim h2.lz, h1.trim h1.lz])
    (ktrimSite_80004f10 hlive) hb2 hz ((kk2.get 27).trans ((kk1.get 27).trans hr27)) ?_
  intro R3 M3 kk3 hb3 hmo3
  refine ktrimHd (pre := []) (post := [h3.trim h3.lz, h2.trim h2.lz, h1.trim h1.lz])
    (ktrimSite_80004f40 hlive) hb3 hz
    ((kk3.get 20).trans ((kk2.get 20).trans ((kk1.get 20).trans hr20))) ?_
  intro R4 M4 kk4 hb4 hmo4
  exact hnext _ _ (kk4.trans (kk3.trans (kk2.trans kk1))) hb4
    (hmo4.trans (hmo3.trans (hmo2.trans hmo1)))

end Dc.Mach
