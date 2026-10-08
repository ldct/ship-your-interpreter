import Dc.Mach.Bc.KaraFree

/-!
# `_bc_rec_mul`'s Karatsuba step: handles and the number heap

The step holds nine numbers (`u1`, `u0`, `v1`, `v0`, `d1`, `d2`, `m1`, `m2`,
`m3`), each a temporary object of its own or a reference to `_zero_`
(`bc_copy_num (_zero_)`).

- `Hd`: a handle (`none` is a reference to `_zero_`).
- `KList P hs A B z`: the heap's objects: owners `P` (the product), the
  temporaries of `hs` in order, the caller's `A ++ z :: B` with `z`'s count
  raised by the references in `hs`.
- `kfreeH`: an inlined free (`KSite`) of the first handle.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- A handle: a temporary object, or (`none`) a reference to `_zero_`. -/
abbrev Hd := Option NumObj

/-- The temporaries of a list of handles. -/
abbrev temps (hs : List Hd) : List NumObj := hs.filterMap id

/-- The references to `_zero_` among the handles. -/
def zeroCount : List Hd → Nat
  | [] => 0
  | none :: hs => zeroCount hs + 1
  | some _ :: hs => zeroCount hs

@[simp] theorem zeroCount_nil : zeroCount [] = 0 := rfl
@[simp] theorem zeroCount_none (hs : List Hd) : zeroCount (none :: hs) = zeroCount hs + 1 := rfl
@[simp] theorem zeroCount_some (x : NumObj) (hs : List Hd) :
    zeroCount (some x :: hs) = zeroCount hs := rfl

/-- The heap's objects under the step: owners `P`, the temporaries of `hs`,
the caller's `A ++ z :: B` with `z` referenced by every `none` of `hs`. -/
def KList (P : List NumObj) (hs : List Hd) (A B : List NumObj) (z : NumObj) : List NumObj :=
  P ++ temps hs ++ A ++ z.withRefs (z.rep.refs + zeroCount hs) :: B

/-- A handle's pointer. -/
def Hd.p (z : NumObj) : Hd → Nat
  | some x => x.rep.p
  | none => z.rep.p

/-- Every temporary has one reference. -/
def HdOK (hs : List Hd) : Prop := ∀ x, some x ∈ hs → x.rep.refs = 1

theorem HdOK.head {h : Hd} {hs : List Hd} (hk : HdOK (h :: hs)) : ∀ x, h = some x → x.rep.refs = 1 :=
  fun x e => hk x (by rw [← e]; exact List.mem_cons_self)

theorem HdOK.tail {h : Hd} {hs : List Hd} (hk : HdOK (h :: hs)) : HdOK hs :=
  fun x m => hk x (List.mem_cons_of_mem _ m)

/-- The object a handle names. -/
def Hd.obj (hs : List Hd) (z : NumObj) : Hd → NumObj
  | some x => x
  | none => z.withRefs (z.rep.refs + zeroCount (none :: hs))

/-- The object a handle of `hs` names in `KList P hs A B z`. -/
def Hd.objIn (hs : List Hd) (z : NumObj) : Hd → NumObj
  | some x => x
  | none => z.withRefs (z.rep.refs + zeroCount hs)

theorem Hd.objIn_p (hs : List Hd) (z : NumObj) (h : Hd) : (Hd.objIn hs z h).rep.p = Hd.p z h := by
  cases h <;> rfl

theorem Hd.objIn_mem {hs : List Hd} {h : Hd} (hm : h ∈ hs) (P A B : List NumObj) (z : NumObj) :
    Hd.objIn hs z h ∈ KList P hs A B z := by
  cases h with
  | some x =>
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_filterMap.mpr ⟨some x, hm, rfl⟩)))
  | none => exact List.mem_append_right _ List.mem_cons_self

theorem Hd.obj_p (hs : List Hd) (z : NumObj) (h : Hd) : (Hd.obj hs z h).rep.p = Hd.p z h := by
  cases h <;> rfl

theorem KList_some (P : List NumObj) (x : NumObj) (hs : List Hd) (A B : List NumObj) (z : NumObj) :
    KList P (some x :: hs) A B z = P ++ x :: (temps hs ++ A ++
      z.withRefs (z.rep.refs + zeroCount hs) :: B) := by
  simp only [KList, temps, List.filterMap_cons, id, zeroCount_some, List.append_assoc,
    List.cons_append]

theorem KList_none (P : List NumObj) (hs : List Hd) (A B : List NumObj) (z : NumObj) :
    KList P (none :: hs) A B z = (P ++ temps hs ++ A) ++
      z.withRefs (z.rep.refs + zeroCount (none :: hs)) :: B := by
  simp only [KList, temps, List.filterMap_cons, id]

theorem KList_rest (P : List NumObj) (hs : List Hd) (A B : List NumObj) (z : NumObj) :
    KList P hs A B z = P ++ (temps hs ++ A ++ z.withRefs (z.rep.refs + zeroCount hs) :: B) := by
  simp only [KList, List.append_assoc]

theorem KList_single (y : NumObj) (hs : List Hd) (A B : List NumObj) (z : NumObj) :
    KList [y] hs A B z = y :: KList [] hs A B z := rfl

theorem KList_nil (P A B : List NumObj) (z : NumObj) : KList P [] A B z = P ++ (A ++ z :: B) := by
  simp only [KList, temps, List.filterMap_nil, zeroCount_nil, Nat.add_zero, NumObj.withRefs_self,
    List.append_nil, List.append_assoc]

/-- Two owners of the heap have different digit buffers. -/
theorem BcHeap.owner_db_ne {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk}
    {P L2 : List NumObj} {x : NumObj} (h : BcHeap S M H F (P ++ x :: L2)) (hx : x.Owns)
    {y : NumObj} (hy : y ∈ P) (hyo : y.Owns) : y.db ≠ x.db := by
  have hd := (List.nodup_append.mp h.distinct).2.1
  rw [objBlocks_append, objBlocks_cons] at hd
  have h1 := (List.nodup_append.mp hd).2.2
  exact h1 _ (mem_objBlocks_db hy hyo) _
    (List.mem_append_left _ (by rw [NumObj.blocks_own hx]; simp))

/-- **The first handle freed** at an inlined free site. -/
theorem kfreeH {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc N : BitVec 64} {fr : Nat → Prop}
    {Loc : (Nat → BitVec 64) → Mem → NumObj → Prop} (site : KSite live S Q pc N fr Loc)
    {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {P A B : List NumObj}
    {z : NumObj} {h : Hd} {hs : List Hd}
    (hb : BcHeap S M H F (KList P (h :: hs) A B z)) (hP : ∀ y ∈ P, y.Owns)
    (hok : ∀ x, h = some x → x.rep.refs = 1) (hz : 1 ≤ z.rep.refs)
    (hl : Loc R M (Hd.obj hs z h))
    (hk : ∀ R' M' H' F', Keeps [1, 10, 14, 15] R' R → BcHeap S M' H' F' (KList P hs A B z) →
      OutFrame fr M' M → DW live S Q N R' M') :
    DW live S Q pc R M := by
  cases h with
  | some x =>
    rw [KList_some] at hb
    have hr : x.rep.refs = 1 := hok x rfl
    refine site _ _ _ _ _ _ _ hb (by omega) (fun _ ho y hy => hb.owner_db_ne ho hy (hP y hy)) hl ?_
    intro R' M' H' F' L' hk' hf hb' ho
    cases hf with
    | dec h2 => omega
    | rel _ => exact hk _ _ _ _ hk' (by simpa only [KList, List.append_assoc] using hb') ho
  | none =>
    rw [KList_none] at hb
    refine site _ _ _ _ _ _ _ hb (by simp only [NumObj.withRefs]; omega)
      (fun h1 => by simp only [NumObj.withRefs, zeroCount_none] at h1; omega) hl ?_
    intro R' M' H' F' L' hk' hf hb' ho
    cases hf with
    | dec _ =>
      have he : (z.withRefs (z.rep.refs + zeroCount (none :: hs))).decRef =
          z.withRefs (z.rep.refs + zeroCount hs) := by
        simp only [NumObj.decRef_eq, NumObj.withRefs_withRefs, NumObj.withRefs, zeroCount_none]
        congr 2
      rw [he] at hb'
      exact hk _ _ _ _ hk' (by simpa only [KList, List.append_assoc] using hb') ho
    | rel h1 => simp only [NumObj.withRefs, zeroCount_none] at h1; omega

end Dc.Mach
