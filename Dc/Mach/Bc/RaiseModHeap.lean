import Dc.Mach.Bc.RaiseEntry
import Dc.Mach.Bc.ZeroScanSites

/-!
# Handles on several caller numbers (`bc_raisemod`)

`bc_raisemod` takes one more reference to each of `base`, `expo`, `_one_`
and `_zero_` before its loop, and each of its four slots (`power`,
`exponent`, `temp`, `parity`) holds either such a reference or a new number
of its own. A slot is a handle `RH`: `own y` (a new number) or `ref y` (a
reference to the caller's number `y`). The heap over the caller's `L` is
`RList hs L`: the owned numbers, then `L` with each number's count raised by
the references to it (`rBump`). The four references may name the same
number.

- `RList.own_split` / `RList.ref_split`: the object a handle names.
- `RList.freed_own` / `RList.freed_ref`: dropping a handle's reference.
- `RList.addRef`: one more reference to a number of `L`.
- `BcHeap.perm`: the heap of owners in any order (a callee's new number
  heads the list; `RList.cons_perm` moves it to its slot).
- `BcHeap.p_ne_mid`, `DropAt.unique`: pointers name one number of a heap.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- What a slot of `bc_raisemod` holds: a new number of its own, or one more
reference to the caller's number at `p`. -/
inductive RH
  | own (y : NumObj)
  | ref (y : NumObj)

/-- The number a handle owns. -/
def RH.tmp : RH → List NumObj
  | .own y => [y]
  | .ref _ => []

/-- A handle's reference to the caller's number at `p`. -/
def RH.cnt (p : Nat) : RH → Nat
  | .own _ => 0
  | .ref y => if y.rep.p = p then 1 else 0

/-- A handle's pointer. -/
def RH.p : RH → Nat
  | .own y => y.rep.p
  | .ref y => y.rep.p

/-- The number of the heap a handle names, with the references `hs` hold. -/
def RH.obj (hs : List RH) : RH → NumObj
  | .own y => y
  | .ref y => y.withRefs (y.rep.refs + (hs.map (RH.cnt y.rep.p)).sum)

/-- The number a handle names, its count aside. -/
def RH.base : RH → NumObj
  | .own y => y
  | .ref y => y

theorem RH.obj_p (hs : List RH) (h : RH) : (RH.obj hs h).rep.p = h.p := by cases h <;> rfl
theorem RH.obj_num (hs : List RH) (h : RH) : (RH.obj hs h).rep.num = h.base.rep.num := by
  cases h <;> rfl
theorem RH.obj_len (hs : List RH) (h : RH) : (RH.obj hs h).rep.len = h.base.rep.len := by
  cases h <;> rfl
theorem RH.obj_scale (hs : List RH) (h : RH) : (RH.obj hs h).rep.scale = h.base.rep.scale := by
  cases h <;> rfl
theorem RH.obj_norm (hs : List RH) (h : RH) : (RH.obj hs h).rep.Norm ↔ h.base.rep.Norm := by
  cases h <;> exact Iff.rfl

/-- The numbers the handles own. -/
def rTemps (hs : List RH) : List NumObj := hs.flatMap RH.tmp

/-- The handles' references to the number at `p`. -/
def rCnt (hs : List RH) (p : Nat) : Nat := (hs.map (RH.cnt p)).sum

/-- A caller's number with the handles' references added. -/
def rBump (hs : List RH) (y : NumObj) : NumObj := y.withRefs (y.rep.refs + rCnt hs y.rep.p)

/-- The heap: the owned numbers, then the caller's numbers with the handles'
references. -/
def RList (hs : List RH) (L : List NumObj) : List NumObj := rTemps hs ++ L.map (rBump hs)

theorem rTemps_append (hs1 hs2 : List RH) : rTemps (hs1 ++ hs2) = rTemps hs1 ++ rTemps hs2 := by
  simp only [rTemps, List.flatMap_append]

@[simp] theorem rTemps_nil : rTemps [] = [] := rfl
@[simp] theorem rTemps_own (y : NumObj) (hs : List RH) : rTemps (.own y :: hs) = y :: rTemps hs := rfl
@[simp] theorem rTemps_ref (y : NumObj) (hs : List RH) : rTemps (.ref y :: hs) = rTemps hs := rfl

theorem rCnt_append (hs1 hs2 : List RH) (p : Nat) : rCnt (hs1 ++ hs2) p = rCnt hs1 p + rCnt hs2 p := by
  simp only [rCnt, List.map_append, List.sum_append]

theorem rCnt_cons (h : RH) (hs : List RH) (p : Nat) : rCnt (h :: hs) p = RH.cnt p h + rCnt hs p := by
  simp only [rCnt, List.map_cons, List.sum_cons]

theorem rCnt_mid (hs1 hs2 : List RH) (h : RH) (p : Nat) :
    rCnt (hs1 ++ h :: hs2) p = RH.cnt p h + rCnt (hs1 ++ hs2) p := by
  simp only [rCnt_append, rCnt_cons]; omega

/-- An owned handle adds no reference. -/
theorem rBump_own (hs1 hs2 : List RH) (x : NumObj) :
    rBump (hs1 ++ .own x :: hs2) = rBump (hs1 ++ hs2) := by
  funext y; simp only [rBump, rCnt_mid, RH.cnt, Nat.zero_add]

/-- A reference to another number adds none to `y`. -/
theorem rBump_ref_ne (hs1 hs2 : List RH) {x y : NumObj} (h : y.rep.p ≠ x.rep.p) :
    rBump (hs1 ++ .ref x :: hs2) y = rBump (hs1 ++ hs2) y := by
  simp only [rBump, rCnt_mid, RH.cnt, if_neg (Ne.symm h), Nat.zero_add]

theorem rBump_p (hs : List RH) (y : NumObj) : (rBump hs y).rep.p = y.rep.p := rfl

theorem rBump_owns {hs : List RH} {y : NumObj} (h : y.Owns) : (rBump hs y).Owns := h

theorem map_rBump_congr {hs hs' : List RH} {A : List NumObj}
    (h : ∀ w ∈ A, rBump hs w = rBump hs' w) : A.map (rBump hs) = A.map (rBump hs') :=
  List.map_congr_left h

/-- **An owned handle's number** in the heap. -/
theorem RList.own_split (hs1 hs2 : List RH) (x : NumObj) (L : List NumObj) :
    RList (hs1 ++ .own x :: hs2) L = rTemps hs1 ++ x :: (rTemps hs2 ++ L.map (rBump (hs1 ++ hs2))) := by
  simp only [RList, rTemps_append, rBump_own, rTemps_own, List.append_assoc, List.cons_append]

/-- **A referenced number** `y` of `L = A ++ y :: B` in the heap. -/
theorem RList.ref_split (hs : List RH) {A B : List NumObj} (y : NumObj) :
    RList hs (A ++ y :: B) = (rTemps hs ++ A.map (rBump hs)) ++ rBump hs y :: B.map (rBump hs) := by
  simp only [RList, List.map_append, List.map_cons, List.append_assoc]

/-- Dropping an owned handle's only reference: its number leaves. -/
theorem RList.freed_own {hs1 hs2 : List RH} {x : NumObj} {L L' : List NumObj} (hr : x.rep.refs = 1)
    (h : FreedRest (rTemps hs1) (rTemps hs2 ++ L.map (rBump (hs1 ++ hs2))) x L') :
    L' = RList (hs1 ++ hs2) L := by
  cases h with
  | dec h2 => omega
  | rel _ => simp only [RList, rTemps_append, List.append_assoc]

/-- Dropping a reference to `y` (no other number of `L` at its pointer): the
handle leaves. -/
theorem RList.freed_ref {hs1 hs2 : List RH} {A B : List NumObj} {y : NumObj} {L' : List NumObj}
    (hd : ∀ w ∈ A ++ B, w.rep.p ≠ y.rep.p) (hy : 1 ≤ y.rep.refs)
    (h : FreedRest (rTemps (hs1 ++ .ref y :: hs2) ++ A.map (rBump (hs1 ++ .ref y :: hs2)))
      (B.map (rBump (hs1 ++ .ref y :: hs2))) (rBump (hs1 ++ .ref y :: hs2) y) L') :
    L' = RList (hs1 ++ hs2) (A ++ y :: B) := by
  have hc := rCnt_mid hs1 hs2 (.ref y) y.rep.p
  simp only [RH.cnt, ite_true] at hc
  have hA := map_rBump_congr (hs := hs1 ++ .ref y :: hs2) (hs' := hs1 ++ hs2) (A := A)
    fun w hw => rBump_ref_ne hs1 hs2 (hd w (List.mem_append_left _ hw))
  have hB := map_rBump_congr (hs := hs1 ++ .ref y :: hs2) (hs' := hs1 ++ hs2) (A := B)
    fun w hw => rBump_ref_ne hs1 hs2 (hd w (List.mem_append_right _ hw))
  have ht : rTemps (hs1 ++ .ref y :: hs2) = rTemps (hs1 ++ hs2) := by
    simp only [rTemps_append, rTemps_ref]
  have hy' : (rBump (hs1 ++ .ref y :: hs2) y).decRef = rBump (hs1 ++ hs2) y := by
    simp only [NumObj.decRef_eq, rBump, NumObj.withRefs_withRefs, NumObj.withRefs_refs, hc]
    congr 1; omega
  cases h with
  | dec _ => rw [RList.ref_split, hA, hB, ht, hy']
  | rel h1 => simp only [rBump, NumObj.withRefs_refs, hc] at h1; omega

/-- **One more reference** to `y` of `L = A ++ y :: B`: its count raised in
the heap is the reference handle added (no other number of `L` at its
pointer). -/
theorem RList.addRef (hs : List RH) {A B : List NumObj} {y : NumObj}
    (hd : ∀ w ∈ A ++ B, w.rep.p ≠ y.rep.p) :
    (rTemps hs ++ A.map (rBump hs)) ++ (rBump hs y).withRefs ((rBump hs y).rep.refs + 1) ::
      B.map (rBump hs) = RList (hs ++ [.ref y]) (A ++ y :: B) := by
  have hA := map_rBump_congr (hs := hs ++ [.ref y]) (hs' := hs) (A := A) fun w hw => by
    have := rBump_ref_ne hs [] (hd w (List.mem_append_left _ hw)); simpa using this
  have hB := map_rBump_congr (hs := hs ++ [.ref y]) (hs' := hs) (A := B) fun w hw => by
    have := rBump_ref_ne hs [] (hd w (List.mem_append_right _ hw)); simpa using this
  have ht : rTemps (hs ++ [.ref y]) = rTemps hs := by
    simp only [rTemps_append, rTemps_ref, rTemps_nil, List.append_nil]
  have hy' : (rBump hs y).withRefs ((rBump hs y).rep.refs + 1) = rBump (hs ++ [.ref y]) y := by
    simp only [rBump, NumObj.withRefs_withRefs, NumObj.withRefs_refs, rCnt_append, rCnt_cons, RH.cnt,
      ite_true]
    rw [show rCnt [] y.rep.p = 0 from rfl,
      show y.rep.refs + (rCnt hs y.rep.p + (1 + 0)) = y.rep.refs + rCnt hs y.rep.p + 1 by omega]
  rw [RList.ref_split, hA, hB, ht, ← hy']

/-- A new number at the head of the heap is its handle's. -/
theorem RList.cons_perm (hs1 hs2 : List RH) (y : NumObj) (L : List NumObj) :
    (y :: RList (hs1 ++ hs2) L).Perm (RList (hs1 ++ .own y :: hs2) L) := by
  rw [RList.own_split]
  simp only [RList, rTemps_append, List.append_assoc]
  exact List.perm_middle.symm

/-- Every number of the heap owns its digits. -/
theorem RList.owns {hs : List RH} {L : List NumObj} (ht : ∀ y, .own y ∈ hs → y.Owns)
    (hL : ∀ y ∈ L, y.Owns) : ∀ y ∈ RList hs L, y.Owns := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · obtain ⟨h0, hh, hy⟩ := List.mem_flatMap.mp h
    cases h0 with
    | own x =>
      simp only [RH.tmp, List.mem_singleton] at hy
      subst hy; exact ht _ hh
    | ref _ => cases hy
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    exact rBump_owns (hL w hw)

/-- **The number heap in any order**, when every number owns its digits. -/
theorem BcHeap.perm {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {L L' : List NumObj}
    (hb : BcHeap S X M H F L) (hp : L.Perm L') (ho : ∀ y ∈ L', y.Owns) : BcHeap S X M H F L' := by
  have hv : ViewsOwned L' := by
    have := ViewsOwned.prefix (T := []) .nil (P := L') fun y hy => .inl (ho y hy)
    simpa only [List.append_nil] using this
  exact ⟨hb.heap, hb.dead, hb.deadLive, fun x hx => hb.nums x (hp.mem_iff.mpr hx),
    fun x hx => hb.blocks x (hp.mem_iff.mpr hx),
    (List.Perm.append_left F (hp.flatMap_right NumObj.blocks)).nodup_iff.mp hb.distinct, hv,
    hb.globOwn⟩

/-- Objects after `x` in the heap have other struct pointers. -/
theorem BcHeap.p_ne_mid {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S X M H F (L1 ++ x :: L2)) {y : NumObj}
    (hy : y ∈ L2) : y.rep.p ≠ x.rep.p := by
  have hp : (L1 ++ x :: L2).Perm ((L1 ++ L2) ++ [x]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hd : (F ++ objBlocks ((L1 ++ L2) ++ [x])).Nodup :=
    (List.Perm.append_left F (hp.flatMap_right NumObj.blocks)).nodup_iff.mp h.distinct
  have hb : ∀ w ∈ (L1 ++ L2) ++ [x], w ∈ L1 ++ x :: L2 := fun w hw => hp.mem_iff.mpr hw
  have hd' := (List.nodup_append.mp hd).2.1
  rw [objBlocks_append] at hd'
  have hne : y.sb ≠ x.sb := (List.nodup_append.mp hd').2.2 _
    (List.mem_flatMap.mpr ⟨y, List.mem_append_right _ hy, y.sb_mem_blocks⟩) _
    (List.mem_flatMap.mpr ⟨x, List.mem_singleton_self _, x.sb_mem_blocks⟩)
  have hxb := h.blocks x (List.mem_append_right _ List.mem_cons_self)
  have hyb := h.blocks y (List.mem_append_right _ (List.mem_cons_of_mem _ hy))
  have hxs := hxb.sSz; have hys := hyb.sSz
  intro e
  rw [hxb.sPay, hyb.sPay] at e
  exact live_apart h.heap hyb.sLive hxb.sLive hne (a := y.sb.pay)
    ⟨Nat.le_refl _, by simp only [Blk.fin, Blk.pay]; omega⟩
    ⟨by omega, by simp only [Blk.fin, Blk.pay] at e ⊢; omega⟩

/-- No other number of the heap has `x`'s struct pointer. -/
theorem BcHeap.p_ne_all {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk}
    {L1 L2 : List NumObj} {x : NumObj} (h : BcHeap S X M H F (L1 ++ x :: L2)) :
    ∀ y ∈ L1 ++ L2, y.rep.p ≠ x.rep.p := fun y hy => by
  rcases List.mem_append.mp hy with hy | hy
  · exact h.p_ne_split hy
  · exact h.p_ne_mid hy

/-- Splits of a list at numbers with one pointer, unique among the list's. -/
theorem split_unique {x x' : NumObj} {L2 L2' : List NumObj} (hp : x'.rep.p = x.rep.p) :
    ∀ {L1 L1' : List NumObj}, (∀ y ∈ L1 ++ L2, y.rep.p ≠ x.rep.p) →
      L1 ++ x :: L2 = L1' ++ x' :: L2' → L1 = L1' ∧ x = x' ∧ L2 = L2'
  | [], [], _, e => by simp only [List.nil_append, List.cons.injEq] at e; exact ⟨rfl, e.1, e.2⟩
  | [], w :: L1', hd, e => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, e⟩ := e
    exact absurd hp (hd x' (by rw [e]; simp))
  | w :: L1, [], hd, e => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, _⟩ := e
    exact absurd hp (hd w (by simp))
  | w :: L1, w' :: L1', hd, e => by
    simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, e⟩ := e
    obtain ⟨h1, h2, h3⟩ := split_unique hp (fun y hy => hd y (List.mem_cons_of_mem _ hy)) e
    exact ⟨by rw [h1], h2, h3⟩

/-! ## Distinct pointers -/

/-- The numbers of a list have distinct struct pointers. -/
def PDist (L : List NumObj) : Prop := (L.map (·.rep.p)).Nodup

theorem pairwise_of_split {R : NumObj → NumObj → Prop} :
    ∀ (L : List NumObj), (∀ L1 x L2, L = L1 ++ x :: L2 → ∀ y ∈ L2, R x y) → L.Pairwise R
  | [], _ => .nil
  | a :: L, h => .cons (h [] a L rfl) (pairwise_of_split L fun L1 x L2 e => h (a :: L1) x L2 (by
      rw [e]; rfl))

/-- A heap's numbers have distinct struct pointers. -/
theorem BcHeap.pdist {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    (h : BcHeap S X M H F L) : PDist L := by
  unfold PDist
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact pairwise_of_split L fun L1 x L2 e y hy => by
    subst e; exact (h.p_ne_mid hy).symm

/-- In a list of distinct pointers, the others differ from `x`'s. -/
theorem PDist.ne {L1 L2 : List NumObj} {x : NumObj} (h : PDist (L1 ++ x :: L2)) :
    ∀ y ∈ L1 ++ L2, y.rep.p ≠ x.rep.p := by
  intro y hy e
  unfold PDist at h
  rw [List.map_append, List.map_cons] at h
  have h2 := List.nodup_cons.mp (List.perm_middle.nodup_iff.mp h)
  apply h2.1
  rw [← e, ← List.map_append]
  exact List.mem_map_of_mem hy

theorem PDist.sublist {L L' : List NumObj} (h : PDist L) (hs : L'.Sublist L) : PDist L' :=
  List.Nodup.sublist (hs.map _) h

theorem map_p_rBump (hs : List RH) (L : List NumObj) :
    (L.map (rBump hs)).map (·.rep.p) = L.map (·.rep.p) := by
  simp only [List.map_map]; rfl

/-- Dropping a handle keeps the pointers distinct. -/
theorem PDist.drop {hs1 hs2 : List RH} {h : RH} {L : List NumObj}
    (hd : PDist (RList (hs1 ++ h :: hs2) L)) : PDist (RList (hs1 ++ hs2) L) := by
  unfold PDist RList at *
  rw [List.map_append, map_p_rBump] at *
  refine hd.sublist (List.Sublist.append ?_ (List.Sublist.refl _))
  refine List.Sublist.map _ ?_
  rw [rTemps_append, rTemps_append]
  exact List.Sublist.append (List.Sublist.refl _) (by
    cases h with
    | own y => exact List.sublist_cons_self _ _
    | ref _ => exact List.Sublist.refl _)

/-- **A reference dropped at a pointer** of a list of distinct pointers is the
drop at that number. -/
theorem DropAt.unique {L1 L2 L' : List NumObj} {x : NumObj} (h : PDist (L1 ++ x :: L2))
    (hd : DropAt (L1 ++ x :: L2) x.rep.p L') : FreedRest L1 L2 x L' := by
  obtain ⟨L1', L2', x', e, hp, hf⟩ := hd
  obtain ⟨rfl, rfl, rfl⟩ := split_unique hp h.ne e
  exact hf

/-! ## The number a handle names -/

/-- A handle of `bc_raisemod` names a number: a new number with one
reference, or a number of the caller's `L`. -/
def RHOK (L : List NumObj) : RH → Prop
  | .own y => y.rep.refs = 1 ∧ y.Owns
  | .ref y => ∃ A B, L = A ++ y :: B ∧ 1 ≤ y.rep.refs

/-- **The object a handle names**, and what dropping its reference leaves:
the heap without the handle. -/
theorem RList.drop {hs1 hs2 : List RH} {h : RH} {L : List NumObj}
    (hd : PDist (RList (hs1 ++ h :: hs2) L)) (hh : RHOK L h) :
    ∃ L1 L2 x, RList (hs1 ++ h :: hs2) L = L1 ++ x :: L2 ∧ x.rep.p = h.p ∧ 1 ≤ x.rep.refs ∧
      (x.rep.refs = 1 → x.Owns) ∧ (∀ y, h = .ref y → 2 ≤ x.rep.refs) ∧
      x = RH.obj (hs1 ++ h :: hs2) h ∧
      ∀ L', FreedRest L1 L2 x L' → L' = RList (hs1 ++ hs2) L := by
  cases h with
  | own y =>
    obtain ⟨hr, ho⟩ := hh
    exact ⟨_, _, y, RList.own_split hs1 hs2 y L, rfl, by omega, fun _ => ho, (fun _ h => by cases h), rfl,
      fun L' hf => RList.freed_own hr hf⟩
  | ref y =>
    obtain ⟨A, B, rfl, hy⟩ := hh
    rw [RList.ref_split] at hd ⊢
    have hne := hd.ne
    refine ⟨_, _, _, rfl, rfl, by simp only [rBump, NumObj.withRefs_refs]; omega, fun h1 => ?_,
      fun _ _ => ?_, rfl, fun L' hf => RList.freed_ref (fun w hw => ?_) hy hf⟩
    · simp only [rBump, NumObj.withRefs_refs, rCnt_mid, RH.cnt, ite_true] at h1; omega
    · simp only [rBump, NumObj.withRefs_refs, rCnt_mid, RH.cnt, ite_true]; omega
    · have := hne (rBump _ w) (by
        rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hw))
        · exact List.mem_append_right _ (List.mem_map_of_mem hw))
      simpa only [rBump_p] using this

/-- A handle's number is in the heap. -/
theorem RH.obj_mem {hs : List RH} {L : List NumObj} {h : RH} (hm : h ∈ hs) (hh : RHOK L h) :
    RH.obj hs h ∈ RList hs L := by
  cases h with
  | own y => exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, hm, List.mem_singleton_self _⟩)
  | ref y =>
    obtain ⟨A, B, rfl, _⟩ := hh
    exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_append_right _ List.mem_cons_self))

end Dc.Mach
