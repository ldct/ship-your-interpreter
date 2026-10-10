import VsaIris.Vsa.Console
import VsaIris.DlHeap
import VsaIris.Call

/-!
# Adequacy's ownership split at a boot configuration

`vsa_adequacy_exit` hands the client one big separating conjunction over a
register map and one over a memory map. A boot reads both off the
configuration on a list of keys (`bmap`); `sepL_of_bmap` turns either into one
points-to per key, `textOwn_of_sepL` persists the code bytes into the run's
read-only text, and `ownSet_of_sepL` packages the owned bytes.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode Iris.BI.BigSepM

/-- The finite map holding `f` on exactly the keys of `l`. -/
def bmap {V : Type} (f : Nat → V) : List Nat → NatMap V
  | [] => ∅
  | r :: rest => PartialMap.insert (bmap f rest) r (f r)

theorem bmap_get? {V : Type} (f : Nat → V) :
    ∀ (l : List Nat) (k : Nat), PartialMap.get? (bmap f l) k = if k ∈ l then some (f k) else none
  | [], k => by simp [bmap, LawfulPartialMap.get?_empty]
  | a :: rest, k => by
    simp only [bmap, Iris.Std.LawfulPartialMap.get?_insert, bmap_get? f rest k, List.mem_cons]
    by_cases h : a = k
    · subst h; simp
    · simp [h, Ne.symm h]

/-- The map agrees with the function it is read off. -/
theorem bmap_agree {V : Type} (f : Nat → V) (l : List Nat) :
    ∀ k v, PartialMap.get? (bmap f l) k = some v → f k = v := by
  intro k v hk
  rw [bmap_get?] at hk
  by_cases hm : k ∈ l
  · simp only [hm, ↓reduceIte] at hk; exact Option.some.inj hk
  · simp only [hm, ↓reduceIte] at hk; exact absurd hk (by simp)

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **One assertion per key** out of a big-op over `bmap`. -/
theorem sepL_of_bmap {V : Type} (P : Nat → V → IProp GF) (f : Nat → V) :
    ∀ (l : List Nat), l.Nodup →
      ([∗map] k ↦ v ∈ bmap f l, P k v) ⊢ sepL (GF := GF) l (fun r => P r (f r))
  | [], _ => by
    rw [sepL_nil]
    exact (bigSepM_eqv_empty (M := NatMap) rfl).1
  | a :: rest, hnd => by
    rw [List.nodup_cons] at hnd
    have hnone : PartialMap.get? (bmap f rest) a = none := by
      rw [bmap_get?]; simp only [hnd.1, ↓reduceIte]
    rw [show bmap f (a :: rest) = PartialMap.insert (bmap f rest) a (f a) from rfl, sepL_cons]
    refine (bigSepM_insert (M := NatMap) hnone).1.trans ?_
    iintro ⟨Ha, Hr⟩
    iframe Ha
    iapply sepL_of_bmap P f rest hnd.2 $$ Hr

/-- A byte points-to discarded to a read-only one. -/
theorem mem_persist (a : Nat) (b : BitVec 8) : (a ↦ₘ b) ⊢@{IProp GF} |==> a ↦ₘ□ b := by
  unfold memPointsTo
  iintro H
  iapply ghost_map_elem_persist $$ H

/-- **The code bytes, persisted**: owning each byte of `text` at its value
gives the run's read-only text. -/
theorem textOwn_of_sepL (f : Nat → BitVec 8) :
    ∀ text : List (Nat × BitVec 8), (∀ p ∈ text, f p.1 = p.2) →
      sepL (GF := GF) (text.map Prod.fst) (fun a => a ↦ₘ f a) ⊢ |==> textOwn text
  | [], _ => by
    iintro _
    imodintro
    unfold textOwn
    simp only [sepL_nil]
    iempintro
  | p :: ps, h => by
    simp only [List.map_cons, sepL_cons]
    iintro ⟨Hp, Hps⟩
    rw [h p List.mem_cons_self]
    ihave Hp := mem_persist p.1 p.2 $$ Hp
    ihave Hps := textOwn_of_sepL f ps (fun q hq => h q (List.mem_cons_of_mem _ hq)) $$ Hps
    imod Hp with #Hp
    imod Hps with #Hps
    imodintro
    unfold textOwn
    simp only [sepL_cons]
    isplitl []
    · iexact Hp
    · iexact Hps

/-- One code byte out of the run's read-only text. -/
theorem textOwn_mem {a : Nat} {b : BitVec 8} :
    ∀ text : List (Nat × BitVec 8), (a, b) ∈ text → textOwn (GF := GF) text ⊢ a ↦ₘ□ b
  | [], h => absurd h List.not_mem_nil
  | q :: qs, h => by
    unfold textOwn
    simp only [sepL_cons]
    iintro ⟨#Hq, #Hqs⟩
    rcases List.mem_cons.mp h with rfl | h
    · iexact Hq
    · iapply textOwn_mem qs h
      unfold textOwn
      iexact Hqs

/-- **An instruction's code out of the run's read-only text.** -/
theorem instrAt_of_textOwn {text : List (Nat × BitVec 8)} {i : Nat} {code : List (BitVec 8)}
    (h : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ text) : textOwn (GF := GF) text ⊢ instrAt i code := by
  rw [instrAt_eq]
  suffices hs : ∀ L : List (Nat × DFrac × BitVec 8), (∀ p ∈ L, p.2.1 = DFrac.discard ∧
      (p.1, p.2.2) ∈ text) → textOwn (GF := GF) text ⊢ sepL L (fun p => p.1 ↦ₘ{p.2.1} p.2.2) from
    hs _ fun p hp => ⟨by
      unfold codeFoot at hp
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
      rfl, h p hp⟩
  intro L
  induction L with
  | nil => intro _; iintro _; simp only [sepL_nil]; iempintro
  | cons p ps ih =>
    intro hL
    simp only [sepL_cons]
    iintro #H
    obtain ⟨e, hm⟩ := hL p List.mem_cons_self
    rw [e]
    isplitl []
    · iapply textOwn_mem text hm
      iexact H
    · iapply ih fun q hq => hL q (List.mem_cons_of_mem _ hq)
      iexact H

/-- The owned bytes `S`, enumerated by `l`. -/
theorem ownSet_of_sepL {S : Nat → Prop} {l : List Nat} (hl : l.Nodup ∧ ∀ a, a ∈ l ↔ S a)
    (Φ : Nat → IProp GF) : sepL l Φ ⊢ ownSet S Φ := by
  unfold ownSet
  iintro H
  iexists l
  iframe H
  ipureintro
  exact hl

end

end VsaIris
