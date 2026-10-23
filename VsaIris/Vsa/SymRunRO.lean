import VsaIris.Vsa.SymRun

/-!
# Symbolic runs over any read-only register list

`SWP` (`SymRun.lean`) fixes the read-only registers to `roR` (`gp` at
`gpV`). A run before `gp` is set (a boot's first instructions) owns `gp`:
`SWPR live ro …` is `SWP` with the read-only list `ro` a parameter, and
`swpr_segL` is `swp_segL` over it. `swpr_run` reads it back as a `LocalRun`
from matching values; `SWPR … roR` is `SWP` (`swpr_roR`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config)
open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section SWPR

variable (live : Nat → Prop) (ro : List (Nat × BitVec 64)) (text : List (Nat × BitVec 8))
  (rs : List Nat) (S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)

/-- **The weakest precondition at a symbolic state, read-only list `ro`.** -/
def SWPR (pc : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) : Prop :=
  ∃ n, ∀ rv mv, Matches rs S pc R Mt rv mv →
    LocalRun (vsaModel live) ro text rs S Q n rv mv

variable {live ro text rs S Q}

/-- `SWP` is `SWPR` at `roR`. -/
theorem swpr_roR {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} :
    SWPR live roR text rs S Q pc R Mt ↔ SWP live text rs S Q pc R Mt := Iff.rfl

/-- The run is done. -/
theorem swpr_done {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : ∀ rv mv, Matches rs S pc R Mt rv mv → Q rv mv) : SWPR live ro text rs S Q pc R Mt :=
  ⟨0, h⟩

/-- **Reading the run back** from matching values. -/
theorem swpr_run {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : SWPR live ro text rs S Q pc R Mt) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (hm : Matches rs S pc R Mt rv mv) : ∃ n, LocalRun (vsaModel live) ro text rs S Q n rv mv := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn rv mv hm⟩

/-- Only the PC, the owned registers other than `PC` and the owned bytes
matter. -/
theorem swpr_congr {pc pc' : BitVec 64} {R R' : Nat → BitVec 64} {Mt Mt' : Mem} (hpc : pc' = pc)
    (hR : ∀ r ∈ rs, r ≠ VsaIris.PC → R' r = R r) (hM : ∀ a, S a → imgM Mt' a = imgM Mt a)
    (h : SWPR live ro text rs S Q pc' R' Mt') : SWPR live ro text rs S Q pc R Mt := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun rv mv hm => hn rv mv ⟨hm.pc.trans hpc.symm,
    fun r hr hne => (hm.regs r hr hne).trans (hR r hr hne).symm,
    fun a ha => (hm.img a ha).trans (hM a ha).symm⟩⟩

/-- **One reflected segment over an arbitrary pin list `L`**, read-only list
`ro` (`swp_segL` at any `ro`): a pinned register is owned or read-only with
the segment leaving its value. -/
theorem swpr_segL {pc0 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (LD W : List Nat) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 (keysG L) bs)
    (hkeys : KeysOK (keysG L)) (hwr : ∀ x ∈ wrChain bs, x ∈ keysG L)
    (hcover : ∀ a, a ∉ W → OutL (segOut bs L lds).log a)
    (hlive : ∀ p ∈ text, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded text m → (∀ a ∈ LD, (m[a]?).getD 0 = imgM Mt a) →
      ChainFacts m m L lds bs)
    (hPC : VsaIris.PC ∈ rs)
    (hL : ∀ p ∈ L, (p.1 ∈ rs ∧ p.1 ≠ VsaIris.PC ∧ R p.1 = p.2) ∨
      ((p.1, p.2) ∈ ro ∧ finReg bs L lds p.1 = p.2))
    (hLD : ∀ a ∈ LD, S a) (hW : ∀ a ∈ W, S a)
    (hk : SWPR live ro text rs S Q (evalBlocksPC pc0 (SegEvalState.init L lds) bs)
      (fun r => if r ∈ keysG L then finReg bs L lds r else R r)
      (writeLog Mt (segOut bs L lds).log)) :
    SWPR live ro text rs S Q pc0 R Mt := by
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨k, segFrom_of_runFact
    (seg_runFact live bs L lds pc0 (textMRof text ++ LD.map fun a => (a, DFrac.own 1, imgM Mt a))
      (W.map fun a => (a, imgM Mt a)) k hlen hwf hkeys hwr ?_ ?_)
    (fun p hp => by cases hp) ?_ ?_ ?_ ?_⟩⟩
  · intro a ha
    exact hcover a fun hW' => ha _ (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hW') rfl
  · intro c hok hfoot
    obtain ⟨_, hMR, _, _⟩ := hfoot
    refine hfacts c.σ.mem (textLoaded_of_foot hok hlive hMR) fun a ha => ?_
    have := hMR (a, DFrac.own 1, imgM Mt a) (List.mem_append_right _
      (List.mem_map_of_mem (f := fun a => (a, DFrac.own 1, imgM Mt a)) ha))
    exact this
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact .inl hq
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact .inr ⟨hLD a ha, hm.img a (hLD a ha)⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inl ⟨hPC, hm.pc⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      rcases hL q hq with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, (hm.regs _ h1 h2).trans h3⟩
      · exact .inr ⟨h1, h2⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact ⟨hW a ha, hm.img a (hW a ha)⟩
  · intro rv' mv' h1 h2 h3 h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · by_cases hkL : r ∈ keysG L
      · rw [ite_eq_left_iff.2 (fun h => absurd hkL h)]
        obtain ⟨v, hv⟩ := (mem_keysG_iff r L).1 hkL
        exact h1 _ (List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun p => (p.1, p.2, finReg bs L lds p.1)) hv))
      · rw [ite_eq_right_iff.2 (fun h => absurd h hkL)]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
        rcases List.mem_cons.mp hp with rfl | hp
        · exact fun e => hne e.symm
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact fun e => hkL ((mem_keysG_iff r L).2 ⟨q.2, by rw [← e]; exact hq⟩)
    · by_cases hw : a ∈ W
      · have := h3 _ (List.mem_map_of_mem
          (f := fun p => (p.1, p.2, ((writeLog (wbase (W.map fun a => (a, imgM Mt a)))
            (segOut bs L lds).log)[p.1]?).getD 0))
          (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hw))
        refine this.trans (writeLog_getD_congr _ _ _ _ ?_)
        obtain ⟨o', ho', hg⟩ := wbase_get (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hw)
        show ((wbase (W.map fun a => (a, imgM Mt a)))[a]?).getD 0 = (Mt[a]?).getD 0
        rw [hg]
        obtain ⟨b, _, e⟩ := List.mem_map.mp ho'
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rfl
      · rw [h4 a ha fun p hp => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
          exact fun e => hw (e ▸ hc)]
        rw [hm.img a ha]
        unfold imgM
        rw [writeLog_out _ _ _ (hcover a hw)]

end SWPR

end VsaIris.Sym
