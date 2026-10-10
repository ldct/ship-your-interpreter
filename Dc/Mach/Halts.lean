import Dc.Mach.BootGp
import VsaIris.Vsa.BootSplit

/-!
# `Halts` from a dc run (M11)

`dc_halts`: at a loaded configuration `c` (`PC = _start`, the code bytes
present, the owned bytes `S` enumerated by `l` and disjoint from the code,
`StartPre` on its memory), a printing run from `main`'s call of `dc_evalstr`
(0x80001914) to `_exit`'s `tohost` store with the exit word of `e` and the
console satisfying `φ` (`ExitQ φ`) makes the machine halt: `Halts c out e`
with `φ (e, out)`. The run before `dc_evalstr` is `start_spec` (the `gp`
pair through `wp_gpBoot`); `dc_makestring`'s out of memory is the caller's
`hoom` (`DcMemfail.lean`'s open supplier), `bc_init_numbers`' exits with
status 1, which `φ` admits (`hφ1`).

The ownership split follows the WHILE route (`VsaIris/Interp/EndToEnd.lean`):
adequacy's register and memory maps are read off `c` on `bootRegs` and on the
code addresses followed by `l` (`bmap`); the code bytes are persisted into
`textOwn dcText` (`textOwn_of_sepL`); at the end `wp_exitW` closes the run
from `_exit`'s store (`exitKont`), and `vsa_adequacy_exit` gives `Halts`.
-/

namespace Dc.Mach

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config)

/-! ## The code addresses are distinct -/

/-- A list strictly increasing, as a boolean check. -/
def incrB : List Nat → Bool
  | a :: b :: l => decide (a < b) && incrB (b :: l)
  | _ => true

theorem incrB_lt : ∀ (a : Nat) (l : List Nat), incrB (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, _, hx => absurd hx List.not_mem_nil
  | a, b :: l, h, x, hx => by
    simp only [incrB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (incrB_lt b l h.2 x hx)

theorem incrB_nodup : ∀ l : List Nat, incrB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | a :: b :: l, h => by
    have h' := h
    simp only [incrB, Bool.and_eq_true] at h'
    exact List.nodup_cons.mpr ⟨fun hm => Nat.lt_irrefl a (incrB_lt a (b :: l) h a hm),
      incrB_nodup (b :: l) h'.2⟩

/-- **The code and `.rodata` addresses are distinct** (one kernel check of
their order). -/
theorem dcText_nodup : (dcText.map Prod.fst).Nodup :=
  incrB_nodup _ (by decide +kernel)

/-! ## The end of a run -/

/-- **At `_exit`'s store** with the exit word of `e` (below `2^47`), the
console `t` satisfying `φ` at `(e, t)`. -/
structure ExitW (φ : Nat × String → Prop) (t : String) (rv : Nat → BitVec 64) (e : BitVec 64) :
    Prop where
  pc : rv VsaIris.PC = BitVec.ofNat 64 exitSite.pc
  base : rv exitSite.rs1 = exitSite.base
  word : rv exitSite.rs2 = exitWord e
  lt : e.toNat < 2 ^ 47
  post : φ (e.toNat, t)

/-- The end condition of a whole dc run: `_exit`'s store for some code. -/
def ExitQ (φ : Nat × String → Prop) (t : String) (rv : Nat → BitVec 64) (_ : Nat → BitVec 8) :
    Prop :=
  ∃ e, ExitW φ t rv e

/-- `dc_memfail`'s exit continuation when `φ` admits status 1. -/
theorem exitK_one {live S : Nat → Prop} {φ : Nat × String → Prop} (hφ1 : ∀ t, φ (1, t)) :
    ExitK live S (fun t rv mv => ExitQ φ t rv mv) 1#64 := fun t R' M' h15 h14 =>
  swpo_done fun rv _ hm =>
    ⟨1#64, { pc := hm.pc
             base := (hm.regs 14 (by decide) (by decide)).trans h14
             word := (hm.regs 15 (by decide) (by decide)).trans h15
             lt := by decide
             post := hφ1 t }⟩

section Iris

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `dcRegs` with `PC`, `a4`, `a5` first. -/
theorem dcRegs_perm : dcRegs.Perm ([32, 14, 15] ++
    [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
      30, 31]) := by decide

/-- **The run's end**: at `_exit`'s store the halting step reports the
console, so the continuation of a whole dc run holds. -/
theorem exitKont {live S : Nat → Prop} (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ dcText, live p.1) (φ : Nat × String → Prop) :
    textOwn (GF := GF) dcText ⊢
      runKontO Wp (fun v => iprop(⌜φ v⌝)) dcRegs S (fun t rv mv => ExitQ φ t rv mv) := by
  iintro #Htx %t' %rv' %mv' %hq Hr _ Hc
  obtain ⟨e, hw⟩ := hq
  ihave Hr := (sepL_perm _ dcRegs_perm).1 $$ Hr
  simp only [List.cons_append, List.nil_append, sepL_cons]
  icases Hr with ⟨Hpc, H14, H15, -⟩
  ihave #Hi := instrAt_of_textOwn (i := exitSite.pc) (code := exitSite.code)
    tohost_800005c8_code $$ Htx
  iapply wp_exitW Wp exitSite tohost_800005c8_cert e hw.lt (DFrac.own 1) (DFrac.own 1)
    (DFrac.own 1) t' (fun p hp => hlive _ (tohost_800005c8_code p hp))
  rw [← hw.pc, ← hw.base, ← hw.word, show VsaIris.PC = 32 from rfl, show exitSite.rs1 = 14 from rfl,
    show exitSite.rs2 = 15 from rfl]
  iframe Hi Hpc H14 H15 Hc
  ipureintro
  exact hw.post

end Iris

theorem bootRegs_nodup : bootRegs.Nodup := by decide

/-- **The whole run's WP from adequacy's ownership** (the key list `K` of the
memory map kept abstract: the code addresses followed by `l`). -/
theorem dc_boot_wp {live S : Nat → Prop} {c : Config} {l K : List Nat} [G : MachGS .hasLC MachGF]
    (hlive : ∀ p ∈ dcText, live p.1)
    (hpc : (vsaModel live).reg c VsaIris.PC = 0x80000000#64)
    (htext : ∀ p ∈ dcText, (vsaModel live).mem c p.1 = p.2)
    (hl : l.Nodup ∧ ∀ a, a ∈ l ↔ S a) (hnd : K.Nodup) (hK : K = dcText.map Prod.fst ++ l)
    {φ : Nat × String → Prop}
    (hrun : DWO live S (fun t rv mv => ExitQ φ t rv mv) (Vsa.Machine.output c.σ) 0x80000008#64
      (upd ((vsaModel live).reg c) 3 gpV) c.σ.mem) :
    ⊢ ([∗map] k ↦ v ∈ bmap ((vsaModel live).reg c) bootRegs, k ↦ᵣ v) -∗
      ([∗map] k ↦ v ∈ bmap ((vsaModel live).mem c) K, k ↦ₘ v) -∗
      consoleOwn (Vsa.Machine.output c.σ) -∗
      (twpW (GF := MachGF) (vsaModel live)).W (fun v => iprop(⌜φ v⌝)) := by
  have e : sepL (GF := MachGF) K (fun r => r ↦ₘ (vsaModel live).mem c r) ⊢
      sepL (dcText.map Prod.fst) (fun r => r ↦ₘ (vsaModel live).mem c r) ∗
        sepL l (fun r => r ↦ₘ (vsaModel live).mem c r) := by
    rw [hK]; exact (sepL_append _ _ _).1
  iintro Hr Hm Hc
  ihave Hr := sepL_of_bmap (fun k v => iprop(k ↦ᵣ v)) ((vsaModel live).reg c) bootRegs
    bootRegs_nodup $$ Hr
  ihave Hm := sepL_of_bmap (fun k v => iprop(k ↦ₘ v)) ((vsaModel live).mem c) K hnd $$ Hm
  ihave Hm := e $$ Hm
  icases Hm with ⟨Ht, Hl⟩
  ihave Ht := textOwn_of_sepL _ dcText htext $$ Ht
  ihave Hl := ownSet_of_sepL hl _ $$ Hl
  iapply wp_of_bupdD (twpW (vsaModel live))
  imod Ht with #Ht
  imodintro
  ihave Hk := exitKont (S := S) (twpW (vsaModel live)) hlive φ $$ Ht
  iapply wp_gpBoot (twpW (vsaModel live)) (mv := (vsaModel live).mem c) hlive hpc (fun _ _ => rfl) hrun
  isplitl []
  · iexact Ht
  isplitl [Hr]
  · iexact Hr
  isplitl [Hl]
  · iexact Hl
  isplitl [Hc]
  · iexact Hc
  iexact Hk

/-- **dc halts.** From a loaded configuration and a run from `main`'s call
of `dc_evalstr` to `_exit`'s store (`hk`), the machine halts with some code
and output satisfying `φ`. -/
theorem dc_halts {live S : Nat → Prop} (c : Config) {l s : List Nat} (φ : Nat × String → Prop)
    (hok : VsaOk live c) (hlive : ∀ p ∈ dcText, live p.1)
    (hpc : (vsaModel live).reg c VsaIris.PC = 0x80000000#64)
    (htext : ∀ p ∈ dcText, (vsaModel live).mem c p.1 = p.2)
    (hl : l.Nodup ∧ ∀ a, a ∈ l ↔ S a) (hsep : ∀ a ∈ l, ∀ p ∈ dcText, p.1 ≠ a)
    (pre : StartPre S c.σ.mem s) (hφ1 : ∀ t, φ (1, t))
    (hoom : ∀ M1 R' M' sp', Filled M1 c.σ.mem freeListAddr bssLen (fun _ => 0#8) →
      OomAt S stackTop mainW M1 (fun _ => False) sp' R' M' →
      DWO live S (fun t rv mv => ExitQ φ t rv mv) (Vsa.Machine.output c.σ) 0x80001e74#64 R' M')
    (hk : ∀ M1 R1 R' M' H' F L C b1 b2, Filled M1 c.σ.mem freeListAddr bssLen (fun _ => 0#8) →
      R1 1 = 0x8000003c#64 → R1 2 = BitVec.ofNat 64 stackTop →
      BootEval S stackTop mainW M1 R1 R' M' H' F L C (msObj b1 b2 s) s →
      DWO live S (fun t rv mv => ExitQ φ t rv mv) (Vsa.Machine.output c.σ) 0x80001914#64 R' M') :
    ∃ e out, Vsa.Machine.Halts c out e ∧ φ (e, out) := by
  have hnd : (dcText.map Prod.fst ++ l).Nodup :=
    List.nodup_append.mpr ⟨dcText_nodup, hl.1, fun a ha b hb e => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact hsep b hb p hp e⟩
  have hrun := start_spec hlive pre (upd ((vsaModel live).reg c) 3 gpV) (exitK_one hφ1) hoom hk
  refine vsa_adequacy_exit (GF := MachGF) live c (bmap ((vsaModel live).reg c) bootRegs)
    (bmap ((vsaModel live).mem c) (dcText.map Prod.fst ++ l)) (bmap_agree _ _) (bmap_agree _ _)
    hok φ ?_
  intro G
  exact dc_boot_wp hlive hpc htext hl hnd rfl hrun

end Dc.Mach
