import Dc.Mach.Halts

/-!
# The boot's hand-over, for both WPs (M11)

`start_spec` runs from `_start` (after `gp`) to one of three ends
(`BootEnd`): `main`'s call of `dc_evalstr` (`EvalCallAt`) or the exit with
status 1 after out of memory (`ExitW`). `bootEnd_run` is that run; `bootEnd_kont` turns one Iris
continuation per end (`RunRes`: the registers, owned bytes and console at
the end, beside the run's read-only resources) into the run's continuation.

* `dc_wp_boot`: the whole run's WP from adequacy's ownership, for any `Wp`.
* `dc_halts_wp` (total WP, `vsa_adequacy_exit`): a halt with `ψ`.
* `dc_stuck` (partial WP, `vsa_adequacyP`): divergence or a halt with `ψ`,
  the shape of `stuck_sim`.

Both are parametric over the run from `0x80001914` (`hev`); the status-1 exit is
closed by `exit1_kont` when `ψ (1, t)` holds.
-/

namespace Dc.Mach

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config)

/-- **At `main`'s call of `dc_evalstr`** after the boot from `M0`, the
values `rv`/`mv` matching the symbolic state. -/
structure EvalCallAt (S : Nat → Prop) (M0 : Mem) (s : List Nat) (rv : Nat → BitVec 64)
    (mv : Nat → BitVec 8) (M1 : Mem) (R1 R' : Nat → BitVec 64) (M' : Mem) (H' : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (b1 b2 : Blk) : Prop where
  fill : Filled M1 M0 freeListAddr bssLen (fun _ => 0#8)
  ra : R1 1 = 0x8000003c#64
  sp : R1 2 = BitVec.ofNat 64 stackTop
  st : BootEval S stackTop mainW M1 R1 R' M' H' F L C (msObj b1 b2 s) s
  mat : Matches dcRegs S 0x80001914#64 R' M' rv mv

/-- **Where the boot hands over** (console `t0` before `dc_evalstr`). -/
inductive BootEnd (S : Nat → Prop) (M0 : Mem) (s : List Nat) (t0 : String) :
    String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop
  | eval {rv mv M1 R1 R' M' H' F L C b1 b2} :
      EvalCallAt S M0 s rv mv M1 R1 R' M' H' F L C b1 b2 → BootEnd S M0 s t0 t0 rv mv
  | exit1 {t rv mv} : ExitW (fun _ => True) t rv 1#64 → BootEnd S M0 s t0 t rv mv

/-- **The boot's run** from `0x80000008` to its hand-over. -/
theorem bootEnd_run {live S : Nat → Prop} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem}
    {s : List Nat} (pre : StartPre S M0 s) (R : Nat → BitVec 64) (t : String) :
    DWO live S (BootEnd S M0 s t) t 0x80000008#64 R M0 :=
  start_spec hlive pre R
    (fun t' R' M' h15 h14 => swpo_done fun rv _ hm =>
      .exit1 { pc := hm.pc
               base := (hm.regs 14 (by decide) (by decide)).trans h14
               word := (hm.regs 15 (by decide) (by decide)).trans h15
               lt := by decide
               post := trivial })
    (fun M1 R1 R' M' H' F L C b1 b2 hf h1 h2 he => swpo_done fun _ _ hm =>
      .eval { fill := hf, ra := h1, sp := h2, st := he, mat := hm })

section Iris

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The owned resources at a hand-over: dc's registers, the bytes `S`, the console. -/
abbrev RunRes (S : Nat → Prop) (t : String) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) :
    IProp GF :=
  iprop(sepL dcRegs (fun r => r ↦ᵣ rv r) ∗ ownSet S (fun a => a ↦ₘ mv a) ∗ consoleOwn t)

/-- **The boot's continuation** from one continuation per hand-over. -/
theorem bootEnd_kont {M : MachineModel} (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF}
    {S : Nat → Prop} {M0 : Mem} {s : List Nat} {t0 : String}
    (hev : ∀ rv mv M1 R1 R' M' H' F L C b1 b2, EvalCallAt S M0 s rv mv M1 R1 R' M' H' F L C b1 b2 →
      roOwn (GF := GF) roR dcText ∗ RunRes S t0 rv mv ⊢ Wp.W Φ)
    (hex : ∀ t rv mv, ExitW (fun _ => True) t rv 1#64 →
      roOwn (GF := GF) roR dcText ∗ RunRes S t rv mv ⊢ Wp.W Φ) :
    roOwn (GF := GF) roR dcText ⊢ runKontO Wp Φ dcRegs S (BootEnd S M0 s t0) := by
  iintro #Hro %t %rv %mv %hq Hr HS Hc
  rcases hq with ⟨h⟩ | ⟨h⟩
  · iapply hev _ _ _ _ _ _ _ _ _ _ _ _ h
    isplitl []
    · iexact Hro
    isplitl [Hr]
    · iexact Hr
    isplitl [HS]
    · iexact HS
    iexact Hc
  · iapply hex _ _ _ h
    isplitl []
    · iexact Hro
    isplitl [Hr]
    · iexact Hr
    isplitl [HS]
    · iexact HS
    iexact Hc

/-- **The status-1 exit**, for a postcondition admitting it. -/
theorem exit1_kont {live S : Nat → Prop} (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ dcText, live p.1) {ψ : Nat × String → Prop} (hψ : ∀ t, ψ (1, t))
    {t : String} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : ExitW (fun _ => True) t rv 1#64) :
    roOwn (GF := GF) roR dcText ∗ RunRes S t rv mv ⊢ Wp.W (fun v => iprop(⌜ψ v⌝)) := by
  iintro ⟨#Hro, Hr, HS, Hc⟩
  ihave #Htx := roOwn_text roR dcText $$ Hro
  iapply exitKont (S := S) Wp hlive ψ $$ Htx %t %rv %mv
    %⟨1#64, { h with post := hψ t }⟩ Hr HS Hc

end Iris

/-- **The whole run's WP from adequacy's ownership**, for any `Wp`, from one
continuation per hand-over of the boot. -/
theorem dc_wp_boot {live S : Nat → Prop} {c : Config} {l s : List Nat} [G : MachGS .hasLC MachGF]
    (Wp : MachWP (GF := MachGF) (vsaModel live)) {Φ : Nat × String → IProp MachGF}
    (hlive : ∀ p ∈ dcText, live p.1)
    (hpc : (vsaModel live).reg c VsaIris.PC = 0x80000000#64)
    (htext : ∀ p ∈ dcText, (vsaModel live).mem c p.1 = p.2)
    (hl : l.Nodup ∧ ∀ a, a ∈ l ↔ S a) (hsep : ∀ a ∈ l, ∀ p ∈ dcText, p.1 ≠ a)
    (pre : StartPre S c.σ.mem s)
    (hev : ∀ rv mv M1 R1 R' M' H' F L C b1 b2,
      EvalCallAt S c.σ.mem s rv mv M1 R1 R' M' H' F L C b1 b2 →
      roOwn (GF := MachGF) roR dcText ∗ RunRes S (Vsa.Machine.output c.σ) rv mv ⊢ Wp.W Φ)
    (hex : ∀ t rv mv, ExitW (fun _ => True) t rv 1#64 →
      roOwn (GF := MachGF) roR dcText ∗ RunRes S t rv mv ⊢ Wp.W Φ) :
    ⊢ ([∗map] k ↦ v ∈ bmap ((vsaModel live).reg c) bootRegs, k ↦ᵣ v) -∗
      ([∗map] k ↦ v ∈ bmap ((vsaModel live).mem c) (dcText.map Prod.fst ++ l), k ↦ₘ v) -∗
      consoleOwn (Vsa.Machine.output c.σ) -∗ Wp.W Φ := by
  have hnd : (dcText.map Prod.fst ++ l).Nodup :=
    List.nodup_append.mpr ⟨dcText_nodup, hl.1, fun a ha b hb e => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact hsep b hb p hp e⟩
  exact dc_boot_wpG Wp hlive hpc htext hl hnd rfl
    (bootEnd_run hlive pre (upd ((vsaModel live).reg c) 3 gpV) _) (bootEnd_kont Wp hev hex)

/-- **dc halts (total WP).** The run's continuation at `dc_evalstr`'s call
gives a halt satisfying `ψ`. -/
theorem dc_halts_wp {live S : Nat → Prop} (c : Config) {l s : List Nat} (ψ : Nat × String → Prop)
    (hok : VsaOk live c) (hlive : ∀ p ∈ dcText, live p.1)
    (hpc : (vsaModel live).reg c VsaIris.PC = 0x80000000#64)
    (htext : ∀ p ∈ dcText, (vsaModel live).mem c p.1 = p.2)
    (hl : l.Nodup ∧ ∀ a, a ∈ l ↔ S a) (hsep : ∀ a ∈ l, ∀ p ∈ dcText, p.1 ≠ a)
    (pre : StartPre S c.σ.mem s) (hψ1 : ∀ t, ψ (1, t))
    (hev : ∀ [_G : MachGS .hasLC MachGF], ∀ rv mv M1 R1 R' M' H' F L C b1 b2,
      EvalCallAt S c.σ.mem s rv mv M1 R1 R' M' H' F L C b1 b2 →
      roOwn (GF := MachGF) roR dcText ∗ RunRes S (Vsa.Machine.output c.σ) rv mv ⊢
        (twpW (GF := MachGF) (vsaModel live)).W (fun v => iprop(⌜ψ v⌝))) :
    ∃ e out, Vsa.Machine.Halts c out e ∧ ψ (e, out) := by
  refine vsa_adequacy_exit (GF := MachGF) live c (bmap ((vsaModel live).reg c) bootRegs)
    (bmap ((vsaModel live).mem c) (dcText.map Prod.fst ++ l)) (bmap_agree _ _) (bmap_agree _ _)
    hok ψ ?_
  intro G
  exact dc_wp_boot (twpW (vsaModel live)) hlive hpc htext hl hsep pre hev
    (fun _ _ _ h => exit1_kont _ hlive hψ1 h)

/-- **dc diverges or halts (partial WP)**, `stuck_sim`'s shape: the run's
partial continuations give divergence or a halt satisfying `ψ`. -/
theorem dc_stuck {live S : Nat → Prop} (c : Config) {l s : List Nat} (ψ : Nat × String → Prop)
    (hok : VsaOk live c) (hlive : ∀ p ∈ dcText, live p.1)
    (hpc : (vsaModel live).reg c VsaIris.PC = 0x80000000#64)
    (htext : ∀ p ∈ dcText, (vsaModel live).mem c p.1 = p.2)
    (hl : l.Nodup ∧ ∀ a, a ∈ l ↔ S a) (hsep : ∀ a ∈ l, ∀ p ∈ dcText, p.1 ≠ a)
    (pre : StartPre S c.σ.mem s) (hψ1 : ∀ t, ψ (1, t))
    (hev : ∀ [_G : MachGS .hasLC MachGF], ∀ rv mv M1 R1 R' M' H' F L C b1 b2,
      EvalCallAt S c.σ.mem s rv mv M1 R1 R' M' H' F L C b1 b2 →
      roOwn (GF := MachGF) roR dcText ∗ RunRes S (Vsa.Machine.output c.σ) rv mv ⊢
        (wpW (GF := MachGF) (vsaModel live)).W (fun v => iprop(⌜ψ v⌝))) :
    Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ ψ (e, out) := by
  refine vsa_adequacyP (GF := MachGF) live c (bmap ((vsaModel live).reg c) bootRegs)
    (bmap ((vsaModel live).mem c) (dcText.map Prod.fst ++ l)) (bmap_agree _ _) (bmap_agree _ _)
    hok ψ ?_
  intro G
  exact dc_wp_boot (wpW (vsaModel live)) hlive hpc htext hl hsep pre hev
    (fun _ _ _ h => exit1_kont _ hlive hψ1 h)

end Dc.Mach
