import Dc.Mach.BootStart
import VsaIris.Vsa.SymRunRO

/-!
# `_start`'s `gp` pair (M11)

```
80000000 auipc gp,0x1b ; 80000004 addi gp,gp,1296      (gp = __global_pointer$)
```

`DW` holds `gp` read-only at `gpV`; these two instructions write it, so they
run before `DW` holds, owning `gp`: a run over the read-only list `[]` and the
registers `gp :: dcRegs` (`SWPR`, `SymRunRO.lean`). `gp_pair` is one reflected
segment (`dx_80000000`, with the code bytes `dc_at_80000000`/`dc_at_80000004`
the step table leaves out) to `0x80000008` with `gp = gpV`.
-/

namespace Dc.Mach

open VsaIris Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Inst VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The registers the boot owns: `gp` and dc's. -/
abbrev bootRegs : List Nat := 3 :: dcRegs

/-- The `gp` pair as one block. -/
def dx_80000000 : List BBlock :=
  [{ body := [mkLine 0x80000000#64 0x0001b197#32, mkLine 0x80000004#64 0x51018193#32], term := none }]

/-- The code bytes of `0x80000000`. -/
theorem dc_at_80000000 {m : Mem} (h : TextLoaded dcText m) :
    m[(0x80000000 : Nat)]? = some (0x97 : BitVec 8) ∧
    m[(0x80000001 : Nat)]? = some (0xb1 : BitVec 8) ∧
    m[(0x80000002 : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x80000003 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h _ (List.mem_append_left dcRO (List.mem_append_left dcCodeNode974_1949 (List.mem_append_left dcCodeNode487_974 (List.mem_append_left dcCodeNode243_487 (List.mem_append_left dcCodeNode121_243 (List.mem_append_left dcCodeNode60_121 (List.mem_append_left dcCodeNode30_60 (List.mem_append_left dcCodeNode15_30 (List.mem_append_left dcCodeNode7_15 (List.mem_append_left dcCodeNode3_7 (List.mem_append_left dcCodeNode1_3 ((by decide : ((0x80000000 : Nat), (0x97#8 : BitVec 8)) ∈ dcCodeChunk0))))))))))))),
   h _ (List.mem_append_left dcRO (List.mem_append_left dcCodeNode974_1949 (List.mem_append_left dcCodeNode487_974 (List.mem_append_left dcCodeNode243_487 (List.mem_append_left dcCodeNode121_243 (List.mem_append_left dcCodeNode60_121 (List.mem_append_left dcCodeNode30_60 (List.mem_append_left dcCodeNode15_30 (List.mem_append_left dcCodeNode7_15 (List.mem_append_left dcCodeNode3_7 (List.mem_append_left dcCodeNode1_3 ((by decide : ((0x80000001 : Nat), (0xb1#8 : BitVec 8)) ∈ dcCodeChunk0))))))))))))),
   h _ (List.mem_append_left dcRO (List.mem_append_left dcCodeNode974_1949 (List.mem_append_left dcCodeNode487_974 (List.mem_append_left dcCodeNode243_487 (List.mem_append_left dcCodeNode121_243 (List.mem_append_left dcCodeNode60_121 (List.mem_append_left dcCodeNode30_60 (List.mem_append_left dcCodeNode15_30 (List.mem_append_left dcCodeNode7_15 (List.mem_append_left dcCodeNode3_7 (List.mem_append_left dcCodeNode1_3 ((by decide : ((0x80000002 : Nat), (0x01#8 : BitVec 8)) ∈ dcCodeChunk0))))))))))))),
   h _ (List.mem_append_left dcRO (List.mem_append_left dcCodeNode974_1949 (List.mem_append_left dcCodeNode487_974 (List.mem_append_left dcCodeNode243_487 (List.mem_append_left dcCodeNode121_243 (List.mem_append_left dcCodeNode60_121 (List.mem_append_left dcCodeNode30_60 (List.mem_append_left dcCodeNode15_30 (List.mem_append_left dcCodeNode7_15 (List.mem_append_left dcCodeNode3_7 (List.mem_append_left dcCodeNode1_3 ((by decide : ((0x80000003 : Nat), (0x00#8 : BitVec 8)) ∈ dcCodeChunk0)))))))))))))⟩

/-- The code bytes of `0x80000004`. -/
theorem dc_at_80000004 {m : Mem} (h : TextLoaded dcText m) :
    m[(0x80000004 : Nat)]? = some (0x93 : BitVec 8) ∧
    m[(0x80000005 : Nat)]? = some (0x81 : BitVec 8) ∧
    m[(0x80000006 : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x80000007 : Nat)]? = some (0x51 : BitVec 8) :=
  ⟨h _ (List.mem_append_left dcRO (List.mem_append_left dcCodeNode974_1949 (List.mem_append_left dcCodeNode487_974 (List.mem_append_left dcCodeNode243_487 (List.mem_append_left dcCodeNode121_243 (List.mem_append_left dcCodeNode60_121 (List.mem_append_left dcCodeNode30_60 (List.mem_append_left dcCodeNode15_30 (List.mem_append_left dcCodeNode7_15 (List.mem_append_left dcCodeNode3_7 (List.mem_append_left dcCodeNode1_3 ((by decide : ((0x80000004 : Nat), (0x93#8 : BitVec 8)) ∈ dcCodeChunk0))))))))))))),
   h _ (List.mem_append_left dcRO (List.mem_append_left dcCodeNode974_1949 (List.mem_append_left dcCodeNode487_974 (List.mem_append_left dcCodeNode243_487 (List.mem_append_left dcCodeNode121_243 (List.mem_append_left dcCodeNode60_121 (List.mem_append_left dcCodeNode30_60 (List.mem_append_left dcCodeNode15_30 (List.mem_append_left dcCodeNode7_15 (List.mem_append_left dcCodeNode3_7 (List.mem_append_left dcCodeNode1_3 ((by decide : ((0x80000005 : Nat), (0x81#8 : BitVec 8)) ∈ dcCodeChunk0))))))))))))),
   h _ (List.mem_append_left dcRO (List.mem_append_left dcCodeNode974_1949 (List.mem_append_left dcCodeNode487_974 (List.mem_append_left dcCodeNode243_487 (List.mem_append_left dcCodeNode121_243 (List.mem_append_left dcCodeNode60_121 (List.mem_append_left dcCodeNode30_60 (List.mem_append_left dcCodeNode15_30 (List.mem_append_left dcCodeNode7_15 (List.mem_append_left dcCodeNode3_7 (List.mem_append_left dcCodeNode1_3 ((by decide : ((0x80000006 : Nat), (0x01#8 : BitVec 8)) ∈ dcCodeChunk0))))))))))))),
   h _ (List.mem_append_left dcRO (List.mem_append_left dcCodeNode974_1949 (List.mem_append_left dcCodeNode487_974 (List.mem_append_left dcCodeNode243_487 (List.mem_append_left dcCodeNode121_243 (List.mem_append_left dcCodeNode60_121 (List.mem_append_left dcCodeNode30_60 (List.mem_append_left dcCodeNode15_30 (List.mem_append_left dcCodeNode7_15 (List.mem_append_left dcCodeNode3_7 (List.mem_append_left dcCodeNode1_3 ((by decide : ((0x80000007 : Nat), (0x51#8 : BitVec 8)) ∈ dcCodeChunk0)))))))))))))⟩

/-- **`_start`'s `gp` pair** from `0x80000000`, owning `gp`: `gp = gpV` at
`0x80000008`, every other register and every byte unchanged. -/
theorem gp_pair {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {R : Nat → BitVec 64} {Mt : Mem}
    (hk : SWPR live [] dcText bootRegs S Q 0x80000008#64 (upd R 3 gpV) Mt) :
    SWPR live [] dcText bootRegs S Q 0x80000000#64 R Mt := by
  refine swpr_segL dx_80000000 [(3, R 3)] [] [] [] 1 rfl
    (by rw [show keysG [(3, R 3)] = [3] from rfl]; decide) (by rw [show keysG [(3, R 3)] = [3] from rfl]; decide)
    (by rw [show keysG [(3, R 3)] = [3] from rfl]; decide)
    (fun a _ => trivial) hlive
    (fun m hm _ => by unfold dx_80000000 ChainFacts; chain_facts hm with "Dc.Mach.dc_at_")
    (by decide) (fun p hp => ?_) (fun a h => by cases h) (fun a h => by cases h) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact .inl ⟨show (3 : Nat) ∈ bootRegs by decide, show (3 : Nat) ≠ PC by decide, rfl⟩
  · refine swpr_congr rfl (fun r hr hne => ?_) (fun a _ => rfl) hk
    rw [show keysG [(3, R 3)] = [3] from rfl]
    by_cases h3 : r = 3
    · subst h3; simp only [upd_same, List.mem_singleton, ↓reduceIte]; rfl
    · simp only [upd_other _ _ h3, List.mem_singleton, h3, ↓reduceIte]

section Iris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- A register points-to discarded to a read-only one. -/
theorem reg_persistD (r : Nat) (v : BitVec 64) : (r ↦ᵣ v) ⊢@{IProp GF} |==> r ↦ᵣ□ v := by
  unfold regPointsTo
  iintro H
  iapply ghost_map_elem_persist $$ H

/-- A basic update before the rest of the run. -/
theorem wp_of_bupdD {M : MachineModel} (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} :
    (|==> Wp.W Φ) ⊢ Wp.W Φ :=
  BIUpdateFUpdate.fupd_of_bupd.trans Wp.fupd

/-- **The boot run from `_start`.** Owning `gp` and dc's registers at `rv`
(`PC = 0x80000000`), the bytes `S` at `mv` (`Mt`'s image), the code and the
console at `t`: the `gp` pair runs (`gp_pair`), `gp` becomes read-only at
`gpV` (`reg_persistD`), and the printing run `DWO` from `0x80000008` (with
`gp` set in `rv`) continues to `Q` (`wp_lroW`). -/
theorem wp_gpBoot (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} {Mt : Mem}
    (hpc : rv VsaIris.PC = 0x80000000#64) (hmt : ∀ a, S a → mv a = imgM Mt a)
    (hk : DWO live S Q t 0x80000008#64 (upd rv 3 gpV) Mt) :
    textOwn (GF := GF) dcText ∗ sepL bootRegs (fun r => r ↦ᵣ rv r) ∗
      ownSet S (fun a => a ↦ₘ mv a) ∗ consoleOwn t ∗ runKontO Wp Φ dcRegs S Q ⊢ Wp.W Φ := by
  have hs : SWPR live [] dcText bootRegs S
      (fun rv' mv' => rv' 3 = gpV ∧ Matches dcRegs S 0x80000008#64 (upd rv 3 gpV) Mt rv' mv')
      0x80000000#64 rv Mt :=
    gp_pair hlive (swpr_done fun rv' mv' hm =>
      ⟨(hm.regs 3 (by decide) (by decide)).trans (upd_same _ _ _),
        ⟨hm.pc, fun r hr hne => hm.regs r (List.mem_cons_of_mem _ hr) hne, hm.img⟩⟩)
  obtain ⟨n, hrun⟩ := swpr_run hs ⟨hpc, fun _ _ _ => rfl, hmt⟩
  iintro ⟨#Htx, Hr, HS, Hc, Hk⟩
  iapply wp_localRunW Wp n rv mv hrun
  unfold roOwn
  simp only [sepL_nil]
  isplitl []
  · isplitl []
    · iempintro
    · unfold textOwn; iexact Htx
  isplitl [Hr]
  · iexact Hr
  isplitl [HS]
  · iexact HS
  iintro %rv' %mv' %hq Hr' HS'
  obtain ⟨hgp, hm⟩ := hq
  simp only [bootRegs, sepL_cons]
  icases Hr' with ⟨Hgp, Hr'⟩
  iapply wp_of_bupdD Wp
  ihave Hgp := reg_persistD 3 (rv' 3) $$ Hgp
  imod Hgp with #Hgp
  imodintro
  iapply wp_lroW Wp (swpo_run hk hm)
  unfold roOwn
  simp only [roR, sepL_cons, sepL_nil]
  rw [show gp = 3 from rfl, ← hgp]
  isplitl []
  · isplitl []
    · isplitl []
      · iexact Hgp
      · iempintro
    · unfold textOwn; iexact Htx
  iframe Hr' HS' Hc Hk

end Iris

end Dc.Mach
