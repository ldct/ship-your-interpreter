import Dc.Mach.Run
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.ExecuteLoad

/-!
# Observed loads from owned bytes

The reflected block model (`MKind`, `Vsa/Sim/BlockMem.lean`) has no signed
byte load, so dc's two `lb`s (`_bc_shift_addsub`) have no reflected segment.
They are observed ALU steps (`stepObs_alu`: one step, PC advanced by four, one
GPR written, memory, output and other registers unchanged) whose value
depends on one byte of OWNED memory:

* `aluStepT_of_obs`: `aluStep_of_obs` (`VsaIris/Vsa/SymObs.lean`) with the
  read bytes split into code bytes (read-only, `live`, so present) and data
  bytes read TOTALLY (`getD 0`, the model's own read; no presence demanded);
* `swp_aluM`: such an `AluStep` as one step of a symbolic run, the data bytes
  owned (`S`) at their image values `imgM Mt a` (`segFrom_of_runFact`'s owned
  read alternative);
* `exec_lb_tot`: `execute (LOAD … false 1)` at the skeleton state, total read
  (`vmem_read_data_one_total`, `execute_load_signed_char`).

The step table (`scripts/dc/gen_dc_steps.py`) emits `stL_<pc>` per `lb` over
these three.
-/

namespace Dc.Mach

open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step MState)
open VsaIris Vsa.Sim VsaIris.Inst VsaIris.MallocFast VsaIris.Sym Vsa.MemRepr

/-- **An observed ALU step whose data bytes are read totally, as an `AluStep`.**
`MC` are code bytes (`live`, hence present); `MD` are data bytes, handed to the
observation as total reads. -/
theorem aluStepT_of_obs {live : Nat → Prop} {i : Nat} {RR : List (Nat × DFrac × BitVec 64)}
    {MC MD : List (Nat × DFrac × BitVec 8)} {rd : Nat} {val : BitVec 64}
    (hrd1 : 1 ≤ rd) (hrd31 : rd ≤ 31) (hRRk : ∀ q ∈ RR, 1 ≤ q.1 ∧ q.1 ≤ 31)
    (hlive : ∀ p ∈ MC, live p.1)
    (hsite : ∀ c : Config, GoodState c.σ → c.tick < 2 →
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) →
      (∀ q ∈ RR, gprGet c.σ q.1 = some q.2.2) → (∀ q ∈ MC, c.σ.mem[q.1]? = some q.2.2) →
      (∀ q ∈ MD, (c.σ.mem[q.1]?).getD 0 = q.2.2) →
      ∃ (σ' : MState) (i' : Nat) (vm : BitVec 64),
        Step ⟨c.σ, c.tick, c.steps⟩ ⟨σ', i', c.steps + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
        σ'.mem = c.σ.mem ∧
        ReadsLikePost σ' (sigmaPost_alu c.σ (BitVec.ofNat 64 i) vm (gprReg rd) (gprRT rd val))) :
    AluStep live i RR (MC ++ MD) rd val := by
  intro c hok hpc hRR hMR
  have hpcσ : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) := by
    obtain ⟨w, hw⟩ := hok.good.PC
    have h : pcVal c.σ = BitVec.ofNat 64 i := hpc
    unfold pcVal at h
    rw [hw] at h ⊢
    exact congrArg some h
  have hRRσ : ∀ q ∈ RR, gprGet c.σ q.1 = some q.2.2 := fun q hq =>
    gprGet_eq_of_vsaReg hok (hRRk q hq).1 (hRRk q hq).2 (hRR q hq)
  obtain ⟨σ', i', vm, hs, hi', hG', hmem, hobs⟩ :=
    hsite c hok.good hok.tick hpcσ hRRσ
      (code_present hok MC (fun q hq => hMR q (List.mem_append_left _ hq)) hlive)
      (fun q hq => hMR q (List.mem_append_right _ hq))
  have hrdn : ∀ rr ∈ noiseRegs, (gprReg rd == rr) = false :=
    gpr_avoids_noiseO' rd (by omega) hrd1
  have hother : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ ([rd] : List Nat), (gprReg m == R) = false) → σ'.regs.get? R = c.σ.regs.get? R := by
    intro R hn hw
    rw [hobs.1 R (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))]
    exact get?_sigmaPost_alu _ _ _ _ _ R (hn _ (by decide)) (hn _ (by decide))
      (hw rd (by simp)) (hn _ (by decide)) (hn _ (by decide))
  have hgpr : ∀ n, 1 ≤ n → n ≤ 31 → n ≠ rd → gprGet σ' n = gprGet c.σ n := fun n h1 h31 hne =>
    gprGet_of_frame n h1 h31 (gpr_avoids_noiseO n (by omega) h1)
      (fun m hm => by
        simp only [List.mem_singleton] at hm; subst hm
        exact gprReg_beq_false m (by omega) n (by omega) hrd1 h1 (Ne.symm hne))
      hother
  have hrdg : gprGet σ' rd = some val := gprGet_obs_rd rd hrd1 hrd31 hobs
  refine ⟨⟨σ', i', c.steps + 1⟩, hs, ⟨hG', hi', fun n h1 h31 => ?_, fun a ha => ?_, ?_⟩,
    ?_, ?_, fun k hk1 hk2 => ?_, fun a => ?_, ?_⟩
  · by_cases hn : n = rd
    · subst hn; rw [hrdg]; rfl
    · rw [hgpr n h1 h31 hn]; exact hok.gpr n h1 h31
  · change (σ'.mem[a]?).isSome; rw [hmem]; exact hok.live a ha
  · rw [hother _ (by decide) (fun m hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact gpr_htif _ (by omega) (by omega))]
    exact hok.htifIdle
  · change pcVal σ' = _
    unfold pcVal; rw [obs_alu_pc hobs, VsaIris.Inst.addInt_ofNat_four]; rfl
  · change vsaReg _ rd = val
    rw [vsaReg_gpr (by unfold VsaIris.PC; omega)]
    change (gprGet σ' rd).getD 0 = val
    rw [hrdg]; rfl
  · change vsaReg _ k = vsaReg c k
    rw [vsaReg_gpr hk1, vsaReg_gpr (c := c) hk1]
    by_cases hr : 1 ≤ k ∧ k ≤ 31
    · change (gprGet σ' k).getD 0 = _
      rw [hgpr k hr.1 hr.2 hk2]
    · change (gprGet σ' k).getD 0 = _
      rw [gprGet_none (by unfold VsaIris.PC at hk1; omega),
        gprGet_none (by unfold VsaIris.PC at hk1; omega)]
  · change (σ'.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0
    rw [hmem]
  · show Vsa.Machine.output σ' = Vsa.Machine.output c.σ
    unfold Vsa.Machine.output; rw [hobs.2]

/-- **An observed ALU step reading owned bytes, in a symbolic run** (`swp_alu`
with data bytes `MD`, owned at their image values). -/
theorem swp_aluM {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (i : Nat) (code : List (BitVec 8)) (MD : List (Nat × DFrac × BitVec 8)) (rd : Nat)
    (ks : List Nat) (val : BitVec 64)
    (hstep : AluStep live i (ks.map fun k => (k, DFrac.own 1, R k)) (codeFoot i code ++ MD) rd val)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ text)
    (hMD : ∀ p ∈ MD, S p.1 ∧ imgM Mt p.1 = p.2.2)
    (hPC : VsaIris.PC ∈ rs) (hrd : rd ∈ rs)
    (hks : ∀ k ∈ ks, k ∈ rs ∧ k ≠ VsaIris.PC) (hpc : pc = BitVec.ofNat 64 i)
    (hk : SWP live text rs S Q (BitVec.ofNat 64 (i + 4)) (upd R rd val) Mt) :
    SWP live text rs S Q pc R Mt := by
  subst hpc
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨0, segFrom_of_runFact (MW := [])
    (runFact_of_aluStep (old := rv rd) hstep) (fun p hp => ?_) (fun p hp => ?_) ?_
    (fun p hp => by cases hp) ?_⟩⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact .inr ⟨(hks k hk).1, hm.regs _ (hks k hk).1 (hks k hk).2⟩
  · rcases List.mem_append.mp hp with h | h
    · exact .inl (hcode p h)
    · exact .inr ⟨(hMD p h).1, by rw [hm.img _ (hMD p h).1, (hMD p h).2]⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inl ⟨hPC, hm.pc⟩
    · exact .inl ⟨hrd, rfl⟩
  · intro rv' mv' h1 h2 _ h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · by_cases hr1 : r = rd
      · subst hr1
        rw [upd_same]
        exact h1 (r, rv r, val) (by simp)
      · rw [upd_other _ _ hr1]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact fun e => hne e.symm
        · exact fun e => hr1 e.symm
    · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]

/-- **Signed byte load `lb rd, off(rs1)`**, total read: writes the sign
extension of the byte at `vbase + sext off` (`getD 0`). -/
theorem exec_lb_tot (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (b : BitVec 8)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64) (b : BitVec (8 * 1)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hea : LdOK (vbase + sign_extend (m := 64) off).toNat 1)
    (hb : (σ.mem[(vbase + sign_extend (m := 64) off).toNat]?).getD 0 = b) :
    (execute (instruction.LOAD (off, rs1, rd, false, 1))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hread := vmem_read_data_one_total (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase initMstatus initPmpaddr
    hpriv hmstatus (by decide) hseccfg hpma hcfg haddr hbase' hrs1 hea.1 hea.2.1 hea.2.2
  have hv : ldByteT (afterNextPC (afterPrelude σ) pc) (vbase + sign_extend (m := 64) off) = b := hb
  rw [hv] at hread
  exact execute_load_signed_char off rs1 rd 1 (b : BitVec (8 * 1))
    (afterNextPC (afterPrelude σ) pc) σ' (by decide) hread hwr

end Dc.Mach
