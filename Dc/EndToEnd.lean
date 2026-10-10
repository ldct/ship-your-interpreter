import Dc.Mach.BootEvalCall
import Dc.Refinement

/-!
# The end-to-end theorem (M12), from `evalstr`'s specification

`Dc.endToEnd_of_evalstr`: the statement of `Dc/PLAN.md` ("The final
theorem") for `dcBoot prog`, from

* `hev`: `EvalstrSpec` (`Dc/Mach/EvalBase.lean`, term direction),
* `hdiv`: `EvalstrDivSpec` (`BootEvalCall.lean`, the stuck direction),
* `hoom`: `evalstr`'s out-of-memory continuation at the boot's call
  (`EvOomBoot`), open until the out-of-memory stack pointers are aligned
  (`OomMemfail.lean`, `fnOomA_memfail`).

The program's admissibility is `DcAdmissible`: it fits `dc_script.text`
with its `NUL` and has none, nests at most `dcD` deep (the stack bound,
`StackBound.lean`), runs at most `dcK` leaking commands (`LeakBound`, the
reference and handle budget of `EvAt`), every `dc_func` call meets the
SizeBound (`CallP`), and the tail depth stays below `2^31` (`TailBound`,
`evalstr`'s 32-bit `tail_depth`).

The proof is `Dc.refinement` for the layout `dcLayout` (`dcBoot`,
`DcAdmissible`): `term_sim` by `dc_halts_loaded` with `evalstr`'s run
(`evcall_boot`, `EvEntryP.spec`) and its return (`evstr_ret`), `stuck_sim`
by `dc_stuck_loaded` with `EvalstrDivSpec` behind the same call.
-/

namespace Dc

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Dc.Mach Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open Vsa.Machine

/-- **The leak budget** of an admissible program: `EvAt.budget` with one
handle (`4 * k + 9 ≤ 2^20`). -/
abbrev dcK : Nat := 262141

/-- **The programs the binary is proved for.** -/
structure DcAdmissible (prog : List Nat) : Prop where
  len : prog.length < 8192
  nz : 0 ∉ prog
  byte : ∀ c ∈ prog, c < 256
  nest : NestBound 70 prog dcD
  leak : LeakBound 70 prog dcK
  size : ∀ n, AllCalls 70 (fun st _ _ => CallP st) n St.init ⟨prog, 1, false⟩
  tail : TailBound 70 prog

theorem DcAdmissible.dcProg {prog : List Nat} (h : DcAdmissible prog) : DcProg prog :=
  ⟨h.len, h.nz, h.byte⟩

theorem DcAdmissible.budget {prog : List Nat} (h : DcAdmissible prog) :
    EvBudget 70 dcD dcK St.init ⟨prog, 1, false⟩ :=
  ⟨h.nest, h.leak, h.size, h.tail, by have := h.len; simp only; omega⟩

/-- The binary's layout: boot configurations and admissible programs. -/
def dcLayout : DcLayout := ⟨dcBoot, DcAdmissible⟩

/-- **`evalstr`'s out-of-memory continuation at the boot's call** (open:
`OomAt`'s stack pointer is not known to be aligned). -/
def EvOomBoot (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) : Prop :=
  ∀ (M : Mem) (H : Heap) (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs : List GV)
    (st : St), DcAt dcOwn M H F L C G hs st → EvOom dcLive dcOwn Q evSp evW 0x87ffffe0 M

/-- **`term_sim`.** -/
theorem dc_term_sim (hev : ∀ Q, EvalstrSpec dcLive dcOwn Q)
    (hoom : ∀ ψ : Nat × String → Prop, (∀ t, ψ (1, t)) → EvOomBoot (fun t rv mv => ExitQ ψ t rv mv))
    (prog out : List Nat) (hp : DcAdmissible prog) (hrun : Runs 70 prog out) :
    Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1 := by
  obtain ⟨st, r, hl, hout⟩ := hrun
  have hld := dcBoot_loaded prog
  let ψ : Nat × String → Prop := fun v => (v.1 = 0 ∧ v.2 = outStr out) ∨ v.1 = 1
  have hψ1 : ∀ t, ψ (1, t) := fun _ => .inr rfl
  have hc : output (dcBoot prog).σ = "" := hld.out
  obtain ⟨e, o, hh, hψ⟩ := dc_halts_loaded (dcBoot prog) hld hp.dcProg ψ hψ1
    fun M1 R1 R' M' H F L C b1 b2 hf hr1 _ be => by
      refine evcall_boot hld (k := dcK) (by decide) hf hr1 be
        fun R2 M2 e1 en hra1 hra hpre => ?_
      have hspec := en.spec (hev _) (t0 := output (dcBoot prog).σ) hl hp.budget
        (hoom ψ hψ1 _ _ _ _ _ _ _ _ en.dc) fun R'' M'' H'' F'' L'' C'' G'' xs' p' _ e2 e10 post => ?_
      · simpa [outStr, St.init] using hspec
      rw [e1]
      have hpost : ∀ a, 0x87ffffd0 ≤ a → a < 0x88000000 → ¬ (0x87ffffe0 ≤ a ∧ a < 0x87fffff0) →
          imgM M'' a = imgM M2 a := fun a h1 h2 h3 =>
        post.out a (outHeap_of_ge (by simp [heapEnd]; omega))
          (fun hg => by have := hg.1.lt; simp [heapStart] at this; omega)
          (fun ho => by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr] at ho; omega)
          (fun hf => by simp only [frameIn, evSp, evW, heapEnd] at hf; omega) h3
          (fun hi => by simp only [InP, inPtrAddr] at hi; omega)
      have hpost0 : ψ (0, output (dcBoot prog).σ ++ outStr st.out) :=
        .inl ⟨rfl, by rw [hc, hout]; simp⟩
      refine evstr_ret post.dc post.slot ?_ ?_ R'' (by rw [e2, en.r2]) e10
        fun R3 M3 hpc h14 h15 => ⟨0#64, ⟨hpc, h14, h15, by decide, hpost0⟩⟩
      · rw [ldv_congr .ld fun j hj => hpost _ (by omega) (by simp only [widthOfM] at hj; omega)
          (by simp only [widthOfM] at hj; omega)]
        exact hra1
      · rw [ldv_congr .ld fun j hj => hpost _ (by omega) (by simp only [widthOfM] at hj; omega)
          (by simp only [widthOfM] at hj; omega)]
        exact hra
  rcases hψ with ⟨h0, h1⟩ | h1
  · subst h0; subst h1; exact .inl hh
  · subst h1; exact .inr ⟨o, hh⟩

/-- **`stuck_sim`.** -/
theorem dc_stuck_sim (hdiv : EvalstrDivSpec dcLive dcOwn) (prog : List Nat) (hp : DcAdmissible prog)
    (hno : ¬ ∃ out, Runs 70 prog out) :
    Diverges (dcBoot prog) ∨ ∃ out e, Halts (dcBoot prog) out e ∧ e ≠ 0 := by
  have hld := dcBoot_loaded prog
  refine dc_stuck_loaded (dcBoot prog) hld hp.dcProg (fun v => v.1 ≠ 0) (fun _ => Nat.one_ne_zero) ?_
  intro _G rv mv M1 R1 R' M' H F L C b1 b2 ea
  have hno' : ¬ ∃ st' r, Loop 70 St.init ⟨(msObj b1 b2 prog).s, 1, false⟩ st' r :=
    fun ⟨st', r, hl⟩ => hno ⟨st'.out, st', r, hl, rfl⟩
  have hpro : DWO dcLive dcOwn
      (fun t rv mv => t = output (dcBoot prog).σ ∧ ∃ R2 M2,
        EvEntryP dcOwn evSp evW dcD dcK 0x87ffffe0 M2 R2 H F L C (bootG [msObj b1 b2 prog])
          [.str b1.pay] [] St.init (msObj b1 b2 prog) ∧
        Matches dcRegs dcOwn 0x80001448#64 R2 M2 rv mv)
      (output (dcBoot prog).σ) 0x80001914#64 R' M' :=
    evcall_boot hld (by decide) ea.fill ea.ra ea.st fun R2 M2 _ en _ _ _ =>
      swpo_done fun rv2 mv2 hm => ⟨rfl, R2, M2, en, hm⟩
  iintro ⟨#Hro, Hr, HS, Hc⟩
  iapply wp_lroW (wpW (vsaModel dcLive)) (swpo_run hpro ea.mat)
  isplitl []
  · iexact Hro
  isplitl [Hr]
  · iexact Hr
  isplitl [HS]
  · iexact HS
  isplitl [Hc]
  · iexact Hc
  iintro %t' %rv' %mv' %hq Hr' HS' Hc'
  obtain ⟨rfl, R2, M2, en, hm⟩ := hq
  iapply hdiv (output (dcBoot prog).σ) evSp evW dcD dcK 0x87ffffe0 M2 R2 H F L C _ _ _ St.init
    (msObj b1 b2 prog) hno' hp.budget en rv' mv' hm
  isplitl []
  · iexact Hro
  isplitl [Hr']
  · iexact Hr'
  isplitl [HS']
  · iexact HS'
  iexact Hc'

/-- **THE END-TO-END THEOREM** (`Dc/PLAN.md`), from `evalstr`'s
specification in both directions and its out-of-memory continuation at the
boot's call: for every admissible program, a terminating run is a clean
halt of `dcBoot prog` with the same output or a heap-exhaustion exit; every
clean halt is a terminating run with that output; divergence means no run
terminates. -/
theorem endToEnd_of_evalstr (hev : ∀ Q, EvalstrSpec dcLive dcOwn Q)
    (hdiv : EvalstrDivSpec dcLive dcOwn)
    (hoom : ∀ ψ : Nat × String → Prop, (∀ t, ψ (1, t)) → EvOomBoot (fun t rv mv => ExitQ ψ t rv mv))
    (prog : List Nat) (hp : DcAdmissible prog) :
    (∀ out, Runs 70 prog out →
       Halts (dcBoot prog) (outStr out) 0 ∨ ∃ s, Halts (dcBoot prog) s 1) ∧
    (∀ s, Halts (dcBoot prog) s 0 → ∃ out, Runs 70 prog out ∧ s = outStr out) ∧
    (Diverges (dcBoot prog) → ¬ ∃ out, Runs 70 prog out) :=
  refinement (L := dcLayout) ⟨dc_term_sim hev hoom, dc_stuck_sim hdiv⟩ prog hp

end Dc
