import Dc.Mach.EvalDivRun
import Dc.Mach.BootEvalCall
import Dc.Mach.EvalEntryB
import Dc.Mach.DcFuncSpec

/-!
# `EvalstrDivSpec` from the segments (M10, stuck direction)

`div_supply`: the positions of a diverging evaluation (`DivAt`) with their
segments form a `DivSupply`; `div_lob` turns it into the partial WP with a
nonzero exit code at every position. `evalstrDiv_of`: `EvalstrDivSpec` from
the entry position. The `DC_EVALTOS` segment is a hypothesis (`DivTosStep`)
until its continuation-generic core lands.
-/

namespace Dc.Mach

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **The `DC_EVALTOS` segment**: from the `DC_EVALTOS` code of a diverging
evaluation to a further position, or an error exit. -/
def DivTosStep : Prop :=
  ∀ t rv mv, DivAt .tos t rv mv →
    ∃ Qp : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop,
      LRO (vsaModel dcLive) roR dcText dcRegs dcOwn Qp t rv mv ∧ ¬ Qp t rv mv ∧
      ∀ t' rv' mv', Qp t' rv' mv' →
        (∃ p', DivAt p' t' rv' mv') ∨ ∃ e, ExitW (fun v => v.1 ≠ 0) t' rv' e

/-- **The positions with their segments.** -/
theorem div_supply (hent : ∀ Q, EvEntryCore dcLive dcOwn Q) (hfn : ∀ Q, FnSpecH dcLive dcOwn Q)
    (hint : ∀ Q, EvIntCore dcLive dcOwn Q) (hstr : ∀ Q, EvStrCore dcLive dcOwn Q)
    (htos : DivTosStep) : DivSupply dcLive dcOwn DivPos DivAt where
  step p t rv mv h := match p, h with
    | .entry, h => seg_entry hent h
    | .head, h => seg_head hfn h
    | .ret, h => seg_ret hint hstr h
    | .tos, h => htos t rv mv h

/-- **`EvalstrDivSpec`** from the segments. -/
theorem evalstrDiv_of (hent : ∀ Q, EvEntryCore dcLive dcOwn Q) (hfn : ∀ Q, FnSpecH dcLive dcOwn Q)
    (hint : ∀ Q, EvIntCore dcLive dcOwn Q) (hstr : ∀ Q, EvStrCore dcLive dcOwn Q)
    (htos : DivTosStep) : EvalstrDivSpec dcLive dcOwn := by
  intro _G t0 sp W d k q M R H F L C G hs xs st o hno hb e rv mv hm
  have hat : DivAt .entry (t0 ++ Dc.outStr st.out) rv mv :=
    ⟨t0, sp, W, d, k, q, M, R, H, F, L, C, G, hs, xs, st, o,
      ⟨{ len := hb.frameLen, sb := e.sb, srt := e.srt, dc := e.dc, strIn := e.strIn,
          held := e.held, slot := e.slot, slotPlace := e.slotPlace, r2 := e.r2, r10 := e.r10,
          al := e.al, frame := e.frame, room := e.room, stk := e.stk, stkPr := e.stkPr,
          stkDn := e.stkDn, budget := e.budget, mb := e.mb, err := e.err, globs := e.globs },
        ⟨hb.nest, hb.leak, hb.size, hb.tail, runDiv_of_not hno⟩, rfl, hm⟩⟩
  have H := div_lob (GF := MachGF) dcText_live (div_supply hent hfn hint hstr htos)
  iintro ⟨#Hro, Hr⟩
  ihave Hw := H $$ %DivPos.entry %(t0 ++ Dc.outStr st.out) %rv %mv %hat Hro Hr
  iexact Hw

/-- **`EvalstrDivSpec`** with the entry (`ev_entry_k`) and `dc_func`'s
contract (`dc_func_spec`) discharged. -/
theorem evalstrDiv (hint : ∀ Q, EvIntCore dcLive dcOwn Q) (hstr : ∀ Q, EvStrCore dcLive dcOwn Q)
    (htos : DivTosStep) : EvalstrDivSpec dcLive dcOwn :=
  evalstrDiv_of (fun _ => ev_entry_k dcText_live)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hr ho hk => dc_func_spec dcText_live hp hr ho hk)
    hint hstr htos

end Dc.Mach
