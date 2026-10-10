import Dc.Mach.EvalDivRun
import Dc.Mach.BootEvalCall
import Dc.Mach.EvalEntryB
import Dc.Mach.DcFuncSpec
import Dc.Mach.EvalTos5
import Dc.Mach.EvalInv
import Dc.Mach.EvalIntB
import Dc.Mach.EvalStrB

/-!
# `EvalstrDivSpec` from the segments (M10, stuck direction)

`div_supply`: the positions of a diverging evaluation (`DivAt`) with their
segments form a `DivSupply`; `div_lob` turns it into the partial WP with a
nonzero exit code at every position. `evalstrDiv_of`: `EvalstrDivSpec` from
the entry position. The term direction's entry at every fuel
(`EvEntrySpec`) closes a nested evaluation that completes.
-/

namespace Dc.Mach

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **From the `DC_EVALTOS` code** (`ev_tos_k`): a plain value or the tail
call to the loop head; a nested evaluation diverging to its entry, or
completing (`EvEntrySpec` at its fuel) to the loop head after it. -/
theorem tos_dwo (hev : ∀ Q n, EvEntrySpec dcLive dcOwn Q n) {t0 : String} {sp W d k q : Nat}
    {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs xs : List GV} {st : St} {rest : List Nat} {td : Nat} {o : StrObj}
    (ev : EvAt dcOwn sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o)
    (h25 : R 25 = BitVec.ofNat 64 (sp - 176 + 32)) (bud : TosDivBud 70 d k st rest td) :
    DWO dcLive dcOwn (DivQ [.head, .entry]) (t0 ++ Dc.outStr st.out) 0x80001748#64 R M := by
  have hh : DivPos.head ∈ [DivPos.head, .entry] := by simp
  have he : DivPos.entry ∈ [DivPos.head, .entry] := by simp
  refine ev_tos_k dcText_live ev h25 (evOom_div ev)
    (fun hs' => ⟨headK hh (bud.plain hs'), endK (bud.plain hs')⟩) (fun x more p' hst hw => ?_)
    (fun x more hst hw => ?_)
  · have b := bud.tailCall hst hw
    refine ⟨?_, headK hh b, endK b⟩
    have := b.tail 0
    simpa [tailMax] using this
  · obtain ⟨hd, hb⟩ := bud.nested hst hw
    have hx : x.length < 2 ^ 24 := ev.sb.top hst x (by simp [Val.strs])
    rcases hb with b | ⟨n, k1, st', hfu, hk1, b⟩
    · refine ⟨d - 1, k, fun _ _ => False, by omega, Nat.le_refl _, ?_, fun _ _ h => h.elim⟩
      intro R1 M1 H1 G1 p' o1 en hox _ _
      exact swpo_done fun _ _ hm => .inl ⟨.entry, he, t0, sp - 176, W - 176, d - 1, k, sp - 176 + 32,
        M1, R1, H1, F, L, C, G1, .str p' :: (xs ++ hs), [], { st with stack := more }, o1,
        ⟨en, by rw [hox]; exact b, rfl, hm⟩⟩
    · refine ⟨d - 1, k1, fun st1 r1 => st1 = st' ∧ r1 = .ok, by omega, hk1, ?_, ?_⟩
      · intro R1 M1 H1 G1 p' o1 en hox hoom hk
        exact hev _ n t0 (sp - 176) (W - 176) (d - 1) k1 (sp - 176 + 32) M1 R1 H1 F L C G1 _ [] _ st'
          o1 .ok (by rw [hox]; exact hfu) en hoom (hk _ _ ⟨rfl, rfl⟩)
      · rintro st1 r1 ⟨rfl, rfl⟩
        have hi := (inv_step n).1 _ _ _ _ hfu.run ⟨ev.sb.pop hst, ev.srt.stack more, hx⟩
        exact ⟨hi.1, hi.2, fun _ => ⟨headK hh b, endK b⟩, fun h => Status.noConfusion h,
          fun h => Status.noConfusion h⟩

/-- **From the `DC_EVALTOS` code** to the loop head or a nested entry. -/
theorem seg_tos (hev : ∀ Q n, EvEntrySpec dcLive dcOwn Q n) {t : String} {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} (hat : DivAt .tos t rv mv) :
    ∃ Qp : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop,
      LRO (vsaModel dcLive) roR dcText dcRegs dcOwn Qp t rv mv ∧ ¬ Qp t rv mv ∧
      ∀ t' rv' mv', Qp t' rv' mv' →
        (∃ p', DivAt p' t' rv' mv') ∨ ∃ e, ExitW (fun v => v.1 ≠ 0) t' rv' e := by
  obtain ⟨t0, sp, W, d, k, q, M0, R0, R, M, H, F, L, C, G, hs, xs, st, rest, td, o, h⟩ := hat
  refine div_seg (ps := [.head, .entry]) ?_ h.mat (by simp [posPC]) (by decide)
  rw [h.con]
  exact tos_dwo hev h.ev h.h25 h.bud

/-- **The positions with their segments.** -/
theorem div_supply (hent : ∀ Q, EvEntryCore dcLive dcOwn Q) (hfn : ∀ Q, FnSpecH dcLive dcOwn Q)
    (hint : ∀ Q, EvIntCore dcLive dcOwn Q) (hstr : ∀ Q, EvStrCore dcLive dcOwn Q)
    (hev : ∀ Q n, EvEntrySpec dcLive dcOwn Q n) : DivSupply dcLive dcOwn DivPos DivAt where
  step p _ _ _ h := match p, h with
    | .entry, h => seg_entry hent h
    | .head, h => seg_head hfn h
    | .ret, h => seg_ret hint hstr h
    | .tos, h => seg_tos hev h

/-- **`EvalstrDivSpec`** from the segments. -/
theorem evalstrDiv_of (hent : ∀ Q, EvEntryCore dcLive dcOwn Q) (hfn : ∀ Q, FnSpecH dcLive dcOwn Q)
    (hint : ∀ Q, EvIntCore dcLive dcOwn Q) (hstr : ∀ Q, EvStrCore dcLive dcOwn Q)
    (hev : ∀ Q n, EvEntrySpec dcLive dcOwn Q n) : EvalstrDivSpec dcLive dcOwn := by
  intro _G t0 sp W d k q M R H F L C G hs xs st o hno hb e rv mv hm
  have hat : DivAt .entry (t0 ++ Dc.outStr st.out) rv mv :=
    ⟨t0, sp, W, d, k, q, M, R, H, F, L, C, G, hs, xs, st, o,
      ⟨{ len := hb.frameLen, sb := e.sb, srt := e.srt, dc := e.dc, strIn := e.strIn,
          held := e.held, slot := e.slot, slotPlace := e.slotPlace, r2 := e.r2, r10 := e.r10,
          al := e.al, frame := e.frame, room := e.room, stk := e.stk, stkPr := e.stkPr,
          stkDn := e.stkDn, budget := e.budget, mb := e.mb, err := e.err, globs := e.globs },
        ⟨hb.nest, hb.leak, hb.size, hb.tail, runDiv_of_not hno⟩, rfl, hm⟩⟩
  have H := div_lob (GF := MachGF) dcText_live (div_supply hent hfn hint hstr hev)
  iintro ⟨#Hro, Hr⟩
  ihave Hw := H $$ %DivPos.entry %(t0 ++ Dc.outStr st.out) %rv %mv %hat Hro Hr
  iexact Hw

/-- **`EvalstrDivSpec`** with the entry (`ev_entry_k`) and `dc_func`'s
contract (`dc_func_spec`) discharged. -/
theorem evalstrDiv (hint : ∀ Q, EvIntCore dcLive dcOwn Q) (hstr : ∀ Q, EvStrCore dcLive dcOwn Q)
    (hev : ∀ Q n, EvEntrySpec dcLive dcOwn Q n) : EvalstrDivSpec dcLive dcOwn :=
  evalstrDiv_of (fun _ => ev_entry_k dcText_live)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hr ho hk => dc_func_spec dcText_live hp hr ho hk)
    hint hstr hev

/-- **`EvalstrDivSpec`** from the term direction's entry at every fuel
(`EvEntrySpec`): `DC_INT` (`evs_int_k`) and `DC_STR` (`evs_str_k`) discharged. -/
theorem evalstrDiv_of_term (hev : ∀ Q n, EvEntrySpec dcLive dcOwn Q n) :
    EvalstrDivSpec dcLive dcOwn :=
  evalstrDiv (fun _ => evs_int_k dcText_live) (fun _ => evs_str_k dcText_live) hev

end Dc.Mach
