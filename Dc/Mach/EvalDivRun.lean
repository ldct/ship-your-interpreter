import Dc.Mach.EvalDivLob
import Dc.Mach.EvalDivBudget
import Dc.Mach.EvalPieces
import Dc.Mach.EvalCases1
import Dc.Mach.EvalCases2
import Dc.Mach.EvalCases3
import Dc.Mach.EvalCases4
import Dc.Mach.EvalCases5
import Dc.Mach.EvalCases7
import Dc.Mach.OomMemfail
import Dc.Mach.MainTail

/-!
# `evalstr`'s diverging run, position by position (M10, stuck direction)

The positions of a diverging evaluation (`DivPos`, `DivAt`), each with the
machine state of A's term-direction invariants and the model-side budgets of
a diverging evaluation (`DivBud`, `TosDivBud`):

* `entry`: `evalstr`'s entry (`0x80001448`, `EvEntry`);
* `head`: the loop head (`0x800014f8`, `EvAt`);
* `ret`: `dc_func`'s return (`0x80001528`/`0x80001728`, `EvCall` and the
  outcome `FnOut`);
* `tos`: the `DC_EVALTOS` code (`0x80001748`).

The segments between them reuse A's continuation-generic spans: the entry
(`EvEntryCore`), the call of `dc_func` (`ev_call_mid`/`ev_call_last` with
`dc_func`'s contract `FnSpecH`), and the status cores `evs_*_k` (with
`EvIntCore`/`EvStrCore`). An empty next frame, `DC_QUIT` leaving the
activation and `DC_EOF_ERROR` contradict the divergence. `evOom_div`: every
out-of-memory point inside the activation exits with status 1.
-/

namespace Dc.Mach

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## Positions -/

/-- **At the loop head** of a diverging evaluation. -/
structure DivHead (t : String) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (t0 : String)
    (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk)
    (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St) (f : Frame)
    (o : StrObj) : Prop where
  ev : EvAt dcOwn sp W d k q M0 R0 R M H F L C G hs xs st f o
  h12 : R 12 = boolWord f.neg
  bud : DivBud 70 d k st f
  con : t = t0 ++ Dc.outStr st.out
  mat : Matches dcRegs dcOwn 0x800014f8#64 R M rv mv

/-- **At `dc_func`'s return** in a diverging evaluation. -/
structure DivRet (t : String) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (t0 : String)
    (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk)
    (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St) (c : Nat)
    (rest : List Nat) (td : Nat) (neg : Bool) (o : StrObj) (Rc R' : Nat → BitVec 64) (Mc M' : Mem)
    (H' : Heap) (F' : List Blk) (L' : List NumObj) (C' : BcConsts) (G' : DcG) (st' : St)
    (ex : List GV) (code : Nat) : Prop where
  e : EvCall dcOwn sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
    G' st' ex
  fo : FnOut st (dcFunc 70 st c rest.head? neg) code st'
  h10 : R' 10 = BitVec.ofNat 64 code
  bud : DivBud 70 d k st ⟨c :: rest, td, neg⟩
  con : t = t0 ++ Dc.outStr st'.out
  mat : Matches dcRegs dcOwn (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' rv mv

/-- **At the `DC_EVALTOS` code** in a diverging evaluation. -/
structure DivTos (t : String) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (t0 : String)
    (sp W d k q : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk)
    (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St) (rest : List Nat)
    (td : Nat) (o : StrObj) : Prop where
  ev : EvAt dcOwn sp W d k q M0 R0 R M H F L C G hs xs st ⟨rest, td, false⟩ o
  h25 : R 25 = BitVec.ofNat 64 (sp - 176 + 32)
  bud : TosDivBud 70 d k st rest td
  con : t = t0 ++ Dc.outStr st.out
  mat : Matches dcRegs dcOwn 0x80001748#64 R M rv mv

/-- **At `evalstr`'s entry** with a diverging evaluation. -/
structure DivEntry (t : String) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (t0 : String)
    (sp W d k q : Nat) (M : Mem) (R : Nat → BitVec 64) (H : Heap) (F : List Blk)
    (L : List NumObj) (C : BcConsts) (G : DcG) (hs xs : List GV) (st : St) (o : StrObj) : Prop where
  en : EvEntry dcOwn sp W d k q M R H F L C G hs xs st o
  bud : DivBud 70 d k st ⟨o.s, 1, false⟩
  con : t = t0 ++ Dc.outStr st.out
  mat : Matches dcRegs dcOwn 0x80001448#64 R M rv mv

/-- The positions. -/
inductive DivPos where
  | entry | head | ret | tos

/-- At a position. -/
def DivAt : DivPos → String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop
  | .entry, t, rv, mv => ∃ t0 sp W d k q M R H F L C G hs xs st o,
      DivEntry t rv mv t0 sp W d k q M R H F L C G hs xs st o
  | .head, t, rv, mv => ∃ t0 sp W d k q M0 R0 R M H F L C G hs xs st f o,
      DivHead t rv mv t0 sp W d k q M0 R0 R M H F L C G hs xs st f o
  | .ret, t, rv, mv => ∃ t0 sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H'
      F' L' C' G' st' ex code, DivRet t rv mv t0 sp W d k q M0 R0 R M H F L C G hs xs st c rest td
        neg o Rc R' Mc M' H' F' L' C' G' st' ex code
  | .tos, t, rv, mv => ∃ t0 sp W d k q M0 R0 R M H F L C G hs xs st rest td o,
      DivTos t rv mv t0 sp W d k q M0 R0 R M H F L C G hs xs st rest td o

/-- A segment's end: one of the given positions, or `_exit`'s store with a
nonzero code. -/
def DivQ (ps : List DivPos) (t : String) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  (∃ p ∈ ps, DivAt p t rv mv) ∨ ∃ e, ExitW (fun v => v.1 ≠ 0) t rv e

/-- The PCs of a position. -/
def posPC : DivPos → BitVec 64 → Prop
  | .entry, pc => pc = 0x80001448#64
  | .head, pc => pc = 0x800014f8#64
  | .ret, pc => pc = 0x80001528#64 ∨ pc = 0x80001728#64
  | .tos, pc => pc = 0x80001748#64

theorem DivAt.pc {p : DivPos} {t : String} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : DivAt p t rv mv) : posPC p (rv VsaIris.PC) := by
  cases p with
  | entry => obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h; exact h.mat.pc
  | head => obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h; exact h.mat.pc
  | tos => obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h; exact h.mat.pc
  | ret =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rest, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, h⟩ := h
    have := h.mat.pc
    show _ ∨ _
    by_cases hr : rest = [] <;> simp only [hr, ↓reduceIte] at this <;> simp [this]

/-- **A segment** from a symbolic run into positions `ps`, which the start
is not at. -/
theorem div_seg {ps : List DivPos} {t : String} {pc : BitVec 64} {R : Nat → BitVec 64} {M : Mem}
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} (hd : DWO dcLive dcOwn (DivQ ps) t pc R M)
    (hm : Matches dcRegs dcOwn pc R M rv mv) (hne : ∀ p ∈ ps, ¬ posPC p pc)
    (hx : pc ≠ 0x800005c8#64) :
    ∃ Qp : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop,
      LRO (vsaModel dcLive) roR dcText dcRegs dcOwn Qp t rv mv ∧ ¬ Qp t rv mv ∧
      ∀ t' rv' mv', Qp t' rv' mv' →
        (∃ p', DivAt p' t' rv' mv') ∨ ∃ e, ExitW (fun v => v.1 ≠ 0) t' rv' e := by
  refine ⟨DivQ ps, swpo_run hd hm, ?_, fun _ _ _ h => h.imp (fun ⟨p, _, hp⟩ => ⟨p, hp⟩) id⟩
  rintro (⟨p, hp, hat⟩ | ⟨e, hw⟩)
  · exact hne p hp (hm.pc ▸ hat.pc)
  · exact hx (hm.pc ▸ hw.pc)

/-! ## Out of memory -/

/-- **Out of memory inside an activation** exits with status 1, into any
segment end. -/
theorem evOom_div {ps : List DivPos} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64}
    {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
    {hs xs : List GV} {st : St} {f : Frame} {o : StrObj}
    (ev : EvAt dcOwn sp W d k q M0 R0 R M H F L C G hs xs st f o) :
    EvOom dcLive dcOwn (DivQ ps) sp W q M0 := by
  intro t' R' M' sp' ho
  have hlo := ho.lo; have hhi := ho.hi; have hal := ho.al
  have hroom := ev.room; have hsf := ev.frame; have hsh := hsf.hi
  have hq := ev.slotPlace.lo
  have htx : tohostAddr = 0x8001ad00 := rfl
  simp only [heapEnd] at hroom
  -- `progname` and `stderr` at the activation's entry, through the invariant's frame
  have pin : ∀ a, PinWords a → imgM M a = imgM M0 a := fun a hp =>
    ev.out a (DcGlob.outHeap (by simp only [PinWords, DcGlob] at hp ⊢; omega)) (fun hc => hc.2 hp)
      (fun ho => by simp only [ocG, PinWords, stdoutFile, lineMaxAddr, errnoAddr, outColAddr,
        dc_addrs] at ho hp; omega)
      (fun hf => by simp only [frameIn, PinWords, dc_addrs] at hf hp; omega)
      (fun hf => by simp only [PinWords, dc_addrs] at hf hp; omega)
      (fun hf => by simp only [PinWords, dc_addrs] at hf hp; omega)
      (fun hf => by simp only [PinWords, InP, inPtrAddr, dc_addrs] at hf hp; omega)
  have hpn : ldv .ld M0 prognameAddr = BitVec.ofNat 64 dcNameAddr := by
    rw [← ldv_congr .ld fun j hj => pin _ (by simp only [PinWords, widthOfM, dc_addrs] at hj ⊢; omega)]
    exact ev.dc.view.prog
  have hfd : FdAt dcOwn M0 stderrAddr 2 :=
    { ev.dc.errFile with
      val := by
        rw [← ldv_congr .lw fun j hj => pin _ (by
          simp only [PinWords, widthOfM, stderrAddr, dc_addrs] at hj ⊢; omega)]
        exact ev.dc.errFile.val }
  refine oom_memfail dcText_live ev.dc.glob hpn hfd (by simp only [heapEnd]; omega)
    (fun a hp hc => ?_) ho
    ⟨fun a e1 e2 => ⟨by simp only [tohostAddr]; omega, by simp only [stackTop]; omega⟩,
      by omega, by omega, hal⟩ (by simp only [stderrAddr]; omega)
    fun R'' M'' h15 h14 => swpo_done fun rv _ hm =>
      .inr ⟨1#64, { pc := hm.pc
                    base := (hm.regs 14 (by decide) (by decide)).trans h14
                    word := (hm.regs 15 (by decide) (by decide)).trans h15
                    lt := by decide
                    post := by show (1 : Nat) ≠ 0; decide }⟩
  simp only [PinWords, ocG, InP, inPtrAddr, stdoutFile, lineMaxAddr, errnoAddr, outColAddr,
    dc_addrs] at hp hc
  omega

/-! ## Continuations into the positions -/

section

variable {ps : List DivPos} {t0 : String} {sp W d k k' q : Nat} {M0 : Mem} {R0 : Nat → BitVec 64}
  {G : DcG} {hs xs : List GV} {st' : St}

/-- The loop head as a segment's end. -/
theorem headK {f' : Frame} (hp : DivPos.head ∈ ps) (bud : DivBud 70 d k' st' f') :
    EvHeadK dcLive dcOwn (DivQ ps) t0 sp W d k k' q M0 R0 G hs xs st' f' :=
  fun R2 M2 H2 F2 L2 C2 G2 xs2 o' ev h12 _ _ _ => swpo_done fun _ _ hm =>
    .inl ⟨.head, hp, t0, sp, W, d, k', q, M0, R0, R2, M2, H2, F2, L2, C2, G2, hs, xs2, st', f', o',
      ⟨ev, h12, bud, rfl, hm⟩⟩

/-- An empty next frame contradicts the divergence. -/
theorem endK {f' : Frame} {k' : Nat} (bud : DivBud 70 d k' st' f') :
    EvEndK dcLive dcOwn (DivQ ps) t0 sp W d k q M0 R0 G hs xs st' f' := fun he => by
  obtain ⟨s, td, neg⟩ := f'
  simp only at he
  subst he
  exact (RunDiv.not_nil bud.run).elim

/-- The `DC_EVALTOS` code as a segment's end. -/
theorem tosK {rest : List Nat} {td : Nat} (hp : DivPos.tos ∈ ps) (bud : TosDivBud 70 d k' st' rest td) :
    EvTosK dcLive dcOwn (DivQ ps) t0 sp W d k k' q M0 R0 G hs xs st' rest td :=
  fun R2 M2 H2 F2 L2 C2 G2 xs2 o' ev h25 _ _ => swpo_done fun _ _ hm =>
    .inl ⟨.tos, hp, t0, sp, W, d, k', q, M0, R0, R2, M2, H2, F2, L2, C2, G2, hs, xs2, st', rest, td, o',
      ⟨ev, h25, bud, rfl, hm⟩⟩

end

/-! ## The segments -/

/-- **From `evalstr`'s entry** to its loop head (`EvEntryCore`). -/
theorem seg_entry (hent : ∀ Q, EvEntryCore dcLive dcOwn Q) {t : String} {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} (hat : DivAt .entry t rv mv) :
    ∃ Qp : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop,
      LRO (vsaModel dcLive) roR dcText dcRegs dcOwn Qp t rv mv ∧ ¬ Qp t rv mv ∧
      ∀ t' rv' mv', Qp t' rv' mv' →
        (∃ p', DivAt p' t' rv' mv') ∨ ∃ e, ExitW (fun v => v.1 ≠ 0) t' rv' e := by
  obtain ⟨t0, sp, W, d, k, q, M, R, H, F, L, C, G, hs, xs, st, o, h⟩ := hat
  refine div_seg (ps := [.head]) ?_ h.mat (by simp [posPC]) (by decide)
  rw [h.con]
  exact hent _ t0 sp W d k q M R H F L C G hs xs st o h.en (fun _ => headK (by simp) h.bud)
    fun he => (RunDiv.not_nil (he ▸ h.bud.run)).elim

/-- **From the loop head** to `dc_func`'s return (`ev_call_mid`/`ev_call_last`). -/
theorem seg_head (hfn : ∀ Q, FnSpecH dcLive dcOwn Q) {t : String} {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} (hat : DivAt .head t rv mv) :
    ∃ Qp : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop,
      LRO (vsaModel dcLive) roR dcText dcRegs dcOwn Qp t rv mv ∧ ¬ Qp t rv mv ∧
      ∀ t' rv' mv', Qp t' rv' mv' →
        (∃ p', DivAt p' t' rv' mv') ∨ ∃ e, ExitW (fun v => v.1 ≠ 0) t' rv' e := by
  obtain ⟨t0, sp, W, d, k, q, M0, R0, R, M, H, F, L, C, G, hs, xs, st, ⟨s, td, neg⟩, o, h⟩ := hat
  refine div_seg (ps := [.ret]) ?_ h.mat (by simp [posPC]) (by decide)
  rw [h.con]
  cases s with
  | nil => exact (RunDiv.not_nil h.bud.run).elim
  | cons c rest =>
    have hcall : CallOK st c := by have := h.bud.size 1; simp only [AllCalls] at this; exact this.1
    have hret : ∀ (pc : Nat), pc = (if rest = [] then 0x80001728 else 0x80001528) →
        ∀ Rc Mc, Keeps [1, 10, 11, 15, 23] Rc R → Rc 23 = R 8 + 1#64 →
        EvCallMem sp M Mc (peekWord rest.head?) →
        EvRet dcLive dcOwn (DivQ [.ret]) t0 sp W G (xs ++ hs) st c (dcFunc 70 st c rest.head? neg) Rc Mc
          pc := by
      intro pc hpc Rc Mc kc c23 mem R' M' H' F' L' C' G' code st' ex k1 e2 e10 hfo hp
      exact swpo_done fun _ _ hm => .inl ⟨.ret, by simp, t0, sp, W, d, k, q, M0, R0, R, M, H, F, L, C,
        G, hs, xs, st, c, rest, td, neg, o, Rc, R', Mc, M', H', F', L', C', G', st', ex, code,
        ⟨⟨h.ev, kc, c23, mem, k1, e2, hp⟩, hfo, e10, h.bud, rfl,
          by rw [hpc] at hm; by_cases hr : rest = [] <;> simp only [hr, ↓reduceIte] at hm ⊢ <;> exact hm⟩⟩
    by_cases hr : rest = []
    · subst hr
      exact ev_call_last dcText_live (hfn _) h.ev h.h12 hcall (evOom_div h.ev)
        (hret 0x80001728 (by simp))
    · exact ev_call_mid dcText_live (hfn _) h.ev h.h12 hr hcall (evOom_div h.ev)
        (hret 0x80001528 (by simp [hr]))

/-- **From `dc_func`'s return**: the status cases (`evs_*_k`, `EvIntCore`,
`EvStrCore`) to the loop head or the `DC_EVALTOS` code. -/
theorem ret_dwo (hint : ∀ Q, EvIntCore dcLive dcOwn Q) (hstr : ∀ Q, EvStrCore dcLive dcOwn Q)
    {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV} {st : St} {c : Nat}
    {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj} {Rc R' : Nat → BitVec 64} {Mc M' : Mem}
    {H' : Heap} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG} {st' : St}
    {ex : List GV} {code : Nat}
    (e : EvCall dcOwn sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st' ex)
    (fo : FnOut st (dcFunc 70 st c rest.head? neg) code st') (h10 : R' 10 = BitVec.ofNat 64 code)
    (bud : DivBud 70 d k st ⟨c :: rest, td, neg⟩) :
    DWO dcLive dcOwn (DivQ [.head, .tos]) (t0 ++ Dc.outStr st'.out)
      (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  have hh : DivPos.head ∈ [DivPos.head, .tos] := by simp
  have ht : DivPos.tos ∈ [DivPos.head, .tos] := by simp
  generalize hres : dcFunc 70 st c rest.head? neg = res at fo
  cases fo with
  | ok s =>
    obtain ⟨b, -, hlc⟩ := bud.ok hres
    obtain ⟨hsb, hsrt⟩ := res_ok_facts e.ev.sb e.ev.srt hres
    exact evs_zero_k dcText_live e h10 hlc hsb hsrt (headK hh b) (endK b)
  | eatOne s =>
    obtain ⟨b, -, hlc⟩ := bud.eatOne hres
    exact evs_eat_k dcText_live e hres h10 hlc (headK hh b) (endK b)
  | evalReg s reg =>
    have hlc : leakOne c ≤ k := by
      cases hg : regGet st' reg with
      | none => exact (bud.evalRegNone hres hg).2.2
      | some v => exact (bud.evalReg hres hg).2.2
    exact evs_reg_k dcText_live e hres h10 hlc (evOom_div e.ev)
      (fun v hg => tosK ht (bud.evalReg hres hg).1) (fun hg => headK hh (bud.evalRegNone hres hg).1)
      (fun hg => endK (bud.evalRegNone hres hg).1)
  | evalTos s =>
    obtain ⟨b, -, hlc⟩ := bud.evalTos hres
    exact evs_tos_k dcText_live e hres h10 hlc (tosK ht b)
  | quit s =>
    obtain ⟨hlt, b, -, hlc⟩ := bud.quitStay hres
    exact evs_quit_k dcText_live e hres h10 hlc (fun hle => absurd hle (Nat.not_le.mpr hlt))
      (fun _ => headK hh b) (fun _ => endK b)
  | int =>
    obtain ⟨b, -, hlc⟩ := bud.int hres
    exact hint _ t0 sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' ex e hres h10 hlc (evOom_div e.ev) (headK hh b) (endK b)
  | str =>
    obtain ⟨b, -, hlc⟩ := bud.str hres
    exact hstr _ t0 sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' ex e hres h10 hlc (evOom_div e.ev) (headK hh b) (endK b)
  | system =>
    obtain ⟨b, -, hlc⟩ := bud.system hres
    exact evs_system_k dcText_live e h10 hlc (evOom_div e.ev) (headK hh b) (endK b)
  | comment =>
    obtain ⟨b, -, hlc⟩ := bud.comment hres
    exact evs_comment_k dcText_live e h10 hlc (headK hh b) (endK b)
  | negcmp =>
    obtain ⟨b, -, hlc⟩ := bud.negcmp hres
    exact evs_neg_k dcText_live e h10 hlc (headK hh b) (endK b)
  | eofError => exact (runDiv_eof bud.run hres).elim
  | sqrt hsq =>
    obtain ⟨b, -, hlc⟩ := bud.sqrt hres hsq
    exact evs_sqrt_k dcText_live e hres h10 hlc (headK hh b) (endK b)

/-- **From `dc_func`'s return** to the loop head or the `DC_EVALTOS` code. -/
theorem seg_ret (hint : ∀ Q, EvIntCore dcLive dcOwn Q) (hstr : ∀ Q, EvStrCore dcLive dcOwn Q)
    {t : String} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} (hat : DivAt .ret t rv mv) :
    ∃ Qp : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop,
      LRO (vsaModel dcLive) roR dcText dcRegs dcOwn Qp t rv mv ∧ ¬ Qp t rv mv ∧
      ∀ t' rv' mv', Qp t' rv' mv' →
        (∃ p', DivAt p' t' rv' mv') ∨ ∃ e, ExitW (fun v => v.1 ≠ 0) t' rv' e := by
  obtain ⟨t0, sp, W, d, k, q, M0, R0, R, M, H, F, L, C, G, hs, xs, st, c, rest, td, neg, o, Rc, R',
    Mc, M', H', F', L', C', G', st', ex, code, h⟩ := hat
  refine div_seg (ps := [.head, .tos]) ?_ h.mat
    (by by_cases hr : rest = [] <;> simp [posPC, hr]) (by by_cases hr : rest = [] <;> simp [hr])
  rw [h.con]
  exact ret_dwo hint hstr h.e h.fo h.h10 h.bud

end Dc.Mach
