import Dc.Mach.EvalRoutes
import Dc.Mach.DcFuncArmR1

/-!
# `evalstr`'s `DC_QUIT` route (M10)

At `0x800016b8`: `unwind_depth` against `tail_depth`. With
`unwind_depth ≥ tail_depth` the activation stores `unwind_depth -
tail_depth` and returns `DC_QUIT` (`ev_quit_out`); otherwise it stays with
`tail_depth - unwind_depth` (`rt_quit_stay`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- The invariant at other caller-saved registers. -/
theorem EvAt.mod {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R R1 : Nat → BitVec 64} {M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV} {st : St}
    {f : Frame} {o : StrObj} (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o)
    (k1 : Keeps cClob R1 R) : EvAt S sp W d k q M0 R0 R1 M H F L C G hs xs st f o :=
  { ev with
    pos := by
      obtain ⟨i, hi, hd, h8⟩ := ev.pos
      exact ⟨i, hi, hd, (k1.get 8 (by decide)).trans h8⟩
    s1 := (k1.get 9 (by decide)).trans ev.s1
    s6 := (k1.get 22 (by decide)).trans ev.s6
    s8 := (k1.get 24 (by decide)).trans ev.s8
    cs := ⟨(k1.get 18 (by decide)).trans ev.cs.s2, (k1.get 19 (by decide)).trans ev.cs.s3,
      (k1.get 20 (by decide)).trans ev.cs.s4, (k1.get 21 (by decide)).trans ev.cs.s5⟩
    r2 := (k1.get 2 (by decide)).trans ev.r2
    keep := (k1.mono (by decide)).trans ev.keep }

/-- **A return with the status set** at `0x8000185c` (`s0`–`s9` reloaded,
the epilogue). -/
theorem ev_ret {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {sp W d k q : Nat} {M0 : Mem}
    {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
    {G : DcG} {hs xs : List GV} {st : St} {f : Frame} {o : StrObj} {r : Status}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o) (h10 : R 10 = statusWord r)
    {Ge : DcG} {hse xse : List GV} {ke : Nat} (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail)
    (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st r) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x8000185c#64 R M := by
  have hsf : StackFrame S sp 176 := ev.frame.mono (by have := ev.stk; omega)
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := ev.room; simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have e2 := ev.r2
  have sv := ev.saved
  have g1 := sv.get 1 168 (by decide); have g8 := sv.get 8 160 (by decide)
  have g9 := sv.get 9 152 (by decide); have g18 := sv.get 18 144 (by decide)
  have g19 := sv.get 19 136 (by decide); have g20 := sv.get 20 128 (by decide)
  have g21 := sv.get 21 120 (by decide); have g22 := sv.get 22 112 (by decide)
  have g23 := sv.get 23 104 (by decide); have g24 := sv.get 24 96 (by decide)
  have g25 := sv.get 25 88 (by decide)
  have hal := ev.al
  bc_run hlive hlive [e2, g8, g9, g18, g19, g20, g21, g22, g23, g24, g25] at 0x8000147c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hstk := ev.stk
  refine ev_epi hlive hsf (by simp only [heapEnd]; omega) _ (by bsimp [e2]) g1 hal
    fun R' k e1 e2' => hk R' M H F L C G xs o.hb.pay ?_ (e2'.trans ev.r20.symm) ?_ ?_
  · refine Keeps.restoreAll (rs := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25])
      ((k.mono (by decide)).trans (by keeps_tac (ev.keep.mono (by decide)))) fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact e1
    · exact e2'.trans ev.r20.symm
    all_goals rw [k.get _ (by decide)]; bsimp []
  · rw [k.get 10 (by decide)]; bsimp [h10]
  · have hh := ev.held
    obtain ⟨hst, rfl⟩ : ∃ hst, hs = .str o.hb.pay :: hst := by
      cases hs with
      | nil => cases hh
      | cons g hst => simp at hh; subst hh; exact ⟨hst, rfl⟩
    simp only [List.tail_cons] at htl hpin
    exact
      { dc := htl ▸ ev.dc
        slot := ev.slot
        strIn := ⟨o, ev.strIn, rfl⟩
        grow := by omega
        pin := htl ▸ hpin
        mb := ev.mb
        globs := ev.globs
        out := fun a e1 e2 e3 e4 e5 e6 => ev.out a e1 e2 e3
          (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))
          (fun hf => e4 (by simp only [frameIn]; omega)) e5 e6 }

/-- The invariant after a store to `unwind_depth` alone. -/
theorem EvAt.setUnwind {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64}
    {M M1 : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
    {hs xs : List GV} {st : St} {f : Frame} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o)
    (hm1 : MemOnly (fun a => unwindAddr ≤ a ∧ a < unwindAddr + 4) M1 M) {v : Nat}
    (hv : ldv .lw M1 unwindAddr = BitVec.ofNat 64 v) (hvl : v < 2 ^ 31) :
    EvAt S sp W d k q M0 R0 R M1 H F L C G hs xs { st with unwind := v } f o := by
  have hq := ev.slotPlace
  have hab := ev.room; have hstk := ev.stk
  have hfar : ∀ a, sp - 176 ≤ a → imgM M1 a = imgM M a := fun a ha =>
    hm1 a (by simp only [unwindAddr, heapEnd] at hab ⊢; omega)
  have hglob : ∀ a, ¬ (DcGlob a ∧ ¬ PinWords a) → imgM M1 a = imgM M a := fun a ha =>
    hm1 a fun hw => ha ⟨by simp only [DcGlob, dc_addrs] at hw ⊢; omega,
      by simp only [PinWords, dc_addrs] at hw ⊢; omega⟩
  exact
    { ev with
      dc := ev.dc.setUnwind' hm1 hv hvl
      sb := ⟨ev.sb.1, ev.sb.2⟩
      srt := fun r e he => ev.srt r e he
      slot := ⟨by rw [ldv_congr .ld fun j hj => hfar _ (by have := hq.lo; omega)]; exact ev.slot.tag,
               by rw [ldv_congr .ld fun j hj => hfar _ (by have := hq.lo; omega)]; exact ev.slot.ptr⟩
      saved := ev.saved.transport (lo := 88) (top := 176) (hag := fun a h1 h2 => hfar a (by omega))
      mb := ev.mb.transport fun a e1 e2 => hm1 a (by simp only [mulBaseAddr, unwindAddr] at e1 e2 ⊢; omega)
      globs := by
        have g := ev.globs
        exact ⟨g.intrOwn, by rw [ldv_congr .lw fun j hj => hm1 _ (by simp only [unwindAddr, widthOfM] at hj ⊢; omega)]; exact g.intr,
          g.laOwn, by rw [ldv_congr .lw fun j hj => hm1 _ (by simp only [unwindAddr, widthOfM] at hj ⊢; omega)]; exact g.la,
          g.inOwn⟩
      out := fun a e1 e2 e3 e4 e5 e6 e7 => (hglob a e2).trans (ev.out a e1 e2 e3 e4 e5 e6 e7) }

/-- **`DC_QUIT` leaving the activation** (`0x800016b8`, `unwind_depth ≥
tail_depth`): `unwind_depth -= tail_depth`, `DC_QUIT` returned. -/
theorem ev_quit_out {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t0 : String} {sp W d k q : Nat} {M0 : Mem}
    {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
    {G : DcG} {hs xs : List GV} {st : St} {f : Frame} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o) (hle : f.td ≤ st.unwind)
    {Ge : DcG} {hse xse : List GV} {ke : Nat} (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail)
    (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse { st with unwind := st.unwind - f.td } .quit) :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800016b8#64 R M := by
  have hsf : StackFrame S sp 176 := ev.frame.mono (by have := ev.stk; omega)
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab := ev.room; simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hG := ev.dc.glob
  have hu := ev.dc.view.unwind
  have hur := ev.dc.den.unwind
  have e24 := ev.s8
  have htd := ev.tdLt
  have ti1 : (BitVec.ofNat 64 f.td).toInt = f.td := toInt_ofNat_small (by omega)
  have ti2 : (BitVec.ofNat 64 st.unwind).toInt = st.unwind := toInt_ofNat_small (by omega)
  have hsw := subw_ofNat hle hur
  bc_run hlive hlive [hu, e24, ti1, ti2] at 0x8000190c 0x800016c4
  all_goals first | (intro hc; exfalso; omega) | intro _
  bc_run hlive hlive [hu, e24, ti1, ti2, hsw] at 0x8000185c
  all_goals first | (intro b hb; have := of_mem_accAddrs hb; exact hG b (by simp only [DcGlob, dc_addrs]; omega)) | skip
  generalize hM1 : writeLog M [(2147601800, 4, BitVec.ofNat 64 (st.unwind - f.td))] = M1
  have hm1 : MemOnly (fun a => unwindAddr ≤ a ∧ a < unwindAddr + 4) M1 M := fun a ha => by
    rw [← hM1, imgM_store_miss _ _ (by simp only [unwindAddr] at ha; omega)]
  have hv : ldv .lw M1 unwindAddr = BitVec.ofNat 64 (st.unwind - f.td) := by
    rw [← hM1]; exact ldv_lw_hitN _ rfl (by simp only [BitVec.toNat_ofNat]; omega) (by omega)
  exact ev_ret (r := .quit) (st := { st with unwind := st.unwind - f.td }) hlive ((ev.setUnwind hm1 hv (by omega)).mod (by keeps_tac Keeps.refl _ _))
    (by bsimp []; rfl) htl hgrow hpin hk

/-- **`DC_QUIT` absorbed by tail-recursion levels** (`0x800016b8`,
`unwind_depth < tail_depth`): `s0 = s7`, `tail_depth -= unwind_depth`,
`a2 = 0`, the test at `0x800016d0`. -/
theorem rt_quit_stay {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {t : String} {R : Nat → BitVec 64} {M : Mem} {u td : Nat}
    (hG : ∀ a, DcGlob a → S a) (hu : ldv .lw M unwindAddr = BitVec.ofNat 64 u)
    (h24 : R 24 = BitVec.ofNat 64 td) (hlt : u < td) (htd : td < 2 ^ 31)
    (hk : ∀ R2, Keeps [8, 12, 15, 24] R2 R → R2 8 = R 23 → R2 12 = 0#64 →
      R2 24 = BitVec.ofNat 64 (td - u) → DWO live S Q t 0x800016d0#64 R2 M) :
    DWO live S Q t 0x800016b8#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have ti1 : (BitVec.ofNat 64 td).toInt = td := toInt_ofNat_small (by omega)
  have ti2 : (BitVec.ofNat 64 u).toInt = u := toInt_ofNat_small (by omega)
  have hsw := subw_ofNat (Nat.le_of_lt hlt) htd
  bc_run hlive hlive [hu, h24, ti1, ti2] at 0x8000190c 0x800016c4
  all_goals first | (intro hc; exfalso; omega) | intro _
  bc_run hlive hlive [hu, h24, hsw] at 0x800016d0
  exact hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp []) (by bsimp [])

end Dc.Mach
