import Dc.Mach.EvalRoute

/-!
# `evalstr`'s loop test (M10)

Every status route ends in `bltu s0, s1, 0x800014f8; j 0x8000156c` (at one
of nine places, `BltuAt`): the loop head for a nonempty rest of the string,
the exit otherwise. `ev_join` decides the test from `EvAt.pos`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **The loop test at `p`**: `bltu s0, s1, 0x800014f8` then `j 0x8000156c`. -/
def BltuAt (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (p : Nat) : Prop :=
  ∀ t R M, ((R 8).toNat < (R 9).toNat → DWO live S Q t 0x800014f8#64 R M) →
    (¬ (R 8).toNat < (R 9).toNat → DWO live S Q t 0x8000156c#64 R M) →
    DWO live S Q t (BitVec.ofNat 64 p) R M

set_option hygiene false in
/-- A loop test from its two generated steps. -/
macro "bltu_at " p:ident j:ident : term =>
  `(fun t R M k1 k2 => $p hlive k1 fun h => $j hlive (k2 h))

theorem bltu_800015a0 {live S Q} (hlive : ∀ p ∈ dcText, live p.1) : BltuAt live S Q 0x800015a0 :=
  bltu_at st_800015a0 st_800015a4
theorem bltu_800015c4 {live S Q} (hlive : ∀ p ∈ dcText, live p.1) : BltuAt live S Q 0x800015c4 :=
  bltu_at st_800015c4 st_800015c8
theorem bltu_800015dc {live S Q} (hlive : ∀ p ∈ dcText, live p.1) : BltuAt live S Q 0x800015dc :=
  bltu_at st_800015dc st_800015e0
theorem bltu_80001660 {live S Q} (hlive : ∀ p ∈ dcText, live p.1) : BltuAt live S Q 0x80001660 :=
  bltu_at st_80001660 st_80001664
theorem bltu_800016b0 {live S Q} (hlive : ∀ p ∈ dcText, live p.1) : BltuAt live S Q 0x800016b0 :=
  bltu_at st_800016b0 st_800016b4
theorem bltu_800016d0 {live S Q} (hlive : ∀ p ∈ dcText, live p.1) : BltuAt live S Q 0x800016d0 :=
  bltu_at st_800016d0 st_800016d4
theorem bltu_80001718 {live S Q} (hlive : ∀ p ∈ dcText, live p.1) : BltuAt live S Q 0x80001718 :=
  bltu_at st_80001718 st_8000171c
theorem bltu_800017d0 {live S Q} (hlive : ∀ p ∈ dcText, live p.1) : BltuAt live S Q 0x800017d0 :=
  bltu_at st_800017d0 st_800017d4
theorem bltu_800018f0 {live S Q} (hlive : ∀ p ∈ dcText, live p.1) : BltuAt live S Q 0x800018f0 :=
  bltu_at st_800018f0 st_800018f4

/-- **The loop test decided**: the head for a nonempty rest, the exit for
the empty one. -/
theorem ev_join {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {p : Nat} (hb : BltuAt live S Q p) {t : String} {sp W d k q : Nat} {M0 : Mem}
    {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
    {G : DcG} {hs xs : List GV} {st : St} {f : Frame} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o)
    (hhead : f.s ≠ [] → DWO live S Q t 0x800014f8#64 R M)
    (hdone : f.s = [] → DWO live S Q t 0x8000156c#64 R M) :
    DWO live S Q t (BitVec.ofNat 64 p) R M := by
  obtain ⟨j, hj, hdrop, h8⟩ := ev.pos
  have h9 := ev.s1
  have hso := ev.dc.view.strs o ev.strIn
  have bt := blk_bounds ev.dc.heap.heap (ev.dc.heap.raw.live o.tb
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ev.strIn, by simp⟩))))
  have htz := hso.tsz
  simp only [heapStart, heapEnd] at bt
  have e8 : (R 8).toNat = o.tb.pay + j := by rw [h8, BitVec.toNat_ofNat]; omega
  have e9 : (R 9).toNat = o.tb.pay + o.s.length := by rw [h9, BitVec.toNat_ofNat]; omega
  have hl : (o.s.drop j).length = o.s.length - j := List.length_drop
  refine hb t R M (fun hlt => hhead fun he => ?_) fun hge => hdone ?_
  · rw [hdrop, he] at hl; simp at hl; omega
  · rw [← hdrop]; apply List.eq_nil_of_length_eq_zero; omega

end Dc.Mach
