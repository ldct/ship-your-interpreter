import Dc.Mach.Bc.RaiseSquare

/-!
# `bc_raise` from its entry (`0x8000660c`)

    660c warn on num2's scale; exponent = bc_num2long (num2)
    681c exponent 0: error for a nonzero integer part; result = _one_
    6648 rscale = MIN (scale1 · exponent, MAX (scale, scale1)) (positive) or
         scale (negative, the exponent negated); the loops (`ra_loops`)
    6740 / 68cc the result from `temp` (`ra_end2`) or from `power` (`ra_endPow2`)

- `RaSlot.transport`: the result slot through the frame's writes.
- `RaMode`: the sign flag `s8` and `rscale` against `Num.raise`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The result slot through writes off the heap's complement and the frame. -/
theorem RaSlot.transport {S : Nat → Prop} {R0 : Nat → BitVec 64} {Mt0 M : Mem} {sp W q : Nat}
    {L : List NumObj} {x1 x2 z o xr : NumObj} (cx : RaCtx S R0 sp W q)
    (hs : RaSlot Mt0 L x1 x2 z o xr q)
    (hag : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) :
    RaSlot M L x1 x2 z o xr q :=
  { hs with
    wr := by
      rw [ldv_congr .ld fun j hj => hag _ (cx.slot.out _ (by simp only [widthOfM] at hj; omega))
        (by have := cx.slot.apart; simp only [frameIn, widthOfM] at hj ⊢; omega)]
      exact hs.wr }

/-- `bc_raise`'s sign flag `s8` and `rscale` for the exponent `raExp x2`
(nonzero, magnitude `u`). -/
structure RaMode (x1 x2 : NumObj) (k u rs nf : Nat) : Prop where
  abs : u = (raExp x2).natAbs
  cases : (nf = 0 ∧ 0 < raExp x2 ∧ rs = min (x1.rep.scale * u) (max k x1.rep.scale)) ∨
    (nf = 1 ∧ raExp x2 < 0 ∧ rs = k)

/-- `_one_` has one integer digit and no fraction. -/
theorem one_size {o : NumRep} (hs : NumShape o) (hn : o.Norm) (h1 : o.num = Num.one) :
    o.len + o.scale ≤ 1 := by
  have hsc : o.scale = 0 := by rw [← NumRep.num_scale, h1]; rfl
  have := NumRep.size_le hs hn (E := 1) (by rw [h1]; decide)
  omega

/-- **The result from `temp`** at `0x80006740`: the second loop's exit. -/
theorem ra_end2 {live : Nat → Prop} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q k u rs nf P : Nat} {H : Heap} {F : List Blk}
    {A B : List NumObj} {x1 x2 z o xr Pw T : NumObj}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u)
    (hK : RaK live S Q t R0 Mt0 (A ++ x1 :: B) xr q sp W (Num.raise x1.rep.num x2.rep.num k).1)
    (ha : RaArgs S Mt0 (A ++ x1 :: B) x1 x2 z o k) (hs0 : RaSlot Mt0 (A ++ x1 :: B) x1 x2 z o xr q)
    (hm : RaMode x1 x2 k u rs nf)
    (st : RaP2 S Mt0 M R0 R sp W q H F A B x1 Pw (some T) P u 0 rs nf) :
    DW live S (DQ live S Q t) 0x80006740#64 R M := by
  have cx := env.cx
  ra_facts cx
  have hsf := cx.frame
  have hb0 := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb0.heap.own a h1 h2
  have hb : BcHeap S M H F (T :: Pw :: (A ++ x1 :: B)) := by
    have := hb0.kperm (List.Perm.swap (some T) (some Pw) []) (fun _ h => nomatch h) (fun x hx => by
      rcases List.mem_cons.mp hx with h | h
      · cases h; exact .inl st.tm.owns
      · rw [List.mem_singleton] at h; cases h; exact .inl st.pw.owns)
    simpa [KList, zeroCount, temps, NumObj.withRefs_self] using this
  have hs := hs0.transport cx st.ra.out
  have hTn : T.rep.num = Num.powRaise x1.rep.num u := st.tm.num
  have hTs : T.rep.scale = x1.rep.scale * u := by
    rw [← NumRep.num_scale, hTn, Dc.BcModel.powRaise_scale, NumRep.num_scale]
  have hk24 : k < 2 ^ 24 := by have := ha.size; omega
  have hx1sz := (hb.nums x1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha.m1))).shape.size
  rcases hm.cases with ⟨rfl, hpos, hrs⟩ | ⟨rfl, hneg, hrs⟩
  · bc_run hlive hS [st.r24] at 0x8000688c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine ra_pos2 hlive cx hK hs ha.owns st.ra hb (st.t1 T rfl) st.pw1 st.tm.owns st.pw.owns
      st.tm.norm st.tm.len (by rw [hTs, hrs]; omega) (by rw [hrs]; omega) ?_ st.r20 st.r22 st.w8
    have hne : ¬ (raExp x2 == 0) = true := by simp; omega
    have hlt : ¬ (raExp x2 < 0) := by omega
    simp only [Num.raise, raExp] at hne hlt ⊢
    rw [if_neg hne, if_neg hlt, ← hm.abs, ← hTn, NumRep.num_neg, NumRep.num_mag, NumRep.num_scale,
      hTs, hrs]
    rfl
  · bc_run hlive hS [st.r24] at 0x80006744
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hom := ha.mo
    have hos := one_size (hb.nums o (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hom))).shape
      ha.oneNorm ha.oneNum
    have hTm : T ∈ T :: Pw :: (A ++ x1 :: B) := List.mem_cons_self
    have hx1m : x1 ∈ T :: Pw :: (A ++ x1 :: B) :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha.m1)
    have hTz : T.rep.len + T.rep.scale ≤ u * (x1.rep.len + x1.rep.scale) + 1 :=
      st.tm.size (hb.nums T hTm).shape (hb.nums x1 hx1m).shape rfl (by have := env.u1; omega)
    have hLu : u * (x1.rep.len + x1.rep.scale) < 2 ^ 24 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_succ _))
        (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ u)) env.size)
    refine ra_neg2 hlive cx hK ha hs st.ra hb (st.t1 T rfl) st.pw1 st.tm.owns st.pw.owns ?_
      (by omega) ?_ st.r20 (by rw [st.r22, hrs]) st.w8
    · intro h0
      refine ⟨?_, hneg⟩
      rw [hTn, Dc.BcModel.powRaise_mag] at h0
      exact (Nat.pow_eq_zero.mp h0).1
    · have hne : ¬ (raExp x2 == 0) = true := by simp; omega
      simp only [Num.raise, raExp] at hne hneg ⊢
      rw [if_neg hne, if_pos hneg, ← hm.abs, ← hTn]

end Dc.Mach
