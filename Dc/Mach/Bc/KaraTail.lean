import Dc.Mach.Bc.KaraFreeSites
import Dc.Mach.Bc.KaraState
import Dc.Mach.Bc.RecMul

/-!
# `_bc_rec_mul`'s Karatsuba step: the frees and the return

- `KAt`: the state inside the step (`RmAt` and the words of `s3`, `s7`–`s11`
  saved at `0x80004db0`).
- `KProd`: the product's facts.
- `kara_frees`: the nine inlined frees from `0x800051c4`, the restores at
  `0x8000535c` and the epilogue.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- Inside the Karatsuba step: `RmAt`, and `s3`, `s7`–`s11` saved. -/
structure KAt (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp q W : Nat) : Prop where
  rm : RmAt S M0 M R0 R sp q W
  saved2 : SavedWords M (sp - 192) rmSlots2 R0

/-- The product's facts (`RmPost` but its heap, slot and frame). -/
structure KProd (u v : NumRep) (ulen vlen : Nat) (y : NumObj) : Prop where
  owns : y.Owns
  refs : y.rep.refs = 1
  neg : y.rep.neg = false
  /-- `n_value` is `n_ptr` -/
  vptr : y.rep.val = y.rep.ptr
  len : y.rep.len = ulen + vlen + 1
  scale : y.rep.scale = 0
  val : dvalBE y.rep.ds = dvalBE (u.ds.take ulen) * dvalBE (v.ds.take vlen)

/-- A pointer slot of the frame (`o` from the lowered `sp`). -/
theorem RmCtx.kslot {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp q W : Nat}
    (cx : RmCtx S R0 sp q W) (o : Nat) (ho : o + 8 ≤ 192 := by decide)
    (ha : o % 8 = 0 := by decide) :
    KSlot S (slotBytes (sp - 192 + o)) (sp - 192 + o) := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big; have hab := cx.above; simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  exact ⟨frame_acc hsf (by omega) (by omega),
    fun a h1 h2 => by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega,
    fun a h1 h2 => ⟨h1, h2⟩, by omega, by omega, by omega⟩

/-- A word off the heap and off `fr` survives `OutFrame`. -/
theorem OutFrame.ldv {fr : Nat → Prop} {M' M : Mem} (h : OutFrame fr M' M) {a : Nat}
    (ho : ∀ j, j < 8 → OutHeap (a + j)) (hf : ∀ j, j < 8 → ¬ fr (a + j)) :
    ldv .ld M' a = ldv .ld M a :=
  ldv_congr .ld fun j hj => h _ (ho j hj) (hf j hj)

end Dc.Mach

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- The restores at `0x8000535c` and the epilogue. -/
theorem kara_ret {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {u v : NumRep} {y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 L u v la lb q sp W)
    (st : KAt S M0 M R0 R sp q W) (hb : BcHeap S M H F (y :: L)) (hy : KProd u v la lb y)
    (hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay) :
    DW live S Q 0x8000535c#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have e19 := st.saved2.get 19 152
  have e23 := st.saved2.get 23 120
  have e24 := st.saved2.get 24 112
  have e25 := st.saved2.get 25 104
  have e26 := st.saved2.get 26 96
  have e27 := st.saved2.get 27 88
  have h2 := st.rm.r2
  bc_run hlive hS [h2, e19, e23, e24, e25, e26, e27] at 0x80004d84
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  exact rm_epi hlive cx hk (st.rm.keeps (by keeps_tac Keeps.refl _ _) (by bsimp []))
    (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
    ⟨hb, hy.owns, hy.refs, hy.neg, hy.vptr, hy.len, hy.scale, hy.val, hq, st.rm.out⟩

/-- **The nine inlined frees** from `0x800051c4` (`u1`, `u0`, `v1`, `m1`, `v0`,
`m2`, `m3`, `d1`, `d2`), then the return. -/
theorem kara_frees {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {A B : List NumObj} {z : NumObj}
    {u v : NumRep} {y : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (hk : RmK live S Q R0 M0 (A ++ z :: B) u v la lb q sp W)
    (st : KAt S M0 M R0 R sp q W) {hu1 hu0 hv1 hm1 hv0 hm2 hm3 hd1 hd2 : Hd}
    (hb : BcHeap S M H F (KList [y] [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2] A B z))
    (hok : HdOK [hu1, hu0, hv1, hm1, hv0, hm2, hm3, hd1, hd2]) (hz : 1 ≤ z.rep.refs)
    (hy : KProd u v la lb y) (hq : ldv .ld M q = BitVec.ofNat 64 y.sb.pay)
    (r24 : R 24 = BitVec.ofNat 64 (Hd.p z hu1)) (r19 : R 19 = BitVec.ofNat 64 (Hd.p z hu0))
    (r27 : R 27 = BitVec.ofNat 64 (Hd.p z hv1)) (r20 : R 20 = BitVec.ofNat 64 (Hd.p z hv0))
    (r21 : R 21 = BitVec.ofNat 64 (Hd.p z hd1)) (r23 : R 23 = BitVec.ofNat 64 (Hd.p z hd2))
    (r25 : R 25 = BitVec.ofNat 64 bcFreeAddr)
    (s40 : ldv .ld M (sp - 192 + 40) = BitVec.ofNat 64 (Hd.p z hm1))
    (s48 : ldv .ld M (sp - 192 + 48) = BitVec.ofNat 64 (Hd.p z hm2))
    (s56 : ldv .ld M (sp - 192 + 56) = BitVec.ofNat 64 (Hd.p z hm3)) :
    DW live S Q 0x800051c4#64 R M := by
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big
  have hP : ∀ x ∈ [y], x.Owns := fun x hx => by
    rw [List.mem_singleton.mp hx]; exact hy.owns
  have k40 := cx.kslot 40; have k48 := cx.kslot 48; have k56 := cx.kslot 56
  have h2 := st.rm.r2
  -- `u1`, `u0`, `v1`
  refine kfreeH (ksite_800051c4 (fr := fun _ => False) hlive) hb hP hok.head hz
    ⟨by rw [Hd.obj_p]; exact r24, r25⟩ fun R1 M1 H1 F1 k1 hb1 o1 => ?_
  have ok1 := hok.tail
  refine kfreeH (ksite_800051ec (fr := fun _ => False) hlive) hb1 hP ok1.head hz
    ⟨by rw [Hd.obj_p, k1.get 19]; exact r19, by rw [k1.get 25]; exact r25⟩
    fun R2 M2 H2 F2 k2 hb2 o2 => ?_
  have ok2 := ok1.tail
  have k21 := k2.trans k1
  refine kfreeH (ksite_80005214 (fr := fun _ => False) hlive) hb2 hP ok2.head hz
    ⟨by rw [Hd.obj_p, k21.get 27]; exact r27, by rw [k21.get 25]; exact r25⟩
    fun R3 M3 H3 F3 k3 hb3 o3 => ?_
  have ok3 := ok2.tail
  have k31 := k3.trans k21
  -- `m1`
  refine kfreeH (ksite_8000523c hlive (sp - 192)) hb3 hP ok3.head hz
    ⟨by rw [k31.get 25]; exact r25, by rw [k31.get 2]; exact h2, k40, by
      rw [Hd.obj_p, o3.ldv (fun j hj => k40.out _ (by omega) (by omega)) (fun _ _ h => h),
        o2.ldv (fun j hj => k40.out _ (by omega) (by omega)) (fun _ _ h => h),
        o1.ldv (fun j hj => k40.out _ (by omega) (by omega)) (fun _ _ h => h)]
      exact s40⟩
    fun R4 M4 H4 F4 k4 hb4 o4 => ?_
  have ok4 := ok3.tail
  have k41 := k4.trans k31
  -- `v0`
  refine kfreeH (ksite_80005274 (fr := fun _ => False) hlive) hb4 hP ok4.head hz
    ⟨by rw [Hd.obj_p, k41.get 20]; exact r20, by rw [k41.get 25]; exact r25⟩
    fun R5 M5 H5 F5 k5 hb5 o5 => ?_
  have ok5 := ok4.tail
  have k51 := k5.trans k41
  -- `m2`, `m3`
  have n40 : ∀ c, 48 ≤ c → ∀ j, j < 8 → ¬ slotBytes (sp - 192 + 40) (sp - 192 + c + j) :=
    fun c hc j _ h => by simp only [slotBytes] at h; omega
  refine kfreeH (ksite_8000529c hlive (sp - 192)) hb5 hP ok5.head hz
    ⟨by rw [k51.get 25]; exact r25, by rw [k51.get 2]; exact h2, k48, by
      rw [Hd.obj_p, o5.ldv (fun j hj => k48.out _ (by omega) (by omega)) (fun _ _ h => h),
        o4.ldv (fun j hj => k48.out _ (by omega) (by omega)) (n40 48 (by omega)),
        o3.ldv (fun j hj => k48.out _ (by omega) (by omega)) (fun _ _ h => h),
        o2.ldv (fun j hj => k48.out _ (by omega) (by omega)) (fun _ _ h => h),
        o1.ldv (fun j hj => k48.out _ (by omega) (by omega)) (fun _ _ h => h)]
      exact s48⟩
    fun R6 M6 H6 F6 k6 hb6 o6 => ?_
  have ok6 := ok5.tail
  have k61 := k6.trans k51
  have n48 : ∀ j, j < 8 → ¬ slotBytes (sp - 192 + 48) (sp - 192 + 56 + j) :=
    fun j _ h => by simp only [slotBytes] at h; omega
  refine kfreeH (ksite_800052d4 hlive (sp - 192)) hb6 hP ok6.head hz
    ⟨by rw [k61.get 25]; exact r25, by rw [k61.get 2]; exact h2, k56, by
      rw [Hd.obj_p, o6.ldv (fun j hj => k56.out _ (by omega) (by omega)) n48,
        o5.ldv (fun j hj => k56.out _ (by omega) (by omega)) (fun _ _ h => h),
        o4.ldv (fun j hj => k56.out _ (by omega) (by omega)) (n40 56 (by omega)),
        o3.ldv (fun j hj => k56.out _ (by omega) (by omega)) (fun _ _ h => h),
        o2.ldv (fun j hj => k56.out _ (by omega) (by omega)) (fun _ _ h => h),
        o1.ldv (fun j hj => k56.out _ (by omega) (by omega)) (fun _ _ h => h)]
      exact s56⟩
    fun R7 M7 H7 F7 k7 hb7 o7 => ?_
  have ok7 := ok6.tail
  have k71 := k7.trans k61
  -- `d1`, `d2`
  refine kfreeH (ksite_8000530c (fr := fun _ => False) hlive) hb7 hP ok7.head hz
    ⟨by rw [Hd.obj_p, k71.get 21]; exact r21, by rw [k71.get 25]; exact r25⟩
    fun R8 M8 H8 F8 k8 hb8 o8 => ?_
  have ok8 := ok7.tail
  have k81 := k8.trans k71
  refine kfreeH (ksite_80005334 (fr := fun _ => False) hlive) hb8 hP ok8.head hz
    ⟨by rw [Hd.obj_p, k81.get 23]; exact r23, by rw [k81.get 25]; exact r25⟩
    fun R9 M9 H9 F9 k9 hb9 o9 => ?_
  have k91 := k9.trans k81
  rw [KList_nil] at hb9
  -- the frame: off the heap, only the three slots changed
  have hag : ∀ a, OutHeap a → ¬ slotBytes (sp - 192 + 40) a → ¬ slotBytes (sp - 192 + 48) a →
      ¬ slotBytes (sp - 192 + 56) a → imgM M9 a = imgM M a := fun a ha h1 h2 h3 => by
    rw [o9 a ha id, o8 a ha id, o7 a ha h3, o6 a ha h2, o5 a ha id, o4 a ha h1, o3 a ha id,
      o2 a ha id, o1 a ha id]
  have hfr : ∀ a, sp - 192 + 88 ≤ a → a < sp → imgM M9 a = imgM M a := fun a h1 h2 =>
    hag a (by
      have hab := cx.above
      simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at hab ⊢; omega)
      (by simp only [slotBytes]; omega) (by simp only [slotBytes]; omega)
      (by simp only [slotBytes]; omega)
  have st9 : KAt S M0 M9 R0 R9 sp q W :=
    ⟨(st.rm.mem (st.rm.saved.transport (lo := 128) (top := 192) (hag := fun a h1 h2 => hfr a (by omega)
        (by omega))) fun a ha hs hf => hag a ha
          (fun h => hf (by simp only [slotBytes, frameIn] at h ⊢; omega))
          (fun h => hf (by simp only [slotBytes, frameIn] at h ⊢; omega))
          (fun h => hf (by simp only [slotBytes, frameIn] at h ⊢; omega))).keeps
        (k91.mono (by decide)) (k91.get 2),
      st.saved2.transport (lo := 88) (top := 160) (hag := fun a h1 h2 => hfr a h1 (by omega))⟩
  have hqo := cx.slotApart
  exact kara_ret hlive cx hk st9 hb9 hy (by
    rw [OutFrame.ldv (fr := fun a => slotBytes (sp - 192 + 40) a ∨ slotBytes (sp - 192 + 48) a ∨
        slotBytes (sp - 192 + 56) a)
      (fun a ha hn => hag a ha (fun h => hn (.inl h)) (fun h => hn (.inr (.inl h)))
        (fun h => hn (.inr (.inr h))))
      (fun j hj => cx.slotOut _ ⟨by omega, by omega⟩)
      (fun j hj h => by simp only [slotBytes] at h; omega)]
    exact hq)

end Dc.Mach
