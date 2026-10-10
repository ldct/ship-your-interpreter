import Dc.Mach.Bc.OutNumPop

/-! # `bc_out_num` in a base other than 10: the exit

From `0x80007320` (`int_part` in `s0`) the five numbers are freed by the
generated sites (`ffree_80007320` … `ffree_800073f0`), `s8`–`s11` are
reloaded and the epilogue returns with the caller's heap.

- `SlotWords.drop`: a handle's word dropped.
- `OgSt.freeSlot`: the state's inputs to a generated free site, and the state
  after it.
- `OgK7`/`og_exit`: from `0x80007320`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The words of the handles other than `h`. -/
theorem SlotWords.drop {M : Mem} {b : Nat} {h : RH} {o : Nat} {hs2 : List RH} {os2 : List Nat} :
    ∀ {hs1 : List RH} {os1 : List Nat}, hs1.length = os1.length →
      SlotWords M b (hs1 ++ h :: hs2) (os1 ++ o :: os2) → SlotWords M b (hs1 ++ hs2) (os1 ++ os2)
  | [], [], _, ⟨_, h2⟩ => h2
  | _ :: _, _ :: _, hl, ⟨h1, h2⟩ => ⟨h1, SlotWords.drop (Nat.succ.inj hl) h2⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **A handle freed** at a generated site: the site's inputs (the handle's
number `x` in the heap), and the state after any route of it, with the
handle and its word dropped. -/
theorem OgSt.freeSlot {live S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {hs1 hs2 : List RH} {h : RH}
    {os1 os2 : List Nat} {o : Nat} {sent : List Nat} {t : String} {P : Prop}
    (st : OgSt S X G I Mt0 M R0 R sp W H F L (hs1 ++ h :: hs2) (os1 ++ o :: os2) sent t)
    (cx : OnCtx S R0 sp W d) (cb : CharFn live S Q (R0 12) d G I)
    (hl : hs1.length = os1.length) (hok : RHOK L h)
    (k : ∀ L1 L2 x, BcHeap S X M H F (L1 ++ x :: L2) → 1 ≤ x.rep.refs →
      (x.rep.refs = 1 → x.Owns → ∀ y ∈ L1, y.db ≠ x.db) → x.rep.p = h.p →
      (∀ (R' : Nat → BitVec 64) M' H' F' L' (cl : List Nat), Keeps cl R' R →
        (∀ z ∈ cl, z ∈ onAll ∧ z ≠ 2 ∧ z ≠ 9) → KFreed H F L1 L2 x H' F' L' →
        BcHeap S X M' H' F' L' → OutFrame (fun _ => False) M' M →
        OgSt S X G I Mt0 M' R0 R' sp W H' F' L (hs1 ++ hs2) (os1 ++ os2) sent t) → P) : P := by
  obtain ⟨L1, L2, x, e, hp, hr, hnv, _, _, hfr⟩ := RList.slot st.heap hok st.own
  have hb' : BcHeap S X M H F (L1 ++ x :: L2) := by rw [← e]; exact st.heap
  refine k L1 L2 x hb' hr hnv hp fun R' M' H' F' L' cl hk hks hkf hb1 hof => ?_
  have hL : L' = RList (hs1 ++ hs2) L := hfr L' hkf.rest
  subst hL
  have hm : ∀ a, OutHeap a → imgM M' a = imgM M a := fun a ha => hof a ha id
  on_facts cx
  have hsf := cx.cc.frame
  have hsl := hsf.lo
  have on1 : OnAt S G Mt0 M' R0 R sp W onSlots3 :=
    { st.on with
      saved := st.on.saved.transport (lo := 72) (top := 176) (by decide) (by decide)
        fun a h1 _ => hm a (outHeap_of_ge (by simp only [heapEnd]; omega))
      out := fun a ha hg hf => (hm a ha).trans (st.on.out a ha hg hf) }
  exact
    { on := on1.regs hk hks
      heap := hb1
      own := st.own.drop
      words := (st.words.transport fun o ho => by
        have := st.offs o ho
        exact ldv_congr .ld fun j hj => hm _ (outHeap_of_ge (by simp only [heapEnd]; omega))).drop hl
      offs := fun o' ho' => st.offs o' (by
        rcases List.mem_append.mp ho' with h1 | h1
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
      nd := by
        have := st.nd
        rw [List.nodup_append] at this ⊢
        exact ⟨this.1, (List.nodup_cons.mp this.2.1).2,
          fun a ha b hb => this.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩
      inv := cb.stab _ _ _ _ st.inv fun a hg => hm a (cb.off a hg).2.1 }

/-- The exit from `0x80007320`: the five numbers' handles, `int_part` in
`s0`, the characters of `x` sent. -/
def OgK7 (live S : Nat → Prop) (X0 : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x : NumObj) (ob : Nat) (cs : List Nat) : Prop :=
  ∀ (t : String) (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk)
    (ip fr bs mx : NumObj) (cur : RH),
    OgSt S X0 G I Mt0 M R0 R sp W H F L [.own ip, .own fr, cur, .own bs, .own mx]
      [16, 24, 40, 32, 56] (cs ++ Num.outChars x.rep.num ob) t →
    (∀ h ∈ [RH.own ip, .own fr, cur, .own bs, .own mx], RHOK L h) →
    R 8 = BitVec.ofNat 64 ip.rep.p → R 22 = BitVec.ofNat 64 fr.rep.p →
    R 19 = BitVec.ofNat 64 bs.rep.p → R 26 = BitVec.ofNat 64 cur.p →
    R 24 = BitVec.ofNat 64 mx.rep.p → DWO live S Q t 0x80007320#64 R M

/-- **The epilogue** with every handle freed and `s8`–`s11` the caller's. -/
theorem og_epi {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {t : String}
    {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk}
    (st : OgSt S X0 G I Mt0 M R0 R sp W H F L [] [] (cs ++ Num.outChars x.rep.num ob) t)
    (hs : ∀ z ∈ [24, 25, 26, 27], R z = R0 z) :
    DWO live S Q t 0x80007434#64 R M :=
  on_epi hlive fx.cx (fun p hp => st.on.saved p ((by decide : ∀ p ∈ onSlots2, p ∈ onSlots3) p hp))
    st.on.r2 st.on.keep hs fun R' hk' =>
      fx.hK.ret R' M t H F hk' st.inv (by rw [← RList.nil L]; exact st.heap) st.on.out

/-- From `0x800074ec` (`max_o_digit` still referenced): `s8`–`s11`
reloaded. -/
theorem og_tailD {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {t : String}
    {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk}
    (st : OgSt S X0 G I Mt0 M R0 R sp W H F L [] [] (cs ++ Num.outChars x.rep.num ob) t) :
    DWO live S Q t 0x800074ec#64 R M := by
  have cx := fx.cx
  on_facts cx
  have hsf := cx.cc.frame
  have sv := st.on.saved
  have q2 := st.on.r2
  have g24 := sv.get 24 96; have g25 := sv.get 25 88; have g26 := sv.get 26 80
  have g27 := sv.get 27 72
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  bc_run hlive hS [q2, g24, g25, g26, g27] at 0x80007434
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine og_epi hlive fx (st.regs (ks := [24, 25, 26, 27]) (by keeps_tac Keeps.refl _ _))
    fun z hz => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> bsimp [g24, g25, g26, g27]

/-- From `0x80007428` (`max_o_digit` freed, `s9` reloaded): `s8`, `s10`,
`s11` reloaded. -/
theorem og_tailO {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {t : String}
    {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk}
    (st : OgSt S X0 G I Mt0 M R0 R sp W H F L [] [] (cs ++ Num.outChars x.rep.num ob) t)
    (h25 : R 25 = R0 25) :
    DWO live S Q t 0x80007428#64 R M := by
  have cx := fx.cx
  on_facts cx
  have hsf := cx.cc.frame
  have sv := st.on.saved
  have q2 := st.on.r2
  have g24 := sv.get 24 96; have g26 := sv.get 26 80
  have g27 := sv.get 27 72
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  bc_run hlive hS [q2, g24, g26, g27] at 0x80007434
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine og_epi hlive fx (st.regs (ks := [24, 26, 27]) (by keeps_tac Keeps.refl _ _))
    fun z hz => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> bsimp [g24, h25, g26, g27]

/-- **`max_o_digit` freed** at `0x800073f0`, the last handle. -/
theorem og_exitMx {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {t : String}
    {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {mx : NumObj}
    (st : OgSt S X0 G I Mt0 M R0 R sp W H F L [.own mx] [56] (cs ++ Num.outChars x.rep.num ob) t)
    (hok : RHOK L (.own mx)) (h24 : R 24 = BitVec.ofNat 64 mx.rep.p) :
    DWO live S Q t 0x800073f0#64 R M := by
  have cx := fx.cx
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  refine st.freeSlot (hs1 := []) (os1 := []) cx cb rfl hok fun L1 L2 x5 hb hr hnv hp post => ?_
  exact ffree_800073f0 hlive hb hr hnv (by rw [hp]; exact h24) st.on.r2
    (frame_acc hsf (by omega) (by omega)) (by simp only [heapEnd]; omega) (by omega)
    (st.on.saved.get 25 88)
    (fun R5 M5 H5 F5 L5' hk5 hkf hb5 hof =>
      og_tailD hlive fx (post R5 M5 H5 F5 L5' _ hk5 (by decide) hkf hb5 hof))
    (fun R5 M5 H5 F5 L5' hk5 h25 hkf hb5 hof =>
      og_tailO hlive fx (post R5 M5 H5 F5 L5' _ hk5 (by decide) hkf hb5 hof) h25)
    (fun R5 M5 H5 F5 L5' hk5 h25 hkf hb5 hof =>
      og_tailO hlive fx (post R5 M5 H5 F5 L5' _ hk5 (by decide) hkf hb5 hof) h25)

/-- **The exit** from `0x80007320`. -/
theorem og_exit {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) :
    OgK7 live S X0 Q I G Mt0 R0 sp W L x ob cs := by
  intro t R M H F ip fr bs mx cur st hok h8 h22 h19 h26 h24
  have cx := fx.cx
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  refine st.freeSlot (hs1 := []) (os1 := []) cx cb rfl (hok _ (by simp))
    fun L1 L2 x1 hb hr hnv hp post => ?_
  have k1 : FreeK [1, 10, 14, 15] live S X0 (DQ live S Q t) 0x80007354#64 R M (fun _ => False)
      H F L1 L2 x1 := fun R1 M1 H1 F1 L1' hk1 hkf hb1 hof => by
    have st1 := post R1 M1 H1 F1 L1' _ hk1 (by decide) hkf hb1 hof
    refine st1.freeSlot (hs1 := []) (os1 := []) cx cb rfl (hok _ (by simp))
      fun L1 L2 x2 hb hr hnv hp post => ?_
    have k2 : FreeK [1, 10, 14, 15] live S X0 (DQ live S Q t) 0x80007388#64 R1 M1 (fun _ => False)
        H1 F1 L1 L2 x2 := fun R2 M2 H2 F2 L2' hk2 hkf hb2 hof => by
      have st2 := post R2 M2 H2 F2 L2' _ hk2 (by decide) hkf hb2 hof
      refine st2.freeSlot (hs1 := [cur]) (os1 := [40]) cx cb rfl (hok _ (by simp))
        fun L1 L2 x3 hb hr hnv hp post => ?_
      have k3 : FreeK [1, 10, 14, 15] live S X0 (DQ live S Q t) 0x800073bc#64 R2 M2
          (fun _ => False) H2 F2 L1 L2 x3 := fun R3 M3 H3 F3 L3' hk3 hkf hb3 hof => by
        have st3 := post R3 M3 H3 F3 L3' _ hk3 (by decide) hkf hb3 hof
        refine st3.freeSlot (hs1 := []) (os1 := []) cx cb rfl (hok _ (by simp))
          fun L1 L2 x4 hb hr hnv hp post => ?_
        have k4 : FreeK [1, 10, 14, 15] live S X0 (DQ live S Q t) 0x800073f0#64 R3 M3
            (fun _ => False) H3 F3 L1 L2 x4 := fun R4 M4 H4 F4 L4' hk4 hkf hb4 hof => by
          have st4 := post R4 M4 H4 F4 L4' _ hk4 (by decide) hkf hb4 hof
          exact og_exitMx hlive fx st4 (hok _ (by simp))
            (by rw [hk4.get 24 (by decide), hk3.get 24 (by decide), hk2.get 24 (by decide),
                  hk1.get 24 (by decide)]
                exact h24)
        exact ffree_800073bc hlive hb hr hnv
          (by rw [hp, hk3.get 26 (by decide), hk2.get 26 (by decide), hk1.get 26 (by decide)]
              exact h26) k4 k4 k4
      exact ffree_80007388 hlive hb hr hnv
        (by rw [hp, hk2.get 19 (by decide), hk1.get 19 (by decide)]; exact h19) k3 k3 k3
    exact ffree_80007354 hlive hb hr hnv (by rw [hp, hk1.get 22 (by decide)]; exact h22) k2 k2 k2
  exact ffree_80007320 hlive hb hr hnv (by rw [hp]; exact h8) k1 k1 k1

end Dc.Mach
