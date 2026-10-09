import Dc.Mach.Bc.OutNumExit

/-! # `bc_out_num` in a base other than 10: the fraction digits

-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel (FracInv FracFuel)

set_option linter.unusedSimpArgs false

/-- The characters of the fraction digit `d` at index `i`: a space before
every long digit but the first. -/
abbrev ogDigF (ob d i : Nat) : List Nat :=
  if ob ≤ 16 then [Num.hexChar d] else Num.outLong d (Num.decText (ob - 1)).length (i != 0)

/-- The fraction digits' characters from the index `i`. -/
def ogFracOut (ob s fuel : Nat) (f : Num) (t i : Nat) : List Nat :=
  ((Num.fracDigits ob s fuel f t).zipIdx i).flatMap fun p => ogDigF ob p.1 p.2

/-- The fraction part: the magnitude below one, positive. -/
theorem frac_part (n : Num) : ogFrac n = ⟨false, n.mag % 10 ^ n.scale, n.scale⟩ := by
  obtain ⟨neg, m, s⟩ := n
  have hp : 0 < 10 ^ s := Nat.pow_pos (by decide)
  have hdm := Nat.div_add_mod m (10 ^ s)
  simp only [ogFrac, ogIp, Num.div, Num.one, Nat.one_ne_zero, beq_iff_eq, ite_false, Option.getD_some,
    Nat.zero_add, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Num.sub, Num.align, Nat.max_zero,
    Nat.zero_max, Nat.max_self, Nat.sub_zero, Nat.sub_self]
  have hr : m % 10 ^ s < 10 ^ s := Nat.mod_lt _ hp
  generalize m / 10 ^ s = q at hdm ⊢
  generalize m % 10 ^ s = r at hdm hr ⊢
  generalize 10 ^ s = P at hdm hp hr ⊢
  have hcmp : ∀ (A B : Nat), B ≤ A → (compare A B = .gt ∧ B < A) ∨ (compare A B = .eq ∧ A = B) :=
    fun A B h => by
      rcases Nat.lt_or_ge B A with h' | h'
      · exact .inl ⟨Nat.compare_eq_gt.mpr h', h'⟩
      · exact .inr ⟨Nat.compare_eq_eq.mpr (by omega), by omega⟩
  have hqP : q * P ≤ m := by rw [Nat.mul_comm]; omega
  by_cases hq : q = 0
  · subst hq
    cases neg
    · rcases hcmp m 0 (Nat.zero_le _) with ⟨e, h⟩ | ⟨e, h⟩ <;> simp [e, Num.zero] <;> omega
    · simp; omega
  · cases neg <;>
    · rcases hcmp m (q * P) hqP with ⟨e, h⟩ | ⟨e, h⟩ <;> simp [hq, e, Num.zero] <;>
        rw [Nat.mul_comm] at hdm <;> omega

/-- The whole target split at the fraction loop. -/
theorem og_target {x : NumObj} {ob : Nat} {cs : List Nat} (hm : x.rep.num.mag ≠ 0) (hb : ob ≠ 10) :
    cs ++ Num.outChars x.rep.num ob =
      ogIntOut x ob cs ++ (if x.rep.num.scale == 0 then []
        else 46 :: ogFracOut ob x.rep.num.scale (4 * x.rep.num.scale + 4) (ogFrac x.rep.num) 1 0) := by
  have hz : x.rep.num.isZero = false := by simp [Num.isZero, hm]
  rw [Dc.BcModel.outChars_base hz hb]
  simp only [ogIntOut, ogFracOut, ogDigI, ogDigF, signOut, ogFrac, ogIp, List.append_assoc]

/-- One fraction digit. -/
theorem ogFracOut_step {ob s fuel t i : Nat} {f : Num} (h : FracInv f s) (ht0 : t ≠ 0)
    (ht : t < 10 ^ s) (hb0 : 0 < ob) (hb : ob < 2 ^ 31) :
    ogFracOut ob s (fuel + 1) f t i =
      ogDigF ob (f.mag * ob / 10 ^ s) i ++
        ogFracOut ob s fuel ⟨false, f.mag * ob % 10 ^ s, s⟩ (t * ob) (i + 1) := by
  unfold ogFracOut
  rw [Dc.BcModel.fracDigits_unfold ht0 ht, Dc.BcModel.fracStep_mul h,
    (Dc.BcModel.fracStep_digit h hb0 hb).1, Int.natAbs_natCast, Dc.BcModel.fracStep_sub]
  simp [List.zipIdx_cons]

/-- No more fraction digits. -/
theorem ogFracOut_stop {ob s fuel t i : Nat} {f : Num} (ht0 : t ≠ 0) (ht : 10 ^ s ≤ t) :
    ogFracOut ob s fuel f t i = [] := by
  unfold ogFracOut; rw [Dc.BcModel.fracDigits_stop ht0 ht]; rfl

/-- A product of integers at scale 0. -/
theorem mul_int (a b : Nat) : Num.mul ⟨false, a, 0⟩ ⟨false, b, 0⟩ 0 = ⟨false, a * b, 0⟩ := by
  simp only [Num.mul, Nat.add_zero, Nat.max_self, Nat.min_self, Nat.sub_self, Nat.pow_zero,
    Nat.div_one, bne_self_eq_false]
  congr 1
  split <;> rfl

/-- The registers the fraction loop keeps: `s2` the number, `s3` `base`,
`s5` `ref_str`, `s7` the base, `s8` `max_o_digit`, `s9` 16, `s10`
`cur_dig`. -/
structure OgFrRegs (R : Nat → BitVec 64) (x : NumObj) (ob : Nat) (bs mx : NumObj) (cur : RH) :
    Prop where
  r18 : R 18 = BitVec.ofNat 64 x.rep.p
  r19 : R 19 = BitVec.ofNat 64 bs.rep.p
  r21 : R 21 = 0x800081e8#64
  r23 : R 23 = BitVec.ofNat 64 ob
  r24 : R 24 = BitVec.ofNat 64 mx.rep.p
  r25 : R 25 = 16#64
  r26 : R 26 = BitVec.ofNat 64 cur.p

theorem OgFrRegs.keep {R R' : Nat → BitVec 64} {x : NumObj} {ob : Nat} {bs mx : NumObj}
    {cur : RH} (h : OgFrRegs R x ob bs mx cur) {ks : List Nat} (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∉ [18, 19, 21, 23, 24, 25, 26] := by decide) :
    OgFrRegs R' x ob bs mx cur :=
  ⟨by rw [hk.get 18 fun h => hks 18 h (by decide)]; exact h.r18,
    by rw [hk.get 19 fun h => hks 19 h (by decide)]; exact h.r19,
    by rw [hk.get 21 fun h => hks 21 h (by decide)]; exact h.r21,
    by rw [hk.get 23 fun h => hks 23 h (by decide)]; exact h.r23,
    by rw [hk.get 24 fun h => hks 24 h (by decide)]; exact h.r24,
    by rw [hk.get 25 fun h => hks 25 h (by decide)]; exact h.r25,
    by rw [hk.get 26 fun h => hks 26 h (by decide)]; exact h.r26⟩

/-- **The fraction loop's head** (`0x80007290`): the six handles (`t_num`
last, at `48`), `frac_part` `f` below one, `t_num = tv` with `tv < 10 ^ scale`,
the characters still to send those of the digits from `f`, `pre_space` the
index's flag. -/
structure OgFH (S : Nat → Prop) (X0 : Raws) (G : Nat → Prop) (I : List Nat → String → Mem → Prop)
    (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat) (H : Heap) (F : List Blk)
    (L : List NumObj) (x : NumObj) (ob : Nat) (cs sent : List Nat) (t : String)
    (ip fr bs mx : NumObj) (cur tn : RH) (f : Num) (tv fuel i : Nat) : Prop where
  st : OgSt S X0 G I Mt0 M R0 R sp W H F L [.own ip, .own fr, cur, .own bs, .own mx, tn]
    [16, 24, 40, 32, 56, 48] sent t
  ipOK : RHOK L (.own ip)
  curOK : RHOK L cur
  tnOK : RHOK L tn
  frn : NewNum f fr
  fi : FracInv f x.rep.scale
  tnv : tn.base.rep.num = ⟨false, tv, 0⟩
  tnN : tn.base.rep.Norm
  tnP : 1 ≤ tn.base.rep.len
  tv0 : tv ≠ 0
  tlt : tv < 10 ^ x.rep.scale
  fl : FracFuel x.rep.scale tv fuel
  tgt : sent ++ ogFracOut ob x.rep.scale fuel f tv i = cs ++ Num.outChars x.rep.num ob
  sp8 : ¬ ob ≤ 16 → ldv .ld M (sp - 176 + 8) = boolWord (i != 0)
  regs : OgFrRegs R x ob bs mx cur
  r13 : R 13 = BitVec.ofNat 64 x.rep.scale
  r20 : R 20 = BitVec.ofNat 64 tn.p
  r22 : R 22 = BitVec.ofNat 64 fr.rep.p

/-- **After a digit** (`0x80007268`): `t_num` still `tv`, the digits left
those from `f` against `tv * base`, from the index `i`. -/
structure OgFT (S : Nat → Prop) (X0 : Raws) (G : Nat → Prop) (I : List Nat → String → Mem → Prop)
    (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat) (H : Heap) (F : List Blk)
    (L : List NumObj) (x : NumObj) (ob : Nat) (cs sent : List Nat) (t : String)
    (ip fr bs mx : NumObj) (cur tn : RH) (f : Num) (tv fuel i : Nat) : Prop where
  st : OgSt S X0 G I Mt0 M R0 R sp W H F L [.own ip, .own fr, cur, .own bs, .own mx, tn]
    [16, 24, 40, 32, 56, 48] sent t
  ipOK : RHOK L (.own ip)
  curOK : RHOK L cur
  tnOK : RHOK L tn
  frn : NewNum f fr
  fi : FracInv f x.rep.scale
  tnv : tn.base.rep.num = ⟨false, tv, 0⟩
  tnN : tn.base.rep.Norm
  tnP : 1 ≤ tn.base.rep.len
  tv0 : tv ≠ 0
  tlt : tv < 10 ^ x.rep.scale
  fl : FracFuel x.rep.scale (tv * ob) fuel
  tgt : sent ++ ogFracOut ob x.rep.scale fuel f (tv * ob) i = cs ++ Num.outChars x.rep.num ob
  sp8 : ¬ ob ≤ 16 → ldv .ld M (sp - 176 + 8) = boolWord (i != 0)
  regs : OgFrRegs R x ob bs mx cur
  r8 : R 8 = BitVec.ofNat 64 ip.rep.p
  r20 : R 20 = BitVec.ofNat 64 tn.p

/-- The loop from its head with `fuel` iterations' bound. -/
def OgFL (live S : Nat → Prop) (X0 : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x : NumObj) (ob : Nat) (cs : List Nat) (bs mx : NumObj)
    (fuel : Nat) : Prop :=
  ∀ (t : String) (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (ip fr : NumObj)
    (cur tn : RH) (f : Num) (tv i : Nat) (sent : List Nat),
    OgFH S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur tn f tv fuel i →
    DWO live S Q t 0x80007290#64 R M

/-- **The loop's end** at `0x80007500`: `t_num` freed, then the exit. -/
theorem og_fexit {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {t : String}
    {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {ip fr bs mx : NumObj}
    {cur tn : RH}
    (st : OgSt S X0 G I Mt0 M R0 R sp W H F L [.own ip, .own fr, cur, .own bs, .own mx, tn]
      [16, 24, 40, 32, 56, 48] (cs ++ Num.outChars x.rep.num ob) t)
    (hok : ∀ h ∈ [RH.own ip, .own fr, cur, .own bs, .own mx, tn], RHOK L h)
    (h8 : R 8 = BitVec.ofNat 64 ip.rep.p) (h22 : R 22 = BitVec.ofNat 64 fr.rep.p)
    (h19 : R 19 = BitVec.ofNat 64 bs.rep.p) (h26 : R 26 = BitVec.ofNat 64 cur.p)
    (h24 : R 24 = BitVec.ofNat 64 mx.rep.p) (h20 : R 20 = BitVec.ofNat 64 tn.p) :
    DWO live S Q t 0x80007500#64 R M := by
  have cx := fx.cx
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  refine st.freeSlot (hs1 := [.own ip, .own fr, cur, .own bs, .own mx]) (hs2 := [])
    (os1 := [16, 24, 40, 32, 56]) (os2 := []) cx cb rfl (hok _ (by simp))
    fun L1 L2 x6 hb hr hnv hp post => ?_
  have k : ∀ pc, (pc = 0x80007320#64 ∨ pc = 0x80007530#64) →
      FreeK [1, 10, 14, 15] live S X0 (DQ live S Q t) pc R M (fun _ => False) H F L1 L2 x6 :=
    fun pc hpc R6 M6 H6 F6 L6' hk6 hkf hb6 hof => by
      have st6 := post R6 M6 H6 F6 L6' _ hk6 (by decide) hkf hb6 hof
      simp only [List.append_nil] at st6
      have k7 := og_exit hlive fx t R6 M6 H6 F6 ip fr bs mx cur st6
        (fun h hh => hok h (List.mem_append_left [tn] hh))
        (by rw [hk6.get 8 (by decide)]; exact h8) (by rw [hk6.get 22 (by decide)]; exact h22)
        (by rw [hk6.get 19 (by decide)]; exact h19) (by rw [hk6.get 26 (by decide)]; exact h26)
        (by rw [hk6.get 24 (by decide)]; exact h24)
      rcases hpc with rfl | rfl
      · exact k7
      · have hS : HeapOwn S := fun a h1 h2 => hb6.heap.own a h1 h2
        bc_run hlive hS [] at 0x80007320
        exact k7
  exact ffree_80007500 hlive hb hr hnv (by rw [hp]; exact h20) (k _ (.inl rfl)) (k _ (.inr rfl))
    (k _ (.inr rfl))

/-- `pre_space` through a callee that wrote a handle's word and below the
frame. -/
theorem ldv8_of_out {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp W d : Nat}
    (cx : OnCtx S R0 sp W d) {M M' : Mem} {o : Nat} (ho : 16 ≤ o)
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - 176 + o) a → ¬ frameIn (sp - 176) (W - 176) a →
      imgM M' a = imgM M a) :
    ldv .ld M' (sp - 176 + 8) = ldv .ld M (sp - 176 + 8) := by
  on_facts cx
  have hsf := cx.cc.frame
  have hsl := hsf.lo
  exact ldv_congr .ld fun j hj => hout _
    (outHeap_of_ge (by simp only [heapEnd, widthOfM] at hj ⊢; omega))
    (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
    (by simp only [frameIn, widthOfM] at hj ⊢; omega)

/-- The base as a number. -/
theorem ofInt_nat (n : Nat) : Num.ofInt (n : Int) = ⟨false, n, 0⟩ := by simp [Num.ofInt]

/-- **The loop's tail** from `0x80007268`: `t_num *= base`, then the exit
once `t_num` has more than `scale` digits, else the next digit. -/
theorem og_ftail {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {bs mx : NumObj}
    (hbs : NewNum (Num.ofInt ob) bs) (hmx : NewNum (Num.ofInt (ob - 1 : Nat)) mx) {fuel : Nat}
    (ih : OgFL live S X0 Q I G Mt0 R0 sp W L x ob cs bs mx fuel)
    {t : String} {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {ip fr : NumObj}
    {cur tn : RH} {f : Num} {tv i : Nat} {sent : List Nat}
    (ft : OgFT S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur tn f tv fuel i) :
    DWO live S Q t 0x80007268#64 R M := by
  have cx := fx.cx
  have ha := fx.ha
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  have st := ft.st
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have h2 := st.on.r2
  have hob := ha.obHi
  have hob2 := ha.obLo
  have htnm := RH.obj_mem (hs := [.own ip, .own fr, cur, .own bs, .own mx, tn]) (by simp) ft.tnOK
  have hbsm : bs ∈ RList [.own ip, .own fr, cur, .own bs, .own mx, tn] L := by
    simp [RList, rTemps, RH.tmp]
  have htns := (st.heap.nums _ htnm).shape
  have hbss : NumShape bs.rep := (st.heap.nums bs hbsm).shape
  have htl := RH.obj_len [.own ip, .own fr, cur, .own bs, .own mx, tn] tn
  have htnum : (RH.obj [.own ip, .own fr, cur, .own bs, .own mx, tn] tn).rep.num =
      ⟨false, tv, 0⟩ := by rw [RH.obj_num, ft.tnv]
  have hts : (RH.obj [.own ip, .own fr, cur, .own bs, .own mx, tn] tn).rep.scale = 0 := by
    rw [← NumRep.num_scale, htnum]
  have htnorm := (RH.obj_norm [.own ip, .own fr, cur, .own bs, .own mx, tn] tn).2 ft.tnN
  have htsz := NumRep.size_le htns htnorm (E := x.rep.scale) (by rw [htnum]; exact ft.tlt)
  have hbs0 : bs.rep.scale = 0 := by rw [← NumRep.num_scale, hbs.num]; rfl
  have hbmag : bs.rep.num.mag = ob := by rw [hbs.num]; simp [Num.ofInt]
  have hbssz := NumRep.size_le hbss hbs.norm (E := 10) (by rw [hbmag]; omega)
  have hxsz := ha.size
  have htP := ft.tnP
  have hbP := hbs.pos
  have hG : ∀ a, G a → ¬ constBytes a := fun a hg => (cb.off a hg).2.2.1
  have hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p := by
    rw [st.on.glob hG (by omega) (by simp only [twoAddr, zeroAddr]; omega) (by omega)]
    exact ha.zero.glob
  have hz8 : KZero M z (6 + 2 ^ 30) := { ha.zero.mono (by omega) with glob := hzg }
  have hrc := rCnt_le [.own ip, .own fr, cur, .own bs, .own mx, tn] z.rep.p
  simp only [List.length_cons, List.length_nil] at hrc
  have hzk : KZero M (rBump [.own ip, .own fr, cur, .own bs, .own mx, tn] z) (2 ^ 30) :=
    KZero.withRefs (hz8.mono (by omega))
  have hmb : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80 :=
    (st.on.mulBase (fun a hg => (cb.off a hg).2.2.2) (by omega)).trans ha.mulBase
  bc_run hlive hS [h2, ft.r20, ft.regs.r19] at 0x8000573c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine hc_mulH (hs1 := [.own ip, .own fr, cur, .own bs, .own mx]) (h := tn) (hs2 := [])
    (o := 48) (u1 := RH.obj [.own ip, .own fr, cur, .own bs, .own mx, tn] tn) (u2 := bs)
    (z := rBump [.own ip, .own fr, cur, .own bs, .own mx, tn] z) (k := 0) hlive
    (cx.hcFrame (by omega) rfl) (fx.hK.hcOom t) st.on.out st.heap st.own ft.tnOK
    ⟨htnm, hbsm, RList.mem_caller _ ha.mz, by omega, by omega, by omega, by omega,
      hzk.mono (by omega), hmb⟩
    (st.words.get (hs1 := [_, _, _, _, _]) (os1 := [16, 24, 40, 32, 56]) (hs2 := []) (os2 := [])
      rfl)
    (by bsimp [h2]) (by bsimp []; try decide) (by rw [RH.obj_p]; bsimp []) (by bsimp [])
    (by bsimp []) (by bsimp []) ?_
  intro R1 M1 H1 F1 y hk1 hb1 hown1 hres hout1
  have hy : y.rep.num = ⟨false, tv * ob, 0⟩ := by
    rw [hres.num, htnum, hbs.num, ofInt_nat, mul_int]
  have hk1' : Keeps ogKs R1 R := (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  have og1 := st.ret (hs1 := [_, _, _, _, _]) (hs2 := []) (os1 := [16, 24, 40, 32, 56])
    (os2 := []) cx cb rfl hk1' (by decide) hb1 hown1 hres.slot hout1
  have hS1 : HeapOwn S := fun a h1 h2 => og1.heap.heap.own a h1 h2
  have q1 := og1.on.r2
  have hw48 : ldv .ld M1 (sp - 176 + 48) = BitVec.ofNat 64 y.rep.p := hres.slot
  have hw24 : ldv .ld M1 (sp - 176 + 24) = BitVec.ofNat 64 fr.rep.p :=
    og1.words.get (hs1 := [_]) (os1 := [16]) (hs2 := [_, _, _, _]) (os2 := [40, 32, 56, 48]) rfl
  have hxn := og1.heap.nums _ (RList.mem_caller [.own ip, .own fr, cur, .own bs, .own mx, .own y]
    ha.mx)
  have hxsc : ldv .lw M1 (x.rep.p + 8) = BitVec.ofNat 64 x.rep.scale := hxn.scale
  have hxs := hxn.shape
  have hx1 : heapStart ≤ x.rep.p := hxs.pLo
  have hx2 : x.rep.p + 40 ≤ heapEnd := hxs.pHi
  have hym : y ∈ RList [.own ip, .own fr, cur, .own bs, .own mx, .own y] L := by
    simp [RList, rTemps, RH.tmp]
  have hyn := og1.heap.nums y hym
  have hys := hyn.shape
  have hyl := hyn.len
  have hy1 : heapStart ≤ y.rep.p := hys.pLo
  have hy2 : y.rep.p + 40 ≤ heapEnd := hys.pHi
  simp only [heapStart, heapEnd] at hx1 hx2 hy1 hy2
  have hp0 : 0 < tv * ob := Nat.mul_pos (Nat.pos_of_ne_zero ft.tv0) (by omega)
  have hlen : y.rep.len = (Num.decText (tv * ob)).length := by
    rw [← NumRep.intLen_eq hys hres.norm hres.pos, hy]
    exact Dc.BcModel.intLen_dec (by omega)
  have hsz := ha.size
  have hysz : y.rep.len < 2 ^ 31 := by
    rw [hlen]
    have : tv * ob < 10 ^ (x.rep.scale + 10) := by
      rw [Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_lt ft.tlt (by omega)
    have := (Dc.BcModel.decText_le_iff (s := x.rep.scale + 10) (by omega)).2 this
    omega
  have g18 : R1 18 = BitVec.ofNat 64 x.rep.p := by
    rw [hk1.get 18 (by decide)]; bsimp [ft.regs.r18]
  bsimp []
  bc_run hlive hS1 [q1, hw48, hw24, hxsc, hyl, g18] at 0x80007290 0x80007500
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS1 (by omega) (by omega) | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  · intro hc
    rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hc
    have hge : 10 ^ x.rep.scale ≤ tv * ob := by
      have h' : ¬ (Num.decText (tv * ob)).length ≤ x.rep.scale := by omega
      rw [Dc.BcModel.decText_le_iff (by omega)] at h'; omega
    have hsent : sent = cs ++ Num.outChars x.rep.num ob := by
      have := ft.tgt; rwa [ogFracOut_stop (by omega) hge, List.append_nil] at this
    subst hsent
    refine og_fexit hlive fx (og1.regs (ks := [13, 15, 20, 22]) (by keeps_tac Keeps.refl _ _))
      (fun h hh => ?_) ?_ (by bsimp []) ?_ ?_ ?_ (by bsimp [RH.p])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ft.ipOK
      · exact ⟨ft.frn.refs, ft.frn.owns⟩
      · exact ft.curOK
      · exact ⟨hbs.refs, hbs.owns⟩
      · exact ⟨hmx.refs, hmx.owns⟩
      · exact ⟨hres.refs, hres.owns⟩
    · bsimp []; rw [hk1.get 8 (by decide)]; bsimp [ft.r8]
    · bsimp []; rw [hk1.get 19 (by decide)]; bsimp [ft.regs.r19]
    · bsimp []; rw [hk1.get 26 (by decide)]; bsimp [ft.regs.r26]
    · bsimp []; rw [hk1.get 24 (by decide)]; bsimp [ft.regs.r24]
  · intro hc
    rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hc
    have hlt : tv * ob < 10 ^ x.rep.scale :=
      (Dc.BcModel.decText_le_iff (by omega)).1 (by omega)
    exact ih t _ M1 H1 F1 ip fr cur (.own y) f (tv * ob) i sent
      { st := og1.regs (ks := [13, 15, 20, 22]) (by keeps_tac Keeps.refl _ _)
        ipOK := ft.ipOK
        curOK := ft.curOK
        tnOK := ⟨hres.refs, hres.owns⟩
        frn := ft.frn
        fi := ft.fi
        tnv := hy
        tnN := hres.norm
        tnP := hres.pos
        tv0 := by omega
        tlt := hlt
        fl := ft.fl
        tgt := ft.tgt
        sp8 := fun h => by rw [ldv8_of_out cx (o := 48) (by omega) hout1]; exact ft.sp8 h
        regs := ft.regs.keep (ks := [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 20, 22, 28, 29, 30,
          31]) (Keeps.trans (by keeps_tac Keeps.refl _ _) ((hk1.mono (by decide)).trans
            (by keeps_tac Keeps.refl _ _)))
        r13 := by bsimp []
        r20 := by bsimp [RH.p]
        r22 := by bsimp [] }

end Dc.Mach
