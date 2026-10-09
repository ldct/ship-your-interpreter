import Dc.Mach.Bc.OutNumExit

/-! # `bc_out_num` in a base other than 10: the fraction digits

From `0x8000721c` (after the integer part): nothing more at scale 0, else
`.`, then the loop from `0x80007290` that multiplies `frac_part` by the
base, sends its integer part as a digit (`ref_str` up to base 16, else
`bc_out_long` with a space before all but the first) and keeps the rest,
while `t_num = base ^ i` has at most `scale` digits.

- `ogFracOut`: the model's characters for the fraction digits
  (`Num.fracDigits`) from an index; `og_target`, `ogFracOut_step`,
  `ogFracOut_stop` split `Num.outChars` along the loop.
- `OgFH` (loop head), `OgFD` (digit computed), `OgFT` (digit sent): the
  loop's states over the six handles (`t_num` at `48`).
- `og_fcalc`, `og_fdig`, `og_ftail`: one iteration; `og_floop` all of them
  by induction on the fuel `FracFuel`; `og_fexit` frees `t_num` (the
  generated `ffree_80007500`) into `og_exit`.
- `og_dot`, `og_s7`: the entry, `OgK6`.
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

/-- Through a store below the handles' words (`pre_space` at `8`). -/
theorem OgSt.lowWord {live S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W d : Nat}
    {H : Heap} {F : List Blk} {L : List NumObj} {hs : List RH} {os : List Nat}
    {sent : List Nat} {t : String}
    (st : OgSt S X G I Mt0 M R0 R sp W H F L hs os sent t) (cx : OnCtx S R0 sp W d)
    (cb : CharFn live S Q (R0 12) d G I) {o : Nat} (ho : o + 8 ≤ 16) (v : BitVec 64) :
    OgSt S X G I Mt0 (writeLog M [(sp - 176 + o, 8, v)]) R0 R sp W H F L hs os sent t :=
  (st.pre.frame cx cb (by omega) v).close (st.words.transport fun o' ho' => by
    have := st.offs o' ho'; exact ldv_ld_miss _ _ (by omega)) st.offs st.nd

/-- **A digit computed** (`0x800072d4`): `s6` the digit `dg` of index `i`,
`frac_part` the rest `f`. -/
structure OgFD (S : Nat → Prop) (X0 : Raws) (G : Nat → Prop) (I : List Nat → String → Mem → Prop)
    (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat) (H : Heap) (F : List Blk)
    (L : List NumObj) (x : NumObj) (ob : Nat) (cs sent : List Nat) (t : String)
    (ip fr bs mx : NumObj) (cur tn : RH) (f : Num) (tv fuel i dg : Nat) : Prop where
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
  tgt : sent ++ ogDigF ob dg i ++ ogFracOut ob x.rep.scale fuel f (tv * ob) (i + 1) =
    cs ++ Num.outChars x.rep.num ob
  dlt : dg < ob
  sp8 : ¬ ob ≤ 16 → ldv .ld M (sp - 176 + 8) = boolWord (i != 0)
  regs : OgFrRegs R x ob bs mx cur
  r8 : R 8 = BitVec.ofNat 64 ip.rep.p
  r20 : R 20 = BitVec.ofNat 64 tn.p
  r22 : R 22 = BitVec.ofNat 64 dg

/-- **The digit sent** from `0x800072d4`: its `ref_str` character up to base
16, else `bc_out_long` with the width of `max_o_digit` and `pre_space`
(then set), then the tail. -/
theorem og_fdig {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {bs mx : NumObj}
    (hbs : NewNum (Num.ofInt ob) bs) (hmx : NewNum (Num.ofInt (ob - 1 : Nat)) mx) {fuel : Nat}
    (ih : OgFL live S X0 Q I G Mt0 R0 sp W L x ob cs bs mx fuel)
    {t : String} {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {ip fr : NumObj}
    {cur tn : RH} {f : Num} {tv i dg : Nat} {sent : List Nat}
    (fd : OgFD S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur tn f tv fuel i dg) :
    DWO live S Q t 0x800072d4#64 R M := by
  have cx := fx.cx
  have cb := fx.cb
  have hob := fx.ha.obHi
  have hob2 := fx.ha.obLo
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => fd.st.heap.heap.own a h1 h2
  have h9 := fd.st.on.cb
  have h2 := fd.st.on.r2
  have hdg := fd.dlt
  have h21 := fd.regs.r21
  have h22 := fd.r22
  have h23 := fd.regs.r23
  have h25 := fd.regs.r25
  bc_run hlive hS [h21, h22, h23, h25] at 0x80007260 0x800072dc
  · intro hc
    have h16 : ob ≤ 16 := by
      rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hc; simp at hc; omega
    have hdg16 : dg < 16 := by omega
    have hro := refStr_bytes dg hdg16
    have e : (BitVec.ofNat 64 (2147516904 + dg)).toNat = 2147516904 + dg := by
      rw [BitVec.toNat_ofNat]; omega
    dx_ro hlive
    · bsimp [e]; simp only [LdOK, tohostAddr]; omega
    · bsimp [e]; intro b hb; rw [accAddrs_one, List.mem_singleton] at hb; subst hb; rw [hro.1]; exact hro.2
    bsimp [e]
    have hch : Num.hexChar dg < 256 := by unfold Num.hexChar; split <;> omega
    rw [ldvf_lbu, hro.1, zext8_ofNat hch]
    bc_run hlive hS [h9]
    · rw [jalr_tgt _ cx.fal]; exact cx.fal
    rw [jalr_tgt _ cx.fal]
    refine OgSt.call (X := X0) (Mt0 := Mt0) (H := H) (F := F) (L := L)
      (hs := [.own ip, .own fr, cur, .own bs, .own mx, tn]) (os := [16, 24, 40, 32, 56, 48])
      (sent := sent) ?_ cx cb (c := Num.hexChar dg) (by bsimp []) hch (by bsimp [])
      fun R' M' t' hk' st' _ => ?_
    · exact fd.st.regs (ks := [1, 10, 15]) (by keeps_tac Keeps.refl _ _)
    have kk : Keeps cClob R' R := hk'.trans (by keeps_tac Keeps.refl _ _)
    bsimp []
    exact og_ftail hlive fx hbs hmx ih (i := i + 1)
      { st := st'
        ipOK := fd.ipOK
        curOK := fd.curOK
        tnOK := fd.tnOK
        frn := fd.frn
        fi := fd.fi
        tnv := fd.tnv
        tnN := fd.tnN
        tnP := fd.tnP
        tv0 := fd.tv0
        tlt := fd.tlt
        fl := fd.fl
        tgt := by rw [← fd.tgt]; simp [ogDigF, h16]
        sp8 := fun h => absurd h16 h
        regs := fd.regs.keep kk
        r8 := by rw [kk.get 8 (by decide)]; exact fd.r8
        r20 := by rw [kk.get 20 (by decide)]; exact fd.r20 }
  · intro hc
    have h16 : ¬ ob ≤ 16 := by
      rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)] at hc; simp at hc; omega
    have hw8 := fd.sp8 h16
    have hmxm : mx ∈ RList [.own ip, .own fr, cur, .own bs, .own mx, tn] L := by
      simp [RList, rTemps, RH.tmp]
    have hmxn := fd.st.heap.nums mx hmxm
    have hmxs := hmxn.shape
    have hsz := hmxs.size
    have hp1 := hmxs.pHi
    have hp2 := hmxs.pLo
    simp only [heapEnd, heapStart] at hp1 hp2
    have hl := hmxn.len
    have h24 := fd.regs.r24
    bc_run hlive hS [h24, hl, h9, hw8, h2, h22] at 0x800064ec
    all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
    refine OgSt.long hlive (fd.st.regs (ks := [1, 10, 11, 12, 13, 15]) (by keeps_tac Keeps.refl _ _))
      cx cb (v := dg) (size := mx.rep.len) (sp_ := (i != 0)) (by bsimp [h9]) (by bsimp [])
      (by omega) (by bsimp []) (by omega) (by bsimp []) (by bsimp []) fun R' M' t' hk' st' _ => ?_
    have kk : Keeps cClob R' R := hk'.trans (by keeps_tac Keeps.refl _ _)
    have q2 := st'.on.r2
    have hS' : HeapOwn S := fun a h1 h2 => st'.heap.heap.own a h1 h2
    bsimp []
    bc_run hlive hS' [q2] at 0x80007268
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hw := mx_len hmx hmxs hob2
    exact og_ftail hlive fx hbs hmx ih (i := i + 1)
      { st := (st'.lowWord cx cb (o := 8) (by omega) _).regs (ks := [15])
          (by keeps_tac Keeps.refl _ _)
        ipOK := fd.ipOK
        curOK := fd.curOK
        tnOK := fd.tnOK
        frn := fd.frn
        fi := fd.fi
        tnv := fd.tnv
        tnN := fd.tnN
        tnP := fd.tnP
        tv0 := fd.tv0
        tlt := fd.tlt
        fl := fd.fl
        tgt := by rw [← fd.tgt, hw]; simp [ogDigF, h16]
        sp8 := fun _ => by rw [ldv_store_hit]; rfl
        regs := fd.regs.keep (ks := [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31])
          (Keeps.trans (by keeps_tac Keeps.refl _ _) kk)
        r8 := by bsimp []; rw [kk.get 8 (by decide)]; exact fd.r8
        r20 := by bsimp []; rw [kk.get 20 (by decide)]; exact fd.r20 }

/-- **A digit computed** from the loop's head `0x80007290`:
`bc_multiply (frac_part, base, &frac_part, scale)`, the digit
`bc_num2long (frac_part)`, `bc_int2num (&int_part, digit)` and
`bc_sub (frac_part, int_part, &frac_part, 0)`. -/
theorem og_fcalc {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {bs mx : NumObj}
    (hbs : NewNum (Num.ofInt ob) bs) (hmx : NewNum (Num.ofInt (ob - 1 : Nat)) mx) {fuel : Nat}
    (ih : OgFL live S X0 Q I G Mt0 R0 sp W L x ob cs bs mx fuel)
    {t : String} {R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk} {ip fr : NumObj}
    {cur tn : RH} {f : Num} {tv i : Nat} {sent : List Nat}
    (fh : OgFH S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur tn f tv (fuel + 1) i) :
    DWO live S Q t 0x80007290#64 R M := by
  have cx := fx.cx
  have ha := fx.ha
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  have st := fh.st
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have h2 := st.on.r2
  have hob := ha.obHi
  have hob2 := ha.obLo
  have hsx := ha.size
  have hfrm : fr ∈ RList [.own ip, .own fr, cur, .own bs, .own mx, tn] L := by
    simp [RList, rTemps, RH.tmp]
  have hbsm : bs ∈ RList [.own ip, .own fr, cur, .own bs, .own mx, tn] L := by
    simp [RList, rTemps, RH.tmp]
  have hfrs : NumShape fr.rep := (st.heap.nums fr hfrm).shape
  have hbss : NumShape bs.rep := (st.heap.nums bs hbsm).shape
  have hfsc : fr.rep.scale = x.rep.scale := by
    rw [← NumRep.num_scale, fh.frn.num]; exact fh.fi.scale
  have hfrsz := NumRep.size_le hfrs fh.frn.norm (E := x.rep.scale)
    (by rw [fh.frn.num]; exact fh.fi.lt)
  have hfP := fh.frn.pos
  have hbs0 : bs.rep.scale = 0 := by rw [← NumRep.num_scale, hbs.num]; rfl
  have hbmag : bs.rep.num.mag = ob := by rw [hbs.num]; simp [Num.ofInt]
  have hbssz := NumRep.size_le hbss hbs.norm (E := 10) (by rw [hbmag]; omega)
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
  bc_run hlive hS [h2, fh.r22, fh.regs.r19, fh.r13] at 0x8000573c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine hc_mulH (hs1 := [.own ip]) (h := .own fr) (hs2 := [cur, .own bs, .own mx, tn])
    (o := 24) (u1 := fr) (u2 := bs) (z := rBump [.own ip, .own fr, cur, .own bs, .own mx, tn] z)
    (k := x.rep.scale) hlive (cx.hcFrame (by omega) rfl) (fx.hK.hcOom t) st.on.out st.heap st.own
    ⟨fh.frn.refs, fh.frn.owns⟩
    ⟨hfrm, hbsm, RList.mem_caller _ ha.mz, by omega, by omega, by omega, by omega,
      hzk.mono (by omega), hmb⟩
    (st.words.get (hs1 := [_]) (os1 := [16]) (hs2 := [_, _, _, _]) (os2 := [40, 32, 56, 48]) rfl)
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp []) (by bsimp []) (by bsimp [])
    (by bsimp [fh.r13]) ?_
  intro R1 M1 H1 F1 y hk1 hb1 hown1 hres hout1
  have hy : y.rep.num = ⟨false, f.mag * ob, x.rep.scale⟩ := by
    rw [hres.num, fh.frn.num, hbs.num, ofInt_nat, Dc.BcModel.fracStep_mul fh.fi]
  obtain ⟨hdv, hdlt⟩ := Dc.BcModel.fracStep_digit (b := ob) fh.fi (by omega) hob
  generalize hdg : f.mag * ob / 10 ^ x.rep.scale = dg at hdv hdlt
  have hk1' : Keeps ogKs R1 R := (hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  have og1 := st.ret (hs1 := [_]) (hs2 := [_, _, _, _]) (os1 := [16]) (os2 := [40, 32, 56, 48])
    cx cb rfl hk1' (by decide) hb1 hown1 hres.slot hout1
  have hS1 : HeapOwn S := fun a h1 h2 => og1.heap.heap.own a h1 h2
  have q1 := og1.on.r2
  have hym : y ∈ RList [.own ip, .own y, cur, .own bs, .own mx, tn] L := by
    simp [RList, rTemps, RH.tmp]
  have hyn := og1.heap.nums y hym
  have hw24 : ldv .ld M1 (sp - 176 + 24) = BitVec.ofNat 64 y.rep.p := hres.slot
  bsimp []
  bc_run hlive hS1 [q1, hw24] at 0x800065a0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine bc_num2long_spec hlive hS1 hyn hres.pos _ (by bsimp []) (by bsimp [])
    fun R3 hk3 h103 => ?_
  bsimp []
  have g10 : R3 10 = BitVec.ofNat 64 dg := by
    rw [h103, hy, hdv]; exact ofInt_natCast64 _
  have hsx6 := sxw_ofNat (k := dg) (by omega)
  have g2 : R3 2 = BitVec.ofNat 64 (sp - 176) := by rw [hk3.get 2 (by decide)]; bsimp [q1]
  bc_run hlive hS1 [g10, hsx6, g2] at 0x8000690c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine hc_i2nH (hs1 := []) (h := .own ip) (hs2 := [.own y, cur, .own bs, .own mx, tn]) (o := 16)
    (v := (dg : Int)) hlive (cx.hcFrame (by omega) rfl) (fx.hK.hcOom t) og1.on.out og1.heap
    og1.own fh.ipOK
    (og1.words.get (hs1 := []) (os1 := []) (hs2 := [_, _, _, _, _]) (os2 := [24, 40, 32, 56, 48])
      rfl)
    (by bsimp [g2]) (by bsimp []; try decide) (by bsimp [])
    (by bsimp []; exact (ofInt_natCast64 dg).symm) (by omega) (by omega) ?_
  intro R4 M4 H4 F4 ip2 hk4 hb4 hown4 hres4 hout4
  have og2 := og1.ret (hs1 := []) (hs2 := [_, _, _, _, _]) (os1 := [])
    (os2 := [24, 40, 32, 56, 48]) (ks := ogKs) cx cb rfl
    ((hk4.mono (by decide)).trans (Keeps.trans (by keeps_tac Keeps.refl _ _)
      ((hk3.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))) (by decide) hb4
    hown4 hres4.slot hout4
  have hS4 : HeapOwn S := fun a h1 h2 => og2.heap.heap.own a h1 h2
  have q4 := og2.on.r2
  have hw16 : ldv .ld M4 (sp - 176 + 16) = BitVec.ofNat 64 ip2.rep.p := hres4.slot
  have g27 : R4 27 = BitVec.ofNat 64 y.rep.p := by
    rw [hk4.get 27 (by decide)]; bsimp []; rw [hk3.get 27 (by decide)]; bsimp []
  bsimp []
  bc_run hlive hS4 [q4, hw16, g27] at 0x80004ac4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hym2 : y ∈ RList [.own ip2, .own y, cur, .own bs, .own mx, tn] L := by
    simp [RList, rTemps, RH.tmp]
  have hipm2 : ip2 ∈ RList [.own ip2, .own y, cur, .own bs, .own mx, tn] L := by
    simp [RList, rTemps, RH.tmp]
  have hys : NumShape y.rep := (og2.heap.nums y hym2).shape
  have hips : NumShape ip2.rep := (og2.heap.nums ip2 hipm2).shape
  have hmag : f.mag * ob < 10 ^ (x.rep.scale + 10) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt fh.fi.lt (by omega)
  have hysz := NumRep.size_le hys hres.norm (E := x.rep.scale + 10) (by rw [hy]; exact hmag)
  have hysc : y.rep.scale = x.rep.scale := by rw [← NumRep.num_scale, hy]
  have hip2n : ip2.rep.num = ⟨false, dg, 0⟩ := by rw [hres4.num, ofInt_nat]
  have hipsz := NumRep.size_le hips hres4.norm (E := 10) (by rw [hip2n]; show dg < 10 ^ 10; omega)
  have hipsc : ip2.rep.scale = 0 := by rw [← NumRep.num_scale, hip2n]
  have hyP := hres.pos
  have hiP := hres4.pos
  refine hc_subH (hs1 := [.own ip2]) (h := .own y) (hs2 := [cur, .own bs, .own mx, tn]) (o := 24)
    (u1 := y) (u2 := ip2) (k := 0) hlive (cx.hcFrame (by omega) rfl) (fx.hK.hcOom t) og2.on.out
    og2.heap og2.own ⟨hres.refs, hres.owns⟩
    ⟨hym2, hipm2, hres.norm, hres4.norm, by omega, fun h => absurd h (by omega),
      fun h => absurd h (by omega)⟩
    (fun _ => ⟨hyP, hiP⟩)
    (og2.words.get (hs1 := [_]) (os1 := [16]) (hs2 := [_, _, _, _]) (os2 := [40, 32, 56, 48])
      rfl)
    (by bsimp [q4]) (by bsimp []; try decide) (by bsimp []) (by bsimp []) (by bsimp [])
    (by bsimp []) ?_
  intro R5 M5 H5 F5 y2 hk5 hb5 hown5 hres5 hout5
  have og3 := og2.ret (hs1 := [_]) (hs2 := [_, _, _, _]) (os1 := [16]) (os2 := [40, 32, 56, 48])
    (ks := ogKs) cx cb rfl ((hk5.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)) (by decide)
    hb5 hown5 hres5.slot hout5
  have hf' : y2.rep.num = ⟨false, f.mag * ob % 10 ^ x.rep.scale, x.rep.scale⟩ := by
    rw [hres5.num, hy, hres4.num, ← hdg]; exact Dc.BcModel.fracStep_sub
  have kk : Keeps [1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 22, 27, 28, 29, 30, 31] R5 R :=
    (hk5.mono (by decide)).trans (Keeps.trans (by keeps_tac Keeps.refl _ _)
      ((hk4.mono (by decide)).trans (Keeps.trans (by keeps_tac Keeps.refl _ _)
        ((hk3.mono (by decide)).trans (Keeps.trans (by keeps_tac Keeps.refl _ _)
          ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)))))))
  bsimp []
  exact og_fdig hlive fx hbs hmx ih (i := i) (dg := dg)
    { st := og3
      ipOK := ⟨hres4.refs, hres4.owns⟩
      curOK := fh.curOK
      tnOK := fh.tnOK
      frn := { hres5.toNewNum with num := hf' }
      fi := Dc.BcModel.fracStep_inv fh.fi
      tnv := fh.tnv
      tnN := fh.tnN
      tnP := fh.tnP
      tv0 := fh.tv0
      tlt := fh.tlt
      fl := Dc.BcModel.fracFuel_step fh.fl (by omega)
      tgt := by
        have := fh.tgt
        rw [ogFracOut_step fh.fi fh.tv0 fh.tlt (by omega) hob, hdg, ← List.append_assoc] at this
        exact this
      dlt := hdlt
      sp8 := fun h => by
        rw [ldv8_of_out cx (by omega) hout5, ldv8_of_out cx (by omega) hout4,
          ldv8_of_out cx (by omega) hout1]
        exact fh.sp8 h
      regs := fh.regs.keep kk
      r8 := by rw [hk5.get 8 (by decide)]; bsimp []
      r20 := by rw [kk.get 20 (by decide)]; exact fh.r20
      r22 := by rw [hk5.get 22 (by decide)]; bsimp []; rw [hk4.get 22 (by decide)]; bsimp [] }

/-- **The fraction loop** for every bound, by induction. -/
theorem og_floop {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {bs mx : NumObj}
    (hbs : NewNum (Num.ofInt ob) bs) (hmx : NewNum (Num.ofInt (ob - 1 : Nat)) mx) :
    ∀ fuel, OgFL live S X0 Q I G Mt0 R0 sp W L x ob cs bs mx fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro t R M H F ip fr cur tn f tv i sent fh
    exact absurd (Dc.BcModel.fracFuel_pos fh.fl fh.tlt) (Nat.lt_irrefl 0)
  | succ fuel ih =>
    intro t R M H F ip fr cur tn f tv i sent fh
    exact og_fcalc hlive fx hbs hmx ih fh

/-- **The fraction's start** at `0x8000722c` (after `.`): one more reference
to `_one_` in `t_num`, `pre_space` cleared, then the loop. -/
theorem og_dot {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {fr bs mx : NumObj}
    (hfr : NewNum (ogFrac x.rep.num) fr) (hbs : NewNum (Num.ofInt ob) bs)
    (hmx : NewNum (Num.ofInt (ob - 1 : Nat)) mx) {t1 : String} {R1 : Nat → BitVec 64} {M1 : Mem}
    {H : Heap} {F : List Blk} {ip : NumObj} {cur : RH}
    (st1 : OgSt S X0 G I Mt0 M1 R0 R1 sp W H F L [.own ip, .own fr, cur, .own bs, .own mx]
      [16, 24, 40, 32, 56] (ogIntOut x ob cs ++ [46]) t1)
    (hcur : RHOK L cur) (hip : NewNum ⟨false, 0, 0⟩ ip) (hs1 : 1 ≤ x.rep.scale)
    (g18 : R1 18 = BitVec.ofNat 64 x.rep.p) (g19 : R1 19 = BitVec.ofNat 64 bs.rep.p)
    (g22 : R1 22 = BitVec.ofNat 64 fr.rep.p) (g23 : R1 23 = BitVec.ofNat 64 ob)
    (g24 : R1 24 = BitVec.ofNat 64 mx.rep.p) (g26 : R1 26 = BitVec.ofNat 64 cur.p)
    (g27 : R1 27 = BitVec.ofNat 64 oneAddr) :
    DWO live S Q t1 0x8000722c#64 R1 M1 := by
  have cx := fx.cx
  have ha := fx.ha
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  have hsz := ha.size
  have hS1 : HeapOwn S := fun a h1 h2 => st1.heap.heap.own a h1 h2
  have hG : ∀ a, G a → ¬ constBytes a := fun a hg => (cb.off a hg).2.2.1
  have hone : ldv .ld M1 oneAddr = BitVec.ofNat 64 o.rep.p := by
    rw [st1.on.glob hG (by omega) (by simp only [twoAddr, oneAddr]; omega)
      (by simp only [oneAddr, zeroAddr]; omega)]
    exact ha.one
  have hto : (BitVec.ofNat 64 oneAddr).toNat = oneAddr := rfl
  have hldo : LdOK oneAddr 8 := by simp only [LdOK, oneAddr, tohostAddr]; omega
  have hcst : ∀ b ∈ accAddrs oneAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.cc.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have hom := st1.heap.nums _ (RList.mem_caller [.own ip, .own fr, cur, .own bs, .own mx] ha.mo)
  have hos := hom.shape
  have ho1 : heapStart ≤ o.rep.p := hos.pLo
  have ho2 : o.rep.p + 40 ≤ heapEnd := hos.pHi
  have ho3 : o.rep.p % 8 = 0 := hos.pAl
  simp only [heapStart, heapEnd] at ho1 ho2
  have hol1 : (rBump [.own ip, .own fr, cur, .own bs, .own mx] o).rep.len = 1 := by
    rw [← NumRep.intLen_eq hos ha.oneNorm ha.oneLen]
    show o.rep.num.intLen = 1
    rw [ha.oneNum]; rfl
  have hol : ldv .lw M1 (o.rep.p + 4) = BitVec.ofNat 64 1 := by
    have := hom.len; rw [hol1] at this; exact this
  have hor : ldv .lw M1 (o.rep.p + 12) =
      BitVec.ofNat 64 (o.rep.refs + rCnt [.own ip, .own fr, cur, .own bs, .own mx] o.rep.p) :=
    RList.refsAt st1.heap ha.mo
  have hrc := rCnt_le [.own ip, .own fr, cur, .own bs, .own mx] o.rep.p
  simp only [List.length_cons, List.length_nil] at hrc
  have hro := ha.refs o ha.mo
  have hx := sxw_ofNat (k := o.rep.refs + rCnt [.own ip, .own fr, cur, .own bs, .own mx] o.rep.p + 1)
    (by omega)
  have hxn1 := st1.heap.nums _ (RList.mem_caller [.own ip, .own fr, cur, .own bs, .own mx] ha.mx)
  have hxsc1 : ldv .lw M1 (x.rep.p + 8) = BitVec.ofNat 64 x.rep.scale := hxn1.scale
  have hxs := hxn1.shape
  have hx1 : heapStart ≤ x.rep.p := hxs.pLo
  have hx2 : x.rep.p + 40 ≤ heapEnd := hxs.pHi
  simp only [heapStart, heapEnd] at hx1 hx2
  have q1 := st1.on.r2
  bc_run hlive hS1 [g27, hto, hone, g18, hxsc1, hor, hol, hx, q1] at 0x80007290 0x8000754c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS1 (by omega) (by omega) | exact hldo | exact hcst | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  · intro hc
    exfalso
    rw [toInt_ofNat_small (by omega)] at hc; simp at hc; omega
  intro _
  bc_run hlive hS1 [q1] at 0x80007290
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have p1 := (st1.pre.frame cx cb (o := 48) (by omega) (BitVec.ofNat 64 o.rep.p)).bump cx cb ha.mo
    (ha.owns o ha.mo)
    (v := BitVec.ofNat 64 (o.rep.refs + rCnt [.own ip, .own fr, cur, .own bs, .own mx] o.rep.p + 1))
    (toNat_ofNat_mod32 (by omega)) (by omega)
  have og := p1.close (os := [16, 24, 40, 32, 56, 48])
    ⟨by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
        exact st1.words.get (hs1 := []) (os1 := []) (hs2 := [_, _, _, _]) (os2 := [24, 40, 32, 56]) rfl,
      by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
         exact st1.words.get (hs1 := [_]) (os1 := [16]) (hs2 := [_, _, _]) (os2 := [40, 32, 56]) rfl,
      by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
         exact st1.words.get (hs1 := [_, _]) (os1 := [16, 24]) (hs2 := [_, _]) (os2 := [32, 56]) rfl,
      by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
         exact st1.words.get (hs1 := [_, _, _]) (os1 := [16, 24, 40]) (hs2 := [_]) (os2 := [56]) rfl,
      by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
         exact st1.words.get (hs1 := [_, _, _, _]) (os1 := [16, 24, 40, 32]) (hs2 := []) (os2 := []) rfl,
      by rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _, trivial⟩
  have hpos : 0 < 10 ^ x.rep.scale := Nat.pow_pos (by decide)
  refine og_floop hlive fx hbs hmx (4 * x.rep.scale + 4) t1 _ _ H F ip fr cur (.ref o)
    (ogFrac x.rep.num) 1 0 (ogIntOut x ob cs ++ [46]) ?_
  exact
    { st := (og.lowWord cx cb (o := 8) (by omega) _).regs (ks := [12, 13, 14, 15, 20, 21, 25])
        (by keeps_tac Keeps.refl _ _)
      ipOK := ⟨hip.refs, hip.owns⟩
      curOK := hcur
      tnOK := RHOK.ofMem ha.mo (ha.live o ha.mo)
      frn := hfr
      fi := by rw [frac_part]; exact ⟨rfl, rfl, Nat.mod_lt _ hpos⟩
      tnv := by show o.rep.num = _; rw [ha.oneNum]; rfl
      tnN := ha.oneNorm
      tnP := ha.oneLen
      tv0 := by decide
      tlt := Nat.one_lt_pow (by omega) (by decide)
      fl := Dc.BcModel.fracFuel_init _
      tgt := by
        rw [og_target fx.mag fx.ne, if_neg (by simp [NumRep.num_scale]; omega)]
        simp [NumRep.num_scale]
      sp8 := fun _ => by rw [ldv_store_hit]; rfl
      regs := ⟨by bsimp [g18], by bsimp [g19], by bsimp [], by bsimp [g23], by bsimp [g24],
        by bsimp [], by bsimp [g26]⟩
      r13 := by bsimp []
      r20 := by bsimp [RH.p]
      r22 := by bsimp [g22] }


/-- **After the integer part** (`0x8000721c`): no fraction digits at scale
0, else `.`, `t_num` one more reference to `_one_`, `pre_space` cleared and
the loop. -/
theorem og_s7 {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {fr bs mx : NumObj}
    (hfr : NewNum (ogFrac x.rep.num) fr) (hbs : NewNum (Num.ofInt ob) bs)
    (hmx : NewNum (Num.ofInt (ob - 1 : Nat)) mx) :
    OgK6 live S X0 Q I G Mt0 R0 sp W L x ob cs fr bs mx := by
  intro t R M H F ip cur st hcur hip rg
  have cx := fx.cx
  have ha := fx.ha
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have h2 := st.on.r2
  have hxn := st.heap.nums _ (RList.mem_caller [.own ip, .own fr, cur, .own bs, .own mx] ha.mx)
  have hxsc : ldv .lw M (x.rep.p + 8) = BitVec.ofNat 64 x.rep.scale := hxn.scale
  have hxs := hxn.shape
  have hx1 : heapStart ≤ x.rep.p := hxs.pLo
  have hx2 : x.rep.p + 40 ≤ heapEnd := hxs.pHi
  simp only [heapStart, heapEnd] at hx1 hx2
  have hsz := ha.size
  have h18 := rg.r18
  bc_run hlive hS [h18, hxsc] at 0x8000731c 0x80007224
  all_goals first | exact acc_heap hS (by omega) (by omega) | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  · intro hc
    have hs0 : x.rep.scale = 0 := by
      rw [toInt_ofNat_small (by omega)] at hc; simp at hc; omega
    have hw16 : ldv .ld M (sp - 176 + 16) = BitVec.ofNat 64 ip.rep.p :=
      st.words.get (hs1 := []) (os1 := []) (hs2 := [_, _, _, _]) (os2 := [24, 40, 32, 56]) rfl
    bc_run hlive hS [h2, hw16] at 0x80007320
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have htg : ogIntOut x ob cs = cs ++ Num.outChars x.rep.num ob := by
      rw [og_target fx.mag fx.ne, if_pos (by simp [NumRep.num_scale, hs0])]; simp
    refine og_exit hlive fx t _ M H F ip fr bs mx cur
      (htg ▸ st.regs (ks := [8, 15]) (by keeps_tac Keeps.refl _ _)) (fun h hh => ?_) (by bsimp [])
      (by bsimp [rg.r22]) (by bsimp [rg.r19]) (by bsimp [rg.r26]) (by bsimp [rg.r24])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl
    · exact ⟨hip.refs, hip.owns⟩
    · exact ⟨hfr.refs, hfr.owns⟩
    · exact hcur
    · exact ⟨hbs.refs, hbs.owns⟩
    · exact ⟨hmx.refs, hmx.owns⟩
  · intro hc
    have hs1 : 1 ≤ x.rep.scale := by
      rw [toInt_ofNat_small (by omega)] at hc; simp at hc; omega
    have h9 := st.on.cb
    bc_run hlive hS [h9]
    · rw [jalr_tgt _ cx.fal]; exact cx.fal
    rw [jalr_tgt _ cx.fal]
    refine OgSt.call (X := X0) (Mt0 := Mt0) (H := H) (F := F) (L := L)
      (hs := [.own ip, .own fr, cur, .own bs, .own mx]) (os := [16, 24, 40, 32, 56])
      (sent := ogIntOut x ob cs) ?_ cx cb (c := 46) (by bsimp []) (by decide) (by bsimp [])
      fun R1 M1 t1 hk1 st1 _ => ?_
    · exact st.regs (ks := [1, 10, 15]) (by keeps_tac Keeps.refl _ _)
    have kk1 : Keeps cClob R1 R := hk1.trans (by keeps_tac Keeps.refl _ _)
    bsimp []
    exact og_dot hlive fx hfr hbs hmx st1 hcur hip hs1
      (by rw [kk1.get 18 (by decide)]; exact rg.r18) (by rw [kk1.get 19 (by decide)]; exact rg.r19)
      (by rw [kk1.get 22 (by decide)]; exact rg.r22) (by rw [kk1.get 23 (by decide)]; exact rg.r23)
      (by rw [kk1.get 24 (by decide)]; exact rg.r24) (by rw [kk1.get 26 (by decide)]; exact rg.r26)
      (by rw [kk1.get 27 (by decide)]; exact rg.r27)

end Dc.Mach
