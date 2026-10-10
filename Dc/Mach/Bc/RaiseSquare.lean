import Dc.Mach.Bc.RaiseLoop

/-!
# `bc_raise`'s second loop (`0x800066f0` to `0x80006740`)

    66f0 power = power² at pwrscale doubled
    6708 odd bit: calcscale += pwrscale; temp = temp · power; exponent >>= 1
         zero → 6740; else (and on an even bit) power reloaded, again

The handles are `[power, temp]` (`RaP2`); the first squaring starts from
`temp` and `power` naming one object (`ra_p2_sq` takes any handles whose
squaring leaves `[temp]`). `Dc.BcModel.RaiseInv` is the arithmetic.

- `RaAt.mulRet`: `bc_raise`'s frame through a `bc_multiply` into a handle word.
- `RaP2`: the state at `0x800066f0` and `0x80006708`.
- `ra_p2_sq`, `ra_p2_tail`, `ra_p2_loop`: one squaring, the rest of an
  iteration, the loop.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The frame of `bc_raise` through a `bc_multiply` writing the handle word
at `sp - 96 + o`, after register moves `ks`. -/
theorem RaAt.mulRet {S : Nat → Prop} {Mt0 M M1 : Mem} {R0 R R' R1 : Nat → BitVec 64}
    {sp W q o : Nat} {slots : List (Nat × Nat)} {ks : List Nat} (cx : RaCtx S R0 sp W q)
    (h : RaAt S Mt0 M R0 R sp W q slots) (hk : Keeps ks R' R) (hk1 : Keeps binClob R1 R')
    (ho : o = 0 ∨ o = 8)
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - 96 + o) a → ¬ frameIn (sp - 96) (W - 96) a →
      imgM M1 a = imgM M a)
    (hks : ∀ z ∈ ks, z ∈ raAll ∧ z ≠ 2 ∧ z ≠ 23 := by decide)
    (hlo : ∀ p ∈ slots, 16 ≤ p.2 := by decide) (htop : ∀ p ∈ slots, p.2 + 8 ≤ 96 := by decide) :
    RaAt S Mt0 M1 R0 R1 sp W q slots := by
  ra_facts cx
  exact (h.regsA hk hks).call hlo htop (by omega) (by omega) (hk1.mono (by decide))
    (fun a h1 h2' h3 => hout a h1 (fun h => h2' ⟨by have := h.1; omega,
      by have := h.2; omega⟩) h3)
    (fun a h1 _ => outHeap_of_ge (by simp only [heapEnd]; omega))

/-- The other handle word through a `bc_multiply` into `sp - 96 + o`. -/
theorem ldv_mulRet {M M1 : Mem} {sp W o o' : Nat} (hW : 96 ≤ W) (hsp : heapEnd + W ≤ sp)
    (hoo : o + 8 ≤ o' ∨ o' + 8 ≤ o) (ho : o' + 8 ≤ 16)
    (hout : ∀ a, OutHeap a → ¬ slotBytes (sp - 96 + o) a → ¬ frameIn (sp - 96) (W - 96) a →
      imgM M1 a = imgM M a) :
    ldv .ld M1 (sp - 96 + o') = ldv .ld M (sp - 96 + o') :=
  ldv_congr .ld fun j hj => hout _ (outHeap_of_ge (by simp only [widthOfM] at hj; omega))
    (by simp only [slotBytes, widthOfM] at hj ⊢; omega)
    (by simp only [frameIn, widthOfM] at hj ⊢; omega)

/-- The caller's `x1` from its entry among the handles. -/
theorem NumShape.ofWithRefs {x1 : NumObj} {k : Nat} (h : NumShape (x1.withRefs k).rep)
    (hk : x1.rep.refs < 2 ^ 31) : NumShape x1.rep :=
  ⟨h.dsLen, h.dig, h.size, hk, h.pAl, h.pLo, h.pHi, h.ptrLe, h.vLo, h.vHi, h.sep, h.emptyScale,
    h.emptyIn⟩

/-- The second loop's state at `0x800066f0` (before the squaring, `s2` the
power too) and `0x80006708` (after it): `power` the fresh `Pw` holding
`a ^ P`, `temp` the handle `hT` holding `a ^ T`, the exponent left `e`,
`pwrscale` and `calcscale` in `s1`, `s5`, `temp`'s pointer in `s4`. -/
structure RaP2 (S : Nat → Prop) (X : Raws) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat) (H : Heap)
    (F : List Blk) (A B : List NumObj) (x1 Pw : NumObj) (hT : Hd) (P T e rs nf : Nat) : Prop where
  ra : RaAt S Mt0 M R0 R sp W q raSlots2
  heap : BcHeap S X M H F (KList [] [some Pw, hT] A B x1)
  pw : RaPow x1.rep.num P Pw
  pw1 : Pw.rep.refs = 1
  tm : RaPow x1.rep.num T (Hd.objIn [hT] x1 hT)
  t1 : ∀ x, hT = some x → x.rep.refs = 1
  r9 : R 9 = BitVec.ofNat 64 (x1.rep.scale * P)
  r8 : R 8 = BitVec.ofNat 64 e
  r20 : R 20 = BitVec.ofNat 64 (Hd.p x1 hT)
  r21 : R 21 = BitVec.ofNat 64 (x1.rep.scale * T)
  r22 : R 22 = BitVec.ofNat 64 rs
  r24 : R 24 = BitVec.ofNat 64 nf
  w8 : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 Pw.rep.p
  w0 : ldv .ld M (sp - 96) = BitVec.ofNat 64 (Hd.p x1 hT)

/-- **A squaring of the second loop** from `0x800066f0`: the handles
`hs1 ++ hW :: hs2` leave `[hT]` once `power` (`hW`) is dropped. -/
theorem ra_p2_sq {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q u P T e rs nf : Nat} {H : Heap}
    {F : List Blk} {A B : List NumObj} {x1 z o : NumObj} {hs1 hs2 : List Hd} {hW hT : Hd}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u) (hoom : RaOom live S Q Mt0 sp W q)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots2)
    (hb : BcHeap S X M H F (KList [] (hs1 ++ hW :: hs2) A B x1))
    (hown : ∀ x, some x ∈ hs1 ++ hW :: hs2 → x.Owns)
    (hzc : zeroCount (hs1 ++ hW :: hs2) ≤ 2)
    (hd : hs1 ++ Hd.drop hW ++ hs2 = [hT]) (hh : ∀ x, hW = some x → 1 ≤ x.rep.refs)
    (hpw : RaPow x1.rep.num P (Hd.objIn (hs1 ++ hW :: hs2) x1 hW))
    (htm : RaPow x1.rep.num T (Hd.objIn [hT] x1 hT)) (ht1 : ∀ x, hT = some x → x.rep.refs = 1)
    (hP1 : 1 ≤ P) (hPu : 2 * P ≤ u)
    (h18 : R 18 = BitVec.ofNat 64 (Hd.p x1 hW)) (h9 : R 9 = BitVec.ofNat 64 (x1.rep.scale * P))
    (h8 : R 8 = BitVec.ofNat 64 e) (h20 : R 20 = BitVec.ofNat 64 (Hd.p x1 hT))
    (h21 : R 21 = BitVec.ofNat 64 (x1.rep.scale * T))
    (h22 : R 22 = BitVec.ofNat 64 rs) (h24 : R 24 = BitVec.ofNat 64 nf)
    (hw8 : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 (Hd.p x1 hW))
    (hw0 : ldv .ld M (sp - 96) = BitVec.ofNat 64 (Hd.p x1 hT))
    (hk : ∀ R' M' H' F' Pw, RaP2 S X Mt0 M' R0 R' sp W q H' F' A B x1 Pw hT (2 * P) T e rs nf →
      DW live S Q 0x80006708#64 R' M') :
    DW live S Q 0x800066f0#64 R M := by
  have cx := env.cx
  ra_facts cx
  have hsf := cx.frame
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := ra.r2
  have hcs := env.cst.transport cx ra.out
  have hsz := env.size
  have hWm := Hd.objIn_mem (hs := hs1 ++ hW :: hs2) (List.mem_append_right _ List.mem_cons_self)
    [] A B x1
  have hWs := (hb.nums _ hWm).shape
  have hx1m : x1.withRefs (x1.rep.refs + zeroCount (hs1 ++ hW :: hs2)) ∈
      KList [] (hs1 ++ hW :: hs2) A B x1 := by
    simp only [KList, List.nil_append, List.append_assoc]
    exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)
  have hx1s := NumShape.ofWithRefs (hb.nums _ hx1m).shape (by have := env.refs1; omega)
  have hpz := hpw.size hWs hx1s rfl hP1
  have hLm : P * (x1.rep.len + x1.rep.scale) ≤ u * (x1.rep.len + x1.rep.scale) :=
    Nat.mul_le_mul_right _ (by omega)
  have hLu : u * (x1.rep.len + x1.rep.scale + 1) < 2 ^ 24 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ u)) hsz
  have hLL : u * (x1.rep.len + x1.rep.scale) ≤ u * (x1.rep.len + x1.rep.scale + 1) :=
    Nat.mul_le_mul_left _ (Nat.le_succ _)
  have hsa : x1.rep.scale * (2 * P) ≤ u * (x1.rep.len + x1.rep.scale + 1) := by
    rw [Nat.mul_comm u]; exact Nat.mul_le_mul (by omega) hPu
  have hsc : x1.rep.scale * P * 2 ^ 1 = x1.rep.scale * (2 * P) := by
    rw [Nat.pow_one, Nat.mul_assoc, Nat.mul_comm P 2]
  have hl9 : x1.rep.scale * P * 2 ^ 1 < 2 ^ 31 := by rw [hsc]; omega
  have hown' : ∀ y ∈ KList [] (hs1 ++ hW :: hs2) A B x1, y.Owns := KList.owns hown env.owns
  have hzk : KZero M (z.inK x1 (zeroCount (hs1 ++ hW :: hs2)))
      (4 * ((Hd.objIn (hs1 ++ hW :: hs2) x1 hW).rep.len +
        (Hd.objIn (hs1 ++ hW :: hs2) x1 hW).rep.scale +
        ((Hd.objIn (hs1 ++ hW :: hs2) x1 hW).rep.len +
          (Hd.objIn (hs1 ++ hW :: hs2) x1 hW).rep.scale)) + 8) :=
    KZero.inK x1 _ (hcs.zero.mono (by omega))
  bc_run hlive hS [h2, h18, h9, slliw_ofNat hl9] at 0x8000573c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine ra_mulK (hs1 := hs1) (h := hW) (hs2 := hs2) (o := 8)
    (u1 := Hd.objIn (hs1 ++ hW :: hs2) x1 hW) (u2 := Hd.objIn (hs1 ++ hW :: hs2) x1 hW)
    (z := z.inK x1 (zeroCount (hs1 ++ hW :: hs2)))
    (k := x1.rep.scale * P * 2 ^ 1) hlive cx hoom.dm (.inr rfl) ra.out hb hown' env.r1 hh
    ⟨hWm, hWm, NumObj.inK_memK _ env.mz, by have := hpw.len; omega, by have := hpw.len; omega,
      by omega, hl9, hzk, hcs.mulBase⟩ hw8 (by bsimp [h2]) (by bsimp []; try decide)
    (by bsimp [h18, Hd.objIn_p]) (by bsimp [h18, Hd.objIn_p]) (by bsimp [h2]) (by bsimp []) ?_
  intro R1 M1 H1 F1 y hk1 hb1 hmr hout1
  rw [List.append_assoc, ← List.append_assoc hs1, hd] at hb1
  have hpow : RaPow x1.rep.num (2 * P) y := by
    have := RaPow.mul (a := x1.rep.num) (m := P) (n := P) (k := x1.rep.scale * P * 2 ^ 1) (by
      rw [NumRep.num_scale, Nat.pow_one]; omega) (by omega)
      (by rw [← hpw.num]; exact hmr.toNewNum)
    rwa [← Nat.two_mul] at this
  refine hk R1 M1 H1 F1 y
    { ra := ra.mulRet cx (ks := [1, 9, 10, 11, 12, 13]) (by keeps_tac Keeps.refl _ _) hk1
        (.inr rfl) hout1
      heap := hb1
      pw := hpow
      pw1 := hmr.refs
      tm := htm
      t1 := ht1
      r9 := by rw [hk1.get 9 (by decide), ← hsc]; bsimp []
      r8 := by rw [hk1.get 8 (by decide)]; bsimp [h8]
      r20 := by rw [hk1.get 20 (by decide)]; bsimp [h20]
      r21 := by rw [hk1.get 21 (by decide)]; bsimp [h21]
      r22 := by rw [hk1.get 22 (by decide)]; bsimp [h22]
      r24 := by rw [hk1.get 24 (by decide)]; bsimp [h24]
      w8 := hmr.slot
      w0 := by
        have := ldv_mulRet (o := 8) (o' := 0) (by omega) (by simp only [heapEnd]; omega)
          (by omega) (by omega) hout1
        rw [Nat.add_zero] at this; rw [this, hw0] }

/-- **The rest of an iteration** from `0x80006708` (`power = a ^ P` squared,
`u = T + P·e`): an odd bit multiplies `power` into `temp` at
`calcscale = pwrscale + calcscale`; `e >>= 1`; the loop again or its exit. -/
theorem ra_p2_tail {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q u P T e rs nf : Nat} {H : Heap}
    {F : List Blk} {A B : List NumObj} {x1 z o Pw : NumObj} {hT : Hd}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u) (hoom : RaOom live S Q Mt0 sp W q)
    (st : RaP2 S X Mt0 M R0 R sp W q H F A B x1 Pw hT P T e rs nf)
    (hinv : u = T + P * e) (he1 : 1 ≤ e) (hP1 : 1 ≤ P) (hT1 : 1 ≤ T)
    (hloop : ∀ R' M' H' F' Pw' hT' T', RaP2 S X Mt0 M' R0 R' sp W q H' F' A B x1 Pw' hT' P T' (e / 2) rs nf →
      R' 18 = BitVec.ofNat 64 Pw'.rep.p → T' = (if e % 2 = 1 then T + P else T) → 1 ≤ e / 2 →
      DW live S Q 0x800066f0#64 R' M')
    (hexit : ∀ R' M' H' F' Pw' T', RaP2 S X Mt0 M' R0 R' sp W q H' F' A B x1 Pw' (some T') P u 0 rs nf →
      DW live S Q 0x80006740#64 R' M') :
    DW live S Q 0x80006708#64 R M := by
  have cx := env.cx
  ra_facts cx
  have hsf := cx.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.ra
  have h2 := ra.r2
  have hcs := env.cst.transport cx ra.out
  have hsz := env.size
  have hLu : u * (x1.rep.len + x1.rep.scale + 1) < 2 ^ 24 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ u)) hsz
  have heu : e ≤ u := by
    have : 1 * e ≤ P * e := Nat.mul_le_mul_right _ hP1
    omega
  have he64 : e < 2 ^ 64 := by
    have : u ≤ u * (x1.rep.len + x1.rep.scale + 1) := Nat.le_mul_of_pos_right u (by omega)
    omega
  have hsr : e % 2 ^ 64 / 2 ^ 1 = e / 2 := by rw [Nat.mod_eq_of_lt he64, Nat.pow_one]
  bc_run hlive hS [h2, st.r8, and1_ofNat he64] at 0x8000573c 0x800066f0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals intro hz
  all_goals rcases Nat.mod_two_eq_zero_or_one e with hpar | hpar <;> rw [hpar] at hz ⊢
  all_goals first | exact absurd hz (by decide) | skip
  · -- odd: temp = temp · power
    have hTPu : T + P ≤ u := by
      have : P * 1 ≤ P * e := Nat.mul_le_mul_left _ he1
      omega
    have hscs : x1.rep.scale * P + x1.rep.scale * T ≤ u * (x1.rep.len + x1.rep.scale + 1) := by
      rw [← Nat.mul_add, Nat.mul_comm u]; exact Nat.mul_le_mul (by omega) (by omega)
    have hk31 : x1.rep.scale * P + x1.rep.scale * T < 2 ^ 31 := by omega
    bc_run hlive hS [h2, st.w8, st.r9, st.r21, st.r20, st.r8, addw_ofNat hk31, shr_ofNat, hsr]
      at 0x8000573c
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hTm : Hd.objIn [some Pw, hT] x1 hT ∈ KList [] [some Pw, hT] A B x1 :=
      Hd.objIn_mem (List.mem_cons_of_mem _ List.mem_cons_self) [] A B x1
    have hPm : Hd.objIn [some Pw, hT] x1 (some Pw) ∈ KList [] [some Pw, hT] A B x1 :=
      Hd.objIn_mem List.mem_cons_self [] A B x1
    have hx1m : x1.withRefs (x1.rep.refs + zeroCount [some Pw, hT]) ∈
        KList [] [some Pw, hT] A B x1 := by
      simp only [KList, List.nil_append, List.append_assoc]
      exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)
    have hx1s := NumShape.ofWithRefs (hb.nums _ hx1m).shape (by have := env.refs1; omega)
    have hTs := (hb.nums _ hTm).shape
    have hPs := (hb.nums _ hPm).shape
    have hTz : (Hd.objIn [some Pw, hT] x1 hT).rep.len + (Hd.objIn [some Pw, hT] x1 hT).rep.scale ≤
        T * (x1.rep.len + x1.rep.scale) + 1 := st.tm.size hTs hx1s rfl hT1
    have hPz : (Hd.objIn [some Pw, hT] x1 (some Pw)).rep.len +
        (Hd.objIn [some Pw, hT] x1 (some Pw)).rep.scale ≤
        P * (x1.rep.len + x1.rep.scale) + 1 := st.pw.size hPs hx1s rfl hP1
    have hTl : 1 ≤ (Hd.objIn [some Pw, hT] x1 hT).rep.len := st.tm.len
    have hPl : 1 ≤ (Hd.objIn [some Pw, hT] x1 (some Pw)).rep.len := st.pw.len
    have hLL : (T + P) * (x1.rep.len + x1.rep.scale) ≤ u * (x1.rep.len + x1.rep.scale + 1) :=
      Nat.mul_le_mul hTPu (Nat.le_succ _)
    rw [Nat.add_mul] at hLL
    have hzc : zeroCount [some Pw, hT] ≤ 1 := by cases hT <;> simp
    have hown : ∀ x, some x ∈ [some Pw, hT] → x.Owns := by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · cases h; exact st.pw.owns
      · rw [List.mem_singleton] at h; subst h; exact st.tm.owns
    have hzk : KZero M (z.inK x1 (zeroCount [some Pw, hT]))
        (4 * ((Hd.objIn [some Pw, hT] x1 hT).rep.len + (Hd.objIn [some Pw, hT] x1 hT).rep.scale +
          ((Hd.objIn [some Pw, hT] x1 (some Pw)).rep.len +
            (Hd.objIn [some Pw, hT] x1 (some Pw)).rep.scale)) + 8) :=
      KZero.inK x1 _ (hcs.zero.mono (by omega))
    refine ra_mulK (hs1 := [some Pw]) (h := hT) (hs2 := []) (o := 0)
      (u1 := Hd.objIn [some Pw, hT] x1 hT) (u2 := Hd.objIn [some Pw, hT] x1 (some Pw))
      (z := z.inK x1 (zeroCount [some Pw, hT]))
      (k := x1.rep.scale * P + x1.rep.scale * T) hlive cx hoom.dm (.inl rfl) ra.out hb
      (KList.owns hown env.owns) env.r1 (fun x hx => Nat.le_of_eq (st.t1 x hx).symm)
      ⟨hTm, hPm, NumObj.inK_memK _ env.mz, by omega, by omega, by omega, hk31, hzk, hcs.mulBase⟩
      (by rw [Nat.add_zero]; exact st.w0) (by bsimp [h2]) (by bsimp []; try decide)
      (by bsimp [st.r20, Hd.objIn_p]) (by bsimp [Hd.objIn_p, Hd.p]) (by bsimp [h2]) (by bsimp []) ?_
    intro R1 M1 H1 F1 y hk1 hb1 hmr hout1
    have hdrop : Hd.drop hT = [] := by
      cases hT with
      | none => rfl
      | some x => simp only [Hd.drop, st.t1 x rfl, ite_true]
    rw [hdrop] at hb1
    have hb2 : BcHeap S X M1 H1 F1 (KList [] [some Pw, some y] A B x1) :=
      hb1.kperm (List.Perm.swap (some Pw) (some y) []) (fun _ h => nomatch h) (fun x hx => by
        rcases List.mem_cons.mp hx with h | h
        · cases h; exact .inl st.pw.owns
        · rw [List.mem_singleton] at h; cases h; exact .inl hmr.owns)
    have hpowT : RaPow x1.rep.num (T + P) y :=
      RaPow.mul (a := x1.rep.num) (m := T) (n := P) (k := x1.rep.scale * P + x1.rep.scale * T)
        (by rw [NumRep.num_scale]; omega) (by omega)
        (by rw [← st.tm.num, ← st.pw.num]; exact hmr.toNewNum)
    have hrA : RaAt S Mt0 M1 R0 R1 sp W q raSlots2 :=
      ra.mulRet cx (ks := [15, 11, 21, 10, 13, 12, 8, 1]) (by keeps_tac Keeps.refl _ _) hk1
        (.inl rfl) hout1
    have h2' := hrA.r2
    have h8' : R1 8 = BitVec.ofNat 64 (e / 2) := by rw [hk1.get 8 (by decide)]; bsimp []
    have hsl : ldv .ld M1 (sp - 96) = BitVec.ofNat 64 y.rep.p := by
      have := hmr.slot; rwa [Nat.add_zero] at this
    have hw8 : ldv .ld M1 (sp - 96 + 8) = BitVec.ofNat 64 Pw.rep.p := by
      rw [ldv_mulRet (o := 0) (o' := 8) (by omega) (by simp only [heapEnd]; omega) (by omega)
        (by omega) hout1]; exact st.w8
    have hst : ∀ R', Keeps [18, 20] R' R1 → R' 20 = BitVec.ofNat 64 y.rep.p →
        RaP2 S X Mt0 M1 R0 R' sp W q H1 F1 A B x1 Pw (some y) P (T + P) (e / 2) rs nf := by
      intro R' hk h20'
      have e21 : x1.rep.scale * (T + P) = x1.rep.scale * P + x1.rep.scale * T := by
        rw [Nat.mul_add, Nat.add_comm]
      exact
        { ra := hrA.regsA hk
          heap := hb2
          pw := st.pw
          pw1 := st.pw1
          tm := hpowT
          t1 := fun x hx => by cases hx; exact hmr.refs
          r9 := by rw [hk.get 9 (by decide), hk1.get 9 (by decide)]; bsimp [st.r9]
          r8 := by rw [hk.get 8 (by decide)]; exact h8'
          r20 := by rw [h20']; rfl
          r21 := by rw [hk.get 21 (by decide), hk1.get 21 (by decide), e21]; bsimp []
          r22 := by rw [hk.get 22 (by decide), hk1.get 22 (by decide)]; bsimp [st.r22]
          r24 := by rw [hk.get 24 (by decide), hk1.get 24 (by decide)]; bsimp [st.r24]
          w8 := hw8
          w0 := by rw [hsl]; rfl }
    bsimp []
    bc_run hlive hS [h2', h8', hsl, hw8] at 0x800066f0 0x80006740
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    all_goals intro hz
    · have h2'' : (upd R1 20 (BitVec.ofNat 64 y.rep.p)) 2 = BitVec.ofNat 64 (sp - 96) := by
        bsimp [h2']
      bc_run hlive hS [h2'', hw8] at 0x800066f0
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      have he2 : e / 2 ≠ 0 := fun h => hz (by rw [h])
      exact hloop _ M1 H1 F1 Pw (some y) (T + P)
        (hst _ (by keeps_tac Keeps.refl _ _) (by bsimp [])) (by bsimp []) (by simp [hpar])
        (by omega)
    · have he2 : e / 2 = 0 := by
        rcases Nat.eq_zero_or_pos (e / 2) with h | h
        · exact h
        · exact absurd (fun h' => by
            have := congrArg BitVec.toNat h'
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
            simp at this; omega) hz
      have hu' : T + P = u := by
        have : e = 1 := by omega
        rw [hinv, this, Nat.mul_one]
      have := hst (upd R1 20 (BitVec.ofNat 64 y.rep.p)) (by keeps_tac Keeps.refl _ _) (by bsimp [])
      rw [hu', he2] at this
      exact hexit _ M1 H1 F1 Pw y this
  · -- even: the loop again
    bc_run hlive hS [h2, st.w8, st.r8, shr_ofNat, hsr] at 0x800066f0
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    exact hloop _ M H F Pw hT T
      { st with
        ra := st.ra.regsA (ks := [15, 8, 18]) (by keeps_tac Keeps.refl _ _)
        r9 := by bsimp [st.r9]
        r8 := by bsimp []
        r20 := by bsimp [st.r20]
        r21 := by bsimp [st.r21]
        r22 := by bsimp [st.r22]
        r24 := by bsimp [st.r24] }
      (by bsimp []) (by simp [hpar]) (by omega)

/-- **The second loop** from `0x800066f0` (`u = T + 2·P·e`, `e ≥ 1`): to its
exit at `0x80006740` with `temp = a ^ u`. -/
theorem ra_p2_loop {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q u rs nf : Nat} {A B : List NumObj} {x1 z o : NumObj}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u) (hoom : RaOom live S Q Mt0 sp W q)
    (hexit : ∀ R' M' H' F' Pw' T' P', RaP2 S X Mt0 M' R0 R' sp W q H' F' A B x1 Pw' (some T') P' u 0 rs nf →
      DW live S Q 0x80006740#64 R' M') :
    ∀ e P T {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {Pw : NumObj} {hT : Hd},
      RaP2 S X Mt0 M R0 R sp W q H F A B x1 Pw hT P T e rs nf → R 18 = BitVec.ofNat 64 Pw.rep.p →
      u = T + 2 * P * e → 1 ≤ e → 1 ≤ P → 1 ≤ T → DW live S Q 0x800066f0#64 R M := by
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    intro P T M R H F Pw hT st h18 hu he1 hP1 hT1
    have hPu : 2 * P ≤ u := by
      have : P ≤ P * e := Nat.le_mul_of_pos_right P he1
      rw [Nat.mul_assoc] at hu; omega
    refine ra_p2_sq (hs1 := []) (hW := some Pw) (hs2 := [hT]) hlive env hoom st.ra st.heap
      (fun x hx => by
        rcases List.mem_cons.mp hx with h | h
        · cases h; exact st.pw.owns
        · rw [List.mem_singleton] at h; subst h; exact st.tm.owns)
      (by cases hT <;> simp) (by simp [Hd.drop, st.pw1]) (fun x hx => by cases hx; exact Nat.le_of_eq st.pw1.symm)
      st.pw st.tm st.t1 hP1 hPu h18 st.r9 st.r8 st.r20 st.r21 st.r22 st.r24 st.w8 st.w0 ?_
    intro R1 M1 H1 F1 Pw1 st1
    refine ra_p2_tail hlive env hoom st1 (by rw [hu, Nat.mul_assoc]) he1 (by omega) hT1 ?_
      (fun R' M' H' F' Pw' hT' st' => hexit R' M' H' F' Pw' hT' _ st')
    intro R2 M2 H2 F2 Pw2 hT2 T2 st2 h18' hT2e he2
    have hinv := (Dc.BcModel.RaiseInv.step (u := u) (T := T) (P := P) (e := e) ⟨hu⟩).total
    rw [← hT2e] at hinv
    exact ih (e / 2) (by omega) (2 * P) T2 st2 h18' hinv he2 (by omega)
      (by rw [hT2e]; split <;> omega)

/-- **The second loop from any handles** whose squaring leaves `[temp]`
(the first iteration, `temp` and `power` one object). -/
theorem ra_p2_first {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q u P T e rs nf : Nat} {H : Heap}
    {F : List Blk} {A B : List NumObj} {x1 z o : NumObj} {hs1 hs2 : List Hd} {hW hT : Hd}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u) (hoom : RaOom live S Q Mt0 sp W q)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots2)
    (hb : BcHeap S X M H F (KList [] (hs1 ++ hW :: hs2) A B x1))
    (hown : ∀ x, some x ∈ hs1 ++ hW :: hs2 → x.Owns)
    (hzc : zeroCount (hs1 ++ hW :: hs2) ≤ 2)
    (hd : hs1 ++ Hd.drop hW ++ hs2 = [hT]) (hh : ∀ x, hW = some x → 1 ≤ x.rep.refs)
    (hpw : RaPow x1.rep.num P (Hd.objIn (hs1 ++ hW :: hs2) x1 hW))
    (htm : RaPow x1.rep.num T (Hd.objIn [hT] x1 hT)) (ht1 : ∀ x, hT = some x → x.rep.refs = 1)
    (hu : u = T + 2 * P * e) (he1 : 1 ≤ e) (hP1 : 1 ≤ P) (hT1 : 1 ≤ T)
    (h18 : R 18 = BitVec.ofNat 64 (Hd.p x1 hW)) (h9 : R 9 = BitVec.ofNat 64 (x1.rep.scale * P))
    (h8 : R 8 = BitVec.ofNat 64 e) (h20 : R 20 = BitVec.ofNat 64 (Hd.p x1 hT))
    (h21 : R 21 = BitVec.ofNat 64 (x1.rep.scale * T))
    (h22 : R 22 = BitVec.ofNat 64 rs) (h24 : R 24 = BitVec.ofNat 64 nf)
    (hw8 : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 (Hd.p x1 hW))
    (hw0 : ldv .ld M (sp - 96) = BitVec.ofNat 64 (Hd.p x1 hT))
    (hexit : ∀ R' M' H' F' Pw' T' P', RaP2 S X Mt0 M' R0 R' sp W q H' F' A B x1 Pw' (some T') P' u 0 rs nf →
      DW live S Q 0x80006740#64 R' M') :
    DW live S Q 0x800066f0#64 R M := by
  have hPu : 2 * P ≤ u := by
    have : P ≤ P * e := Nat.le_mul_of_pos_right P he1
    rw [Nat.mul_assoc] at hu; omega
  refine ra_p2_sq hlive env hoom ra hb hown hzc hd hh hpw htm ht1 hP1 hPu h18 h9 h8 h20 h21 h22 h24
    hw8 hw0 ?_
  intro R1 M1 H1 F1 Pw1 st1
  refine ra_p2_tail hlive env hoom st1 (by rw [hu, Nat.mul_assoc]) he1 (by omega) hT1 ?_
    (fun R' M' H' F' Pw' hT' st' => hexit R' M' H' F' Pw' hT' _ st')
  intro R2 M2 H2 F2 Pw2 hT2 T2 st2 h18' hT2e he2
  have hinv := (Dc.BcModel.RaiseInv.step (u := u) (T := T) (P := P) (e := e) ⟨hu⟩).total
  rw [← hT2e] at hinv
  exact ra_p2_loop hlive env hoom hexit (e / 2) (2 * P) T2 st2 h18' hinv he2 (by omega)
    (by rw [hT2e]; split <;> omega)

/-- The frame through a store below the saved words (`power`, `temp`). -/
theorem RaAt.lowStore {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q a : Nat}
    {slots : List (Nat × Nat)} (cx : RaCtx S R0 sp W q) (h : RaAt S Mt0 M R0 R sp W q slots)
    (ha1 : sp - 96 ≤ a) (ha2 : a + 8 ≤ sp - 80) (v : BitVec 64)
    (hlo : ∀ p ∈ slots, 16 ≤ p.2 := by decide) :
    RaAt S Mt0 (writeLog M [(a, 8, v)]) R0 R sp W q slots := by
  ra_facts cx
  exact { h with
    saved := fun p hp => by
      rw [ldv_ld_miss _ _ (by have := hlo p hp; omega)]; exact h.saved p hp
    out := fun b hb hf => by
      rw [imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]; exact h.out b hb hf }

/-- `s5` saved at the second loop's entry. -/
theorem RaAt.saveS5 {S : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q : Nat}
    (cx : RaCtx S R0 sp W q) (h : RaAt S Mt0 M R0 R sp W q raSlots1) {v : BitVec 64}
    (hv : v = R0 21) :
    RaAt S Mt0 (writeLog M [(sp - 96 + 40, 8, v)]) R0 R sp W q raSlots2 := by
  ra_facts cx
  exact { h with
    saved := by rw [hv]; exact h.saved.store 21 40
    out := fun a ha hf => by
      rw [imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]; exact h.out a ha hf }

theorem RaPow.withRefs {a : Num} {m : Nat} {y : NumObj} (h : RaPow a m y) (k : Nat) :
    RaPow a m (y.withRefs k) :=
  ⟨h.num, h.norm, h.len, h.owns⟩

@[simp] theorem NumObj.withRefs_refs (x : NumObj) (k : Nat) : (x.withRefs k).rep.refs = k := rfl

@[simp] theorem NumObj.withRefs_p (x : NumObj) (k : Nat) : (x.withRefs k).rep.p = x.rep.p := rfl

/-- `temp = power` names the power object twice: one more reference. -/
def Hd.cp : Hd → List Hd
  | some P => [some (P.withRefs 2)]
  | none => [none, none]

/-- `power`'s handle among `Hd.cp`. -/
def Hd.cpW : Hd → Hd
  | some P => some (P.withRefs 2)
  | none => none

/-- The handles after `power`'s. -/
def Hd.cpRest : Hd → List Hd
  | some _ => []
  | none => [none]

theorem Hd.cp_eq (h : Hd) : Hd.cp h = [] ++ Hd.cpW h :: Hd.cpRest h := by cases h <;> rfl

theorem Hd.cp_drop {h : Hd} (hf : ∀ P, h = some P → P.rep.refs = 1) :
    [] ++ Hd.drop (Hd.cpW h) ++ Hd.cpRest h = [h] := by
  cases h with
  | none => rfl
  | some P =>
    simp only [Hd.cpW, Hd.cpRest, Hd.drop, NumObj.withRefs, List.nil_append, List.append_nil]
    rw [if_neg (by decide)]
    exact congrArg (fun x => [some x]) (NumObj.withRefs2_decRef (hf P rfl))

theorem Hd.cpW_p (x1 : NumObj) (h : Hd) : Hd.p x1 (Hd.cpW h) = Hd.p x1 h := by cases h <;> rfl

theorem Hd.cp_zero (h : Hd) : zeroCount (Hd.cp h) ≤ 2 := by cases h <;> simp [Hd.cp]

theorem RaPow.cp {a : Num} {m : Nat} {x1 : NumObj} {h : Hd} (hp : RaPow a m (Hd.objIn [h] x1 h)) :
    RaPow a m (Hd.objIn (Hd.cp h) x1 (Hd.cpW h)) := by
  cases h with
  | none => exact hp.withRefs _
  | some P => exact hp.withRefs _

theorem Hd.cp_owns {x1 : NumObj} {h : Hd} (hp : (Hd.objIn [h] x1 h).Owns) :
    ∀ x, some x ∈ Hd.cp h → x.Owns := by
  cases h with
  | none => intro x hx; simp [Hd.cp] at hx
  | some P => intro x hx; simp only [Hd.cp, List.mem_singleton, Option.some.injEq] at hx; subst hx; exact hp

theorem Hd.cpW_refs {h : Hd} : ∀ x, Hd.cpW h = some x → 1 ≤ x.rep.refs := by
  cases h with
  | none => intro x hx; cases hx
  | some P => intro x hx; cases hx; simp [NumObj.withRefs]

/-- The power object's extra reference among the handles. -/
theorem BcHeap.cpRefs {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {A B : List NumObj}
    {x1 : NumObj} {h : Hd} (hb : BcHeap S X M H F (KList [] [h] A B x1))
    (hf : ∀ P, h = some P → P.rep.refs = 1) (hr : x1.rep.refs + 2 < 2 ^ 31) :
    BcHeap S X (writeLog M [((Hd.objIn [h] x1 h).rep.p + 12, 4,
      BitVec.ofNat 64 ((Hd.objIn [h] x1 h).rep.refs + 1))]) H F (KList [] (Hd.cp h) A B x1) := by
  cases h with
  | none =>
    rw [show [none] = ([] : List Hd) ++ none :: [] from rfl, KList.split_none] at hb
    have := hb.setRefs (k := (x1.withRefs (x1.rep.refs + 1)).rep.refs + 1)
      (toNat_ofNat_mod32 (by simp only [NumObj.withRefs]; omega))
      (by simp only [NumObj.withRefs]; omega)
    rw [show Hd.cp none = ([] : List Hd) ++ none :: [none] from rfl, KList.split_none]
    simpa [zeroCount, NumObj.withRefs_withRefs, NumObj.withRefs_refs, Hd.objIn, temps,
      Nat.add_assoc] using this
  | some P =>
    rw [show [some P] = ([] : List Hd) ++ some P :: [] from rfl, KList.split_some] at hb
    have := hb.setRefs (k := P.rep.refs + 1) (toNat_ofNat_mod32 (by rw [hf P rfl]; omega))
      (by rw [hf P rfl]; omega)
    simp only [Hd.objIn]
    rw [hf P rfl] at this ⊢
    rw [show Hd.cp (some P) = ([] : List Hd) ++ some (P.withRefs 2) :: [] from rfl, KList.split_some]
    simpa [zeroCount, Hd.objIn, temps] using this

/-- The state at `0x800068cc` (the exponent was `2^i`): `temp` and `power`
both the power object. -/
structure RaC (S : Nat → Prop) (X : Raws) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat) (H : Heap)
    (F : List Blk) (A B : List NumObj) (x1 : NumObj) (hP : Hd) (i rs nf : Nat) : Prop where
  ra : RaAt S Mt0 M R0 R sp W q raSlots1
  r21 : R 21 = R0 21
  heap : BcHeap S X M H F (KList [] (Hd.cp hP) A B x1)
  pow : RaPow x1.rep.num (2 ^ i) (Hd.objIn [hP] x1 hP)
  fresh : ∀ P, hP = some P → P.rep.refs = 1
  base : hP = none → i = 0
  r18 : R 18 = BitVec.ofNat 64 (Hd.p x1 hP)
  r22 : R 22 = BitVec.ofNat 64 rs
  r24 : R 24 = BitVec.ofNat 64 nf
  w8 : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 (Hd.p x1 hP)

/-- **`temp = power`** from `0x800066d0` (the first loop's odd exponent `e`,
`a5` the power's reference count): `e = 1` ends at `0x800068cc`; otherwise
the second loop to `0x80006740`. -/
theorem ra_copy {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q u i e rs nf : Nat} {H : Heap}
    {F : List Blk} {A B : List NumObj} {x1 z o : NumObj} {hP : Hd}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u) (hoom : RaOom live S Q Mt0 sp W q)
    (st : RaP1 S X Mt0 M R0 R sp W q H F A B x1 hP i e rs nf) (hu : u = 2 ^ i * e)
    (he : e % 2 = 1) (h15 : R 15 = BitVec.ofNat 64 (Hd.objIn [hP] x1 hP).rep.refs)
    (hpow2 : ∀ R' M' H' F', RaC S X Mt0 M' R0 R' sp W q H' F' A B x1 hP i rs nf → e = 1 →
      DW live S Q 0x800068cc#64 R' M')
    (hexit : ∀ R' M' H' F' Pw' T' P', RaP2 S X Mt0 M' R0 R' sp W q H' F' A B x1 Pw' (some T') P' u 0 rs nf →
      DW live S Q 0x80006740#64 R' M') :
    DW live S Q 0x800066d0#64 R M := by
  have cx := env.cx
  ra_facts cx
  have hsf := cx.frame
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.ra
  have h2 := ra.r2
  have hym := Hd.objIn_mem (hs := [hP]) (List.mem_singleton_self hP) [] A B x1
  have h18 : R 18 = BitVec.ofNat 64 (Hd.objIn [hP] x1 hP).rep.p := by
    rw [Hd.objIn_p]; exact st.r18
  have hrc : (Hd.objIn [hP] x1 hP).rep.refs + 1 < 2 ^ 31 := by
    cases hP with
    | some P => simp only [Hd.objIn, st.fresh P rfl]; omega
    | none => have := env.refs1; simp only [Hd.objIn, NumObj.withRefs, zeroCount]; omega
  generalize hyd : Hd.objIn [hP] x1 hP = y at hym h18 h15 hrc
  have hn := hb.nums y hym
  num_facts hn
  have he64 : e < 2 ^ 64 := by
    have : u ≤ u * (x1.rep.len + x1.rep.scale + 1) := Nat.le_mul_of_pos_right u (by omega)
    have : e ≤ u := hu ▸ Nat.le_mul_of_pos_left e (Nat.two_pow_pos i)
    have := env.size
    have : u * (x1.rep.len + x1.rep.scale + 1) < 2 ^ 24 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ u)) env.size
    omega
  have hsr : e % 2 ^ 64 / 2 ^ 1 = e / 2 := by rw [Nat.mod_eq_of_lt he64, Nat.pow_one]
  have hsx : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (y.rep.refs + 1))) =
      BitVec.ofNat 64 (y.rep.refs + 1) := sxw_ofNat hrc
  have hr2 : x1.rep.refs + 2 < 2 ^ 31 := env.refs1
  have hb2 := hb.cpRefs st.fresh hr2
  rw [hyd] at hb2
  have hyp : y.rep.p = Hd.p x1 hP := by rw [← hyd, Hd.objIn_p]
  have hb3 := hb2.out_frame (MemOnly.store _ (sp - 96) 8 (BitVec.ofNat 64 y.rep.p))
    (fun a ha => outHeap_of_ge (by simp only [heapEnd] at *; omega))
  have ra3 := ((ra.heapStore (a := y.rep.p + 12) (w := 4)
    (v := BitVec.ofNat 64 (y.rep.refs + 1)) (by have := hn.shape.pLo; omega)
    (by have := hn.shape.pHi; omega) (by simp only [heapEnd]; omega)).lowStore
    cx (a := sp - 96) (by omega) (by omega) (BitVec.ofNat 64 y.rep.p)).regsA
    (ks := [15, 8]) (R' := upd (upd R 15 (BitVec.ofNat 64 (y.rep.refs + 1))) 8 (BitVec.ofNat 64 (e / 2)))
    (by keeps_tac Keeps.refl _ _)
  have hpH : y.rep.p + 16 ≤ sp - 96 := by
    have := hn.shape.pHi; simp only [heapEnd] at this; omega
  bc_run hlive hS [h2, h15, h18, st.r8, hsx, shr_ofNat, hsr] at 0x800066f0 0x800068cc
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals intro hz
  · have he1 : e = 1 := by
      have : e / 2 = 0 := by
        have := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; simpa using this
      omega
    refine hpow2 _ _ H F
      { ra := ra3
        r21 := by bsimp [st.r21]
        heap := hb3
        pow := st.pow
        fresh := st.fresh
        base := st.base
        r18 := by bsimp [st.r18]
        r22 := by bsimp [st.r22]
        r24 := by bsimp [st.r24]
        w8 := by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact st.w8 } he1
  · have he2 : 1 ≤ e / 2 := by
      rcases Nat.eq_zero_or_pos (e / 2) with h | h
      · exact absurd (by rw [h]) hz
      · exact h
    have h2' : (upd (upd R 15 (BitVec.ofNat 64 (y.rep.refs + 1))) 8 (BitVec.ofNat 64 (e / 2))) 2 =
        BitVec.ofNat 64 (sp - 96) := by bsimp [h2]
    bc_run hlive hS [h2'] at 0x800066f0
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    have hb4 := hb3.out_frame (MemOnly.store _ (sp - 96 + 40) 8 (R 21))
      (fun a ha => outHeap_of_ge (by simp only [heapEnd] at *; omega))
    rw [Hd.cp_eq] at hb4
    have ra4 := (ra3.saveS5 cx st.r21).regsA (ks := [20, 21])
      (R' := upd (upd (upd (upd R 15 (BitVec.ofNat 64 (y.rep.refs + 1))) 8 (BitVec.ofNat 64 (e / 2)))
        20 (R 18)) 21 (R 9)) (by keeps_tac Keeps.refl _ _)
    have hinv := (Dc.BcModel.RaiseInv.init (u := u) (i := i) (e := e / 2) (by
      rw [hu]; congr 1; omega)).total
    have hp1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    refine ra_p2_first (hs1 := []) (hW := Hd.cpW hP) (hs2 := Hd.cpRest hP) (hT := hP) hlive env hoom
      ra4 hb4 (by rw [← Hd.cp_eq]; exact Hd.cp_owns st.pow.owns)
      (by rw [← Hd.cp_eq]; exact Hd.cp_zero hP) (Hd.cp_drop st.fresh) Hd.cpW_refs
      (by rw [← Hd.cp_eq]; exact st.pow.cp) st.pow st.fresh hinv he2 hp1 hp1
      (by bsimp [st.r18, Hd.cpW_p]) (by bsimp [st.r9]) (by bsimp []) (by bsimp [st.r18])
      (by bsimp [st.r9]) (by bsimp [st.r22]) (by bsimp [st.r24])
      (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
        Hd.cpW_p]; exact st.w8)
      (by rw [ldv_ld_miss _ _ (by omega), ldv_store_hit, hyp]) hexit

/-- **Both loops** from `0x8000668c` (`power = num1` with one more
reference, the exponent `u` in `s0`): to `0x800068cc` for `u = 2^i`, or to
the second loop's exit at `0x80006740`. -/
theorem ra_loops {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q u rs nf : Nat} {H : Heap}
    {F : List Blk} {A B : List NumObj} {x1 z o : NumObj}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u) (hoom : RaOom live S Q Mt0 sp W q)
    (ra : RaAt S Mt0 M R0 R sp W q raSlots1) (h21 : R 21 = R0 21)
    (hb : BcHeap S X M H F (A ++ x1 :: B))
    (h18 : R 18 = BitVec.ofNat 64 x1.rep.p) (h9 : R 9 = BitVec.ofNat 64 x1.rep.scale)
    (h8 : R 8 = BitVec.ofNat 64 u) (h22 : R 22 = BitVec.ofNat 64 rs)
    (h24 : R 24 = BitVec.ofNat 64 nf)
    (hpow2 : ∀ R' M' H' F' hP i, RaC S X Mt0 M' R0 R' sp W q H' F' A B x1 hP i rs nf → u = 2 ^ i →
      DW live S Q 0x800068cc#64 R' M')
    (hexit : ∀ R' M' H' F' Pw' T' P', RaP2 S X Mt0 M' R0 R' sp W q H' F' A B x1 Pw' (some T') P' u 0 rs nf →
      DW live S Q 0x80006740#64 R' M') :
    DW live S Q 0x8000668c#64 R M := by
  have cx := env.cx
  ra_facts cx
  have hsf := cx.frame
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have h2 := ra.r2
  have hxm : x1 ∈ A ++ x1 :: B := List.mem_append_right _ List.mem_cons_self
  have hn := hb.nums x1 hxm
  num_facts hn
  have hrf := hn.refs
  have hr1 := env.refs1
  have hu64 : u < 2 ^ 64 := by
    have : u ≤ u * (x1.rep.len + x1.rep.scale + 1) := Nat.le_mul_of_pos_right u (by omega)
    have : u * (x1.rep.len + x1.rep.scale + 1) < 2 ^ 24 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ u)) env.size
    omega
  have hsx : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (x1.rep.refs + 1))) =
      BitVec.ofNat 64 (x1.rep.refs + 1) := sxw_ofNat (by omega)
  have hpH : x1.rep.p + 16 ≤ sp - 96 := by
    have := hn.shape.pHi; simp only [heapEnd] at this; omega
  have hb1 := (hb.out_frame (MemOnly.store _ (sp - 96 + 8) 8 (BitVec.ofNat 64 x1.rep.p))
    (fun a ha => outHeap_of_ge (by simp only [heapEnd] at *; omega))).setRefs (k := x1.rep.refs + 1)
    (toNat_ofNat_mod32 (by omega)) (by omega)
  have hp0 : RaPow x1.rep.num (2 ^ 0) (Hd.objIn [none] x1 none) :=
    ⟨by rw [Nat.pow_zero, Dc.BcModel.powRaise_one]; rfl, env.n1, env.len1,
      env.owns x1 hxm⟩
  have st : ∀ R', Keeps [14, 15] R' R → R' 8 = BitVec.ofNat 64 u →
      RaP1 S X Mt0 (writeLog (writeLog M [(sp - 96 + 8, 8, BitVec.ofNat 64 x1.rep.p)])
        [(x1.rep.p + 12, 4, BitVec.ofNat 64 (x1.rep.refs + 1))]) R0 R' sp W q H F A B x1 none 0 u rs nf :=
    fun R' hk h8' =>
    { ra := ((ra.lowStore cx (a := sp - 96 + 8) (by omega) (by omega)
        (BitVec.ofNat 64 x1.rep.p)).heapStore (a := x1.rep.p + 12) (w := 4)
        (v := BitVec.ofNat 64 (x1.rep.refs + 1))
        (by have := hn.shape.pLo; omega) (by have := hn.shape.pHi; omega)
        (by simp only [heapEnd]; omega)).regsA hk
      r21 := by rw [hk.get 21 (by decide)]; exact h21
      heap := by
        simp only [KList, zeroCount, temps, List.filterMap, List.nil_append]; exact hb1
      pow := hp0
      fresh := fun P h => nomatch h
      base := fun _ => rfl
      r18 := by rw [hk.get 18 (by decide)]; exact h18
      r9 := by rw [hk.get 9 (by decide), Nat.pow_zero, Nat.mul_one]; exact h9
      r8 := h8'
      r22 := by rw [hk.get 22 (by decide)]; exact h22
      r24 := by rw [hk.get 24 (by decide)]; exact h24
      w8 := by rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _ }
  have hcopy : ∀ R' M' H' F' hP i e, RaP1 S X Mt0 M' R0 R' sp W q H' F' A B x1 hP i e rs nf →
      u = 2 ^ i * e → e % 2 = 1 →
      R' 15 = BitVec.ofNat 64 (Hd.objIn [hP] x1 hP).rep.refs → DW live S Q 0x800066d0#64 R' M' :=
    fun R' M' H' F' hP i e st' hu he h15 =>
      ra_copy hlive env hoom st' hu he h15
        (fun R'' M'' H'' F'' sc he1 => hpow2 R'' M'' H'' F'' hP i sc (by rw [hu, he1, Nat.mul_one]))
        hexit
  bc_run hlive hS [h2, h18, hrf, hsx, h8, and1_ofNat hu64] at 0x800066a4 0x800066d0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals intro hz
  all_goals rcases Nat.mod_two_eq_zero_or_one u with hpar | hpar <;> rw [hpar] at hz ⊢
  all_goals first | exact absurd hz (by decide) | skip
  · exact hcopy _ _ H F none 0 u (st _ (by keeps_tac Keeps.refl _ _) (by bsimp [h8]))
      (by rw [Nat.pow_zero, Nat.one_mul]) hpar (by bsimp [Hd.objIn, zeroCount, NumObj.withRefs_refs])
  · refine ra_p1_loop hlive env hoom ?_ u 0 (st _ (by keeps_tac Keeps.refl _ _) (by bsimp [h8]))
      (by rw [Nat.pow_zero, Nat.one_mul]) hpar
    intro R' M' H' F' P i e st' hu' he'
    have cx' := env.cx
    have hb' := st'.heap
    have hS' : HeapOwn S := fun a h1 h2 => hb'.heap.own a h1 h2
    have hPm : P ∈ KList [] [some P] A B x1 :=
      Hd.objIn_mem (hs := [some P]) (List.mem_singleton_self _) [] A B x1
    have hPn := hb'.nums _ hPm
    num_facts hPn
    have hPr := hPn.refs
    have h18' := st'.r18
    simp only [Hd.p] at h18'
    bc_run hlive hS' [h18', hPr] at 0x800066d0
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine hcopy _ M' H' F' (some P) i e ?_ hu' he' ?_
    · exact { st' with
        ra := st'.ra.regsA (ks := [15]) (by keeps_tac Keeps.refl _ _)
        r21 := by bsimp [st'.r21]
        r18 := by bsimp [st'.r18]
        r9 := by bsimp [st'.r9]
        r8 := by bsimp [st'.r8]
        r22 := by bsimp [st'.r22]
        r24 := by bsimp [st'.r24] }
    · bsimp [Hd.objIn]

end Dc.Mach
