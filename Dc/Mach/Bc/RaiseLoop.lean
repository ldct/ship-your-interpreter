import Dc.Mach.Bc.RaiseExit

/-!
# `bc_raise`'s squaring loops (`0x800066a4` to `0x80006740`)

    66a4 power = power², pwrscale doubled         (while the exponent is even)
    66d0 temp = power (one more reference); exponent >>= 1; zero → 68cc
    66f0 power = power²; odd bit: temp = temp · power at calcscale += pwrscale

The handles (`KaraState.lean`) are `power`'s alone in the first loop, then
`temp` and `power`; `x1` (`num1`) carries a reference for each `none`.

- `NumObj.inK`: the caller's number as the handles' heap holds it.
- `RaCst`: `_one_`, `_zero_` and the multiplication base in memory.
- `RaPow a m y`: `y` holds `bc_raise`'s `a ^ m` (`Num.powRaise`).
- `RaP1`/`ra_p1_body`/`ra_p1_loop`: the first loop.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## The caller's numbers among the handles -/

/-- The caller's `y` in `KList [] hs A B x1`: `x1` carries the `c`
references of the handles naming it. -/
noncomputable def NumObj.inK (y x1 : NumObj) (c : Nat) : NumObj :=
  open Classical in if y = x1 then x1.withRefs (x1.rep.refs + c) else y

theorem NumObj.inK_mem {A B : List NumObj} {x1 y : NumObj} (c : Nat) (hy : y ∈ A ++ x1 :: B) :
    y.inK x1 c ∈ A ++ x1.withRefs (x1.rep.refs + c) :: B := by
  unfold NumObj.inK
  split
  · exact List.mem_append_right _ List.mem_cons_self
  · rename_i hne
    rcases List.mem_append.mp hy with h | h
    · exact List.mem_append_left _ h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h hne
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- In the handles' heap. -/
theorem NumObj.inK_memK {A B : List NumObj} {x1 y : NumObj} (hs : List Hd) (hy : y ∈ A ++ x1 :: B) :
    y.inK x1 (zeroCount hs) ∈ KList [] hs A B x1 := by
  have h := NumObj.inK_mem (zeroCount hs) hy
  simp only [KList, List.nil_append, List.append_assoc]
  exact List.mem_append_right _ h

/-- The same number up to its reference count. -/
theorem NumObj.inK_rep (y x1 : NumObj) (c : Nat) :
    ∃ r, (y.inK x1 c).rep = { y.rep with refs := r } ∧ y.rep.refs ≤ r ∧ r ≤ y.rep.refs + c := by
  unfold NumObj.inK; split
  · rename_i e; subst e; exact ⟨_, rfl, by omega, by omega⟩
  · exact ⟨y.rep.refs, rfl, Nat.le_refl _, by omega⟩

theorem NumObj.inK_p (y x1 : NumObj) (c : Nat) : (y.inK x1 c).rep.p = y.rep.p := by
  obtain ⟨r, e, -, -⟩ := y.inK_rep x1 c; rw [e]

theorem NumObj.inK_num (y x1 : NumObj) (c : Nat) :
    (y.inK x1 c).rep.num = y.rep.num := by
  obtain ⟨r, e, -, -⟩ := y.inK_rep x1 c; rw [e]; rfl

theorem NumObj.inK_len (y x1 : NumObj) (c : Nat) :
    (y.inK x1 c).rep.len = y.rep.len := by
  obtain ⟨r, e, -, -⟩ := y.inK_rep x1 c; rw [e]

theorem NumObj.inK_scale (y x1 : NumObj) (c : Nat) :
    (y.inK x1 c).rep.scale = y.rep.scale := by
  obtain ⟨r, e, -, -⟩ := y.inK_rep x1 c; rw [e]

/-- `_zero_` as the handles' heap holds it. -/
theorem KZero.inK {M : Mem} {z : NumObj} {k : Nat} (x1 : NumObj) (c : Nat) (h : KZero M z (k + c)) :
    KZero M (z.inK x1 c) k := by
  obtain ⟨r, e, h1, h2⟩ := z.inK_rep x1 c
  have := h.room
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [e]
  · exact h.glob
  · exact h.len
  · exact h.scale
  · exact h.ds
  · exact h.neg
  · have := h.refs; omega
  · omega

/-! ## Constants -/

/-- `_one_`, `_zero_` and the multiplication base, as `bc_raise` reads them. -/
structure RaCst (M : Mem) (o z : NumObj) : Prop where
  one : ldv .ld M oneAddr = BitVec.ofNat 64 o.rep.p
  zero : KZero M z (2 ^ 30)
  mulBase : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80

theorem RaCst.of_args {S : Nat → Prop} {Mt0 : Mem} {k : Nat} {L : List NumObj}
    {x1 x2 z o : NumObj} (ha : RaArgs S Mt0 L x1 x2 z o k) : RaCst Mt0 o z :=
  ⟨ha.one, ha.zero, ha.mulBase⟩

/-- The constants survive a run that changes only the heap and the window. -/
theorem RaCst.transport {S : Nat → Prop} {Mt0 M : Mem} {R0 : Nat → BitVec 64} {sp W q : Nat}
    {z o : NumObj} (cx : RaCtx S R0 sp W q) (ha : RaCst Mt0 o z)
    (hout : ∀ a, OutHeap a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a) : RaCst M o z := by
  have hab := cx.above
  simp only [heapEnd] at hab
  have hc : ∀ a, 0x8001cd40 ≤ a → a < 0x8001cdd0 → ¬ (0x8001cd48 ≤ a ∧ a < 0x8001cd58) →
      ¬ (0x8001cdb0 ≤ a ∧ a < 0x8001cdb8) → imgM M a = imgM Mt0 a := fun a h1 h2 h3 h4 =>
    hout a (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [frameIn]; omega)
  have hz := ha.zero
  refine ⟨?_, ⟨?_, hz.len, hz.scale, hz.ds, hz.neg, hz.refs, hz.room⟩, ?_⟩
  · rw [ldv_congr .ld fun j hj => hc _ (by simp only [widthOfM, oneAddr] at hj ⊢; omega)
      (by simp only [widthOfM, oneAddr] at hj ⊢; omega) (by simp only [widthOfM, oneAddr] at hj ⊢; omega)
      (by simp only [widthOfM, oneAddr] at hj ⊢; omega)]
    exact ha.one
  · rw [ldv_congr .ld fun j hj => hc _ (by simp only [widthOfM, zeroAddr] at hj ⊢; omega)
      (by simp only [widthOfM, zeroAddr] at hj ⊢; omega) (by simp only [widthOfM, zeroAddr] at hj ⊢; omega)
      (by simp only [widthOfM, zeroAddr] at hj ⊢; omega)]
    exact hz.glob
  · rw [ldv_congr .lw fun j hj => hc _ (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)
      (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)
      (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)
      (by simp only [widthOfM, mulBaseAddr] at hj ⊢; omega)]
    exact ha.mulBase

/-- Every number of the handles' heap owns its digits. -/
theorem KList.owns {hs : List Hd} {A B : List NumObj} {x1 : NumObj}
    (hT : ∀ x, some x ∈ hs → x.Owns) (hL : ∀ y ∈ A ++ x1 :: B, y.Owns) :
    ∀ y ∈ KList [] hs A B x1, y.Owns := by
  intro y hy
  simp only [KList, List.nil_append, List.append_assoc] at hy
  rcases List.mem_append.mp hy with h | h
  · obtain ⟨hd, hm, e⟩ := List.mem_filterMap.mp h
    cases hd with
    | none => cases e
    | some x => cases e; exact hT _ hm
  · rcases List.mem_append.mp h with h | h
    · exact hL y (List.mem_append_left _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact hL x1 (List.mem_append_right _ List.mem_cons_self)
      · exact hL y (List.mem_append_right _ (List.mem_cons_of_mem _ h))

/-- Through register changes inside `raAll`, off `sp` and `s7`. -/
theorem RaAt.regsA {S : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W q : Nat}
    {slots : List (Nat × Nat)} {ks : List Nat} (h : RaAt S Mt0 M R0 R sp W q slots)
    (hk : Keeps ks R' R) (hks : ∀ z ∈ ks, z ∈ raAll ∧ z ≠ 2 ∧ z ≠ 23 := by decide) :
    RaAt S Mt0 M R0 R' sp W q slots :=
  { h with
    r2 := by rw [hk.get 2 fun hm => (hks 2 hm).2.1 rfl]; exact h.r2
    keep := (hk.mono fun z hz => (hks z hz).1).trans h.keep
    r23 := by rw [hk.get 23 fun hm => (hks 23 hm).2.2 rfl]; exact h.r23 }

/-! ## Powers -/

/-- `y` holds `bc_raise`'s `a ^ m`: normalized, an integer digit, an owner. -/
structure RaPow (a : Num) (m : Nat) (y : NumObj) : Prop where
  num : y.rep.num = Num.powRaise a m
  norm : y.rep.Norm
  len : 1 ≤ y.rep.len
  owns : y.Owns

/-- A power's digits: at most `m` times the base's, and one. -/
theorem RaPow.size {a : Num} {m : Nat} {y x1 : NumObj} (h : RaPow a m y) (hs : NumShape y.rep)
    (hx : NumShape x1.rep) (ha : x1.rep.num = a) (hm : 1 ≤ m) :
    y.rep.len + y.rep.scale ≤ m * (x1.rep.len + x1.rep.scale) + 1 := by
  have hmag : y.rep.num.mag = a.mag ^ m := by rw [h.num, Dc.BcModel.powRaise_mag]
  have hsc : y.rep.scale = a.scale * m := by
    rw [← NumRep.num_scale, h.num, Dc.BcModel.powRaise_scale]
  have hxl := NumRep.mag_lt hx
  have ham : a.mag < 10 ^ (x1.rep.len + x1.rep.scale) := by rw [← ha, NumRep.num_mag]; exact hxl
  have hE : y.rep.num.mag < 10 ^ (m * (x1.rep.len + x1.rep.scale)) := by
    rw [hmag, Nat.mul_comm, Nat.pow_mul]
    exact Nat.pow_lt_pow_left ham (by omega)
  have := NumRep.size_le hs h.norm hE
  have has : a.scale = x1.rep.scale := by rw [← ha, NumRep.num_scale]
  rw [hsc, has] at this ⊢
  have : x1.rep.scale * m ≤ m * (x1.rep.len + x1.rep.scale) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- A squared or multiplied power. -/
theorem RaPow.mul {a : Num} {m n k : Nat} {y : NumObj} (hk : a.scale * m + a.scale * n ≤ k)
    (hmn : 2 ≤ m + n) (hy : NewNum (Num.mul (Num.powRaise a m) (Num.powRaise a n) k) y) :
    RaPow a (m + n) y := by
  refine ⟨?_, hy.norm, hy.pos, hy.owns⟩
  rw [hy.num, Dc.BcModel.mul_powRaise a m n k hk]
  unfold Num.powRaise; rw [if_neg (by omega)]

/-- `andi rd, rs, 1` of a natural. -/
theorem and1_ofNat {e : Nat} (h : e < 2 ^ 64) :
    BitVec.ofNat 64 e &&& 1#64 = BitVec.ofNat 64 (e % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [and1_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  omega

/-! ## The fixed context of the loops -/

/-- What the loops use of the operands: the caller's heap `A ++ x1 :: B` of
owners with `_zero_` and `_one_` in it, `num1` (`x1`) normalized with an
integer digit, the exponent `u`'s powers small. -/
structure RaEnv (S : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64) (sp W q : Nat)
    (A B : List NumObj) (x1 z o : NumObj) (u : Nat) : Prop where
  cx : RaCtx S R0 sp W q
  owns : ∀ y ∈ A ++ x1 :: B, y.Owns
  mz : z ∈ A ++ x1 :: B
  mo : o ∈ A ++ x1 :: B
  cst : RaCst Mt0 o z
  n1 : x1.rep.Norm
  len1 : 1 ≤ x1.rep.len
  r1 : 1 ≤ x1.rep.refs
  refs1 : x1.rep.refs + 2 < 2 ^ 31
  u1 : 1 ≤ u
  size : (u + 1) * (x1.rep.len + x1.rep.scale + 1) < 2 ^ 24

/-- The first loop's state at `0x800066a4` (and its exit `0x800066cc`):
`power` the handle `hP` holding `a ^ 2^i`, `pwrscale` (`s1`) its scale, the
exponent left `e` in `s0`, `rscale` and the sign flag in `s6`, `s8`. -/
structure RaP1 (S : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W q : Nat) (H : Heap)
    (F : List Blk) (A B : List NumObj) (x1 : NumObj) (hP : Hd) (i e rs nf : Nat) : Prop where
  ra : RaAt S Mt0 M R0 R sp W q raSlots1
  r21 : R 21 = R0 21
  heap : BcHeap S M H F (KList [] [hP] A B x1)
  pow : RaPow x1.rep.num (2 ^ i) (Hd.objIn [hP] x1 hP)
  fresh : ∀ P, hP = some P → P.rep.refs = 1
  base : hP = none → i = 0
  r18 : R 18 = BitVec.ofNat 64 (Hd.p x1 hP)
  r9 : R 9 = BitVec.ofNat 64 (x1.rep.scale * 2 ^ i)
  r8 : R 8 = BitVec.ofNat 64 e
  r22 : R 22 = BitVec.ofNat 64 rs
  r24 : R 24 = BitVec.ofNat 64 nf
  w8 : ldv .ld M (sp - 96 + 8) = BitVec.ofNat 64 (Hd.p x1 hP)

/-- **One squaring of the first loop** from `0x800066a4` (`e` even):
`power = power²` at the doubled scale, `e >>= 1`, then the loop again or its
exit. -/
theorem ra_p1_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W q u i e rs nf : Nat} {H : Heap}
    {F : List Blk} {A B : List NumObj} {x1 z o : NumObj} {hP : Hd}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u) (hoom : RaOom live S Q Mt0 sp W q)
    (st : RaP1 S Mt0 M R0 R sp W q H F A B x1 hP i e rs nf) (hu : u = 2 ^ i * e)
    (he : e % 2 = 0)
    (hnext : ∀ R' M' H' F' P, RaP1 S Mt0 M' R0 R' sp W q H' F' A B x1 (some P) (i + 1) (e / 2) rs nf →
      e / 2 % 2 = 0 → DW live S Q 0x800066a4#64 R' M')
    (hexit : ∀ R' M' H' F' P, RaP1 S Mt0 M' R0 R' sp W q H' F' A B x1 (some P) (i + 1) (e / 2) rs nf →
      e / 2 % 2 = 1 → DW live S Q 0x800066cc#64 R' M') :
    DW live S Q 0x800066a4#64 R M := by
  have cx := env.cx
  ra_facts cx
  have hsf := cx.frame
  have hal := cx.al
  have hb := st.heap
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have ra := st.ra
  have h2 := ra.r2
  have hcs := env.cst.transport cx ra.out
  have hu1 := env.u1
  have hsz := env.size
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with h | h
    · have : e = 0 := by omega
      subst this; simp at hu; omega
    · exact h
  have hpi : 2 ^ i ≤ u := by rw [hu]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hPm := Hd.objIn_mem (hs := [hP]) (List.mem_singleton_self hP) [] A B x1
  have hPs := (hb.nums _ hPm).shape
  have hx1m : x1.withRefs (x1.rep.refs + zeroCount [hP]) ∈ KList [] [hP] A B x1 := by
    simp only [KList, List.nil_append, List.append_assoc]
    exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)
  have hx1s : NumShape x1.rep := by
    have s := (hb.nums _ hx1m).shape
    exact ⟨s.dsLen, s.dig, s.size, by have := env.refs1; omega, s.pAl, s.pLo, s.pHi, s.ptrLe,
      s.vLo, s.vHi, s.sep, s.emptyScale, s.emptyIn⟩
  have hpz := st.pow.size hPs hx1s rfl (Nat.one_le_two_pow)
  have hLm : 2 ^ i * (x1.rep.len + x1.rep.scale) ≤ u * (x1.rep.len + x1.rep.scale) :=
    Nat.mul_le_mul_right _ hpi
  have hLu : u * (x1.rep.len + x1.rep.scale + 1) < 2 ^ 24 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ u)) hsz
  have hLL : u * (x1.rep.len + x1.rep.scale) ≤ u * (x1.rep.len + x1.rep.scale + 1) :=
    Nat.mul_le_mul_left _ (Nat.le_succ _)
  have hsa : x1.rep.scale * 2 ^ (i + 1) ≤ 2 * (u * (x1.rep.len + x1.rep.scale + 1)) := by
    have h1 : 2 ^ i * x1.rep.scale ≤ u * (x1.rep.len + x1.rep.scale + 1) :=
      Nat.mul_le_mul hpi (by omega)
    have h2 : x1.rep.scale * 2 ^ (i + 1) = 2 * (2 ^ i * x1.rep.scale) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mul_comm x1.rep.scale, Nat.mul_assoc]
    omega
  have hown : ∀ y ∈ KList [] [hP] A B x1, y.Owns := KList.owns (fun x hx => by
    rw [List.mem_singleton] at hx; subst hx; exact st.pow.owns) env.owns
  have hzk : KZero M (z.inK x1 (zeroCount [hP]))
      (4 * ((Hd.objIn [hP] x1 hP).rep.len + (Hd.objIn [hP] x1 hP).rep.scale +
        ((Hd.objIn [hP] x1 hP).rep.len + (Hd.objIn [hP] x1 hP).rep.scale)) + 8) :=
    KZero.inK x1 _ (hcs.zero.mono (by cases hP <;> simp only [zeroCount_none, zeroCount_some,
      zeroCount_nil] <;> omega))
  have hl9 : x1.rep.scale * 2 ^ i * 2 ^ 1 < 2 ^ 31 := by rw [Nat.mul_assoc, ← Nat.pow_add]; omega
  bc_run hlive hS [h2, st.r18, st.r9, slliw_ofNat hl9] at 0x8000573c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine ra_mulK (hs1 := []) (h := hP) (hs2 := []) (o := 8) (u1 := Hd.objIn [hP] x1 hP)
    (u2 := Hd.objIn [hP] x1 hP) (z := z.inK x1 (zeroCount [hP]))
    (k := x1.rep.scale * 2 ^ i * 2 ^ 1) hlive cx hoom.dm (.inr rfl) ra.out hb hown env.r1
    (fun x hx => Nat.le_of_eq (st.fresh x hx).symm) ⟨hPm, hPm, NumObj.inK_memK [hP] env.mz,
      by have := st.pow.len; omega, by have := st.pow.len; omega, by omega, hl9, hzk,
      hcs.mulBase⟩ st.w8 (by bsimp [h2]) (by bsimp []; try decide)
    (by bsimp [st.r18, Hd.objIn_p]) (by bsimp [st.r18, Hd.objIn_p]) (by bsimp [h2])
    (by bsimp []) ?_
  intro R1 M1 H1 F1 y hk1 hb1 hmr hout1
  have hdrop : Hd.drop hP = [] := by
    cases hP with
    | none => rfl
    | some P => simp only [Hd.drop, st.fresh P rfl, ite_true]
  rw [List.nil_append, hdrop, List.nil_append] at hb1
  have hrA : RaAt S Mt0 M1 R0 R1 sp W q raSlots1 :=
    (ra.regsA (ks := [1, 9, 10, 11, 12, 13]) (by keeps_tac Keeps.refl _ _)).call
      (hsp := by omega) (hW := by omega) (hkp := hk1.mono (by decide))
      (hag := fun a h1 h2' h3 => hout1 a h1 (fun h => h2' ⟨by have := h.1; omega,
        by have := h.2; omega⟩) h3)
      (hst := fun a h1 _ => outHeap_of_ge (by have := cx.above; omega))
  have hpow : RaPow x1.rep.num (2 ^ (i + 1)) y := by
    have := RaPow.mul (a := x1.rep.num) (m := 2 ^ i) (n := 2 ^ i) (k := x1.rep.scale * 2 ^ i * 2 ^ 1) (by
      rw [NumRep.num_scale, Nat.pow_one]; omega) (by have := Nat.one_le_two_pow (n := i); omega)
      (by rw [← st.pow.num]; exact hmr.toNewNum)
    rwa [← Nat.two_mul, ← Nat.pow_succ'] at this
  have heu : e ≤ u := hu ▸ Nat.le_mul_of_pos_left e (Nat.two_pow_pos i)
  have hu24 : u < 2 ^ 24 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right u (by omega)) hLu
  have he1 : e < 2 ^ 64 := by omega
  have h8' : R1 8 = BitVec.ofNat 64 e := by rw [hk1.get 8 (by decide)]; bsimp [st.r8]
  have h2' := hrA.r2
  bsimp []
  have hsc : x1.rep.scale * 2 ^ i * 2 ^ 1 = x1.rep.scale * 2 ^ (i + 1) := by
    rw [Nat.pow_succ 2 i, Nat.pow_one, Nat.mul_assoc]
  have st' : ∀ v, RaP1 S Mt0 M1 R0 (upd (upd (upd R1 8 (BitVec.ofNat 64 (e / 2))) 15 v) 18
      (BitVec.ofNat 64 y.rep.p)) sp W q H1 F1 A B x1 (some y) (i + 1) (e / 2) rs nf := fun v =>
    { ra := hrA.regsA (ks := [8, 15, 18]) (by keeps_tac Keeps.refl _ _)
      r21 := by bsimp []; rw [hk1.get 21 (by decide)]; bsimp [st.r21]
      heap := hb1
      pow := hpow
      fresh := fun P hP' => by cases hP'; exact hmr.refs
      base := fun h => nomatch h
      r18 := by bsimp [Hd.p]
      r9 := by bsimp []; rw [hk1.get 9 (by decide), ← hsc]; bsimp []
      r8 := by bsimp []
      r22 := by bsimp []; rw [hk1.get 22 (by decide)]; bsimp [st.r22]
      r24 := by bsimp []; rw [hk1.get 24 (by decide)]; bsimp [st.r24]
      w8 := hmr.slot }
  bc_run hlive hS [h8', h2', hmr.slot, shr_ofNat, and1_ofNat (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) he1)]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals
    intro hz
    rw [show e % 2 ^ 64 / 2 ^ 1 = e / 2 by rw [Nat.mod_eq_of_lt he1, Nat.pow_one],
      and1_ofNat (by omega)] at hz ⊢
    rcases Nat.mod_two_eq_zero_or_one (e / 2) with h | h <;> rw [h] at hz ⊢
  all_goals first | exact absurd hz (by decide) | skip
  · exact hnext _ _ _ _ _ (st' _) (by omega)
  · exact hexit _ _ _ _ _ (st' _) (by omega)

/-- **The first loop** from `0x800066a4` (`e` even): squarings until the
exponent left is odd, then its exit at `0x800066cc`. -/
theorem ra_p1_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 : Mem} {R0 : Nat → BitVec 64} {sp W q u rs nf : Nat}
    {A B : List NumObj} {x1 z o : NumObj}
    (env : RaEnv S Mt0 R0 sp W q A B x1 z o u) (hoom : RaOom live S Q Mt0 sp W q)
    (hexit : ∀ R' M' H' F' P i e, RaP1 S Mt0 M' R0 R' sp W q H' F' A B x1 (some P) i e rs nf →
      u = 2 ^ i * e → e % 2 = 1 → DW live S Q 0x800066cc#64 R' M') :
    ∀ e i {M : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {hP : Hd},
      RaP1 S Mt0 M R0 R sp W q H F A B x1 hP i e rs nf → u = 2 ^ i * e → e % 2 = 0 →
      DW live S Q 0x800066a4#64 R M := by
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    intro i M R H F hP st hu he
    have hu' : u = 2 ^ (i + 1) * (e / 2) := by
      rw [hu, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he)]
    have he0 : e ≠ 0 := by rintro rfl; have := env.u1; simp at hu; omega
    refine ra_p1_body hlive env hoom st hu he ?_ ?_
    · intro R' M' H' F' P st' he'
      exact ih (e / 2) (by omega) (i + 1) st' hu' he'
    · intro R' M' H' F' P st' he'
      exact hexit R' M' H' F' P (i + 1) (e / 2) st' hu' he'

end Dc.Mach
