import Dc.Mach.DcGetnum

/-!
# `dc_getnum` against `readNum` (M9)

`readNum` in three stages: the sign (`rdSign`), the integer digits, the
fraction (`rdFrac`). `gn_first` reads the sign, `gn_after` dispatches after
the integer digits, and `dc_getnum_spec` is the whole function: the result
handle holds `(readNum ibase w).1` and the reader stands after the first
character not consumed, `(readNum ibase w).2`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open VsaIris.Interp (imgLE)

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-! ## `readNum` in stages -/

/-- `readNum`'s sign: `_` and the spaces after it. -/
def rdSign : List Nat → Bool × List Nat
  | 95 :: rest => (true, rest.dropWhile isSpace)
  | s => (false, s)

/-- `readNum`'s fraction after the integer part `ip`. -/
def rdFrac (ib : Nat) (ip : Num) : List Nat → Num × List Nat
  | 46 :: rest =>
    let (fds, s') := takeDigits rest
    let dec := fds.length
    let build : Num := ⟨false, ofDigits ib fds, 0⟩
    let frac := (Num.div build ⟨false, ib ^ dec, 0⟩ dec).getD (Num.zero dec)
    (Num.add ip frac 0, s')
  | s => (ip, s)

/-- `readNum` after the sign, as `readNum` writes it. -/
def rdRest (ib : Nat) (neg : Bool) (s : List Nat) : Num × List Nat :=
  let (ids, s) := takeDigits s
  let ip : Num := ⟨false, ofDigits ib ids, 0⟩
  let (n, s) := match s with
    | 46 :: rest =>
      let (fds, s') := takeDigits rest
      let dec := fds.length
      let build : Num := ⟨false, ofDigits ib fds, 0⟩
      let frac := (Num.div build ⟨false, ib ^ dec, 0⟩ dec).getD (Num.zero dec)
      (Num.add ip frac 0, s')
    | _ => (ip, s)
  ((if neg then Num.sub (Num.zero 0) n 0 else n), s)

theorem rdRest_eq (ib : Nat) (neg : Bool) (s : List Nat) :
    rdRest ib neg s =
      ((if neg then Num.sub (Num.zero 0) (rdFrac ib ⟨false, ofDigits ib (takeDigits s).1, 0⟩ (takeDigits s).2).1 0
        else (rdFrac ib ⟨false, ofDigits ib (takeDigits s).1, 0⟩ (takeDigits s).2).1),
       (rdFrac ib ⟨false, ofDigits ib (takeDigits s).1, 0⟩ (takeDigits s).2).2) := by
  unfold rdRest
  rcases takeDigits s with ⟨ids, s1⟩
  dsimp only
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (unfold rdFrac; split <;> rfl)

theorem readNum_us (ib : Nat) (rest : List Nat) :
    readNum ib (95 :: rest) = rdRest ib true (rest.dropWhile isSpace) := rfl

theorem readNum_no (ib : Nat) {w : List Nat} (h : w[0]? ≠ some 95) : readNum ib w = rdRest ib false w := by
  match w with
  | [] => rfl
  | c :: cs =>
    have hc : c ≠ 95 := fun e => h (by simp [e])
    unfold readNum
    split
    · rename_i neg s heq
      split at heq
      · rename_i e; simp only [List.cons.injEq] at e; exact absurd e.1 hc
      · cases heq; rfl

theorem rdSign_us {w : List Nat} (h : w[0]? = some 95) : rdSign w = (true, (w.drop 1).dropWhile isSpace) := by
  match w, h with
  | 95 :: rest, _ => rfl

theorem rdSign_no {w : List Nat} (h : w[0]? ≠ some 95) : rdSign w = (false, w) := by
  match w with
  | [] => rfl
  | c :: rest =>
    have : c ≠ 95 := fun e => h (by simp [e])
    unfold rdSign; split
    · rename_i e; simp only [List.cons.injEq] at e; exact absurd e.1 this
    · rfl

theorem readNum_eq (ib : Nat) (w : List Nat) : readNum ib w = rdRest ib (rdSign w).1 (rdSign w).2 := by
  by_cases h : w[0]? = some 95
  · match w, h with
    | 95 :: rest, _ => rfl
  · rw [readNum_no ib h, rdSign_no h]

theorem rdFrac_dot {ib : Nat} (hib : 0 < ib) (ip : Num) {w : List Nat} {j : Nat} (hj : w[j]? = some 46) :
    rdFrac ib ip (w.drop j) =
      (Num.add ip (fracQ ib (ofDigits ib (takeDigits (w.drop (j + 1))).1)
        (takeDigits (w.drop (j + 1))).1.length) 0, (takeDigits (w.drop (j + 1))).2) := by
  have hl : j < w.length := by
    rcases Nat.lt_or_ge j w.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  have hc : w.getD j 0 = 46 := by rw [getElem?_of_lt hl] at hj; exact Option.some.inj hj
  rw [drop_cons_getD hl, hc]
  simp only [rdFrac, num_div_frac hib, Option.getD_some]

theorem rdFrac_no {ib : Nat} (ip : Num) {w : List Nat} {j : Nat} (hj : w[j]? ≠ some 46) :
    rdFrac ib ip (w.drop j) = (ip, w.drop j) := by
  rcases Nat.lt_or_ge j w.length with hl | hl
  · have hc : w.getD j 0 ≠ 46 := fun e => hj (by rw [getElem?_of_lt hl, e])
    rw [drop_cons_getD hl]
    unfold rdFrac; split
    · rename_i e; simp only [List.cons.injEq] at e; exact absurd e.1 hc
    · rfl
  · rw [List.drop_eq_nil_of_le hl]; rfl

theorem takeDigits_snd : ∀ l : List Nat, (takeDigits l).2 = l.drop (takeDigits l).1.length
  | [] => rfl
  | c :: cs => by
    unfold takeDigits
    split
    · simp only [List.length_cons, List.drop_succ_cons]; exact takeDigits_snd cs
    · rfl

theorem takeDigits_len : ∀ l : List Nat, (takeDigits l).1.length ≤ l.length
  | [] => Nat.le_refl _
  | c :: cs => by
    unfold takeDigits
    split
    · simp only [List.length_cons]; have := takeDigits_len cs; omega
    · simp

theorem takeDigits_lt16 : ∀ l : List Nat, ∀ d ∈ (takeDigits l).1, d < 16
  | [] => by simp [takeDigits]
  | c :: cs => by
    unfold takeDigits
    split
    · rename_i d hd
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact digitVal_lt hd
      · exact takeDigits_lt16 cs x hx
    · simp

theorem drop_drop_takeDigits (w : List Nat) (j : Nat) :
    (takeDigits (w.drop j)).2 = w.drop (j + (takeDigits (w.drop j)).1.length) := by
  rw [takeDigits_snd, List.drop_drop]

/-! ## The fraction's size -/

theorem decLen_le {n m : Nat} (h : n < 10 ^ m) (hm : 1 ≤ m) : decLen n ≤ m := by
  induction m generalizing n with
  | zero => omega
  | succ m ih =>
    unfold decLen
    split
    · omega
    · have : n / 10 < 10 ^ m := by rw [Nat.pow_succ] at h; omega
      have hm' : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with e | e
        · subst e; omega
        · exact e
      have := ih this hm'
      omega

theorem foldl_digF_lt {ib : Nat} (hib : ib ≤ 16) :
    ∀ (ds : List Nat) (r i : Nat), (∀ d ∈ ds, d < 16) → r < 16 ^ i → ds.foldl (digF ib) r < 16 ^ (i + ds.length)
  | [], r, i, _, h => by simpa using h
  | d :: ds, r, i, hd, h => by
    simp only [List.foldl_cons, List.length_cons]
    have hd0 := hd d List.mem_cons_self
    have : r * ib + d < 16 ^ (i + 1) := by
      rw [Nat.pow_succ]
      have := Nat.mul_le_mul_left r hib
      have : r * 16 + 16 ≤ 16 ^ i * 16 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right 16 h
      omega
    rw [show i + (ds.length + 1) = i + 1 + ds.length by omega]
    exact foldl_digF_lt hib ds _ _ (fun x hx => hd x (List.mem_cons_of_mem _ hx)) this

theorem pow16_le (k : Nat) : 16 ^ k ≤ 10 ^ (2 * k) := by
  rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (by decide) k

/-- **The fraction's sizes** for `gn_fexit`: `k < 2 ^ 24` digits. -/
theorem frac_size {ib k : Nat} (hib : ib ≤ 16) {ds : List Nat} (hd : ∀ d ∈ ds, d < 16) (hk : ds.length = k)
    (hk' : k < 2 ^ 24) :
    (⟨false, ds.foldl (digF ib) 0, 0⟩ : Num).wid + k + (⟨false, ib ^ k, 0⟩ : Num).wid < 2 ^ 27 := by
  have h1 := foldl_digF_lt hib ds 0 0 hd (by decide)
  rw [Nat.zero_add, hk] at h1
  have h2 : ib ^ k < 10 ^ (2 * k + 1) := by
    have := pow16_le k
    have := Nat.pow_le_pow_left hib k
    rw [Nat.pow_succ]; omega
  have e1 := decLen_le (m := 2 * k + 1) (Nat.lt_of_lt_of_le h1 (Nat.le_trans (pow16_le k)
    (Nat.pow_le_pow_right (by decide) (by omega)))) (by omega)
  have e2 := decLen_le h2 (by omega)
  simp only [Num.wid]
  omega

/-! ## The sign -/

/-- **The first character** (`0x80002780`): read it; `_` and the spaces
after it read on, `s6 = '_'`; else `s6 = 0`. On to `0x800027d4` with the
first character of `(rdSign w).2` in `s0`. -/
theorem gn_first {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64}
    {L0 : List NumObj} (gx : GnCtx S M0 sp G o j0) {R : Nat → BitVec 64} {M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} {C : BcConsts} {pr pt pd pb : Nat}
    (hQ : GnQ S M0 R0 sp G hs0 st o j0 ra s6 L0 R M 0 H F L C pr pt pd pb)
    (hhd : HeadOK (rdW o j0)[0]?)
    (hk : ∀ R' M' jS s6', GnQ S M0 R0 sp G hs0 st o j0 ra s6' L0 R' M'
        (min (jS + 1) (rdW o j0).length) H F L C pr pt pd pb → jS ≤ (rdW o j0).length →
        R' 8 = chW (rdW o j0)[jS]? → (rdSign (rdW o j0)).2 = (rdW o j0).drop jS →
        s6' = (if (rdSign (rdW o j0)).1 then chW (some 95) else 0#64) →
        DWO live S Q t 0x800027d4#64 R' M') :
    DWO live S Q t 0x80002780#64 R M := by
  have cx := gx.cx
  have hab := cx.abv
  have h := hQ.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have r18 := hQ.r18
  have hr := h.rd gx.mem gx.j0
  have jt : Sail.BitVec.update (0x80000b70#64) 0 0#1 = 0x80000b70#64 := jalr_tgt _ (by decide)
  bc_run hlive hS [r18]
  · rw [jt]; decide
  rw [jt]
  refine cf_read hlive (hQ.fr.regs (by keeps_tac Keeps.refl _ _)) hab h gx.own gx.mem gx.j0 (j := 0)
    (Nat.zero_le _) hQ.ptr (by bsimp []) fun R1 M1 hk1 e10 fr1 h1 hm1 hp1 => ?_
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  bsimp []
  refine gn_htest hlive hS1 hhd e10 (fun R2 e k2 e8 => ?_) (fun R2 ne k2 e8 e22 => ?_)
  · have hj1 : 0 < (rdW o j0).length := by
      rcases Nat.lt_or_ge 0 (rdW o j0).length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at e; cases e
    have kk : Keeps [1, 8, 10, 14, 15, 22] R2 R :=
      (k2.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans
        ((hk1.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans (by keeps_tac Keeps.refl _ _))
    refine gn_under hlive gx (hQ.next hab (fr1.sregs (k2.mono (by decide)) (k2.get 2)) h1 hm1 kk
      (by rw [k2.get 22, hk1.get 22]; try bsimp [hQ.r22]) hj1 (by rw [hp1, Nat.min_eq_left (by omega)]))
      (e8.trans (by rw [e])) fun R' M' jS hQ' hjS e8' ed => hk R' M' jS _ hQ' hjS e8' ?_ ?_
    · rw [rdSign_us e]; exact ed
    · rw [rdSign_us e]; rfl
  · have kk : Keeps [1, 8, 10, 14, 15, 22] R2 R :=
      (k2.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans
        ((hk1.mono (ks' := [1, 8, 10, 14, 15, 22]) (by decide)).trans (by keeps_tac Keeps.refl _ _))
    refine hk R2 M1 0 0#64 (hQ.next hab (fr1.sregs (k2.mono (by decide)) (k2.get 2)) h1 hm1 kk e22
      (by omega) hp1) (Nat.zero_le _) e8 ?_ ?_
    · rw [rdSign_no ne]; rfl
    · rw [rdSign_no ne]; rfl

/-! ## After the integer digits -/

/-- The integer loop's state as the exit's: `temp` held. -/
theorem GnX.ofI {S : Nat → Prop} {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat} {G : DcG}
    {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {s6 : BitVec 64} {L0 : List NumObj}
    {R : Nat → BitVec 64} {M : Mem} {j v : Nat} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {pr pt pd pb : Nat} (hI : GnI S M0 R0 sp G hs0 st o j0 ra s6 L0 R M j v H F L C pr pt pd pb) :
    GnX S M0 R0 sp G hs0 st o j0 ra s6 L0 R M j ⟨false, v, 0⟩ (some pt) H F L C pr pd pb where
  fr := hI.fr
  h := hI.h.perm (List.Perm.cons _ ((List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ _))))
  w16 := hI.w16
  w24 := hI.w24
  w32 := hI.w32
  w8 := hI.w8
  dr := hI.dr
  keep := hI.keep
  regs := hI.regs
  rd := hI.rd

/-- **The sign test** at `0x8000283c` (`bnez s6`). -/
theorem gn_neg0 {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {neg : Bool}
    {L0 : List NumObj} (cx : CfCtx S 144 sp) (hoom : GnOom live S Q t M0 sp)
    {R : Nat → BitVec 64} {M : Mem} {jE : Nat} {n : Num} {og : Option Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {pr pd pb : Nat}
    (hX : GnX S M0 R0 sp G hs0 st o j0 ra (if neg then chW (some 95) else 0#64) L0 R M jE n og H F L C pr pd pb)
    (hk : ∀ R' M' H' F' L' C' pr',
      GnX S M0 R0 sp G hs0 st o j0 ra (if neg then chW (some 95) else 0#64) L0 R' M' jE
        (if neg then Num.sub (Num.zero 0) n 0 else n) og H' F' L' C' pr' pd pb →
      DWO live S Q t 0x80002840#64 R' M') :
    DWO live S Q t 0x8000283c#64 R M := by
  have hS : HeapOwn S := fun a e1 e2 => hX.h.heap.heap.own a e1 e2
  cases neg with
  | false =>
    have r22 : R 22 = 0#64 := hX.regs.r22
    bc_run hlive hS [r22] at 0x80002840
    exact hk R M H F L C pr hX
  | true =>
    have r22 : R 22 = 95#64 := hX.regs.r22
    bc_run hlive hS [r22] at 0x800029ac
    exact gn_sign hlive cx hoom hX hk

/-- **The sign test** at `0x800029a8` (`beqz s6`) after a fraction. -/
theorem gn_neg1 {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {neg : Bool}
    {L0 : List NumObj} (cx : CfCtx S 144 sp) (hoom : GnOom live S Q t M0 sp)
    {R : Nat → BitVec 64} {M : Mem} {jE : Nat} {n : Num} {og : Option Nat} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {pr pd pb : Nat}
    (hX : GnX S M0 R0 sp G hs0 st o j0 ra (if neg then chW (some 95) else 0#64) L0 R M jE n og H F L C pr pd pb)
    (hk : ∀ R' M' H' F' L' C' pr',
      GnX S M0 R0 sp G hs0 st o j0 ra (if neg then chW (some 95) else 0#64) L0 R' M' jE
        (if neg then Num.sub (Num.zero 0) n 0 else n) og H' F' L' C' pr' pd pb →
      DWO live S Q t 0x80002840#64 R' M') :
    DWO live S Q t 0x800029a8#64 R M := by
  have hS : HeapOwn S := fun a e1 e2 => hX.h.heap.heap.own a e1 e2
  cases neg with
  | false =>
    have r22 : R 22 = 0#64 := hX.regs.r22
    bc_run hlive hS [r22] at 0x80002840
    exact hk R M H F L C pr hX
  | true =>
    have r22 : R 22 = 95#64 := hX.regs.r22
    bc_run hlive hS [r22] at 0x800029ac
    exact gn_sign hlive cx hoom hX hk

/-- **After the integer digits** (`0x80002834`, the character at `j` in
`s0`): a `.` reads the fraction (one lost reference, `lks = [pv]`); then the
sign. On to the exit at `0x80002840` with `rdFrac`'s number signed and the
reader after `rdFrac`'s rest. -/
theorem gn_after {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {R0 : Nat → BitVec 64} {sp : Nat}
    {G : DcG} {hs0 : List GV} {st : St} {o : StrObj} {j0 ra : Nat} {neg : Bool}
    {L0 : List NumObj} (gx : GnCtx S M0 sp G o j0) (hhs : hs0.length + 6 ≤ 2 ^ 20)
    (hoom : GnOom live S Q t M0 sp) (hl : G.lk.length < 2 ^ 29) (hsz : (rdW o j0).length < 2 ^ 24)
    {R : Nat → BitVec 64} {M : Mem} {j v : Nat} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {pr pt pd pb : Nat}
    (hI : GnI S M0 R0 sp G hs0 st o j0 ra (if neg then chW (some 95) else 0#64) L0 R M j v H F L C pr pt pd pb)
    (hk : ∀ R' M' H' F' L' C' (lks : List Nat) pr' pd' og jE, lks.length ≤ 1 →
      GnX S M0 R0 sp { G with lk := lks ++ G.lk } hs0 st o j0 ra (if neg then chW (some 95) else 0#64)
        L0 R' M' jE
        (if neg then Num.sub (Num.zero 0) (rdFrac st.ibase ⟨false, v, 0⟩ ((rdW o j0).drop j)).1 0
          else (rdFrac st.ibase ⟨false, v, 0⟩ ((rdW o j0).drop j)).1) og H' F' L' C' pr' pd' pb →
      (rdFrac st.ibase ⟨false, v, 0⟩ ((rdW o j0).drop j)).2 = (rdW o j0).drop jE →
      DWO live S Q t 0x80002840#64 R' M') :
    DWO live S Q t 0x80002834#64 R M := by
  have cx := gx.cx
  have h := hI.h
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hib := h.den.ibase
  have hr := h.rd gx.mem gx.j0
  have hc : ∀ c, (rdW o j0)[j]? = some c → c < 256 := fun c e => hr.lt c (List.mem_of_getElem? e)
  obtain ⟨hx1, hx2⟩ := chI_bounds hc
  have h8 : R 8 = BitVec.ofInt 64 (chI (rdW o j0)[j]?) := hI.rd.ch.trans (chW_eq _)
  bc_run hlive hS [h8] at 0x8000283c
  all_goals rw [ofInt_eq_lit (k := 46) (by decide) hx1 hx2]
  · intro e
    have ed : (rdW o j0)[j]? = some 46 := by
      cases e' : (rdW o j0)[j]? with
      | none => rw [e'] at e; simp [chI] at e
      | some c => rw [e'] at e; simp only [chI] at e; rw [show c = 46 by omega]
    have hj : j < (rdW o j0).length := by
      rcases Nat.lt_or_ge j (rdW o j0).length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at ed; cases ed
    have hI' := hI.keepT (R' := upd R 15 46#64) (by keeps_tac Keeps.refl _ _)
    refine gn_fentry hlive gx hhs hI' fun R1 M1 H1 F1 L1 C1 pd1 pv1 hF e8 ep => ?_
    refine gnf_loop hlive gx hhs hoom _ j 0 0 R1 M1 none H1 F1 L1 C1 pd1 pv1 rfl hj (Nat.zero_le _) hF
      ⟨hI.rd.le, e8.trans hI'.rd.ch, ep.trans hI'.rd.ptr⟩
      fun R2 M2 og2 H2 F2 L2 C2 pd2 pv2 hF2 hrd2 => ?_
    have hd16 := takeDigits_lt16 ((rdW o j0).drop (j + 1))
    have hlen := takeDigits_len ((rdW o j0).drop (j + 1))
    simp only [List.length_drop] at hlen
    refine gn_fexit hlive cx hoom hl (by simpa using hF2) hrd2
      (frac_size hib.2 hd16 (Nat.zero_add _).symm (by omega)) fun R3 M3 H3 F3 L3 C3 pr3 pd3 hX3 => ?_
    refine gn_neg1 hlive cx hoom hX3 fun R4 M4 H4 F4 L4 C4 pr4 hX4 => ?_
    refine hk R4 M4 H4 F4 L4 C4 [pv2] pr4 pd3 og2
      (j + 1 + (takeDigits ((rdW o j0).drop (j + 1))).1.length) (by simp) ?_ ?_
    · rw [rdFrac_dot (by omega) _ ed]
      simpa [ofDigits] using hX4
    · rw [rdFrac_dot (by omega) _ ed, drop_drop_takeDigits]
  · intro e
    have ed : (rdW o j0)[j]? ≠ some 46 := fun e' => e (by rw [e']; rfl)
    refine gn_neg0 hlive cx hoom (GnX.ofI (hI.keepT (by keeps_tac Keeps.refl _ _))) fun R4 M4 H4 F4 L4 C4 pr4 hX4 => ?_
    refine hk R4 M4 H4 F4 L4 C4 [] pr4 pd (some pt) j (by simp) ?_ ?_
    · rw [rdFrac_no _ ed]; exact hX4
    · rw [rdFrac_no _ ed]

end Dc.Mach
