import Dc.Mach.Bc.OutNumInt

/-! # `bc_out_num` in a base other than 10: printing the integer digits

From `0x80007214` the digit stack is popped, most significant digit first:
each cell's digit is printed and the cell freed. For a base up to 16 a digit
is one character of `ref_str` (`0x8000748c`); above, `bc_out_long` prints it
space-led and zero-padded to the width of `base - 1` (`0x800074b8`). Both
loops end at `0x8000721c` with the stack empty.

- `ogDigI`: one digit's characters in the integer part.
- `OgSt.reframe`: the state through a change below the window and in `G`.
- `OgSt.long`: `bc_out_long` from the state.
- `OgSt.freeCell`: `free` of the head cell.
- `OgPH`: the pop loops' state; `og_popHex`, `og_popLong` by induction on
  the cells; `og_s6`: from `0x80007214`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- The characters of one integer digit `d` in base `ob`. -/
abbrev ogDigI (ob d : Nat) : List Nat :=
  if ob ≤ 16 then [Num.hexChar d] else Num.outLong d (Num.decText (ob - 1)).length true

/-- The characters through the integer part. -/
abbrev ogIntOut (x : NumObj) (ob : Nat) (cs : List Nat) : List Nat :=
  cs ++ signOut x.rep.num ++ (Num.digits ob (ogIp x.rep.num).mag).flatMap (ogDigI ob)

theorem digitsIn_lt (b : Nat) (hb : 0 < b) :
    ∀ fuel n, ∀ d ∈ Num.digitsIn b fuel n, d < b
  | 0, _ => by simp [Num.digitsIn]
  | fuel + 1, n => by
    simp only [Num.digitsIn]
    split
    · simp
    · intro d hd
      rcases List.mem_append.mp hd with h | h
      · exact digitsIn_lt b hb fuel _ d h
      · simp only [List.mem_singleton] at h; subst h; exact Nat.mod_lt _ hb

/-- Every digit is below the base. -/
theorem digits_lt {b : Nat} (hb : 0 < b) (n : Nat) : ∀ d ∈ Num.digits b n, d < b :=
  digitsIn_lt b hb _ _

/-- `ref_str` at `0x800081e8`: `"0123456789ABCDEF"`. -/
theorem refStr_bytes : ∀ i, i < 16 →
    dcROImg (0x800081e8 + i) = BitVec.ofNat 8 (Num.hexChar i) ∧
      (0x800081e8 + i, BitVec.ofNat 8 (Num.hexChar i)) ∈ dcRO := by
  decide +kernel

/-- A live block of the heap lies in the arena. -/
theorem HeapInv.liveBounds {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {c : Blk} (hc : c ∈ H.live) : 2147603920 ≤ c.h ∧ c.fin ≤ 2273312768 :=
  let fb := hi.blk (List.mem_append_right _ hc)
  ⟨fb.lo, Nat.le_trans fb.fin fb.top⟩

/-- `max_o_digit`'s length is the width of `base - 1`. -/
theorem mx_len {ob : Nat} {mx : NumObj} (hmx : NewNum (Num.ofInt (ob - 1 : Nat)) mx)
    (hs : NumShape mx.rep) (hob : 2 ≤ ob) : mx.rep.len = (Num.decText (ob - 1)).length := by
  rw [← NumRep.intLen_eq hs hmx.norm hmx.pos, hmx.num,
    show Num.ofInt ((ob - 1 : Nat) : Int) = ⟨false, ob - 1, 0⟩ by simp [Num.ofInt]]
  exact Dc.BcModel.intLen_dec (by omega)

/-- **The state through a change** off `G`, below the window or at and above
the frame, with the characters `sent'` and console `t'`. -/
theorem OgSt.reframe {live S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {hs : List RH}
    {os : List Nat} {sent sent' : List Nat} {t t' : String}
    (st : OgSt S X G I Mt0 M R0 R sp W H F L hs os sent t)
    (cx : OnCtx S R0 sp W d) (cb : CharFn live S Q (R0 12) d G I)
    (hfr : ∀ a, ¬ G a → (a < sp - W ∨ sp - 176 ≤ a) → imgM M' a = imgM M a)
    (hI : I sent' t' M') :
    OgSt S X G I Mt0 M' R0 R sp W H F L hs os sent' t' := by
  on_facts cx
  have hsf := cx.cc.frame
  have hsl := hsf.lo
  have hG : ∀ a, G a → a < heapStart := fun a hg => (cb.off a hg).1
  have hng : ∀ a, heapStart ≤ a → ¬ G a := fun a h hg => by have := hG a hg; omega
  exact
    { on :=
        { st.on with
          saved := st.on.saved.transport (lo := 72) (top := 176) (by decide) (by decide)
            fun a h1 _ => hfr a (hng a (by simp only [heapStart, heapEnd] at *; omega)) (.inr (by omega))
          out := fun a ha hg hf => by
            rw [hfr a hg (by simp only [frameIn] at hf; omega)]; exact st.on.out a ha hg hf }
      heap := st.heap.out_frame (P := fun a => G a ∨ frameIn sp W a)
        (fun a hp => hfr a (fun hg => hp (.inl hg)) (by
          simp only [frameIn, not_or, not_and, Nat.not_lt] at hp ⊢
          by_cases h : sp - W ≤ a
          · exact .inr (by have := hp.2 h; omega)
          · exact .inl (by omega)))
        (fun a ha => by
          rcases ha with hg | hf
          · exact (cb.off a hg).2.1
          · apply outHeap_of_ge; simp only [frameIn, heapEnd] at hf ⊢; omega)
      own := st.own
      words := st.words.transport fun o ho => by
        have := st.offs o ho
        exact ldv_congr .ld fun j hj => hfr _ (hng _ (by simp only [heapStart, heapEnd] at *; omega))
          (.inr (by omega))
      offs := st.offs
      nd := st.nd
      inv := hI }

/-- **`bc_out_long (v, size, 1, out_char)`** from the state: the characters
grow by `v`'s padded text, the heap, the handles and their words stay. -/
theorem OgSt.long {live S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d v size : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {hs : List RH}
    {os : List Nat} {sent : List Nat} {t : String}
    (st : OgSt S X G I Mt0 M R0 R sp W H F L hs os sent t)
    (cx : OnCtx S R0 sp W d) (cb : CharFn live S Q (R0 12) d G I)
    (h13 : R 13 = R0 12) (h10 : R 10 = BitVec.ofNat 64 v) (hv : v < 2 ^ 63)
    (h11 : R 11 = BitVec.ofNat 64 size) (hsz : size < 2 ^ 31) (h12 : R 12 = boolWord true)
    (h1 : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' t', Keeps cClob R' R →
      OgSt S X G I Mt0 M' R0 R' sp W H F L hs os (sent ++ Num.outLong v size true) t' →
      DWO live S Q t' (R 1) R' M') :
    DWO live S Q t 0x800064ec#64 R M := by
  on_facts cx
  have hsf := cx.cc.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hlo : heapEnd ≤ sp - W := by simp only [heapEnd] at *; omega
  have ccb : CharCb live S Q (R 13) d (fun cs t M' => I cs t M' ∧ Frozen G (sp - W) M M')
      (sp - W) := by
    rw [h13]; exact cb.cb M hlo
  have olx : OLCtx S R (sp - 176) d (sp - W) :=
    { frame := ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩
      above := by simp only [heapEnd] at *; omega
      lo := by omega
      sp0 := st.on.r2
      al := h1
      fal := by rw [h13]; exact cx.fal }
  refine bc_out_long_spec hlive ccb olx (cb.olStable M hlo (by omega)) h10 hv h11 hsz h12
    ⟨st.inv, Frozen.refl _ _ _⟩ fun R' M' t' hk' hI' hhi => hk R' M' t' hk' ?_
  exact (st.reframe cx cb (fun a hg ha => ha.elim (fun h => hI'.2 a hg h) (hhi a)) hI'.1).regs hk'

/-- **`free` of the head cell** from the state: the stack is its rest. -/
theorem OgSt.freeCell {live S : Nat → Prop} {X0 : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {Mt0 M Mc : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {hs : List RH}
    {os : List Nat} {sent : List Nat} {t : String} {c : Blk} {cells : List Blk} {dg : Nat}
    {ds : List Nat} {q : Nat}
    (st : OgSt S ⟨(c :: cells) ++ X0.bs, Mc⟩ G I Mt0 M R0 R sp W H F L hs os sent t)
    (sk : OgStk X0 Mc (c :: cells) (dg :: ds) q) (cx : OnCtx S R0 sp W d)
    (cb : CharFn live S Q (R0 12) d G I)
    (h10 : R 10 = BitVec.ofNat 64 c.pay) (h1 : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H', Keeps [14, 15] R' R →
      OgSt S ⟨cells ++ X0.bs, Mc⟩ G I Mt0 M' R0 R' sp W H' F L hs os sent t →
      OgStk X0 Mc cells ds (ldv .ld Mc (c.pay + 8)).toNat → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80000a0c#64 R M := by
  obtain ⟨lpre, lpost, hl⟩ := List.append_of_mem (st.heap.raw.live c List.mem_cons_self)
  exact free_spec hlive st.heap.heap hl R h10 h1 fun R' M' hk' hp => by
    obtain ⟨st', sk'⟩ := st.pop sk cx cb hl hp
    exact hk R' M' _ hk' (st'.regs hk') sk'

/-- The registers the pop loops and the fraction keep: `s2` the number, `s3`
`base`, `s6` `frac_part`, `s7` the base, `s8` `max_o_digit`, `s10` `cur_dig`, `s11` `&_one_`. -/
structure OgPopRegs (R : Nat → BitVec 64) (x : NumObj) (ob : Nat) (fr bs mx : NumObj) (cur : RH) :
    Prop where
  r18 : R 18 = BitVec.ofNat 64 x.rep.p
  r19 : R 19 = BitVec.ofNat 64 bs.rep.p
  r23 : R 23 = BitVec.ofNat 64 ob
  r24 : R 24 = BitVec.ofNat 64 mx.rep.p
  r26 : R 26 = BitVec.ofNat 64 cur.p
  r27 : R 27 = BitVec.ofNat 64 oneAddr
  r22 : R 22 = BitVec.ofNat 64 fr.rep.p

theorem OgPopRegs.keep {R R' : Nat → BitVec 64} {x : NumObj} {ob : Nat} {fr bs mx : NumObj}
    {cur : RH} (h : OgPopRegs R x ob fr bs mx cur) {ks : List Nat} (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∉ [18, 19, 22, 23, 24, 26, 27] := by decide) :
    OgPopRegs R' x ob fr bs mx cur :=
  ⟨by rw [hk.get 18 fun h => hks 18 h (by decide)]; exact h.r18,
    by rw [hk.get 19 fun h => hks 19 h (by decide)]; exact h.r19,
    by rw [hk.get 23 fun h => hks 23 h (by decide)]; exact h.r23,
    by rw [hk.get 24 fun h => hks 24 h (by decide)]; exact h.r24,
    by rw [hk.get 26 fun h => hks 26 h (by decide)]; exact h.r26,
    by rw [hk.get 27 fun h => hks 27 h (by decide)]; exact h.r27,
    by rw [hk.get 22 fun h => hks 22 h (by decide)]; exact h.r22⟩

/-- After the integer digits (`0x8000721c`): the stack empty, `int_part`
zero, the integer part's characters sent. -/
def OgK6 (live S : Nat → Prop) (X0 : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x : NumObj) (ob : Nat) (cs : List Nat)
    (fr bs mx : NumObj) : Prop :=
  ∀ (t : String) (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (ip : NumObj)
    (cur : RH),
    OgSt S X0 G I Mt0 M R0 R sp W H F L [.own ip, .own fr, cur, .own bs, .own mx]
      [16, 24, 40, 32, 56] (ogIntOut x ob cs) t →
    RHOK L cur → NewNum ⟨false, 0, 0⟩ ip → OgPopRegs R x ob fr bs mx cur →
    DWO live S Q t 0x8000721c#64 R M

/-- **The pop loops' state**: the stack from `p` holds `ds`, whose characters
complete the integer part. -/
structure OgPH (S : Nat → Prop) (X0 : Raws) (G : Nat → Prop) (I : List Nat → String → Mem → Prop)
    (Mt0 M : Mem) (R0 R : Nat → BitVec 64) (sp W : Nat) (H : Heap) (F : List Blk)
    (L : List NumObj) (x : NumObj) (ob : Nat) (cs sent : List Nat) (t : String)
    (ip fr bs mx : NumObj) (cur : RH) (cells : List Blk) (ds : List Nat) (Mc : Mem) (p : Nat) :
    Prop where
  st : OgSt S ⟨cells ++ X0.bs, Mc⟩ G I Mt0 M R0 R sp W H F L
    [.own ip, .own fr, cur, .own bs, .own mx] [16, 24, 40, 32, 56] sent t
  curOK : RHOK L cur
  stk : OgStk X0 Mc cells ds p
  ipn : NewNum ⟨false, 0, 0⟩ ip
  p64 : p < 2 ^ 64
  tgt : sent ++ ds.flatMap (ogDigI ob) = ogIntOut x ob cs
  dlt : ∀ d ∈ ds, d < ob
  regs : OgPopRegs R x ob fr bs mx cur

/-- Through register changes off the kept ones. -/
theorem OgPH.keep {S : Nat → Prop} {X0 : Raws} {G : Nat → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64}
    {sp W : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x : NumObj} {ob : Nat}
    {cs sent : List Nat} {t : String} {ip fr bs mx : NumObj} {cur : RH} {cells : List Blk}
    {ds : List Nat} {Mc : Mem} {p : Nat}
    (ph : OgPH S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur cells ds Mc p)
    {ks : List Nat} (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ onAll ∧ z ≠ 2 ∧ z ≠ 9 := by decide)
    (hks' : ∀ z ∈ ks, z ∉ [18, 19, 22, 23, 24, 26, 27] := by decide) :
    OgPH S X0 G I Mt0 M R0 R' sp W H F L x ob cs sent t ip fr bs mx cur cells ds Mc p :=
  { ph with st := ph.st.regs hk hks, regs := ph.regs.keep hk hks' }

/-- The empty stack: the state of `OgK6`. -/
theorem OgPH.done {live S : Nat → Prop} {X0 : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x : NumObj} {ob : Nat}
    {cs sent : List Nat} {t : String} {ip fr bs mx : NumObj} {cur : RH} {Mc : Mem}
    (ph : OgPH S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur [] [] Mc 0)
    (cx : OnCtx S R0 sp W d) (cb : CharFn live S Q (R0 12) d G I) :
    OgSt S X0 G I Mt0 M R0 R sp W H F L [.own ip, .own fr, cur, .own bs, .own mx]
      [16, 24, 40, 32, 56] (ogIntOut x ob cs) t := by
  have h := ph.tgt
  simp only [List.flatMap_nil, List.append_nil] at h
  exact h ▸ ph.st.outHeap cx cb (ph.st.heap.dropRaws ph.stk.agree) fun _ _ => rfl

/-- A nonempty stack: its head cell, read through the current memory. -/
structure OgTop (S : Nat → Prop) (X0 : Raws) (M Mc : Mem) (cells : List Blk) (ds : List Nat)
    (c : Blk) (cs : List Blk) (dg : Nat) (ds' : List Nat) : Prop where
  cells : cells = c :: cs
  ds : ds = dg :: ds'
  lo : 2147603920 ≤ c.h
  hi : c.fin ≤ 2273312768
  sz : 16 ≤ c.sz
  word : ldv .ld M c.pay = BitVec.ofNat 64 dg
  next : ldv .ld M (c.pay + 8) = ldv .ld Mc (c.pay + 8)

theorem OgPH.top {S : Nat → Prop} {X0 : Raws} {G : Nat → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x : NumObj} {ob : Nat}
    {cs sent : List Nat} {t : String} {ip fr bs mx : NumObj} {cur : RH} {cells : List Blk}
    {ds : List Nat} {Mc : Mem} {p : Nat}
    (ph : OgPH S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur cells ds Mc p)
    (hp : p ≠ 0) :
    ∃ c cs' dg ds', p = c.pay ∧ OgTop S X0 M Mc cells ds c cs' dg ds' := by
  have hc := ph.stk.cells
  match cells, ds, hc with
  | [], [], h => exact absurd h hp
  | c :: cs', dg :: ds', h =>
    have hh := Cells.head h
    have hcl : c ∈ H.live := ph.st.heap.raw.live c List.mem_cons_self
    have hb := ph.st.heap.heap.liveBounds hcl
    have hbp : c.pay = c.h + 16 := rfl
    have hbf : c.fin = c.h + 16 + c.sz := rfl
    have hsz := hh.sz
    have himg : ∀ j, j < 16 → imgM M (c.pay + j) = imgM Mc (c.pay + j) := fun j hj =>
      ph.st.heap.raw.img c List.mem_cons_self _ (by simp only [Blk.In, Blk.pay, Blk.fin]; omega)
    refine ⟨c, cs', dg, ds', hh.p, rfl, rfl, hb.1, hb.2, hsz, ?_, ?_⟩
    · rw [ldv_congr .ld fun j hj => himg j (by simp only [widthOfM] at hj; omega)]; exact hh.word
    · exact ldv_congr .ld fun j hj => by
        rw [Nat.add_assoc]; exact himg _ (by simp only [widthOfM] at hj; omega)

/-- The hex loop from `0x800074a4` (the `bnez s4` after a free) for the
stack `cells`. -/
def OgHexNext (live S : Nat → Prop) (X0 : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x : NumObj) (ob : Nat) (cs : List Nat)
    (fr bs mx : NumObj) (cells : List Blk) : Prop :=
  ∀ (ds : List Nat) (q : Nat) (t : String) (R : Nat → BitVec 64) (M : Mem) (H : Heap)
    (F : List Blk) (ip : NumObj) (cur : RH) (Mc : Mem) (sent : List Nat),
    OgPH S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur cells ds Mc q →
    R 20 = BitVec.ofNat 64 q → R 8 = 0x800081e8#64 → DWO live S Q t 0x800074a4#64 R M

/-- **One hex digit** from `0x8000748c`: its `ref_str` character, then the
cell freed. -/
theorem og_hexStep {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {fr bs mx : NumObj}
    (h16 : ob ≤ 16) {cells : List Blk}
    (ih : OgHexNext live S X0 Q I G Mt0 R0 sp W L x ob cs fr bs mx cells)
    {c : Blk} {dg : Nat} {ds : List Nat} {t : String} {R : Nat → BitVec 64} {M : Mem} {H : Heap}
    {F : List Blk} {ip : NumObj} {cur : RH} {Mc : Mem} {sent : List Nat}
    (ph : OgPH S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur (c :: cells)
      (dg :: ds) Mc c.pay)
    (h25 : R 25 = BitVec.ofNat 64 c.pay) (h10 : R 10 = BitVec.ofNat 64 dg)
    (h20 : R 20 = BitVec.ofNat 64 (ldv .ld Mc (c.pay + 8)).toNat) (h8 : R 8 = 0x800081e8#64) :
    DWO live S Q t 0x8000748c#64 R M := by
  have cx := fx.cx
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => ph.st.heap.heap.own a h1 h2
  have hdg : dg < 16 := Nat.lt_of_lt_of_le (ph.dlt dg List.mem_cons_self) h16
  have hro := refStr_bytes dg hdg
  have h9 := ph.st.on.cb
  bc_run hlive hS [h10, h8, h9] at 0x80007494
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
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
  refine OgSt.call (X := ⟨(c :: cells) ++ X0.bs, Mc⟩) (Mt0 := Mt0) (H := H) (F := F) (L := L)
    (hs := [.own ip, .own fr, cur, .own bs, .own mx]) (os := [16, 24, 40, 32, 56]) (sent := sent)
    ?_ cx cb (c := Num.hexChar dg) (by bsimp []) hch (by bsimp [])
    fun R' M' t' hk' st' => ?_
  · exact ph.st.regs (ks := [1, 10]) (by keeps_tac Keeps.refl _ _)
  have kk : Keeps cClob R' R := hk'.trans (by keeps_tac Keeps.refl _ _)
  have g25 : R' 25 = BitVec.ofNat 64 c.pay := by rw [kk.get 25 (by decide)]; exact h25
  bsimp []
  bc_run hlive hS [g25] at 0x80000a0c
  refine OgSt.freeCell hlive (st'.regs (ks := [1, 10]) (by keeps_tac Keeps.refl _ _)) ph.stk cx cb (by bsimp [g25]) (by bsimp [])
    fun R2 M2 H2 hk2 st2 sk2 => ?_
  have kk2 : Keeps cClob R2 R := (hk2.mono (by decide)).trans
    ((by keeps_tac Keeps.refl _ _ : Keeps cClob _ _).trans kk)
  bsimp []
  exact ih ds _ t' R2 M2 H2 F ip cur Mc (sent ++ [Num.hexChar dg])
    ⟨st2, ph.curOK, sk2, ph.ipn, BitVec.isLt _,
      by rw [← ph.tgt]; simp [ogDigI, h16], fun d hd => ph.dlt d (List.mem_cons_of_mem _ hd),
      ph.regs.keep kk2⟩
    (by rw [kk2.get 20 (by decide)]; exact h20) (by rw [kk2.get 8 (by decide)]; exact h8)

/-- **The hex loop** from `0x800074a4` for every stack, by induction on the
cells. -/
theorem og_hexNext {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {fr bs mx : NumObj}
    (hk6 : OgK6 live S X0 Q I G Mt0 R0 sp W L x ob cs fr bs mx) (h16 : ob ≤ 16) :
    ∀ cells, OgHexNext live S X0 Q I G Mt0 R0 sp W L x ob cs fr bs mx cells := by
  have cx := fx.cx
  have cb := fx.cb
  on_facts cx
  intro cells
  induction cells with
  | nil =>
    intro ds q t R M H F ip cur Mc sent ph h20 h8
    have hS : HeapOwn S := fun a h1 h2 => ph.st.heap.heap.own a h1 h2
    have hq : q = 0 := ph.stk.cells.zero_iff.mpr rfl
    have hl := ph.stk.cells.length
    match ds, hl with
    | [], _ =>
    subst hq
    bc_run hlive hS [h20] at 0x8000721c
    bc_run hlive hS [h20] at 0x8000721c
    exact hk6 t R M H F ip cur (ph.done cx cb) ph.curOK ph.ipn ph.regs
  | cons c cs ih =>
    intro ds q t R M H F ip cur Mc sent ph h20 h8
    have hS : HeapOwn S := fun a h1 h2 => ph.st.heap.heap.own a h1 h2
    have hq0 : q ≠ 0 := fun h => by cases ph.stk.cells.zero_iff.mp h
    obtain ⟨c', cs', dg, ds', hq, tp⟩ := ph.top hq0
    obtain ⟨rfl, rfl⟩ := List.cons.inj tp.cells
    subst hq
    have hds := tp.ds
    subst hds
    have hlo := tp.lo
    have hhi := tp.hi
    have hsz := tp.sz
    have hbp : c.pay = c.h + 16 := rfl
    have hbf : c.fin = c.h + 16 + c.sz := rfl
    have hb0 : (BitVec.ofNat 64 c.pay).toNat = c.pay := by rw [BitVec.toNat_ofNat]; omega
    have hb8 : (BitVec.ofNat 64 (c.pay + 8)).toNat = c.pay + 8 := by rw [BitVec.toNat_ofNat]; omega
    have hw := tp.word
    have hn := tp.next
    have hne : BitVec.ofNat 64 c.pay ≠ 0#64 := fun he => by
      have e := congrArg BitVec.toNat he
      rw [hb0] at e; simp at e <;> omega
    bc_run hlive hS [h20] at 0x8000748c
    · intro _
      bc_run hlive hS [h20, hb0, hb8, hw, hn] at 0x8000748c
      all_goals first | (have e6 : c.pay = c.h + 16 := rfl; have e7 : c.fin = c.h + 16 + c.sz := rfl; exact acc_heap hS (by omega) (by omega)) | (have e6 : c.pay = c.h + 16 := rfl; have e7 : c.fin = c.h + 16 + c.sz := rfl; simp only [StOK, LdOK, tohostAddr]; omega) | skip
      refine og_hexStep hlive fx h16 ih (ph.keep (ks := [10, 20, 25]) (by keeps_tac Keeps.refl _ _)) (by bsimp [h20]) (by bsimp []) ?_ (by bsimp [h8])
      bsimp []
      apply BitVec.eq_of_toNat_eq
      simp
    · intro h; exact absurd hne h

/-- The long loop from `0x800074d0` (the `bnez s4` after a free) for the
stack `cells`. -/
def OgLongNext (live S : Nat → Prop) (X0 : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x : NumObj) (ob : Nat) (cs : List Nat)
    (fr bs mx : NumObj) (cells : List Blk) : Prop :=
  ∀ (ds : List Nat) (q : Nat) (t : String) (R : Nat → BitVec 64) (M : Mem) (H : Heap)
    (F : List Blk) (ip : NumObj) (cur : RH) (Mc : Mem) (sent : List Nat),
    OgPH S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur cells ds Mc q →
    R 20 = BitVec.ofNat 64 q → DWO live S Q t 0x800074d0#64 R M

/-- **One digit above base 16** from `0x800074b8`: `bc_out_long` with the
width of `max_o_digit`, then the cell freed. -/
theorem og_longStep {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {fr bs mx : NumObj}
    (hmx : NewNum (Num.ofInt (ob - 1 : Nat)) mx) (h16 : ¬ ob ≤ 16) {cells : List Blk}
    (ih : OgLongNext live S X0 Q I G Mt0 R0 sp W L x ob cs fr bs mx cells)
    {c : Blk} {dg : Nat} {ds : List Nat} {t : String} {R : Nat → BitVec 64} {M : Mem} {H : Heap}
    {F : List Blk} {ip : NumObj} {cur : RH} {Mc : Mem} {sent : List Nat}
    (ph : OgPH S X0 G I Mt0 M R0 R sp W H F L x ob cs sent t ip fr bs mx cur (c :: cells)
      (dg :: ds) Mc c.pay)
    (h25 : R 25 = BitVec.ofNat 64 c.pay) (h10 : R 10 = BitVec.ofNat 64 dg)
    (h20 : R 20 = BitVec.ofNat 64 (ldv .ld Mc (c.pay + 8)).toNat) :
    DWO live S Q t 0x800074b8#64 R M := by
  have cx := fx.cx
  have cb := fx.cb
  have hob := fx.ha.obHi
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => ph.st.heap.heap.own a h1 h2
  have hdg : dg < ob := ph.dlt dg List.mem_cons_self
  have h9 := ph.st.on.cb
  have hmxm : mx ∈ RList [.own ip, .own fr, cur, .own bs, .own mx] L := by
    simp [RList, rTemps, RH.tmp]
  have hmxn := ph.st.heap.nums mx hmxm
  have hmxs := hmxn.shape
  have hsz := hmxs.size
  have hp1 := hmxs.pHi
  have hp2 := hmxs.pLo
  simp only [heapEnd, heapStart] at hp1 hp2
  have hl := hmxn.len
  have h24 := ph.regs.r24
  bc_run hlive hS [h24, hl, h9] at 0x800064ec
  all_goals first | exact acc_heap hS (by omega) (by omega) | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  refine OgSt.long hlive (ph.st.regs (ks := [1, 11, 12, 13]) (by keeps_tac Keeps.refl _ _)) cx cb
    (v := dg) (size := mx.rep.len) (by bsimp [h9]) (by bsimp [h10]) (by omega) (by bsimp [])
    (by omega) (by bsimp []) (by bsimp []) fun R' M' t' hk' st' => ?_
  have kk : Keeps cClob R' R := hk'.trans (by keeps_tac Keeps.refl _ _)
  have g25 : R' 25 = BitVec.ofNat 64 c.pay := by rw [kk.get 25 (by decide)]; exact h25
  bsimp []
  bc_run hlive hS [g25] at 0x80000a0c
  refine OgSt.freeCell hlive (st'.regs (ks := [1, 10]) (by keeps_tac Keeps.refl _ _)) ph.stk cx cb
    (by bsimp [g25]) (by bsimp []) fun R2 M2 H2 hk2 st2 sk2 => ?_
  have kk2 : Keeps cClob R2 R := (hk2.mono (by decide)).trans
    ((by keeps_tac Keeps.refl _ _ : Keeps cClob _ _).trans kk)
  bsimp []
  have hw := mx_len hmx hmxs fx.ha.obLo
  exact ih ds _ t' R2 M2 H2 F ip cur Mc (sent ++ Num.outLong dg mx.rep.len true)
    ⟨st2, ph.curOK, sk2, ph.ipn, BitVec.isLt _,
      by rw [← ph.tgt, hw]; simp [ogDigI, h16], fun d hd => ph.dlt d (List.mem_cons_of_mem _ hd),
      ph.regs.keep kk2⟩
    (by rw [kk2.get 20 (by decide)]; exact h20)

/-- **The long loop** from `0x800074d0` for every stack, by induction on the
cells. -/
theorem og_longNext {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {fr bs mx : NumObj}
    (hmx : NewNum (Num.ofInt (ob - 1 : Nat)) mx)
    (hk6 : OgK6 live S X0 Q I G Mt0 R0 sp W L x ob cs fr bs mx) (h16 : ¬ ob ≤ 16) :
    ∀ cells, OgLongNext live S X0 Q I G Mt0 R0 sp W L x ob cs fr bs mx cells := by
  have cx := fx.cx
  have cb := fx.cb
  on_facts cx
  intro cells
  induction cells with
  | nil =>
    intro ds q t R M H F ip cur Mc sent ph h20
    have hS : HeapOwn S := fun a h1 h2 => ph.st.heap.heap.own a h1 h2
    have hq : q = 0 := ph.stk.cells.zero_iff.mpr rfl
    have hl := ph.stk.cells.length
    match ds, hl with
    | [], _ =>
    subst hq
    bc_run hlive hS [h20] at 0x8000721c
    bc_run hlive hS [h20] at 0x8000721c
    exact hk6 t R M H F ip cur (ph.done cx cb) ph.curOK ph.ipn ph.regs
  | cons c cs ih =>
    intro ds q t R M H F ip cur Mc sent ph h20
    have hS : HeapOwn S := fun a h1 h2 => ph.st.heap.heap.own a h1 h2
    have hq0 : q ≠ 0 := fun h => by cases ph.stk.cells.zero_iff.mp h
    obtain ⟨c', cs', dg, ds', hq, tp⟩ := ph.top hq0
    obtain ⟨rfl, rfl⟩ := List.cons.inj tp.cells
    subst hq
    have hds := tp.ds
    subst hds
    have hlo := tp.lo
    have hhi := tp.hi
    have hsz := tp.sz
    have hbp : c.pay = c.h + 16 := rfl
    have hbf : c.fin = c.h + 16 + c.sz := rfl
    have hb0 : (BitVec.ofNat 64 c.pay).toNat = c.pay := by rw [BitVec.toNat_ofNat]; omega
    have hb8 : (BitVec.ofNat 64 (c.pay + 8)).toNat = c.pay + 8 := by rw [BitVec.toNat_ofNat]; omega
    have hw := tp.word
    have hn := tp.next
    have hne : BitVec.ofNat 64 c.pay ≠ 0#64 := fun he => by
      have e := congrArg BitVec.toNat he
      rw [hb0] at e; simp at e <;> omega
    bc_run hlive hS [h20] at 0x800074b8
    · intro _
      bc_run hlive hS [h20, hb0, hb8, hw, hn] at 0x800074b8
      all_goals first | (have e6 : c.pay = c.h + 16 := rfl; have e7 : c.fin = c.h + 16 + c.sz := rfl; exact acc_heap hS (by omega) (by omega)) | (have e6 : c.pay = c.h + 16 := rfl; have e7 : c.fin = c.h + 16 + c.sz := rfl; simp only [StOK, LdOK, tohostAddr]; omega) | skip
      refine og_longStep hlive fx hmx h16 ih (ph.keep (ks := [10, 20, 25]) (by keeps_tac Keeps.refl _ _))
        (by bsimp [h20]) (by bsimp []) ?_
      bsimp []
      apply BitVec.eq_of_toNat_eq
      simp
    · intro h; exact absurd hne h

/-- **The integer digits printed** from `0x80007214`: `cur_dig` reloaded,
then the stack popped by the hex or the long loop. -/
theorem og_s6 {live S : Nat → Prop} {X0 : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat} {t : String}
    (fx : OgFix live S X0 Q I G Mt0 R0 sp W d L x z o ob cs) {fr bs mx : NumObj}
    (hmx : NewNum (Num.ofInt (ob - 1 : Nat)) mx)
    (hk6 : OgK6 live S X0 Q I G Mt0 R0 sp W L x ob cs fr bs mx) :
    OgK5 live S X0 Q I G Mt0 R0 sp W L x ob cs t fr bs mx := by
  intro R M H F ip cur cells ds Mc p lh
  have cx := fx.cx
  have cb := fx.cb
  have hob := fx.ha.obHi
  have hob2 := fx.ha.obLo
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => lh.st.heap.heap.own a h1 h2
  have h2 := lh.st.on.r2
  have hw40 : ldv .ld M (sp - 176 + 40) = BitVec.ofNat 64 cur.p :=
    lh.st.words.get (hs1 := [_, _]) (os1 := [16, 24]) (hs2 := [_, _]) (os2 := [32, 56]) rfl
  have hdig := lh.dig
  rw [show Num.digits ob 0 = [] from rfl, List.nil_append] at hdig
  have mk : ∀ R', Keeps [5, 8, 10, 20, 25, 26] R' R → R' 26 = BitVec.ofNat 64 cur.p →
      OgPH S X0 G I Mt0 M R0 R' sp W H F L x ob cs (cs ++ signOut x.rep.num) t ip fr bs mx cur
        cells ds Mc p := fun R' hk h26 =>
    { st := lh.st.regs hk
      curOK := lh.curOK
      stk := lh.stk
      ipn := lh.ipn
      p64 := lh.p64
      tgt := by rw [ogIntOut, hdig]
      dlt := fun dg hd => digits_lt (by omega) _ dg (by rw [hdig]; exact hd)
      regs :=
        ⟨by rw [hk.get 18 (by decide)]; exact lh.regs.r18,
          by rw [hk.get 19 (by decide)]; exact lh.r19,
          by rw [hk.get 23 (by decide)]; exact lh.regs.r23,
          by rw [hk.get 24 (by decide)]; exact lh.r24, h26,
          by rw [hk.get 27 (by decide)]; exact lh.regs.r27,
          by rw [hk.get 22 (by decide)]; exact lh.r22⟩ }
  have h21 := lh.r21
  bc_run hlive hS [h2, hw40, h21] at 0x8000721c 0x80007460
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · intro hne
    have hp : p ≠ 0 := fun e => hne (by rw [e])
    have ph0 := mk (upd R 26 (BitVec.ofNat 64 cur.p)) (by keeps_tac Keeps.refl _ _) (by bsimp [])
    obtain ⟨c, cs', dg, ds', hq, tp⟩ := ph0.top hp
    have hc := tp.cells
    have hd := tp.ds
    subst hc hd hq
    have hlo := tp.lo
    have hhi := tp.hi
    have hsz := tp.sz
    have hbp : c.pay = c.h + 16 := rfl
    have hbf : c.fin = c.h + 16 + c.sz := rfl
    have hb0 : (BitVec.ofNat 64 c.pay).toNat = c.pay := by rw [BitVec.toNat_ofNat]; omega
    have hb8 : (BitVec.ofNat 64 (c.pay + 8)).toNat = c.pay + 8 := by rw [BitVec.toNat_ofNat]; omega
    have hw := tp.word
    have hn := tp.next
    have h23 := lh.regs.r23
    bc_run hlive hS [h21, hb0, hb8, hw, hn, h23] at 0x8000748c 0x800074b8
    all_goals first | (have e6 : c.pay = c.h + 16 := rfl; have e7 : c.fin = c.h + 16 + c.sz := rfl; exact acc_heap hS (by omega) (by omega)) | (have e6 : c.pay = c.h + 16 := rfl; have e7 : c.fin = c.h + 16 + c.sz := rfl; simp only [StOK, LdOK, tohostAddr]; omega) | skip
    · intro hc
      have h16 : ¬ ob ≤ 16 := by
        rw [toInt_ofNat_small (k := ob) (by omega)] at hc; simp at hc; omega
      refine og_longStep hlive fx hmx h16 (og_longNext hlive fx hmx hk6 h16 cs')
        (ph0.keep (ks := [5, 10, 15, 20, 25]) (by keeps_tac Keeps.refl _ _)) (by bsimp [h21]) (by bsimp []) ?_
      bsimp []
      apply BitVec.eq_of_toNat_eq
      simp
    · intro hc
      have h16 : ob ≤ 16 := by
        rw [toInt_ofNat_small (k := ob) (by omega)] at hc; simp at hc; omega
      bc_run hlive hS [h21, hb0, hb8, hw, hn, h23] at 0x8000748c
      refine og_hexStep hlive fx h16 (og_hexNext hlive fx hk6 h16 cs')
        (ph0.keep (ks := [5, 8, 10, 15, 20, 25]) (by keeps_tac Keeps.refl _ _)) (by bsimp [h21]) (by bsimp []) ?_
        (by bsimp [])
      bsimp []
      apply BitVec.eq_of_toNat_eq
      simp
  · intro hz
    have hp : p = 0 := by
      have e := congrArg BitVec.toNat (Classical.not_not.mp hz)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lh.p64] at e
      simpa using e
    subst hp
    have hc := lh.stk.cells
    have hcl : cells = [] := hc.zero_iff.mp rfl
    subst hcl
    have hl := hc.length
    match ds, hl with
    | [], _ =>
    refine hk6 t _ M H F ip cur ((mk _ ?_ ?_).done cx cb) lh.curOK lh.ipn (mk _ ?_ ?_).regs
    all_goals first | (keeps_tac Keeps.refl _ _) | bsimp [hw40]

end Dc.Mach
