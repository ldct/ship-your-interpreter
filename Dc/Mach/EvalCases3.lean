import Dc.Mach.EvalCases2

/-!
# `evalstr`'s loop: the rest of the string, `DC_COMMENT` (M10)

`EvRest`: the text after the command (`s0 + 1` to the end) in memory, owned
and in the state's blocks, NUL-terminated (`EvAt.rest`). It feeds the
callees that scan the rest (`memchr` for `DC_COMMENT`, `dc_system`).
`evs_comment`: `DC_COMMENT` continues after the next newline, or ends the
string's evaluation when there is none.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **The text after the command** at `a` (registers `R` with `s0` at the
command, `s1` at the end). -/
structure EvRest (S : Nat → Prop) (M : Mem) (G : DcG) (R : Nat → BitVec 64) (a : Nat)
    (rest : List Nat) : Prop where
  r8 : R 8 + 1#64 = BitVec.ofNat 64 a
  r9 : R 9 = BitVec.ofNat 64 (a + rest.length)
  own : OwnedBytes S a (rest.length + 1)
  val : ∀ j, j < rest.length → imgM M (a + j) = BitVec.ofNat 8 (rest.getD j 0)
  nul : imgM M (a + rest.length) = 0
  byte : ∀ x ∈ rest, x < 256
  inb : ∀ j, j ≤ rest.length → InBlocks G.blocks (a + j)
  len : a + rest.length < 2 ^ 60

/-- The owned text without its NUL. -/
theorem EvRest.ownRest {S : Nat → Prop} {M : Mem} {G : DcG} {R : Nat → BitVec 64} {a : Nat}
    {rest : List Nat} (h : EvRest S M G R a rest) : OwnedBytes S a rest.length :=
  ⟨fun j hj => h.own.own j (by omega), h.own.lo, by have := h.own.hi; omega⟩

theorem EvAt.rest {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64}
    {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG}
    {hs xs : List GV} {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨c :: rest, td, neg⟩ o) :
    ∃ a, EvRest S M G R a rest := by
  obtain ⟨i, hi, hdrop, h8⟩ := ev.pos
  have hso := ev.dc.view.strs o ev.strIn
  have hmem : o.tb ∈ G.blocks :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ev.strIn, by simp⟩))
  have bt := blk_bounds ev.dc.heap.heap (ev.dc.heap.raw.live o.tb hmem)
  have htz := hso.tsz
  have hlen : (o.s.drop i).length = rest.length + 1 := by rw [hdrop]; rfl
  rw [List.length_drop] at hlen
  have hget : ∀ j, rest.getD j 0 = o.s.getD (i + 1 + j) 0 := fun j => by
    have := congrArg (fun l => l.getD (j + 1) 0) hdrop
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_cons_succ] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← this,
      show i + (j + 1) = i + 1 + j by omega]
  have hS : HeapOwn S := fun a e1 e2 => ev.dc.heap.heap.own a e1 e2
  simp only [heapStart, heapEnd] at bt hS
  refine ⟨o.tb.pay + i + 1, ?_⟩
  exact
    { r8 := by rw [h8, show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      r9 := by rw [ev.s1]; congr 1; omega
      own := ⟨fun j hj => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega),
        by simp only [tohostAddr]; omega, by omega⟩
      val := fun j hj => by
        rw [hget, show o.tb.pay + i + 1 + j = o.tb.pay + (i + 1 + j) by omega]
        exact hso.bytes _ (by omega)
      nul := by
        rw [show o.tb.pay + i + 1 + rest.length = o.tb.pay + o.s.length by omega]; exact hso.nul
      byte := fun x hx => hso.byte x (List.mem_of_mem_drop (show x ∈ o.s.drop i by
        simp only at hdrop; rw [hdrop]; exact List.mem_cons_of_mem _ hx))
      inb := fun j hj => ⟨o.tb, hmem, by simp only [Blk.In, Blk.fin, Blk.pay] at htz ⊢; omega⟩
      len := by omega }

section

variable {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
  {t0 : String} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
  {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
  {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
  {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {H' : Heap} {F' : List Blk} {L' : List NumObj}
  {C' : BcConsts} {G' : DcG} {st'' : St} {ex : List GV} {r : Status} {n : Nat}
  {Ge : DcG} {hse xse : List GV} {ke : Nat}

/-- **`DC_COMMENT`** (`0x800015a8`, from either dispatch table): on after
the next newline, or the exit. -/
theorem evs_comment_at (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex) (hlc : leakOne c ≤ k)
    (hhead : EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs st
      ⟨skipEol rest, td, false⟩)
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st ⟨skipEol rest, td, false⟩)
    {R1 : Nat → BitVec 64} (k1 : Keeps [10, 15] R1 R') :
    DWO live S Q (t0 ++ Dc.outStr st.out) 0x800015a8#64 R1 M' := by
  obtain ⟨o0, -, -, -, ev0⟩ := e.same (e.hal hlc) e.ev.sb e.ev.srt (R2 := R1) (k1.mono (by decide))
  obtain ⟨a, er⟩ := ev0.rest
  have h23 : R' 23 = BitVec.ofNat 64 a := by
    rw [e.k1.get 23 (by decide), e.c23, ← er.r8, k1.get 8 (by decide), e.k1.get 8 (by decide),
      e.kc.get 8 (by decide)]
  have hf := skipEol_find (imgM M') rest a er.val er.byte
  refine rt_comment hlive er.ownRest (by rw [k1.get 23 (by decide)]; exact h23) er.r9
    (fun hn R2 k2 => ?_) (fun p hp R2 k2 h8 h12 => ?_)
  · obtain ⟨o2, -, -, -, ev2⟩ := e.same (e.hal hlc) e.ev.sb e.ev.srt (R2 := R2)
      ((k2.mono (by decide)).trans (k1.mono (by decide)))
    exact hend (hf.2 hn) _ R2 M' H' F' L' C' G' _ _ o2 ev2 (e.grow0 hlc) e.pin0
  · have hm := hf.1 p hp
    have hle : (skipEol rest).length ≤ rest.length := by rw [skipEol_drop rest]; simp
    obtain ⟨o', -, -, -, ev'⟩ := ev_adv e.ev e.kc e.c23 e.mem e.k1 e.e2 e.post (e.hal hlc) e.ev.sb
      e.ev.srt (m := rest.length - (skipEol rest).length) (td' := td) (neg' := false) (by omega)
      e.ev.tdLt (R2 := R2) ((k2.mono (by decide)).trans (k1.mono (by decide)))
      (by rw [h8, h23, BitVec.ofNat_add_ofNat, hm])
      (by rw [k2.get 24 (by decide), k1.get 24 (by decide), e.k1.get 24 (by decide),
        e.kc.get 24 (by decide)]; exact e.ev.s8)
    rw [← skipEol_drop rest] at ev'
    exact ev_cont_k (bltu_800015c4 hlive) ev' h12 (e.grow0 hlc) e.pin0 hhead hend

/-- **`DC_COMMENT`**: the status dispatch then `evs_comment_at`. -/
theorem evs_comment_k (hlive : ∀ p ∈ dcText, live p.1)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex) (h10 : R' 10 = BitVec.ofNat 64 8) (hlc : leakOne c ≤ k)
    (hhead : EvHeadK live S Q t0 sp W d k (k - leakOne c) q M0 R0 G hs xs st
      ⟨skipEol rest, td, false⟩)
    (hend : EvEndK live S Q t0 sp W d k q M0 R0 G hs xs st ⟨skipEol rest, td, false⟩) :
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  split
  · exact evl_8 hlive h10 e.cs fun R1 k1 => evs_comment_at hlive e hlc hhead hend k1
  · exact evm_8 hlive h10 e.cs fun R1 k1 => evs_comment_at hlive e hlc hhead hend k1

/-- **`DC_COMMENT`** (term direction). -/
theorem evs_comment (hlive : ∀ p ∈ dcText, live p.1) (IH : LoopIH live S Q n)
    (e : EvCall S sp W d k q M0 R0 R M H F L C G hs xs st c rest td neg o Rc R' Mc M' H' F' L' C'
      G' st ex)
    (hres : dcFunc 70 st c rest.head? neg = .comment) (h10 : R' 10 = BitVec.ofNat 64 8)
    (hfu : EvFuel 70 (n + 1) d k st ⟨c :: rest, td, neg⟩ st'' r) (hoom : EvOom live S Q sp W q M0)
    (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail) (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r) :
    DWO live S Q (t0 ++ Dc.outStr st.out) (if rest = [] then 0x80001728#64 else 0x80001528#64) R' M' := by
  obtain ⟨hfu', -, hlc⟩ := hfu.comment hres
  exact evs_comment_k hlive e h10 hlc (EvHeadK.ofIH IH hfu' hoom htl hgrow hpin hk)
    (EvEndK.ofFuel hlive hfu' htl hgrow hpin hk)

end

end Dc.Mach
