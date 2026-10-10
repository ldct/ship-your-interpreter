import Dc.Mach.EvalJoin

/-!
# `evalstr`: advancing after `dc_func` (M10)

`ev_adv`: after `dc_func` returned (`EvRet`'s data: the registers at the
call `Rc` with `s7 = s0 + 1`, the post `FnPost`), a status route that moves
`s0` to `s7 + m` (`m` more characters skipped) and sets `next_negcmp` and
`tail_depth` re-establishes `EvAt` over the frame `⟨rest.drop m, td', neg'⟩`.
`ev_cont`: the loop test after it, the head by the caller's continuation,
the exit by `ev_exit`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **The loop test, closed**: the head by `hhead`, an empty rest by the
exit with the evaluation's result. -/
theorem ev_cont {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {p : Nat} (hb : BltuAt live S Q p) {t0 : String}
    {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV} {st st'' : St} {f : Frame}
    {o : StrObj} {r : Status} {n d' k' : Nat}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st f o) (hfu : EvFuel 70 n d' k' st f st'' r)
    {Ge : DcG} {hse xse : List GV} {ke : Nat} (htl : hs.tail = hse.tail)
    (hgrow : G.lk.length + xs.length + 4 * k ≤ Ge.lk.length + xse.length + 4 * ke)
    (hpin : StrPin Ge.strs G.strs hs.tail)
    (hk : EvK live S Q t0 sp W ke q M0 R0 Ge hse xse st'' r)
    (hhead : f.s ≠ [] → DWO live S Q (t0 ++ Dc.outStr st.out) 0x800014f8#64 R M) :
    DWO live S Q (t0 ++ Dc.outStr st.out) (BitVec.ofNat 64 p) R M := by
  refine ev_join hb ev hhead fun he => ?_
  obtain ⟨s, td, neg⟩ := f
  simp only at he
  subst he
  obtain ⟨rfl, rfl⟩ := hfu.nil
  exact ev_exit hlive ev htl hgrow hpin hk

/-- **The invariant after a status route** that sets `s0 = s7 + m`,
`next_negcmp` and `tail_depth` (registers `R2`, all else as after the
call). -/
theorem ev_adv {S : Nat → Prop} {sp W d k q : Nat} {M0 : Mem} {R0 R : Nat → BitVec 64} {M : Mem}
    {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts} {G : DcG} {hs xs : List GV}
    {st : St} {c : Nat} {rest : List Nat} {td : Nat} {neg : Bool} {o : StrObj}
    (ev : EvAt S sp W d k q M0 R0 R M H F L C G hs xs st ⟨c :: rest, td, neg⟩ o)
    {Rc R' : Nat → BitVec 64} {Mc M' : Mem} {w : BitVec 64}
    (hkc : Keeps [1, 10, 11, 15, 23] Rc R) (h23 : Rc 23 = R 8 + 1#64) (hmem : EvCallMem sp M Mc w)
    (k1 : Keeps cClob R' Rc) (e2 : R' 2 = Rc 2)
    {H' : Heap} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {G' : DcG} {st' : St}
    {ex : List GV} {al k' : Nat}
    (hp : FnPost S al (sp - 176) (W - 176) Mc G (xs ++ hs) M' H' F' L' C' G' st' ex)
    (hal : al + 4 * k' ≤ 4 * k) (hsb : StrBound (2 ^ 24) st') (hsrt : ArrSorted st')
    {m td' : Nat} {neg' : Bool} (hm : m ≤ rest.length) (htd : td' < 2 ^ 31)
    {R2 : Nat → BitVec 64} (k2 : Keeps (8 :: 12 :: 24 :: 25 :: cClob) R2 R')
    (h8 : R2 8 = R' 23 + BitVec.ofNat 64 m) (h24 : R2 24 = BitVec.ofNat 64 td') :
    ∃ o', o'.hb = o.hb ∧ o'.tb = o.tb ∧ o'.s = o.s ∧
      EvAt S sp W d k' q M0 R0 R2 M' H' F' L' C' G' hs (ex ++ xs) st' ⟨rest.drop m, td', neg'⟩ o' := by
  obtain ⟨i, hi, hdrop, hr8⟩ := ev.pos
  have hlen : (o.s.drop i).length = rest.length + 1 := by rw [hdrop]; rfl
  rw [List.length_drop] at hlen
  have hso := ev.dc.view.strs o ev.strIn
  have bt := blk_bounds ev.dc.heap.heap (ev.dc.heap.raw.live o.tb
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ev.strIn, by simp⟩))))
  have htz := hso.tsz
  simp only [heapStart, heapEnd] at bt
  have cs := ev.cs
  refine ev.next hmem.only hp hal (j := i + 1 + m) (by omega) ?_ ?_ ?_ ?_ h24 htd ?_ ?_ ?_ hsb hsrt
  · show o.s.drop (i + 1 + m) = rest.drop m
    have e : o.s.drop (i + 1 + m) = ((o.s.drop i).drop 1).drop m := by
      rw [List.drop_drop, List.drop_drop]; congr 1; omega
    rw [e, hdrop]; rfl
  · rw [h8, k1.get 23 (by decide), h23, hr8, show (1#64) = BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
    congr 1; omega
  · rw [k2.get 9 (by decide), k1.get 9 (by decide), hkc.get 9 (by decide)]
  · rw [k2.get 22 (by decide), k1.get 22 (by decide), hkc.get 22 (by decide)]
  · exact ⟨by rw [k2.get 18 (by decide), k1.get 18 (by decide), hkc.get 18 (by decide)]; exact cs.s2,
      by rw [k2.get 19 (by decide), k1.get 19 (by decide), hkc.get 19 (by decide)]; exact cs.s3,
      by rw [k2.get 20 (by decide), k1.get 20 (by decide), hkc.get 20 (by decide)]; exact cs.s4,
      by rw [k2.get 21 (by decide), k1.get 21 (by decide), hkc.get 21 (by decide)]; exact cs.s5⟩
  · rw [k2.get 2 (by decide), e2, hkc.get 2 (by decide)]
  · exact ((k2.mono (by decide)).trans (k1.mono (by decide))).trans (hkc.mono (by decide))

end Dc.Mach
