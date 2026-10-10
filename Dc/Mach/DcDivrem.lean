import Dc.Mach.DcBinop2
import Dc.Mach.DcRaise

/-!
# dc's quotient and remainder (M9)

    dc_divrem (a, b, kscale, quotient, remainder):
      bc_init_num (quotient);
      bc_init_num (remainder);
      if (bc_divmod (a, b, quotient, remainder, kscale)) {
        fprintf (stderr, "%s: divide by zero\n", progname);
        return DC_DOMAIN_ERROR;
      }
      return DC_SUCCESS;

On division by zero both `_zero_` references `bc_init_num` stored in the
slots are lost.

- `DcDen.dropAt`, `DcAt.newNum2`: two handles' numbers dropped, two fresh
  numbers added (`bc_divmod`'s `DmPostQ`).
- `OpRet2.of_dmPostQ`, `OpFail2.of_leak2`.
- `dc_divrem_spec`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-! ## Two results -/

/-- **A handle's reference dropped** at its pointer (`DropAt`): the ghost
state without the handle, the constants at the same addresses. -/
theorem DcDen.dropAt {L Lm : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {p : Nat} (d : DcDen L C G (.num p :: hs) st) (hd : PDist L) (hm : DropAt L p Lm) :
    ∃ C', DcDen Lm C' G hs st ∧ C.SameP C' ∧ PDist Lm ∧
      HsKeep ⟨L, G.strs⟩ ⟨Lm, G.strs⟩ hs := by
  obtain ⟨L1, L2, x, rfl, rfl, hf⟩ := hm
  cases hf with
  | dec _ =>
    exact ⟨_, d.dec hd.ne, C.sameP_subst rfl rfl,
      hd.congr (by simp only [List.map_append, List.map_cons]; rfl), HsKeep.decRef hs⟩
  | rel h1 =>
    exact ⟨C, d.rel hd.ne h1, .refl C,
      hd.sublist (List.Sublist.append (List.Sublist.refl _) (List.sublist_cons_self _ _)),
      HsKeep.rel d h1 _⟩

/-- **Two fresh numbers for two freed handles**: a callee dropped the
references of the handles `.num pr`, `.num pq` (in that order) and added
`yq`, then `yr`, each with one reference. -/
theorem DcAt.newNum2 {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F F' : List Blk}
    {L Lm Lf : List NumObj} {yq yr : NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    {pr pq : Nat} {nq nr : Num}
    (h : DcAt S M H F L C G (.num pr :: .num pq :: hs) st) (hm1 : DropAt L pr Lm)
    (hm2 : DropAt Lm pq Lf) (hb : BcHeap S (G.raws M) M' H' F' (yr :: yq :: Lf))
    (hq : NewNum nq yq) (hr : NewNum nr yr) (hgl : ∀ a, DcGlob a → imgM M' a = imgM M a) :
    ∃ C', DcAt S M' H' F' (yr :: yq :: Lf) C' G (.num yq.rep.p :: .num yr.rep.p :: hs) st ∧
      HsKeep ⟨L, G.strs⟩ ⟨yr :: yq :: Lf, G.strs⟩ hs := by
  have hag : ∀ a, InBlocks G.blocks a → imgM M' a = imgM M a := fun a ⟨c, hc, ha⟩ =>
    hb.raw.img c hc a ha
  have hb' : BcHeap S (G.raws M') M' H' F' (yr :: yq :: Lf) :=
    hb.subRaw (X' := G.raws M') (fun c hc => hc) fun c hc a ha => (hag a ⟨c, hc, ha⟩).symm
  obtain ⟨C1, d1, s1, p1, k1⟩ := h.den.dropAt h.heap.pdist hm1
  obtain ⟨C2, d2, s2, -, k2⟩ := d1.dropAt p1 hm2
  have hbq : BcHeap S (G.raws M) M' H' F' ([yr] ++ yq :: Lf) := hb
  have hbr : BcHeap S (G.raws M) M' H' F' ([] ++ yr :: yq :: Lf) := hb
  have d3 := d2.addNum (y := yq) (fun z hz => hbq.p_ne_all z (by simp [hz])) hq.refs hq.norm
    hq.pos hq.owns
  have d4 := d3.addNum (y := yr) (fun z hz => hbr.p_ne_all z (by simpa using hz)) hr.refs hr.norm
    hr.pos hr.owns
  exact ⟨C2, ⟨hb', h.nodup, (h.view.frame hag hgl).sameP (s1.trans s2), d4.swap, h.glob, h.col⟩,
    ((k1.mono fun g hg => List.mem_cons_of_mem _ hg).trans k2).trans
      ((HsKeep.cons hs).trans (HsKeep.cons hs))⟩

/-- **A two-result operation's success from `bc_divmod`'s results** `yq`, `yr`
in the slots (window `W` below `sp'`, inside the operation's `N` below `sp`). -/
theorem OpRet2.of_dmPostQ {S : Nat → Prop} {M M2 Mt : Mem} {H H3 : Heap} {F F3 : List Blk}
    {L Lf : List NumObj} {xq xr yq yr : NumObj} {C2 : BcConsts} {G : DcG} {hs : List GV}
    {st : St} {pa pb : Nat} {na nb : Num} {m : Num × Num}
    {f : Nat → Num → Num → Option (Num × Num)} {sp qq qr N sp' W lk : Nat}
    (hd2 : DcAt S M2 H F L C2 G (.num xr.rep.p :: .num xq.rep.p :: .num pa :: .num pb :: hs) st)
    (hp : DmPostQ S (G.raws M2) M2 Mt H3 F3 L xq xr qq qr sp' W m Lf yq yr)
    (hval : f st.scale na nb = some m) (hw1 : sp' ≤ sp) (hw2 : sp - N ≤ sp' - W)
    (hab : heapEnd ≤ sp' - W) (hq : sp ≤ qq) (hqr : qq + 8 ≤ qr)
    (hout0 : ∀ a, OutHeap a → ¬ slots2 qq qr a → ¬ frameIn sp N a → imgM M2 a = imgM M a) :
    ∃ C3, ∀ R' : Nat → BitVec 64, R' 10 = 0#64 →
      OpRet2 S M Mt H3 F3 (yr :: yq :: Lf) C3 G G hs st pa pb na nb f R' sp qq qr N lk
        yq.rep.p yr.rep.p m.1 m.2 := by
  simp only [heapEnd] at hab
  obtain ⟨Lm, hm1, hm2⟩ := hp.mid
  obtain ⟨C3, hd3, -⟩ := hd2.newNum2 hm1 hm2 hp.heap hp.quo.toNewNum hp.rem.toNewNum fun a ha =>
    hp.out a ha.outHeap
      (fun hs => by have := ha.lt; simp only [heapStart, slotBytes] at this hs; omega)
      (fun hs => by have := ha.lt; simp only [heapStart, slotBytes] at this hs; omega)
      (fun hf => by have := ha.lt; simp only [heapStart, frameIn] at this hf; omega)
  exact ⟨C3, fun R' ha0 => ⟨ha0, hd3, hval,
    ⟨yq, List.mem_cons_of_mem _ List.mem_cons_self, rfl, hp.quo.num⟩,
    ⟨yr, List.mem_cons_self, rfl, hp.rem.num⟩,
    by rw [hp.quo.slot, (hp.heap.blocks yq (List.mem_cons_of_mem _ List.mem_cons_self)).sPay],
    by rw [hp.rem.slot, (hp.heap.blocks yr List.mem_cons_self).sPay], rfl, by omega,
    fun a ho _ hf hs => by
      rw [hp.out a ho (fun h' => hs (.inl h')) (fun h' => hs (.inr h'))
        fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)]
      exact hout0 a ho hs hf⟩⟩

/-- **A two-result operation's failure that loses both slots' handles**
`p1`, `p2`, the memory changed only on `P` (off the heap and the globals). -/
theorem OpFail2.of_leak2 {S : Nat → Prop} {M M2 M' : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p1 p2 pa pb : Nat}
    {na nb : Num} {f : Nat → Num → Num → Option (Num × Num)} {sp qq qr N : Nat}
    {P : Nat → Prop} {x1 x2 : NumObj}
    (hd2 : DcAt S M2 H F L C G (.num p1 :: .num p2 :: .num pa :: .num pb :: hs) st)
    (hl : G.lk.length + 2 ≤ 2 ^ 29)
    (hx1 : x1 ∈ L) (e1p : x1.rep.p = pa) (e1n : x1.rep.num = na)
    (hx2 : x2 ∈ L) (e2p : x2.rep.p = pb) (e2n : x2.rep.num = nb)
    (hnone : f st.scale na nb = none)
    (hm : MemOnly P M' M2) (hP : ∀ a, P a → OutHeap a ∧ ¬ DcGlob a)
    (hout : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp N a → ¬ slots2 qq qr a →
      imgM M' a = imgM M a)
    (R' : Nat → BitVec 64) (ha0 : R' 10 ≠ 0#64) :
    OpFail2 S M M' H F L C G { G with lk := p2 :: p1 :: G.lk } hs st pa pb na nb f R' sp qq qr
      N 2 where
  a0 := ha0
  h := (((hd2.leak (by omega)).leak (by simp only [List.length_cons]; omega))).outWrite hm hP
  val := hnone
  da := ⟨x1, hx1, e1p, e1n⟩
  db := ⟨x2, hx2, e2p, e2n⟩
  same := rfl
  lkLen := by simp only [List.length_cons]; omega
  out := hout

/-- `_zero_` at one address in two states whose words at `zeroAddr` agree. -/
theorem DcAt.zeroP_eq {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F F' : List Blk}
    {L L' : List NumObj} {C C' : BcConsts} {G G' : DcG} {hs hs' : List GV} {st st' : St}
    (h : DcAt S M H F L C G hs st) (h' : DcAt S M' H' F' L' C' G' hs' st')
    (hz : ldv .ld M' zeroAddr = ldv .ld M zeroAddr) : C'.z.rep.p = C.z.rep.p := by
  have hz2 : BitVec.ofNat 64 C'.z.rep.p = BitVec.ofNat 64 C.z.rep.p := by
    rw [← h'.view.zw, hz, h.view.zw]
  have hn0 := h'.heap.nums C'.z h'.den.mz
  have hnz := h.heap.nums C.z h.den.mz
  have a1 := hn0.shape.pLo; have a2 := hn0.shape.pHi
  have b1 := hnz.shape.pLo; have b2 := hnz.shape.pHi
  simp only [heapStart, heapEnd] at a1 a2 b1 b2
  bv_nat at hz2
  omega

/-! ## `dc_divrem` -/

/-- `dc_divrem`'s 48-byte frame: `OpFrame48` and `s2` at `16`. -/
structure DrFrame (M : Mem) (sp : Nat) (R : Nat → BitVec 64) (k pb : Nat) : Prop
    extends OpFrame48 M sp R k pb where
  w16 : ldv .ld M (sp - 48 + 16) = R 18

theorem DrFrame.transport {M M' : Mem} {sp : Nat} {R : Nat → BitVec 64} {k pb : Nat}
    (h : DrFrame M sp R k pb) (hsp : 48 ≤ sp)
    (hag : ∀ a, sp - 48 ≤ a → a < sp → imgM M' a = imgM M a) : DrFrame M' sp R k pb where
  toOpFrame48 := h.toOpFrame48.transport hsp hag
  w16 := by
    rw [ldv_congr .ld fun j hj => hag _ (by omega) (by simp only [widthOfM] at hj; omega)]
    exact h.w16

/-- **`dc_divrem`'s two `bc_init_num` calls** (`0x800023c8`, `0x800023d0`),
its frame stored: both slots hold new `_zero_` handles. -/
theorem dr_init {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M M1 : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pa pb : Nat}
    {na nb : Num} {R : Nat → BitVec 64} {sp qq qr N lk : Nat}
    (hin : OpIn2 S M H F L C G hs st pa pb na nb R sp qq qr N lk) (hN : 48 ≤ N)
    (hM1 : MemOnly (frameIn sp 48) M1 M) (fr : DrFrame M1 sp R st.scale pb)
    (R1 : Nat → BitVec 64) (r10 : R1 10 = BitVec.ofNat 64 qq) (r9 : R1 9 = BitVec.ofNat 64 qr)
    (r1 : R1 1 = 0x800023cc#64)
    (hk : ∀ R3 M3 L3 C3 x1 x2, Keeps [1, 10, 14, 15] R3 R1 → R3 1 = 0x800023d4#64 →
      DcAt S M3 H F L3 C3 G (.num C3.z.rep.p :: .num C3.z.rep.p :: .num pa :: .num pb :: hs) st →
      ldv .ld M3 qq = BitVec.ofNat 64 C3.z.rep.p → ldv .ld M3 qr = BitVec.ofNat 64 C3.z.rep.p →
      x1 ∈ L3 → x1.rep.p = pa → x1.rep.num = na →
      x2 ∈ L3 → x2.rep.p = pb → x2.rep.num = nb →
      (∀ a, OutHeap a → ¬ slots2 qq qr a → ¬ frameIn sp 48 a → imgM M3 a = imgM M a) →
      DrFrame M3 sp R st.scale pb → DWO live S Q t 0x800023d4#64 R3 M3) :
    DWO live S Q t 0x800049bc#64 R1 M1 := by
  have hsf := hin.frame
  have hsl := hsf.lo
  have hab := hin.above
  simp only [heapEnd] at hab
  have hqs := hin.hiQ
  have hap := hin.apart
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have hP : ∀ a, frameIn sp 48 a → OutHeap a ∧ ¬ DcGlob a := fun a ha =>
    ⟨(above_sp (sp := sp - 48) hab2 (a := a) (by simp only [frameIn] at ha; omega)).1,
     (above_sp (sp := sp - 48) hab2 (a := a) (by simp only [frameIn] at ha; omega)).2.1⟩
  have h1 := hin.h.outWrite hM1 hP
  have hlen : (GV.num pa :: GV.num pb :: hs).length ≤ 2 ^ 30 := by
    have := hin.hsLen; simp only [List.length_cons]; omega
  refine dc_init_num_spec hlive h1 hlen hin.slotQ (by simp only [heapEnd]; omega) R1 r10
    (by rw [r1]; decide) fun R2 M2 L2 C2 hk2 hd2 hkeep2 hw2 hfr2 => ?_
  have hS2 : HeapOwn S := fun a e1 e2 => hd2.heap.heap.own a e1 e2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have q9 : R2 9 = BitVec.ofNat 64 qr := by rw [hk2.get 9 (by decide), r9]
  have q1 : R2 1 = 0x800023cc#64 := by rw [hk2.get 1 (by decide), r1]
  rw [r1]
  bc_run hlive hS2 [q9] at 0x800049bc
  have hlen2 : (GV.num C.z.rep.p :: GV.num pa :: GV.num pb :: hs).length ≤ 2 ^ 30 := by
    have := hin.hsLen; simp only [List.length_cons]; omega
  refine dc_init_num_spec hlive hd2 hlen2 hin.slotR (by simp only [heapEnd]; omega) _
    (by bsimp []) (by bsimp []) fun R3 M3 L3 C3 hk3 hd3 hkeep3 hw3 hfr3 => ?_
  have e1 : C2.z.rep.p = C.z.rep.p := h1.zeroP_eq hd2 (ldv_congr .ld fun j hj =>
    hfr2 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, widthOfM,
        dc_addrs] at hj ⊢; omega)
      (fun hs => by simp only [slotBytes, widthOfM, dc_addrs] at hs hj; omega))
  have e2 : C3.z.rep.p = C2.z.rep.p := hd2.zeroP_eq hd3 (ldv_congr .ld fun j hj =>
    hfr3 _ (by simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr, widthOfM,
        dc_addrs] at hj ⊢; omega)
      (fun hs => by simp only [slotBytes, widthOfM, dc_addrs] at hs hj; omega))
  rw [← e1, ← e2] at hd3
  rw [← e2] at hw3
  have hkeep := (hkeep2.trans (hkeep3.mono fun g hg => List.mem_cons_of_mem _ hg))
  obtain ⟨x1, hx1, e1p, e1n⟩ := (hkeep _ List.mem_cons_self _ hin.da).numObj
  obtain ⟨x2, hx2, e2p, e2n⟩ :=
    (hkeep _ (List.mem_cons_of_mem _ List.mem_cons_self) _ hin.db).numObj
  have hout : ∀ a, OutHeap a → ¬ slots2 qq qr a → ¬ frameIn sp 48 a → imgM M3 a = imgM M a :=
    fun a ho hs hf => by
      rw [hfr3 a ho fun h' => hs (.inr h'), hfr2 a ho fun h' => hs (.inl h')]
      exact hM1 a hf
  refine hk R3 M3 L3 C3 x1 x2 ((hk3.mono (by decide)).trans (by keeps_tac (hk2.mono (by decide))))
    (by rw [hk3.get 1 (by decide)]; bsimp []) hd3
    (by
      rw [ldv_congr .ld fun j hj => hfr3 _ (outHeap_of_ge (by
          simp only [widthOfM, heapEnd] at hj ⊢; omega))
        (fun hs => by simp only [slotBytes, widthOfM] at hs hj; omega), hw2, ← e1, ← e2])
    hw3 hx1 e1p e1n hx2 e2p e2n hout
    (fr.transport (by omega) fun a e1 e2 => by
      have ho := (above_sp hab2 e1).1
      rw [hfr3 a ho fun hs => by simp only [slotBytes] at hs; omega,
        hfr2 a ho fun hs => by simp only [slotBytes] at hs; omega])

end Dc.Mach
