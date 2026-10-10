import Dc.Mach.Bc.SqrtBase

/-!
# Callees on a handle from any caller's frame

A caller with `sp` lowered by `Fz` inside its window `W` (`CallerCtx`) keeps
its numbers as handles (`RList hs L`, `RaiseModHeap.lean`) and passes a
frame word `sp - Fz + o` as a callee's result slot. The callee's new number
replaces the handle. The caller's `out_of_memory` continuation (`HcOom`) may
let the bytes `P` change besides the window.

- `HcOom`, `HcOom.lift`: `out_of_memory` from a callee below the frame.
- `hc_mulH`, `hc_subH`, `hc_divH`, `hc_modH`, `hc_i2nH`: `bc_multiply`,
  `bc_sub`, `bc_divide`, `bc_divmod` for the remainder (`bc_modulo`) and
  `bc_int2num` into a handle's slot.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A caller's `out_of_memory` continuation: off the heap only the window
and the bytes `P` changed since `Mt0`. -/
def HcOom (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (Mt0 : Mem)
    (sp W : Nat) (P : Nat → Prop) : Prop :=
  ∀ R' Mt' sp', sp - W ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
    (∀ a, OutHeap a → ¬ P a → ¬ frameIn sp W a → imgM Mt' a = imgM Mt0 a) →
    DW live S Q 0x80002bcc#64 R' Mt'

/-- **`out_of_memory` from a callee below the frame**, whose own exception
`E` lies in the caller's window. -/
theorem HcOom.lift {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {Mt0 M : Mem} {sp W Fz : Nat} {P : Nat → Prop} (h : HcOom live S Q Mt0 sp W P)
    (hF : Fz ≤ W) (houtM : ∀ a, OutHeap a → ¬ P a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    {E : Nat → Prop} (hE : ∀ a, E a → frameIn sp W a) :
    ∀ R' Mt' sp', sp - Fz - (W - Fz) ≤ sp' → sp' ≤ sp - Fz → R' 2 = BitVec.ofNat 64 sp' →
      (∀ a, OutHeap a → ¬ E a → ¬ frameIn (sp - Fz) (W - Fz) a → imgM Mt' a = imgM M a) →
      DW live S Q 0x80002bcc#64 R' Mt' :=
  fun R' Mt' sp' h1 h2 hr2 hout => h R' Mt' sp' (by omega) (by omega) hr2 fun a ha hp hf => by
    rw [hout a ha (fun he => hf (hE a he)) (fun h' => hf (by simp only [frameIn] at h' ⊢; omega))]
    exact houtM a ha hp hf

/-- The frame of a handle call: the caller's window, a 16-aligned frame of
`Fz` bytes and the handle's word at `o` in its first 64 bytes. -/
structure HcFrame (S : Nat → Prop) (sp W Fz o : Nat) : Prop where
  cc : CallerCtx S sp W
  room : Fz + 512 + rmStack (2 ^ 30) ≤ W
  f16 : Fz % 16 = 0
  slot : o + 8 ≤ Fz
  o8 : o % 8 = 0

/-- The facts of `HcFrame` as `omega` sees them. -/
macro "hc_facts " fr:term : tactic =>
  `(tactic| (cf_facts ($fr).cc
             have _hroom := ($fr).room
             have _hfz := ($fr).f16
             have _hfs := ($fr).slot
             have _hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega))

theorem HcFrame.dslot {S : Nat → Prop} {sp W Fz o : Nat} (fr : HcFrame S sp W Fz o) :
    DmSlot S (sp - Fz) (W - Fz) (sp - Fz + o) := by
  hc_facts fr
  exact fr.cc.slot (by omega) fr.slot fr.o8 fr.f16

theorem HcFrame.inWin {S : Nat → Prop} {sp W Fz o : Nat} (fr : HcFrame S sp W Fz o) :
    ∀ a, slotBytes (sp - Fz + o) a → frameIn sp W a := by
  hc_facts fr
  intro a ha; simp only [slotBytes, frameIn] at ha ⊢; omega

/-- **A callee's new number for a handle's slot** (`BinPostW`): the heap with
the handle replaced, and the number in the slot. -/
theorem hc_binRet {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {M M' : Mem} {R R' : Nat → BitVec 64} {sp W Fz o Wc : Nat} {H : Heap} {F : List Blk}
    {hs1 hs2 : List RH} {h : RH} {L L1 L2 L' : List NumObj} {x y : NumObj} {n : Num}
    (hown : RHOwn (hs1 ++ h :: hs2) L) (hfr : ∀ L', FreedRest L1 L2 x L' → L' = RList (hs1 ++ hs2) L)
    (hp : BinPostW S X M M' H F L1 L2 x (sp - Fz + o) (sp - Fz) Wc n L' y) (hWc : Wc ≤ W - Fz)
    (hret : BcHeap S X M' H F (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      MulRes M' (sp - Fz + o) n y →
      (∀ a, OutHeap a → ¬ slotBytes (sp - Fz + o) a → ¬ frameIn (sp - Fz) (W - Fz) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q (R 1) R' M' := by
  obtain ⟨hb', hres, hown'⟩ := RList.binPost hown hfr hp
  exact hret hb' hown' hres fun a h1 h2 h3 =>
    hp.out a h1 h2 fun h' => h3 (by simp only [frameIn] at h' ⊢; omega)

/-- **`bc_multiply (u1, u2, &h, k)`** on the handle `h` (its word at
`sp - Fz + o`): the product replaces it. -/
theorem hc_mulH {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R : Nat → BitVec 64} {sp W Fz o k : Nat} {P : Nat → Prop}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {u1 u2 z : NumObj} {H : Heap} {F : List Blk}
    (fr : HcFrame S sp W Fz o) (hoom : HcOom live S Q Mt0 sp W P)
    (houtM : ∀ a, OutHeap a → ¬ P a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S X M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h) (ha : MulArgs M (RList (hs1 ++ h :: hs2) L) u1 u2 z k)
    (hw : ldv .ld M (sp - Fz + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - Fz)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - Fz + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ R' M' H' F' y, Keeps binClob R' R →
      BcHeap S X M' H' F' (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      MulRes M' (sp - Fz + o) (Num.mul u1.rep.num u2.rep.num k) y →
      (∀ a, OutHeap a → ¬ slotBytes (sp - Fz + o) a → ¬ frameIn (sp - Fz) (W - Fz) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000573c#64 R M := by
  hc_facts fr
  obtain ⟨L1, L2, x, e, hp, hr1, hnv, _, _, hfr⟩ := RList.slot hb hh hown
  rw [e] at hb ha
  have hsz := ha.size
  have hrs := rmStack_mono (show u1.rep.len + u1.rep.scale + (u2.rep.len + u2.rep.scale) ≤ 2 ^ 30
    by omega)
  have hl := hoom.lift (Fz := Fz) (by omega) houtM (E := fun _ => False) (fun _ h => h.elim)
  refine bc_multiply_spec hlive (fr.cc.mul (F := Fz) (by omega) fr.f16 fr.dslot h2 hal)
    ha (by omega) hb ⟨hr1, by rw [hw, hp], hnv⟩ h10 h11 h12 h13
    ⟨fun R' M' H' F' L' y hk hp' => hc_binRet hown hfr hp' (by omega) (hret R' M' H' F' y hk),
      fun R' M' sp' h1 h2' hr2 hout => hl R' M' sp' h1 h2' hr2 fun a ha _ hf => hout a ha hf⟩

/-- **`bc_sub (u1, u2, &h, k)`** on the handle `h`: the difference replaces
it. -/
theorem hc_subH {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R : Nat → BitVec 64} {sp W Fz o k : Nat} {P : Nat → Prop}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {u1 u2 : NumObj} {H : Heap} {F : List Blk}
    (fr : HcFrame S sp W Fz o) (hoom : HcOom live S Q Mt0 sp W P)
    (houtM : ∀ a, OutHeap a → ¬ P a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S X M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h) (ha : BinArgs (RList (hs1 ++ h :: hs2) L) u1 u2 k)
    (hadd : u1.rep.neg ≠ u2.rep.neg → 1 ≤ u1.rep.len ∧ 1 ≤ u2.rep.len)
    (hw : ldv .ld M (sp - Fz + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - Fz)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - Fz + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ R' M' H' F' y, Keeps binClob R' R →
      BcHeap S X M' H' F' (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      MulRes M' (sp - Fz + o) (Num.sub u1.rep.num u2.rep.num k) y →
      (∀ a, OutHeap a → ¬ slotBytes (sp - Fz + o) a → ¬ frameIn (sp - Fz) (W - Fz) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x80004ac4#64 R M := by
  hc_facts fr
  obtain ⟨L1, L2, x, e, hp, hr1, hnv, _, _, hfr⟩ := RList.slot hb hh hown
  rw [e] at hb ha
  have hl := hoom.lift (Fz := Fz) (by omega) houtM (E := fun _ => False) (fun _ h => h.elim)
  refine bc_sub_spec hlive (fr.cc.bin (F := Fz) (by omega) fr.f16 fr.dslot h2 hal) ha hadd hb
    ⟨hr1, by rw [hw, hp], hnv⟩ h10 h11 h12 h13
    ⟨fun R' M' H' F' L' y hk hp' => hc_binRet hown hfr hp' (by omega) (hret R' M' H' F' y hk),
      fun R' M' sp' h1 h2' hr2 hout => hl R' M' sp' (by omega) (by omega) hr2
        fun a ha _ hf => hout a ha fun h' => hf (by simp only [frameIn] at h' ⊢; omega)⟩

/-- **`bc_divide (u1, u2, &h, k)`** on the handle `h` by a nonzero `u2`: the
quotient replaces it. The dividend may be the handle's own number unless the
divisor is `1` (`hone`). -/
theorem hc_divH {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R : Nat → BitVec 64} {sp W Fz o k : Nat} {P : Nat → Prop}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {u1 u2 z : NumObj} {H : Heap} {F : List Blk}
    (fr : HcFrame S sp W Fz o) (hoom : HcOom live S Q Mt0 sp W P)
    (houtM : ∀ a, OutHeap a → ¬ P a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S X M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h)
    (hm1 : u1 ∈ RList (hs1 ++ h :: hs2) L) (hm2 : u2 ∈ RList (hs1 ++ h :: hs2) L)
    (hmz : z ∈ RList (hs1 ++ h :: hs2) L)
    (hone : ∀ y, h = .own y → IsOneRep u2.rep → u1 ≠ y ∧ u2 ≠ y ∧ z ≠ y)
    (hsz : u1.rep.len + u1.rep.scale + k + u2.rep.len + u2.rep.scale < 2 ^ 27)
    (hz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p) (hzm : z.rep.num.mag = 0)
    (hl1 : 1 ≤ u1.rep.len) (hn2 : u2.rep.num.mag ≠ 0)
    (hw : ldv .ld M (sp - Fz + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - Fz)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = BitVec.ofNat 64 (sp - Fz + o)) (h13 : R 13 = BitVec.ofNat 64 k)
    (hret : ∀ m, Num.div u1.rep.num u2.rep.num k = some m → ∀ R' M' H' F' y,
      Keeps binClob R' R → R' 10 = 0#64 →
      BcHeap S X M' H' F' (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      MulRes M' (sp - Fz + o) m y →
      (∀ a, OutHeap a → ¬ slotBytes (sp - Fz + o) a → ¬ frameIn (sp - Fz) (W - Fz) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000589c#64 R M := by
  hc_facts fr
  obtain ⟨L1, L2, x, e, hp, hr1, hnv, h2r, hxo, hfr⟩ := RList.slot hb hh hown
  rw [e] at hb hm1 hm2 hmz
  have hap : IsOneRep u2.rep → x.rep.refs = 1 → u1 ≠ x ∧ u2 ≠ x ∧ z ≠ x := fun h1 hr => by
    cases h with
    | ref y => have := h2r y rfl; omega
    | own y => rw [hxo]; exact hone y rfl h1
  have hl := hoom.lift (Fz := Fz) (by omega) houtM fr.inWin
  refine bc_divide_specF hlive (q := sp - Fz + o) (W := W - Fz) (n := Num.div u1.rep.num u2.rep.num k)
    (fr.cc.div (F := Fz) (by omega) fr.f16 fr.dslot (.inr (by simp only [zeroAddr]; omega)) h2 hal)
    ⟨fun m hm R' M' H' F' L' y hk h10' hp' => ?_, fun hn => ?_,
      fun R' M' sp' h1 h2' hr2 hout => hl R' M' sp' h1 h2' hr2 hout⟩
    ⟨rfl, hm1, hm2, hmz, fun h1 _ hf => hf.keep hm1 fun e => (hap h1 e).1,
      fun h1 _ hf => hf.keep hm2 fun e => (hap h1 e).2.1,
      fun h1 _ hf => hf.keep hmz fun e => (hap h1 e).2.2, hsz, hz, hl1⟩ hzm hb
    (.num ⟨hr1, by rw [hw, hp], hnv⟩) h10 h11 h12 h13
  · have hyp : y.rep.p = y.sb.pay := (hp'.heap.blocks y List.mem_cons_self).sPay
    exact hret m hm R' M' H' F' y hk h10' (RList.replace hown hp'.owns hp'.heap (hfr L' hp'.rest))
      (hown.set hp'.owns) ⟨⟨hp'.num, hp'.norm, hp'.pos, hp'.refs, hp'.owns⟩, by rw [hp'.slot, hyp]⟩
      hp'.out
  · unfold Num.div at hn
    rw [if_neg (by simpa using hn2)] at hn
    cases hn

/-- **`bc_divmod (u1, u2, NULL, &h, k)`** (`bc_modulo`) on the handle `h` by
a nonzero `u2`: the remainder replaces it. -/
theorem hc_modH {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R : Nat → BitVec 64} {sp W Fz o k : Nat} {P : Nat → Prop}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {u1 u2 z : NumObj} {H : Heap} {F : List Blk}
    (fr : HcFrame S sp W Fz o) (hoom : HcOom live S Q Mt0 sp W P)
    (houtM : ∀ a, OutHeap a → ¬ P a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S X M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h) (ha : DmArgs M (RList (hs1 ++ h :: hs2) L) u1 u2 z k)
    (hm2 : u2.rep.num.mag ≠ 0)
    (hw : ldv .ld M (sp - Fz + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - Fz)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 u1.rep.p) (h11 : R 11 = BitVec.ofNat 64 u2.rep.p)
    (h12 : R 12 = 0#64) (h13 : R 13 = BitVec.ofNat 64 (sp - Fz + o))
    (h14 : R 14 = BitVec.ofNat 64 k)
    (hret : ∀ r, Num.modulo u1.rep.num u2.rep.num k = some r → ∀ R' M' H' F' y,
      Keeps binClob R' R → R' 10 = 0#64 →
      BcHeap S X M' H' F' (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      MulRes M' (sp - Fz + o) r y →
      (∀ a, OutHeap a → ¬ slotBytes (sp - Fz + o) a → ¬ frameIn (sp - Fz) (W - Fz) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x80005fd0#64 R M := by
  hc_facts fr
  have hpd := hb.pdist
  obtain ⟨L1, L2, x, e, hp, hr1, _, _, _, hfr⟩ := RList.slot hb hh hown
  have hxm : x ∈ RList (hs1 ++ h :: hs2) L := by rw [e]; exact List.mem_append_right _ List.mem_cons_self
  have hl := hoom.lift (Fz := Fz) (by omega) houtM (E := fun _ => False) (fun _ h => h.elim)
  refine bc_divmod_rem_spec hlive (fr.cc.dm (F := Fz) (by omega) fr.f16 h2 hal) ha fr.dslot hxm hr1
    (by rw [hw, hp]) hb ⟨fun r hr R' M' H' F' Lf yr hk h10' hp' => ?_, fun hn => ?_,
      fun R' M' sp' h1 h2' hr2 hout => hl R' M' sp' h1 h2' hr2 fun a ha _ hf => hout a ha hf⟩
    h10 h11 h12 h13 h14
  · rw [e] at hpd
    have hf := DropAt.unique hpd (by rw [← e]; exact hp'.mid)
    have hyp : yr.rep.p = yr.sb.pay := (hp'.heap.blocks yr List.mem_cons_self).sPay
    exact hret r hr R' M' H' F' yr hk h10' (RList.replace hown hp'.rem.owns hp'.heap (hfr Lf hf))
      (hown.set hp'.rem.owns) ⟨hp'.rem.toNewNum, by rw [hp'.rem.slot, hyp]⟩ hp'.out
  · obtain ⟨r, hr, _⟩ := Dc.BcModel.modulo_res (a := u1.rep.num) (k := k) hm2
    rw [hr] at hn; cases hn

/-- **`bc_int2num (&h, v)`** on the handle `h`: the new number replaces it. -/
theorem hc_i2nH {live : Nat → Prop} {S : Nat → Prop} {X : Raws}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt0 M : Mem} {R : Nat → BitVec 64} {sp W Fz o : Nat} {v : Int} {P : Nat → Prop}
    {hs1 hs2 : List RH} {h : RH} {L : List NumObj} {H : Heap} {F : List Blk}
    (fr : HcFrame S sp W Fz o) (hoom : HcOom live S Q Mt0 sp W P)
    (houtM : ∀ a, OutHeap a → ¬ P a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a)
    (hb : BcHeap S X M H F (RList (hs1 ++ h :: hs2) L)) (hown : RHOwn (hs1 ++ h :: hs2) L)
    (hh : RHOK L h) (hw : ldv .ld M (sp - Fz + o) = BitVec.ofNat 64 h.p)
    (h2 : R 2 = BitVec.ofNat 64 (sp - Fz)) (hal : (R 1).toNat % 4 = 0)
    (h10 : R 10 = BitVec.ofNat 64 (sp - Fz + o)) (h11 : R 11 = BitVec.ofInt 64 v)
    (hvl : -2 ^ 31 < v) (hvh : v < 2 ^ 31)
    (hret : ∀ R' M' H' F' y, Keeps i2nClob R' R →
      BcHeap S X M' H' F' (RList (hs1 ++ .own y :: hs2) L) → RHOwn (hs1 ++ .own y :: hs2) L →
      MulRes M' (sp - Fz + o) (Num.ofInt v) y →
      (∀ a, OutHeap a → ¬ slotBytes (sp - Fz + o) a → ¬ frameIn (sp - Fz) (W - Fz) a →
        imgM M' a = imgM M a) → DW live S Q (R 1) R' M') :
    DW live S Q 0x8000690c#64 R M := by
  hc_facts fr
  have hsl := fr.dslot
  obtain ⟨L1, L2, x, e, hp, hr1, hnv, _, _, hfr⟩ := RList.slot hb hh hown
  rw [e] at hb
  have ic := fr.cc.i2n (F := Fz) (v := v) (by omega) fr.f16 hsl h2 hal hvl hvh
  have hl := hoom.lift (Fz := Fz) (by omega) houtM fr.inWin
  refine bc_int2num_spec hlive ic (FreeEntry.of_slot hb ⟨hr1, by rw [hw, hp], hnv⟩ hnv hsl.slot hsl.out
    (StackFrame.sub (m := 96) (n := 32) ic.frame (by decide)) (by have := ic.above; omega)
    (.inr (by omega))) h10 h11
    ⟨fun R' M' H' F' L' y hk hp' => ?_, fun R' M' hr2 hout => ?_⟩
  · have hyp : y.rep.p = y.sb.pay := (hp'.heap.blocks y List.mem_cons_self).sPay
    exact hret R' M' H' F' y hk (RList.replace hown hp'.owns hp'.heap (hfr L' hp'.rest))
      (hown.set hp'.owns) ⟨⟨hp'.num, hp'.norm, hp'.pos, hp'.refs, hp'.owns⟩, by rw [hp'.slot, hyp]⟩
      fun a h1 h2 h3 => hp'.out a h1 h2 fun h' => h3 (by simp only [frameIn] at h' ⊢; omega)
  · exact hl R' M' (sp - Fz - 128) (by omega) (by omega) hr2 fun a ha hs hf =>
      hout a ha hs fun h' => hf (by simp only [frameIn] at h' ⊢; omega)

end Dc.Mach
