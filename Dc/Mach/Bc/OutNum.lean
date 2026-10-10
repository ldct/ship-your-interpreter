import Dc.Mach.Bc.OutNumFrac

/-! # `bc_out_num`

`bc_out_num (num, o_base, out_char, 0)` at `0x80006f3c` sends the
characters of `Num.outChars num o_base` through the callback and returns
with the caller's heap (`OnK.ret`), or reaches `out_of_memory` (`OnK.oom`).

- `on_baseGo`: the branch for a base other than 10, from its setup
  (`og_s1`–`og_s5`, `OutNumSetup.lean`, `OutNumInt.lean`) through the
  integer digits (`og_s6`, `OutNumPop.lean`) and the fraction
  (`og_s7`, `OutNumFrac.lean`).
- `bc_out_num_spec`: the whole function (`on_entry`, `OutNumEntry.lean`).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- **The branch for a base other than 10.** -/
theorem on_baseGo {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj} {cs : List Nat}
    (cb : CharFn live S Q (R0 12) d G I) (cx : OnCtx S R0 sp W d) (ha : OnArgs S Mt0 L x z o ob)
    (hK : OnK live S X Q I G R0 Mt0 L sp W (cs ++ Num.outChars x.rep.num ob)) :
    OnBaseGo live S X Q I G Mt0 R0 sp W L x z ob cs := by
  intro R M t H F st hb hI h18 h10 h20 _ h23 hhi hmag hne
  have fx : OgFix live S X Q I G Mt0 R0 sp W d L x z o ob cs := ⟨cb, cx, ha, hK, hmag, hne⟩
  exact og_s1 hlive fx st hb hI h18 h10 h20 h23 hhi
    (og_s2 hlive fx (og_s3 hlive fx (og_s4 hlive fx (og_s5 hlive fx
      fun _ _ _ hfr hbs hmx => og_s6 hlive fx hmx (og_s7 hlive fx hfr hbs hmx)))))

/-- **`bc_out_num (num, o_base, out_char, 0)`** at `0x80006f3c`: the
characters `Num.outChars num o_base` sent after `cs` (`OnK`). -/
theorem bc_out_num_spec {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x z o : NumObj}
    {cs : List Nat} {t : String}
    (cb : CharFn live S Q (R0 12) d G I) (cx : OnCtx S R0 sp W d) (ha : OnArgs S Mt0 L x z o ob)
    (hK : OnK live S X Q I G R0 Mt0 L sp W (cs ++ Num.outChars x.rep.num ob))
    (hb : BcHeap S X Mt0 H F L) (hI : I cs t Mt0) (h10 : R0 10 = BitVec.ofNat 64 x.rep.p)
    (h11 : R0 11 = BitVec.ofNat 64 ob) :
    DWO live S Q t 0x80006f3c#64 R0 Mt0 :=
  on_entry hlive ⟨cb, cx, ha, hK, on_baseGo hlive cb cx ha hK⟩ hb hI h10 h11

end Dc.Mach
