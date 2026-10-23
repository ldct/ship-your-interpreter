import Dc.Mach.Bc.OutNumGo

/-! # `bc_out_num` in a base other than 10: the setup

From `0x800070b8` to the integer loop: `int_part = num / 1` at scale 0,
`frac_part = num - int_part`, both made positive, `base` and `max_o_digit`
from `bc_int2num`, `cur_dig` one more reference to `_zero_`.

- `og_s1`: the saves of `s8`–`s11`, `int_part` a reference to `_zero_`,
  `bc_divide (num, _one_, &int_part, 0)`; continues at `OgK1`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The fixed facts of the branch for a base other than 10. -/
structure OgFix (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W d : Nat) (L : List NumObj) (x z o : NumObj) (ob : Nat) (cs : List Nat) : Prop where
  cb : CharFn live S Q (R0 12) d G I
  cx : OnCtx S R0 sp W d
  ha : OnArgs S Mt0 L x z o ob
  hK : OnK live S X Q I G R0 Mt0 L sp W (cs ++ Num.outChars x.rep.num ob)
  mag : x.rep.num.mag ≠ 0
  ne : ob ≠ 10

/-- `int_part`: `num / 1` at scale 0. -/
abbrev ogIp (n : Num) : Num := (Num.div n Num.one 0).getD n

/-- The registers the setup keeps: `s2` the number, `s4` `&_zero_`, `s7`
the base, `s11` `&_one_`. -/
structure OgRegs (R : Nat → BitVec 64) (x : NumObj) (ob : Nat) : Prop where
  r18 : R 18 = BitVec.ofNat 64 x.rep.p
  r20 : R 20 = BitVec.ofNat 64 zeroAddr
  r23 : R 23 = BitVec.ofNat 64 ob
  r27 : R 27 = BitVec.ofNat 64 oneAddr

theorem OgRegs.keep {R R' : Nat → BitVec 64} {x : NumObj} {ob : Nat} (h : OgRegs R x ob)
    {ks : List Nat} (hk : Keeps ks R' R)
    (hks : 18 ∉ ks ∧ 20 ∉ ks ∧ 23 ∉ ks ∧ 27 ∉ ks := by decide) : OgRegs R' x ob :=
  ⟨by rw [hk.get 18 hks.1]; exact h.r18, by rw [hk.get 20 hks.2.1]; exact h.r20,
    by rw [hk.get 23 hks.2.2.1]; exact h.r23, by rw [hk.get 27 hks.2.2.2]; exact h.r27⟩

/-- After `bc_divide (num, _one_, &int_part, 0)` returns (`0x800070f4`). -/
def OgK1 (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x : NumObj) (ob : Nat) (cs : List Nat) (t : String) : Prop :=
  ∀ (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (ip : NumObj),
    OgSt S X G I Mt0 M R0 R sp W H F L [.own ip] [16] (cs ++ signOut x.rep.num) t →
    NewNum (ogIp x.rep.num) ip → OgRegs R x ob → DWO live S Q t 0x800070f4#64 R M

/-- **The branch's entry** at `0x800070b8`: `s8`–`s11` saved, one more
reference to `_zero_` in `int_part`, then `bc_divide (num, _one_,
&int_part, 0)`. -/
theorem og_s1 {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d ob : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {x z o : NumObj}
    {cs : List Nat} {t : String} (fx : OgFix live S X Q I G Mt0 R0 sp W d L x z o ob cs)
    (st : OnAt S G Mt0 M R0 R sp W onSlots2) (hb : BcHeap S X M H F L)
    (hI : I (cs ++ signOut x.rep.num) t M) (h18 : R 18 = BitVec.ofNat 64 x.rep.p)
    (h10 : R 10 = BitVec.ofNat 64 z.rep.p) (h20 : R 20 = BitVec.ofNat 64 zeroAddr)
    (h23 : R 23 = BitVec.ofNat 64 ob) (hhi : ∀ r ∈ [24, 25, 26, 27], R r = R0 r)
    (hk : OgK1 live S X Q I G Mt0 R0 sp W L x ob cs t) :
    DWO live S Q t 0x800070b8#64 R M := by
  have cx := fx.cx
  have ha := fx.ha
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  rw [← RList.nil L] at hb
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hzn := hb.nums _ (RList.mem_caller [] ha.mz)
  have hzs := hzn.shape
  have hz1 : heapStart ≤ z.rep.p := hzs.pLo
  have hz2 : z.rep.p + 40 ≤ heapEnd := hzs.pHi
  have hz3 : z.rep.p % 8 = 0 := hzs.pAl
  simp only [heapStart, heapEnd] at hz1 hz2
  have hrz := ha.refs z ha.mz
  have hr : ldv .lw M (z.rep.p + 12) = BitVec.ofNat 64 z.rep.refs := by
    have := RList.refsAt hb ha.mz
    simpa [rCnt] using this
  have hx := sxw_ofNat (k := z.rep.refs + 1) (by omega)
  have hG : ∀ a, G a → ¬ constBytes a := fun a hg => (cb.off a hg).2.2.1
  have hone : ldv .ld M oneAddr = BitVec.ofNat 64 o.rep.p := by
    rw [st.glob hG (by omega) (by simp only [twoAddr, oneAddr]; omega)
      (by simp only [oneAddr, zeroAddr]; omega)]
    exact ha.one
  have hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p := by
    rw [st.glob hG (by omega) (by simp only [twoAddr, zeroAddr]; omega) (by omega)]
    exact ha.zero.glob
  have hto : (BitVec.ofNat 64 oneAddr).toNat = oneAddr := rfl
  have hldo : LdOK oneAddr 8 := by simp only [LdOK, oneAddr, tohostAddr]; omega
  have hcst : ∀ b ∈ accAddrs oneAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.cc.consts b (by simp only [constBytes, twoAddr, zeroAddr, oneAddr] at *; omega)
  have h2 := st.r2
  have h24 := hhi 24 (by simp); have h25 := hhi 25 (by simp); have h26 := hhi 26 (by simp)
  have h27 := hhi 27 (by simp)
  bc_run hlive hS [h10, hr, hx, h2, hto, ldv_ld_miss, hone, h18] at 0x8000589c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | exact hldo | exact hcst | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  have st1 := ((((st.store 27 72 h27 (by decide) (by omega) (by omega) (by omega)).store 24 96 h24
    (by decide) (by omega) (by omega) (by omega)).store 26 80 h26 (by decide) (by omega) (by omega)
    (by omega)).store 25 88 h25 (by decide) (by omega) (by omega) (by omega)).heapStore
    (by decide) (by decide) (by simp only [heapEnd]; omega) (by omega)
    (a0 := z.rep.p + 12) (w := 4) (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
    (BitVec.ofNat 64 (z.rep.refs + 1))
  have st2 := st1.word (o := 16) (by decide) (by decide) (by omega) (by omega) (by omega)
    (BitVec.ofNat 64 z.rep.p)
  have hb1 := RList.bump (hs := []) ((((hb.frameStore (sp := sp) (o := 72) (R 27)
    (by simp only [heapEnd]; omega) (by omega)).frameStore (sp := sp) (o := 96) (R 24)
    (by simp only [heapEnd]; omega) (by omega)).frameStore (sp := sp) (o := 80) (R 26)
    (by simp only [heapEnd]; omega) (by omega)).frameStore (sp := sp) (o := 88) (R 25)
    (by simp only [heapEnd]; omega) (by omega)) ha.mz
    (v := BitVec.ofNat 64 (z.rep.refs + 1)) (by simpa [rCnt] using toNat_ofNat_mod32 (k := z.rep.refs + 1) (by omega))
    (by simp [rCnt]; omega)
  have hb2 := hb1.frameStore (sp := sp) (o := 16) (BitVec.ofNat 64 z.rep.p)
    (by simp only [heapEnd]; omega) (by omega)
  have hI1 := cb.frameStore (cb.frameStore (cb.frameStore (cb.frameStore hI (R 27)
    (b := sp - 176 + 72) (by simp only [heapEnd]; omega)) (R 24) (b := sp - 176 + 96)
    (by simp only [heapEnd]; omega)) (R 26) (b := sp - 176 + 80) (by simp only [heapEnd]; omega))
    (R 25) (b := sp - 176 + 88) (by simp only [heapEnd]; omega)
  have hI2 := cb.frameStore (cb.heapStore hI1 (a0 := z.rep.p + 12) (w := 4)
    (BitVec.ofNat 64 (z.rep.refs + 1)) (by simp only [heapStart]; omega)) (BitVec.ofNat 64 z.rep.p)
    (b := sp - 176 + 16) (by simp only [heapEnd]; omega)
  have og : OgSt S X G I Mt0 _ R0 _ sp W H F L [.ref z] [16] (cs ++ signOut x.rep.num) t :=
    { on := st2
      heap := hb2
      own := ⟨fun y hy => by simp at hy, ha.owns⟩
      words := ⟨ldv_store_hit _ _ _, trivial⟩
      offs := by decide
      nd := by decide
      inv := hI2 }
  have hos' : o.rep.len + o.rep.scale ≤ 1 :=
    one_size (o := (rBump [.ref z] o).rep) (hb2.nums _ (RList.mem_caller _ ha.mo)).shape
      ha.oneNorm ha.oneNum
  have hsz := ha.size
  have hzk := ha.zero
  refine hc_divH (hs1 := []) (hs2 := []) (h := .ref z) (o := 16) (k := 0)
    (u1 := rBump [.ref z] x) (u2 := rBump [.ref z] o) (z := rBump [.ref z] z) hlive
    (cx.hcFrame (by omega) rfl) (fx.hK.hcOom t) og.on.out og.heap og.own
    (RHOK.ofMem ha.mz (ha.live z ha.mz)) (RList.mem_caller _ ha.mx) (RList.mem_caller _ ha.mo)
    (RList.mem_caller _ ha.mz) (fun y e => by cases e)
    (by show x.rep.len + x.rep.scale + 0 + o.rep.len + o.rep.scale < _; omega)
    (by rw [og.on.glob hG (by omega) (by simp only [twoAddr, zeroAddr]; omega) (by omega)]; exact hzk.glob)
    (by show z.rep.num.mag = 0; rw [NumRep.num_mag, hzk.ds]; rfl)
    ha.lenx (by show o.rep.num.mag ≠ 0; rw [ha.oneNum]; decide) (og.words.get (hs1 := []) (os1 := []) (hs2 := []) (os2 := []) rfl)
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp []; rfl) (by bsimp [hone]; rfl) (by bsimp [h2])
    (by bsimp []) ?_
  intro m hm R2 M2 H2 F2 y hk2 _ hb3 hown3 hres hout2
  bsimp []
  have hm' : y.rep.num = ogIp x.rep.num := by
    rw [hres.num]
    change Num.div x.rep.num o.rep.num 0 = some m at hm
    rw [ha.oneNum] at hm
    simp [ogIp, hm]
  have hk3 : Keeps ogKs R2 R := (hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  exact hk R2 M2 H2 F2 y (og.ret (hs1 := []) (hs2 := []) (os1 := []) (os2 := []) cx cb rfl hk3
    (by decide) hb3 hown3 hres.slot hout2) { hres.toNewNum with num := hm' }
    ⟨by rw [hk2.get 18 (by decide)]; bsimp [h18], by rw [hk2.get 20 (by decide)]; bsimp [h20],
      by rw [hk2.get 23 (by decide)]; bsimp [h23], by rw [hk2.get 27 (by decide)]; bsimp []; try rfl⟩

/-- After `bc_sub (num, int_part, &frac_part, 0)` returns (`0x80007128`):
`s0` `int_part`, `s10` `_zero_`; `base` and `cur_dig` (at 32 and 40)
references to `_zero_`. -/
def OgK2 (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x z : NumObj) (ob : Nat) (cs : List Nat) (t : String) : Prop :=
  ∀ (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (ip fr : NumObj),
    OgSt S X G I Mt0 M R0 R sp W H F L [.own ip, .own fr, .ref z, .ref z] [16, 24, 40, 32]
      (cs ++ signOut x.rep.num) t →
    NewNum (ogIp x.rep.num) ip → NewNum (Num.sub x.rep.num (ogIp x.rep.num) 0) fr →
    OgRegs R x ob → R 8 = BitVec.ofNat 64 ip.rep.p → R 26 = BitVec.ofNat 64 z.rep.p →
    DWO live S Q t 0x80007128#64 R M

/-- `int_part` has at most one more digit than `num` has digits. -/
theorem ogIp_size {x ip : NumObj} (hx : NumShape x.rep) (hs : NumShape ip.rep)
    (hn : NewNum (ogIp x.rep.num) ip) : ip.rep.len + ip.rep.scale ≤ x.rep.len + x.rep.scale + 1 := by
  obtain ⟨m, hm, hmag, hsc⟩ := Dc.BcModel.div_one_zero x.rep.num
  have e : ogIp x.rep.num = m := by simp [ogIp, hm]
  have hnum := hn.num
  rw [e] at hnum
  have hlt : ip.rep.num.mag < 10 ^ (x.rep.len + x.rep.scale) := by
    rw [hnum, hmag]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by rw [NumRep.num_mag]; exact NumRep.mag_lt hx)
  have hs0 : ip.rep.scale = 0 := by rw [← NumRep.num_scale, hnum, hsc]
  have := NumRep.size_le hs hn.norm hlt
  omega

/-- **`frac_part = num - int_part`** from `0x800070f4`: three more
references to `_zero_` (`frac_part`, `cur_dig`, `base`), then `bc_sub`. -/
theorem og_s2 {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj}
    {cs : List Nat} {t : String} (fx : OgFix live S X Q I G Mt0 R0 sp W d L x z o ob cs)
    (hk : OgK2 live S X Q I G Mt0 R0 sp W L x z ob cs t) :
    OgK1 live S X Q I G Mt0 R0 sp W L x ob cs t := by
  intro R M H F ip st hip rg
  have cx := fx.cx
  have ha := fx.ha
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have hzn := st.heap.nums _ (RList.mem_caller [.own ip] ha.mz)
  have hzs := hzn.shape
  have hz1 : heapStart ≤ z.rep.p := hzs.pLo
  have hz2 : z.rep.p + 40 ≤ heapEnd := hzs.pHi
  have hz3 : z.rep.p % 8 = 0 := hzs.pAl
  simp only [heapStart, heapEnd] at hz1 hz2
  have hrz := ha.refs z ha.mz
  have hc0 : rCnt [.own ip] z.rep.p = 0 := rfl
  have hr : ldv .lw M (z.rep.p + 12) = BitVec.ofNat 64 z.rep.refs := by
    have := RList.refsAt st.heap ha.mz
    rwa [hc0, Nat.add_zero] at this
  have hx := sxw_ofNat (k := z.rep.refs + 3) (by omega)
  have hG : ∀ a, G a → ¬ constBytes a := fun a hg => (cb.off a hg).2.2.1
  have hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p := by
    rw [st.on.glob hG (by omega) (by simp only [twoAddr, zeroAddr]; omega) (by omega)]
    exact ha.zero.glob
  have hw16 : ldv .ld M (sp - 176 + 16) = BitVec.ofNat 64 ip.rep.p :=
    st.words.get (hs1 := []) (os1 := []) (hs2 := []) (os2 := []) rfl
  have hz0 : (BitVec.ofNat 64 zeroAddr).toNat = zeroAddr := rfl
  have hldz : LdOK zeroAddr 8 := by simp only [LdOK, zeroAddr, tohostAddr]; omega
  have hcz : ∀ b ∈ accAddrs zeroAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.cc.consts b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  have h2 := st.on.r2
  bc_run hlive hS [rg.r20, hz0, hzg, h2, hw16, hr, hx, rg.r18] at 0x80004ac4
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | exact hldz | exact hcz | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  have p1 := (((st.pre.bump3 cx cb ha.mz (v := BitVec.ofNat 64 (z.rep.refs + 3))
    (by rw [hc0]; exact toNat_ofNat_mod32 (by omega)) (by rw [hc0]; omega)).frame cx cb (o := 24)
    (by omega) (BitVec.ofNat 64 z.rep.p)).frame cx cb (o := 40) (by omega)
    (BitVec.ofNat 64 z.rep.p)).frame cx cb (o := 32) (by omega) (BitVec.ofNat 64 z.rep.p)
  have og := p1.close (os := [16, 24, 40, 32])
    ⟨by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
        ldv_ld_miss _ _ (by omega)]; exact hw16,
      by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _,
      by rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _, ldv_store_hit _ _ _, trivial⟩
  have hxs := (st.heap.nums _ (RList.mem_caller [.own ip] ha.mx)).shape
  have hips : NumShape ip.rep := (st.heap.nums _ (RH.obj_mem (hs := [.own ip]) (h := .own ip)
    (by simp) ⟨hip.refs, hip.owns⟩)).shape
  have hisz := ogIp_size (x := x) hxs hips hip
  have hsz := ha.size
  have hlx := ha.lenx
  have hlp := hip.pos
  refine hc_subH (hs1 := [.own ip]) (hs2 := [.ref z, .ref z]) (h := .ref z) (o := 24) (k := 0)
    (u1 := rBump [.own ip, .ref z, .ref z, .ref z] x) (u2 := ip) hlive
    (cx.hcFrame (by omega) rfl) (fx.hK.hcOom t) og.on.out og.heap og.own
    (RHOK.ofMem ha.mz (ha.live z ha.mz))
    ⟨RList.mem_caller _ ha.mx, RH.obj_mem (h := .own ip) (by simp) ⟨hip.refs, hip.owns⟩, ha.nx,
      hip.norm, by show max x.rep.len ip.rep.len + 1 + max 0 (max x.rep.scale ip.rep.scale) < _; omega,
      fun h => by simp only [rBump, NumObj.withRefs] at h; omega, fun h => by omega⟩
    (fun _ => ⟨ha.lenx, hip.pos⟩)
    (og.words.get (hs1 := [.own ip]) (os1 := [16]) (hs2 := [.ref z, .ref z]) (os2 := [40, 32]) rfl)
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp []; rfl) (by bsimp []) (by bsimp [h2])
    (by bsimp []) ?_
  intro R2 M2 H2 F2 y hk2 hb3 hown3 hres hout2
  bsimp []
  have hk4 : Keeps [1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 26, 28, 29, 30, 31] R2 R :=
    (hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  have hk3 : Keeps ogKs R2 R := hk4.mono (by decide)
  refine hk R2 M2 H2 F2 ip y (og.ret (hs1 := [.own ip]) (hs2 := [.ref z, .ref z]) (os1 := [16])
    (os2 := [40, 32]) cx cb rfl hk3 (by decide) hb3 hown3 hres.slot hout2) hip
    { hres.toNewNum with num := by rw [hres.num]; show Num.sub x.rep.num ip.rep.num 0 = _; rw [hip.num] }
    (rg.keep hk4) (by rw [hk2.get 8 (by decide)]; bsimp []) (by rw [hk2.get 26 (by decide)]; bsimp [])

/-- `int_part` made positive: `num`'s integer part at scale 0. -/
abbrev ogInt (n : Num) : Num := ⟨false, n.intPart, 0⟩

/-- `frac_part` made positive. -/
abbrev ogFrac (n : Num) : Num := { Num.sub n (ogIp n) 0 with neg := false }

theorem ogIp_pos (n : Num) : ({ ogIp n with neg := false } : Num) = ogInt n := by
  obtain ⟨m, hm, hmag, hsc⟩ := Dc.BcModel.div_one_zero n
  have e : ogIp n = m := by simp [ogIp, hm]
  rw [e]
  obtain ⟨_, _, _⟩ := m
  simp only at hmag hsc
  rw [hmag, hsc]

/-- A number with its sign rewritten. -/
theorem NewNum.setNeg {n : Num} {y : NumObj} (h : NewNum n y) (b : Bool) :
    NewNum { n with neg := b } { y with rep := { y.rep with neg := b } } where
  num := by rw [← h.num]; rfl
  norm := h.norm
  pos := h.pos
  refs := h.refs
  owns := h.owns

/-- After `bc_int2num (&base, o_base)` returns (`0x80007140`): `s0`
`int_part` and `s6` `frac_part`, both positive. -/
def OgK3 (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x z : NumObj) (ob : Nat) (cs : List Nat) (t : String) : Prop :=
  ∀ (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (ip fr bs : NumObj),
    OgSt S X G I Mt0 M R0 R sp W H F L [.own ip, .own fr, .ref z, .own bs] [16, 24, 40, 32]
      (cs ++ signOut x.rep.num) t →
    NewNum (ogInt x.rep.num) ip → NewNum (ogFrac x.rep.num) fr → NewNum (Num.ofInt ob) bs →
    OgRegs R x ob → R 8 = BitVec.ofNat 64 ip.rep.p → R 22 = BitVec.ofNat 64 fr.rep.p →
    DWO live S Q t 0x80007140#64 R M

/-- **Both parts made positive** from `0x80007128`, then
`bc_int2num (&base, o_base)`. -/
theorem og_s3 {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj}
    {cs : List Nat} {t : String} (fx : OgFix live S X Q I G Mt0 R0 sp W d L x z o ob cs)
    (hk : OgK3 live S X Q I G Mt0 R0 sp W L x z ob cs t) :
    OgK2 live S X Q I G Mt0 R0 sp W L x z ob cs t := by
  intro R M H F ip fr st hip hfr rg h8 h26
  have cx := fx.cx
  have ha := fx.ha
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have hw24 : ldv .ld M (sp - 176 + 24) = BitVec.ofNat 64 fr.rep.p :=
    st.words.get (hs1 := [.own ip]) (os1 := [16]) (hs2 := [.ref z, .ref z]) (os2 := [40, 32]) rfl
  have hipm : ip ∈ RList [.own ip, .own fr, .ref z, .ref z] L := by simp [RList, rTemps, RH.tmp]
  have hfrm : fr ∈ RList [.own ip, .own fr, .ref z, .ref z] L := by simp [RList, rTemps, RH.tmp]
  have hips := (st.heap.nums ip hipm).shape
  have hfrs := (st.heap.nums fr hfrm).shape
  have hi1 : heapStart ≤ ip.rep.p := hips.pLo
  have hi2 : ip.rep.p + 40 ≤ heapEnd := hips.pHi
  have hf1 : heapStart ≤ fr.rep.p := hfrs.pLo
  have hf2 : fr.rep.p + 40 ≤ heapEnd := hfrs.pHi
  have hi3 : ip.rep.p % 8 = 0 := hips.pAl
  have hf3 : fr.rep.p % 8 = 0 := hfrs.pAl
  simp only [heapStart, heapEnd] at hi1 hi2 hf1 hf2
  have h2 := st.on.r2
  have hob := ha.obHi
  bc_run hlive hS [h8, rg.r23, h2, hw24] at 0x8000690c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  have og := (st.setSign (hs1 := []) (hs2 := [.own fr, .ref z, .ref z]) cx cb (v := 0#64) false
    (by decide)).setSign (hs1 := [.own { ip with rep := { ip.rep with neg := false } }])
    (hs2 := [.ref z, .ref z]) cx cb (v := 0#64) false (by decide)
  refine hc_i2nH (hs1 := [.own { ip with rep := { ip.rep with neg := false } },
      .own { fr with rep := { fr.rep with neg := false } }, .ref z]) (hs2 := [])
    (h := .ref z) (o := 32) (v := (ob : Int)) hlive
    (cx.hcFrame (by omega) rfl) (fx.hK.hcOom t) og.on.out og.heap og.own
    (RHOK.ofMem ha.mz (ha.live z ha.mz))
    (og.words.get (hs1 := [_, _, _]) (os1 := [16, 24, 40]) (hs2 := []) (os2 := []) rfl)
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp []) (by bsimp []; exact (ofInt_natCast64 ob).symm)
    (by omega) (by omega) ?_
  intro R2 M2 H2 F2 y hk2 hb3 hown3 hres hout2
  bsimp []
  have hk4 : Keeps [1, 5, 10, 11, 12, 13, 14, 15, 22] R2 R :=
    (hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  have hk3 : Keeps ogKs R2 R := hk4.mono (by decide)
  refine hk R2 M2 H2 F2 _ _ y (og.ret (hs1 := [_, _, _]) (hs2 := []) (os1 := [16, 24, 40])
    (os2 := []) cx cb rfl hk3 (by decide) hb3 hown3 hres.slot hout2)
    (by have := hip.setNeg false; rwa [ogIp_pos] at this) (hfr.setNeg false) hres.toNewNum
    (rg.keep hk4) (by rw [hk4.get 8 (by decide)]; exact h8) (by rw [hk2.get 22 (by decide)]; bsimp [])

/-- After `bc_int2num (&max_o_digit, o_base - 1)` returns (`0x80007164`):
the five handles, `s5 = 0`. -/
def OgK4 (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (sp W : Nat) (L : List NumObj) (x z : NumObj) (ob : Nat) (cs : List Nat) (t : String) : Prop :=
  ∀ (R : Nat → BitVec 64) (M : Mem) (H : Heap) (F : List Blk) (ip fr bs mx : NumObj),
    OgSt S X G I Mt0 M R0 R sp W H F L [.own ip, .own fr, .ref z, .own bs, .own mx]
      [16, 24, 40, 32, 56] (cs ++ signOut x.rep.num) t →
    NewNum (ogInt x.rep.num) ip → NewNum (ogFrac x.rep.num) fr → NewNum (Num.ofInt ob) bs →
    NewNum (Num.ofInt (ob - 1 : Nat)) mx →
    OgRegs R x ob → R 8 = BitVec.ofNat 64 ip.rep.p → R 22 = BitVec.ofNat 64 fr.rep.p →
    R 21 = 0#64 → DWO live S Q t 0x80007164#64 R M

/-- **`max_o_digit = o_base - 1`** from `0x80007140`: one more reference to
`_zero_` in its word, then `bc_int2num`. -/
theorem og_s4 {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {I : List Nat → String → Mem → Prop} {G : Nat → Prop} {Mt0 : Mem} {R0 : Nat → BitVec 64}
    {sp W d ob : Nat} {L : List NumObj} {x z o : NumObj}
    {cs : List Nat} {t : String} (fx : OgFix live S X Q I G Mt0 R0 sp W d L x z o ob cs)
    (hk : OgK4 live S X Q I G Mt0 R0 sp W L x z ob cs t) :
    OgK3 live S X Q I G Mt0 R0 sp W L x z ob cs t := by
  intro R M H F ip fr bs st hip hfr hbs rg h8 h22
  have cx := fx.cx
  have ha := fx.ha
  have cb := fx.cb
  on_facts cx
  have hsf := cx.cc.frame
  have hS : HeapOwn S := fun a h1 h2 => st.heap.heap.own a h1 h2
  have hzn := st.heap.nums _ (RList.mem_caller [.own ip, .own fr, .ref z, .own bs] ha.mz)
  have hzs := hzn.shape
  have hz1 : heapStart ≤ z.rep.p := hzs.pLo
  have hz2 : z.rep.p + 40 ≤ heapEnd := hzs.pHi
  have hz3 : z.rep.p % 8 = 0 := hzs.pAl
  simp only [heapStart, heapEnd] at hz1 hz2
  have hrz := ha.refs z ha.mz
  have hc1 : rCnt [.own ip, .own fr, .ref z, .own bs] z.rep.p = 1 := by simp [rCnt, RH.cnt]
  have hr : ldv .lw M (z.rep.p + 12) = BitVec.ofNat 64 (z.rep.refs + 1) := by
    have := RList.refsAt st.heap ha.mz
    rwa [hc1] at this
  have hx := sxw_ofNat (k := z.rep.refs + 1 + 1) (by omega)
  have hG : ∀ a, G a → ¬ constBytes a := fun a hg => (cb.off a hg).2.2.1
  have hzg : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p := by
    rw [st.on.glob hG (by omega) (by simp only [twoAddr, zeroAddr]; omega) (by omega)]
    exact ha.zero.glob
  have hz0 : (BitVec.ofNat 64 zeroAddr).toNat = zeroAddr := rfl
  have hldz : LdOK zeroAddr 8 := by simp only [LdOK, zeroAddr, tohostAddr]; omega
  have hcz : ∀ b ∈ accAddrs zeroAddr 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact cx.cc.consts b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  have h2 := st.on.r2
  have hob := ha.obHi
  have hob2 := ha.obLo
  bc_run hlive hS [rg.r20, hz0, hzg, h2, hr, hx, rg.r23] at 0x8000690c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact acc_heap hS (by omega) (by omega) | exact hldz | exact hcz | (simp only [StOK, LdOK, tohostAddr]; omega) | skip
  have p1 := (st.pre.frame cx cb (o := 56) (by omega) (BitVec.ofNat 64 z.rep.p)).bump cx cb ha.mz
    (ha.owns z ha.mz) (v := BitVec.ofNat 64 (z.rep.refs + 1 + 1))
    (by rw [hc1]; exact toNat_ofNat_mod32 (by omega)) (by rw [hc1]; omega)
  have og := p1.close (os := [16, 24, 40, 32, 56])
    ⟨by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
        exact st.words.get (hs1 := []) (os1 := []) (hs2 := [_, _, _]) (os2 := [24, 40, 32]) rfl,
      by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
         exact st.words.get (hs1 := [_]) (os1 := [16]) (hs2 := [_, _]) (os2 := [40, 32]) rfl,
      by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
         exact st.words.get (hs1 := [_, _]) (os1 := [16, 24]) (hs2 := [_]) (os2 := [32]) rfl,
      by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
         exact st.words.get (hs1 := [_, _, _]) (os1 := [16, 24, 40]) (hs2 := []) (os2 := []) rfl,
      by rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _, trivial⟩
  refine hc_i2nH (hs1 := [.own ip, .own fr, .ref z, .own bs]) (hs2 := [])
    (h := .ref z) (o := 56) (v := ((ob - 1 : Nat) : Int)) hlive
    (cx.hcFrame (by omega) rfl) (fx.hK.hcOom t) og.on.out og.heap og.own
    (RHOK.ofMem ha.mz (ha.live z ha.mz))
    (og.words.get (hs1 := [_, _, _, _]) (os1 := [16, 24, 40, 32]) (hs2 := []) (os2 := []) rfl)
    (by bsimp [h2]) (by bsimp []; try decide) (by bsimp [])
    (by bsimp []; exact (ofInt_natCast64 (ob - 1)).symm)
    (by omega) (by omega) ?_
  intro R2 M2 H2 F2 y hk2 hb3 hown3 hres hout2
  bsimp []
  have hk4 : Keeps [1, 5, 10, 11, 12, 13, 14, 15, 21] R2 R :=
    (hk2.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  have hk3 : Keeps ogKs R2 R := hk4.mono (by decide)
  refine hk R2 M2 H2 F2 ip fr bs y (og.ret (hs1 := [_, _, _, _]) (hs2 := [])
    (os1 := [16, 24, 40, 32]) (os2 := []) cx cb rfl hk3 (by decide) hb3 hown3 hres.slot hout2)
    hip hfr hbs hres.toNewNum (rg.keep hk4) (by rw [hk4.get 8 (by decide)]; exact h8)
    (by rw [hk4.get 22 (by decide)]; exact h22) (by rw [hk2.get 21 (by decide)]; bsimp [])

end Dc.Mach
