import Dc.Mach.Bc.KaraViews

/-!
# `_bc_rec_mul`'s Karatsuba step: the inlined `new_sub_num` sites

Each site writes the five fields of a struct the step took off
`_bc_Free_list` (or `malloc(40)`), turning it into a view of `u`'s or `v`'s
digits; `ViewStruct.toSrc` and `BcHeap.pushView` (`KaraViews.lean`) do the
heap work. The six copies are the four halves under the step's two length
dispatches (`la < n` and `lb < n` give a reference to `_zero_` instead of a
view).
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false

/-- A difference of naturals as a word. -/
theorem ofInt_sub_nat {a b : Nat} (h : b ≤ a) :
    BitVec.ofInt 64 ((a : Int) - b) = BitVec.ofNat 64 (a - b) := by
  rw [show ((a : Int) - b) = ((a - b : Nat) : Int) by omega, ofInt_natCast64]

/-- An address off the struct block is below its payload or past the 40 bytes
of the struct. -/
theorem off_block {sb : Blk} {a : Nat} (hsz : 40 ≤ sb.sz) (ha : ¬ sb.In a) :
    a < sb.pay ∨ sb.pay + 40 ≤ a := by
  rcases Nat.lt_or_ge a sb.pay with h | h
  · exact .inl h
  · refine .inr ?_
    have := Nat.not_lt.mp fun hlt => ha ⟨h, hlt⟩
    simp only [Blk.fin, Blk.pay] at this ⊢; omega

/-- Peel a struct-field read back through the site's stores. -/
macro "kv_miss" : tactic =>
  `(tactic| try simp (disch := omega) only [ldv_lw_miss, ldv_ld_miss])

/-- The five field stores of one site miss every byte off the struct. -/
macro "kv_frame" : tactic =>
  `(tactic| rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    imgM_store_miss _ _ (by omega)])

/-- A doubleword off the struct block read back through the site's five field
stores. -/
macro "kv_ld5" hsz:term ", " hoff:term ", " hv:term : tactic =>
  `(tactic| (rcases off_block $hsz $hoff with hc5 | hc5 <;>
    (rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]; exact $hv)))

/-- The `ViewSrc` of a site whose five stores wrote `n_sign`, `n_len`,
`n_scale`/`n_refs`, `n_ptr` and `n_value`. -/
macro "kv_src" hvs:term ", " hsz:term : tactic =>
  `(tactic| (refine ($hvs).toSrc ?_ ?_ ?_ ?_ ?_ ?_ ?_
             · kv_miss; exact ldv_lw_hitN _ rfl (by simp) (by decide)
             · kv_miss; exact ldv_lw_hitN _ rfl (toNat_ofNat_mod32 (by omega)) (by omega)
             · kv_miss; exact ldv_lw_hit8lo _ rfl (by simp) (by decide)
             · kv_miss; exact ldv_lw_hit8hi _ rfl (by simp) (by decide)
             · kv_miss; exact ldv_store_hit _ _ _
             · kv_miss; rw [ldv_store_hit]; try simp only [Nat.add_zero]
             · intro a ha
               rcases off_block $hsz ha with hc | hc <;> kv_frame))

/-- The site's reached memory against the step's entry memory. -/
macro "kv_base" hvs:term ", " hsz:term : tactic =>
  `(tactic| (intro a h1 h2 h3
             rcases off_block $hsz h2 with hc | hc <;>
               (kv_frame; exact ($hvs).base a h1 h2 h3)))

/-- **The view of `u`'s high half at `0x80004e08`**: `u1` is `u`'s first
`la - n` digits. -/
theorem kview_80004e08 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt M : Mem} {R : Nat → BitVec 64} {H H' : Heap} {F F' : List Blk} {L : List NumObj}
    {w : NumObj} {sb : Blk} {sp n la W : Nat} (hsf : StackFrame S sp W) (hW : 224 ≤ W)
    (hab : heapEnd + W ≤ sp) (hb : BcHeap S Mt H F L)
    (hvs : ViewStruct S Mt M H H' F F' sb L) (hw : w ∈ L) (hn : n < la)
    (hfit : la ≤ w.rep.len + w.rep.scale) (hlb : la < 2 ^ 30)
    (hsp : ldv .ld M (sp - 192) = BitVec.ofNat 64 w.rep.p) (h2 : R 2 = BitVec.ofNat 64 (sp - 192))
    (h24 : R 24 = BitVec.ofNat 64 sb.pay) (h20 : R 20 = BitVec.ofNat 64 la)
    (h8 : R 8 = BitVec.ofNat 64 n) (h26 : R 26 = BitVec.ofNat 64 w.rep.val)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [14, 15, 23] R' R →
      BcHeap S M' H' F' (viewObj sb w 0 (la - n) :: L) →
      R' 23 = BitVec.ofNat 64 w.rep.val →
      (∀ a, ¬ AllocByte H a → ¬ sb.In a → ¬ bcFreeBytes a → imgM M' a = imgM Mt a) →
      DW live S Q 0x80004e30#64 R' M') :
    DW live S Q 0x80004e08#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hvs.inv.own a h1 h2
  have hbb := hvs.bounds
  have hpl := hbb.lo; have hph := hbb.hi; have hal8 := hbb.al; have hsz := hbb.sz
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have hwn := hb.nums w hw
  num_facts hwn
  have hwv : ldv .ld M (w.rep.p + 32) = BitVec.ofNat 64 w.rep.val :=
    (hvs.word_agree hb hw (by decide)).trans hwn.value
  bc_run hlive hS [h24, h20, h8, h26, h2, ldv_ld_miss, ldv_lw_miss, hsp, hwv,
    subw_nat, ofInt_sub_nat] at 0x80004e30
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (exact frame_acc hsf (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr] at *; omega)
  refine hnext _ _ (by keeps_tac Keeps.refl _ _) (hb.pushView hw (by omega) (by omega) ?_) ?_ ?_
  · kv_src hvs, hsz
  · kv_ld5 hsz, (hvs.word_off hb hw (o := 32) (by decide)), hwv
  · kv_base hvs, hsz

/-- **The view of `u`'s low half at `0x80004e3c`**: `u0` is the last `n` of
`u`'s first `la` digits. -/
theorem kview_80004e3c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt M : Mem} {R : Nat → BitVec 64} {H H' : Heap} {F F' : List Blk} {L : List NumObj}
    {w v : NumObj} {sb : Blk} {n la : Nat} (hb : BcHeap S Mt H F L)
    (hvs : ViewStruct S Mt M H H' F F' sb L) (hw : w ∈ L) (hv : v ∈ L) (hn : n < la)
    (hfit : la ≤ w.rep.len + w.rep.scale) (hlb : la < 2 ^ 30) (hn1 : 1 ≤ n)
    (h19 : R 19 = BitVec.ofNat 64 sb.pay) (h20 : R 20 = BitVec.ofNat 64 la)
    (h8 : R 8 = BitVec.ofNat 64 n) (h23 : R 23 = BitVec.ofNat 64 w.rep.val)
    (h18 : R 18 = BitVec.ofNat 64 v.rep.p)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [14, 20, 23] R' R →
      BcHeap S M' H' F' (viewObj sb w (la - n) n :: L) →
      R' 20 = BitVec.ofNat 64 (la - n) → R' 23 = BitVec.ofNat 64 v.rep.val →
      (∀ a, ¬ AllocByte H a → ¬ sb.In a → ¬ bcFreeBytes a → imgM M' a = imgM Mt a) →
      DW live S Q 0x80004e64#64 R' M') :
    DW live S Q 0x80004e3c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hvs.inv.own a h1 h2
  have hbb := hvs.bounds
  have hpl := hbb.lo; have hph := hbb.hi; have hal8 := hbb.al; have hsz := hbb.sz
  have hwn := hb.nums w hw
  have hvn := hb.nums v hv
  num_facts hwn
  num_facts hvn
  have hvv : ldv .ld M (v.rep.p + 32) = BitVec.ofNat 64 v.rep.val :=
    (hvs.word_agree hb hv (by decide)).trans hvn.value
  bc_run hlive hS [h19, h20, h8, h23, h18, ldv_ld_miss, ldv_lw_miss, hvv,
    sub_ofNat] at 0x80004e64
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr] at *; omega)
  refine hnext _ _ (by keeps_tac Keeps.refl _ _) (hb.pushView hw (by omega) (by omega) ?_)
    (by bsimp []) ?_ ?_
  · kv_src hvs, hsz
  · kv_ld5 hsz, (hvs.word_off hb hv (o := 32) (by decide)), hvv
  · kv_base hvs, hsz

/-- **The view of `v`'s high half at `0x800053d0`**: `v1` is `v`'s first
`lb - n` digits. -/
theorem kview_800053d0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt M : Mem} {R : Nat → BitVec 64} {H H' : Heap} {F F' : List Blk} {L : List NumObj}
    {v : NumObj} {sb : Blk} {n lb : Nat} (hb : BcHeap S Mt H F L)
    (hvs : ViewStruct S Mt M H H' F F' sb L) (hv : v ∈ L) (hn : n < lb)
    (hfit : lb ≤ v.rep.len + v.rep.scale) (hlb : lb < 2 ^ 30)
    (h27 : R 27 = BitVec.ofNat 64 sb.pay) (h21 : R 21 = BitVec.ofNat 64 lb)
    (h8 : R 8 = BitVec.ofNat 64 n) (h23 : R 23 = BitVec.ofNat 64 v.rep.val)
    (h18 : R 18 = BitVec.ofNat 64 v.rep.p)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [14, 15, 23] R' R →
      BcHeap S M' H' F' (viewObj sb v 0 (lb - n) :: L) →
      R' 23 = BitVec.ofNat 64 v.rep.val →
      (∀ a, ¬ AllocByte H a → ¬ sb.In a → ¬ bcFreeBytes a → imgM M' a = imgM Mt a) →
      DW live S Q 0x800053f4#64 R' M') :
    DW live S Q 0x800053d0#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hvs.inv.own a h1 h2
  have hbb := hvs.bounds
  have hpl := hbb.lo; have hph := hbb.hi; have hal8 := hbb.al; have hsz := hbb.sz
  have hvn := hb.nums v hv
  num_facts hvn
  have hvv : ldv .ld M (v.rep.p + 32) = BitVec.ofNat 64 v.rep.val :=
    (hvs.word_agree hb hv (by decide)).trans hvn.value
  bc_run hlive hS [h27, h21, h8, h23, h18, ldv_ld_miss, ldv_lw_miss, hvv,
    subw_nat, ofInt_sub_nat] at 0x800053f4
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr] at *; omega)
  refine hnext _ _ (by keeps_tac Keeps.refl _ _) (hb.pushView hv (by omega) (by omega) ?_) ?_ ?_
  · kv_src hvs, hsz
  · kv_ld5 hsz, (hvs.word_off hb hv (o := 32) (by decide)), hvv
  · kv_base hvs, hsz

/-- **The view of `v`'s low half at `0x80005400`**: `v0` is the last `n` of
`v`'s first `lb` digits; `a7` takes `_zero_`. -/
theorem kview_80005400 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt M : Mem} {R : Nat → BitVec 64} {H H' : Heap} {F F' : List Blk} {L : List NumObj}
    {v z : NumObj} {sb : Blk} {n lb : Nat} (hb : BcHeap S Mt H F L)
    (hvs : ViewStruct S Mt M H H' F F' sb L) (hv : v ∈ L) (hn : n < lb)
    (hfit : lb ≤ v.rep.len + v.rep.scale) (hlb : lb < 2 ^ 30) (hn1 : 1 ≤ n)
    (hz : ldv .ld M zeroAddr = BitVec.ofNat 64 z.rep.p) (hzo : ∀ a, constBytes a → S a)
    (h20 : R 20 = BitVec.ofNat 64 sb.pay) (h21 : R 21 = BitVec.ofNat 64 lb)
    (h8 : R 8 = BitVec.ofNat 64 n) (h23 : R 23 = BitVec.ofNat 64 v.rep.val)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [15, 17, 18, 21, 23] R' R →
      BcHeap S M' H' F' (viewObj sb v (lb - n) n :: L) →
      R' 21 = BitVec.ofNat 64 (lb - n) → R' 23 = BitVec.ofNat 64 (v.rep.val + (lb - n)) →
      R' 18 = BitVec.ofNat 64 zeroAddr → R' 17 = BitVec.ofNat 64 z.rep.p →
      (∀ a, ¬ AllocByte H a → ¬ sb.In a → ¬ bcFreeBytes a → imgM M' a = imgM Mt a) →
      DW live S Q 0x80004eb0#64 R' M') :
    DW live S Q 0x80005400#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hvs.inv.own a h1 h2
  have hbb := hvs.bounds
  have hpl := hbb.lo; have hph := hbb.hi; have hal8 := hbb.al; have hsz := hbb.sz
  have hvn := hb.nums v hv
  num_facts hvn
  have hcst : ∀ b ∈ accAddrs 0x8001cdc8 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact hzo b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  simp only [zeroAddr] at hz
  bc_run hlive hS [h20, h21, h8, h23, ldv_ld_miss, ldv_lw_miss, hz,
    sub_ofNat] at 0x80004eb0
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (exact hcst)
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr] at *; omega)
  refine hnext _ _ (by keeps_tac Keeps.refl _ _) (hb.pushView hv (by omega) (by omega) ?_)
    (by bsimp []) (by bsimp []) (by bsimp [zeroAddr]) (by bsimp []) ?_
  · kv_src hvs, hsz
  · kv_base hvs, hsz

/-- **The view of all of `u` at `0x8000539c`** (`u1` a reference to
`_zero_`): `u0` is `u`'s first `la` digits. -/
theorem kview_8000539c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt M : Mem} {R : Nat → BitVec 64} {H H' : Heap} {F F' : List Blk} {L : List NumObj}
    {w v : NumObj} {sb : Blk} {la : Nat} (hb : BcHeap S Mt H F L)
    (hvs : ViewStruct S Mt M H H' F F' sb L) (hw : w ∈ L) (hv : v ∈ L) (hla : 1 ≤ la)
    (hfit : la ≤ w.rep.len + w.rep.scale) (hlb : la < 2 ^ 30)
    (h19 : R 19 = BitVec.ofNat 64 sb.pay) (h20 : R 20 = BitVec.ofNat 64 la)
    (h26 : R 26 = BitVec.ofNat 64 w.rep.val) (h18 : R 18 = BitVec.ofNat 64 v.rep.p)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [14, 23] R' R →
      BcHeap S M' H' F' (viewObj sb w 0 la :: L) →
      R' 23 = BitVec.ofNat 64 v.rep.val →
      (∀ a, ¬ AllocByte H a → ¬ sb.In a → ¬ bcFreeBytes a → imgM M' a = imgM Mt a) →
      DW live S Q 0x800053bc#64 R' M') :
    DW live S Q 0x8000539c#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hvs.inv.own a h1 h2
  have hbb := hvs.bounds
  have hpl := hbb.lo; have hph := hbb.hi; have hal8 := hbb.al; have hsz := hbb.sz
  have hwn := hb.nums w hw
  have hvn := hb.nums v hv
  num_facts hwn
  num_facts hvn
  have hvv : ldv .ld M (v.rep.p + 32) = BitVec.ofNat 64 v.rep.val :=
    (hvs.word_agree hb hv (by decide)).trans hvn.value
  bc_run hlive hS [h19, h20, h26, h18, ldv_ld_miss, ldv_lw_miss, hvv] at 0x800053bc
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr] at *; omega)
  refine hnext _ _ (by keeps_tac Keeps.refl _ _) (hb.pushView hw (by omega) (by omega) ?_) ?_ ?_
  · kv_src hvs, hsz
  · kv_ld5 hsz, (hvs.word_off hb hv (o := 32) (by decide)), hvv
  · kv_base hvs, hsz

/-- **The view of all of `v` at `0x80004e94`** (`v1` a reference to
`_zero_`): `v0` is `v`'s first `lb` digits. -/
theorem kview_80004e94 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt M : Mem} {R : Nat → BitVec 64} {H H' : Heap} {F F' : List Blk} {L : List NumObj}
    {w : NumObj} {sb : Blk} {k : Nat} (hb : BcHeap S Mt H F L)
    (hvs : ViewStruct S Mt M H H' F F' sb L) (hw : w ∈ L) (hk1 : 1 ≤ k)
    (hfit : k ≤ w.rep.len + w.rep.scale) (hkb : k < 2 ^ 31)
    (h20 : R 20 = BitVec.ofNat 64 sb.pay) (h21 : R 21 = BitVec.ofNat 64 k)
    (h23 : R 23 = BitVec.ofNat 64 w.rep.val)
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [15] R' R →
      BcHeap S M' H' F' (viewObj sb w 0 k :: L) →
      (∀ a, ¬ AllocByte H a → ¬ sb.In a → ¬ bcFreeBytes a → imgM M' a = imgM Mt a) →
      DW live S Q 0x80004eb0#64 R' M') :
    DW live S Q 0x80004e94#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hvs.inv.own a h1 h2
  have hbb := hvs.bounds
  have hpl := hbb.lo; have hph := hbb.hi; have hal8 := hbb.al; have hsz := hbb.sz
  bc_run hlive hS [h20, h21, h23] at 0x80004eb0
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr] at *; omega)
  refine hnext _ _ (by keeps_tac Keeps.refl _ _) (hb.pushView hw hk1 (by omega) ?_) ?_
  · kv_src hvs, hsz
  · kv_base hvs, hsz

end Dc.Mach
