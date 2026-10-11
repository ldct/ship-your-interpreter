import Dc.Mach.DcNum2Int

/-!
# `dc_makestring` (M9)

    dc_makestring (s, len):
      result = dc_malloc (sizeof *result);
      result->s_ptr = dc_malloc (len + 1);
      memcpy (result->s_ptr, s, len);
      result->s_ptr[len] = '\0';
      result->s_len = len;
      result->s_refs = 1;
      return (dc_data) { DC_STRING, result };

- `DcAt.newStr`: a string object on two blocks fresh to the state joins the
  ghost with its one reference as a handle (the inverse of `DcAt.dropStr`).
- `dc_makestring_spec`: the new string holds the `len` source bytes.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **A fresh string with one reference** joins the ghost with its handle. -/
theorem DcAt.newStr {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {o : StrObj}
    (h : DcAt S M H F L C G hs st) (f1 : DcFresh H F L G o.hb) (f2 : DcFresh H F L G o.tb)
    (hne : o.hb ≠ o.tb) (hso : StrAt M o) (h1 : o.refs = 1) :
    DcAt S M H F L C { G with strs := o :: G.strs } (.str o.hb.pay :: hs) st := by
  have hi := h.heap.heap
  have hp : ({ G with strs := o :: G.strs } : DcG).blocks.Perm ([o.hb, o.tb] ++ G.blocks) :=
    DcG.blocks_perm_drop (G := { G with strs := o :: G.strs }) (A := []) (B := G.strs) rfl
  have hnd : ([o.hb, o.tb] ++ G.blocks).Nodup := by
    refine List.nodup_append.mpr ⟨by simp [hne], h.nodup, fun a ha b hb e => ?_⟩
    subst e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact f1.notG hb
    · exact f2.notG hb
  have hpay : ∀ o2 ∈ G.strs, o2.hb.pay ≠ o.hb.pay := fun o2 ho2 e => by
    have s1 := (h.view.strs o2 ho2).hsz; have s2 := hso.hsz
    exact live_apart hi (h.heap.raw.live _ (G.str_mem ho2).1) f1.live
      (fun e' => f1.notG (e' ▸ (G.str_mem ho2).1)) (a := o2.hb.pay)
      (by simp only [Blk.In, Blk.pay, Blk.fin] at *; omega)
      (by simp only [Blk.In, Blk.pay, Blk.fin] at *; omega)
  have d := h.den
  have hvo : ∀ g ∈ G.vals ++ hs, g ≠ .str o.hb.pay := fun g hg e => by
    obtain ⟨v, hv⟩ := d.vals_den g hg
    subst e
    cases v with
    | num n => exact hv
    | str s => obtain ⟨o2, ho2, e1, -⟩ := hv; exact hpay o2 ho2 e1
  have hsub : DObjs.Sub ⟨L, G.strs⟩ ⟨L, o :: G.strs⟩ :=
    ⟨fun z hz => ⟨z, hz, rfl, rfl⟩, fun o2 ho2 => ⟨o2, List.mem_cons_of_mem _ ho2, rfl, rfl⟩⟩
  refine ⟨((h.heap.addRaw f2.live f2.notNum).addRaw f1.live f1.notNum).subRaw
      (fun c hc => by
        have := hp.mem_iff.mp hc
        simp only [List.cons_append, List.nil_append] at this
        exact this) (fun _ _ _ _ => rfl),
    hp.nodup_iff.mpr hnd,
    { h.view with strs := fun o2 ho2 => (List.mem_cons.mp ho2).elim (fun e => e ▸ hso) (h.view.strs o2) },
    { d with
      stk := d.stk.imp fun hh => hh.relist hsub
      regs := fun r hr => (d.regs r hr).imp fun hh => hh.relist hsub
      hsDen := fun g hg => ?_
      numRefs := fun z hz => ?_
      strRefs := fun o2 ho2 => ?_ },
    h.glob, h.col⟩
  · rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨.str o.s, o, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨v, hv⟩ := d.hsDen g hg
      exact ⟨v, hv.relist hsub⟩
  · rw [d.numRefs z hz, count_cons_ne _ _ (by simp)]; rfl
  · rcases List.mem_cons.mp ho2 with rfl | ho2
    · show o2.refs = (G.vals ++ .str o2.hb.pay :: hs).count (.str o2.hb.pay)
      rw [count_cons_self, h1, List.count_eq_zero.mpr fun hm => hvo _ hm rfl]
    · show o2.refs = (G.vals ++ .str o.hb.pay :: hs).count (.str o2.hb.pay)
      rw [d.strRefs o2 ho2, count_cons_ne _ _ fun e => hpay o2 ho2 (GV.str.inj e).symm]

/-- The new string object of `dc_makestring`. -/
abbrev msObj (b1 b2 : Blk) (s : List Nat) : StrObj := ⟨b1, b2, s, 1⟩

/-- Two distinct blocks fresh to the state are apart. -/
theorem fresh_sep {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b1 b2 : Blk}
    (h : DcAt S M H F L C G hs st) (f1 : DcFresh H F L G b1) (f2 : DcFresh H F L G b2)
    (hne : b1 ≠ b2) (z1 : 0 < b1.sz) (z2 : 0 < b2.sz) :
    b1.pay + b1.sz ≤ b2.pay ∨ b2.pay + b2.sz ≤ b1.pay := by
  refine Classical.byContradiction fun hc => ?_
  exact live_apart h.heap.heap f1.live f2.live hne (a := max b1.pay b2.pay)
    (by simp only [Blk.In, Blk.pay, Blk.fin] at *; omega)
    (by simp only [Blk.In, Blk.pay, Blk.fin] at *; omega)

/-- The string stores of `dc_makestring`/`dc_readstring`: the terminating
`NUL`, `s_len`, `s_refs = 1`. -/
abbrev msW (M : Mem) (b1 b2 : Blk) (s : List Nat) : Mem :=
  writeLog (writeLog (writeLog M [(b2.pay + s.length, 1, 0#64)])
    [(b1.pay + 8, 8, BitVec.ofNat 64 s.length)]) [(b1.pay + 16, 4, 1#64)]

/-- **A new string** on two fresh blocks, its text and `s_ptr` already
written, after the stores `msW`: the state gains it with one handle. -/
theorem DcAt.makeStr {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b1 b2 : Blk} {s : List Nat}
    (h : DcAt S M H F L C G hs st) (f1 : DcFresh H F L G b1) (f2 : DcFresh H F L G b2)
    (hne : b1 ≠ b2) (hs1 : 24 ≤ b1.sz) (hs2 : s.length + 1 ≤ b2.sz) (hlen : s.length < 2 ^ 60)
    (hby : ∀ c ∈ s, c < 256)
    (hbytes : ∀ i, i < s.length → imgM M (b2.pay + i) = BitVec.ofNat 8 (s.getD i 0))
    (hptr : ldv .ld M b1.pay = BitVec.ofNat 64 b2.pay) :
    DcAt S (msW M b1 b2 s) H F L C { G with strs := msObj b1 b2 s :: G.strs } (.str b1.pay :: hs) st := by
  have hb1 := blk_bounds h.heap.heap f1.live
  have hb2 := blk_bounds h.heap.heap f2.live
  simp only [heapStart, heapEnd] at hb1 hb2
  have hsep := fresh_sep h f1 f2 hne (by omega) (by omega)
  have hin : ∀ (b : Blk) (x w : Nat), b.pay ≤ x → x + w ≤ b.pay + b.sz →
      ∀ a, (x ≤ a ∧ a < x + w) → b.In a := fun b x w h1 h2 a ha => by
    simp only [Blk.In, Blk.pay, Blk.fin] at *; omega
  have hA := h.rawWrite f2 ((MemOnly.store M (b2.pay + s.length) 1 0#64).mono
    (hin b2 _ 1 (by omega) (by omega)))
  have hB := hA.rawWrite f1 ((MemOnly.store _ (b1.pay + 8) 8 (BitVec.ofNat 64 s.length)).mono
    (hin b1 _ 8 (by omega) (by omega)))
  have hC := hB.rawWrite f1 ((MemOnly.store _ (b1.pay + 16) 4 1#64).mono
    (hin b1 _ 4 (by omega) (by omega)))
  have hso : StrAt (msW M b1 b2 s) (msObj b1 b2 s) := {
    ptr := by
      show ldv .ld _ b1.pay = _
      rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), hptr]
    len := by
      show ldv .ld _ (b1.pay + 8) = _
      rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
    refs := ldv_lw_hitN _ rfl (k := 1) (by decide) (by decide)
    bytes := fun i hi' => by
      change i < s.length at hi'
      show imgM _ (b2.pay + i) = _
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
        imgM_store_miss _ _ (by omega)]
      exact hbytes i hi'
    nul := by
      show imgM _ (b2.pay + s.length) = _
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), imgM_sb]
      rfl
    hsz := hs1
    tsz := hs2
    byte := hby
    refsPos := Nat.le_refl 1
    refsLt := show 1 < 2 ^ 31 by decide }
  exact hC.newStr f1 f2 hne hso rfl

/-- `dc_makestring`'s epilogue (`0x80003ab4`): `s_refs = 1`, the tag word
`DC_STRING` in the frame, the saved registers restored. -/
theorem ms_epi {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp p : Nat} {ra s0v s1v s2v : BitVec 64}
    (hS : HeapOwn S) (hp0 : heapStart ≤ p) (hp1 : p + 24 ≤ heapEnd) (hpa : p % 8 = 0)
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h8 : R 8 = BitVec.ofNat 64 p)
    (h11 : R 11 = BitVec.ofNat 64 p) (h14 : R 14 = 2#64) (h15 : R 15 = 1#64)
    (f40 : ldv .ld M (sp - 48 + 40) = ra) (f32 : ldv .ld M (sp - 48 + 32) = s0v)
    (f24 : ldv .ld M (sp - 48 + 24) = s1v) (f16 : ldv .ld M (sp - 48 + 16) = s2v)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 8, 9, 10, 11, 14, 15, 18] R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = s0v → R' 9 = s1v → R' 18 = s2v →
      (R' 10).toNat % 2 ^ 32 = 2 → R' 11 = BitVec.ofNat 64 p →
      DWO live S Q t ra R' (writeLog (writeLog M [(p + 16, 4, 1#64)]) [(sp - 48, 4, 2#64)])) :
    DWO live S Q t 0x80003ab4#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab hp1
  simp only [heapStart] at hp0
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hS [h2, h8, h14, h15, f40, f32, f24, f16]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  have e32 : ldv .ld (writeLog M [(p + 16, 4, 1#64)]) (sp - 48 + 32) = s0v := by
    rw [ldv_ld_miss _ _ (by omega), f32]
  have e24 : ldv .ld (writeLog M [(p + 16, 4, 1#64)]) (sp - 48 + 24) = s1v := by
    rw [ldv_ld_miss _ _ (by omega), f24]
  have e16 : ldv .ld (writeLog M [(p + 16, 4, 1#64)]) (sp - 48 + 16) = s2v := by
    rw [ldv_ld_miss _ _ (by omega), f16]
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) (by bsimp []; congr 1; omega)
    (by bsimp []; exact e32) (by bsimp []; exact e24) (by bsimp []; exact e16)
    (by bsimp []; rw [ld_lo32_sw]; rfl) (by bsimp [h11])

/-- `dc_makestring`'s tail (`0x80003a98`, after `memcpy`): the terminating
`NUL`, `s_len`, `s_refs = 1`, the result `(DC_STRING, b1)`, the epilogue. -/
theorem ms_tail {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b1 b2 : Blk}
    {s : List Nat} {sp : Nat} {ra s0v s1v s2v : BitVec 64}
    (h : DcAt S M H F L C G hs st) (f1 : DcFresh H F L G b1) (f2 : DcFresh H F L G b2)
    (hne : b1 ≠ b2) (hs1 : 24 ≤ b1.sz) (hs2 : s.length + 1 ≤ b2.sz) (hlen : s.length < 2 ^ 60)
    (hby : ∀ c ∈ s, c < 256)
    (hbytes : ∀ i, i < s.length → imgM M (b2.pay + i) = BitVec.ofNat 8 (s.getD i 0))
    (hptr : ldv .ld M b1.pay = BitVec.ofNat 64 b2.pay)
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h8 : R 8 = BitVec.ofNat 64 b1.pay)
    (h9 : R 9 = BitVec.ofNat 64 s.length)
    (f40 : ldv .ld M (sp - 48 + 40) = ra) (f32 : ldv .ld M (sp - 48 + 32) = s0v)
    (f24 : ldv .ld M (sp - 48 + 24) = s1v) (f16 : ldv .ld M (sp - 48 + 16) = s2v)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M', Keeps [1, 2, 8, 9, 10, 11, 14, 15, 18] R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = s0v → R' 9 = s1v → R' 18 = s2v →
      (R' 10).toNat % 2 ^ 32 = 2 → R' 11 = BitVec.ofNat 64 b1.pay →
      DcAt S M' H F L C { G with strs := msObj b1 b2 s :: G.strs } (.str b1.pay :: hs) st →
      StkOut sp 48 M' M → DWO live S Q t ra R' M') :
    DWO live S Q t 0x80003a98#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hi := h.heap.heap
  have hb1 := blk_bounds hi f1.live
  have hb2 := blk_bounds hi f2.live
  simp only [heapStart, heapEnd] at hb1 hb2
  have hsep := fresh_sep h f1 f2 hne (by omega) (by omega)
  bc_run hlive hS [h2, h8, h9, hptr] at 0x80003ab4
  refine ms_epi (p := b1.pay) (sp := sp) hlive hS (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega) (by omega)
    hsf hab _ (by bsimp [h2]) (by bsimp [h8]) (by bsimp []) (by bsimp []) (by bsimp [])
    (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), f40])
    (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), f32])
    (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), f24])
    (by rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), f16]) hal
    fun R' hk1 e1 e2 e8 e9 e18 e10 e11 => ?_
  have hD := (h.makeStr f1 f2 hne hs1 hs2 hlen hby hbytes hptr).outWrite
    (MemOnly.store _ (sp - 48) 4 2#64) fun a ha =>
    ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  refine hk R' _ (hk1.trans (by keeps_tac Keeps.refl _ _)) e1 e2 e8 e9 e18 e10 e11 hD
    fun a ho _ hf => ?_
  simp only [frameIn] at hf
  have := ho.1
  simp only [heapStart, heapEnd] at this
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]

/-- `dc_makestring` from its second `dc_malloc` (`0x80003a88`): `s_ptr`
stored, `memcpy` of the source into `b2`, the tail. -/
theorem ms_copy {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b1 b2 : Blk}
    {s : List Nat} {sp src : Nat} {ra s0v s1v s2v : BitVec 64}
    (h : DcAt S M H F L C G hs st) (f1 : DcFresh H F L G b1) (f2 : DcFresh H F L G b2)
    (hne : b1 ≠ b2) (hs1 : 24 ≤ b1.sz) (hs2 : s.length + 1 ≤ b2.sz) (hlen : s.length < 2 ^ 60)
    (hby : ∀ c ∈ s, c < 256) (hsrc : OwnedBytes S src s.length)
    (hx1 : ∀ i, i < s.length → src + i < b1.pay ∨ b1.pay + 8 ≤ src + i)
    (hx2 : src + s.length ≤ b2.pay ∨ b2.pay + s.length ≤ src)
    (hval : ∀ i, i < s.length → imgM M (src + i) = BitVec.ofNat 8 (s.getD i 0))
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (h8 : R 8 = BitVec.ofNat 64 b1.pay)
    (h9 : R 9 = BitVec.ofNat 64 s.length) (h10 : R 10 = BitVec.ofNat 64 b2.pay)
    (h18 : R 18 = BitVec.ofNat 64 src)
    (f40 : ldv .ld M (sp - 48 + 40) = ra) (f32 : ldv .ld M (sp - 48 + 32) = s0v)
    (f24 : ldv .ld M (sp - 48 + 24) = s1v) (f16 : ldv .ld M (sp - 48 + 16) = s2v)
    (hal : ra.toNat % 4 = 0)
    (hk : ∀ R' M', Keeps [1, 2, 8, 9, 10, 11, 12, 14, 15, 18] R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → R' 8 = s0v → R' 9 = s1v → R' 18 = s2v →
      (R' 10).toNat % 2 ^ 32 = 2 → R' 11 = BitVec.ofNat 64 b1.pay →
      DcAt S M' H F L C { G with strs := msObj b1 b2 s :: G.strs } (.str b1.pay :: hs) st →
      StkOut sp 48 M' M → DWO live S Q t ra R' M') :
    DWO live S Q t 0x80003a88#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have hi := h.heap.heap
  have hb1 := blk_bounds hi f1.live
  have hb2 := blk_bounds hi f2.live
  simp only [heapStart, heapEnd] at hb1 hb2
  bc_run hlive hS [h2, h8, h9, h10, h18] at 0x8000086c
  have hsep := fresh_sep h f1 f2 hne (by omega) (by omega)
  have hdst : OwnedBytes S b2.pay s.length :=
    ⟨fun i hi' => hS _ (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega),
      by rw [htx]; omega, by omega⟩
  refine memcpy_spec hlive ⟨hdst, hsrc, hx2⟩ _ (by bsimp [h10]) (by bsimp [h18]) (by bsimp [h9])
    (by bsimp []) fun R1 M1 hk1 hfill => ?_
  have hin : ∀ (b : Blk) (x w : Nat), b.pay ≤ x → x + w ≤ b.pay + b.sz →
      ∀ a, (x ≤ a ∧ a < x + w) → b.In a := fun b x w e1 e2 a ha => by
    simp only [Blk.In, Blk.pay, Blk.fin] at *; omega
  have hA := h.rawWrite f1 ((MemOnly.store M b1.pay 8 (BitVec.ofNat 64 b2.pay)).mono
    (hin b1 _ 8 (by omega) (by omega)))
  have hB := hA.rawWrite f2 (fun a ha => hfill.rest a (by
    have e : b2.fin = b2.pay + b2.sz := rfl
    simp only [Blk.In, e] at ha; omega))
  have hrest : ∀ a, (a < b2.pay ∨ b2.pay + s.length ≤ a) → (a + 1 ≤ b1.pay ∨ b1.pay + 8 ≤ a) →
      imgM M1 a = imgM M a := fun a e1 e2 => by
    rw [hfill.rest a e1, imgM_store_miss _ _ (by omega)]
  have hfr : ∀ o, o + 8 ≤ 48 → ldv .ld M1 (sp - 48 + o) = ldv .ld M (sp - 48 + o) := fun o ho =>
    ldv_congr .ld fun j hj => hrest _ (by simp only [widthOfM] at hj; omega)
      (by simp only [widthOfM] at hj; omega)
  refine ms_tail hlive hB f1 f2 hne hs1 hs2 hlen hby (fun i hi' => ?_) ?_ hsf hab R1
    (by rw [hk1.get 2 (by decide)]; bsimp [h2]) (by rw [hk1.get 8 (by decide)]; bsimp [h8])
    (by rw [hk1.get 9 (by decide)]; bsimp [h9])
    ((hfr 40 (by omega)).trans f40) ((hfr 32 (by omega)).trans f32)
    ((hfr 24 (by omega)).trans f24) ((hfr 16 (by omega)).trans f16) hal
    fun R' M' hk2 e1 e2 e8 e9 e18 e10 e11 hd hso => hk R' M' ?_ e1 e2 e8 e9 e18 e10 e11 hd ?_
  · rw [hfill.fill i hi', imgM_store_miss _ _ (by have := hx1 i hi'; omega)]
    exact hval i hi'
  · rw [ldv_congr .ld fun j hj => hfill.rest _ (by simp only [widthOfM] at hj; omega)]
    exact ldv_store_hit _ _ _
  · exact (hk2.mono (by decide)).trans ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
  · intro a ho hg hf
    have := ho.1
    simp only [heapStart, heapEnd] at this
    rw [hso a ho hg hf, hrest a (by omega) (by omega)]

/-- **`dc_makestring`'s source**: `s` at `src`, in the state's blocks or
outside the heap and the caller's frame. -/
structure MsSrc (S : Nat → Prop) (M : Mem) (G : DcG) (sp src : Nat) (s : List Nat) : Prop where
  own : OwnedBytes S src s.length
  loc : ∀ i, i < s.length → InBlocks G.blocks (src + i) ∨ (OutHeap (src + i) ∧ ¬ frameIn sp 64 (src + i))
  val : ∀ i, i < s.length → imgM M (src + i) = BitVec.ofNat 8 (s.getD i 0)
  byte : ∀ c ∈ s, c < 256
  len : s.length < 2 ^ 60

/-- A source byte is off every block fresh to the state. -/
theorem ms_src_off {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {b : Blk} {a : Nat}
    (h : DcAt S M H F L C G hs st) (f : DcFresh H F L G b) (ha : InBlocks G.blocks a ∨ OutHeap a) :
    ¬ b.In a := fun hb => by
  rcases ha with ⟨c, hc, hca⟩ | ho
  · exact live_apart h.heap.heap (h.heap.raw.live c hc) f.live (fun e => f.notG (e ▸ hc)) hca hb
  · have := live_in_heap h.heap.heap f.live hb
    exact ho.1 this

/-- **`dc_makestring (s, len)`** at `0x80003a58`: a new string object with one
reference, holding the `len` source bytes, its handle `(DC_STRING, b1)`
returned in `a0`/`a1` and added to the handles. -/
theorem dc_makestring_spec {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {s : List Nat} {sp src : Nat}
    (h : DcAt S M H F L C G hs st) (hsrc : MsSrc S M G sp src s)
    (hsf : StackFrame S sp 64) (hab : heapEnd + 64 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 src)
    (h11 : R 11 = BitVec.ofNat 64 s.length) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' b1 b2, Keeps cClob R' R → R' 2 = R 2 → (R' 10).toNat % 2 ^ 32 = 2 →
      R' 11 = BitVec.ofNat 64 b1.pay →
      DcAt S M' H' F L C { G with strs := msObj b1 b2 s :: G.strs } (.str b1.pay :: hs) st →
      StkOut sp 64 M' M → DWO live S Q t (R 1) R' M')
    (hoom : ∀ R' M', R' 2 = BitVec.ofNat 64 (sp - 64) → StkOut sp 64 M' M →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80003a58#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hlen := hsrc.len
  bc_run hlive hS [h2, word_sub48] at 0x80001ea0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM1 : MemOnly (frameIn sp 48) (writeLog (writeLog (writeLog (writeLog M
      [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 40, 8, R 1)]) [(sp - 48 + 32, 8, R 8)])
      [(sp - 48 + 24, 8, R 9)]) M := fun a ha => by
    simp only [frameIn] at ha; repeat rw [imgM_store_miss _ _ (by omega)]
  have hP : ∀ a, frameIn sp 48 a → OutHeap a ∧ ¬ DcGlob a := fun a ha => by
    simp only [frameIn] at ha
    exact ⟨outHeap_of_ge (by simp only [heapEnd]; omega), fun hg => by
      have := hg.lt; simp only [heapStart] at this; omega⟩
  have h1 := h.outWrite hM1 hP
  -- the source bytes are off the allocator's bytes and both frames
  have hloc : ∀ i, i < s.length → InBlocks G.blocks (src + i) ∨ OutHeap (src + i) := fun i hi' =>
    (hsrc.loc i hi').imp id And.left
  have hnf : ∀ i, i < s.length → ¬ frameIn sp 64 (src + i) := fun i hi' => by
    rcases hsrc.loc i hi' with hb | ⟨_, hf⟩
    · have := (h.inBlocks_heap hb).1; simp only [frameIn, heapEnd] at this ⊢; omega
    · exact hf
  have hna : ∀ {H' : Heap} {M' : Mem} {F' : List Blk} {L' : List NumObj} {C' : BcConsts} {hs' : List GV}
      {st' : St}, DcAt S M' H' F' L' C' G hs' st' → ∀ i, i < s.length → ¬ AllocByte H' (src + i) :=
    fun hd i hi' => (hloc i hi').elim (fun hb => (hd.inBlocks_heap hb).2)
      (OutHeap.not_alloc hd.heap.heap)
  refine dc_malloc_spec hlive h1.heap.heap (n := 24) (sp := sp - 48) (by decide)
    (hsf.sub (m := 48) (n := 16) (by decide)) (by simp only [heapEnd]; omega) _ (by bsimp [])
    (by bsimp []) (by bsimp []) (fun R1 M2 H2 b1 hk1 hp hr10 => ?_) (fun R1 M2 hr2 hfr => ?_)
  rotate_left
  · refine hoom R1 M2 (by rw [hr2, Nat.sub_sub]) fun a ho hg hf => ?_
    rw [hfr a (OutHeap.not_alloc h1.heap.heap ho) fun hf' => hf (by
      simp only [frameIn] at hf' ⊢; omega)]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
  obtain ⟨h2', g1⟩ := h1.malloc hp (by decide) (by simp only [heapEnd]; omega)
  have hS2 : HeapOwn S := fun a e1 e2 => h2'.heap.heap.own a e1 e2
  have q1 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2 (by decide)]; bsimp []
  have q9 : R1 9 = BitVec.ofNat 64 s.length := by rw [hk1.get 9 (by decide)]; bsimp [h11]
  bsimp []
  bc_run hlive hS2 [q1, q9, hr10, word_succ] at 0x80001ea0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_malloc_spec hlive h2'.heap.heap (n := s.length + 1) (sp := sp - 48) (by omega)
    (hsf.sub (m := 48) (n := 16) (by decide)) (by simp only [heapEnd]; omega) _ (by bsimp [q9, word_succ])
    (by bsimp [q1]) (by bsimp []) (fun R2 M3 H3 b2 hk2 hp2 hr10' => ?_) (fun R2 M3 hr2 hfr => ?_)
  rotate_left
  · refine hoom R2 M3 (by rw [hr2, Nat.sub_sub]) fun a ho hg hf => ?_
    rw [hfr a (OutHeap.not_alloc h2'.heap.heap ho) fun hf' => hf (by
      simp only [frameIn] at hf' ⊢; omega),
      hp.frame a (OutHeap.not_alloc h1.heap.heap ho) fun hf' => hf (by
      simp only [frameIn] at hf' ⊢; omega)]
    exact hM1 a fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
  obtain ⟨h3, g2⟩ := h2'.malloc hp2 (by omega) (by simp only [heapEnd]; omega)
  have g1' := g1.afterMalloc hp2
  have hsz1 := hp.size
  have hsz2 := hp2.size
  have hne : b1 ≠ b2 := fun e => by
    subst e
    have e1 : b1.fin = b1.pay + b1.sz := rfl
    have e2 : b1.pay = b1.h + 16 := rfl
    exact live_not_alloc h2'.heap.heap g1.live (a := b1.pay) ⟨Nat.le_refl _, by omega⟩
      (hp2.alloc _ (by omega) (by omega))
  -- frame words and source bytes through both calls
  have hfm : ∀ a, OutHeap a → ¬ frameIn (sp - 48) 16 a → imgM M3 a = imgM M2 a ∧ imgM M2 a =
      imgM (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 40, 8, R 1)])
        [(sp - 48 + 32, 8, R 8)]) [(sp - 48 + 24, 8, R 9)]) a := fun a ho hf =>
    ⟨hp2.frame a (OutHeap.not_alloc h2'.heap.heap ho) hf, hp.frame a (OutHeap.not_alloc h1.heap.heap ho) hf⟩
  have hfrm : ∀ o, 8 ≤ o → o + 8 ≤ 48 → ldv .ld M3 (sp - 48 + o) =
      ldv .ld (writeLog (writeLog (writeLog (writeLog M [(sp - 48 + 16, 8, R 18)]) [(sp - 48 + 40, 8, R 1)])
        [(sp - 48 + 32, 8, R 8)]) [(sp - 48 + 24, 8, R 9)]) (sp - 48 + o) := fun o ho1 ho2 =>
    ldv_congr .ld fun j hj => by
      have ho : OutHeap (sp - 48 + o + j) := outHeap_of_ge (by simp only [widthOfM] at hj; omega)
      have := hfm _ ho (by simp only [frameIn, widthOfM] at hj ⊢; omega)
      exact this.1.trans this.2
  have hv : ∀ i, i < s.length → imgM M3 (src + i) = BitVec.ofNat 8 (s.getD i 0) := fun i hi' => by
    have hf := hnf i hi'
    simp only [frameIn] at hf
    rw [hp2.frame _ (hna h2' i hi') (by simp only [frameIn]; omega),
      hp.frame _ (hna h1 i hi') (by simp only [frameIn]; omega), hM1 _ (by simp only [frameIn]; omega)]
    exact hsrc.val i hi'
  have hb1 := blk_bounds h3.heap.heap g1'.live
  simp only [heapStart, heapEnd] at hb1
  bsimp []
  refine ms_copy (ra := R 1) (s0v := R 8) (s1v := R 9) (s2v := R 18) hlive h3 g1' g2 hne hsz1 (by omega) (by omega) hsrc.byte hsrc.own
    (fun i hi' => ?_) ?_ hv (hsf.mono (n := 48) (by decide)) (by simp only [heapEnd]; omega) R2
    (by rw [hk2.get 2 (by decide)]; bsimp [q1]) (by rw [hk2.get 8 (by decide)]; bsimp [hr10])
    (by rw [hk2.get 9 (by decide)]; bsimp [q9]) hr10'
    (by rw [hk2.get 18 (by decide)]; bsimp []; rw [hk1.get 18 (by decide)]; bsimp [h10])
    ((hfrm 40 (by omega) (by omega)).trans (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]))
    ((hfrm 32 (by omega) (by omega)).trans (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]))
    ((hfrm 24 (by omega) (by omega)).trans (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]))
    ((hfrm 16 (by omega) (by omega)).trans (by simp (disch := omega) only [ldv_ld_miss, ldv_store_hit]))
    hal fun R' M' hk3 e1 e2 e8 e9 e18 e10 e11 hd hso => hk R' M' H3 b1 b2 ?_ (by rw [e2, h2]) e10 e11 hd ?_
  · have := ms_src_off h3 g1' (hloc i hi')
    have e1 : b1.fin = b1.pay + b1.sz := rfl
    simp only [Blk.In, e1] at this
    omega
  · refine Classical.byContradiction fun hc => ?_
    have hm : max src b2.pay - src < s.length := by omega
    have := ms_src_off h3 g2 (hloc _ hm)
    have e1 : b2.fin = b2.pay + b2.sz := rfl
    simp only [Blk.In, e1] at this
    omega
  · refine Keeps.restoreAll (rs := [2, 8, 9, 18]) ((hk3.mono (ks' := [2, 8, 9, 18] ++ cClob) (by decide)).trans
      (by keeps_tac ((hk2.mono (ks' := [2, 8, 9, 18] ++ cClob) (by decide)).trans
        (by keeps_tac ((hk1.mono (ks' := [2, 8, 9, 18] ++ cClob) (by decide)).trans
          (by keeps_tac Keeps.refl _ _)))))) fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rw [e2, h2]
    · exact e8
    · exact e9
    · exact e18
  · intro a ho hg hf
    have hf48 : ¬ frameIn sp 48 a := fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega)
    rw [hso a ho hg hf48]
    have := hfm a ho (fun hf' => hf (by simp only [frameIn] at hf' ⊢; omega))
    rw [this.1, this.2]
    exact hM1 a hf48

end Dc.Mach
