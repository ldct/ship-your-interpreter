import Dc.Mach.DcBinop

/-!
# `dc_cmpop` (M9)

    dc_cmpop ():
      if (dc_stack == NULL || dc_stack->link == NULL)
        { fprintf (stderr, "%s: stack empty\n", progname); return 0; }
      if (top two types are not both DC_NUMBER)
        { fprintf (stderr, "%s: non-numeric value\n", progname); return 0; }
      dc_pop (&b); dc_pop (&a);
      result = dc_compare (b.v.number, a.v.number);   -- `j bc_compare`
      dc_free_num (&a.v.number); dc_free_num (&b.v.number);
      return result;

- `cmpop_msg`: a message and the return of `0`.
- `cmpop_go`: the pops, the comparison and the frees.
- `dc_cmpop_spec`: `cmpop st`, the ordering in `a0` as `ordWord`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **A message of `dc_cmpop`** (`0x8000348c`: non-numeric, `0x800034bc`:
stack empty) to `stderr`, then the return of `0`. -/
theorem cmpop_msg {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 368) (hab : heapEnd + 368 ≤ sp) {pc : BitVec 64}
    (hpc : pc = 0x8000348c#64 ∨ pc = 0x800034bc#64) {ra : BitVec 64}
    (hra : ldv .ld M (sp - 64 + 56) = ra) (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64))
    (hk : ∀ R' M', Keeps (1 :: 2 :: opClob) R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      R' 10 = 0#64 → (∀ a, (a < sp - 64 - 304 ∨ sp - 64 ≤ a) → imgM M' a = imgM M a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t pc R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hpn := h.view.prog
  have hG := h.glob
  have hfd := h.errFile
  have hro : ∀ b ∈ accAddrs 2147516928 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  have hsf1 : StackFrame S (sp - 64) 304 := hsf.within (by omega) (by decide)
  have msg : ∀ {p n : Nat}, ProgMsg p n → n < 2 ^ 60 → ∀ R1 : Nat → BitVec 64,
      Keeps (1 :: fprintfClob) R1 R → (R1 1 = 0x800034a8#64 ∨ R1 1 = 0x800034d8#64) →
      R1 2 = R 2 → (R1 10).toNat = stderrAddr →
      (R1 11).toNat = p → R1 12 = BitVec.ofNat 64 dcNameAddr →
      DWO live S Q t 0x80000774#64 R1 M := by
    intro p n hm hn R1 hk1 e1 e2 e10 e11 e12
    refine fprintf_prog_spec hlive hm hn hsf1 (by simp only [stderrAddr]; omega) hfd R1
      (by rw [e2, h2]; bsimp []) e10 e11 e12
      (by rcases e1 with e1 | e1 <;> rw [e1] <;> rfl) fun R' M' hk2 hfr => ?_
    have hfr' : ∀ a, (a < sp - 64 - 304 ∨ sp - 64 ≤ a) → imgM M' a = imgM M a := hfr
    have q2 : R' 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk2.get 2 (by decide), e2, h2]
    have hra' : ldv .ld M' (sp - 64 + 56) = ra := by
      rw [ldv_congr .ld fun j hj => hfr' _ (.inr (by simp only [widthOfM] at hj; omega))]
      exact hra
    have hS' : HeapOwn S := hS
    have k1 : Keeps (1 :: 2 :: opClob) R' R := (hk2.mono (by decide)).trans (hk1.mono (by decide))
    rcases e1 with e1 | e1 <;> rw [e1]
    · bc_run hlive hS' [q2, hra']
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      · exact hral
      exact hk _ M' (by keeps_tac k1) (by bsimp []) (by bsimp [q2]; congr 1; omega) (by bsimp []) hfr'
    · bc_run hlive hS' [q2, hra']
      all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
      · exact hral
      exact hk _ M' (by keeps_tac k1) (by bsimp []) (by bsimp [q2]; congr 1; omega) (by bsimp []) hfr'
  rcases hpc with rfl | rfl
  · bc_run hlive hS [h2, hpn, stderr_word] at 0x80000774
    exact msg nonNumMsg (by decide) _ (by keeps_tac Keeps.refl _ _) (.inl (by bsimp []))
      (by bsimp []) (by bsimp []; decide) (by bsimp []) (by bsimp [])
  · bc_run hlive hS [h2, hpn, stderr_word] at 0x80000774
    exact msg stackEmptyMsg (by decide) _ (by keeps_tac Keeps.refl _ _) (.inr (by bsimp []))
      (by bsimp []) (by bsimp []; decide) (by bsimp []) (by bsimp [])

/-- `cmpop` of a stack with two numbers on top. -/
theorem cmpop_push2 (st : St) (na nb : Num) :
    cmpop ((st.push (.num na)).push (.num nb)) = (Num.cmp nb na, st) := by
  cases st; rfl

/-- **`dc_cmpop` with two numbers on top** (`0x800034dc` to the return): both
popped, compared, freed. -/
theorem cmpop_go {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 400) (hab : heapEnd + 400 ≤ sp)
    {cb ca : Blk} {pb pa : Nat} {rest : List (Blk × GV)}
    (hstk : G.stk = (cb, .num pb) :: (ca, .num pa) :: rest) {ra : BitVec 64}
    (hra : ldv .ld M (sp - 64 + 56) = ra) (hral : ra.toNat % 4 = 0)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 (sp - 64))
    (hk : ∀ R' M' H' F' L' C' G', Keeps (1 :: 2 :: opClob) R' R → R' 1 = ra →
      R' 2 = BitVec.ofNat 64 sp → G'.lk = G.lk → R' 10 = ordWord (cmpop st).1 →
      DcAt S M' H' F' L' C' G' hs (cmpop st).2 →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp 400 a → imgM M' a = imgM M a) →
      DWO live S Q t ra R' M') :
    DWO live S Q t 0x800034dc#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 64 := by simp only [heapEnd]; omega
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  bc_run hlive hS [h2] at 0x8000310c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hslot : ∀ o, o + 16 ≤ 64 → o % 8 = 0 → DatSlot S (sp - 64) (sp - 64 + o) := fun o h1 h2 =>
    ⟨fun i hi => hsf.own _ (by omega) (by omega), by omega, by omega, by omega⟩
  have hden := h.den.stk
  rw [hstk] at hden
  have hne : st.stack ≠ [] := fun e => by rw [e] at hden; cases hden
  refine dc_pop_spec hlive h (hsf.within (m := 64) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (hslot 32 (by omega) (by omega)) _ (by bsimp []) (by bsimp [h2])
    (by bsimp []) (fun R2 M2 H2 G1 g v st1 est eG hk2 e10 h1' hd1 hout1 => ?_)
    (fun e => absurd e hne)
  obtain ⟨c, rfl⟩ := eG
  simp only [List.cons.injEq, Prod.mk.injEq] at hstk
  obtain ⟨⟨rfl, rfl⟩, hG1⟩ := hstk
  subst est
  obtain ⟨nb, rfl, hdb⟩ := (by cases hden with | cons hh _ => exact den_num_head hh :
    ∃ nb, v = .num nb ∧ (GV.num pb).Den ⟨L, G1.strs⟩ (.num nb))
  have q2 : R2 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk2.get 2 (by decide)]; bsimp [h2]
  have hS2 : HeapOwn S := fun a h1 h2 => h1'.heap.heap.own a h1 h2
  bsimp []
  bc_run hlive hS2 [q2] at 0x8000310c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hden1 := h1'.den.stk
  rw [hG1] at hden1
  have hne1 : st1.stack ≠ [] := fun e => by rw [e] at hden1; cases hden1
  refine dc_pop_spec hlive h1' (hsf.within (m := 64) (n := 336) (by omega) (by decide))
    (by simp only [heapEnd]; omega) (hslot 16 (by omega) (by omega)) _ (by bsimp []) (by bsimp [q2])
    (by bsimp []) (fun R3 M3 H3 G2 g2 v2 st2 est2 eG2 hk3 e10' h2' hd2 hout2 => ?_)
    (fun e => absurd e hne1)
  obtain ⟨c2, rfl⟩ := eG2
  simp only [List.cons.injEq, Prod.mk.injEq] at hG1
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hG1
  subst est2
  obtain ⟨na, rfl, hda⟩ := (by cases hden1 with | cons hh _ => exact den_num_head hh :
    ∃ na, v2 = .num na ∧ (GV.num pa).Den ⟨L, G2.strs⟩ (.num na))
  have ag3 : ∀ a, sp - 64 ≤ a → (a < sp - 64 + 16 ∨ sp - 64 + 32 ≤ a) → imgM M3 a = imgM M2 a :=
    fun a ha hn => hout2 a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 _) hn
  have hb3 : ldv .ld M3 (sp - 64 + 32 + 8) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => ag3 _ (by omega) (by simp only [widthOfM] at hj; omega)]
    exact hd1.ptr
  have ha3 := hd2.ptr
  have q3 : R3 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk3.get 2 (by decide)]; bsimp [q2]
  have hS3 : HeapOwn S := fun a h1 h2 => h2'.heap.heap.own a h1 h2
  bsimp []
  bc_run hlive hS3 [q3, hb3, ha3] at 0x800049d8
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  obtain ⟨xa, hxa, epa, ena⟩ := hda
  obtain ⟨xb, hxb, epb, enb⟩ := hdb
  have hxb2 : xb ∈ L := hxb
  have pa1 := h2'.den.pos xa hxa
  have pb1 := h2'.den.pos xb hxb
  refine bc_compare_spec hlive hS3 (h2'.heap.nums xb hxb) (h2'.heap.nums xa hxa)
    (h2'.den.norm xb hxb) (h2'.den.norm xa hxa) (fun e => absurd e (by omega))
    (fun e => absurd e (by omega)) _ ?_ ?_ ?_ fun R4 hk4 h40 => ?_
  all_goals try (bsimp [epa, epb, GV.ptr]; done)
  have q4 : R4 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk4.get 2 (by decide)]; bsimp [q3]
  bsimp []
  bc_run hlive hS3 [q4] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hm4 : MemOnly (frameIn sp 64) (writeLog M3 [(sp - 64 + 8, 8, R4 10)]) M3 := fun a ha => by
    simp only [frameIn] at ha; rw [imgM_store_miss _ _ (by omega)]
  have h4 := h2'.outWrite hm4 fun a ha => by
    simp only [frameIn] at ha; exact ⟨(above_sp hab2 ha.1).1, (above_sp hab2 ha.1).2.1⟩
  have hsf32 : StackFrame S (sp - 64) 32 := hsf.within (by omega) (by decide)
  have hwa : ldv .ld (writeLog M3 [(sp - 64 + 8, 8, R4 10)]) (sp - 64 + 24) = BitVec.ofNat 64 pa := by
    rw [ldv_ld_miss _ _ (by omega)]; exact ha3
  refine dc_free_num_spec hlive h4 (q := sp - 64 + 24) (hsf.slot (by omega) (by omega) (by omega))
    (by omega) hwa hsf32 (by simp only [heapEnd]; omega) (Or.inr (by omega)) _ (by bsimp [])
    (by bsimp [q4]) (by bsimp []) (fun R5 M5 H5 F5 L5 C5 hk5 h5 _ hout5 => ?_)
  have ag5 : ∀ a, sp - 64 ≤ a → ¬ slotBytes (sp - 64 + 24) a →
      imgM M5 a = imgM (writeLog M3 [(sp - 64 + 8, 8, R4 10)]) a :=
    fun a ha hn => hout5 a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 32) hn
  have q5 : R5 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk5.get 2 (by decide)]; bsimp [q4]
  have hS5 : HeapOwn S := fun a e1 e2 => h5.heap.heap.own a e1 e2
  have hwb : ldv .ld M5 (sp - 64 + 40) = BitVec.ofNat 64 pb := by
    rw [ldv_congr .ld fun j hj => ag5 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega),
      ldv_ld_miss _ _ (by omega)]
    exact hb3
  bsimp []
  bc_run hlive hS5 [q5] at 0x80002ba0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  refine dc_free_num_spec hlive h5 (q := sp - 64 + 40) (hsf.slot (by omega) (by omega) (by omega))
    (by omega) hwb hsf32 (by simp only [heapEnd]; omega) (Or.inr (by omega)) _ (by bsimp [])
    (by bsimp [q5]) (by bsimp []) (fun R6 M6 H6 F6 L6 C6 hk6 h6 _ hout6 => ?_)
  have ag6 : ∀ a, sp - 64 ≤ a → ¬ slotBytes (sp - 64 + 40) a → imgM M6 a = imgM M5 a :=
    fun a ha hn => hout6 a (above_sp hab2 ha).1 (above_sp hab2 ha).2.1 ((above_sp hab2 ha).2.2 32) hn
  have q6 : R6 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk6.get 2 (by decide)]; bsimp [q5]
  have hS6 : HeapOwn S := fun a e1 e2 => h6.heap.heap.own a e1 e2
  have hag : ∀ a, sp - 64 + 48 ≤ a → imgM M6 a = imgM M3 a :=
    fun a ha => by
      rw [ag6 a (by omega) (by simp only [slotBytes]; omega),
        ag5 a (by omega) (by simp only [slotBytes]; omega), imgM_store_miss _ _ (by omega)]
  have hw8 : ldv .ld M6 (sp - 64 + 8) = R4 10 := by
    rw [ldv_congr .ld fun j hj =>
      (ag6 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega)).trans
        (ag5 _ (by omega) (by simp only [slotBytes, widthOfM] at hj ⊢; omega))]
    exact ldv_store_hit _ _ _
  have hra6 : ldv .ld M6 (sp - 64 + 56) = ra := by
    rw [ldv_congr .ld fun j hj => hag _ (by simp only [widthOfM] at hj; omega),
      ldv_congr .ld fun j hj => ag3 _ (by omega) (.inr (by simp only [widthOfM] at hj; omega)),
      ldv_congr .ld fun j hj => hout1 _ (above_sp hab2 (a := sp - 64 + 56 + j) (by omega)).1
        (above_sp hab2 (a := sp - 64 + 56 + j) (by omega)).2.1
        ((above_sp hab2 (a := sp - 64 + 56 + j) (by omega)).2.2 _)
        (.inr (by simp only [widthOfM] at hj; omega))]
    exact hra
  bsimp []
  bc_run hlive hS6 [q6, hw8, hra6]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  · exact hral
  rw [cmpop_push2] at hk
  refine hk _ M6 H6 F6 L6 C6 _ (by keeps_tac ((hk6.mono (by decide)).trans (by keeps_tac
    ((hk5.mono (by decide)).trans (by keeps_tac ((hk4.mono (by decide)).trans (by keeps_tac
      ((hk3.mono (by decide)).trans (by keeps_tac ((hk2.mono (by decide)).trans
        (by keeps_tac Keeps.refl _ _)))))))))))
    (by bsimp []) (by bsimp []; congr 1; omega) rfl (by bsimp [h40, ena, enb]) h6 fun a ho hg hf => ?_
  have hlo : a < sp - 400 ∨ sp ≤ a :=
    Classical.byContradiction fun hc => hf ⟨by omega, by omega⟩
  have hf1 : ¬ frameIn (sp - 64) 32 a := fun h' => by have := h'.1; have := h'.2; omega
  have hf2 : ¬ frameIn (sp - 64) 336 a := fun h' => by have := h'.1; have := h'.2; omega
  rw [hout6 a ho hg hf1 (by simp only [slotBytes]; omega), hout5 a ho hg hf1 (by simp only [slotBytes]; omega),
    imgM_store_miss _ _ (by omega), hout2 a ho hg hf2 (by omega), hout1 a ho hg hf2 (by omega)]

theorem cmpop_of_no2 {st : St} (h : No2 st) : cmpop st = (.eq, st) := by
  unfold cmpop
  split
  · rename_i b a rest e; exact absurd e (h b a rest)
  · rfl

/-- **`dc_cmpop`** at `0x8000345c`: the ordering of `cmpop st` in `a0`
(`ordWord`), the state `(cmpop st).2`; with fewer than two numbers on top a
message goes to `stderr`. -/
theorem dc_cmpop_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St}
    (h : DcAt S M H F L C G hs st) {sp : Nat}
    (hsf : StackFrame S sp 400) (hab : heapEnd + 400 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps (1 :: 2 :: opClob) R' R → R' 1 = R 1 → R' 2 = R 2 →
      G'.lk = G.lk → R' 10 = ordWord (cmpop st).1 → DcAt S M' H' F' L' C' G' hs (cmpop st).2 →
      StkOut sp 400 M' M → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x8000345c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 64 := by simp only [heapEnd]; omega
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  bc_run hlive hS [h2, word_sub64 (x := sp) (by omega)] at 0x8000346c
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hm1 : MemOnly (frameIn sp 64) (writeLog M [(sp - 64 + 56, 8, R 1)]) M := fun a ha => by
    simp only [frameIn] at ha; rw [imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hm1 fun a ha => by
    simp only [frameIn] at ha; exact ⟨(above_sp hab2 ha.1).1, (above_sp hab2 ha.1).2.1⟩
  have hra : ldv .ld (writeLog M [(sp - 64 + 56, 8, R 1)]) (sp - 64 + 56) = R 1 := ldv_store_hit _ _ _
  have hds : dcStackAddr = 2147601816 := rfl
  refine stkchk_8000346c hlive h1 _ (by bsimp []; rw [hds, ldv_ld_miss _ _ (by omega)])
    (fun hpc hno R1 hk1 => ?_) fun cb ca pb pa rest hstk R1 hk1 _ => ?_
  · have q1 : R1 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk1.get 2 (by decide)]; bsimp []
    have k1 : Keeps (1 :: 2 :: opClob) R1 R :=
      (hk1.mono (by decide) : Keeps (1 :: 2 :: opClob) R1 _).trans (by keeps_tac Keeps.refl _ _)
    refine cmpop_msg hlive h1 (hsf.mono (by decide)) (by omega) hpc hra hal R1 q1
      fun R' M' kk e1 e2 e10 hfr => ?_
    have hm' : MemOnly (frameIn sp 400) M' M := fun a ha => by
      simp only [frameIn] at ha
      rw [hfr a (by omega), hm1 a (by simp only [frameIn]; omega)]
    refine hk R' M' H F L C G (kk.trans k1) e1
      (by rw [e2, h2]) rfl (by rw [cmpop_of_no2 hno, e10]; rfl) ?_ fun a _ _ hf => hm' a hf
    rw [cmpop_of_no2 hno]
    exact h.outWrite hm' fun a ha => by
      simp only [frameIn] at ha
      exact ⟨(above_sp (sp := sp - 400) (by simp only [heapEnd]; omega) ha.1).1,
        (above_sp (sp := sp - 400) (by simp only [heapEnd]; omega) ha.1).2.1⟩
  · have q1 : R1 2 = BitVec.ofNat 64 (sp - 64) := by rw [hk1.get 2 (by decide)]; bsimp []
    have k1 : Keeps (1 :: 2 :: opClob) R1 R :=
      (hk1.mono (by decide) : Keeps (1 :: 2 :: opClob) R1 _).trans (by keeps_tac Keeps.refl _ _)
    refine cmpop_go hlive h1 hsf hab hstk hra hal R1 q1
      fun R' M' H' F' L' C' G' kk e1 e2 elk e10 h' hout => ?_
    refine hk R' M' H' F' L' C' G' (kk.trans k1) e1
      (by rw [e2, h2]) elk e10 h' fun a ho hg hf => ?_
    rw [hout a ho hg hf, hm1 a fun h' => hf (by simp only [frameIn] at h' ⊢; omega)]

end Dc.Mach
