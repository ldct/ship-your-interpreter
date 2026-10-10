import Dc.Mach.DcDumpLoop

/-!
# `dc_dump_num`'s output and exit (M9)

- `dn_print`: the print loop, by induction on the cells: `putchar` of each
  cell's byte, then `free` of the cell.
- `dn_free`: `bc_free_num` of one of the three slots from inside the frame.
- `dn_exit`: the three frees and the epilogue.
- `dc_dump_num_spec`: the whole function.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **After the print loop** (`0x80002b68`): the three handles in their slots. -/
structure DnEnd (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64) (sp : Nat) (H : Heap)
    (F : List Blk) (L : List NumObj) (C : BcConsts) (G : DcG) (hs : List GV) (st : St)
    (pd pv pb : Nat) : Prop where
  fr : DnAt S M0 M R0 R sp
  h : DcAt S M H F L C G (.num pd :: .num pv :: .num pb :: hs) st
  w24 : ldv .ld M (sp - 80 + 24) = BitVec.ofNat 64 pv
  w32 : ldv .ld M (sp - 80 + 32) = BitVec.ofNat 64 pb
  w40 : ldv .ld M (sp - 80 + 40) = BitVec.ofNat 64 pd

/-- **The print loop** (`0x80002b50` to `0x80002b68`): each cell's byte
printed, the cell freed. -/
theorem dn_print {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {T : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pd pv pb sp : Nat} {R0 : Nat → BitVec 64}
    (hsf : StackFrame S sp dnN) (hab : heapEnd + dnN ≤ sp)
    (hk : ∀ R' M' H', DnEnd S M0 M' R0 R' sp H' F L C G hs st pd pv pb →
      DWO live S Q T 0x80002b68#64 R' M') :
    ∀ cells ds p t' R M H, DnPr S M0 M R0 R sp H F L C G hs st pd pv pb cells ds p →
      t' ++ Dc.outStr ds = T → DWO live S Q t' 0x80002b50#64 R M := by
  have hsf' := hsf; have hab' := hab
  have hNW : dnN = 80 + (176 + rmStack (2 ^ 30)) := rfl
  rw [hNW] at hsf' hab'
  have hsl := hsf'.lo; have hsh := hsf'.hi; have hsa := hsf'.al
  simp only [heapEnd] at hab'
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 80 := by simp only [heapEnd]; omega
  intro cells
  induction cells with
  | nil => intro ds p t' R M H hp _; exact absurd rfl hp.ne
  | cons c cs ih =>
  intro ds p t' R M H hp ht
  cases ds with
  | nil => have := hp.stk.stk.length; simp at this
  | cons d ds =>
  have hd := hp.stk.stk.head
  have hfc := hp.stk.fresh c List.mem_cons_self
  have hdl : d < 256 := hp.stk.dig d List.mem_cons_self
  have h := hp.h
  have hi := h.heap.heap
  have hS : HeapOwn S := fun a e1 e2 => hi.own a e1 e2
  have hcz := hd.sz
  have hcl := live_in_heap hi hfc.live (a := c.pay) ⟨Nat.le_refl _, by simp only [Blk.pay, Blk.fin]; omega⟩
  have hch := live_in_heap hi hfc.live (a := c.pay + 15)
    ⟨by simp only [Blk.pay]; omega, by simp only [Blk.pay, Blk.fin]; omega⟩
  simp only [heapStart, heapEnd] at hcl hch
  have hcal : c.h % 16 = 0 := (hi.blk (List.mem_append_right _ hfc.live)).al
  have hcp : c.pay = c.h + 16 := rfl
  have s0 : R 8 = BitVec.ofNat 64 c.pay := hd.p ▸ hp.s0
  have hfd : FdAt S M stdoutFile 1 :=
    ⟨fun i hi => h.glob _ (by simp only [DcGlob, stdoutFile, dc_addrs]; omega),
      h.view.outFd, by decide, by decide, by decide⟩
  have po : putcStr (lo8 (BitVec.ofNat 64 d)) = Dc.outStr [d] := by rw [putc_ofNat hdl]; rfl
  bc_run hlive hS [s0, hd.word] at 0x80000628
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  refine putchar_spec hlive hfd _ ?pal fun R1 hk1 h10 => ?_
  case pal => bsimp []
  have r18 : R1 8 = BitVec.ofNat 64 c.pay := by rw [hk1.get 8 (by decide)]; bsimp [s0]
  bsimp [po]
  bc_run hlive hS [r18] at 0x80000a0c
  all_goals first | exact acc_heap hS (by omega) (by omega) | skip
  obtain ⟨lpre, lpost, hl⟩ := List.append_of_mem hfc.live
  refine free_spec hlive hi hl _ ?f10 ?fal fun R2 M2 hk2 hpf => ?_
  case f10 => bsimp [r18]
  case fal => bsimp []
  have h2 := h.free hfc hl hpf
  have sk2 := hp.stk.free hi hl hpf
  have e2 : ∀ a, OutHeap a → imgM M2 a = imgM M a := fun a ho => hpf.frame a (OutHeap.not_alloc hi ho)
  have g : ∀ o, ldv .ld M2 (sp - 80 + o) = ldv .ld M (sp - 80 + o) := fun o =>
    dn_ld hab2 (fun _ => False) (fun a ho _ _ => e2 a ho) fun _ _ h => h
  generalize hw : ldv .ld M (c.pay + 8) = w at sk2
  have r28 : R2 8 = w := by rw [hk2.get 8 (by decide)]; bsimp [r18, hw]
  have hS2 : HeapOwn S := fun a e1 e2 => h2.heap.heap.own a e1 e2
  have k2 : Keeps (2 :: 8 :: 9 :: cClob) R2 R :=
    (hk2.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac
      ((hk1.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac Keeps.refl _ _)))
  have fr2 := hp.fr.next hab2 (fun a ho _ _ => e2 a ho) k2 (by
    rw [hk2.get 2 (by decide)]; bsimp [hk1.get 2 (by decide), hp.fr.r2])
  bsimp []
  cases cs with
  | nil =>
    cases ds with
    | cons _ _ => have := sk2.stk.length; simp at this
    | nil =>
    have hw0 : w = 0#64 := by
      have := (sk2.stk.zero_iff).mpr rfl
      exact BitVec.eq_of_toNat_eq (by simpa using this)
    rw [hw0] at r28
    bc_run hlive hS2 [r28]
    rw [ht]
    exact hk R2 M2 _ ⟨fr2, h2, (g 24).trans hp.w24, (g 32).trans hp.w32, (g 40).trans hp.w40⟩
  | cons c' cs' =>
    cases ds with
    | nil => have := sk2.stk.length; simp at this
    | cons d' ds' =>
    have hp' := sk2.stk.head.p
    have hfc' := sk2.fresh c' List.mem_cons_self
    have hcl' := live_in_heap h2.heap.heap hfc'.live (a := c'.pay)
      ⟨Nat.le_refl _, by have := sk2.stk.head.sz; simp only [Blk.pay, Blk.fin]; omega⟩
    simp only [heapStart, heapEnd] at hcl'
    have r28' : R2 8 = BitVec.ofNat 64 c'.pay := by
      rw [r28, ← hp']; exact BitVec.eq_of_toNat_eq (by simp)
    bc_run hlive hS2 [r28']
    · intro _
      refine ih (d' :: ds') (c'.pay) (t' ++ Dc.outStr [d]) R2 M2 _
        ⟨fr2, h2, (g 24).trans hp.w24, (g 32).trans hp.w32, (g 40).trans hp.w40, r28', hp' ▸ sk2,
          List.cons_ne_nil _ _⟩ ?_
      rw [String.append_assoc, ← outStr_append]; exact ht
    · intro hz; exfalso
      exact hz fun e => by rw [ofNat_eq_zero_iff (by omega)] at e; omega

/-- **`bc_free_num` of the handle in the slot at `o`** (`24`, `32` or `40`)
from inside the frame: the frame kept, its other words kept. -/
theorem dn_free {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {p sp o : Nat}
    {R0 R : Nat → BitVec 64}
    (hfr : DnAt S M0 M R0 R sp) (h : DcAt S M H F L C G (.num p :: hs) st)
    (hsf : StackFrame S sp dnN) (hab : heapEnd + dnN ≤ sp)
    (ho : 24 ≤ o) (ho' : o + 8 ≤ 48) (ho8 : o % 8 = 0)
    (hw : ldv .ld M (sp - 80 + o) = BitVec.ofNat 64 p)
    (h10 : R 10 = BitVec.ofNat 64 (sp - 80 + o)) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', DnAt S M0 M' R0 R' sp → DcAt S M' H' F' L' C' G hs st →
      (∀ o', o' + 8 ≤ 80 → (o' + 8 ≤ o ∨ o + 8 ≤ o') →
        ldv .ld M' (sp - 80 + o') = ldv .ld M (sp - 80 + o')) →
      DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x800048c0#64 R M := by
  have hsf' := hsf; have hab' := hab
  have hNW : dnN = 80 + (176 + rmStack (2 ^ 30)) := rfl
  rw [hNW] at hsf' hab'
  have hsl := hsf'.lo; have hsh := hsf'.hi; have hsa := hsf'.al
  simp only [heapEnd] at hab'
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 80 := by simp only [heapEnd]; omega
  refine bc_free_num_dcK hlive h (hsf'.slot (by omega) (by omega) (by omega)) (by simp only [heapEnd]; omega)
    hw (hsf'.within (m := 80) (n := 32) (by omega) (by decide)) (by simp only [heapEnd]; omega)
    (.inr (by omega)) R h10 hfr.r2 hal fun R' M' H' F' L' C' hk' hd hout _ => ?_
  refine hk R' M' H' F' L' C' (hfr.next hab2 (fun a ho hg hn => hout a ho hg
      (fun h => hn (by simp only [frameIn, dnW] at h ⊢; omega))
      (fun h => hn (by simp only [slotBytes] at h ⊢; omega)))
    ((hk'.mono (ks' := 2 :: 8 :: 9 :: cClob) (by decide)).trans (by keeps_tac Keeps.refl _ _))
    (by rw [hk'.get 2 (by decide)]; exact hfr.r2)) hd fun o' h1 h2 =>
      dn_ld hab2 (fun a => frameIn (sp - 80) 32 a ∨ slotBytes (sp - 80 + o) a)
        (fun a ho hg hn => hout a ho hg (fun h => hn (.inl h)) (fun h => hn (.inr h)))
        fun j hj h => by rcases h with h | h <;> simp only [frameIn, slotBytes] at h <;> omega

/-- **The three frees and the epilogue** (`0x80002b68` to the return). -/
theorem dn_exit {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {pd pv pb sp : Nat}
    {R0 R : Nat → BitVec 64}
    (he : DnEnd S M0 M R0 R sp H F L C G hs st pd pv pb)
    (hsf : StackFrame S sp dnN) (hab : heapEnd + dnN ≤ sp) (h02 : R0 2 = BitVec.ofNat 64 sp)
    (hal0 : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps cClob R' R0 → R' 2 = R0 2 → DcAt S M' H' F' L' C' G hs st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp dnN a → imgM M' a = imgM M0 a) →
      DWO live S Q t (R0 1) R' M') :
    DWO live S Q t 0x80002b68#64 R M := by
  have hsf' := hsf; have hab' := hab
  have hNW : dnN = 80 + (176 + rmStack (2 ^ 30)) := rfl
  rw [hNW] at hsf' hab'
  have hsl := hsf'.lo; have hsh := hsf'.hi; have hsa := hsf'.al
  simp only [heapEnd] at hab'
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hab2 : heapEnd ≤ sp - 80 := by simp only [heapEnd]; omega
  have hS : HeapOwn S := fun a e1 e2 => he.h.heap.heap.own a e1 e2
  bc_run hlive hS [he.fr.r2] at 0x800048c0
  refine dn_free hlive (he.fr.next hab2 (fun _ _ _ _ => rfl) (by keeps_tac Keeps.refl _ _)
    (by bsimp [he.fr.r2])) he.h hsf hab (o := 40) (by omega) (by omega) rfl he.w40 ?a10 ?aal
    fun R1 M1 H1 F1 L1 C1 fr1 h1 g1 => ?_
  case a10 => bsimp []
  case aal => bsimp []
  have hS1 : HeapOwn S := fun a e1 e2 => h1.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS1 [fr1.r2] at 0x800048c0
  refine dn_free hlive (fr1.next hab2 (fun _ _ _ _ => rfl) (by keeps_tac Keeps.refl _ _)
    (by bsimp [fr1.r2])) (h1.perm (List.Perm.swap _ _ _)) hsf hab (o := 32) (by omega) (by omega) rfl
    ((g1 32 (by omega) (by omega)).trans he.w32) ?b10 ?bal fun R2 M2 H2 F2 L2 C2 fr2 h2 g2 => ?_
  case b10 => bsimp []
  case bal => bsimp []
  have hS2 : HeapOwn S := fun a e1 e2 => h2.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS2 [fr2.r2] at 0x800048c0
  refine dn_free hlive (fr2.next hab2 (fun _ _ _ _ => rfl) (by keeps_tac Keeps.refl _ _)
    (by bsimp [fr2.r2])) h2 hsf hab (o := 24) (by omega) (by omega) rfl
    ((g2 24 (by omega) (by omega)).trans ((g1 24 (by omega) (by omega)).trans he.w24)) ?c10 ?cal
    fun R3 M3 H3 F3 L3 C3 fr3 h3 _ => ?_
  case c10 => bsimp []
  case cal => bsimp []
  have hS3 : HeapOwn S := fun a e1 e2 => h3.heap.heap.own a e1 e2
  bsimp []
  bc_run hlive hS3 [fr3.r2, fr3.w56, fr3.w64, fr3.w72]
  all_goals first | exact frame_acc hsf' (by omega) (by omega) | exact hal0 | skip
  have e2 : BitVec.ofNat 64 (sp - 80 + 80) = R0 2 := by rw [h02]; congr 1; omega
  refine hk _ M3 H3 F3 L3 C3 (Keeps.restoreAll (rs := [2, 8, 9])
    ((show Keeps ([2, 8, 9] ++ cClob) _ R3 by keeps_tac Keeps.refl _ _).trans fr3.keep) fun z hz => ?_)
    (by bsimp [e2]) h3 fr3.out
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl <;> bsimp [e2]

/-- **`dc_dump_num (dcvalue, DC_TOSS)`** (`0x80002aa4`): the bytes of the
integer part printed, the handle `dcvalue` released. -/
theorem dc_dump_num_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {xp sp : Nat} {n : Dc.Num}
    (h : DcAt S M H F L C G (.num xp :: hs) st) (hx : (GV.num xp).Den ⟨L, G.strs⟩ (.num n))
    (hwid : n.wid < 2 ^ 20) (hhs : hs.length + 3 ≤ 2 ^ 20) (hmb : MulBase S M)
    (hsf : StackFrame S sp dnN) (hab : heapEnd + dnN ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : R 10 = BitVec.ofNat 64 xp)
    (h11 : R 11 = 0#64) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps cClob R' R → R' 2 = R 2 → DcAt S M' H' F' L' C' G hs st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp dnN a → imgM M' a = imgM M a) →
      DWO live S Q (t ++ Dc.outStr n.dump) (R 1) R' M')
    (hoom : ∀ R' M' sp', OomAt S sp dnN M (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M') :
    DWO live S Q t 0x80002aa4#64 R M := by
  have hsz : decLen n.intPart < 2 ^ 20 := by
    have := decLen_mono (Nat.div_le_self n.mag (10 ^ n.scale))
    simp only [Dc.Num.wid] at hwid
    simp only [Dc.Num.intPart]; omega
  refine dn_pro hlive h (by omega) hsf hab R h2 h10 h11 hal
    fun R1 M1 L1 C1 fr1 r8 h1 hz1 hkp1 m8 m24 m32 m40 => ?_
  refine dn_div hlive fr1 r8 h1 hz1 (hkp1 _ List.mem_cons_self _ hx) hwid hsf hab m8 m24 m32 m40
    (fun R2 M2 H2 F2 L2 C2 pv fr2 _ h2' hv2 w24 w32 w40 => ?_) hoom
  refine dn_i2n hlive fr2 h2' hv2 hsf hab w24 w32 w40 (fun R3 M3 H3 F3 L3 C3 pb hl => ?_) hoom
  refine dn_loop hlive hmb hsz hhs hsf hab (fun R4 M4 H4 F4 L4 C4 pd4 pv4 cells p4 hpr => ?_) hoom
    _ _ _ _ _ _ _ _ _ _ _ _ hl
  exact dn_print hlive (T := t ++ Dc.outStr n.dump) hsf hab
    (fun R5 M5 H5 he => dn_exit hlive he hsf hab h2 hal hk) cells _ p4 t R4 M4 H4 hpr (by rw [dump_eq])

end Dc.Mach
