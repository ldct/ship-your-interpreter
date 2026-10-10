import Dc.Mach.DcOutStr

/-!
# `dc_print` (M9)

    dc_print (value, obase, newline, discard):
      if (value.dc_type == DC_NUMBER) dc_out_num (value.v.number, obase, discard);
      else if (value.dc_type == DC_STRING) dc_out_str (value.v.string, discard);
      else dc_garbage ("in dc_print", -1);
      if (newline == DC_WITHNL) putchar ('\n');
      fflush (stdout);

- `pr_tail`, `pr_nl`: the `fflush` tail, with or without the newline.
- `dc_print_spec`: the console extended by `Val.out 70 ob v` (and a newline),
  the handle kept or released.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- `dc_print`'s tail (`0x80002044`): `ra` reloaded, `fflush (stdout)` (a
no-op returning `0`) as the tail call. -/
theorem pr_tail {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} {ra : BitVec 64}
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (f40 : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 10] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp → DWO live S Q t ra R' M) :
    DWO live S Q t 0x80002044#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hro : ∀ b ∈ accAddrs 2147516936 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  bc_run hlive hlive [h2, f40, stdout_word]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (by keeps_tac Keeps.refl _ _) (by bsimp []) ?_
  bsimp []; congr 1; omega

/-- `dc_print`'s newline (`0x80002074`): `putchar ('\n')`, then the tail. -/
theorem pr_nl {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} {ra : BitVec 64}
    (hfd : FdAt S M stdoutFile 1)
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (f40 : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 10, 14, 15] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      DWO live S Q (t ++ Dc.outStr [10]) ra R' M) :
    DWO live S Q t 0x80002074#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [heapEnd] at hab
  have htx : tohostAddr = 0x8001ad00 := rfl
  bc_run hlive hlive [] at 0x80000628
  refine putchar_spec hlive hfd _ (by bsimp []) fun R1 hk1 e10 => ?_
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 48) := by rw [hk1.get 2 (by decide)]; bsimp [h2]
  have hro : ∀ b ∈ accAddrs 2147516936 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  have p10 : putcStr (lo8 10#64) = Dc.outStr [10] := by
    rw [show (10#64 : BitVec 64) = BitVec.ofNat 64 10 from rfl, putc_ofNat (by decide)]; rfl
  bsimp []
  rw [p10]
  bc_run hlive hlive [q2, f40, stdout_word]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ ?_ (by bsimp []) ?_
  · exact by keeps_tac ((hk1.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))
  · bsimp []; congr 1; omega

theorem outStr_append (a b : List Nat) : Dc.outStr (a ++ b) = Dc.outStr a ++ Dc.outStr b := by
  simp [Dc.outStr, String.ofList_append]

/-- `dc_print`'s stack: its 48 bytes and `dc_out_num`'s. -/
abbrev prN : Nat := 48 + onN

/-- The newline `dc_print` appends. -/
def nlBytes (nl : Bool) : List Nat := if nl then [10] else []

/-- `dc_print` after its callee (`0x80002038`, the string route): the saved
`newline` reloaded, the newline and the `fflush` tail. -/
theorem pr_after_str {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} {ra : BitVec 64} {nl : Bool}
    (hfd : FdAt S M stdoutFile 1)
    (hsf : StackFrame S sp 48) (hab : heapEnd + 48 ≤ sp) (R : Nat → BitVec 64)
    (h2 : R 2 = BitVec.ofNat 64 (sp - 48)) (f8 : ldv .ld M (sp - 48 + 8) = boolWord nl)
    (f40 : ldv .ld M (sp - 48 + 40) = ra) (hal : ra.toNat % 4 = 0)
    (hk : ∀ R', Keeps [1, 2, 10, 13, 14, 15] R' R → R' 1 = ra → R' 2 = BitVec.ofNat 64 sp →
      DWO live S Q (t ++ Dc.outStr (nlBytes nl)) ra R' M) :
    DWO live S Q t 0x80002038#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  cases nl
  · have f8' : ldv .ld M (sp - 48 + 8) = 0#64 := f8
    bc_run hlive hlive [h2, f8']
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine pr_tail hlive hsf hab _ ?q f40 hal fun R' hk' e1 e2 => ?_
    case q => bsimp [h2]
    have e : t ++ Dc.outStr (nlBytes false) = t := by
      rw [show nlBytes false = [] from rfl, show Dc.outStr [] = "" from rfl, String.append_empty]
    rw [← e]
    exact hk R' (by keeps_tac ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) e1 e2
  · have f8' : ldv .ld M (sp - 48 + 8) = 1#64 := f8
    bc_run hlive hlive [h2, f8']
    all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
    refine pr_nl hlive hfd hsf hab _ ?q f40 hal fun R' hk' e1 e2 => ?_
    case q => bsimp [h2]
    exact hk R' (by keeps_tac ((hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _))) e1 e2

/-- `dc_print` on a number (from `0x8000200c`, `a0` the tag `1`). -/
theorem pr_num {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {x : NumObj}
    {ob sp : Nat} {nl keep : Bool}
    (h : DcAt S M H F L C G hs st) (hd : keep = false → hs.head? = some (.num x.rep.p))
    (hx : x ∈ L) (hhs : hs.length ≤ 2 ^ 20)
    (hsz : x.rep.len + x.rep.scale < 2 ^ 20) (hmb : MulBase S M) (hob2 : 2 ≤ ob) (hob : ob < 2 ^ 31)
    (herr : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a)
    (hsf : StackFrame S sp prN) (hab : heapEnd + prN ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : (R 10).toNat % 2 ^ 32 = 1)
    (h11 : R 11 = BitVec.ofNat 64 x.rep.p) (h12 : R 12 = BitVec.ofNat 64 ob)
    (h13 : R 13 = boolWord nl) (h14 : R 14 = boolWord keep) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C', Keeps cClob R' R → R' 2 = R 2 →
      DcAt S M' H' F' L' C' G (if keep then hs else hs.tail) st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp prN a → imgM M' a = imgM M a) →
      DWO live S Q (t ++ Dc.outStr (Dc.Num.out 70 ob x.rep.num ++ nlBytes nl)) (R 1) R' M')
    (hoom : ∀ t' R' M' sp', OomAt S sp prN M ocG sp' R' M' → DWO live S Q t' 0x80001e74#64 R' M') :
    DWO live S Q t 0x8000200c#64 R M := by
  have hNW : prN = 48 + (32 + (176 + 512 + rmStack (2 ^ 30) + 48)) := rfl
  have hsf' := hsf
  have hab0 := hab
  rw [hNW] at hsf' hab0
  have hsl := hsf'.lo; have hsh := hsf'.hi; have hsa := hsf'.al
  simp only [heapEnd] at hab0
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have ht := sxw_lo32 h10 (by decide)
  bc_run hlive hS [h2, ht, h11, h12, h13, h14, word_sub48 (show 48 ≤ sp by omega)] at 0x80002a4c
  all_goals first | exact frame_acc hsf' (by omega) (by omega) | skip
  bc_run hlive hS [h2, ht, h11, h12, h13, h14, word_sub48 (show 48 ≤ sp by omega)] at 0x80002a4c
  all_goals first | exact frame_acc hsf' (by omega) (by omega) | skip
  have hNW : prN = 48 + (32 + (176 + 512 + rmStack (2 ^ 30) + 48)) := rfl
  have hON : onN = 32 + (176 + 512 + rmStack (2 ^ 30) + 48) := rfl
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have hM1 : MemOnly (frameIn sp 48) (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 nl.toNat)]) M := fun a ha => by
    simp only [frameIn] at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hM1 fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have hmb1 := hmb.transport (M' := writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 nl.toNat)]) fun a e1 e2 => hM1 a fun hp => by
    simp only [frameIn, mulBaseAddr] at e1 e2 hp; simp only [heapEnd] at hab2; omega
  have m8 : ldv .ld (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 nl.toNat)]) (sp - 48 + 8) = boolWord nl := ldv_store_hit _ _ _
  have m40 : ldv .ld (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 nl.toNat)]) (sp - 48 + 40) = R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 nl.toNat)] = M1 at hM1 h1 hmb1 m8 m40 ⊢
  refine dc_out_num_spec hlive (keep := keep) h1 hd hx hhs hsz hmb1 hob2 hob herr
    (hsf.within (m := 48) (n := onN) (by omega) (by decide)) (by simp only [heapEnd]; omega) _
    (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
    (fun R' M' H' F' L' C' hk' e2 hD hfr => ?_)
    fun t' R' M' sp' ho => hoom t' R' M' sp' ⟨by have := ho.lo; omega, by have := ho.hi; omega, ho.r2, fun a e1 e2 e3 e4 =>
      (ho.out a e1 e2 (fun hf => e3 (by simp only [frameIn] at hf ⊢; omega)) e4).trans
        (hM1 a fun hf => e3 (by simp only [frameIn] at hf ⊢; omega))⟩
  have kf : ∀ o, 8 ≤ o → o < 48 → imgM M' (sp - 48 + o) = imgM M1 (sp - 48 + o) := fun o h8 h48 =>
    hfr _ (above_sp hab2 (by omega)).1 (above_sp hab2 (by omega)).2.1
      (by simp only [ocG, stdoutFile, lineMaxAddr, errnoAddr, outColAddr]; simp only [heapEnd] at hab2; omega)
      ((above_sp hab2 (by omega)).2.2 _)
  have f8 : ldv .ld M' (sp - 48 + 8) = boolWord nl := (ldv_congr .ld fun j hj => by
    have := kf (8 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m8
  have f40 : ldv .ld M' (sp - 48 + 40) = R 1 := (ldv_congr .ld fun j hj => by
    have := kf (40 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m40
  have q2 : R' 2 = BitVec.ofNat 64 (sp - 48) := by rw [e2]; bsimp []
  have hfr' : ∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp prN a → imgM M' a = imgM M a :=
    fun a e1 e2 e3 e4 => (hfr a e1 e2 e3 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))).trans
      (hM1 a fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))
  have hsf48 : StackFrame S sp 48 := by simpa using hsf.within (m := 0) (n := 48) (by omega) (by decide)
  clear kf hM1 m8 m40 h1 hmb1
  bsimp []
  cases nl
  · have f8' : ldv .ld M' (sp - 48 + 8) = 0#64 := f8
    bc_run hlive hlive [q2, f8']
    all_goals first | exact frame_acc hsf48 (by omega) (by omega) | skip
    refine pr_tail hlive hsf48 (by simp only [heapEnd]; omega) _ ?q f40 hal
      fun R'' hk'' e1 e2' => ?_
    case q => bsimp [q2]
    rw [show Dc.Num.out 70 ob x.rep.num = Dc.Num.out 70 ob x.rep.num ++ nlBytes false from
      (List.append_nil _).symm]
    refine hk R'' M' H' F' L' C' ?_ (by rw [e2', h2]) hD hfr'
    refine Keeps.restoreAll (rs := [2]) ((hk''.mono (ks' := [2] ++ cClob) (by decide)).trans
      (by keeps_tac ((hk'.mono (ks' := [2] ++ cClob) (by decide)).trans
        (show Keeps ([2] ++ cClob) _ R by keeps_tac Keeps.refl _ _)))) fun z hz => ?_
    simp only [List.mem_singleton] at hz; subst hz; rw [e2', h2]
  · have f8' : ldv .ld M' (sp - 48 + 8) = 1#64 := f8
    bc_run hlive hlive [q2, f8']
    all_goals first | exact frame_acc hsf48 (by omega) (by omega) | skip
    refine pr_nl hlive ⟨fun i hi => hD.glob _ (by simp only [DcGlob, stdoutFile, dc_addrs]; omega),
      hD.view.outFd, by decide, by decide, by decide⟩ hsf48 (by simp only [heapEnd]; omega) _
      ?q1 f40 hal fun R'' hk'' e1 e2' => ?_
    case q1 => bsimp [q2]
    rw [String.append_assoc, ← outStr_append]
    refine hk R'' M' H' F' L' C' ?_ (by rw [e2', h2]) hD hfr'
    refine Keeps.restoreAll (rs := [2]) ((hk''.mono (ks' := [2] ++ cClob) (by decide)).trans
      (by keeps_tac ((hk'.mono (ks' := [2] ++ cClob) (by decide)).trans
        (show Keeps ([2] ++ cClob) _ R by keeps_tac Keeps.refl _ _)))) fun z hz => ?_
    simp only [List.mem_singleton] at hz; subst hz; rw [e2', h2]

/-- `dc_print` on a string (from `0x8000200c`, `a0` the tag `2`). -/
theorem pr_str {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {o : StrObj}
    {sp : Nat} {nl keep : Bool}
    (h : DcAt S M H F L C G hs st) (hd : keep = false → hs.head? = some (.str o.hb.pay))
    (ho : o ∈ G.strs)
    (hsf : StackFrame S sp 112) (hab : heapEnd + 112 ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : (R 10).toNat % 2 ^ 32 = 2)
    (h11 : R 11 = BitVec.ofNat 64 o.hb.pay) (h13 : R 13 = boolWord nl) (h14 : R 14 = boolWord keep)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' G', Keeps cClob R' R → R' 2 = R 2 → SameNodes G G' →
      DcAt S M' H' F L C G' (if keep then hs else hs.tail) st → StkOut sp 112 M' M →
      DWO live S Q (t ++ Dc.outStr (o.s ++ nlBytes nl)) (R 1) R' M') :
    DWO live S Q t 0x8000200c#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hab' := hab
  simp only [heapEnd] at hab'
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a e1 e2 => h.heap.heap.own a e1 e2
  have ht := sxw_lo32 h10 (by decide)
  bc_run hlive hS [h2, ht, h11, h13, h14, word_sub48 (show 48 ≤ sp by omega)] at 0x800039e0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  bc_run hlive hS [h2, ht, h11, h13, h14, word_sub48 (show 48 ≤ sp by omega)] at 0x800039e0
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hab2 : heapEnd ≤ sp - 48 := by simp only [heapEnd]; omega
  have hM1 : MemOnly (frameIn sp 48) (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 nl.toNat)]) M := fun a ha => by
    simp only [frameIn] at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have h1 := h.outWrite hM1 fun a ha =>
    ⟨(above_sp hab2 (by simp only [frameIn] at ha; omega)).1,
      (above_sp hab2 (by simp only [frameIn] at ha; omega)).2.1⟩
  have m8 : ldv .ld (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 nl.toNat)]) (sp - 48 + 8) = boolWord nl := ldv_store_hit _ _ _
  have m40 : ldv .ld (writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 nl.toNat)]) (sp - 48 + 40) = R 1 := by
    rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]
  generalize writeLog (writeLog M [(sp - 48 + 40, 8, R 1)])
      [(sp - 48 + 8, 8, BitVec.ofNat 64 nl.toNat)] = M1 at hM1 h1 m8 m40 ⊢
  refine dc_out_str_spec hlive (keep := keep) h1 hd ho
    (hsf.within (m := 48) (n := 64) (by omega) (by decide)) (by simp only [heapEnd]; omega) _
    (by bsimp []) (by bsimp []) (by bsimp []) (by bsimp [])
    (fun R' M' H' G' hk' e2 hsn hD hstk => ?_)
  have kf : ∀ o, 8 ≤ o → o < 48 → imgM M' (sp - 48 + o) = imgM M1 (sp - 48 + o) := fun o h8 h48 =>
    hstk _ (above_sp hab2 (by omega)).1 (above_sp hab2 (by omega)).2.1
      (by simp only [frameIn]; omega)
  have f8 : ldv .ld M' (sp - 48 + 8) = boolWord nl := (ldv_congr .ld fun j hj => by
    have := kf (8 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m8
  have f40 : ldv .ld M' (sp - 48 + 40) = R 1 := (ldv_congr .ld fun j hj => by
    have := kf (40 + j) (by omega) (by have : widthOfM .ld = 8 := rfl; omega); simpa [Nat.add_assoc] using this).trans m40
  have q2 : R' 2 = BitVec.ofNat 64 (sp - 48) := by rw [e2]; bsimp []
  have hfr' : StkOut sp 112 M' M :=
    fun a e1 e2 e4 => (hstk a e1 e2 (fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))).trans
      (hM1 a fun hf => e4 (by simp only [frameIn] at hf ⊢; omega))
  have hsf48 : StackFrame S sp 48 := by simpa using hsf.within (m := 0) (n := 48) (by omega) (by decide)
  clear kf hM1 m8 m40 h1
  refine pr_after_str hlive ⟨fun i hi => hD.glob _ (by simp only [DcGlob, stdoutFile, dc_addrs]; omega),
    hD.view.outFd, by decide, by decide, by decide⟩ hsf48 (by simp only [heapEnd]; omega) _
    q2 f8 f40 hal fun R'' hk'' e1 e2' => ?_
  rw [String.append_assoc, ← outStr_append]
  refine hk R'' M' H' G' ?_ (by rw [e2', h2]) hsn hD hfr'
  refine Keeps.restoreAll (rs := [2]) ((hk''.mono (ks' := [2] ++ cClob) (by decide)).trans
    (by keeps_tac ((hk'.mono (ks' := [2] ++ cClob) (by decide)).trans
      (show Keeps ([2] ++ cClob) _ R by keeps_tac Keeps.refl _ _)))) fun z hz => ?_
  simp only [List.mem_singleton] at hz; subst hz; rw [e2', h2]

/-- **`dc_print (value, obase, newline, discard)`** at `0x8000200c`: the
console extended by `Val.out 70 obase v` (and a newline when `nl`), the handle
`g` (with `DC_TOSS`, the head of the handles `hs`) released unless `keep`; `fflush` is a no-op. -/
theorem dc_print_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {g : GV} {v : Val}
    {ob sp : Nat} {nl keep : Bool}
    (h : DcAt S M H F L C G hs st) (hd : keep = false → hs.head? = some g)
    (hv : g.Den ⟨L, G.strs⟩ v) (hhs : hs.length ≤ 2 ^ 20)
    (hsz : ∀ x ∈ L, g = .num x.rep.p → x.rep.len + x.rep.scale < 2 ^ 20) (hmb : MulBase S M)
    (hob2 : 2 ≤ ob) (hob : ob < 2 ^ 31)
    (herr : ∀ a, errnoAddr ≤ a → a < errnoAddr + 4 → S a)
    (hsf : StackFrame S sp prN) (hab : heapEnd + prN ≤ sp)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (h10 : (R 10).toNat % 2 ^ 32 = g.tag)
    (h11 : R 11 = BitVec.ofNat 64 g.ptr) (h12 : R 12 = BitVec.ofNat 64 ob)
    (h13 : R 13 = boolWord nl) (h14 : R 14 = boolWord keep) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' H' F' L' C' G', Keeps cClob R' R → R' 2 = R 2 → SameNodes G G' →
      DcAt S M' H' F' L' C' G' (if keep then hs else hs.tail) st →
      (∀ a, OutHeap a → ¬ DcGlob a → ¬ ocG a → ¬ frameIn sp prN a → imgM M' a = imgM M a) →
      DWO live S Q (t ++ Dc.outStr (Dc.Val.out 70 ob v ++ nlBytes nl)) (R 1) R' M')
    (hoom : ∀ t' R' M' sp', OomAt S sp prN M ocG sp' R' M' → DWO live S Q t' 0x80001e74#64 R' M') :
    DWO live S Q t 0x8000200c#64 R M := by
  have hNW : prN = 48 + (32 + (176 + 512 + rmStack (2 ^ 30) + 48)) := rfl
  have hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega
  cases g <;> cases v <;> simp only [GV.Den] at hv
  · obtain ⟨x, hx, rfl, rfl⟩ := hv
    exact pr_num hlive h hd hx hhs (hsz x hx rfl) hmb hob2 hob herr hsf hab R h2 h10 h11 h12 h13 h14 hal
      (fun R' M' H' F' L' C' hk' e2 hD hfr => hk R' M' H' F' L' C' G hk' e2 ⟨rfl, rfl, rfl⟩ hD hfr) hoom
  · obtain ⟨o, ho, rfl, rfl⟩ := hv
    have hsf' := hsf
    rw [hNW] at hsf' hab
    have hsf112 : StackFrame S sp 112 := by
      simpa using hsf'.within (m := 0) (n := 112) (by omega) (by decide)
    exact pr_str hlive h hd ho hsf112 (by omega) R h2 h10 h11 h13 h14 hal fun R' M' H' G' hk' e2 hsn hD hstk =>
        hk R' M' H' F L C G' hk' e2 hsn hD fun a e1 e2 _ e4 =>
          hstk a e1 e2 fun hf => e4 (by simp only [frameIn] at hf ⊢; rw [hNW]; omega)

end Dc.Mach
