import Dc.Mach.Bc.KaraPopLast

/-!
# `_bc_rec_mul`'s Karatsuba step: the entry

At `0x80004db0` the step saves `s3` and `s7`–`s11` (`rmSlots2`, completing
`KAt`), computes the half `n = (max la lb + 1) / 2`, points `s9` at
`_bc_Free_list` and reads its head, loads `u`'s digits into `s10`, and tests
`la` against `n`: `KEntry` is the state at either route.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-! ## The half's word arithmetic -/

theorem exw_ofNat {k : Nat} (hk : k < 2 ^ 32) :
    BitVec.extractLsb 31 0 (BitVec.ofNat 64 k) = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb', Nat.mod_eq_of_lt hk]

theorem srliw31_small {k : Nat} (hk : k < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 k) >>> 31) = 0#64 := by
  rw [exw_ofNat (by omega)]
  have h0 : (BitVec.ofNat 32 k) >>> 31 = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega)]
    omega
  rw [h0]
  apply BitVec.eq_of_toNat_eq
  simp

theorem sraiw1_small {k : Nat} (hk : k < 2 ^ 31) :
    BitVec.signExtend 64 (shift_bits_right_arith (BitVec.ofNat 32 k) 1#5)
      = BitVec.ofNat 64 (k / 2) := by
  have h0 : shift_bits_right_arith (BitVec.ofNat 32 k) 1#5 = BitVec.ofNat 32 (k / 2) := by
    apply BitVec.eq_of_toNat_eq
    simp [shift_bits_right_arith, BitVec.toNatInt, BitVec.toNat_sshiftRight,
      BitVec.msb_eq_decide, Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega)]
    rw [ite_eq_right (by omega), Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  rw [h0]
  exact sext32_small (by omega)

theorem sext32_ofNat {k : Nat} (hk : k < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 k := sext32_small hk

/-- The step's half: `(m + 1) / 2` from `addiw`, `srliw`, `addw`, `sraiw`. -/
theorem half_word {k : Nat} (hk : k < 2 ^ 31) :
    BitVec.signExtend 64 (shift_bits_right_arith
      (BitVec.extractLsb 31 0 (BitVec.signExtend 64
        (BitVec.extractLsb 31 0 (BitVec.signExtend 64
            (BitVec.extractLsb 31 0 (BitVec.ofNat 64 k) >>> 31))
          + BitVec.extractLsb 31 0 (BitVec.ofNat 64 k)))) 1#5)
      = BitVec.ofNat 64 (k / 2) := by
  rw [srliw31_small hk, exw_ofNat (show k < 2 ^ 32 by omega),
    show BitVec.extractLsb 31 0 (0#64) = 0#32 from by decide, BitVec.zero_add,
    sext32_ofNat hk, exw_ofNat (show k < 2 ^ 32 by omega)]
  exact sraiw1_small hk

/-- The step at either route of its first length test. -/
structure KEntry (S : Nat → Prop) (M0 M : Mem) (R0 R : Nat → BitVec 64)
    (sp q W n la lb : Nat) (uo vo : NumObj) (F : List Blk) : Prop where
  st : KAt S M0 M R0 R sp q W
  fl : R 25 = BitVec.ofNat 64 bcFreeAddr
  slot : R 9 = BitVec.ofNat 64 q
  half : R 8 = BitVec.ofNat 64 n
  s6 : R 22 = BitVec.ofNat 64 (la + lb)
  s4 : R 20 = BitVec.ofNat 64 la
  s5 : R 21 = BitVec.ofNat 64 lb
  s10 : R 26 = BitVec.ofNat 64 uo.rep.val
  s2 : R 18 = BitVec.ofNat 64 vo.rep.p
  head : R 14 = BitVec.ofNat 64 (deadHead F)
  u : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p

/-- **The half and the first length test at `0x80004dd0`**, both routes of
`max la lb` joined. -/
theorem kara_half {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (ka : KAt S M0 M R0 R sp q W) (hb : BcHeap S M H F L)
    (huL : uo ∈ L) (hN : la + lb < 2 ^ 30) (hla : 20 ≤ la) (hlb : 20 ≤ lb)
    (h15 : R 15 = BitVec.ofNat 64 (max la lb))
    (h0 : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p)
    (h22 : R 22 = BitVec.ofNat 64 (la + lb)) (h20 : R 20 = BitVec.ofNat 64 la)
    (h21 : R 21 = BitVec.ofNat 64 lb) (h18 : R 18 = BitVec.ofNat 64 vo.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 q)
    (hlo : ∀ (R' : Nat → BitVec 64) (M' : Mem),
      KEntry S M0 M' R0 R' sp q W ((max la lb + 1) / 2) la lb uo vo F →
      la < (max la lb + 1) / 2 → M' = M → DW live S Q 0x80005378#64 R' M')
    (hhi : ∀ (R' : Nat → BitVec 64) (M' : Mem),
      KEntry S M0 M' R0 R' sp q W ((max la lb + 1) / 2) la lb uo vo F →
      (max la lb + 1) / 2 ≤ la → M' = M → DW live S Q 0x80004df8#64 R' M') :
    DW live S Q 0x80004dd0#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big; have hab := cx.above
  simp only [heapEnd] at hab
  have h2 := ka.rm.r2
  have hfa : (BitVec.ofNat 64 bcFreeAddr).toNat = bcFreeAddr := by
    simp only [bcFreeAddr, BitVec.toNat_ofNat]
  have hgl : ∀ b ∈ accAddrs 2147601840 8, S b := fun b hbm => by
    have := of_mem_accAddrs hbm
    exact hb.globOwn b (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega)
  have hhd := hb.dead.head
  have hun := hb.nums uo huL
  num_facts hun
  have huv := hun.value
  have hkeep : ∀ (R' : Nat → BitVec 64), Keeps [8, 14, 15, 25, 26] R' R → R' 2 = R 2 →
      KAt S M0 M R0 R' sp q W :=
    fun R' kk h2' => ⟨ka.rm.keeps (kk.mono (by decide)) h2', ka.saved2⟩
  have hm : max la lb + 1 < 2 ^ 31 := by omega
  have hsx := sxw_ofNat hm
  have hhw := half_word hm
  bc_run hlive hS [h2, h0, h15, h20, h21, huv, hhd, hfa, hsx, hhw, toInt_ofNat_small] at 0x80005378 0x80004df8
  all_goals try (exact hgl)
  all_goals try (exact ldOK_bcFree)
  all_goals try (exact frame_acc hsf (by omega) (by omega))
  all_goals try (exact acc_heap hS (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr, bcFreeAddr] at *; omega)
  · intro hlt
    refine hlo _ M ⟨hkeep _ (by keeps_tac Keeps.refl _ _) (by bsimp []), ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, h0⟩ (by omega) rfl
    all_goals bsimp [h9, h22, h20, h21, h18, huv, hhd]
  · intro hge
    refine hhi _ M ⟨hkeep _ (by keeps_tac Keeps.refl _ _) (by bsimp []), ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, h0⟩ (by omega) rfl
    all_goals bsimp [h9, h22, h20, h21, h18, huv, hhd]

/-- The offsets `0x80004db0` spills to. -/
abbrev kSpills : List Nat := [88, 96, 104, 112, 120, 152]

/-- The memory after `0x80004db0`'s six spills. -/
def kSpillMem (M : Mem) (R0 : Nat → BitVec 64) (fr : Nat) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog (writeLog M
    [(fr + 152, 8, R0 19)]) [(fr + 120, 8, R0 23)]) [(fr + 112, 8, R0 24)])
    [(fr + 104, 8, R0 25)]) [(fr + 96, 8, R0 26)]) [(fr + 88, 8, R0 27)]

/-- Bytes off the spilled range are unchanged. -/
theorem kSpillMem_off (M : Mem) (R0 : Nat → BitVec 64) {fr a : Nat}
    (h : a < fr + 88 ∨ fr + 160 ≤ a) : imgM (kSpillMem M R0 fr) a = imgM M a := by
  simp only [kSpillMem]
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]

/-- A word off the spilled range is unchanged. -/
theorem kSpillMem_ldv (M : Mem) (R0 : Nat → BitVec 64) {fr a : Nat}
    (h : a + 8 ≤ fr + 88 ∨ fr + 160 ≤ a) : ldv .ld (kSpillMem M R0 fr) a = ldv .ld M a :=
  ldv_congr .ld fun j hj => kSpillMem_off M R0 (by simp only [widthOfM] at hj; omega)

/-- **The six spills**: `s3` and `s7`–`s11` in their slots. -/
theorem kSpillMem_saved2 (M : Mem) (R0 : Nat → BitVec 64) (fr : Nat) :
    SavedWords (kSpillMem M R0 fr) fr rmSlots2 R0 := by
  have h := ((((((SavedWords.nil M fr R0).store 19 152).store 23 120).store 24 112).store
    25 104).store 26 96).store 27 88
  exact fun p hp => h p (by
    simp only [rmSlots2, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- The prologue's slots survive the spills. -/
theorem kSpillMem_saved {M : Mem} {R0 : Nat → BitVec 64} {fr : Nat}
    (h : SavedWords M fr rmSlots R0) : SavedWords (kSpillMem M R0 fr) fr rmSlots R0 := by
  have hdis : ∀ p ∈ rmSlots, ∀ o ∈ kSpills, p.2 + 8 ≤ o ∨ o + 8 ≤ p.2 := by decide
  intro p hp
  have e1 := hdis p hp 88 (by decide); have e2 := hdis p hp 96 (by decide)
  have e3 := hdis p hp 104 (by decide); have e4 := hdis p hp 112 (by decide)
  have e5 := hdis p hp 120 (by decide); have e6 := hdis p hp 152 (by decide)
  simp only [kSpillMem]
  rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
    ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega)]
  exact h p hp

/-- **The step's entry at `0x80004db0`**: `s3` and `s7`–`s11` spilled
(completing `KAt`), then `max la lb` and the half. -/
theorem kara_entry {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M0 M : Mem} {R0 R : Nat → BitVec 64} {sp q W la lb : Nat} {L : List NumObj}
    {uo vo : NumObj} {H : Heap} {F : List Blk}
    (cx : RmCtx S R0 sp q W) (st : RmAt S M0 M R0 R sp q W) (kp : RmKept R R0)
    (hb : BcHeap S M H F L) (huL : uo ∈ L) (hN : la + lb < 2 ^ 30)
    (hla : 20 ≤ la) (hlb : 20 ≤ lb)
    (h0 : ldv .ld M (sp - 192) = BitVec.ofNat 64 uo.rep.p)
    (h22 : R 22 = BitVec.ofNat 64 (la + lb)) (h20 : R 20 = BitVec.ofNat 64 la)
    (h21 : R 21 = BitVec.ofNat 64 lb) (h18 : R 18 = BitVec.ofNat 64 vo.rep.p)
    (h9 : R 9 = BitVec.ofNat 64 q)
    (hlo : ∀ (R' : Nat → BitVec 64) (M' : Mem),
      KEntry S M0 M' R0 R' sp q W ((max la lb + 1) / 2) la lb uo vo F →
      la < (max la lb + 1) / 2 → BcHeap S M' H F L → M' = kSpillMem M R0 (sp - 192) →
      DW live S Q 0x80005378#64 R' M')
    (hhi : ∀ (R' : Nat → BitVec 64) (M' : Mem),
      KEntry S M0 M' R0 R' sp q W ((max la lb + 1) / 2) la lb uo vo F →
      (max la lb + 1) / 2 ≤ la → BcHeap S M' H F L → M' = kSpillMem M R0 (sp - 192) →
      DW live S Q 0x80004df8#64 R' M') :
    DW live S Q 0x80004db0#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hS : HeapOwn S := fun a h1 h2 => hb.heap.own a h1 h2
  have hsf := cx.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hW := cx.big; have hab := cx.above
  simp only [heapEnd] at hab
  have h2 := st.r2
  have hk19 := kp.k19; have hk23 := kp.k23; have hk24 := kp.k24
  have hk25 := kp.k25; have hk26 := kp.k26; have hk27 := kp.k27
  have hdis : ∀ p ∈ rmSlots, ∀ o ∈ kSpills, p.2 + 8 ≤ o ∨ o + 8 ≤ p.2 := by decide
  have half : ∀ (R' : Nat → BitVec 64) (M' : Mem), KAt S M0 M' R0 R sp q W → Keeps [15] R' R →
      BcHeap S M' H F L → ldv .ld M' (sp - 192) = BitVec.ofNat 64 uo.rep.p →
      R' 15 = BitVec.ofNat 64 (max la lb) → M' = kSpillMem M R0 (sp - 192) →
      DW live S Q 0x80004dd0#64 R' M' := by
    intro R' M' ka0 kk hb' h0' h15 hM
    have ka : KAt S M0 M' R0 R' sp q W :=
      ⟨ka0.rm.keeps (kk.mono (by decide)) (kk.get 2 (by decide)), ka0.saved2⟩
    exact kara_half hlive cx ka hb' huL hN hla hlb h15 h0'
      ((kk.get 22 (by decide)).trans h22) ((kk.get 20 (by decide)).trans h20)
      ((kk.get 21 (by decide)).trans h21) ((kk.get 18 (by decide)).trans h18)
      ((kk.get 9 (by decide)).trans h9)
      (fun R'' M'' ke hlt he => hlo R'' M'' (he ▸ ke) hlt (he ▸ hb') (he.trans hM))
      (fun R'' M'' ke hge he => hhi R'' M'' (he ▸ ke) hge (he ▸ hb') (he.trans hM))
  have hbS : BcHeap S (kSpillMem M R0 (sp - 192)) H F L :=
    hb.out_frame (P := frameIn sp W) (fun a hp => kSpillMem_off M R0 (by
        rcases Nat.lt_or_ge a (sp - W) with h | h
        · omega
        · have := Nat.not_lt.mp fun hlt => hp ⟨h, hlt⟩; omega))
      fun a hp => by
        have hp1 := hp.1; have hp2 := hp.2
        simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega
  have h0S : ldv .ld (kSpillMem M R0 (sp - 192)) (sp - 192) = BitVec.ofNat 64 uo.rep.p :=
    (kSpillMem_ldv M R0 (by omega)).trans h0
  have katS : KAt S M0 (kSpillMem M R0 (sp - 192)) R0 R sp q W :=
    ⟨⟨st.r2, kSpillMem_saved st.saved, st.regs, fun a ha h1 h2 =>
      (kSpillMem_off M R0 (by
        rcases Nat.lt_or_ge a (sp - W) with h | h
        · omega
        · have := Nat.not_lt.mp fun hlt => h2 ⟨h, hlt⟩; omega)).trans (st.out a ha h1 h2)⟩,
      kSpillMem_saved2 M R0 (sp - 192)⟩
  bc_run hlive hS [h2, h20, h21, hk19, hk23, hk24, hk25, hk26, hk27] at 0x80005434 0x80004dd0
  all_goals try (exact frame_acc hsf (by omega) (by omega))
  all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr] at *; omega)
  all_goals (try (intro hc; simp (disch := omega) only [toInt_ofNat_small] at hc))
  all_goals (try (bc_run hlive hS [h21] at 0x80004dd0))
  all_goals refine half _ _ katS ?_ hbS h0S ?_ rfl
  all_goals try (keeps_tac Keeps.refl _ _)
  all_goals (bsimp [h20, h21]; congr 1; omega)

end Dc.Mach
