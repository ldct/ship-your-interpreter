import Dc.Mach.Bc.KaraPopSites

/-!
# `_bc_rec_mul`'s last two struct sources

The two views of `v`'s low half are the step's last, so their dispatches
differ from the four regular copies (`KaraPopSites.lean`): neither hands on
the new chain head, the `lb ≥ n` copy branches the other way out of
`malloc`, and the `lb < n` copy also carries `_zero_`'s struct pointer in
`a7`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Dc.BcModel

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

/-- **The struct of the last view at `0x80005400`** (`lb ≥ n`): the chain's
head, or `malloc(40)`; the fresh route rejoins the site with `bnez`. -/
theorem ksplit_800053f4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj}
    (hb : BcHeap S Mt H F L) (hh : R 20 = BitVec.ofNat 64 (deadHead F))
    (h25 : R 25 = BitVec.ofNat 64 bcFreeAddr)
    (hoom : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [1, 10, 12, 13, 14, 15, 20] R' R →
      (∀ a, ¬ AllocByte H a → imgM M' a = imgM Mt a) → DW live S Q 0x80002bcc#64 R' M')
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem) (H' : Heap) (F' : List Blk) (sb : Blk),
      Keeps [1, 10, 12, 13, 14, 15, 20] R' R → ViewStruct S Mt M' H H' F F' sb L →
      R' 20 = BitVec.ofNat 64 sb.pay → DW live S Q 0x80005400#64 R' M') :
    DW live S Q 0x800053f4#64 R Mt := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := hb.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hfa : (BitVec.ofNat 64 bcFreeAddr).toNat = bcFreeAddr := by
    simp only [bcFreeAddr, BitVec.toNat_ofNat]
  have hgl : ∀ b ∈ accAddrs 2147601840 8, S b := fun b hbm => by
    have := of_mem_accAddrs hbm
    exact hb.globOwn b (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega)
  rcases F with _ | ⟨sb, F'⟩
  · simp only [deadHead] at hh
    bc_run hlive hS [hh, h25, hfa] at 0x800055a0
    bc_run hlive hS [] at 0x8000096c
    refine malloc_spec hlive hi (n := 40) (by decide) _ (by bsimp []) (by bsimp []) ?_
    intro R1 Mt1 H1 hk1 hpost
    bsimp []
    have hkk : Keeps [1, 10, 12, 13, 14, 15, 20] R1 R :=
      (Keeps.mono hk1 (by decide)).trans (by keeps_tac Keeps.refl _ _)
    cases hres : hpost.res with
    | null e1 e2 e3 =>
      iterate 2 all_goals (try bc_run hlive hS [e1] at 0x80002bcc)
      exact hoom _ _ (by keeps_tac hkk) hpost.frame
    | block sb e1 e2 e3 e4 e5 =>
      have hsb1 : sb ∈ H1.live := by rw [e3]; exact List.mem_cons_self
      have fbb := hpost.inv.blk (List.mem_append_right _ hsb1)
      have hsl := fbb.lo; have hsf2 := fbb.fin; have hst := fbb.top
      simp only [heapStart] at hsl
      simp only [heapEnd] at hst
      have hbp : sb.pay = sb.h + 16 := rfl
      have hbf : sb.fin = sb.h + 16 + sb.sz := rfl
      have hsz : 40 ≤ sb.sz := e2
      have hsp64 : sb.pay < 2 ^ 64 := by omega
      have hsppos : 0 < sb.pay := by omega
      bc_run hlive hS [e1, hfa] at 0x800055b0 0x80005400
      · intro _
        refine hnext _ _ H1 [] sb ?_ (ViewStruct.fresh hb rfl hpost.inv hpost.frame e3 hsz e5) ?_
        · keeps_tac hkk
        · bsimp [e1]
      · intro hc; exfalso; bv_nat at hc
        simp only [Nat.mod_eq_of_lt hsp64] at hc; omega
  · have hpn := hb.popNext rfl
    simp only [deadHead] at hh
    have hsbl := (hb.deadLive sb List.mem_cons_self).1
    have fbb := hi.blk (List.mem_append_right _ hsbl)
    have hsl := fbb.lo; have hsf2 := fbb.fin; have hst := fbb.top; have hal := fbb.al
    simp only [heapStart] at hsl
    simp only [heapEnd] at hst
    have hbp : sb.pay = sb.h + 16 := rfl
    have hbf : sb.fin = sb.h + 16 + sb.sz := rfl
    have hsz : 40 ≤ sb.sz := (hb.deadLive sb List.mem_cons_self).2
    have hsp64 : sb.pay < 2 ^ 64 := by omega
    have hsppos : 0 < sb.pay := by omega
    have hpa : (BitVec.ofNat 64 (sb.pay + 16)).toNat = sb.pay + 16 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    bc_run hlive hS [hh, h25, hpn, hfa] at 0x800055a0 0x80005400
    · intro hc; exfalso; bv_nat at hc
      simp only [Nat.mod_eq_of_lt hsp64] at hc; omega
    · intro _
      bc_run hlive hS [hh, h25, hpn, hfa] at 0x80005400
      all_goals try (exact hgl)
      all_goals try (exact ldOK_bcFree)
      all_goals try (exact stOK_bcFree)
      all_goals try (exact acc_heap hS (by omega) (by omega))
      all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr, bcFreeAddr] at *; omega)
      refine hnext _ _ H F' sb ?_
        (ViewStruct.popAt hb rfl _ (by first | rfl | (rw [hpa]; exact hpn))) ?_
      · keeps_tac Keeps.refl _ _
      · bsimp [hh]

/-- **The struct of the last view at `0x80004e94`** (`lb < n`, the whole of
`v`): the chain's head, or `malloc(40)`; both routes carry `_zero_`'s struct
pointer into `a7`. -/
theorem ksplit_80004e80 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {Mt : Mem} {R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj} {zp : Nat}
    (hb : BcHeap S Mt H F L) (hh : R 15 = BitVec.ofNat 64 (deadHead F))
    (h25 : R 25 = BitVec.ofNat 64 bcFreeAddr) (h18 : R 18 = BitVec.ofNat 64 zeroAddr)
    (h27 : R 27 = BitVec.ofNat 64 zp) (hzp : ldv .ld Mt zeroAddr = BitVec.ofNat 64 zp)
    (hzo : ∀ a, constBytes a → S a)
    (hoom : ∀ (R' : Nat → BitVec 64) (M' : Mem), Keeps [1, 10, 12, 13, 14, 15, 17, 20] R' R →
      (∀ a, ¬ AllocByte H a → imgM M' a = imgM Mt a) → DW live S Q 0x80002bcc#64 R' M')
    (hnext : ∀ (R' : Nat → BitVec 64) (M' : Mem) (H' : Heap) (F' : List Blk) (sb : Blk),
      Keeps [1, 10, 12, 13, 14, 15, 17, 20] R' R → ViewStruct S Mt M' H H' F F' sb L →
      R' 20 = BitVec.ofNat 64 sb.pay → R' 17 = BitVec.ofNat 64 zp →
      DW live S Q 0x80004e94#64 R' M') :
    DW live S Q 0x80004e80#64 R Mt := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hi := hb.heap
  have hS : HeapOwn S := fun a h1 h2 => hi.own a h1 h2
  have hfa : (BitVec.ofNat 64 bcFreeAddr).toNat = bcFreeAddr := by
    simp only [bcFreeAddr, BitVec.toNat_ofNat]
  have hza : (BitVec.ofNat 64 zeroAddr).toNat = zeroAddr := by
    simp only [zeroAddr, BitVec.toNat_ofNat]
  have hgl : ∀ b ∈ accAddrs 2147601840 8, S b := fun b hbm => by
    have := of_mem_accAddrs hbm
    exact hb.globOwn b (by simp only [bcFreeAddr]; omega) (by simp only [bcFreeAddr]; omega)
  have hcst : ∀ b ∈ accAddrs 2147601864 8, S b := fun b hb' => by
    have := of_mem_accAddrs hb'
    exact hzo b (by simp only [constBytes, twoAddr, zeroAddr] at *; omega)
  rcases F with _ | ⟨sb, F'⟩
  · simp only [deadHead] at hh
    bc_run hlive hS [hh, h25, hfa] at 0x800055ec
    bc_run hlive hS [] at 0x8000096c
    refine malloc_spec hlive hi (n := 40) (by decide) _ (by bsimp []) (by bsimp []) ?_
    intro R1 Mt1 H1 hk1 hpost
    bsimp []
    have hkk : Keeps [1, 10, 12, 13, 14, 15, 17, 20] R1 R :=
      (Keeps.mono hk1 (by decide)).trans (by keeps_tac Keeps.refl _ _)
    have h18' : R1 18 = BitVec.ofNat 64 zeroAddr := by rw [hkk.get 18 (by decide)]; exact h18
    have hzp' : ldv .ld Mt1 zeroAddr = BitVec.ofNat 64 zp := by
      rw [ldv_congr .ld fun j hj => hpost.frame _ fun ha => not_zeroAddr_of_alloc hi ha
        (by simp only [zeroAddr, widthOfM] at hj ⊢; omega)]
      exact hzp
    cases hres : hpost.res with
    | null e1 e2 e3 =>
      iterate 2 all_goals (try bc_run hlive hS [e1] at 0x80002bcc)
      exact hoom _ _ (by keeps_tac hkk) hpost.frame
    | block sb e1 e2 e3 e4 e5 =>
      have hsb1 : sb ∈ H1.live := by rw [e3]; exact List.mem_cons_self
      have fbb := hpost.inv.blk (List.mem_append_right _ hsb1)
      have hsl := fbb.lo; have hsf2 := fbb.fin; have hst := fbb.top
      simp only [heapStart] at hsl
      simp only [heapEnd] at hst
      have hbp : sb.pay = sb.h + 16 := rfl
      have hbf : sb.fin = sb.h + 16 + sb.sz := rfl
      have hsz : 40 ≤ sb.sz := e2
      have hsp64 : sb.pay < 2 ^ 64 := by omega
      have hsppos : 0 < sb.pay := by omega
      bc_run hlive hS [e1, h18', hzp', hfa, hza] at 0x800055b0 0x80004e94
      · intro hc; exfalso; bv_nat at hc
        simp only [Nat.mod_eq_of_lt hsp64] at hc; omega
      · intro _
        bc_run hlive hS [e1, h18', hzp', hfa, hza] at 0x80004e94
        all_goals try (exact hcst)
        all_goals try (exact ldOK_zero)
        all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr, zeroAddr] at *; omega)
        refine hnext _ _ H1 [] sb ?_ (ViewStruct.fresh hb rfl hpost.inv hpost.frame e3 hsz e5)
          ?_ ?_
        · keeps_tac hkk
        · bsimp [e1]
        · bsimp [hzp']
  · have hpn := hb.popNext rfl
    simp only [deadHead] at hh
    have hsbl := (hb.deadLive sb List.mem_cons_self).1
    have fbb := hi.blk (List.mem_append_right _ hsbl)
    have hsl := fbb.lo; have hsf2 := fbb.fin; have hst := fbb.top; have hal := fbb.al
    simp only [heapStart] at hsl
    simp only [heapEnd] at hst
    have hbp : sb.pay = sb.h + 16 := rfl
    have hbf : sb.fin = sb.h + 16 + sb.sz := rfl
    have hsz : 40 ≤ sb.sz := (hb.deadLive sb List.mem_cons_self).2
    have hsp64 : sb.pay < 2 ^ 64 := by omega
    have hsppos : 0 < sb.pay := by omega
    have hpa : (BitVec.ofNat 64 (sb.pay + 16)).toNat = sb.pay + 16 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    bc_run hlive hS [hh, h25, h27, hpn, hfa] at 0x800055ec 0x80004e94
    · intro hc; exfalso; bv_nat at hc
      simp only [Nat.mod_eq_of_lt hsp64] at hc; omega
    · intro _
      bc_run hlive hS [hh, h25, h27, hpn, hfa] at 0x80004e94
      all_goals try (exact hgl)
      all_goals try (exact ldOK_bcFree)
      all_goals try (exact stOK_bcFree)
      all_goals try (exact acc_heap hS (by omega) (by omega))
      all_goals try (simp only [LdOK, StOK, StOKb, tohostAddr, bcFreeAddr] at *; omega)
      refine hnext _ _ H F' sb ?_
        (ViewStruct.popAt hb rfl _ (by first | rfl | (rw [hpa]; exact hpn))) ?_ ?_
      · keeps_tac Keeps.refl _ _
      · bsimp [hh]
      · bsimp [h27]

end Dc.Mach
