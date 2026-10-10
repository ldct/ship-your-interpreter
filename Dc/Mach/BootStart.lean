import Dc.Mach.BootMain

/-!
# `_start` after `gp`, and the exit (M11)

```
80000008 auipc sp,0x8000 ; 8000000c addi sp,sp,-8        (sp = __stack_top)
80000010 auipc t0 ; 80000014 addi t0 = free_list ; 80000018 auipc t1 ; 8000001c addi t1 = __bss_end
80000020 bgeu t0,t1,80000030 ; 80000024 sd zero,0(t0) ; 80000028 addi t0,t0,8 ; 8000002c j 80000020
80000030 li a0,0 ; 80000034 li a1,0 ; 80000038 jal main ; 8000003c j exit
```

`start_spec`: from the loader's memory (`StartPre`: dc's writable bytes owned,
`.data`'s dc words and the script) at `0x80000008`, `sp` set, `.bss` zeroed
(`bss_loop`, a `Filled` of zero doublewords), then `main_spec` to the call of
`dc_evalstr` with `main`'s 8 MiB frame. `start_exit`: `main`'s return at
`0x8000003c` to `_exit`'s store with the exit word of `main`'s status.
`flush_okay_spec`: `stdout`'s `ferror`/`fflush`/`fclose` stubs, status `0`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `__stack_top`. -/
abbrev stackTop : Nat := 0x88000000

/-- The bytes of `.bss`: `free_list` … `__bss_end`. -/
abbrev bssLen : Nat := heapStart - freeListAddr

/-- `.bss`'s length as a literal. -/
theorem bssLen_eq : bssLen = 2184 := rfl

/-- `_start`'s `.bss` loop at `0x80000020` with `t0 = free_list + i`. -/
theorem bss_loop {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hown : ∀ a, freeListAddr ≤ a → a < heapStart → S a)
    (Mt0 : Mem) (R0 : Nat → BitVec 64)
    (hk : ∀ R' Mt', Keeps [5] R' R0 → Filled Mt' Mt0 freeListAddr bssLen (fun _ => 0#8) →
      DW live S Q 0x80000030#64 R' Mt') :
    ∀ k i (R : Nat → BitVec 64) (Mt : Mem), bssLen - i = 8 * k → i ≤ bssLen →
      R 5 = BitVec.ofNat 64 (freeListAddr + i) → R 6 = BitVec.ofNat 64 heapStart →
      Keeps [5] R R0 → Filled Mt Mt0 freeListAddr i (fun _ => 0#8) →
      DW live S Q 0x80000020#64 R Mt := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k with
  | zero =>
    intro i R Mt hn hi h5 h6 hkeep hf
    have hi' : i = bssLen := by omega
    subst hi'
    dx_run hlive
    · intro hc; exact hk R Mt hkeep hf
    · intro hc; exfalso; apply hc; rw [h5, h6]; simp only [bssLen, BitVec.toNat_ofNat, heapStart,
        freeListAddr]; omega
  | succ k ih =>
    intro i R Mt hn hi h5 h6 hkeep hf
    have hi8 : i % 8 = 0 := by simp only [bssLen_eq] at hn; omega
    have hlt : i + 8 ≤ bssLen := by omega
    simp only [bssLen_eq] at hlt hn hi
    apply st_80000020 hlive
    · intro hc; exfalso; rw [h5, h6] at hc
      simp only [BitVec.toNat_ofNat, heapStart, freeListAddr] at hc; omega
    · intro _
      dx_run hlive at 0x80000020
      all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, se12_zero,
        BitVec.add_zero, h5, h6, ofNat_add_ofNat]
      · simp only [BitVec.toNat_ofNat, StOK, freeListAddr]; omega
      · intro b hb
        have hb' := of_mem_accAddrs hb
        simp only [BitVec.toNat_ofNat] at hb'
        exact hown b (by simp only [freeListAddr] at hb' ⊢; omega)
          (by simp only [freeListAddr, heapStart] at hb' ⊢; omega)
      · refine ih (i + 8) _ _ (by simp only [bssLen_eq]; omega) (by simp only [bssLen_eq]; omega)
          ?_ ?_ ?_ ?_
        · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h5, ofNat_add_ofNat,
            Nat.add_assoc]
        · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h6]
        · keeps_tac hkeep
        · exact hf.snocW (by simp only [BitVec.toNat_ofNat, freeListAddr]; omega)

/-- **The loader's memory** at `0x80000008` (`gp` set): dc's writable bytes
(above the HTIF words, below `__stack_top`) owned, `.data`'s dc words at their
initial values, the script `s` (no `NUL`) at `dc_script + 16`, NUL-ended. -/
structure StartPre (S : Nat → Prop) (M : Mem) (s : List Nat) : Prop where
  own : ∀ a, tohostAddr + 16 ≤ a → a < stackTop → S a
  ibase : ldv .lw M ibaseAddr = BitVec.ofNat 64 10
  obase : ldv .lw M obaseAddr = BitVec.ofNat 64 10
  lineMax : ldv .lw M lineMaxAddr = BitVec.ofInt 64 (-1)
  outFd : ldv .lw M stdFilesAddr = BitVec.ofNat 64 1
  errFd : ldv .lw M (stdFilesAddr + 4) = BitVec.ofNat 64 2
  text : ∀ i, i < s.length → imgM M (scriptAddr + i) = BitVec.ofNat 8 (s.getD i 0)
  nul : imgM M (scriptAddr + s.length) = 0#8
  nz : 0 ∉ s
  byte : ∀ c ∈ s, c < 256
  len : s.length < 8192

/-- `main`'s frame: the 8 MiB from `__heap_end` to `__stack_top`. -/
abbrev mainW : Nat := stackTop - heapEnd

/-- **The fresh boot** from the loader's memory with `.bss` zeroed. -/
theorem StartPre.boot {S : Nat → Prop} {M M' : Mem} {s : List Nat} (h : StartPre S M s)
    (hf : Filled M' M freeListAddr bssLen (fun _ => 0#8)) : BootPre S M' stackTop mainW s := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hr : ∀ a, a < freeListAddr → imgM M' a = imgM M a := fun a ha => hf.rest a (.inl ha)
  have hw : ∀ (k : MKind) a, a + widthOfM k ≤ freeListAddr → ldv k M' a = ldv k M a :=
    fun k a ha => ldv_congr k fun j hj => hr _ (by omega)
  have hz : ∀ a, freeListAddr ≤ a → a < heapStart → imgM M' a = 0#8 := fun a h1 h2 => by
    have := hf.fill (a - freeListAddr) (by simp only [bssLen]; omega)
    rwa [show freeListAddr + (a - freeListAddr) = a by omega] at this
  have hlen := h.len
  have hsl : ∀ i, i ≤ s.length → scriptAddr + i < freeListAddr := fun i hi => by
    simp only [scriptAddr, freeListAddr]; omega
  refine
    { heap :=
        { brkWord := ldv_zero .ld (.inl rfl) fun j hj => hz _
            (by simp only [brkAddr, freeListAddr]; omega)
            (by simp only [widthOfM] at hj; simp only [brkAddr, heapStart]; omega)
          brkZero := fun _ => rfl
          brkLo := fun h => absurd rfl h
          brkHi := by simp only [heapEnd]; omega
          brkAl := rfl
          links := .nil (ldv_zero .ld (.inl rfl) fun j hj => hz _ (by omega)
            (by simp only [widthOfM] at hj; simp only [freeListAddr, heapStart]; omega))
          hdr := fun _ h => absurd h List.not_mem_nil
          hAl := fun _ h => absurd h List.not_mem_nil
          szAl := fun _ h => absurd h List.not_mem_nil
          lo := fun _ h => absurd h List.not_mem_nil
          hi := fun _ h => absurd h List.not_mem_nil
          apart := List.Pairwise.nil
          own := fun a h1 h2 => h.own a (by simp only [heapStart] at h1; omega)
            (by simp only [heapEnd, stackTop] at h2 ⊢; omega)
          globOwn := fun a h1 h2 => h.own a (by simp only [freeListAddr] at h1; omega)
            (by simp only [freeListAddr, stackTop] at h2 ⊢; omega) }
      bss := hz
      ibase := (hw .lw _ (by simp only [widthOfM, dc_addrs, freeListAddr]; omega)).trans h.ibase
      obase := (hw .lw _ (by simp only [widthOfM, dc_addrs, freeListAddr]; omega)).trans h.obase
      lineMax := (hw .lw _ (by simp only [widthOfM, dc_addrs, freeListAddr]; omega)).trans h.lineMax
      outFd := (hw .lw _ (by simp only [widthOfM, dc_addrs, freeListAddr]; omega)).trans h.outFd
      errFd := (hw .lw _ (by simp only [widthOfM, dc_addrs, freeListAddr]; omega)).trans h.errFd
      glob := fun a ha => h.own a (by have := ha.lt; omega)
        (by have := ha.lt; simp only [heapStart, stackTop] at this ⊢; omega)
      col := fun a h1 h2 => h.own a (by simp only [dc_addrs] at h1; omega)
        (by simp only [dc_addrs, stackTop] at h2 ⊢; omega)
      bcFree := fun a h1 h2 => h.own a (by simp only [dc_addrs] at h1; omega)
        (by simp only [dc_addrs, stackTop] at h2 ⊢; omega)
      frame := ⟨fun a h1 h2 => h.own a (by simp only [mainW, stackTop, heapEnd] at h1; omega) h2,
        by simp only [mainW, stackTop, heapEnd]; omega, by simp only [stackTop]; omega, rfl⟩
      room := by simp only [mainW, stackTop, heapEnd]; omega
      big := by simp only [mainW, stackTop, heapEnd]; omega
      script :=
        { own := fun i hi => h.own _ (by simp only [scriptAddr]; omega)
            (by simp only [scriptAddr, stackTop]; omega)
          nz := fun i hi e => by
            rw [hr _ (hsl i (by omega)), h.text i hi] at e
            have hm : s.getD i 0 ∈ s := by simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]; exact List.getElem_mem hi
            have hb := h.byte _ hm
            have := congrArg BitVec.toNat e
            simp only [BitVec.toNat_ofNat] at this
            rw [Nat.mod_eq_of_lt hb] at this
            rw [this] at hm; exact h.nz hm
          nul := by rw [hr _ (hsl _ (Nat.le_refl _))]; exact h.nul
          lo := by simp only [scriptAddr]; omega
          hi := by simp only [scriptAddr]; omega }
      text := fun i hi => (hr _ (hsl i (by omega))).trans (h.text i hi)
      byte := h.byte
      len := h.len }

/-- **`_start` from `0x80000008`** (after `gp`): `sp = __stack_top`, `.bss`
zeroed into `M1`, `main` called with `ra = 0x8000003c`, then `main_spec` to
the call of `dc_evalstr` (`BootEval` over `main`'s entry `M1`, `R1`).
`bc_init_numbers`' out of memory exits with status 1 (`hex`);
`dc_makestring`'s goes to `hoom`. -/
theorem start_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {s : List Nat}
    (h : StartPre S M s) (R : Nat → BitVec 64) (hex : ExitK live S Q 1#64)
    (hoom : ∀ M1 R' M' sp', Filled M1 M freeListAddr bssLen (fun _ => 0#8) →
      OomAt S stackTop mainW M1 (fun _ => False) sp' R' M' → DWO live S Q t 0x80001e74#64 R' M')
    (hk : ∀ M1 R1 R' M' H' F L C b1 b2, Filled M1 M freeListAddr bssLen (fun _ => 0#8) →
      R1 1 = 0x8000003c#64 → R1 2 = BitVec.ofNat 64 stackTop →
      BootEval S stackTop mainW M1 R1 R' M' H' F L C (msObj b1 b2 s) s →
      DWO live S Q t 0x80001914#64 R' M') :
    DWO live S Q t 0x80000008#64 R M := by
  dx_run hlive at 0x80000020
  refine bss_loop hlive (fun a h1 h2 => h.own a (by simp only [freeListAddr, tohostAddr] at h1 ⊢; omega)
      (by simp only [heapStart, stackTop] at h2 ⊢; omega)) M _ (fun R1 M1 k1 hf => ?_) 273 0 _ _ rfl
    (by simp only [bssLen_eq]; omega) (by bsimp []) (by bsimp []) (by keeps_tac Keeps.refl _ _)
    (Filled.zero M _ _)
  dx_run hlive at 0x80000b00
  exact main_spec hlive (h.boot hf) _ (by bsimp [k1.get 2]) hex (fun R' M' sp' ho => hoom M1 R' M' sp' hf ho)
    fun R' M' H' F L C b1 b2 he => hk M1 _ R' M' H' F L C b1 b2 hf (by bsimp []) (by bsimp [k1.get 2]) he

/-- **`main`'s return into `_start`** (`0x8000003c`, `a0` the status):
`exit` to `_exit`'s store with the exit word of the status. -/
theorem start_exit {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} (hsf : StackFrame S stackTop 16)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 stackTop)
    (hk : ∀ R' M', R' 15 = exitWord (R 10 &&& 4294967295#64) → R' 14 = exitSite.base →
      DWO live S Q t 0x800005c8#64 R' M') :
    DWO live S Q t 0x8000003c#64 R M := by
  dx_run hlive at 0x800005d0
  exact exit_spec hlive hsf _ (by rw [h2]; rfl) hk

/-- **`flush_okay ()`** at `0x80000ab0`: `ferror`, `fflush`, `fclose` of
`stdout` (`.rodata`'s pointer, `stdout_word`) all return `0`, so it returns
`0`; only its 16-byte frame is written. -/
theorem flush_okay_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {sp : Nat} (hsf : StackFrame S sp 16)
    (R : Nat → BitVec 64) (h2 : R 2 = BitVec.ofNat 64 sp) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M', Keeps cClob R' R → R' 2 = R 2 → R' 10 = 0#64 →
      (∀ a, ¬ frameIn sp 16 a → imgM M' a = imgM M a) → DWO live S Q t (R 1) R' M') :
    DWO live S Q t 0x80000ab0#64 R M := by
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  simp only [tohostAddr] at hsl
  have hro : ∀ b ∈ accAddrs 2147516936 8, (b, dcROImg b) ∈ dcRO := by decide +kernel
  dx_run [3] hlive
  all_goals (try bsimp [h2])
  all_goals first | (simp only [StOK, tohostAddr]; omega) | exact frame_acc hsf (by omega) (by omega) | skip
  refine stR_80000abc hlive (by bsimp []; simp only [LdOK, tohostAddr]; omega) (by bsimp []; exact hro) ?_
  bsimp [stdout_word]
  dx_run hlive at 0x8000071c
  all_goals (try bsimp [h2])
  all_goals first | (simp only [StOK, tohostAddr]; omega) | exact frame_acc hsf (by omega) (by omega) | skip
  refine ferror_spec hlive _ (by bsimp []; try decide) fun R1 k1 e1 => ?_
  bsimp []
  apply st_80000acc hlive _ fun hc => absurd e1 hc
  intro _
  dx_run hlive at 0x8000070c
  all_goals (try bsimp [k1.get 8])
  refine fflush_spec hlive _ (by bsimp []; try decide) fun R2 k2 e2 => ?_
  bsimp []
  apply st_80000aec hlive (fun hc => absurd e2 hc)
  intro _
  dx_run hlive at 0x80000714
  all_goals (try bsimp [k2.get 8, k1.get 8])
  refine fclose_spec hlive _ (by bsimp []; try decide) fun R3 k3 e3 => ?_
  bsimp []
  dx_run hlive
  all_goals (try bsimp [e3, k3.get 2, k2.get 2, k1.get 2, h2])
  all_goals first | (simp only [LdOK, tohostAddr]; omega) | exact frame_acc hsf (by omega) (by omega) | skip
  all_goals (try rw [ldv_store_hit])
  · exact hal
  rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega), ldv_store_hit]
  refine hk _ _ (fun z hz => ?_) (by simp only [upd_apply, ite_true]; rw [h2]; congr 1; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; decide) fun a ha => ?_
  · simp only [cClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨n1, -, -, -, n10, -⟩ := hz
    by_cases z2 : z = 2
    · subst z2; simp only [upd_apply, ite_true]; rw [h2]; congr 1; omega
    by_cases z8 : z = 8
    · subst z8; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    simp only [upd_apply, n1, n10, z2, z8, ite_false, k3 z (by simp [n10]), k2 z (by simp [n10]),
      k1 z (by simp [n10])]
  · simp only [frameIn, not_and, Nat.not_lt] at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]


end Dc.Mach
