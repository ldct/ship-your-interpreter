import Dc.Mach.Malloc

/-!
# `realloc` (`dc-port/libc/libc.c`)

```
80000a2c beqz a0,80000aa8 ; 80000a30 ld a4,-16(a0) ; 80000a34 mv a3,a0
80000a38 bltu a4,a1,80000a40 ; 80000a3c ret
80000a40 addi sp,sp,-32 ; 80000a44 mv a0,a1 ; 80000a48 sd ra,24(sp)
80000a4c sd a3,8(sp) ; 80000a50 jal malloc ; 80000a54 beqz a0,80000a9c
80000a58 ld a3,8(sp) ; 80000a5c ld a1,-16(a3) ; 80000a60 beqz a1,80000a84
80000a64 add a1,a3,a1 ; 80000a68 mv a4,a0 ; 80000a6c mv a5,a3
80000a70 lbu a2,0(a5) ; 80000a74 addi a5,a5,1 ; 80000a78 addi a4,a4,1
80000a7c sb a2,-1(a4) ; 80000a80 bne a1,a5,80000a70     (memcpy, inlined)
80000a84 auipc a4,0x1c ; 80000a88 ld a4,708(a4) ; 80000a8c addi a5,a3,-16
80000a90 sd a4,-8(a3) ; 80000a94 auipc a4,0x1c ; 80000a98 sd a5,692(a4)
                                                        (free, inlined)
80000a9c ld ra,24(sp) ; 80000aa0 addi sp,sp,32 ; 80000aa4 ret
80000aa8 mv a0,a1 ; 80000aac j malloc
```

- `realloc_null_spec`: `realloc(NULL, n)` is `malloc(n)` (a tail call,
  closed by `malloc_spec`).
- `realloc_spec`: `realloc(p, n)` for the payload `p` of the live block `b`
  ends in `ReallocPost`: the invariant for the new heap and one of three
  results (`ReallocRes`): `p` itself when `n ≤ b.sz`; `NULL` with the same
  blocks when the heap is exhausted; or a fresh live block `c` holding a copy
  of `b`'s `b.sz` bytes, with `b` freed. Only allocator bytes of the old heap
  and the 32-byte frame change. The call to `malloc` is closed by
  `malloc_spec`, the inlined `free` by `HeapInv.push`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `sx_norm` on the goal only: register lookups, literal immediates and
literal sums. -/
macro "gnorm" : tactic =>
  `(tactic| try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, reduceIte,
    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
    BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat, BitVec.reduceToNat, Nat.reduceAdd])

/-- `gnorm` at a hypothesis. -/
macro "gnorm_at " h:ident : tactic =>
  `(tactic| try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, reduceIte,
    LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
    BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat, BitVec.reduceToNat, Nat.reduceAdd] at $h:ident)

/-- The copy loop of `realloc` at `0x80000a70`: `a5 = s + i`, `a4 = d + i`,
`a1 = s + n`; leaves at `0x80000a84`. -/
theorem realloc_copy {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {d s n : Nat} (hc : CopyArgs S d s n) (Mt0 : Mem)
    (R0 : Nat → BitVec 64)
    (hk : ∀ R' Mt', Keeps [11, 12, 14, 15] R' R0 → Filled Mt' Mt0 d n (fun j => imgM Mt0 (s + j)) →
      DW live S Q 0x80000a84#64 R' Mt') :
    ∀ k i (R : Nat → BitVec 64) (Mt : Mem), n - i = k → i < n →
      R 15 = BitVec.ofNat 64 (s + i) → R 14 = BitVec.ofNat 64 (d + i) →
      R 11 = BitVec.ofNat 64 (s + n) → Keeps [11, 12, 14, 15] R R0 →
      Filled Mt Mt0 d i (fun j => imgM Mt0 (s + j)) →
      DW live S Q 0x80000a70#64 R Mt := by
  have hlo := hc.dst.lo
  have hhi := hc.dst.hi
  have hlo' := hc.src.lo
  have hhi' := hc.src.hi
  have hdj := hc.disj
  have htx : tohostAddr = 0x8001ad00 := rfl
  intro k
  induction k with
  | zero => intro i R Mt h1 h2; omega
  | succ k ih =>
    intro i R Mt hn hi h15 h14 h11 hkeep hf
    have hsrc : imgM Mt (s + i) = imgM Mt0 (s + i) := hf.rest _ (by omega)
    dx_run hlive at 0x80000a84
    dc_sides [h11, h15, h14] hc.src
    all_goals (try dc_own hc.dst)
    · intro hne
      refine ih (i + 1) _ _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_
      · refine Classical.byContradiction fun hge => hne ?_
        congr 1; omega
      · dc_simp [h15, Nat.add_assoc]
      · dc_simp [h14, Nat.add_assoc]
      · dc_simp [h11]
      · keeps_tac hkeep
      · exact hf.snoc (by dc_simp [h14]) (by rw [sbData_zext, hsrc])
    · intro heq
      have hn' : i + 1 = n := by
        refine Classical.byContradiction fun hne => heq ?_
        rw [ofNat_ne_iff (by omega) (by omega)]; omega
      refine hk _ _ (by keeps_tac hkeep) ?_
      have := hf.snoc (A := d + i) rfl (v := zero_extend (m := 64) (imgM Mt (s + i)))
        (by rw [sbData_zext, hsrc])
      rwa [hn'] at this

/-- The registers `realloc` may change. -/
abbrev reallocClob : List Nat := [10, 11, 12, 13, 14, 15]

/-- The result of `realloc(p, n)` for the live block `b` (split out of the
live list as `lpre ++ b :: lpost`). -/
inductive ReallocRes (Mt Mt' : Mem) (H H' : Heap) (b : Blk) (lpre lpost : List Blk) (n : Nat)
    (r : BitVec 64) : Prop
  /-- `n ≤ b.sz`: the block itself, nothing changed. -/
  | same : n ≤ b.sz → r = BitVec.ofNat 64 b.pay → H' = H → Mt' = Mt →
      ReallocRes Mt Mt' H H' b lpre lpost n r
  /-- The heap is exhausted: `NULL`, the same blocks. -/
  | null : r = 0#64 → H'.free = H.free → H'.live = H.live →
      ReallocRes Mt Mt' H H' b lpre lpost n r
  /-- A fresh block `c` of at least `n` bytes, carved from allocator bytes,
  holding `b`'s bytes; `b` heads the free list. -/
  | moved (c : Blk) : r = BitVec.ofNat 64 c.pay → n ≤ c.sz → b.sz < c.sz →
      H'.live = c :: (lpre ++ lpost) → (∃ F, H'.free = b :: F ∧ ∀ x ∈ F, x ∈ H.free) →
      (∀ a, c.h ≤ a → a < c.fin → AllocByte H a) →
      (∀ i, i < b.sz → imgM Mt' (c.pay + i) = imgM Mt (b.pay + i)) →
      ReallocRes Mt Mt' H H' b lpre lpost n r

/-- `realloc`'s postcondition: the invariant, the result, and the frame (only
allocator bytes of the old heap and the 32 bytes below `sp` change). -/
structure ReallocPost (S : Nat → Prop) (Mt Mt' : Mem) (H H' : Heap) (b : Blk)
    (lpre lpost : List Blk) (n sp : Nat) (r : BitVec 64) : Prop where
  inv : HeapInv S Mt' H'
  res : ReallocRes Mt Mt' H H' b lpre lpost n r
  frame : ∀ a, ¬ AllocByte H a → (a < sp - 32 ∨ sp ≤ a) → imgM Mt' a = imgM Mt a

/-- A store outside the allocator's bytes keeps the invariant. -/
theorem HeapInv.store_off {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {x w : Nat} (v : BitVec 64) (hx : heapEnd ≤ x) :
    HeapInv S (writeLog Mt [(x, w, v)]) H :=
  hi.transport fun a ha => imgM_store_miss _ _ (by have := (AllocByte.bound hi ha).2; omega)

/-- A doubleword load of bytes a run kept. -/
theorem ldv_keep {Mt Mt' : Mem} {a : Nat} {v : BitVec 64} (h : ldv .ld Mt a = v)
    (hag : ∀ j, j < 8 → imgM Mt' (a + j) = imgM Mt (a + j)) : ldv .ld Mt' a = v :=
  (ldv_ld_congr hag).trans h

/-- `realloc`'s epilogue at `0x80000a9c`. -/
theorem realloc_exit {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {sp : Nat} (hfr : StackFrame S sp 32)
    (R0 R : Nat → BitVec 64) (h2 : (R 2).toNat = sp - 32) (h2' : R 2 + 32#64 = R0 2)
    (hra : ldv .ld M (sp - 8) = R0 1) (hkeep : Keeps [1, 2, 10, 11, 12, 13, 14, 15] R R0)
    (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps reallocClob R' R0 → R' 10 = R 10 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x80000a9c#64 R M := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  dx_run hlive
  all_goals (try dc_frame hfr)
  all_goals simp (disch := sx_addr) only [ldv_eq_at hra]
  all_goals (try (dc_simp [hal]; done))
  refine hk _ ?_ (by dc_simp [])
  refine Keeps.restore (by dc_simp [h2']) ?_
  refine Keeps.restore rfl ?_
  exact hkeep.mono (by decide)

/-- `realloc` after `malloc` returns (`0x80000a54`): `NULL` returns at once;
a fresh block `c` receives `b`'s bytes and `b` is freed. `M` is the memory
after `malloc`, `Mt` the memory at entry. -/
theorem realloc_body {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt M : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H H1 : Heap} (hi : HeapInv S Mt H) (hinv : HeapInv S M H1)
    {lpre : List Blk} {b : Blk} {lpost : List Blk} (hl : H.live = lpre ++ b :: lpost)
    {n sp : Nat} (hlt : b.sz < n) (hfr : StackFrame S sp 32) (hsp : heapEnd + 32 ≤ sp)
    (R0 R : Nat → BitVec 64) (hres : MallocRes H H1 n (R 10))
    (hframe : ∀ a, ¬ AllocByte H a → (a < sp - 32 ∨ sp ≤ a) → imgM M a = imgM Mt a)
    (h2 : (R 2).toNat = sp - 32) (h2' : R 2 + 32#64 = R0 2)
    (hra : ldv .ld M (sp - 8) = R0 1) (hpw : ldv .ld M (sp - 24) = BitVec.ofNat 64 (b.h + 16))
    (hkeep : Keeps [1, 2, 10, 11, 12, 13, 14, 15] R R0) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt' H', Keeps reallocClob R' R0 →
      ReallocPost S Mt Mt' H H' b lpre lpost n sp (R' 10) → DW live S Q (R0 1) R' Mt') :
    DW live S Q 0x80000a54#64 R M := by
  heap_consts
  have hbL : b ∈ H.live := by rw [hl]; simp
  have hbB : b ∈ H.blocks := List.mem_append_right _ hbL
  have fb := hi.blk hbB
  have hblo : 2147603920 ≤ b.h := fb.lo
  have hbfin : b.h + 16 + b.sz ≤ H.brk := fb.fin
  have hbtop : H.brk ≤ 2273312768 := fb.top
  have hbal : b.h % 16 = 0 := fb.al
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hspl : 2273312768 + 32 ≤ sp := hsp
  -- the payload of `b` is the client's, so `malloc` kept it
  have hsrc : ∀ i, i < b.sz → imgM M (b.h + 16 + i) = imgM Mt (b.h + 16 + i) := fun i hi' =>
    hframe _ (hi.live_fresh hbL (by simp only [Blk.pay]; omega) (by simp only [Blk.fin]; omega)).1
      (by omega)
  cases hres with
  | null e1 e2 e3 =>
    dx_run hlive at 0x80000a9c
    · intro _
      exact realloc_exit hlive hfr R0 R h2 h2' hra hkeep hal fun R' hk' h10 =>
        hk R' M H1 hk' ⟨hinv, .null (h10.trans e1) e2 e3, hframe⟩
    · intro h; exact absurd e1 h
  | block c e1 e2 e3 e4 e5 =>
    have hcL : c ∈ H1.live := by rw [e3]; exact List.mem_cons_self
    have hcB : c ∈ H1.blocks := List.mem_append_right _ hcL
    have hbL1 : b ∈ H1.live := by rw [e3]; exact List.mem_cons_of_mem _ hbL
    have hbB1 : b ∈ H1.blocks := List.mem_append_right _ hbL1
    have fc := hinv.blk hcB
    have hclo : 2147603920 ≤ c.h := fc.lo
    have hcfin : c.h + 16 + c.sz ≤ H1.brk := fc.fin
    have hctop : H1.brk ≤ 2273312768 := fc.top
    have hcb : c.Apart b := by
      have hp := (List.pairwise_append.1 hinv.apart).2.1
      rw [e3, List.pairwise_cons] at hp
      exact hp.1 b hbL
    have hcb' : c.h + 16 + c.sz ≤ b.h ∨ b.h + 16 + b.sz ≤ c.h := hcb
    have hszc : n ≤ c.sz := e2
    have hdrb : ldv .ld M b.h = BitVec.ofNat 64 b.sz := hinv.hdr b hbB1
    -- after the copy (`0x80000a84`): free `b`, return `c`
    have hfree : ∀ (R2 : Nat → BitVec 64) (M2 : Mem), Keeps [1, 2, 10, 11, 12, 13, 14, 15] R2 R0 →
        R2 2 = R 2 → R2 10 = R 10 → R2 13 = BitVec.ofNat 64 (b.h + 16) →
        Filled M2 M (c.h + 16) b.sz (fun j => imgM M (b.h + 16 + j)) →
        DW live S Q 0x80000a84#64 R2 M2 := by
      intro R2 M2 hk2 e22 e210 e213 hf
      have hinv2 : HeapInv S M2 H1 := hinv.transport fun a ha => hf.rest a (by
        refine Classical.byContradiction fun hin => ?_
        have := (hinv.live_fresh hcL (a := a) (by simp only [Blk.pay]; omega)
          (by simp only [Blk.fin]; omega)).1
        exact this ha)
      have hfl : ldv .ld M2 2147601736 = BitVec.ofNat 64 (headOf H1.free) := hinv2.links.head
      have hA : (R2 13 + 18446744073709551608#64).toNat = b.h + 8 := by
        rw [e213, ofNat_add_ofNat, BitVec.toNat_ofNat]; omega
      have hw : R2 13 + 18446744073709551600#64 = BitVec.ofNat 64 b.h := by
        rw [e213, ofNat_add_ofNat]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
      have hra2 : ldv .ld M2 (sp - 8) = R0 1 := ldv_keep hra fun j hj => hf.rest _ (by omega)
      dx_run hlive at 0x80000a9c
      all_goals (try (gnorm; intro x hx; have := of_mem_accAddrs hx
                      exact hi.globOwn x (by momega) (by momega)))
      all_goals (try (gnorm; rw [hA]; simp only [StOK]; momega))
      all_goals (try (gnorm; rw [hA]; intro x hx; have := of_mem_accAddrs hx
                      exact hi.own x (by momega) (by momega)))
      refine realloc_exit hlive hfr R0 _ ?e2 ?e2' ?era ?ekeep hal ?ek
      case e2 => dc_simp [e22, h2]
      case e2' => dc_simp [e22, h2']
      case ekeep => keeps_tac hk2
      case era => simp (disch := first | momega | (rw [hA]; momega)) only [ldv_ld_miss]; exact hra2
      intro R' hk' h10
      refine hk R' _ ⟨H1.braw, b :: H1.free, (c :: lpre) ++ lpost⟩ hk' ⟨?_, ?_, ?_⟩
      · exact hinv2.push_at (lpre := c :: lpre) (by rw [e3, hl]; rfl) hA hfl rfl hw
      · refine .moved c (by rw [h10]; dc_simp [e210, e1]) hszc (by omega) rfl
          ⟨H1.free, rfl, e4⟩ e5 fun i hi' => ?_
        simp only [Blk.pay]
        simp (disch := first | momega | (rw [hA]; momega)) only [imgM_store_miss]
        rw [hf.fill i hi', hsrc i hi']
      · intro a ha hout
        have h1 : ¬ (2147601736 ≤ a ∧ a < 2147601752) := fun h => ha (.glob h.1 h.2)
        have h2 : ¬ (b.h ≤ a ∧ a < b.h + 16) := fun h => ha (.hdr b hbB h.1 h.2)
        have h3 : ¬ (c.h ≤ a ∧ a < c.h + 16 + c.sz) := fun h => ha (e5 a h.1 h.2)
        simp (disch := first | momega | (rw [hA]; momega)) only [imgM_store_miss]
        rw [hf.rest a (by omega), hframe a ha hout]
    dx_run hlive at 0x80000a9c
    · intro h; exfalso; rw [e1, ofNat_eq_zero_iff (by simp only [Blk.pay]; omega)] at h
      simp only [Blk.pay] at h; omega
    · intro _
      dx_run [1] hlive
      all_goals (try dc_frame hfr)
      all_goals (try (gnorm; simp only [LdOK]; sx_addr))
      simp (disch := sx_addr) only [ldv_eq_at hpw]
      have hA : (BitVec.ofNat 64 (b.h + 16) + 18446744073709551600#64).toNat = b.h := by
        rw [ofNat_add_ofNat, BitVec.toNat_ofNat]; omega
      dx_run [1] hlive
      all_goals (try (gnorm; rw [hA]; simp only [LdOK]; omega))
      all_goals (try (gnorm; rw [hA]; intro x hx; have := of_mem_accAddrs hx
                      exact hi.own x (by momega) (by momega)))
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hA, hdrb]
      dx_run hlive at 0x80000a70 0x80000a84
      · intro h0
        have hz : b.sz = 0 := (ofNat_eq_zero_iff (by omega)).1 h0
        refine hfree _ _ (by keeps_tac hkeep) (by dc_simp []) (by dc_simp []) (by dc_simp []) ?_
        rw [hz]; exact Filled.zero M _ _
      · intro hnz
        have hnz' : b.sz ≠ 0 := fun h => hnz (by rw [h]; rfl)
        dx_run hlive at 0x80000a70
        have hcp : CopyArgs S (c.h + 16) (b.h + 16) b.sz :=
          ⟨⟨fun i hi' => hi.own _ (by momega) (by momega), by momega, by omega⟩,
            ⟨fun i hi' => hi.own _ (by momega) (by momega), by momega, by omega⟩, by omega⟩
        refine realloc_copy hlive hcp M _ ?kont (b.sz - 0) 0 _ _ rfl (by omega) ?r15 ?r14 ?r11
          (Keeps.refl _ _) (Filled.zero M _ _)
        case r15 => dc_simp []
        case r14 => dc_simp [e1]
        case r11 => dc_simp []
        case kont =>
          intro R' Mt' hk' hf
          refine hfree _ _ ?_ ?_ ?_ ?_ hf
          · exact (hk'.mono (by decide)).trans (by keeps_tac hkeep)
          · rw [hk'.get 2]; dc_simp []
          · rw [hk'.get 10]; dc_simp []
          · rw [hk'.get 13]; dc_simp []

/-- `realloc` growing the live block `b` (`0x80000a40`, `b.sz < n`): save
`ra` and `p`, call `malloc(n)`, continue in `realloc_body`. -/
theorem realloc_grow {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} (hi : HeapInv S Mt H)
    {lpre : List Blk} {b : Blk} {lpost : List Blk} (hl : H.live = lpre ++ b :: lpost)
    {n sp : Nat} (hlt : b.sz < n) (hn : n < 2 ^ 62) (hfr : StackFrame S sp 32)
    (hsp : heapEnd + 32 ≤ sp) (R0 R : Nat → BitVec 64) (hsp0 : (R0 2).toNat = sp)
    (h11 : R 11 = BitVec.ofNat 64 n) (h13 : R 13 = BitVec.ofNat 64 (b.h + 16))
    (hkeep : Keeps reallocClob R R0) (hal : (R0 1).toNat % 4 = 0)
    (hk : ∀ R' Mt' H', Keeps reallocClob R' R0 →
      ReallocPost S Mt Mt' H H' b lpre lpost n sp (R' 10) → DW live S Q (R0 1) R' Mt') :
    DW live S Q 0x80000a40#64 R Mt := by
  have hlo := hfr.lo
  have hhi := hfr.hi
  have hal2 := hfr.al
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hspl : 2273312768 + 32 ≤ sp := hsp
  have hR2 : (R 2).toNat = sp := by rw [hkeep.get 2]; exact hsp0
  have hR1 : R 1 = R0 1 := hkeep.get 1
  have hoff : ∀ a, AllocByte H a → a < 2273312768 := fun a ha => (AllocByte.bound hi ha).2
  dx_run hlive at 0x8000096c
  all_goals (try dc_frame hfr)
  refine malloc_spec hlive ((hi.store_off _ (by sx_addr)).store_off _ (by sx_addr)) hn _
    (by dc_simp [h11]; try decide) (by dc_simp []; try decide) fun R1 Mt1 H1 hk1 hp => ?_
  have hkm : ∀ a, 2273312768 ≤ a → imgM Mt1 a = imgM (writeLog (writeLog Mt
      [((R 2 + 18446744073709551584#64 + 24#64).toNat, 8, R 1)])
      [((R 2 + 18446744073709551584#64 + 8#64).toNat, 8, R 13)]) a :=
    fun a ha => hp.frame a fun h => by have := hoff a h; omega
  refine realloc_body hlive hi hp.inv hl hlt hfr hsp R0 R1 hp.res ?_ ?_ ?_ ?_ ?_ ?_ hal hk
  · intro a ha hout
    rw [hp.frame a ha]
    simp (disch := sx_addr) only [imgM_store_miss]
  · rw [hk1.get 2]; dc_simp []; sx_addr
  · rw [hk1.get 2]; dc_simp []; rw [hkeep.get 2]; exact add_lits_cancel _ _ _ (by decide)
  · refine ldv_keep ?_ fun j hj => hkm _ (by omega)
    simp (disch := sx_addr) only [ldv_ld_hit_eq, ldv_ld_miss]; exact hR1
  · refine ldv_keep ?_ fun j hj => hkm _ (by omega)
    simp (disch := sx_addr) only [ldv_ld_hit_eq, ldv_ld_miss]; exact h13
  · exact (hk1.mono (by decide)).trans (by keeps_tac (hkeep.mono (by decide)))

/-- **`realloc(p, n)`** at `0x80000a2c` for the payload `p` of the live
block `b`, `n < 2^62`, with a 32-byte frame above the heap: `ReallocPost`;
clobbers `a0`–`a5`. -/
theorem realloc_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} (hi : HeapInv S Mt H)
    {lpre : List Blk} {b : Blk} {lpost : List Blk} (hl : H.live = lpre ++ b :: lpost)
    {n sp : Nat} (hn : n < 2 ^ 62) (hfr : StackFrame S sp 32) (hsp : heapEnd + 32 ≤ sp)
    (R : Nat → BitVec 64) (hsp0 : (R 2).toNat = sp) (h10 : R 10 = BitVec.ofNat 64 b.pay)
    (h11 : R 11 = BitVec.ofNat 64 n) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt' H', Keeps reallocClob R' R →
      ReallocPost S Mt Mt' H H' b lpre lpost n sp (R' 10) → DW live S Q (R 1) R' Mt') :
    DW live S Q 0x80000a2c#64 R Mt := by
  have hbB : b ∈ H.blocks := List.mem_append_right _ (by rw [hl]; simp)
  have fb := hi.blk hbB
  have hblo : 2147603920 ≤ b.h := fb.lo
  have hbfin : b.h + 16 + b.sz ≤ H.brk := fb.fin
  have hbtop : H.brk ≤ 2273312768 := fb.top
  have hbal : b.h % 16 = 0 := fb.al
  have hdr : ldv .ld Mt b.h = BitVec.ofNat 64 b.sz := hi.hdr b hbB
  have hA : (R 10 + 18446744073709551600#64).toNat = b.h := by
    rw [h10, ofNat_add_ofNat, BitVec.toNat_ofNat]; simp only [Blk.pay]; omega
  dx_run hlive at 0x80000a40
  all_goals (try (gnorm; rw [hA]; simp only [LdOK]; momega))
  all_goals (try (gnorm; rw [hA]; intro x hx; have := of_mem_accAddrs hx
                  exact hi.own x (by momega) (by momega)))
  · intro hlt
    dc_simp [h11] at hlt
    try rw [hA, hdr, ofNat_toNat_lt (by omega)] at hlt
    exact realloc_grow hlive hi hl hlt hn hfr hsp R _ hsp0
      (by simp (disch := decide) only [upd_other]; exact h11)
      (by simp (disch := decide) only [upd_other, upd_same]; exact h10)
      (by keeps_tac Keeps.refl _ _) hal hk
  · intro hge
    dc_simp [h11] at hge
    try rw [hA, hdr, ofNat_toNat_lt (by omega)] at hge
    dx_run hlive
    exact hk _ Mt H (by keeps_tac Keeps.refl _ _)
      ⟨hi, .same (by omega) (by
        simp only [upd_other _ _ (show (10:Nat) ≠ 13 by decide),
          upd_other _ _ (show (10:Nat) ≠ 14 by decide)]; exact h10) rfl rfl, fun _ _ _ => rfl⟩

/-- **`realloc(NULL, n)`** at `0x80000a2c` is `malloc(n)`. -/
theorem realloc_null_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} (hi : HeapInv S Mt H) {n : Nat}
    (hn : n < 2 ^ 62) (R : Nat → BitVec 64) (h10 : R 10 = 0#64) (h11 : R 11 = BitVec.ofNat 64 n)
    (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt' H', Keeps (11 :: mallocClob) R' R → MallocPost S Mt Mt' H H' n (R' 10) →
      DW live S Q (R 1) R' Mt') :
    DW live S Q 0x80000a2c#64 R Mt := by
  dx_run hlive at 0x8000096c
  · intro _
    dx_run hlive at 0x8000096c
    refine malloc_spec hlive hi hn _ (by dc_simp [h11]) (by dc_simp [hal]) fun R' Mt' H' hk' hp => ?_
    refine hk R' Mt' H' ?_ hp
    exact (hk'.mono (by decide)).trans (by keeps_tac Keeps.refl _ _)
  · intro h; exact absurd h10 h

end Dc.Mach
