import Dc.Mach.HeapInv

/-!
# `malloc` and `free` (`dc-port/libc/libc.c`)

Specs over the heap invariant `HeapInv` (`HeapInv.lean`):

- `malloc_spec`: `malloc(n)` at `0x8000096c` ends in `MallocPost` — the
  invariant for the new heap, the result (`NULL` with the same blocks, or a
  block of at least `n` bytes carved from allocator bytes, now live), and the
  frame (only allocator bytes change). Its parts: the first-fit scan of the
  free list (`malloc_scan`), the first setting of the bump pointer
  (`malloc_top`) and the bump (`malloc_bump`).
- `free_spec`: `free(p)` at `0x80000a0c` for a live block: `FreePost` (the
  block heads the free list, only allocator bytes change); `free_null_spec`
  for `NULL`.

The fresh block of `malloc` is the client's: `HeapInv.live_fresh` gives that
its payload holds no allocator byte and is apart from every other live block.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- `omega` with the allocator's and HTIF's addresses as literals. -/
macro "momega" : tactic =>
  `(tactic| (heap_consts; have _htx : tohostAddr = 0x8001ad00 := rfl; omega))

/-- The registers `malloc` may change. -/
abbrev mallocClob : List Nat := [10, 12, 13, 14, 15]

/-- A literal minus a smaller value. -/
theorem toNat_lit_sub {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat = a - b := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- `HeapInv.bump` at the addresses and values of the machine's stores. -/
theorem HeapInv.bump_at {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    (hne : H.braw ≠ 0) {size : Nat} (hsz : size % 16 = 0) (hroom : H.braw + 16 + size ≤ heapEnd)
    {A B : Nat} {v w : BitVec 64} (hA : A = H.braw) (hv : v = BitVec.ofNat 64 size)
    (hB : B = brkAddr) (hw : w = BitVec.ofNat 64 (H.braw + 16 + size)) :
    HeapInv S (writeLog (writeLog Mt [(A, 8, v)]) [(B, 8, w)])
      ⟨H.braw + 16 + size, H.free, ⟨H.braw, size⟩ :: H.live⟩ := by
  subst hA hv hB hw; exact hi.bump hne hsz hroom

/-- `HeapInv.take` at the address and value of the machine's store. -/
theorem HeapInv.take_at {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {pre : List Blk} {b : Blk} {post : List Blk} (hf : H.free = pre ++ b :: post)
    {A : Nat} {v : BitVec 64} (hA : A = linkOf freeListAddr pre)
    (hv : v = BitVec.ofNat 64 (headOf post)) :
    HeapInv S (writeLog Mt [(A, 8, v)]) ⟨H.braw, pre ++ post, b :: H.live⟩ := by
  subst hA hv; exact hi.take hf

/-- `HeapInv.init` at the address and value of the machine's store. -/
theorem HeapInv.init_at {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    (h0 : H.braw = 0) {A : Nat} {v : BitVec 64} (hA : A = brkAddr)
    (hv : v = BitVec.ofNat 64 heapStart) :
    HeapInv S (writeLog Mt [(A, 8, v)]) ⟨heapStart, H.free, H.live⟩ := by
  subst hA hv; exact hi.init h0

/-- The allocator's bytes do not grow when the bump pointer is first set. -/
theorem AllocByte.of_init {H : Heap} (h0 : H.braw = 0) {a : Nat}
    (h : AllocByte ⟨heapStart, H.free, H.live⟩ a) : AllocByte H a := by
  cases h with
  | glob h1 h2 => exact .glob h1 h2
  | hdr b hb h1 h2 => exact .hdr b hb h1 h2
  | freePay b hb h1 h2 => exact .freePay b hb h1 h2
  | top h1 h2 =>
    refine .top ?_ h2
    rw [Heap.brk_of_eq h0]
    rwa [Heap.brk_of_ne (show (heapStart : Nat) ≠ 0 by decide)] at h1

/-- The continuation of `malloc(n)` entered with registers `R0`. -/
abbrev MallocK (live S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (R0 : Nat → BitVec 64) (Mt : Mem) (H : Heap) (n : Nat) : Prop :=
  ∀ R' Mt' H', Keeps mallocClob R' R0 → MallocPost S Mt Mt' H H' n (R' 10) →
    DW live S Q (R0 1) R' Mt'

/-- The bump at `0x800009c0`: `a0` the bump pointer (set), `a3` the rounded size. -/
theorem malloc_bump {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} (hi : HeapInv S Mt H) (hne : H.braw ≠ 0)
    {n size : Nat} (hsz : size % 16 = 0) (hn : n ≤ size) (hbig : size < 2 ^ 63)
    (R0 R : Nat → BitVec 64) (hkeep : Keeps mallocClob R R0)
    (h10 : R 10 = BitVec.ofNat 64 H.braw) (h13 : R 13 = BitVec.ofNat 64 size)
    (hal : (R0 1).toNat % 4 = 0) (hk : MallocK live S Q R0 Mt H n) :
    DW live S Q 0x800009c0#64 R Mt := by
  have hlo : 2147603920 ≤ H.braw := hi.brkLo hne
  have hhi : H.braw ≤ 2273312768 := hi.brkHi
  have hal16 := hi.brkAl
  have h1 : R 1 = R0 1 := hkeep.get 1
  dx_run hlive
  · intro _
    dx_run hlive
    · dc_simp [h1, hal]
    · rw [h1]
      exact hk _ Mt H (by keeps_tac hkeep) ⟨hi, .null (by dc_simp []) rfl rfl, fun _ _ => rfl⟩
  · intro hge
    dc_simp [h10, h13] at hge
    rw [toNat_lit_sub (a := 2273312768) (b := H.braw) (by omega) (by omega)] at hge
    have hroom : H.braw + 16 + size ≤ 2273312768 := by omega
    dx_run hlive
    · dc_simp [h10]; simp only [StOK]; momega
    · dc_simp [h10]; intro b hb; have := of_mem_accAddrs hb; exact hi.own b (by momega) (by momega)
    · sx_norm; intro b hb; have := of_mem_accAddrs hb; exact hi.globOwn b (by momega) (by momega)
    · dc_simp [h1, hal]
    · rw [h1]
      refine hk _ _ _ (by keeps_tac hkeep) ⟨hi.bump_at hne hsz hroom (by dc_simp [h10]) (by rw [h13]) rfl
          (by dc_simp [h10, h13]; congr 1; omega), ?_, ?_⟩
      · refine .block ⟨H.braw, size⟩ (by dc_simp [h10, Blk.pay]) hn rfl (fun c hc => hc)
          fun a h1 h2 => .top (by rw [Heap.brk_of_ne hne]; exact h1) (by bomega)
      · intro a ha
        have h1 : ¬ (2147601736 ≤ a ∧ a < 2147601752) := fun h => ha (.glob h.1 h.2)
        have h2 : ¬ (H.braw ≤ a ∧ a < 2273312768) :=
          fun h => ha (.top (by rw [Heap.brk_of_ne hne]; exact h.1) h.2)
        rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by rw [h10, ofNat_toNat_lt (by omega)]; omega)]

/-- The top of the heap at `0x800009b4` (no free block fits): set the bump
pointer on first use, then bump. -/
theorem malloc_top {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} (hi : HeapInv S Mt H)
    {n size : Nat} (hsz : size % 16 = 0) (hn : n ≤ size) (hbig : size < 2 ^ 63)
    (R0 R : Nat → BitVec 64) (hkeep : Keeps mallocClob R R0) (h13 : R 13 = BitVec.ofNat 64 size)
    (hal : (R0 1).toNat % 4 = 0) (hk : MallocK live S Q R0 Mt H n) :
    DW live S Q 0x800009b4#64 R Mt := by
  have hbw : ldv .ld Mt 2147601744 = BitVec.ofNat 64 H.braw := hi.brkWord
  have hhi : H.braw ≤ 2273312768 := hi.brkHi
  dx_run hlive
  all_goals (try (sx_norm; simp only [LdOK]; momega))
  all_goals (try (sx_norm; intro b hb; have := of_mem_accAddrs hb; exact hi.globOwn b (by momega) (by momega)))
  · intro h0
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, hbw, ofNat_eq_zero_iff (show H.braw < 2 ^ 64 by omega)] at h0
    dx_run hlive at 0x800009c0
    all_goals (try (sx_norm; simp only [StOK]; momega))
    all_goals (try (sx_norm; intro b hb; have := of_mem_accAddrs hb; exact hi.globOwn b (by momega) (by momega)))
    refine malloc_bump hlive (hi.init_at h0 rfl (by decide)) (by show heapStart ≠ 0; decide) hsz hn
      hbig R0 _ (by keeps_tac hkeep) (by dc_simp []; decide) (by dc_simp [h13]) hal ?_
    intro R' Mt' H' hk' hp
    refine hk R' Mt' H' hk' ⟨hp.inv, ?_, fun a ha => ?_⟩
    · cases hp.res with
      | null e1 e2 e3 => exact .null e1 e2 e3
      | block b e1 e2 e3 e4 e5 => exact .block b e1 e2 e3 e4 fun a h1 h2 => AllocByte.of_init h0 (e5 a h1 h2)
    · rw [hp.frame a (fun h => ha (AllocByte.of_init h0 h))]
      refine imgM_store_miss _ _ ?_
      have : ¬ (2147601736 ≤ a ∧ a < 2147601752) := fun h => ha (.glob h.1 h.2)
      momega
  · intro hne
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, hbw] at hne
    have hne' : H.braw ≠ 0 := fun e => hne (by rw [e])
    refine malloc_bump hlive hi hne' hsz hn hbig R0 _ (by keeps_tac hkeep) ?_ ?_ hal hk
    · dc_simp [hbw]
    · dc_simp [h13]

/-- The first-fit scan at `0x80000998`: `a5` the block `c` of the free list
`pre ++ c :: post`, `a2` the link word before it, `a3` the rounded size. -/
theorem malloc_scan {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} (hi : HeapInv S Mt H)
    {n size : Nat} (hsz : size % 16 = 0) (hn : n ≤ size) (hbig : size < 2 ^ 63)
    (R0 : Nat → BitVec 64) (hal : (R0 1).toNat % 4 = 0) (hk : MallocK live S Q R0 Mt H n) :
    ∀ k (pre : List Blk) (c : Blk) (post : List Blk) (R : Nat → BitVec 64), post.length = k →
      H.free = pre ++ c :: post → R 15 = BitVec.ofNat 64 c.h →
      R 12 = BitVec.ofNat 64 (linkOf freeListAddr pre) → R 13 = BitVec.ofNat 64 size →
      Keeps mallocClob R R0 → DW live S Q 0x80000998#64 R Mt := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro pre c post R hlen hf h15 h12 h13 hkeep
  have hcb : c ∈ H.blocks := List.mem_append_left _ (by rw [hf]; simp)
  have fc := hi.blk hcb
  have hclo : 2147603920 ≤ c.h := fc.lo
  have hcfin : c.h + 16 + c.sz ≤ H.brk := fc.fin
  have htop : H.brk ≤ 2273312768 := fc.top
  have hcal := fc.al
  have hch : Chain Mt freeListAddr (pre ++ c :: post) := hf ▸ hi.links
  have hszc : ldv .ld Mt c.h = BitVec.ofNat 64 c.sz := hi.hdr c hcb
  have hnx : ldv .ld Mt (c.h + 8) = BitVec.ofNat 64 (headOf post) := (Chain.at pre hch).2
  have h1 : R 1 = R0 1 := hkeep.get 1
  have hcb' : c.h < 2 ^ 64 := by omega
  have hszc' : ldv .ld Mt (R 15).toNat = BitVec.ofNat 64 c.sz := by
    rw [h15, ofNat_toNat_lt hcb']; exact hszc
  have hnx' : ldv .ld Mt (R 15 + 8#64).toNat = BitVec.ofNat 64 (headOf post) := by
    rw [h15, ofNat_add_ofNat, ofNat_toNat_lt (by omega)]; exact hnx
  dx_run hlive
  · dc_simp [h15]; simp only [LdOK]; momega
  · dc_simp [h15]; intro b hb; have := of_mem_accAddrs hb; exact hi.own b (by momega) (by momega)
  · sx_norm; dc_simp [h15]; simp only [LdOK]; momega
  · sx_norm; dc_simp [h15]; intro b hb; have := of_mem_accAddrs hb; exact hi.own b (by momega) (by momega)
  · intro hlt
    dc_simp [h13, hszc'] at hlt
    dx_run hlive
    · intro h0
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hnx'] at h0
      cases post with
      | nil => exact malloc_top hlive hi hsz hn hbig R0 _ (by keeps_tac hkeep) (by dc_simp [h13]) hal hk
      | cons c' post' =>
        exfalso
        have hc'b : c' ∈ H.blocks := List.mem_append_left _ (by rw [hf]; simp)
        have := (hi.blk hc'b).lo; have := (hi.blk hc'b).fin; have := (hi.blk hc'b).top
        simp only [headOf] at h0
        rw [ofNat_eq_zero_iff (by bomega)] at h0; bomega
    · intro h0
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hnx'] at h0
      cases post with
      | nil => exact absurd rfl h0
      | cons c' post' =>
        have hc'b : c' ∈ H.blocks := List.mem_append_left _ (by rw [hf]; simp)
        have := (hi.blk hc'b).lo; have := (hi.blk hc'b).fin; have := (hi.blk hc'b).top
        refine ih post'.length (by simp at hlen; omega) (pre ++ [c]) c' post' _ rfl
          (by rw [hf]; simp) ?_ ?_ ?_ (by keeps_tac hkeep)
        · dc_simp [hnx']; rfl
        · dc_simp [h15, linkOf_snoc]
        · dc_simp [h13]
  · intro hge
    dc_simp [h13, hszc'] at hge
    have lw := hi.linkWord hf
    have hwlo := lw.lo; have hwhi := lw.hi; have hwal := lw.al
    have hA : (R 12).toNat = linkOf freeListAddr pre := by
      rw [h12, ofNat_toNat_lt (by momega)]
    dx_run hlive
    · dc_simp [hA]; simp only [StOK]; momega
    · dc_simp [hA]; intro b hb; have hb' := of_mem_accAddrs hb
      have := lw.own (b - linkOf freeListAddr pre) (by omega)
      rwa [Nat.add_sub_cancel' hb'.1] at this
    · dc_simp [h1, hal]
    · rw [h1]
      refine hk _ _ _ (by keeps_tac hkeep) ⟨hi.take_at hf hA hnx', ?_, fun a ha => ?_⟩
      · refine .block c (by dc_simp [h15, Blk.pay]) (by omega) rfl (fun d hd => ?_) fun a h1 h2 => ?_
        · rw [hf]; simp only [List.mem_append, List.mem_cons] at hd ⊢
          rcases hd with h | h
          · exact .inl h
          · exact .inr (.inr h)
        · by_cases h3 : a < c.pay
          · exact .hdr c hcb h1 h3
          · exact .freePay c (by rw [hf]; simp) (by omega) h2
      · refine imgM_store_miss _ _ ?_
        rw [hA]
        refine Classical.byContradiction fun hc => ha ?_
        have := lw.alloc (a - linkOf freeListAddr pre) (by omega)
        rwa [Nat.add_sub_cancel' (by omega)] at this

/-- `malloc`'s rounded size. -/
abbrev mallocSize (n : Nat) : Nat := (n + 15) / 16 * 16

/-- **`malloc(n)`** at `0x8000096c`, `n < 2^62`, on a heap satisfying
`HeapInv`: `MallocPost` — the invariant for the new heap, `NULL` or a fresh
live block of at least `n` bytes, and only allocator bytes changed; clobbers
`a0`, `a2`–`a5`. -/
theorem malloc_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} (hi : HeapInv S Mt H) {n : Nat}
    (hn : n < 2 ^ 62) (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 n)
    (hal : (R 1).toNat % 4 = 0) (hk : MallocK live S Q R Mt H n) :
    DW live S Q 0x8000096c#64 R Mt := by
  have hfl : ldv .ld Mt 2147601736 = BitVec.ofNat 64 (headOf H.free) := hi.links.head
  have hms : mallocSize n < 2 ^ 63 := by unfold mallocSize; omega
  have hsz : R 10 + 15#64 &&& 18446744073709551600#64 = BitVec.ofNat 64 (mallocSize n) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_and_m16, h10, ofNat_add_ofNat, ofNat_toNat_lt (x := n + 15) (by omega),
      ofNat_toNat_lt (x := mallocSize n) (by omega)]
  have hsz16 : mallocSize n % 16 = 0 := by unfold mallocSize; omega
  have hnle : n ≤ mallocSize n := by unfold mallocSize; omega
  have hsz' : BitVec.ofNat 64 n + 15#64 &&& 18446744073709551600#64 =
      BitVec.ofNat 64 (mallocSize n) := h10 ▸ hsz
  dx_run hlive
  · intro h
    exfalso
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h10, hsz',
      ofNat_toNat_lt (x := mallocSize n) (by omega), ofNat_toNat_lt (x := n) (by omega)] at h
    omega
  · intro _
    dx_run hlive
    · sx_norm; intro b hb; have := of_mem_accAddrs hb; exact hi.globOwn b (by momega) (by momega)
    · intro h0
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hfl] at h0
      have hnil : H.free = [] := by
        cases hf : H.free with
        | nil => rfl
        | cons c post =>
          exfalso
          have hcb : c ∈ H.blocks := List.mem_append_left _ (by rw [hf]; simp)
          have := (hi.blk hcb).lo; have := (hi.blk hcb).fin; have := (hi.blk hcb).top
          rw [hf] at h0; simp only [headOf] at h0
          rw [ofNat_eq_zero_iff (by bomega)] at h0; bomega
      exact malloc_top hlive hi hsz16 hnle hms R _ (by keeps_tac Keeps.refl _ _) (by dc_simp [hsz]) hal hk
    · intro h0
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hfl] at h0
      cases hf : H.free with
      | nil => rw [hf] at h0; exact absurd rfl h0
      | cons c post =>
        have hcb : c ∈ H.blocks := List.mem_append_left _ (by rw [hf]; simp)
        have := (hi.blk hcb).lo; have := (hi.blk hcb).fin; have := (hi.blk hcb).top
        dx_run hlive at 0x80000998
        refine malloc_scan hlive hi hsz16 hnle hms R hal hk post.length [] c post _ rfl
          (by rw [hf]; rfl) ?_ ?_ ?_ (by keeps_tac Keeps.refl _ _)
        · dc_simp [hfl, hf, headOf]
        · sx_norm; rfl
        · dc_simp [hsz]

/-! ## `free` (`0x80000a0c`)

```
80000a0c beqz a0,80000a28 ; 80000a10 auipc a4,0x1c ; 80000a14 ld a4,824(a4)
80000a18 addi a5,a0,-16 ; 80000a1c sd a4,-8(a0) ; 80000a20 auipc a4,0x1c
80000a24 sd a5,808(a4) ; 80000a28 ret
```
-/

/-- `free`'s postcondition: the live block `b` (split out of the live list as
`lpre ++ b :: lpost`) heads the free list, and only allocator bytes changed. -/
structure FreePost (S : Nat → Prop) (Mt Mt' : Mem) (H H' : Heap) (b : Blk)
    (lpre lpost : List Blk) : Prop where
  inv : HeapInv S Mt' H'
  free : H'.free = b :: H.free
  live : H'.live = lpre ++ lpost
  frame : ∀ a, ¬ AllocByte H a → imgM Mt' a = imgM Mt a

/-- `HeapInv.push` at the addresses and values of the machine's stores. -/
theorem HeapInv.push_at {S : Nat → Prop} {Mt : Mem} {H : Heap} (hi : HeapInv S Mt H)
    {lpre : List Blk} {b : Blk} {lpost : List Blk} (hl : H.live = lpre ++ b :: lpost)
    {A B : Nat} {v w : BitVec 64} (hA : A = b.h + 8) (hv : v = BitVec.ofNat 64 (headOf H.free))
    (hB : B = freeListAddr) (hw : w = BitVec.ofNat 64 b.h) :
    HeapInv S (writeLog (writeLog Mt [(A, 8, v)]) [(B, 8, w)])
      ⟨H.braw, b :: H.free, lpre ++ lpost⟩ := by
  subst hA hv hB hw; exact hi.push hl

/-- **`free(p)`** at `0x80000a0c` for the payload `p` of the live block `b`:
`FreePost`; clobbers `a4`, `a5`. -/
theorem free_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {H : Heap} (hi : HeapInv S Mt H)
    {lpre : List Blk} {b : Blk} {lpost : List Blk} (hl : H.live = lpre ++ b :: lpost)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofNat 64 b.pay) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' Mt', Keeps [14, 15] R' R →
      FreePost S Mt Mt' H ⟨H.braw, b :: H.free, lpre ++ lpost⟩ b lpre lpost →
      DW live S Q (R 1) R' Mt') :
    DW live S Q 0x80000a0c#64 R Mt := by
  have hbb : b ∈ H.blocks := List.mem_append_right _ (by rw [hl]; simp)
  have fb := hi.blk hbb
  have hblo : 2147603920 ≤ b.h := fb.lo
  have hbfin := fb.fin
  have hbtop : H.brk ≤ 2273312768 := fb.top
  have hbal := fb.al
  have hfl : ldv .ld Mt 2147601736 = BitVec.ofNat 64 (headOf H.free) := hi.links.head
  have hA : (R 10 + 18446744073709551608#64).toNat = b.h + 8 := by
    rw [h10, ofNat_add_ofNat, BitVec.toNat_ofNat]; bomega
  have hw : R 10 + 18446744073709551600#64 = BitVec.ofNat 64 b.h := by
    rw [h10, ofNat_add_ofNat]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; bomega
  dx_run hlive
  · intro h0; exfalso; rw [h10, ofNat_eq_zero_iff (by bomega)] at h0; bomega
  · intro _
    dx_run hlive
    · sx_norm; intro b hb; have := of_mem_accAddrs hb; exact hi.globOwn b (by momega) (by momega)
    · sx_norm; rw [hA]; simp only [StOK]; bomega
    · sx_norm; rw [hA]; intro x hx; have := of_mem_accAddrs hx; exact hi.own x (by bomega) (by bomega)
    · sx_norm; intro b hb; have := of_mem_accAddrs hb; exact hi.globOwn b (by momega) (by momega)
    · refine hk _ _ (by keeps_tac Keeps.refl _ _) ⟨hi.push_at hl hA hfl rfl hw, rfl, rfl, fun a ha => ?_⟩
      have h1 : ¬ (2147601736 ≤ a ∧ a < 2147601752) := fun h => ha (.glob h.1 h.2)
      have h2 : ¬ (b.h ≤ a ∧ a < b.pay) := fun h => ha (.hdr b hbb h.1 h.2)
      rw [imgM_store_miss _ _ (by momega), imgM_store_miss _ _ (by rw [hA]; bomega)]

/-- **`free(NULL)`** at `0x80000a0c`: returns at once. -/
theorem free_null_spec {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) (R : Nat → BitVec 64) (h10 : R 10 = 0#64)
    (hal : (R 1).toNat % 4 = 0) (hk : DW live S Q (R 1) R Mt) :
    DW live S Q 0x80000a0c#64 R Mt := by
  dx_run hlive
  · intro _; dx_run hlive; exact hk
  · intro h; exact absurd h10 h

end Dc.Mach
