import Dc.Mach.Bc.SqrtEntry
import Dc.Mach.Bc.OutLong
import Dc.BcModel.OutBase

/-!
# `bc_out_num`'s contract and state (`lib/number.c`, `0x80006f3c`)

    bc_out_num (num, o_base, out_char, leading_zero):
      num negative: out_char ('-')
      num zero: out_char ('0')                                  (a tail call)
      o_base = 10: the integer digits (none for a lone `0`), then `.` and
        the fraction digits
      otherwise: int_part = num / 1, frac_part = num - int_part, both made
        positive; base = o_base, max_o_digit = o_base - 1; push the digits of
        int_part (bc_modulo, malloc'd cells, bc_divide) and print them from the
        stack; then `.` and the fraction digits while t = base ^ i has at most
        `scale` digits; free the five numbers

`dc` passes `leading_zero = 0` (`dc_out_num`), so the branches that print a
leading `0` are not taken (`OnCtx.lz`).

The callback `out_char` is a `CharFn`: a call changes the stack below its
`sp` and a footprint `G` among the globals, and extends the characters sent
(`I`). The frame is 176 bytes; its words `+16` … `+56` hold `int_part`,
`frac_part`, `base`, `cur_dig`, `t_num` and `max_o_digit`.

- `CharFn`, `CharFn.cb`: the callback, and the `CharCb` it gives `bc_out_long`
  with the globals frozen (`Frozen`).
- `OnCtx`/`OnArgs`/`OnK`: the contract.
- `OnAt`: inside the frame.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## The callback -/

/-- **A character callback with a footprint** at `f`: from `I cs t M` (the
characters `cs` sent so far, the console `t`, the memory), a call with the
byte `c` in `a0`, using `d` bytes below `sp`, returns to `ra` with
`I (cs ++ [c])`, keeping `sp` and `s0`–`s11`, and changing only the `d` bytes
below `sp` and the footprint `G`, which lies among the globals apart from the
heap's and the number constants (`constBytes`); `I` reads only `G`. -/
structure CharFn (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (f : BitVec 64) (d : Nat) (G : Nat → Prop) (I : List Nat → String → Mem → Prop) : Prop where
  call : ∀ cs c t sp (R : Nat → BitVec 64) M, I cs t M → StackFrame S sp d →
    heapEnd + d ≤ sp → R 2 = BitVec.ofNat 64 sp → R 10 = BitVec.ofNat 64 c → c < 256 →
    (R 1).toNat % 4 = 0 →
    (∀ R' M' t', Keeps cClob R' R → I (cs ++ [c]) t' M' →
      (∀ a, ¬ G a → (a < sp - d ∨ sp ≤ a) → imgM M' a = imgM M a) →
      DWO live S Q t' (R 1) R' M') →
    DWO live S Q t f R M
  off : ∀ a, G a → a < heapStart ∧ OutHeap a ∧ ¬ constBytes a ∧
    ¬ (mulBaseAddr ≤ a ∧ a < mulBaseAddr + 4)
  /-- the invariant reads only the footprint -/
  stab : ∀ cs t M M', I cs t M → (∀ a, G a → imgM M' a = imgM M a) → I cs t M'

/-- Below the heap's end, nothing outside `G` changed since `Mb`. -/
def Frozen (G : Nat → Prop) (Mb M : Mem) : Prop := ∀ a, ¬ G a → a < heapEnd → imgM M a = imgM Mb a

theorem Frozen.refl (G : Nat → Prop) (M : Mem) : Frozen G M M := fun _ _ _ => rfl

/-- **The `CharCb` a `CharFn` gives** (`bc_out_long`'s callback contract), its
invariant carrying the globals frozen since `Mb`. -/
theorem CharFn.cb {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {f : BitVec 64} {d : Nat} {G : Nat → Prop} {I : List Nat → String → Mem → Prop}
    (h : CharFn live S Q f d G I) (Mb : Mem) :
    CharCb live S Q f d (fun cs t M => I cs t M ∧ Frozen G Mb M) where
  call := fun cs c t sp R M hI hsf hab h2 h10 hc hal hk =>
    h.call cs c t sp R M hI.1 hsf hab h2 h10 hc hal fun R' M' t' hk' hI' hfr =>
      hk R' M' t' hk' ⟨hI', fun a hg ha => (hfr a hg (.inl (by omega))).trans (hI.2 a hg ha)⟩
        fun a ha => hfr a (fun hg => by
          have := (h.off a hg).1; simp only [heapStart, heapEnd] at this hab; omega) (.inr ha)

/-- `bc_out_long`'s stack writes keep that invariant. -/
theorem CharFn.olStable {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {f : BitVec 64} {d : Nat} {G : Nat → Prop} {I : List Nat → String → Mem → Prop}
    (h : CharFn live S Q f d G I) (Mb : Mem) {sp : Nat} (hab : heapEnd + 416 ≤ sp) :
    OLStable (fun cs t M => I cs t M ∧ Frozen G Mb M) sp := fun cs t M M' hI hm =>
  ⟨h.stab cs t M M' hI.1 fun a hg => hm a fun hf => by
      have := (h.off a hg).1; simp only [heapStart, heapEnd, frameIn] at this hab hf; omega,
    fun a hg ha => (hm a fun hf => by simp only [frameIn, heapEnd] at hf ha hab; omega).trans
      (hI.2 a hg ha)⟩

/-! ## The contract -/

/-- `bc_out_num`'s context: a caller's window with room for its 176-byte
frame, the callees below it and the callback's `d` bytes; the callback
pointer (`a2`) 4-aligned and `leading_zero` (`a3`) zero. -/
structure OnCtx (S : Nat → Prop) (R0 : Nat → BitVec 64) (sp W d : Nat) : Prop where
  cc : CallerCtx S sp W
  big : 176 + 512 + rmStack (2 ^ 30) + d ≤ W
  dlo : 16 ≤ d
  sp0 : R0 2 = BitVec.ofNat 64 sp
  al : (R0 1).toNat % 4 = 0
  fal : (R0 12).toNat % 4 = 0
  lz : R0 13 = 0#64

/-- The facts of `OnCtx` as `omega` sees them. -/
macro "on_facts " cx:term : tactic =>
  `(tactic| (cf_facts ($cx).cc
             have _hW := ($cx).big
             have _hd := ($cx).dlo
             have _hrm : 224 ≤ rmStack (2 ^ 30) := by unfold rmStack; omega))

/-- The number `x` of the caller's heap `L` in base `ob`: `_zero_` (`z`) and
`_one_` (`o`) in `L` at their globals, sizes small enough for the callees,
every number referenced, owning its buffer and with room for eight more
references. -/
structure OnArgs (S : Nat → Prop) (M : Mem) (L : List NumObj) (x z o : NumObj) (ob : Nat) :
    Prop where
  mx : x ∈ L
  nx : x.rep.Norm
  lenx : 1 ≤ x.rep.len
  size : x.rep.len + x.rep.scale < 2 ^ 20
  refs : ∀ y ∈ L, y.rep.refs + 8 < 2 ^ 31
  live : ∀ y ∈ L, 1 ≤ y.rep.refs
  owns : ∀ y ∈ L, y.Owns
  mz : z ∈ L
  zero : KZero M z (2 ^ 30 + 8)
  mo : o ∈ L
  one : ldv .ld M oneAddr = BitVec.ofNat 64 o.rep.p
  oneNum : o.rep.num = Dc.Num.one
  oneNorm : o.rep.Norm
  oneLen : 1 ≤ o.rep.len
  mulBase : ldv .lw M mulBaseAddr = BitVec.ofNat 64 80
  obLo : 2 ≤ ob
  obHi : ob < 2 ^ 31

/-- `bc_out_num`'s continuations: back at `ra` with the characters `target`
sent and the caller's heap `L` as it was (its allocator and dead chain
changed), off the heap only `G` and the window changed; or `out_of_memory`
at any console. -/
structure OnK (live S : Nat → Prop) (X : Raws) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (I : List Nat → String → Mem → Prop) (G : Nat → Prop) (R0 : Nat → BitVec 64) (M0 : Mem)
    (L : List NumObj) (sp W : Nat) (target : List Nat) : Prop where
  ret : ∀ R' M' t' H' F', Keeps cClob R' R0 → I target t' M' → BcHeap S X M' H' F' L →
    (∀ a, OutHeap a → ¬ G a → ¬ frameIn sp W a → imgM M' a = imgM M0 a) →
    DWO live S Q t' (R0 1) R' M'
  oom : ∀ t' R' M' sp', sp - W ≤ sp' → sp' ≤ sp → R' 2 = BitVec.ofNat 64 sp' →
    (∀ a, OutHeap a → ¬ G a → ¬ frameIn sp W a → imgM M' a = imgM M0 a) →
    DWO live S Q t' 0x80002bcc#64 R' M'

/-! ## Inside `bc_out_num` -/

/-- The registers `bc_out_num` changes before its epilogue. -/
abbrev onAll : List Nat :=
  [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31]

/-- Inside `bc_out_num`: `sp` lowered by 176, the saved registers in the
frame, the callback in `s1`, and off the heap only `G` and the window
changed. -/
structure OnAt (S : Nat → Prop) (G : Nat → Prop) (Mt0 M : Mem) (R0 R : Nat → BitVec 64)
    (sp W : Nat) (slots : List (Nat × Nat)) : Prop where
  r2 : R 2 = BitVec.ofNat 64 (sp - 176)
  saved : SavedWords M (sp - 176) slots R0
  keep : Keeps onAll R R0
  cb : R 9 = R0 12
  out : ∀ a, OutHeap a → ¬ G a → ¬ frameIn sp W a → imgM M a = imgM Mt0 a

/-- Through a change of registers outside the saved ones and `s1`. -/
theorem OnAt.regs {S G : Nat → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64} {sp W : Nat}
    {slots : List (Nat × Nat)} (h : OnAt S G Mt0 M R0 R sp W slots) {ks : List Nat}
    (hk : Keeps ks R' R) (hks : ∀ z ∈ ks, z ∈ onAll ∧ z ≠ 2 ∧ z ≠ 9 := by decide) :
    OnAt S G Mt0 M R0 R' sp W slots :=
  { h with
    r2 := by rw [hk.get 2 fun hm => (hks 2 hm).2.1 rfl]; exact h.r2
    keep := (hk.mono fun z hz => (hks z hz).1).trans h.keep
    cb := by rw [hk.get 9 fun hm => (hks 9 hm).2.2 rfl]; exact h.cb }

/-- Through a callback call at the frame's `sp`. -/
theorem OnAt.char {S G : Nat → Prop} {Mt0 M M' : Mem} {R0 R R' : Nat → BitVec 64} {sp W d : Nat}
    {slots : List (Nat × Nat)} (h : OnAt S G Mt0 M R0 R sp W slots)
    (hlo : ∀ p ∈ slots, 0 ≤ p.2 := by decide) (htop : ∀ p ∈ slots, p.2 + 8 ≤ 176 := by decide)
    (hsp : 176 + d ≤ W) (hab : heapEnd + W ≤ sp) (hG : ∀ a, G a → a < heapStart)
    (hk : Keeps cClob R' R)
    (hfr : ∀ a, ¬ G a → (a < sp - 176 - d ∨ sp - 176 ≤ a) → imgM M' a = imgM M a) :
    OnAt S G Mt0 M' R0 R' sp W slots where
  r2 := by rw [hk.get 2]; exact h.r2
  saved := h.saved.transport hlo htop fun a h1 _ => hfr a (fun hg => by
    have := hG a hg; simp only [heapStart, heapEnd] at this hab; omega) (.inr (by omega))
  keep := (hk.mono (by decide)).trans h.keep
  cb := by rw [hk.get 9]; exact h.cb
  out := fun a ha hg hf => by
    rw [hfr a hg (by simp only [frameIn] at hf; omega)]; exact h.out a ha hg hf

/-- The prologue's saved registers (`s1`, `s2`, `s5`, `s7`, `ra`, `s4`). -/
abbrev onSlots0 : List (Nat × Nat) := [(9, 152), (18, 144), (21, 120), (23, 104), (1, 168), (20, 128)]

/-- With `s6`, `s3` and `s0` saved (`0x80006f90`, `0x80006f98`, `0x80006fc8`). -/
abbrev onSlots2 : List (Nat × Nat) :=
  [(8, 160), (19, 136), (22, 112), (9, 152), (18, 144), (21, 120), (23, 104), (1, 168), (20, 128)]

/-- With `s8`–`s11` saved too (the branch for a base other than 10). -/
abbrev onSlots3 : List (Nat × Nat) :=
  [(25, 88), (26, 80), (24, 96), (27, 72), (8, 160), (19, 136), (22, 112), (9, 152), (18, 144),
    (21, 120), (23, 104), (1, 168), (20, 128)]

/-- A save of `r` (the caller's value `v`) at `sp - 176 + o`. -/
theorem OnAt.store {S G : Nat → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64} {sp W : Nat}
    {slots : List (Nat × Nat)} (h : OnAt S G Mt0 M R0 R sp W slots) (r o : Nat) {v : BitVec 64}
    (hv : v = R0 r) (hd : ∀ p ∈ slots, p.2 + 8 ≤ o ∨ o + 8 ≤ p.2 := by decide)
    (ho : o + 8 ≤ 176) (hsp : 176 ≤ sp) (hW : 176 ≤ W) :
    OnAt S G Mt0 (writeLog M [(sp - 176 + o, 8, v)]) R0 R sp W ((r, o) :: slots) :=
  { h with
    saved := by rw [hv]; exact h.saved.store r o hd
    out := fun a ha hg hf => by
      rw [imgM_store_miss _ _ (by simp only [frameIn] at hf; omega)]; exact h.out a ha hg hf }

/-- A store into the frame keeps the heap. -/
theorem BcHeap.frameStore {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    (hb : BcHeap S X M H F L) {sp o : Nat} (v : BitVec 64) (hsp : heapEnd + 176 ≤ sp)
    (ho : o + 8 ≤ 176) : BcHeap S X (writeLog M [(sp - 176 + o, 8, v)]) H F L :=
  hb.out_frame (P := fun a => sp - 176 + o ≤ a ∧ a < sp - 176 + o + 8)
    (fun a hp => imgM_store_miss _ _ (by omega)) (fun a hp => outHeap_of_ge (by omega))

/-- A store above the heap keeps the callback's invariant. -/
theorem CharFn.frameStore {live S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {f : BitVec 64} {d : Nat} {G : Nat → Prop} {I : List Nat → String → Mem → Prop}
    (h : CharFn live S Q f d G I) {cs : List Nat} {t : String} {M : Mem} (hI : I cs t M)
    {b : Nat} (v : BitVec 64) (hb : heapEnd ≤ b) : I cs t (writeLog M [(b, 8, v)]) :=
  h.stab cs t M _ hI fun a hg => imgM_store_miss _ _ (.inl (by
    have := (h.off a hg).1; simp only [heapStart, heapEnd] at this hb; omega))

/-- The callback's frame below `bc_out_num`'s. -/
theorem OnCtx.cbFrame {S : Nat → Prop} {R0 : Nat → BitVec 64} {sp W d : Nat}
    (cx : OnCtx S R0 sp W d) : StackFrame S (sp - 176) d := by
  on_facts cx
  have hsf := cx.cc.frame
  have := hsf.lo; have := hsf.hi; have := hsf.al
  exact ⟨fun a h1 h2 => hsf.own a (by omega) (by omega), by omega, by omega, by omega⟩

/-- **The callback from inside the frame**: `out_char (c)` with `sp` at the
frame, the heap and the frame's words kept. -/
theorem on_call {live S : Nat → Prop} {X : Raws}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {G : Nat → Prop} {I : List Nat → String → Mem → Prop} {Mt0 M : Mem}
    {R0 R : Nat → BitVec 64} {sp W d c : Nat} {slots : List (Nat × Nat)} {H : Heap}
    {F : List Blk} {L : List NumObj} {cs : List Nat} {t : String}
    (cb : CharFn live S Q (R0 12) d G I) (cx : OnCtx S R0 sp W d)
    (st : OnAt S G Mt0 M R0 R sp W slots)
    (hlo : ∀ p ∈ slots, 0 ≤ p.2 := by decide) (htop : ∀ p ∈ slots, p.2 + 8 ≤ 176 := by decide)
    (hb : BcHeap S X M H F L) (hI : I cs t M) (h10 : R 10 = BitVec.ofNat 64 c) (hc : c < 256)
    (h1 : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' t', Keeps cClob R' R → I (cs ++ [c]) t' M' → OnAt S G Mt0 M' R0 R' sp W slots →
      BcHeap S X M' H F L → (∀ a, ¬ G a → a < heapEnd → imgM M' a = imgM M a) →
      DWO live S Q t' (R 1) R' M') :
    DWO live S Q t (R0 12) R M := by
  on_facts cx
  have hG : ∀ a, G a → a < heapStart := fun a hg => (cb.off a hg).1
  refine cb.call cs c t (sp - 176) R M hI cx.cbFrame (by simp only [heapEnd]; omega) st.r2 h10 hc h1
    fun R' M' t' hk' hI' hfr => hk R' M' t' hk' hI'
      (st.char hlo htop (by omega) (by simp only [heapEnd]; omega) hG hk' hfr)
      (hb.out_frame (P := fun a => G a ∨ frameIn (sp - 176) d a)
        (fun a hp => hfr a (fun hg => hp (.inl hg)) (by
          simp only [frameIn, not_or, not_and, Nat.not_lt] at hp ⊢
          by_cases h : sp - 176 - d ≤ a
          · exact .inr (hp.2 h)
          · exact .inl (by omega)))
        (fun a ha => by
          rcases ha with hg | hf
          · exact (cb.off a hg).2.1
          · apply outHeap_of_ge; simp only [frameIn, heapEnd] at hf ⊢; omega))
      fun a hg ha => hfr a hg (.inl (by simp only [heapEnd] at ha; omega))

/-- **The epilogue** at `0x80007434`: `s0`–`s7` and `ra` restored (`s8`–`s11`
already the caller's), `sp` raised, the return. -/
theorem on_epi {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hlive : ∀ p ∈ dcText, live p.1)
    {M : Mem} {R0 R : Nat → BitVec 64} {sp W d : Nat} (cx : OnCtx S R0 sp W d)
    (sv : SavedWords M (sp - 176) onSlots2 R0) (h2 : R 2 = BitVec.ofNat 64 (sp - 176))
    (hkp : Keeps onAll R R0) (hs : ∀ z ∈ [24, 25, 26, 27], R z = R0 z)
    (hk : ∀ R', Keeps cClob R' R0 → DW live S Q (R0 1) R' M) :
    DW live S Q 0x80007434#64 R M := by
  on_facts cx
  have hsf := cx.cc.frame
  have hal := cx.al
  have h24 := hs 24 (by simp); have h25 := hs 25 (by simp); have h26 := hs 26 (by simp)
  have h27 := hs 27 (by simp)
  have g1 := sv.get 1 168; have g8 := sv.get 8 160; have g9 := sv.get 9 152
  have g18 := sv.get 18 144; have g19 := sv.get 19 136; have g20 := sv.get 20 128
  have g21 := sv.get 21 120; have g22 := sv.get 22 112; have g23 := sv.get 23 104
  bc_run hlive hsf [h2, g1, g8, g9, g18, g19, g20, g21, g22, g23]
  all_goals first | exact frame_acc hsf (by omega) (by omega) | exact hal | skip
  refine hk _ (Keeps.unwind (all := onAll)
    (saved := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) ?_
    (hk := by keeps_tac Keeps.refl _ _) (hkp := hkp))
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | (bsimp [cx.sp0, h2, g1, g8, g9, g18, g19, g20, g21, g22, g23, h24, h25, h26, h27]; done)
    | skip
  rw [upd_same, cx.sp0, show sp - 176 + 176 = sp by omega]

end Dc.Mach
