import Dc.Mach.BootInit
import Dc.Mach.MainScript
import Dc.Mach.DcMemfail

/-!
# `main` up to `dc_evalstr` (M11)

```
80000b00 addi sp,sp,-32 ; 80000b04 auipc a5 ; 80000b08 addi a5 = "dc" ; 80000b0c sd ra,24(sp)
80000b10 auipc a4 ; 80000b14 sd a5,progname
80000b18 jal dc_math_init ; 80000b1c jal dc_string_init ; 80000b20 jal dc_register_init
80000b24 jal dc_array_init ; 80000b28 … 80000b30 jal strlen (script)
80000b34 mv a1,a0 ; 80000b38 auipc a0 ; 80000b3c addi a0 = script ; 80000b40 jal dc_makestring
80000b44 sd a0,0(sp) ; 80000b48 mv a0,sp ; 80000b4c sd a1,8(sp) ; 80000b50 jal dc_evalstr
```

From the fresh boot `BootPre` (`.bss` zero, `.data`'s dc words at their
initial values, the heap empty, the script at `dc_script + 16`), `main_spec`
runs to `dc_evalstr`'s entry with `BootEval`: the state relation `DcAt` for
`St.init` over the ghost `bootG o` (the script's string object `o`, its one
reference the handle `(DC_STRING, o)` in `main`'s frame, `a0` pointing at
it). The state is built by `boot_dcAt` from `bc_init_numbers`'s three
constants (`InitPost`) and the zeroed globals. `bc_init_numbers`' out of
memory ends in `dc_memfail_spec` (the `progname` word was just stored);
`dc_makestring`'s goes to the caller's `hoom` (`OomAt`), whose `progname`
supplier is the open M11 item of `DcMemfail.lean`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- A load of zero bytes reads `0`. -/
theorem ldv_zero {M : Mem} (k : MKind) (hk : k = .ld ∨ k = .lw) {a : Nat}
    (h : ∀ j, j < widthOfM k → imgM M (a + j) = 0#8) : ldv k M a = 0#64 := by
  unfold ldv bytesAt
  rw [List.map_congr_left (g := fun _ => 0#8) fun j hj => h j (List.mem_range.mp hj)]
  rcases hk with rfl | rfl <;> rfl

/-- **The fresh boot** at `main`'s entry (memory `M`, frame `W` bytes below
`sp`): `.bss` (`free_list` … `__bss_end`) zero, `.data`'s dc words at their
initial values, the heap empty, the script `s` (no `NUL`) at
`dc_script + 16`, and the bytes dc owns. -/
structure BootPre (S : Nat → Prop) (M : Mem) (sp W : Nat) (s : List Nat) : Prop where
  heap : HeapInv S M ⟨0, [], []⟩
  bss : ∀ a, freeListAddr ≤ a → a < heapStart → imgM M a = 0#8
  ibase : ldv .lw M ibaseAddr = BitVec.ofNat 64 10
  obase : ldv .lw M obaseAddr = BitVec.ofNat 64 10
  lineMax : ldv .lw M lineMaxAddr = BitVec.ofInt 64 (-1)
  outFd : ldv .lw M stdFilesAddr = BitVec.ofNat 64 1
  errFd : ldv .lw M (stdFilesAddr + 4) = BitVec.ofNat 64 2
  glob : ∀ a, DcGlob a → S a
  col : ∀ a, outColAddr ≤ a → a < outColAddr + 4 → S a
  bcFree : ∀ a, bcFreeAddr ≤ a → a < bcFreeAddr + 8 → S a
  frame : StackFrame S sp W
  room : heapEnd + W ≤ sp
  big : 400 ≤ W
  script : OwnedCStr S M scriptAddr s.length
  text : ∀ i, i < s.length → imgM M (scriptAddr + i) = BitVec.ofNat 8 (s.getD i 0)
  byte : ∀ c ∈ s, c < 256
  len : s.length < 8192

/-- The ghost of the state `main` hands to `dc_evalstr`: the script's string
object `o` and nothing else. -/
def bootG (o : List StrObj) : DcG := ⟨[], fun _ => [], o, none, []⟩

@[simp] theorem bootG_vals (o : List StrObj) : (bootG o).vals = [] := by
  simp [DcG.vals, bootG]

@[simp] theorem bootG_blocks (o : List StrObj) :
    (bootG o).blocks = o.flatMap (fun o => [o.hb, o.tb]) := by
  simp [DcG.blocks, bootG]

/-- **The fresh state.** `bc_init_numbers`' three constants as the whole
number heap, the globals as `DcView` reads them for `St.init`: dc holds
`St.init` with no blocks and no handles. -/
theorem boot_dcAt {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk}
    {z o t : NumObj} (hb : BcHeap S X M H F [t, o, z])
    (hz : z.rep = zeroRep z.sb.pay z.db.pay 1 0)
    (ho : o.rep = { zeroRep o.sb.pay o.db.pay 1 0 with ds := [1] })
    (ht : t.rep = { zeroRep t.sb.pay t.db.pay 1 0 with ds := [2] })
    (hv : DcView M (bootG []) ⟨z, o, t⟩ St.init) (hg : ∀ a, DcGlob a → S a)
    (hc : ∀ a, outColAddr ≤ a → a < outColAddr + 4 → S a) :
    DcAt S M H F [t, o, z] ⟨z, o, t⟩ (bootG []) [] St.init := by
  have hzo : z.rep.p ≠ o.rep.p := fun e => by
    have := hb.eq_of_p (by simp) (by simp) e
    have e2 := congrArg (fun x : NumObj => x.rep.ds) this
    simp only [hz, ho, zeroRep] at e2; simp at e2
  have hzt : z.rep.p ≠ t.rep.p := fun e => by
    have := hb.eq_of_p (by simp) (by simp) e
    have e2 := congrArg (fun x : NumObj => x.rep.ds) this
    simp only [hz, ht, zeroRep] at e2; simp at e2
  have hot : o.rep.p ≠ t.rep.p := fun e => by
    have := hb.eq_of_p (by simp) (by simp) e
    have e2 := congrArg (fun x : NumObj => x.rep.ds) this
    simp only [ho, ht, zeroRep] at e2; simp at e2
  have hrefs : ∀ x ∈ [t, o, z], x.rep.refs = 1 := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*, zeroRep]
  refine
    { heap := hb.subRaw (fun b hb' => by simp [DcG.raws] at hb') fun b hb' => by
        simp [DcG.raws] at hb'
      nodup := by simp
      view := hv
      den := ?_
      glob := hg
      col := hc }
  refine
    { stk := .nil
      regs := fun _ _ => .nil
      regsHi := fun _ _ => ⟨rfl, rfl⟩
      hsDen := fun _ h => absurd h List.not_mem_nil
      owns := ?_
      norm := ?_
      pos := ?_
      numRefs := ?_
      strRefs := fun _ h => absurd h List.not_mem_nil
      live := fun x hx => Nat.le_of_eq (hrefs x hx).symm
      lkLen := by simp [bootG]
      lkIn := fun _ h => absurd h List.not_mem_nil
      mz := by simp
      mo := by simp
      mt := by simp
      zv := by simp [NumRep.num, hz, zeroRep, Num.zero, dval]
      ov := by simp [NumRep.num, ho, zeroRep, Num.one, dval]
      tv := by simp [NumRep.num, ht, zeroRep, dval]
      ibase := by decide
      obase := by decide
      scale := by decide
      unwind := by decide
      lbuf := fun _ h => absurd h (by simp [bootG]) }
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [NumObj.Owns, *, zeroRep]
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [NumRep.Norm, *, zeroRep]
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*, zeroRep]
  · intro x hx
    rw [hrefs x hx]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [bootG_vals, List.nil_append, List.count_nil, Nat.zero_add, BcConsts.cnt]
    rcases hx with rfl | rfl | rfl <;>
      simp [List.countP_cons, bootG, hzo, hzt, hot, Ne.symm hzo, Ne.symm hzt, Ne.symm hot]

/-- The `progname` word. -/
abbrev PnWord (a : Nat) : Prop := prognameAddr ≤ a ∧ a < prognameAddr + 8

/-- The empty number heap of the fresh boot. -/
theorem BootPre.bcHeap {S : Nat → Prop} {M : Mem} {sp W : Nat} {s : List Nat}
    (h : BootPre S M sp W s) (M' : Mem) : BcHeap S ⟨[], M'⟩ M ⟨0, [], []⟩ [] [] where
  heap := h.heap
  dead := .nil (ldv_zero .ld (.inl rfl) fun j hj => h.bss _
    (by simp only [widthOfM] at hj; simp only [freeListAddr, bcFreeAddr]; omega)
    (by simp only [widthOfM] at hj; simp only [heapStart, bcFreeAddr]; omega))
  deadLive _ h := absurd h List.not_mem_nil
  nums _ h := absurd h List.not_mem_nil
  blocks _ h := absurd h List.not_mem_nil
  distinct := List.nodup_nil
  views := .nil
  globOwn := h.bcFree
  raw := ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩

local macro_rules | `(tactic| sx_side) => `(tactic| dc_side)

/-- **`main` after its initialisers** (`0x80000b28`): the fresh state over
`bc_init_numbers`' constants, `main`'s 32-byte frame with `ra` saved, the
callee-saved registers kept, every byte off the heap, the globals and the
frame as at entry `M0`. -/
structure MainMid (S : Nat → Prop) (sp W : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem)
    (H : Heap) (F : List Blk) (L : List NumObj) (C : BcConsts) : Prop where
  dc : DcAt S M H F L C (bootG []) [] St.init
  r2 : R 2 = BitVec.ofNat 64 (sp - 32)
  ra : ldv .ld M (sp - 8) = R0 1
  keep : Keeps (2 :: cClob) R R0
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp W a → imgM M a = imgM M0 a

/-- The exit continuation of `dc_memfail`: `_exit`'s store with status 1. -/
abbrev ExitK (live S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (e : BitVec 64) : Prop :=
  ∀ t R' M', R' 15 = exitWord e → R' 14 = exitSite.base → DWO live S Q t 0x800005c8#64 R' M'

/-- **`main`'s prologue and initialisers** from `0x80000b00`: `progname`
stored, `bc_init_numbers` (its out of memory through `dc_memfail_spec` to
`hex`), `dc_string_init`, `dc_register_init`, `dc_array_init`; at
`0x80000b28` the fresh state (`MainMid`). -/
theorem main_init {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {sp W : Nat} {s : List Nat}
    (pre : BootPre S M0 sp W s) (R0 : Nat → BitVec 64) (h2 : R0 2 = BitVec.ofNat 64 sp)
    (hex : ExitK live S Q 1#64)
    (hk : ∀ R M H F z o t', MainMid S sp W M0 R0 R M H F [t', o, z] ⟨z, o, t'⟩ →
      DWO live S Q t 0x80000b28#64 R M) :
    DWO live S Q t 0x80000b00#64 R0 M0 := by
  have hsf := pre.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hroom := pre.room; have hbig := pre.big
  simp only [heapEnd] at hroom
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hG := pre.glob
  have hS : HeapOwn S := fun a h1 h2 => pre.heap.own a h1 h2
  bc_run hlive hS [h2] at 0x80004948
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  -- the two stores
  have hM1 : MemOnly (fun a => frameIn sp 32 a ∨ PnWord a)
      (writeLog (writeLog M0 [(sp - 32 + 24, 8, R0 1)]) [(2147601760, 8, 2147514848#64)]) M0 :=
    fun a ha => by
      simp only [not_or, frameIn, PnWord, dc_addrs] at ha
      rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hb1 := (pre.bcHeap M0).out_frame hM1 fun a ha => by
    rcases ha with ha | ha
    · simp only [frameIn] at ha; exact outHeap_of_ge (by simp only [heapEnd]; omega)
    · exact DcGlob.outHeap (by simp only [PnWord, DcGlob] at ha ⊢; omega)
  refine bc_init_numbers_spec hlive hb1
    { frame := hsf.within (m := 32) (n := 48) (by omega) (by decide)
      above := by simp only [heapEnd]; omega
      consts := fun a ha => hG a (by simp only [constBytes, DcGlob, dc_addrs] at ha ⊢; omega)
      sp0 := by bsimp []
      al := by bsimp []; try decide }
    ⟨fun R1 M2 H2 F2 z o t' k1 ip => ?_, fun R1 M2 e2 hout => ?_⟩
  rotate_left
  · -- out of memory: `j dc_memfail`
    bc_run hlive hS [] at 0x80001e74
    have hw : ∀ (k : MKind) a, (∀ j, j < widthOfM k → OutHeap (a + j) ∧
        ¬ (frameIn (sp - 32) 48 (a + j) ∨ constBytes (a + j))) → ldv k M2 a = ldv k
          (writeLog (writeLog M0 [(sp - 32 + 24, 8, R0 1)]) [(2147601760, 8, 2147514848#64)]) a :=
      fun k a ha => ldv_congr k fun j hj => hout _ (ha j hj).1 (ha j hj).2
    refine dc_memfail_spec hlive hG ?_ ?_ (hsf.within (m := 80) (n := 320) (by omega) (by decide))
      (by simp only [stderrAddr]; omega) _ (by rw [e2, Nat.sub_sub]) (hex t)
    · rw [hw .ld _ fun j hj => ⟨DcGlob.outHeap (by simp only [widthOfM, DcGlob, dc_addrs] at hj ⊢; omega),
        by simp only [widthOfM, frameIn, constBytes, dc_addrs] at hj ⊢; omega⟩]
      exact ldv_store_hit _ _ _
    · refine { own := fun i hi => hG _ (by simp only [DcGlob, dc_addrs, stderrAddr]; omega)
               val := ?_, lo := by simp only [stderrAddr]; omega, hi := by simp only [stderrAddr]; omega
               small := by decide }
      rw [hw .lw _ fun j hj => ⟨DcGlob.outHeap (by simp only [widthOfM, DcGlob, dc_addrs, stderrAddr] at hj ⊢; omega),
        by simp only [widthOfM, frameIn, constBytes, dc_addrs, stderrAddr] at hj ⊢; omega⟩,
        ldv_congr .lw fun j hj => hM1 _ (by simp only [widthOfM, frameIn, PnWord, dc_addrs, stderrAddr] at hj ⊢; omega)]
      exact pre.errFd
  -- `dc_string_init`, `dc_register_init`, `dc_array_init`
  have hS2 : HeapOwn S := fun a h1 h2 => ip.heap.heap.own a h1 h2
  bsimp []
  bc_run hlive hS2 [] at 0x80003c74
  refine dc_string_init_spec hlive _ (by bsimp []; try decide) fun R2 k2 _ => ?_
  bsimp []
  bc_run hlive hS2 [] at 0x80002cd0
  refine dc_register_init_spec hlive (fun a h1 h2 => hG a (by simp only [DcGlob, dc_addrs] at h1 h2 ⊢; omega))
    _ (by bsimp []; try decide) fun R3 M3 k3 hf => ?_
  bsimp []
  bc_run hlive hS2 [] at 0x80003c78
  refine dc_array_init_spec hlive _ (by bsimp []; try decide) fun R4 k4 _ => ?_
  bsimp []
  -- the memory at `0x80000b28`
  have keep3 : ∀ a, OutHeap a → ¬ frameIn (sp - 32) 48 a → ¬ constBytes a →
      ¬ (dcRegAddr ≤ a ∧ a < dcRegAddr + 2048) → ¬ (frameIn sp 32 a ∨ PnWord a) →
      imgM M3 a = imgM M0 a := fun a e1 e2 e3 e4 e5 =>
    (hf.rest a (by simp only [dc_addrs] at e4 ⊢; omega)).trans ((ip.out a e1 fun h => h.elim e2 e3).trans
      (hM1 a e5))
  have gw : ∀ (k : MKind) a, (∀ j, j < widthOfM k → 0x8001ad10 ≤ a + j ∧ a + j < bcFreeAddr ∧
      ¬ (freeListAddr ≤ a + j ∧ a + j < freeListAddr + 16) ∧ ¬ PnWord (a + j)) →
      ldv k M3 a = ldv k M0 a := fun k a ha => ldv_congr k fun j hj => by
    obtain ⟨e1, e2, e3, e4⟩ := ha j hj
    refine keep3 _ ?_ ?_ ?_ ?_ ?_
    · simp only [OutHeap, heapStart, heapEnd, freeListAddr, bcFreeAddr] at e1 e2 e3 ⊢; omega
    · simp only [frameIn, bcFreeAddr] at e2 ⊢; omega
    · simp only [constBytes, dc_addrs, bcFreeAddr] at e2 ⊢; omega
    · simp only [dc_addrs, bcFreeAddr] at e2 ⊢; omega
    · simp only [frameIn, bcFreeAddr, not_or] at e2 ⊢; exact ⟨by omega, e4⟩
  have gz : ∀ (k : MKind), (k = .ld ∨ k = .lw) → ∀ a, (∀ j, j < widthOfM k →
      freeListAddr + 16 ≤ a + j ∧ a + j < bcFreeAddr ∧ ¬ PnWord (a + j)) → ldv k M3 a = 0#64 :=
    fun k hk a ha => (gw k a fun j hj => by
      obtain ⟨e1, e2, e3⟩ := ha j hj
      simp only [freeListAddr, bcFreeAddr] at e1 e2 ⊢; exact ⟨by omega, by omega, by omega, e3⟩).trans
      (ldv_zero k hk fun j hj => by
        obtain ⟨e1, e2, _⟩ := ha j hj
        exact pre.bss _ (by omega) (by simp only [heapStart, bcFreeAddr] at e2 ⊢; omega))
  have gr : ∀ (k : MKind) a, a + widthOfM k ≤ dcRegAddr → ldv k M3 a = ldv k M2 a :=
    fun k a ha => ldv_congr k fun j hj => hf.rest _ (.inl (by omega))
  have hv : DcView M3 (bootG []) ⟨z, o, t'⟩ St.init :=
    { stk := .nil (gz .ld (.inl rfl) _ fun j hj => by
        simp only [widthOfM, PnWord, dc_addrs, freeListAddr, bcFreeAddr] at hj ⊢; omega)
      regs := fun r hr => .nil (ldv_zero .ld (.inl rfl) fun j hj => by
        have := hf.fill (8 * r + j) (by simp only [widthOfM] at hj; omega)
        rwa [show dcRegAddr + (8 * r + j) = regAddr r + j by simp only [regAddr]; omega] at this)
      strs := fun o h => absurd h (by simp [bootG])
      zw := by rw [gr .ld _ (by simp only [widthOfM, dc_addrs]; omega), ip.zero]; exact ip.gZero
      ow := by rw [gr .ld _ (by simp only [widthOfM, dc_addrs]; omega), ip.one]; exact ip.gOne
      tw := by rw [gr .ld _ (by simp only [widthOfM, dc_addrs]; omega), ip.two]; exact ip.gTwo
      ibase := (gw .lw _ fun j hj => by
        simp only [widthOfM, PnWord, dc_addrs, freeListAddr, bcFreeAddr] at hj ⊢; omega).trans pre.ibase
      obase := (gw .lw _ fun j hj => by
        simp only [widthOfM, PnWord, dc_addrs, freeListAddr, bcFreeAddr] at hj ⊢; omega).trans pre.obase
      scale := gz .lw (.inr rfl) _ fun j hj => by
        simp only [widthOfM, PnWord, dc_addrs, freeListAddr, bcFreeAddr] at hj ⊢; omega
      unwind := gz .lw (.inr rfl) _ fun j hj => by
        simp only [widthOfM, PnWord, dc_addrs, freeListAddr, bcFreeAddr] at hj ⊢; omega
      noexit := gz .lw (.inr rfl) _ fun j hj => by
        simp only [widthOfM, PnWord, dc_addrs, freeListAddr, bcFreeAddr] at hj ⊢; omega
      lineMax := .inl ((gw .lw _ fun j hj => by
        simp only [widthOfM, PnWord, dc_addrs, freeListAddr, bcFreeAddr] at hj ⊢; omega).trans pre.lineMax)
      lbuf := gz .ld (.inl rfl) _ fun j hj => by
        simp only [widthOfM, PnWord, dc_addrs, freeListAddr, bcFreeAddr] at hj ⊢; omega
      lbufLen := fun b h => absurd h (by simp [bootG])
      outFd := (gw .lw _ fun j hj => by
        simp only [widthOfM, PnWord, dc_addrs, freeListAddr, bcFreeAddr] at hj ⊢; omega).trans pre.outFd
      errFd := (gw .lw _ fun j hj => by
        simp only [widthOfM, PnWord, dc_addrs, freeListAddr, bcFreeAddr] at hj ⊢; omega).trans pre.errFd
      prog := by
        rw [gr .ld _ (by simp only [widthOfM, dc_addrs]; omega), OutFrame.ldv ip.out
          (fun j hj => DcGlob.outHeap (by simp only [DcGlob, dc_addrs]; omega))
          (fun j hj => by simp only [frameIn, constBytes, dc_addrs]; omega)]
        exact ldv_store_hit _ _ _ }
  have hb3 := ip.heap.out_frame (P := fun a => dcRegAddr ≤ a ∧ a < dcRegAddr + 2048)
    (fun a ha => hf.rest a (by simp only [not_and, Nat.not_lt] at ha; omega))
    fun a ha => DcGlob.outHeap (by simp only [DcGlob, dc_addrs] at ha ⊢; omega)
  refine hk R4 M3 H2 F2 z o t' ⟨boot_dcAt hb3 ip.zero ip.one ip.two hv hG pre.col, ?_, ?_, ?_, ?_⟩
  · bsimp [k4.get 2, k3.get 2, k2.get 2, k1.get 2]
  · rw [ldv_congr .ld fun j hj => hf.rest _ (.inr (by simp only [widthOfM, dc_addrs] at hj ⊢; omega)),
      OutFrame.ldv ip.out (fun j hj => outHeap_of_ge (by simp only [heapEnd]; omega))
        (fun j hj => by simp only [frameIn, constBytes, dc_addrs]; omega),
      ldv_store_miss _ _ _ (by simp only [widthOfM]; omega), show sp - 8 = sp - 32 + 24 by omega]
    exact ldv_store_hit _ _ _
  · intro z hz
    simp only [cClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨n2, n1, -, -, -, n10, n11, n12, n13, n14, n15, -⟩ := hz
    simp only [k4 z (by simp), k3 z (by simp; omega), k2 z (by simp), upd_apply, n1, n2, n14, n15,
      ite_false, k1 z (by simp [initClob]; omega)]
  · intro a e1 e2 e3
    refine keep3 a e1 (fun h => e3 (by simp only [frameIn] at h ⊢; omega))
      (fun h => e2 (by simp only [constBytes, DcGlob, dc_addrs] at h ⊢; omega))
      (fun h => e2 (by simp only [DcGlob, dc_addrs] at h ⊢; omega)) ?_
    rintro (h | h)
    · exact e3 (by simp only [frameIn] at h ⊢; omega)
    · exact e2 (by simp only [PnWord, DcGlob, dc_addrs] at h ⊢; omega)

/-- **At `main`'s call of `dc_evalstr`** (`0x80001914`, entry `M0`/`R0`): dc
holds `St.init` over the ghost `bootG [o]`, the script's string object `o`
(text `s`, one reference: the handle `(DC_STRING, o)` at `sp - 32`, which
`a0` points to), `ra` the return into `main`, `main`'s saved `ra` at
`sp - 8`, the callee-saved registers kept, every byte off the heap, the
globals and the frame as at entry. -/
structure BootEval (S : Nat → Prop) (sp W : Nat) (M0 : Mem) (R0 R : Nat → BitVec 64) (M : Mem)
    (H : Heap) (F : List Blk) (L : List NumObj) (C : BcConsts) (o : StrObj) (s : List Nat) : Prop where
  dc : DcAt S M H F L C (bootG [o]) [.str o.hb.pay] St.init
  text : o.s = s
  refs : o.refs = 1
  dat : DatAt M (sp - 32) (.str o.hb.pay)
  r1 : R 1 = 0x80000b54#64
  r2 : R 2 = BitVec.ofNat 64 (sp - 32)
  r10 : R 10 = BitVec.ofNat 64 (sp - 32)
  ra : ldv .ld M (sp - 8) = R0 1
  keep : Keeps (2 :: cClob) R R0
  out : ∀ a, OutHeap a → ¬ DcGlob a → ¬ frameIn sp W a → imgM M a = imgM M0 a

/-- **`main`'s script string** from `0x80000b28`: `strlen`, `dc_makestring`
of the script, the handle stored in the frame, the call of `dc_evalstr`. -/
theorem main_mk {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 M : Mem} {sp W : Nat} {s : List Nat}
    {R0 R : Nat → BitVec 64} {H : Heap} {F : List Blk} {L : List NumObj} {C : BcConsts}
    (pre : BootPre S M0 sp W s) (mid : MainMid S sp W M0 R0 R M H F L C)
    (hoom : ∀ R' M' sp', OomAt S sp W M0 (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M')
    (hk : ∀ R' M' H' b1 b2, BootEval S sp W M0 R0 R' M' H' F L C (msObj b1 b2 s) s →
      DWO live S Q t 0x80001914#64 R' M') :
    DWO live S Q t 0x80000b28#64 R M := by
  have hsf := pre.frame
  have hsl := hsf.lo; have hsh := hsf.hi; have hsa := hsf.al
  have hroom := pre.room; have hbig := pre.big
  simp only [heapEnd] at hroom
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hlen := pre.len
  have hS : HeapOwn S := fun a h1 h2 => mid.dc.heap.heap.own a h1 h2
  -- the script's bytes are as at entry
  have hsc0 := pre.script
  have hsm : ∀ i, i ≤ s.length → imgM M (scriptAddr + i) = imgM M0 (scriptAddr + i) := fun i hi =>
    mid.out _ (by simp only [OutHeap, scriptAddr, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega)
      (by simp only [DcGlob, scriptAddr, dc_addrs]; omega) (by simp only [frameIn, scriptAddr]; omega)
  have hsc : OwnedCStr S M scriptAddr s.length :=
    { own := hsc0.own, nz := fun i hi => by rw [hsm i (by omega)]; exact hsc0.nz i hi
      nul := by rw [hsm _ (Nat.le_refl _)]; exact hsc0.nul, lo := hsc0.lo, hi := hsc0.hi }
  refine main_scriptLen hlive hsc R fun R1 h10 k1 => ?_
  have q2 : R1 2 = BitVec.ofNat 64 (sp - 32) := by
    rw [k1 2 (by decide) (by decide) (by decide)]; bsimp [mid.r2]
  bc_run hlive hS [q2] at 0x80003a58
  have hsrc : MsSrc S M (bootG []) (sp - 32) scriptAddr s :=
    { own := ⟨fun i hi => hsc0.own i (by omega), hsc0.lo, by have := hsc0.hi; omega⟩
      loc := fun i hi => .inr ⟨by
          simp only [OutHeap, scriptAddr, heapStart, heapEnd, freeListAddr, bcFreeAddr]; omega,
        by simp only [frameIn, scriptAddr]; omega⟩
      val := fun i hi => (hsm i (by omega)).trans (pre.text i hi)
      byte := pre.byte
      len := by omega }
  refine dc_makestring_spec hlive mid.dc hsrc
    (hsf.within (m := 32) (n := 64) (by omega) (by decide)) (by simp only [heapEnd]; omega) _
    (by bsimp [q2]) (by bsimp []) (by bsimp [h10]) (by bsimp []; try decide)
    (fun R2 M2 H2 b1 b2 k2 e2 e10 e11 hd hso => ?_) (fun R2 M2 e2 hso => ?_)
  rotate_left
  · refine hoom R2 M2 (sp - 32 - 64) ⟨by omega, by omega, e2, fun a e1 e2' e3 _ => ?_⟩
    exact (hso a e1 e2' fun h => e3 (by simp only [frameIn] at h ⊢; omega)).trans (mid.out a e1 e2' e3)
  have hS2 : HeapOwn S := fun a h1 h2 => hd.heap.heap.own a h1 h2
  have q2' : R2 2 = BitVec.ofNat 64 (sp - 32) := by rw [e2]; bsimp [q2]
  bsimp []
  bc_run hlive hS2 [q2'] at 0x80001914
  all_goals first | exact frame_acc hsf (by omega) (by omega) | skip
  have hM : MemOnly (fun a => sp - 32 ≤ a ∧ a < sp - 16)
      (writeLog (writeLog M2 [(sp - 32, 8, R2 10)]) [(sp - 32 + 8, 8, R2 11)]) M2 := fun a ha => by
    simp only [not_and, Nat.not_lt] at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  refine hk _ _ H2 b1 b2
    { dc := hd.outWrite hM fun a ha => above_sp (sp := sp - 32) (a := a + 32 - 32)
          (by simp only [heapEnd]; omega) (by omega) |>.imp (by intro h; simpa using h)
            (fun h => by simpa using h.1)
      text := rfl
      refs := rfl
      dat := ⟨?_, ?_⟩
      r1 := by bsimp []
      r2 := by bsimp [q2']
      r10 := by bsimp [q2']
      ra := ?_
      keep := ?_
      out := ?_ }
  · rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega), ldv_store_hit]; exact e10
  · rw [ldv_store_hit]; exact e11
  · rw [ldv_store_miss _ _ _ (by simp only [widthOfM]; omega),
      ldv_store_miss _ _ _ (by simp only [widthOfM]; omega),
      ldv_congr .ld fun j hj => hso _ (outHeap_of_ge (by simp only [heapEnd]; omega))
        (fun h => by have := h.lt; simp only [heapStart] at this; omega)
        (by simp only [frameIn]; omega)]
    exact mid.ra
  · intro z hz
    have hz' := hz
    simp only [cClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz'
    obtain ⟨n2, n1, -, -, -, n10, n11, n12, n13, n14, n15, -⟩ := hz'
    rw [← mid.keep z hz]
    simp only [upd_apply, n1, n10, n11, ite_false, k2 z (fun h => hz (List.mem_cons_of_mem _ h))]
    rw [k1 z n10 n14 n15]
    simp only [upd_apply, n1, ite_false]
  · intro a e1 e2' e3
    rw [hM a fun h => e3 (by simp only [frameIn]; omega),
      hso a e1 e2' fun h => e3 (by simp only [frameIn] at h ⊢; omega)]
    exact mid.out a e1 e2' e3

/-- **`main` from its entry to the call of `dc_evalstr`.** From the fresh
boot (`BootPre`, `R0 2 = sp`), the run reaches `dc_evalstr`'s
entry `0x80001914` with `BootEval`: `St.init` over the script's string
object. `bc_init_numbers`' out of memory exits with status 1 (`hex`);
`dc_makestring`'s goes to `hoom`. -/
theorem main_spec {live S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {t : String} (hlive : ∀ p ∈ dcText, live p.1) {M0 : Mem} {sp W : Nat} {s : List Nat}
    (pre : BootPre S M0 sp W s) (R0 : Nat → BitVec 64) (h2 : R0 2 = BitVec.ofNat 64 sp)
    (hex : ExitK live S Q 1#64)
    (hoom : ∀ R' M' sp', OomAt S sp W M0 (fun _ => False) sp' R' M' →
      DWO live S Q t 0x80001e74#64 R' M')
    (hk : ∀ R' M' H' F L C b1 b2, BootEval S sp W M0 R0 R' M' H' F L C (msObj b1 b2 s) s →
      DWO live S Q t 0x80001914#64 R' M') :
    DWO live S Q t 0x80000b00#64 R0 M0 :=
  main_init hlive pre R0 h2 hex fun _ _ _ _ _ _ _ mid =>
    main_mk hlive pre mid hoom fun _ _ _ _ _ he => hk _ _ _ _ _ _ _ _ he

end Dc.Mach
