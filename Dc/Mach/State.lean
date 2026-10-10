import Dc.Machine
import Dc.Mach.Bc.RawCells

/-!
# The dc state in memory (M9)

How the machine holds a `Dc.St` (`dc/stack.c`, `dc/array.c`, `dc/string.c`):

- `dc_data` (16 bytes): the type as an `int` at `+0` (`1` a number, `2` a
  string, `0` a register level without value), the pointer at `+8`.
- The evaluation stack: `dc_stack` heads a chain of 32-byte `dc_list` nodes
  (datum `+0`, array `+16` always `NULL`, link `+24`).
- Register `r < 256`: `dc_register[r]` heads a chain of `dc_list` levels,
  each with its array: a chain of 32-byte `dc_array` nodes (index `int` at
  `+0`, datum `+8`, link `+24`) sorted by index.
- A string (`struct dc_string`, 24 bytes): text pointer `+0`, length `+8`,
  reference count `int` at `+16`; the text block holds the bytes and a NUL.
- Numbers are objects of the number heap (`BcHeap`).

The ghost `DcG` names every node block, every datum's target (`GV`) and
every string object. `DcAt` ties memory to a state: chains, denotations,
globals, and exact reference counts (`numRefs`, `strRefs`) over the state's
references plus the caller's handles `hs` (data held in C locals). The
blocks of the ghost are the raw blocks of the number heap (`DcG.raws`), so
every number callee keeps them byte-identical.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-! ## Addresses -/

/-- `dc_stack` -/
abbrev dcStackAddr : Nat := 0x8001cd98
/-- `dc_register[256]` -/
abbrev dcRegAddr : Nat := 0x8001cdd0
/-- `dc_ibase` -/
abbrev ibaseAddr : Nat := 0x8001cd38
/-- `dc_obase` -/
abbrev obaseAddr : Nat := 0x8001cd34
/-- `dc_scale` -/
abbrev scaleAddr : Nat := 0x8001cd8c
/-- `unwind_depth` -/
abbrev unwindAddr : Nat := 0x8001cd88
/-- `unwind_noexit` -/
abbrev noexitAddr : Nat := 0x8001cd80
/-- `line_max` (`out_char`) -/
abbrev lineMaxAddr : Nat := 0x8001cd3c
/-- `out_col` (`out_char`) -/
abbrev outColAddr : Nat := 0x8001cd90
/-- `progname` -/
abbrev prognameAddr : Nat := 0x8001cd60
/-- The descriptor words of `stdout`'s and `stderr`'s `FILE`s (`.data`). -/
abbrev stdFilesAddr : Nat := 0x8001ad14
/-- The string `"dc"` in `.rodata`, `progname`'s value. -/
abbrev dcNameAddr : Nat := 0x800079e0
/-- `line_buf` (`dc_readstring`) -/
abbrev lineBufAddr : Nat := 0x8001cda8
/-- `buflen` (`dc_readstring`) -/
abbrev bufLenAddr : Nat := 0x8001cda0

/-- The word of register `r`'s chain. -/
abbrev regAddr (r : Nat) : Nat := dcRegAddr + 8 * r

/-! ## Data -/

/-- What a datum points to: a number struct or a string header. -/
inductive GV where
  | num (p : Nat)
  | str (p : Nat)
  deriving DecidableEq

/-- The `dc_type` of a datum. -/
def GV.tag : GV → Nat
  | .num _ => 1
  | .str _ => 2

/-- The pointer of a datum. -/
def GV.ptr : GV → Nat
  | .num p => p
  | .str p => p

/-- `dc_data` at `a`: the type (an `int`) and the pointer. -/
structure DatAt (Mt : Mem) (a : Nat) (g : GV) : Prop where
  tag : (ldv .ld Mt a).toNat % 2 ^ 32 = g.tag
  ptr : ldv .ld Mt (a + 8) = BitVec.ofNat 64 g.ptr

/-- A string object: the header block `hb` and the text block `tb`. -/
structure StrObj where
  hb : Blk
  tb : Blk
  s : List Nat
  refs : Nat

/-- Memory holds the string object `o`. -/
structure StrAt (Mt : Mem) (o : StrObj) : Prop where
  ptr : ldv .ld Mt o.hb.pay = BitVec.ofNat 64 o.tb.pay
  len : ldv .ld Mt (o.hb.pay + 8) = BitVec.ofNat 64 o.s.length
  refs : ldv .lw Mt (o.hb.pay + 16) = BitVec.ofNat 64 o.refs
  bytes : ∀ i, i < o.s.length → imgM Mt (o.tb.pay + i) = BitVec.ofNat 8 (o.s.getD i 0)
  nul : imgM Mt (o.tb.pay + o.s.length) = 0#8
  hsz : 24 ≤ o.hb.sz
  tsz : o.s.length + 1 ≤ o.tb.sz
  byte : ∀ c ∈ o.s, c < 256
  refsPos : 1 ≤ o.refs
  refsLt : o.refs < 2 ^ 31

/-- The objects data can point to. -/
structure DObjs where
  L : List NumObj
  ss : List StrObj

/-- The datum `g` denotes the value `v`. -/
def GV.Den (O : DObjs) : GV → Val → Prop
  | .num p, .num n => ∃ x ∈ O.L, x.rep.p = p ∧ x.rep.num = n
  | .str p, .str s => ∃ o ∈ O.ss, o.hb.pay = p ∧ o.s = s
  | _, _ => False

/-! ## Chains -/

/-- A chain of blocks from the pointer word at `a`, linked through the word at
`+off`, each block satisfying `P` with its ghost. -/
inductive LChain {α : Type} (Mt : Mem) (off : Nat) (P : Blk → α → Prop) : Nat → List (Blk × α) → Prop
  | nil {a : Nat} : ldv .ld Mt a = 0#64 → LChain Mt off P a []
  | cons {a : Nat} {b : Blk} {x : α} {l : List (Blk × α)} :
      ldv .ld Mt a = BitVec.ofNat 64 b.pay → P b x → LChain Mt off P (b.pay + off) l →
      LChain Mt off P a ((b, x) :: l)

/-- An array element: index and datum. -/
structure ANode where
  idx : Nat
  v : GV

/-- An array node: index `int` at `+0`, datum at `+8`. -/
structure ANodeAt (Mt : Mem) (b : Blk) (e : ANode) : Prop where
  idx : ldv .lw Mt b.pay = BitVec.ofNat 64 e.idx
  idxLt : e.idx < 2 ^ 31
  dat : DatAt Mt (b.pay + 8) e.v
  sz : 32 ≤ b.sz

/-- A register level: its datum (if any) and its array. -/
structure RLev where
  v : Option GV
  arr : List (Blk × ANode)

/-- A register level's node: the datum or type `0`, the array chain. -/
structure RLevAt (Mt : Mem) (b : Blk) (e : RLev) : Prop where
  dat : match e.v with
    | some g => DatAt Mt b.pay g
    | none => ldv .lw Mt b.pay = 0#64
  arr : LChain Mt 24 (ANodeAt Mt) (b.pay + 16) e.arr
  sz : 32 ≤ b.sz

/-- A stack node: the datum, no array. -/
structure SNodeAt (Mt : Mem) (b : Blk) (g : GV) : Prop where
  dat : DatAt Mt b.pay g
  arr : ldv .ld Mt (b.pay + 16) = 0#64
  sz : 32 ≤ b.sz

/-! ## The ghost state -/

/-- The ghost of dc's memory: the stack nodes, each register's levels, the
string objects, `dc_readstring`'s line buffer once allocated, and the number
references dc lost (`lk`, one pointer per reference never released: the
`_zero_` of a failed `dc_div`/`dc_rem`/`dc_divrem`/`dc_modexp` result slot,
`bc_sqrt`'s and `bc_raisemod`'s leaks). -/
structure DcG where
  stk : List (Blk × GV)
  regs : Nat → List (Blk × RLev)
  strs : List StrObj
  lbuf : Option Blk
  lk : List Nat

/-- A level's blocks: its node and its array nodes. -/
def RLev.blocks (be : Blk × RLev) : List Blk := be.1 :: be.2.arr.map (·.1)

/-- A level's references: its datum and its array's data. -/
def RLev.vals (be : Blk × RLev) : List GV := be.2.v.toList ++ be.2.arr.map (·.2.v)

/-- The blocks of the ghost. -/
def DcG.blocks (G : DcG) : List Blk :=
  G.stk.map (·.1) ++ (List.range 256).flatMap (fun r => (G.regs r).flatMap RLev.blocks) ++
    G.strs.flatMap (fun o => [o.hb, o.tb]) ++ G.lbuf.toList

/-- The references the state holds. -/
def DcG.vals (G : DcG) : List GV :=
  G.stk.map (·.2) ++ (List.range 256).flatMap (fun r => (G.regs r).flatMap RLev.vals)

/-- The raw blocks of the number heap for `G` at memory `Mt`. -/
def DcG.raws (G : DcG) (Mt : Mem) : Raws := ⟨G.blocks, Mt⟩

/-- The number heap's constants `_zero_`, `_one_`, `_two_`. -/
structure BcConsts where
  z : NumObj
  o : NumObj
  t : NumObj

/-- How many of the constants' words point to `p`. -/
def BcConsts.cnt (C : BcConsts) (p : Nat) : Nat :=
  [C.z, C.o, C.t].countP (·.rep.p = p)

/-- A level denotes an `Entry`. -/
structure RLev.Den (O : DObjs) (e : RLev) (v : Entry) : Prop where
  val : Option.Rel (GV.Den O) e.v v.val
  arr : List.Forall₂ (fun (be : Blk × ANode) (iv : Nat × Val) => be.2.idx = iv.1 ∧ be.2.v.Den O iv.2)
    e.arr v.arr

/-- The global bytes dc's state reads: the descriptors of `stdout` and
`stderr`, `dc_obase`, `dc_ibase`, `line_max`, `progname`, `unwind_noexit`,
`unwind_depth`, `dc_scale`, `dc_stack`, `buflen`, `line_buf`, `_two_`,
`_one_`, `_zero_`, `dc_register`. -/
def DcGlob (a : Nat) : Prop :=
  (stdFilesAddr ≤ a ∧ a < stdFilesAddr + 8) ∨ (obaseAddr ≤ a ∧ a < lineMaxAddr + 4) ∨
    (prognameAddr ≤ a ∧ a < prognameAddr + 8) ∨ (noexitAddr ≤ a ∧ a < noexitAddr + 4) ∨
    (unwindAddr ≤ a ∧ a < scaleAddr + 4) ∨ (dcStackAddr ≤ a ∧ a < lineBufAddr + 8) ∨
    (twoAddr ≤ a ∧ a < dcRegAddr + 2048)

/-- A byte of one of the blocks. -/
def InBlocks (bs : List Blk) (a : Nat) : Prop := ∃ b ∈ bs, b.In a

/-- **The memory side**: what the bytes of the ghost's blocks and of dc's
globals say. It reads nothing else (`DcView.frame`). -/
structure DcView (Mt : Mem) (G : DcG) (C : BcConsts) (st : St) : Prop where
  stk : LChain Mt 24 (SNodeAt Mt) dcStackAddr G.stk
  regs : ∀ r, r < 256 → LChain Mt 24 (RLevAt Mt) (regAddr r) (G.regs r)
  strs : ∀ o ∈ G.strs, StrAt Mt o
  zw : ldv .ld Mt zeroAddr = BitVec.ofNat 64 C.z.rep.p
  ow : ldv .ld Mt oneAddr = BitVec.ofNat 64 C.o.rep.p
  tw : ldv .ld Mt twoAddr = BitVec.ofNat 64 C.t.rep.p
  ibase : ldv .lw Mt ibaseAddr = BitVec.ofNat 64 st.ibase
  obase : ldv .lw Mt obaseAddr = BitVec.ofNat 64 st.obase
  scale : ldv .lw Mt scaleAddr = BitVec.ofNat 64 st.scale
  unwind : ldv .lw Mt unwindAddr = BitVec.ofNat 64 st.unwind
  noexit : ldv .lw Mt noexitAddr = boolWord st.noexit
  lineMax : ldv .lw Mt lineMaxAddr = BitVec.ofInt 64 (-1) ∨
    ldv .lw Mt lineMaxAddr = BitVec.ofNat 64 70
  lbuf : ldv .ld Mt lineBufAddr = BitVec.ofNat 64 (match G.lbuf with | some b => b.pay | none => 0)
  lbufLen : ∀ b, G.lbuf = some b → ldv .ld Mt bufLenAddr = BitVec.ofNat 64 2016
  outFd : ldv .lw Mt stdFilesAddr = BitVec.ofNat 64 1
  errFd : ldv .lw Mt (stdFilesAddr + 4) = BitVec.ofNat 64 2
  prog : ldv .ld Mt prognameAddr = BitVec.ofNat 64 dcNameAddr

/-- **The ghost side**: denotations, ranges, and exact reference counts over
the state's references and the handles `hs`. -/
structure DcDen (L : List NumObj) (C : BcConsts) (G : DcG) (hs : List GV) (st : St) : Prop where
  stk : List.Forall₂ (fun (bg : Blk × GV) v => bg.2.Den ⟨L, G.strs⟩ v) G.stk st.stack
  regs : ∀ r, r < 256 → List.Forall₂ (fun (be : Blk × RLev) v => be.2.Den ⟨L, G.strs⟩ v)
    (G.regs r) (st.regs r)
  regsHi : ∀ r, 256 ≤ r → st.regs r = [] ∧ G.regs r = []
  hsDen : ∀ g ∈ hs, ∃ v, g.Den ⟨L, G.strs⟩ v
  owns : ∀ x ∈ L, x.Owns
  norm : ∀ x ∈ L, x.rep.Norm
  pos : ∀ x ∈ L, 1 ≤ x.rep.len
  numRefs : ∀ x ∈ L, x.rep.refs = (G.vals ++ hs).count (.num x.rep.p) + C.cnt x.rep.p +
    G.lk.count x.rep.p
  strRefs : ∀ o ∈ G.strs, o.refs = (G.vals ++ hs).count (.str o.hb.pay)
  /-- every number of the heap is referenced: a count reaching zero releases it -/
  live : ∀ x ∈ L, 1 ≤ x.rep.refs
  lkLen : G.lk.length ≤ 2 ^ 29
  lkIn : ∀ p ∈ G.lk, ∃ x ∈ L, x.rep.p = p
  mz : C.z ∈ L
  mo : C.o ∈ L
  mt : C.t ∈ L
  zv : C.z.rep.num = Num.zero 0
  ov : C.o.rep.num = Num.one
  tv : C.t.rep.num = ⟨false, 2, 0⟩
  ibase : 2 ≤ st.ibase ∧ st.ibase ≤ 16
  obase : 2 ≤ st.obase ∧ st.obase < 2 ^ 31
  scale : st.scale < 2 ^ 31
  unwind : st.unwind < 2 ^ 31
  lbuf : ∀ b, G.lbuf = some b → 2016 ≤ b.sz

/-- **Memory `Mt` holds the dc state `st`**, with ghost `G`, number heap
`H`/`F`/`L` with constants `C`, and the caller's handles `hs`. -/
structure DcAt (S : Nat → Prop) (Mt : Mem) (H : Heap) (F : List Blk) (L : List NumObj)
    (C : BcConsts) (G : DcG) (hs : List GV) (st : St) : Prop where
  heap : BcHeap S (G.raws Mt) Mt H F L
  nodup : G.blocks.Nodup
  view : DcView Mt G C st
  den : DcDen L C G hs st
  glob : ∀ a, DcGlob a → S a
  col : ∀ a, outColAddr ≤ a → a < outColAddr + 4 → S a

/-- The global addresses as literals. -/
theorem dc_addrs : dcStackAddr = 0x8001cd98 ∧ dcRegAddr = 0x8001cdd0 ∧ ibaseAddr = 0x8001cd38 ∧
    obaseAddr = 0x8001cd34 ∧ scaleAddr = 0x8001cd8c ∧ unwindAddr = 0x8001cd88 ∧
    noexitAddr = 0x8001cd80 ∧ lineMaxAddr = 0x8001cd3c ∧ outColAddr = 0x8001cd90 ∧
    lineBufAddr = 0x8001cda8 ∧ bufLenAddr = 0x8001cda0 ∧ zeroAddr = 0x8001cdc8 ∧
    oneAddr = 0x8001cdc0 ∧ twoAddr = 0x8001cdb8 ∧ bcFreeAddr = 0x8001cdb0 ∧
    prognameAddr = 0x8001cd60 ∧ stdFilesAddr = 0x8001ad14 ∧ dcNameAddr = 0x800079e0 := by
  decide

/-! ## Frames -/

/-- A chain survives a memory agreeing on its first word and on each block's
link word, each block's predicate carried over. -/
theorem LChain.frame {α : Type} {Mt Mt' : Mem} {off : Nat} {P P' : Blk → α → Prop} :
    ∀ {a : Nat} {l : List (Blk × α)}, LChain Mt off P a l →
      ldv .ld Mt' a = ldv .ld Mt a →
      (∀ bx ∈ l, P bx.1 bx.2 → P' bx.1 bx.2 ∧
        ldv .ld Mt' (bx.1.pay + off) = ldv .ld Mt (bx.1.pay + off)) →
      LChain Mt' off P' a l
  | _, _, .nil h, ha, _ => .nil (ha.trans h)
  | _, _, .cons h hp hl, ha, hb => by
    obtain ⟨hp', hw⟩ := hb _ List.mem_cons_self hp
    exact .cons (ha.trans h) hp' (hl.frame hw fun bx hm => hb bx (List.mem_cons_of_mem _ hm))

/-- Every block of a chain satisfies the predicate. -/
theorem LChain.forall {α : Type} {Mt : Mem} {off : Nat} {P : Blk → α → Prop} :
    ∀ {a : Nat} {l : List (Blk × α)}, LChain Mt off P a l → ∀ bx ∈ l, P bx.1 bx.2
  | _, _, .nil _, _, hm => by cases hm
  | _, _, .cons _ hp hl, bx, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hp
    · exact hl.forall bx hm

theorem DcG.stk_mem {G : DcG} {bg : Blk × GV} (h : bg ∈ G.stk) : bg.1 ∈ G.blocks := by
  unfold DcG.blocks
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨bg, h, rfl⟩)))

theorem DcG.reg_mem {G : DcG} {r : Nat} (hr : r < 256) {be : Blk × RLev} (h : be ∈ G.regs r) :
    be.1 ∈ G.blocks := by
  unfold DcG.blocks
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, List.mem_flatMap.mpr ⟨be, h, by
      simp [RLev.blocks]⟩⟩)))

theorem DcG.arr_mem {G : DcG} {r : Nat} (hr : r < 256) {be : Blk × RLev} (h : be ∈ G.regs r)
    {bn : Blk × ANode} (hn : bn ∈ be.2.arr) : bn.1 ∈ G.blocks := by
  unfold DcG.blocks
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, List.mem_flatMap.mpr ⟨be, h, by
      simp only [RLev.blocks]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨bn, hn, rfl⟩)⟩⟩)))

theorem DcG.str_mem {G : DcG} {o : StrObj} (h : o ∈ G.strs) :
    o.hb ∈ G.blocks ∧ o.tb ∈ G.blocks := by
  unfold DcG.blocks
  constructor
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨o, h, by simp⟩))
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨o, h, by simp⟩))

/-- A word inside a block agrees when the block's bytes do. -/
theorem ldv_blk {Mt Mt' : Mem} {bs : List Blk} {b : Blk} (hb : b ∈ bs)
    (hag : ∀ a, InBlocks bs a → imgM Mt' a = imgM Mt a) (k : MKind) {o : Nat}
    (ho : o + widthOfM k ≤ b.sz) : ldv k Mt' (b.pay + o) = ldv k Mt (b.pay + o) :=
  ldv_congr k fun j hj => hag _ ⟨b, hb, by simp only [Blk.In, Blk.pay, Blk.fin]; omega⟩

/-- A global word agrees when dc's globals do. -/
theorem ldv_glob {Mt Mt' : Mem} (hag : ∀ a, DcGlob a → imgM Mt' a = imgM Mt a) (k : MKind)
    {a : Nat} (ha : ∀ j, j < widthOfM k → DcGlob (a + j)) : ldv k Mt' a = ldv k Mt a :=
  ldv_congr k fun j hj => hag _ (ha j hj)

theorem DatAt.frame {Mt Mt' : Mem} {bs : List Blk} {b : Blk} (hb : b ∈ bs)
    (hag : ∀ a, InBlocks bs a → imgM Mt' a = imgM Mt a) {o : Nat} (ho : o + 16 ≤ b.sz) {g : GV}
    (h : DatAt Mt (b.pay + o) g) : DatAt Mt' (b.pay + o) g :=
  by
    have e := ldv_blk (o := o + 8) hb hag .ld (by simp only [widthOfM]; omega)
    rw [← Nat.add_assoc] at e
    exact ⟨by rw [ldv_blk hb hag .ld (by simp only [widthOfM]; omega)]; exact h.tag, e.trans h.ptr⟩

theorem StrAt.frame {Mt Mt' : Mem} {bs : List Blk} {o : StrObj} (hh : o.hb ∈ bs) (ht : o.tb ∈ bs)
    (hag : ∀ a, InBlocks bs a → imgM Mt' a = imgM Mt a) (h : StrAt Mt o) : StrAt Mt' o := by
  have hs := h.hsz; have hts := h.tsz
  refine { h with ptr := ?_, len := ?_, refs := ?_, bytes := fun i hi => ?_, nul := ?_ }
  · have := ldv_blk (o := 0) hh hag .ld (by simp only [widthOfM]; omega)
    simp only [Nat.add_zero] at this; rw [this]; exact h.ptr
  · rw [ldv_blk hh hag .ld (by simp only [widthOfM]; omega)]; exact h.len
  · rw [ldv_blk hh hag .lw (by simp only [widthOfM]; omega)]; exact h.refs
  · rw [hag _ ⟨o.tb, ht, by simp only [Blk.In, Blk.pay, Blk.fin]; omega⟩]; exact h.bytes i hi
  · rw [hag _ ⟨o.tb, ht, by simp only [Blk.In, Blk.pay, Blk.fin]; omega⟩]; exact h.nul

/-- The stack's chain word and the register words. -/
def ChainWords (a : Nat) : Prop :=
  (dcStackAddr ≤ a ∧ a < dcStackAddr + 8) ∨ (dcRegAddr ≤ a ∧ a < dcRegAddr + 2048)

/-- A stack chain through a memory agreeing on its blocks and first word. -/
theorem stkChain_frame {Mt Mt' : Mem} {a : Nat} {l : List (Blk × GV)}
    (h : LChain Mt 24 (SNodeAt Mt) a l) (ha : ldv .ld Mt' a = ldv .ld Mt a)
    (hb : ∀ bg ∈ l, ∀ x, bg.1.In x → imgM Mt' x = imgM Mt x) :
    LChain Mt' 24 (SNodeAt Mt') a l := by
  refine h.frame ha fun bg hm hp => ?_
  have hb' : ∀ x, InBlocks [bg.1] x → imgM Mt' x = imgM Mt x := fun x ⟨c, hc, hcx⟩ => by
    rw [List.mem_singleton.mp hc] at hcx; exact hb bg hm x hcx
  have hbm : bg.1 ∈ [bg.1] := List.mem_singleton_self _
  have hsz := hp.sz
  exact ⟨⟨by simpa using DatAt.frame (o := 0) hbm hb' (by omega) (by simpa using hp.dat),
    (ldv_blk hbm hb' .ld (by simp only [widthOfM]; omega)).trans hp.arr, hsz⟩,
    ldv_blk hbm hb' .ld (by simp only [widthOfM]; omega)⟩

/-- A level's blocks. -/
theorem RLev.mem_blocks_arr {be : Blk × RLev} {bn : Blk × ANode} (hn : bn ∈ be.2.arr) :
    bn.1 ∈ RLev.blocks be := by
  simp only [RLev.blocks]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨bn, hn, rfl⟩)

/-- A register chain through a memory agreeing on its levels' blocks and first word. -/
theorem regChain_frame {Mt Mt' : Mem} {a : Nat} {l : List (Blk × RLev)}
    (h : LChain Mt 24 (RLevAt Mt) a l) (ha : ldv .ld Mt' a = ldv .ld Mt a)
    (hb : ∀ be ∈ l, ∀ c ∈ RLev.blocks be, ∀ x, c.In x → imgM Mt' x = imgM Mt x) :
    LChain Mt' 24 (RLevAt Mt') a l := by
  refine h.frame ha fun be hm hp => ?_
  have hb' : ∀ x, InBlocks (RLev.blocks be) x → imgM Mt' x = imgM Mt x :=
    fun x ⟨c, hc, hcx⟩ => hb be hm c hc x hcx
  have hbm : be.1 ∈ RLev.blocks be := List.mem_cons_self
  have hsz := hp.sz
  refine ⟨⟨?_, hp.arr.frame (ldv_blk hbm hb' .ld (by simp only [widthOfM]; omega))
    fun bn hn hq => ?_, hsz⟩, ldv_blk hbm hb' .ld (by simp only [widthOfM]; omega)⟩
  · have hd := hp.dat
    revert hd
    cases be.2.v with
    | some g => exact fun hd => by simpa using DatAt.frame (o := 0) hbm hb' (by omega) (by simpa using hd)
    | none =>
      exact fun hd => by
        have := ldv_blk (o := 0) hbm hb' .lw (by simp only [widthOfM]; omega)
        simp only [Nat.add_zero] at this; rw [this]; exact hd
  · have hcm := RLev.mem_blocks_arr hn
    have hcs := hq.sz
    refine ⟨⟨?_, hq.idxLt, DatAt.frame hcm hb' (by omega) hq.dat, hcs⟩,
      ldv_blk hcm hb' .ld (by simp only [widthOfM]; omega)⟩
    have := ldv_blk (o := 0) hcm hb' .lw (by simp only [widthOfM]; omega)
    simp only [Nat.add_zero] at this; rw [this]; exact hq.idx

/-- **The view with new chains**: the strings and the globals other than the
chain words read the same, the stack and register chains are given at `Mt'`. -/
theorem DcView.withChains {Mt Mt' : Mem} {G G' : DcG} {C : BcConsts} {st st' : St}
    (h : DcView Mt G C st) (hstr : G'.strs = G.strs) (hlb : G'.lbuf = G.lbuf)
    (hst : st'.ibase = st.ibase ∧ st'.obase = st.obase ∧ st'.scale = st.scale ∧
      st'.unwind = st.unwind ∧ st'.noexit = st.noexit)
    (hb : ∀ o ∈ G.strs, ∀ x, (o.hb.In x ∨ o.tb.In x) → imgM Mt' x = imgM Mt x)
    (hg : ∀ a, DcGlob a → ¬ ChainWords a → imgM Mt' a = imgM Mt a)
    (hs : LChain Mt' 24 (SNodeAt Mt') dcStackAddr G'.stk)
    (hr : ∀ r, r < 256 → LChain Mt' 24 (RLevAt Mt') (regAddr r) (G'.regs r)) :
    DcView Mt' G' C st' := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := hst
  have gw : ∀ (k : MKind) a, (∀ j, j < widthOfM k → DcGlob (a + j) ∧ ¬ ChainWords (a + j)) →
      ldv k Mt' a = ldv k Mt a := fun k a ha =>
    ldv_congr k fun j hj => hg _ (ha j hj).1 (ha j hj).2
  refine
    { stk := hs
      regs := hr
      strs := fun o ho => by
        rw [hstr] at ho
        exact (h.strs o ho).frame (bs := [o.hb, o.tb]) (by simp) (by simp) fun x ⟨c, hc, hcx⟩ => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact hb o ho x (.inl hcx)
          · exact hb o ho x (.inr hcx)
      zw := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.zw
      ow := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.ow
      tw := (gw .ld _ fun j hj => by simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.tw
      ibase := by
        rw [e1]; exact (gw .lw _ fun j hj => by
          simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.ibase
      obase := by
        rw [e2]; exact (gw .lw _ fun j hj => by
          simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.obase
      scale := by
        rw [e3]; exact (gw .lw _ fun j hj => by
          simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.scale
      unwind := by
        rw [e4]; exact (gw .lw _ fun j hj => by
          simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.unwind
      noexit := by
        rw [e5]; exact (gw .lw _ fun j hj => by
          simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.noexit
      lineMax := by
        rw [gw .lw _ fun j hj => by simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega]
        exact h.lineMax
      lbuf := by
        rw [hlb]; exact (gw .ld _ fun j hj => by
          simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.lbuf
      lbufLen := fun b e => (gw .ld _ fun j hj => by
        simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans
          (h.lbufLen b (hlb ▸ e))
      outFd := (gw .lw _ fun j hj => by
        simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.outFd
      errFd := (gw .lw _ fun j hj => by
        simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.errFd
      prog := (gw .ld _ fun j hj => by
        simp only [widthOfM, DcGlob, ChainWords, dc_addrs] at hj ⊢; omega).trans h.prog }

/-- **The view reads only the ghost's blocks and dc's globals.** -/
theorem DcView.frame {Mt Mt' : Mem} {G : DcG} {C : BcConsts} {st : St} (h : DcView Mt G C st)
    (hb : ∀ a, InBlocks G.blocks a → imgM Mt' a = imgM Mt a)
    (hg : ∀ a, DcGlob a → imgM Mt' a = imgM Mt a) : DcView Mt' G C st :=
  h.withChains rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
    (fun o ho x hx => hx.elim (fun hx => hb x ⟨o.hb, (G.str_mem ho).1, hx⟩)
      fun hx => hb x ⟨o.tb, (G.str_mem ho).2, hx⟩)
    (fun a ha _ => hg a ha)
    (stkChain_frame h.stk
      (ldv_glob hg .ld fun j hj => by simp only [widthOfM, DcGlob, dc_addrs] at hj ⊢; omega)
      fun bg hm x hx => hb x ⟨bg.1, G.stk_mem hm, hx⟩)
    fun r hr => regChain_frame (h.regs r hr)
      (ldv_glob hg .ld fun j hj => by simp only [widthOfM, DcGlob, regAddr, dc_addrs] at hj ⊢; omega)
      fun be hm c hc x hx => hb x ⟨c, by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact G.reg_mem hr hm
        · obtain ⟨bn, hn, rfl⟩ := List.mem_map.mp hc
          exact G.arr_mem hr hm hn, hx⟩

end Dc.Mach
