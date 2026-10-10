import Dc.Mach.BootImage
import Dc.Mach.HaltsP

/-!
# The loaded configuration's facts (M11)

From `DcLoaded prog c` (`BootImage.lean`) and an admissible program
(`DcProg`: shorter than the script buffer, no `NUL`, bytes), every
configuration fact `dc_halts`/`dc_halts_wp`/`dc_stuck` take: the live code
(`dcLive`, `DcLoaded.vsaOk`), `PC = _start`, the code bytes
(`DcLoaded.text`), the owned bytes (`dcOwn`, everything writable from the
HTIF words to `__stack_top`, enumerated by `dcOwnList`, apart from the code),
and `StartPre` (`DcLoaded.start`: `.data`'s dc words and the script).
`dc_halts_loaded`, `dc_halts_wp_loaded`, `dc_stuck_loaded` restate the
three theorems at such a configuration; `dcBoot_loaded` instantiates them at
`dcBoot prog`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim Vsa.Sim.Boot VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open Vsa.Machine (Config)

/-- The bytes a dc run reads without owning: the code (`.text`, `.rodata`). -/
def dcLive (a : Nat) : Prop := 0x80000000 ≤ a ∧ a < 0x80000000 + dcTextLen

/-- Every code byte's address lies in the code piece (one kernel check). -/
theorem dcText_inB :
    (dcText.all fun p => decide (0x80000000 ≤ p.1 ∧ p.1 < 0x80000000 + dcTextLen)) = true := by
  decide +kernel

theorem dcText_live : ∀ p ∈ dcText, dcLive p.1 := fun p hp => by
  have := List.all_eq_true.1 dcText_inB p hp
  simpa [dcLive] using this

/-- The bytes a dc run owns: every writable byte from the HTIF words to `__stack_top`. -/
def dcOwn (a : Nat) : Prop := tohostAddr + 16 ≤ a ∧ a < stackTop

/-- Their enumeration. -/
def dcOwnList : List Nat := List.range' (tohostAddr + 16) (stackTop - (tohostAddr + 16))

theorem dcOwnList_spec : dcOwnList.Nodup ∧ ∀ a, a ∈ dcOwnList ↔ dcOwn a :=
  ⟨List.nodup_range', fun a => by
    simp only [dcOwnList, dcOwn, List.mem_range'_1, stackTop, tohostAddr]⟩

theorem dcOwn_sep : ∀ a ∈ dcOwnList, ∀ p ∈ dcText, p.1 ≠ a := fun a ha p hp e => by
  have h1 := (dcOwnList_spec.2 a).1 ha
  have h2 := dcText_live p hp
  subst e
  simp only [dcOwn, dcLive, dcTextLen, tohostAddr] at h1 h2
  omega

/-- **An admissible script**: it fits the buffer with its `NUL`, has no `NUL`,
and is bytes. -/
structure DcProg (prog : List Nat) : Prop where
  len : prog.length < 8192
  nz : 0 ∉ prog
  byte : ∀ c ∈ prog, c < 256

/-- A code byte's address is in the loader's pieces. -/
theorem inPieces_of_live {a : Nat} (h : dcLive a) : inPieces dcBootPieces a = true := by
  simp only [dcLive, dcTextLen] at h
  simp only [inPieces, dcBootPieces, List.any_cons, List.any_nil, Bool.or_eq_true,
    decide_eq_true_eq, Bool.or_false]
  omega

/-- A key's first entry in a list with distinct keys. -/
theorem lookup_of_mem {β : Type} : ∀ (l : List (Nat × β)), (l.map Prod.fst).Nodup →
    ∀ p ∈ l, l.lookup p.1 = some p.2
  | [], _, _, hp => absurd hp List.not_mem_nil
  | q :: qs, hnd, p, hp => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [List.lookup]
    · have hne : p.1 ≠ q.1 := fun e => hnd.1 (e ▸ List.mem_map_of_mem hp)
      have hb : (p.1 == q.1) = false := by simpa using hne
      simp only [List.lookup, hb]
      exact lookup_of_mem qs hnd.2 p hp

namespace DcLoaded

variable {prog : List Nat} {c : Config}

/-- The loader's bytes, as the run reads them. -/
theorem img (h : DcLoaded prog c) {x : Nat} (hx : inPieces dcBootPieces x = true) :
    imgM c.σ.mem x = dcImageByte prog x := by
  unfold imgM; rw [h.mem x hx]; rfl

/-- **The global invariant** at a loaded configuration. -/
theorem vsaOk (h : DcLoaded prog c) : VsaOk dcLive c where
  good := h.good
  tick := h.tick
  gpr := h.gpr
  live a ha := by rw [h.mem a (inPieces_of_live ha)]; rfl
  htifIdle := h.htif

theorem vsaPC (h : DcLoaded prog c) : (vsaModel dcLive).reg c VsaIris.PC = 0x80000000#64 := by
  show vsaReg c VsaIris.PC = _
  simp [vsaReg, pcVal, h.pc]

/-- **The code bytes.** -/
theorem text (h : DcLoaded prog c) : ∀ p ∈ dcText, (vsaModel dcLive).mem c p.1 = p.2 := by
  intro p hp
  have hl := dcText_live p hp
  show imgM c.σ.mem p.1 = p.2
  rw [h.img (inPieces_of_live hl)]
  simp only [dcLive, dcTextLen] at hl
  simp only [dcImageByte, dcTextLen, show ¬ p.1 < 0x80000000 by omega, show p.1 < 0x80000000 + 33304 by omega,
    ↓reduceIte, lookup_of_mem dcText dcText_nodup p hp, Option.getD_some]

/-- A `.data` word outside the script buffer reads the loader's data. -/
theorem ldv_data (h : DcLoaded prog c) (k : MKind) {a : Nat}
    (ha : ∀ j, j < widthOfM k → (0x8001ad00 ≤ a + j ∧ a + j < scriptAddr) ∨
      (scriptAddr + 8192 ≤ a + j ∧ a + j < 0x8001ad00 + 8260)) :
    ldv k c.σ.mem a = ldvf k (fun x => dcDataByte (x - 0x8001ad00)) a := by
  suffices e : bytesAt (imgM c.σ.mem) a (widthOfM k) =
      bytesAt (fun x => dcDataByte (x - 0x8001ad00)) a (widthOfM k) by
    show bytesVal k _ = bytesVal k _
    rw [e]
  unfold bytesAt
  refine List.map_congr_left fun j hj => ?_
  have hj' := ha j (List.mem_range.mp hj)
  rw [h.img (by
    simp only [inPieces, dcBootPieces, List.any_cons, List.any_nil, Bool.or_eq_true,
      decide_eq_true_eq, Bool.or_false]
    simp only [scriptAddr] at hj'; omega)]
  simp only [scriptAddr] at hj'
  simp only [dcImageByte, dcTextLen, scriptAddr, show ¬ a + j < 0x80000000 by omega,
    show ¬ a + j < 0x80000000 + 33304 by omega, show ¬ (0x8001ad30 ≤ a + j ∧ a + j < 0x8001ad30 + 8192) by omega,
    ↓reduceIte]

/-- **`StartPre`** at a loaded configuration of an admissible script. -/
theorem start (h : DcLoaded prog c) (hp : DcProg prog) : StartPre dcOwn c.σ.mem prog := by
  have hlen := hp.len
  have hs : ∀ i, i ≤ prog.length → imgM c.σ.mem (scriptAddr + i) = BitVec.ofNat 8 (prog.getD i 0) :=
    fun i hi => by
      rw [h.img (by
        simp only [inPieces, dcBootPieces, List.any_cons, List.any_nil, Bool.or_eq_true,
          decide_eq_true_eq, Bool.or_false, scriptAddr]; omega)]
      simp only [dcImageByte, dcTextLen, scriptAddr, show ¬ 0x8001ad30 + i < 0x80000000 by omega,
        show ¬ 0x8001ad30 + i < 0x80000000 + 33304 by omega,
        show 0x8001ad30 ≤ 0x8001ad30 + i ∧ 0x8001ad30 + i < 0x8001ad30 + 8192 by omega, ↓reduceIte,
        Nat.add_sub_cancel_left, and_self]
  exact
    { own := fun a h1 h2 => ⟨h1, h2⟩
      ibase := (h.ldv_data .lw fun j hj => by
        simp only [widthOfM, scriptAddr, dc_addrs] at hj ⊢; omega).trans (by decide)
      obase := (h.ldv_data .lw fun j hj => by
        simp only [widthOfM, scriptAddr, dc_addrs] at hj ⊢; omega).trans (by decide)
      lineMax := (h.ldv_data .lw fun j hj => by
        simp only [widthOfM, scriptAddr, dc_addrs] at hj ⊢; omega).trans (by decide)
      outFd := (h.ldv_data .lw fun j hj => by
        simp only [widthOfM, scriptAddr, dc_addrs] at hj ⊢; omega).trans (by decide)
      errFd := (h.ldv_data .lw fun j hj => by
        simp only [widthOfM, scriptAddr, dc_addrs] at hj ⊢; omega).trans (by decide)
      text := fun i hi => hs i (by omega)
      nul := by rw [hs _ (Nat.le_refl _)]; simp [List.getD_eq_getElem?_getD]
      nz := hp.nz
      byte := hp.byte
      len := hp.len }

end DcLoaded

/-- **dc halts at a loaded configuration** (`dc_halts`). -/
theorem dc_halts_loaded {prog : List Nat} (c : Config) (h : DcLoaded prog c) (hp : DcProg prog)
    (φ : Nat × String → Prop) (hφ1 : ∀ t, φ (1, t))
    (hk : ∀ M1 R1 R' M' H' F L C b1 b2, Filled M1 c.σ.mem freeListAddr bssLen (fun _ => 0#8) →
      R1 1 = 0x8000003c#64 → R1 2 = BitVec.ofNat 64 stackTop →
      BootEval dcOwn stackTop mainW M1 R1 R' M' H' F L C (msObj b1 b2 prog) prog →
      DWO dcLive dcOwn (fun t rv mv => ExitQ φ t rv mv) (Vsa.Machine.output c.σ) 0x80001914#64 R' M') :
    ∃ e out, Vsa.Machine.Halts c out e ∧ φ (e, out) :=
  dc_halts c φ h.vsaOk dcText_live h.vsaPC h.text dcOwnList_spec dcOwn_sep (h.start hp) hφ1 hk

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode in
/-- **dc halts at a loaded configuration**, continuations as Iris
entailments (`dc_halts_wp`). -/
theorem dc_halts_wp_loaded {prog : List Nat} (c : Config) (h : DcLoaded prog c) (hp : DcProg prog)
    (ψ : Nat × String → Prop) (hψ1 : ∀ t, ψ (1, t))
    (hev : ∀ [_G : MachGS .hasLC MachGF], ∀ rv mv M1 R1 R' M' H' F L C b1 b2,
      EvalCallAt dcOwn c.σ.mem prog rv mv M1 R1 R' M' H' F L C b1 b2 →
      roOwn (GF := MachGF) roR dcText ∗ RunRes dcOwn (Vsa.Machine.output c.σ) rv mv ⊢
        (twpW (GF := MachGF) (vsaModel dcLive)).W (fun v => iprop(⌜ψ v⌝))) :
    ∃ e out, Vsa.Machine.Halts c out e ∧ ψ (e, out) :=
  dc_halts_wp c ψ h.vsaOk dcText_live h.vsaPC h.text dcOwnList_spec dcOwn_sep (h.start hp) hψ1 hev

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode in
/-- **dc diverges or halts at a loaded configuration** (`dc_stuck`). -/
theorem dc_stuck_loaded {prog : List Nat} (c : Config) (h : DcLoaded prog c) (hp : DcProg prog)
    (ψ : Nat × String → Prop) (hψ1 : ∀ t, ψ (1, t))
    (hev : ∀ [_G : MachGS .hasLC MachGF], ∀ rv mv M1 R1 R' M' H' F L C b1 b2,
      EvalCallAt dcOwn c.σ.mem prog rv mv M1 R1 R' M' H' F L C b1 b2 →
      roOwn (GF := MachGF) roR dcText ∗ RunRes dcOwn (Vsa.Machine.output c.σ) rv mv ⊢
        (wpW (GF := MachGF) (vsaModel dcLive)).W (fun v => iprop(⌜ψ v⌝))) :
    Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ ψ (e, out) :=
  dc_stuck c ψ h.vsaOk dcText_live h.vsaPC h.text dcOwnList_spec dcOwn_sep (h.start hp) hψ1 hev

end Dc.Mach
