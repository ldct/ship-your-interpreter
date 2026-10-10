import Dc.Mach.BootImage
import Vsa.Elf

/-!
# dc boot replay: the kernel's `dcBoot prog` facts hold of the machine's state

Run: `lake env lean --run scripts/dc/DcBootReplay.lean [elf] < programs`
(programs NUL-separated on stdin, as `scripts/dc/DcElfRun.lean` reads them).

For each program `prog` (`|prog| < 8192`, no NUL), it patches the ELF's
script buffer (after the magic `@@DC-SCRIPT-v1@@`), parses it, and checks
natively:

* `DcElfLoads elf prog` (`elfPieces elf = dcImagePieces prog`, evaluated as
  `fastPieces` after `textKeysOk`), so the
  loader's memory is `dcLoadedMem prog` (`dc_initializeMemory_eq`);
* after `Vsa.setupElf`, every field of `DcLoaded prog`: the `GoodState`
  control registers equal `dcBoot prog`'s, `PC = 0x80000000`, `x1 … x31`
  present, `htif_payload_writes = 0`, the loader's bytes `dcImageByte prog`
  on `dcBootPieces`, no output; the clock counter is `0`.

This is native evaluation (not kernel-checked): the evidence that the state
the binary reaches satisfies the hypothesis `DcLoaded prog c` of the
kernel-checked theorems. Exit status 0 iff every check passes.
-/

open Vsa Vsa.Sim Vsa.Sim.Boot Dc.Mach LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Vsa.Machine

def magic : List UInt8 := "@@DC-SCRIPT-v1@@".toUTF8.toList

def findMagic (b : ByteArray) : Option Nat := Id.run do
  for i in [0:b.size - magic.length] do
    if (List.range magic.length).all fun j => b[i + j]! == magic[j]! then
      return some i
  return none

def patch (b : ByteArray) (off : Nat) (prog : List UInt8) : ByteArray := Id.run do
  let mut out := b
  for i in [0:8192] do
    out := out.set! (off + i) (prog.getD i 0)
  return out

/-- `dcText` as an array; `textKeysOk` checks its `i`-th key is
`0x80000000 + i`, so `dcText.lookup (0x80000000 + i) = some textArr[i].2`
and `fastByte prog` is `dcImageByte prog` (without its quadratic lookup). -/
def textArr : Array (Nat × BitVec 8) := dcText.toArray

def textKeysOk : Bool :=
  textArr.size == dcTextLen && (List.range dcTextLen).all fun i => textArr[i]!.1 == 0x80000000 + i

def fastByte (prog : List Nat) (x : Nat) : BitVec 8 :=
  if 0x80000000 ≤ x ∧ x < 0x80000000 + dcTextLen then textArr[x - 0x80000000]!.2 else dcImageByte prog x

def fastPieces (prog : List Nat) : List (Nat × List UInt8) :=
  dcBootPieces.map fun p => (p.1, (List.range p.2).map fun i => UInt8.ofBitVec (fastByte prog (p.1 + i)))

def check (label : String) (ok : Bool) : IO Bool := do
  unless ok do IO.println s!"  [BAD] {label}"
  pure ok

def checkOne (elfB : ByteArray) (off : Nat) (p : List UInt8) : IO Bool := do
  let prog := p.map (·.toNat)
  match mkRawELFFile? (patch elfB off p) with
  | .ok (.elf64 elf) =>
    let mut ok := true
    ok := (← check "DcElfLoads" (decide (elfPieces elf = fastPieces prog))) && ok
    let σ0 : SequentialState RegisterType trivialChoiceSource :=
      ⟨Std.ExtDHashMap.emptyWithCapacity, (), initializeMemory .B64 elf, default, default, default⟩
    match (Vsa.setupElf elf).run σ0 with
    | .error e _ => IO.println s!"  setup error: {e.print}"; pure false
    | .ok _ σ =>
      let bs := (dcBoot prog).σ
      let eq64 (r : Register) (h : RegisterType r = BitVec 64) : Bool :=
        (h ▸ σ.regs.get? r : Option (BitVec 64)) == (h ▸ bs.regs.get? r : Option (BitVec 64))
      let pres64 (r : Register) (h : RegisterType r = BitVec 64) : Bool :=
        (h ▸ σ.regs.get? r : Option (BitVec 64)).isSome
      ok := (← check "cur_privilege" ((σ.regs.get? Register.cur_privilege : Option Privilege) ==
        (bs.regs.get? Register.cur_privilege : Option Privilege))) && ok
      ok := (← check "misa" (eq64 Register.misa rfl)) && ok
      ok := (← check "mstatus" (eq64 Register.mstatus rfl)) && ok
      ok := (← check "mie" (eq64 Register.mie rfl)) && ok
      ok := (← check "mseccfg" (eq64 Register.mseccfg rfl)) && ok
      ok := (← check "satp" (eq64 Register.satp rfl)) && ok
      ok := (← check "mtvec" (eq64 Register.mtvec rfl)) && ok
      ok := (← check "mideleg" (eq64 Register.mideleg rfl)) && ok
      ok := (← check "medeleg" (eq64 Register.medeleg rfl)) && ok
      ok := (← check "menvcfg" (eq64 Register.menvcfg rfl)) && ok
      ok := (← check "mcyclecfg" (eq64 Register.mcyclecfg rfl)) && ok
      ok := (← check "minstretcfg" (eq64 Register.minstretcfg rfl)) && ok
      ok := (← check "htif_tohost present" (pres64 Register.htif_tohost rfl)) && ok
      ok := (← check "mip present" (pres64 Register.mip rfl)) && ok
      ok := (← check "mtime present" (pres64 Register.mtime rfl)) && ok
      ok := (← check "mtimecmp present" (pres64 Register.mtimecmp rfl)) && ok
      ok := (← check "minstret present" (pres64 Register.minstret rfl)) && ok
      ok := (← check "mcycle present" (pres64 Register.mcycle rfl)) && ok
      ok := (← check "nextPC present" (pres64 Register.nextPC rfl)) && ok
      ok := (← check "mcountinhibit" ((σ.regs.get? Register.mcountinhibit : Option (BitVec 32)) ==
        (bs.regs.get? Register.mcountinhibit : Option (BitVec 32)))) && ok
      ok := (← check "elp" ((σ.regs.get? Register.elp : Option (BitVec 1)) == some 0#1)) && ok
      ok := (← check "hart_state" ((σ.regs.get? Register.hart_state : Option HartState) ==
        (bs.regs.get? Register.hart_state : Option HartState))) && ok
      ok := (← check "htif_done = false" ((σ.regs.get? Register.htif_done : Option Bool) == some false)) && ok
      ok := (← check "htif_tohost_base" ((σ.regs.get? Register.htif_tohost_base : Option (Option (BitVec 64))) ==
        (bs.regs.get? Register.htif_tohost_base : Option (Option (BitVec 64))))) && ok
      ok := (← check "pmpcfg_n" ((σ.regs.get? Register.pmpcfg_n : Option (Vector Pmpcfg_ent 64)) ==
        (bs.regs.get? Register.pmpcfg_n : Option (Vector Pmpcfg_ent 64)))) && ok
      ok := (← check "pmpaddr_n" ((σ.regs.get? Register.pmpaddr_n : Option (Vector (BitVec 64) 64)) ==
        (bs.regs.get? Register.pmpaddr_n : Option (Vector (BitVec 64) 64)))) && ok
      ok := (← check "pma_regions" ((σ.regs.get? Register.pma_regions : Option (List PMA_Region)) ==
        (bs.regs.get? Register.pma_regions : Option (List PMA_Region)))) && ok
      ok := (← check "sig_meip present" (σ.regs.get? Register.sig_meip : Option (BitVec 1)).isSome) && ok
      ok := (← check "sig_seip present" (σ.regs.get? Register.sig_seip : Option (BitVec 1)).isSome) && ok
      ok := (← check "minstret_increment present"
        (σ.regs.get? Register.minstret_increment : Option Bool).isSome) && ok
      ok := (← check "PC = 0x80000000" ((σ.regs.get? Register.PC : Option (BitVec 64)) == some 0x80000000#64)) && ok
      ok := (← check "x1..x31 present" ((List.range 31).all fun j => (gprGet σ (j + 1)).isSome)) && ok
      ok := (← check "htif_payload_writes = 0"
        ((σ.regs.get? Register.htif_payload_writes : Option (BitVec 4)) == some 0#4)) && ok
      ok := (← check "no output" (σ.sailOutput.size == 0)) && ok
      ok := (← check "loader bytes on dcBootPieces" (dcBootPieces.all fun (b, n) =>
        (List.range n).all fun i => σ.mem[b + i]? == some (fastByte prog (b + i)))) && ok
      pure ok
  | _ => IO.println "  ELF parse error"; pure false

def main (args : List String) : IO UInt32 := do
  let path := args.headD "dc-port/dc-riscv-htif.elf"
  let elfB ← IO.FS.readBinFile path
  let some m := findMagic elfB | do IO.eprintln "magic not found"; return 1
  let input ← (← IO.getStdin).readBinToEnd
  let mut bad := 0
  let mut n := 0
  unless textKeysOk do IO.println "dcText keys are not 0x80000000 + i"; return 1
  for p in input.toList.splitOn 0 do
    if p.isEmpty || p.length ≥ 8192 then continue
    n := n + 1
    if !(← checkOne elfB (m + 16) p) then
      bad := bad + 1
      IO.println s!"FAIL program {n}"
  IO.println s!"dc boot replay: {n} programs, {bad} failing"
  pure (if bad == 0 then 0 else 1)
