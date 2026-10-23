import Vsa.ElfRun

/-! Runs `dc-port/dc-riscv-htif.elf` on the Sail RV64 model of the proof
(`Vsa.runElf`: `setupElf` + `stepOnce`). Reads NUL-separated programs from
stdin; for each, writes it into the ELF's script buffer (after the magic
`@@DC-SCRIPT-v1@@`), runs the machine, and prints one line:
`<exit code> <steps> <hex of console output>`, or `FUEL <steps>`/`ERROR`. -/

def hex (bs : List Nat) : String :=
  let h := "0123456789abcdef".toList
  String.join (bs.map fun b => String.ofList [h[b / 16]!, h[b % 16]!])

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

def main (args : List String) : IO UInt32 := do
  let path := args.headD "dc-port/dc-riscv-htif.elf"
  let fuel := (args[1]? >>= String.toNat?).getD 200000000
  let elfB ← IO.FS.readBinFile path
  let some m := findMagic elfB | do IO.eprintln "magic not found"; return 1
  let input ← (← IO.getStdin).readBinToEnd
  for p in input.toList.splitOn 0 do
    if p.isEmpty then continue
    if p.length ≥ 8192 then IO.println "ERROR too long"; continue
    match mkRawELFFile? (patch elfB (m + 16) p) with
    | .ok (.elf64 elf) =>
      match Vsa.runElf elf fuel with
      | .ok r =>
        let out := r.output.toList.map Char.toNat
        match r.exitCode with
        | some c => IO.println s!"{c} {r.steps} {hex out}"
        | none => IO.println s!"FUEL {r.steps}"
      | .error e => IO.println s!"ERROR {e}"
    | _ => IO.println "ERROR parse"
  return 0
