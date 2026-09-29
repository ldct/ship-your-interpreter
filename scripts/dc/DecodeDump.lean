import Vsa.ElfRun

/-! Prints `<word>;OK;<ast>` for every hex instruction word on stdin, the
Sail decoder's result in the machine state `setupElf` produces (decoding
reads only `misa`, the privilege and `mseccfg`). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1

def parseHex (s : String) : Nat :=
  s.foldl (fun a c => a * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 87)) 0

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Vsa.whileElf? with
  | .error e => IO.println s!"ELF-ERR {e}"
  | .ok elf =>
    match (Vsa.setupElf elf).run (Vsa.initState elf) with
    | .error e _ => IO.println s!"SETUP-ERR {e.print}"
    | .ok _ σ' =>
      for l in input.splitOn "\n" do
        if l.trim.isEmpty then continue
        let w : BitVec 32 := BitVec.ofNat 32 (parseHex l.trim)
        match (ext_decode w).run σ' with
        | .ok ast _ => IO.println s!"{l.trim};OK;{(toString (repr ast)).replace "\n" " "}"
        | .error e _ => IO.println s!"{l.trim};ERR;{e.print}"
