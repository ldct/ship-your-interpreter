import Dc.Interp

/-! Differential-test driver: reads NUL-separated programs from stdin and,
for each, prints the hex of `runOut` (or `NONE`) on its own line. The line
length is the first command-line argument (default 70). -/

def hex (bs : List Nat) : String :=
  String.join (bs.map fun b =>
    let h := "0123456789abcdef".toList
    String.ofList [h[b / 16]!, h[b % 16]!])

def main (args : List String) : IO Unit := do
  let lm := (args.head? >>= String.toNat?).getD 70
  let input ← (← IO.getStdin).readBinToEnd
  let progs := (input.toList.map UInt8.toNat).splitOn 0
  for p in progs do
    if p.isEmpty then continue
    match Dc.runOut lm 1000000 p with
    | some out => IO.println (hex out)
    | none => IO.println "NONE"
