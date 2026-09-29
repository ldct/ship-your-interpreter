import Dc.Mach.Steps
import Dc.Mach.Htif
import VsaIris.Vsa.AllocTac

/-!
# Driving the dc step table

`dx_run h` runs dc's code symbolically from a `DW … pc R Mt` goal, the dc
twin of `sx_run` (`VsaIris/Vsa/AllocTac.lean`, whose side-condition tactics
`sx_side`, `sx_norm`, `sx_mem` it reuses). At a literal PC it tries the step
lemmas of the instruction in order — `st_<pc>` (owned bytes), `stR_<pc>`
(`.rodata` loads), `stO_<pc>` (observed `sltu`/`sltiu`), `stL_<pc>` (observed
`lb` of an owned byte) — and takes the first
whose side conditions `sx_side` closes (else `st_<pc>` with its side
conditions left open). `h : ∀ p ∈ dcText, live p.1`.

The run stops at a branch it cannot decide, at a symbolic PC (`ret`, `jr`),
at a `tohost` store (`stP_<pc>`, `Tohost.lean`, takes the printed byte),
at a PC listed after `at` (the entries of functions with their own specs, so
a call is closed by the callee's spec), or after the fuel (default 400
instructions; `dx_run [n] h`).
-/

namespace Dc.Mach

open Lean Elab Tactic Meta VsaIris.Sym

private def hex8 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (8 - s.length) (Char.ofNat 48)) ++ s

/-- Try `sx_side` on a goal; `true` when it closes. -/
private def trySide (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| ((try sx_norm) <;> (try sx_mem) <;> sx_side))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

/-- Close a branch goal `C → DW …` when `sx_side` refutes `C`. -/
private def tryPrune (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| (intro hc; exfalso; ((try sx_norm) <;> (try sx_mem) <;> (revert hc; sx_side))))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

/-- Apply one step lemma; split the new goals into continuations and side
conditions `sx_side` cannot close. -/
private def applyStep (h : Syntax) (nm : Name) (g : MVarId) :
    TacticM (Option (List MVarId × List MVarId)) := do
  unless (← getEnv).contains nm do return none
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| apply $(mkIdent nm) $(⟨h⟩))) g
    let mut conts : List MVarId := []
    let mut open_ : List MVarId := []
    for g' in gs do
      let ty ← g'.withContext (do instantiateMVars (← g'.getType))
      if ← g'.withContext (forallTelescopeReducing ty fun _ b => isSWP b) then
        conts := conts ++ [g']
      else if !(← trySide g') then
        open_ := open_ ++ [g']
    return some (conts, open_)
  catch _ =>
    saved.restore; return none

/-- One step at a literal PC: the first variant whose side conditions all
close, else `st_<pc>` with its open side conditions. -/
def dxStep (h : Syntax) (g : MVarId) : TacticM (Option (List MVarId × List MVarId)) := do
  let some pc ← g.withContext (do swpPC? (← g.getType)) | return none
  let base := Name.mkStr (Name.mkStr .anonymous "Dc") "Mach"
  if (← getEnv).contains (Name.mkStr base s!"stP_{hex8 pc}") then return none
  let names := ["st_", "stR_", "stO_", "stL_"].map fun p => Name.mkStr base s!"{p}{hex8 pc}"
  let mut fallback : Option (List MVarId × List MVarId × Tactic.SavedState) := none
  for nm in names do
    let saved ← saveState
    match ← applyStep h nm g with
    | some (conts, []) => return some (conts, [])
    | some (conts, open_) =>
      if fallback.isNone then fallback := some (conts, open_, ← saveState)
      saved.restore
    | none => saved.restore
  match fallback with
  | some (conts, open_, st) => st.restore; return some (conts, open_)
  | none => return none

/-- `dx_run h`, `dx_run [n] h`, `dx_run h at pc…`. -/
syntax "dx_run " ("[" num "] ")? term (" at " num+)? : tactic

elab_rules : tactic
  | `(tactic| dx_run $[[$n]]? $h $[at $stops*]?) => do
    let budget := (n.map (·.getNat)).getD 400
    let stopPCs : List Nat := match stops with
      | some ss => ss.toList.map (·.getNat)
      | none => []
    let mut pending : List MVarId := []
    let mut cur ← getMainGoal
    let mut stuck : List MVarId := []
    let mut first := true
    for _ in [0:budget] do
      if let some pc ← cur.withContext (do swpPC? (← cur.getType)) then
        if !first && stopPCs.contains pc then stuck := [cur]; break
      first := false
      let some (conts, open_) ← dxStep h cur | stuck := [cur]; break
      pending := pending ++ open_
      match conts with
      | [c] =>
        let c ← do
          let saved ← saveState
          try
            match ← evalTacticAt (← `(tactic| ((try sx_norm) <;> (try sx_mem)))) c with
            | [c'] => pure c'
            | _ => saved.restore; pure c
          catch _ => saved.restore; pure c
        if (← c.withContext (do swpPC? (← c.getType))).isSome then
          cur := c
        else
          stuck := [c]; break
      | [t, f] =>
        if ← tryPrune t then
          let [f'] ← evalTacticAt (← `(tactic| intro hc)) f | stuck := [f]; break
          cur := f'
        else if ← tryPrune f then
          let [t'] ← evalTacticAt (← `(tactic| intro hc)) t | stuck := [t]; break
          cur := t'
        else
          stuck := [t, f]; break
      | cs => stuck := cs; break
    if stuck.isEmpty then stuck := [cur]
    setGoals (pending ++ stuck)

end Dc.Mach
