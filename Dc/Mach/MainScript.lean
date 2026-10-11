import Dc.Mach.Strlen

/-!
# `main`'s script length

`main` (`0x80000b00`) measures the embedded script before evaluating it:

```
80000b28 auipc a0,0x1a ; 80000b2c addi a0,a0,520   (a0 = dc_script + 0x10)
80000b30 jal   strlen
80000b34 mv    a1,a0 …
```

`main_scriptLen` runs the two address instructions and the call with
`dx_run` (stopping at `strlen`'s entry) and closes the call by `strlen_spec`:
the first use of the driver on straight-line code and a call.
-/

namespace Dc.Mach

open Vsa.MemRepr VsaIris.Sym VsaIris.MallocFast

/-- The embedded script's text (`dc_script + 0x10`, in `.data`). -/
abbrev scriptAddr : Nat := 0x8001ad30

/-- **`main`'s `strlen(script)`.** From `0x80000b28` with the script an owned
C string of length `len`: back at `0x80000b34` with `a0 = len`, `ra` the
return address, and every other register but `a4`/`a5` unchanged. -/
theorem main_scriptLen {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Mt : Mem}
    (hlive : ∀ p ∈ dcText, live p.1) {len : Nat} (hs : OwnedCStr S Mt scriptAddr len)
    (R : Nat → BitVec 64)
    (hk : ∀ R', R' 10 = BitVec.ofNat 64 len → StrlenKeep R' (upd R 1 0x80000b34#64) →
      DW live S Q 0x80000b34#64 R' Mt) :
    DW live S Q 0x80000b28#64 R Mt := by
  dx_run hlive at 0x80000904
  refine strlen_spec hlive hs _ rfl (by simp only [upd_same]; decide)
    fun R' h10 hkeep => hk R' h10 fun z h1 h2 h3 => ?_
  rw [hkeep z h1 h2 h3]
  simp only [upd_apply]
  split <;> simp

end Dc.Mach
