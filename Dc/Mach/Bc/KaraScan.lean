import Dc.Mach.Bc.KaraState
import Dc.Mach.Bc.Scan

/-!
# `_bc_rec_mul`'s inlined `bc_is_zero` tests

`bc_is_zero (h)` inlined six times (`u1`, `v1`, `d1`, `d2`, `u0`, `v0`): the
handle is `_zero_` itself, or its digits are scanned. The tests are generated
(`scripts/dc/gen_kara_scan.py` → `KaraScanSites.lean`); `HdZero` is what the
zero outcome tells.
-/

namespace Dc.Mach

/-- The handle is `_zero_`, or all its digits are zero. -/
def HdZero (h : Hd) : Prop := ∀ x, h = some x → ∀ j, j < x.rep.len + x.rep.scale → x.rep.ds.getD j 0 = 0

end Dc.Mach
