import Dc.Num

/-!
# Number widths

`Num.wid n` is the number of digits bc stores for `n` at most: the decimal
length of the magnitude plus the scale. The size hypothesis of the
refinement theorem bounds the widths of the numbers the arithmetic commands
receive.
-/

namespace Dc

/-- The decimal length of a magnitude (at least one digit). -/
def decLen (n : Nat) : Nat := if n < 10 then 1 else decLen (n / 10) + 1
decreasing_by omega

theorem one_le_decLen (n : Nat) : 1 ≤ decLen n := by
  unfold decLen; split <;> omega

theorem lt_pow_decLen (n : Nat) : n < 10 ^ decLen n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold decLen
    split
    · omega
    · have := ih (n / 10) (by omega)
      rw [Nat.pow_succ]
      omega

/-- The digits bc stores for `n` at most. -/
def Num.wid (n : Num) : Nat := decLen n.mag + n.scale

end Dc
