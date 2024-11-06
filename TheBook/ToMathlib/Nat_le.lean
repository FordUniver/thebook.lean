import Mathlib.Data.Nat.Defs

-- https://github.com/leanprover-community/mathlib4/pull/18694

namespace Nat

theorem le_div_iff_mul_le2' {a b c : Nat} (hb : 0 < b) : a ≤ c / b ↔ b * a ≤ c := by
   rw [Nat.mul_comm]
   exact Nat.le_div_iff_mul_le' hb

end Nat
