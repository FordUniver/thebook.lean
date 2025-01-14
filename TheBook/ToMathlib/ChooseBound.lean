import Mathlib.Data.Nat.Choose.Basic

-- https://github.com/leanprover-community/mathlib4/pull/20735

namespace Nat

theorem choose_succ_le_two_pow {n k : ℕ} : (n + 1).choose k <= 2 ^ n := by
  by_cases lt : n + 1 < k
  · simp [choose_eq_zero_of_lt lt]
  · cases' n with n
    · cases k <;> simp_all
    · cases' k with k
      · exact Nat.one_le_two_pow
      · calc
          (n + 2).choose (k + 1) =
            (n + 1).choose k +
            (n + 1).choose (k + 1)           := by simp [choose_succ_succ']
          _ ≤ 2 ^ n + (n + 1).choose (k + 1) := Nat.add_le_add_right choose_succ_le_two_pow _
          _ ≤ 2 ^ n + 2 ^ n                  := Nat.add_le_add_left choose_succ_le_two_pow _
          _ = 2 ^ (n + 1)                    := Eq.symm (two_pow_succ n)

end Nat
