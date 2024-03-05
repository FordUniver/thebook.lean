import Mathlib.Tactic

open scoped Nat BigOperators

theorem mathlib_infinitude_primes
  (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by {
    let p := Nat.minFac (n ! + 1)

    have f1 : n ! + 1 ≠ 1 := Nat.ne_of_gt <| Nat.succ_lt_succ <| Nat.factorial_pos _
    have p_prime : Nat.Prime p := Nat.minFac_prime f1
    have p_ge_n : n ≤ p :=
      le_of_not_ge fun h ↦
        have h₁ : p ∣ n ! := Nat.dvd_factorial (Nat.minFac_pos _) h
        have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (Nat.minFac_dvd _)
        p_prime.not_dvd_one h₂

    exact ⟨p, p_ge_n, p_prime⟩
  }
