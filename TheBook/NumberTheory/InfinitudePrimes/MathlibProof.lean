import Mathlib.Tactic

open scoped Nat BigOperators

theorem infinitude_primes (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
  let p := Nat.minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := Nat.ne_of_gt <| Nat.succ_lt_succ <| Nat.factorial_pos _
  have pp : Nat.Prime p := Nat.minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := Nat.dvd_factorial (Nat.minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (Nat.minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩

-- can also get this from the 'actual' Euclid's proof

theorem canonical_infinitude_primes :
  Infinite { p : ℕ | Nat.Prime p} := by {
    sorry
  }
