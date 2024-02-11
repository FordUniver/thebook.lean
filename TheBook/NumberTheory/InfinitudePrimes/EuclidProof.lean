import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Set.Finite

open scoped BigOperators

theorem euclid_infinitude_primes
  (S : Finset ℕ) (hS : ∀ s ∈ S, Nat.Prime s) : ∃ p, Nat.Prime p ∧ p ∉ S := by {
    let n := (∏ i in S, i).succ

    have n_ne_one : n ≠ 1 := by {
      rw [Nat.succ_ne_succ, Finset.prod_ne_zero_iff]
      exact fun s s_in_S => Nat.Prime.ne_zero (hS s s_in_S)
    }

    obtain ⟨p, p_prime, p_dvd_n⟩ : ∃ p, Nat.Prime p ∧ p ∣ n :=
      Nat.exists_prime_and_dvd n_ne_one

    have p_not_in_S : p ∉ S := by {
      by_contra p_in_S
      have p_dvd_ProdS : p ∣ (∏ i in S, i) := Finset.dvd_prod_of_mem (fun i => i) p_in_S
      have p_dvd_one : p ∣ 1 := (Nat.dvd_add_right p_dvd_ProdS).mp p_dvd_n
      have p_ndvd_one : ¬p ∣ 1 := Nat.Prime.not_dvd_one p_prime
      contradiction
    }

    exact ⟨p, p_prime, p_not_in_S⟩
  }


theorem euclid_infinitude_primes_standardised : { p : ℕ | Nat.Prime p}.Infinite := by {
  rw [Set.Infinite]
  by_contra con

  let S := Set.Finite.toFinset con
  have S_prime : ∀ p ∈ S, Nat.Prime p := by {
    intro p p_in_S
    rw [Set.Finite.mem_toFinset con] at p_in_S
    rw [Set.mem_setOf_eq] at p_in_S
    exact p_in_S
  }

  obtain ⟨p, ⟨p_prime, p_not_in_S⟩⟩ := euclid_infinitude_primes S S_prime

  apply p_not_in_S
  rw [Set.Finite.mem_toFinset con]
  rw [Set.mem_setOf_eq]
  exact p_prime
}
