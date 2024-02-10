import Mathlib.Tactic

open scoped Nat BigOperators

-- TODO: remove hS requirement

theorem infinitude_primes
  (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) : ∃ p, Nat.Prime p ∧ p ∉ S := by {
    let sprod := (∏ i in S, i)
    have sprod_ne_zero : sprod ≠ 0 := by {
      rw [Finset.prod_ne_zero_iff]
      intro s s_in_S
      exact Nat.Prime.ne_zero (hS s s_in_S)
    }

    let n := sprod + 1
    have n_ne_one : n ≠ 1 := Nat.succ_ne_succ.mpr sprod_ne_zero

    obtain ⟨p, p_prime, p_div_n⟩ : ∃ p, Nat.Prime p ∧ p ∣ n :=
      Nat.exists_prime_and_dvd n_ne_one

    have p_not_in_S : p ∉ S := by {
      by_contra p_in_S
      have p_dvd_sprod : p ∣ sprod := Finset.dvd_prod_of_mem (fun i => i) p_in_S
      have p_dvd_one : p ∣ 1 := (Nat.dvd_add_right p_dvd_sprod).mp p_div_n
      have p_not_dvd_one : ¬p ∣ 1 := Nat.Prime.not_dvd_one p_prime
      contradiction
    }

    use p, p_prime, p_not_in_S
  }

theorem canonical_infinitude_primes :
  Infinite { p : ℕ | Nat.Prime p} := by {
    sorry
  }
