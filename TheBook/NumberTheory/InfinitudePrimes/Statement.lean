import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic.TFAE

theorem infinitude_of_primes_tfae : List.TFAE [
    { p : ℕ | Nat.Prime p}.Infinite,
    ∀ (S : Finset ℕ), (∃ p, Nat.Prime p ∧ p ∉ S),
    (∀ (S : Finset ℕ) (_ : ∀ s ∈ S, Nat.Prime s), (∃ p, Nat.Prime p ∧ p ∉ S)),
    (∀ n : ℕ, (∃ p, Nat.Prime p ∧ p > n)),
    ∃ (P : ℕ → ℕ), (Function.Injective P) ∧ (∀ k, (P k).Prime) ] := by

  tfae_have 1 ↔ 2 := by
    constructor
    · exact fun primes_are_infinite S => Set.Infinite.exists_not_mem_finset primes_are_infinite S
    · intro rhs
      by_contra con
      simp [Set.Infinite] at con
      obtain ⟨p, ⟨p_prime, p_not_in_S⟩⟩ := rhs (Set.Finite.toFinset con)
      rw [Set.Finite.mem_toFinset con, Set.mem_setOf_eq] at p_not_in_S
      contradiction

  tfae_have 2 ↔ 3 := by
    constructor
    · exact fun a S _ => a S
    · intro rhs S
      let Sprimes := S.filter Nat.Prime
      obtain ⟨p, p_prime, p_notin_Sprimes⟩ := rhs Sprimes (fun _ g => (Finset.mem_filter.mp g).right)
      obtain p_notin_S := fun p_in_S => p_notin_Sprimes (Finset.mem_filter.mpr ⟨p_in_S, p_prime⟩)
      exact ⟨p, ⟨p_prime, p_notin_S⟩⟩

  tfae_have 4 ↔ 2 := by
    constructor
    · intro lhs S
      by_cases h : S.Nonempty
      · let S_max := Finset.max' S h
        obtain ⟨p, p_prime, p_gt_maxS⟩ := lhs S_max
        obtain p_notin_S := fun p_in_S => LT.lt.false (Nat.lt_of_le_of_lt (Finset.le_max' S p p_in_S) p_gt_maxS )
        exact ⟨p, ⟨p_prime, p_notin_S⟩⟩
      · rw [Finset.not_nonempty_iff_eq_empty.mp h]
        exact ⟨2, Nat.prime_two, Finset.not_mem_empty 2⟩
    · intro rhs n
      obtain ⟨p, p_prime, p_notin_S⟩ := rhs (Finset.range (n + 1))
      have h : p > n := by simp [Finset.mem_range] at p_notin_S; exact p_notin_S
      exact ⟨p, ⟨p_prime, h⟩⟩

  tfae_have 1 ↔ 5 := by
    constructor
    · let primes := { p : ℕ | Nat.Prime p}
      let P := fun n => (Nat.nth (primes.Mem) n)
      exact fun h => ⟨P, Nat.nth_injective h, fun k => Nat.nth_mem_of_infinite h k⟩
    · intro ⟨P, P_inj, P_im_prime⟩
      exact Set.infinite_of_injective_forall_mem P_inj P_im_prime

  tfae_finish
