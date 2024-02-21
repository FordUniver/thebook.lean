import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite

open Function

namespace infinitude_primes_equivalence

theorem first_equivalence : { p : ℕ | Nat.Prime p}.Infinite ↔ ∀ (S : Finset ℕ), (∃ p, Nat.Prime p ∧ p ∉ S) := by
  apply Iff.intro
  · exact λ primes_are_infinite S => Set.Infinite.exists_not_mem_finset primes_are_infinite S
  · intro h
    by_contra con
    simp [Set.Infinite] at con
    obtain ⟨p, ⟨p_prime, p_not_in_S⟩⟩ := h (Set.Finite.toFinset con)
    rw [Set.Finite.mem_toFinset con, Set.mem_setOf_eq] at p_not_in_S
    contradiction

theorem second_equivalence : (∀ (S : Finset ℕ), (∃ p, Nat.Prime p ∧ p ∉ S)) ↔ (∀ (S : Finset ℕ) (hS : ∀ s ∈ S, Nat.Prime s), (∃ p, Nat.Prime p ∧ p ∉ S)) := by
  apply Iff.intro
  · exact fun a S _ => a S
  · intro h S
    let Sprimes := S.filter Nat.Prime
    obtain ⟨p, p_prime, p_notin_Sprimes⟩ := h Sprimes (λ _ g => (Finset.mem_filter.mp g).right)
    obtain p_notin_S := λ p_in_S => p_notin_Sprimes (Finset.mem_filter.mpr ⟨p_in_S, p_prime⟩)
    exact ⟨p, ⟨p_prime, p_notin_S⟩⟩

theorem third_equivalence : { p : ℕ | Nat.Prime p}.Infinite ↔ ∃ (P : ℕ → ℕ), (Injective P) ∧ (∀ k, (P k).Prime) := by
  apply Iff.intro
  · let primes := { p : ℕ | Nat.Prime p}
    let P := λ k => (Nat.nth (primes.Mem) k)
    intro h
    exact ⟨P, Nat.nth_injective h, λ k => Nat.nth_mem_of_infinite h k⟩
  · intro ⟨P, P_inj, P_im_prime⟩
    exact Set.infinite_of_injective_forall_mem P_inj P_im_prime

end infinitude_primes_equivalence
