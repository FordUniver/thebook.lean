import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Antichain
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Slice

namespace Slice

open Finset

variable {α : Type*} {𝒜 : Finset (Finset α)} {A A₁ A₂ : Finset α} {r r₁ r₂ : ℕ}

/- Equivalence for a slice to be a singleton. -/
lemma singleton_explicit : (𝒜 # s) = {layer_s} ↔ layer_s ∈ 𝒜 ∧ #layer_s = s ∧ #(𝒜 # s) = 1  := by
  constructor
  · intro h
    have := Finset.mem_singleton_self layer_s
    rw [←h] at this
    simp [slice] at this
    exact ⟨this.left, this.right, by simp [h]⟩
  · intro h
    refine' eq_singleton_iff_unique_mem.mpr _
    constructor
    · simp [slice]
      constructor
      · exact h.left
      · exact h.right.left
    · intro x hx
      sorry
