import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import TheBook.ToMathlib.EdgeFinset

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local notation "E" => G.edgeFinset
local notation "d(" v ")" => G.degree v
local notation "I(" v ")" => G.incidenceFinset v

open Finset

lemma handshaking : ∑ v, d(v) = 2 * #E := by
  calc  ∑ v, d(v)
    _ = ∑ v, #I(v)             := by simp [G.card_incidenceFinset_eq_degree]
    _ = ∑ v, #{e ∈ E | v ∈ e}  := by simp [G.incidenceFinset_eq_filter]
    _ = ∑ e ∈ E, #{v | v ∈ e}  := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ = ∑ e ∈ E, 2             := Finset.sum_congr rfl (λ e he ↦ (G.card_filter_mem_of_mem_edgeFinset e he))
    _ = 2 * ∑ e ∈ E, 1         := (Finset.mul_sum E (λ _ ↦ 1) 2).symm
    _ = 2 * #E                 := by rw [Finset.card_eq_sum_ones E]
