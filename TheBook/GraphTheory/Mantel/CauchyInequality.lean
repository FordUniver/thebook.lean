import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Aesop


prefix:100 "#" => Finset.card
set_option linter.unusedSectionVars false

namespace CauchyMantelTheorem

variable {V' : Type*} [Fintype V'] [DecidableEq V']
variable (G : SimpleGraph V') [DecidableRel G.Adj]

local notation "V" => @Finset.univ V' _
abbrev E' := Sym2 V'
local notation "E" => G.edgeFinset
local notation "N(" v ")" => G.neighborFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card V'

lemma degree_eq_number_of_incident_edges (v : V') : d(v) = #(G.incidenceFinset v) := by
  -- need to show a one-to-one correspondence between the set of edges incident to v and the set of vertices v
  -- should be able to use incidenceSetEquivNeighborSet for this
  sorry

lemma edges_have_two_incident_vertices (e : E') {he: e ∈ E} : #{v : V' | v ∈ e}.toFinset = 2 := by
  -- The issue is that edges are Sym2 V' and there does not seem any
  -- way of obtaining a set of two distinct elements from that

  have : #{v : V' | v ∈ e} ≤ 2 := by
    sorry

  -- Finset.card_ne_zero_of_mem
  have : #{v : V' | v ∈ e} ≠ 0 := by
    obtain ⟨v₁, v₂⟩ := e
    have : v₁ ∈ e := by sorry
    sorry

  have : #{v : V' | v ∈ e} ≥ 2 := by
    obtain ⟨v₁, v₂⟩ := e
    have : v₁ ≠ v₂ := SimpleGraph.not_isDiag_of_mem_edgeFinset he
    have : v₁ ∈ {v : V' | v ∈ e} := by sorry
    have : v₂ ∈ {v : V' | v ∈ e} := by sorry
    sorry

  sorry

-- This is equivalent to SimpleGraph.sum_degrees_eq_twice_card_edges G in mathlib
lemma handshake : ∑ v : V', d(v) = 2 * #E := 
  calc ∑ v : V', d(v)
   _ = ∑ v : V', #(G.incidenceFinset v)  := by sorry --simp [degree_eq_number_of_incident_edges]
   _ = ∑ v ∈ V, #{e ∈ E | v ∈ e}         := by sorry
   _ = ∑ e ∈ E, #{v ∈ V | v ∈ e}         := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
   _ = ∑ e ∈ E, #{v : V' | v ∈ e}        := by sorry
   _ = ∑ e ∈ E, 2                        := by sorry --rw [edges_have_two_incident_vertices]
   _ = 2 * #E                            := by simp [Nat.mul_comm]

lemma simplified_cauchy_schwarz (f : V' → ℝ) : #V * (∑ v ∈ V, f v ^ 2) ≥ (∑ v ∈ V, f v) ^ 2 := by
  let const_one (_ : V') : ℕ := 1
  calc (∑ v ∈ V, f v) ^ 2
    _ = (∑ v ∈ V, (const_one v) * f v)^2 := by simp [const_one]
    _ ≤ (∑ v ∈ V, (const_one v)^2) * (∑ v ∈ V, f v^2) := by simp [Finset.sum_mul_sq_le_sq_mul_sq]
    _ = #V * (∑ v ∈ V, f v^2) := by simp [const_one]
  -- actually this is sq_sum_le_card_mul_sum_sq

theorem mantel (h: G.CliqueFree 3) : #G.edgeFinset ≤ n^2 / 4 := by

  -- The degrees of two adjacent vertices cannot sum to more than n
  have (i j : V') (hij: G.Adj i j) : d(i) + d(j) ≤ n := by
    -- Otherwise there would exist a vertex k adjacent to both i and j by pigeonhole principle
    by_contra hc
    simp at hc


    -- these two blocks should be combined into one
    have : #(N(i) ∩ N(j)) + n ≥ #N(i) + #N(j) := by
      have : #(N(i) ∩ N(j)) + #(N(i) ∪ N(j)) = #N(i) + #N(j) := Finset.card_inter_add_card_union _ _
      have : #(N(i) ∪ N(j)) ≤ n := Finset.card_le_univ _
      linarith

    have : #(N(i) ∩ N(j)) > 0 := (Nat.lt_add_left_iff_pos.mp (Nat.lt_of_lt_of_le hc this))

    have : ∃ k : V', G.Adj i k ∧ G.Adj j k := by
      obtain ⟨k, h⟩ := Finset.card_pos.mp this
      simp [Set.mem_inter_iff] at h
      exact Exists.intro k h

    -- But then i, j, k would form a triangle, contradicting the assumption that G has no 3-cliques
    obtain ⟨k, hik, hjk⟩ := this
    exact h {i, j, k} (sorry)

  let sum_degrees_of_edge (e : E') : ℕ := Sym2.lift ⟨λ x y => d(x) + d(y), λ x y => by simp [Nat.add_comm]⟩ e

  -- We slightly modify the argument to avoid division (in particular by zero)
  have := calc n^2 * #E
    _ ≥ n^2 * ∑ (e ∈ E), sum_degrees_of_edge e  := by sorry
    _ = n * ∑ (v ∈ V), d(v)^2                   := by sorry
    _ ≥ (∑ (v ∈ V),  d(v))^2                    := by sorry -- sq_sum_le_card_mul_sum_sq
    _ = (2 * #E)^2                              := by rw [handshake]
    _ = 4 * #E^2                                := by linarith

  -- technically not quite correct because we are in Nat and division rounds down
  -- perhapos correcting it to the floor ceiling notation fixes it?
  -- or perhaps the floor ceiling aligns with the division already?
  have : #E ≤ n^2 / 4 := by sorry

  exact this

#check sq_sum_le_card_mul_sum_sq


-- Probably needs to use floor and ceil to be precise ...
theorem mantel_equality (h: G.CliqueFree 3) : 0 = 0 := by
  sorry


end CauchyMantelTheorem
