import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Aesop

namespace CauchyMantelTheorem

-- Assume V is a finite type
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
instance : Fintype G.edgeSet := G.fintypeEdgeSet

lemma degree_eq_number_of_incident_edges (v : V) : G.degree v = Finset.card (Finset.filter (λ e => v ∈ e) G.edgeFinset) := by sorry

lemma edges_have_two_incident_vertices (e : Sym2 V) {h: e ∈ G.edgeFinset} : Finset.card (Finset.filter (λ v => v ∈ e) (@Finset.univ V _)) = 2 := by
  calc Finset.card (Finset.filter (λ v => v ∈ e) (@Finset.univ V _))
    _ = 2 := by sorry

-- This is equivalent to SimpleGraph.sum_degrees_eq_twice_card_edges G in mathlib
lemma handshake : ∑ v : V, G.degree v = 2 * G.edgeFinset.card := by 
  let E := G.edgeFinset
  let V' := @Finset.univ V _

  calc ∑ v : V, G.degree v
  --  _ = ∑ v ∈ V', Finset.card {e ∈ E | v ∈ e} := by sorry --simp [degree_eq_number_of_incident_edges]
   _ = ∑ v ∈ V', Finset.card (Finset.filter (λ e => v ∈ e) E) := by simp [degree_eq_number_of_incident_edges]
   _ = ∑ e ∈ E, Finset.card (Finset.filter (λ v => v ∈ e) V') := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (λ v e => v ∈ e)
  --  _ = ∑ e ∈ E, Finset.card {v ∈ V' | v ∈ e} := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (λ v e => v ∈ e)
   _ = ∑ e ∈ E, 2 := by sorry -- edges_have_two_incident_vertices
   _ = 2 * E.card := by simp [V', edges_have_two_incident_vertices, Nat.mul_comm]


#check Finset.sum_mul_sq_le_sq_mul_sq -- probably the Cauchy-Schwarz inequality we want

theorem mantel (h: G.CliqueFree 3) : G.edgeFinset.card ≤ (Fintype.card V)^2 / 4 := by
  let n := Fintype.card V
  let E := G.edgeFinset
  let V' := @Finset.univ V _

  have (i j : V) (h: G.Adj i j) : G.degree i + G.degree j ≤ n := by sorry
  let sum_degrees_of_edge (e : Sym2 V) : ℕ := Sym2.lift ⟨λ x y => G.degree x + G.degree y, λ x y => by simp [Nat.add_comm]⟩ e
  have : ∑ (e ∈ E), sum_degrees_of_edge e ≤ n * E.card := by sorry
  have : ∑ (e ∈ E), sum_degrees_of_edge e = ∑ (v : V), (G.degree v)^2 := by sorry
  have : E.card*n ≥ ∑ (v : V), (G.degree v)^2 := by sorry
  have : ∑ (v : V), (G.degree v)^2 ≥ (∑ (v : V), G.degree v)^2 / n := by sorry
  have : (∑ (v : V), G.degree v)^2 / n = (2 * E.card)^2 / n := by rw [handshake]
  have : (2 * E.card)^2 = 4 * E.card^2 := by linarith
  have : (2 * E.card)^2 / n = 4 * E.card^2 / n := by aesop
  
  sorry

-- Probably needs to use floor and ceil to be precise ...
theorem mantel_equality (h: G.CliqueFree 3) : 0 = 0 := by
  sorry

end CauchyMantelTheorem
