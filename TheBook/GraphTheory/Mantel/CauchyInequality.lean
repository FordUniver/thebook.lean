import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Aesop

namespace CauchyMantelTheorem

-- Assume V is a finite type
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
instance : Fintype G.edgeSet := G.fintypeEdgeSet

#check Finset.sum_mul_sq_le_sq_mul_sq --probably the Cauchy-Schwarz inequality we want

-- This is equivalent to SimpleGraph.sum_degrees_eq_twice_card_edges G in mathlib
lemma handshake : ∑ v : V, G.degree v = 2 * G.edgeFinset.card := by 
  -- double counting
  sorry

lemma mantel (h: G.CliqueFree 3) : G.edgeFinset.card ≤ (Fintype.card V)^2 / 4 := by
  let n := Fintype.card V
  let m := G.edgeFinset.card
  have (i j : V) (h: G.Adj i j) : G.degree i + G.degree j ≤ n := by sorry
  let sum_degrees_of_edge (e : Sym2 V) : ℕ := Sym2.lift ⟨λ x y => G.degree x + G.degree y, λ x y => by simp [Nat.add_comm]⟩ e
  have : ∑ (e : Sym2 V), sum_degrees_of_edge e ≤ n * m := by sorry
  have : ∑ (e : Sym2 V), sum_degrees_of_edge e = ∑ (v : V), (G.degree v)^2 := by sorry
  have : m*n ≥ ∑ (v : V), (G.degree v)^2 := by sorry
  have : ∑ (v : V), (G.degree v)^2 ≥ (∑ (v : V), G.degree v)^2 / n := by sorry
  have : (∑ (v : V), G.degree v)^2 / n = 4 * m^2 / n := by sorry -- SimpleGraph.sum_degrees_eq_twice_card_edges
  sorry

lemma mantel_equality (h: G.CliqueFree 3) : 0 = 0 := by
  sorry

end CauchyMantelTheorem
