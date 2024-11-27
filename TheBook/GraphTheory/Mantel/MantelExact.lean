import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import TheBook.ToMathlib.EdgeFinset
import Aesop

namespace CauchyMantelTheorem

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "I(" v ")" => G.incidenceFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card α

open Finset

def completeBipartiteGraph (s t : ℕ) : SimpleGraph (Fin s ⊕ Fin t) :=
{ Adj := fun x y =>
    match x, y with
    | Sum.inl _, Sum.inl _ => false
    | Sum.inr _, Sum.inr _ => false
    | _, _                 => true,
  symm := by aesop_graph
  loopless := fun x h =>
    match x, h with
    | Sum.inl _, h => by simp_all
    | Sum.inr _, h => by simp_all  }

lemma completeBipartiteGraph_triangle_free (k₁ k₂ : ℕ) : (completeBipartiteGraph k₁ k₂).CliqueFree 3 := by
  sorry

lemma completeBipartiteGraph_order (k₁ k₂ : ℕ) : #(completeBipartiteGraph k₁ k₂).edgeFinset = k1 * k2 := by
  sorry

theorem mantel_maximal_iff : G.CliqueFree 3 ∧ #E = n^2 / 4 ↔ Nonempty (G ≃g completeBipartiteGraph (n / 2) ((n + 1) / 2)) := by
  constructor
  · intro ⟨h, hE⟩
    -- if we have equality then in the above chain of inequalities we have
    --
    -- in the AM-GM proof we have an independent set A size α
    -- a set B of size n - α that is also an independent set
    -- since if we have equality then 4 * #E = n^2 and therefore
    -- #E = ∑ i ∈ B, d(i) and therefore 1 = #{ i ∈ B | i ∈ e } for all e ∈ E
    -- in order to get to n^2 / 4 edges we ned to have all edges between A and B
    -- and 4 * #A * #B = (#A + #B)^2 so that one one way or the other the cardinalities match
    sorry

  · intro ⟨φ, hφ⟩

    have hCliqueFree : G.CliqueFree 3 := by
      by_contra hc
      rw [SimpleGraph.CliqueFree] at hc
      push_neg at hc
      obtain ⟨t, ⟨tclique, tcard⟩⟩ := hc
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp tcard
      let a' := φ a
      let b' := φ b
      let c' := φ c
      -- by pigeonhole, two of a', b', c' must be in the same partite set
      -- but their sources are adjacent in G
      -- giving a contradiction in the complete bipartite graph
      sorry

    have hE : #E = n^2 / 4 := by
      -- the complete bipartite graph has order n/2 * (n + 1)/2 which evaluates to n^2/4
      -- so G has order n^2/4 by the automorphism φ
      sorry

    exact ⟨hCliqueFree, hE⟩
    

end CauchyMantelTheorem
