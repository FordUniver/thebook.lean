import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Pairwise

-- https://github.com/leanprover-community/mathlib4/pull/18218

open Finset Fintype

namespace SimpleGraph

/-! ### Independent Sets -/

section IndependentSet

variable {α : Type*} {G : SimpleGraph α}

/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
abbrev IsIndependentSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)

-- The neighbors of a vertex i form an independent set in a trianlge free graph G.
theorem isIndependentSet_neighborSet_if_triangleFree [DecidableEq α] (h: G.CliqueFree 3) :
    G.IsIndependentSet (G.neighborSet i) := by
  by_contra nind
  simp [SimpleGraph.IsIndependentSet, Set.Pairwise] at nind
  obtain ⟨j, aij, k, aik, _, ajk⟩ := nind
  exact h {i, j, k} (is3Clique_triple_iff.mpr (by simp only [aij, aik, ajk, and_self]))

end IndependentSet

end SimpleGraph
