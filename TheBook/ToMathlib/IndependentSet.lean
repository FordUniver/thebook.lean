import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Pairwise

-- TODO PR link

/-!
# Independent Sets in Graphs

This file defines independent sets (aka cocliques) in simple graphs.
An independent set is a set of vertices that are pairwise nonadjacent.

-/

open Finset Fintype Function

namespace SimpleGraph

variable {α β : Type*} (G H : SimpleGraph α)


/-! ### Independent Sets -/

section IndependentSet

variable {s t : Set α}

/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
abbrev IsIndependentSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)

theorem isIndependentSet_iff : G.IsIndependentSet s ↔ s.Pairwise (fun v w ↦ ¬G.Adj v w) :=
  Iff.rfl

/-- An independent set is a clique in the complement graph and vice versa. -/
theorem isIndependentSet_iff_isClique_of_complement : G.IsIndependentSet s ↔ Gᶜ.IsClique s := by
  rw [isIndependentSet_iff, isClique_iff]; repeat rw [Set.Pairwise]
  simp_all only [compl_adj, ne_eq, not_false_eq_true, true_and]

---------------------------------------------------------------------------------
/- here come the actualy new thrms -/

-- The neighbors of a vertex i form an independent set in a trianlge free graph G.
theorem isIndependentSet_neighborSet_if_triangleFree [DecidableEq α] (h: G.CliqueFree 3) :
    G.IsIndependentSet (G.neighborSet i) := by
  by_contra nind
  simp [SimpleGraph.IsIndependentSet, Set.Pairwise] at nind
  obtain ⟨j, aij, k, aik, _, ajk⟩ := nind
  exact h {i, j, k} (is3Clique_triple_iff.mpr (by simp only [aij, aik, ajk, and_self]))

-- If `s` is an independent set, its complement meets every edge of `G`.
lemma compl_independentSet_meets_every_edge
    [Fintype α] [DecidableEq α] {s : Finset α} (indA : G.IsIndependentSet s) :
    ∀ e ∈ G.edgeSet, { b ∈ sᶜ | b ∈ e }.Nonempty := by
    rintro ⟨v, w⟩ edgee
    by_contra c
    simp_all [Finset.filter_eq_empty_iff, SimpleGraph.isIndependentSet_iff, Set.Pairwise]
    by_cases vins : v ∈ s
    . have wins : w ∈ s := by by_contra wnins; exact (c wnins).right rfl
      exact (indA vins wins (SimpleGraph.Adj.ne edgee)) edgee
    . exact (c vins).left rfl

---------------------------------------------------------------------------------

end IndependentSet

section NIndependentSet

variable {n : ℕ} {s : Finset α}

/-- An `n`-IndependentSet in a graph is a set of `n` vertices which are pairwise nonadjacent. -/
structure IsNIndependentSet (n : ℕ) (s : Finset α) : Prop where
  IndependentSet : G.IsIndependentSet s
  card_eq : s.card = n

theorem isNIndependentSet_iff : G.IsNIndependentSet n s ↔ G.IsIndependentSet s ∧ s.card = n :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- An independent n-set is an n-clique in the complement graph and vice versa. -/
theorem isNIndependentSet_iff_isNClique_of_complement :
    G.IsNIndependentSet n s ↔ Gᶜ.IsNClique n s := by
  rw [isNIndependentSet_iff, isIndependentSet_iff_isClique_of_complement]
  simp [isNClique_iff]

end NIndependentSet

end SimpleGraph
