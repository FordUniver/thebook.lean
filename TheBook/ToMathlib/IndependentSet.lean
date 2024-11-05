import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Pairwise
import TheBook.ToMathlib.CliqueNumber

-- https://github.com/leanprover-community/mathlib4/pull/18608

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
  s.Pairwise (fun v w => ¬G.Adj v w)

theorem isIndependentSet_iff : G.IsIndependentSet s ↔ s.Pairwise (fun v w => ¬G.Adj v w) :=
  Iff.rfl

/-- An independent set is a clique in the complement graph and vice versa. -/
theorem isIndependentSet_iff_isClique_of_complement : G.IsIndependentSet s ↔ Gᶜ.IsClique s := by
  rw [isIndependentSet_iff, isClique_iff]; repeat rw [Set.Pairwise]
  simp_all only [compl_adj, ne_eq, not_false_eq_true, true_and]

---------------------------------------------------------------------------------
/- here come the actualy new thrms -/

-- If `s` is an independent set, its complement meets every edge of `G`.
lemma compl_independentSet_meets_every_edge
    [Fintype α] [DecidableEq α] {s : Finset α} (indA : G.IsIndependentSet s) :
  ∀ e ∈ G.edgeSet, { b ∈ sᶜ | b ∈ e }.Nonempty := by
  rintro ⟨v, w⟩ edgee
  by_contra c
  simp_all [filter_eq_empty_iff, isIndependentSet_iff]
  by_cases vins : v ∈ s
  · have wins : w ∈ s := by by_contra wnins; exact (c wnins).right rfl
    exact (indA vins wins (Adj.ne edgee)) edgee
  · exact (c vins).left rfl

-- The neighbors of a vertex i form an independent set in a trianlge free graph G.
theorem isIndependentSet_neighborSet_if_triangleFree [DecidableEq α] (h: G.CliqueFree 3) (v : α) :
    G.IsIndependentSet (G.neighborSet v) := by
  by_contra nind
  simp [SimpleGraph.IsIndependentSet, Set.Pairwise] at nind
  obtain ⟨j, avj, k, avk, _, ajk⟩ := nind
  exact h {v, j, k} (is3Clique_triple_iff.mpr (by simp [avj, avk, ajk]))


---------------------------------------------------------------------------------

end IndependentSet

section NIndependentSet

variable {n : ℕ} {s : Finset α}

/-- An `n`-IndependentSet in a graph is a set of `n` vertices which are pairwise nonadjacent. -/
structure IsNIndependentSet (n : ℕ) (s : Finset α) : Prop where
  IndependentSet : G.IsIndependentSet s
  card_eq : s.card = n

theorem isNIndependentSet_iff : G.IsNIndependentSet n s ↔ G.IsIndependentSet s ∧ s.card = n :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- An independent n-set is an n-clique in the complement graph and vice versa. -/
theorem isNIndependentSet_iff_isNClique_of_complement :
    G.IsNIndependentSet n s ↔ Gᶜ.IsNClique n s := by
  rw [isNIndependentSet_iff, isIndependentSet_iff_isClique_of_complement]
  simp [isNClique_iff]

end NIndependentSet

section CocliqueNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximal number of vertices of an independent set in a graph `G`. -/
noncomputable def cocliqueNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNIndependentSet n s}

lemma cocliqueNum_eq_compl_cliqueNum : G.cocliqueNum = Gᶜ.cliqueNum := by
  simp [cliqueNum, ← isNIndependentSet_iff_isNClique_of_complement, cocliqueNum]

/-- An independent set in a graph `G` such that there is no independent set with more vertices. -/
structure IsMaximumIndependentSet (G : SimpleGraph α) (s : Finset α) : Prop where
  (independentSet : G.IsIndependentSet s)
  (maximum : ∀ t : Finset α, G.IsIndependentSet t → #t ≤ #s)

theorem isMaximumIndependentSet_iff {s : Finset α} :
    G.IsMaximumIndependentSet s ↔
    G.IsIndependentSet s ∧ ∀ t : Finset α, G.IsIndependentSet t → #t ≤ #s :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

lemma isMaximumIndependentSet_iff_compl_isMaximumClique (s : Finset α)  :
    G.IsMaximumIndependentSet s ↔ Gᶜ.IsMaximumClique s := by
  simp [isMaximumIndependentSet_iff, isIndependentSet_iff_isClique_of_complement,
  isMaximumClique_iff]

/-- An independent set in a graph `G` that cannot be extended by adding more vertices. -/
structure IsMaximalIndependentSet (G : SimpleGraph α) (s : Finset α) : Prop where
  (independentSet : G.IsIndependentSet s)
  (maximal : ∀ t : Finset α, G.IsIndependentSet t → s ⊆ t → t = s)

theorem isMaximalIndependentSet_iff {s : Finset α} :
    G.IsMaximalIndependentSet s ↔
    G.IsIndependentSet s ∧ ∀ t : Finset α, G.IsIndependentSet t → s ⊆ t → t = s :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

lemma isMaximalIndependentSet_iff_compl_isMaximalClique (s : Finset α)  :
    G.IsMaximalIndependentSet s ↔ Gᶜ.IsMaximalClique s := by
  simp [isMaximalIndependentSet_iff, isIndependentSet_iff_isClique_of_complement,
  isMaximalClique_iff]

lemma maximal_of_maximum_independentSet (s : Finset α) (M : G.IsMaximumIndependentSet s) :
    G.IsMaximalIndependentSet s := by
  rw [isMaximalIndependentSet_iff_compl_isMaximalClique]
  rw [isMaximumIndependentSet_iff_compl_isMaximumClique] at M
  exact maximal_of_maximum s M

end CocliqueNumber

/-! ### Finset of independent sets -/


section IndependentSetFinset

variable [fin : Fintype α]

theorem IsIndependentSet.card_le_cocliqueNum {t : Finset α} {tc : G.IsIndependentSet t} :
    #t ≤ G.cocliqueNum := by
  simp [isIndependentSet_iff_isClique_of_complement, cocliqueNum,
  isNIndependentSet_iff_isNClique_of_complement] at *
  exact tc.card_le_cliqueNum

lemma exists_isNIndependentSet_cocliqueNum : ∃ s, G.IsNIndependentSet G.cocliqueNum s := by
  simp [isIndependentSet_iff_isClique_of_complement, cocliqueNum,
  isNIndependentSet_iff_isNClique_of_complement]
  exact exists_isNClique_cliqueNum

theorem maximumIndependentSet_card_eq_cocliqueNum
    (t : Finset α) (tmc : G.IsMaximumIndependentSet t) : #t = G.cocliqueNum := by
  simp [isMaximumIndependentSet_iff, isIndependentSet_iff_isClique_of_complement, cocliqueNum,
  isNIndependentSet_iff_isNClique_of_complement, ← isMaximumClique_iff] at *
  exact Gᶜ.maximumClique_card_eq_cliqueNum t tmc

lemma maximumIndependentSet_exists : ∃ (s : Finset α), G.IsMaximumIndependentSet s := by
  simp [isMaximumIndependentSet_iff_compl_isMaximumClique, maximumClique_exists]

variable [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α}

end IndependentSetFinset

end SimpleGraph
