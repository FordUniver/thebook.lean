import Mathlib.Data.Nat.Lattice
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.SetNotation
import TheBook.ToMathlib.IndependentSet
-- import TheBook.ToMathlib.FinsetCard

local prefix:100 "#" => Finset.card

namespace SimpleGraph

section Clique


variable {α : Type*} {G : SimpleGraph α}

noncomputable def cliqueNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNClique n s}
noncomputable def cocliqueNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNIndependentSet n s}

noncomputable def isMaximumIndependentSet (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsIndependentSet s ∧ ∀ (t : Finset α), G.IsIndependentSet t → #t ≤ #s

noncomputable def isMaximalIndependentSet (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsIndependentSet s ∧ ∀ (t : Finset α), G.IsIndependentSet t → ¬ s ⊂ t

noncomputable def isMaximumClique (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsClique s ∧ ∀ (t : Finset α), G.IsClique t → #t ≤ #s

noncomputable def isMaximalClique (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsClique s ∧ ∀ (t : Finset α), G.IsClique t → ¬ s ⊂ t

lemma cliquenum_ge_clique_card {G : SimpleGraph α} : G.cliqueNum ≥ #G.cliqueNum := by sorry

lemma isMaximumIndependentSet_iff {G : SimpleGraph α} {s : Finset α} (h : G.isMaximumIndependentSet s) :
    #s = G.cocliqueNum := by
    have : #s ∈ {n | ∃ s, G.IsNIndependentSet n s} := by sorry
    have : G.cocliqueNum ≥ #s := by sorry
    sorry

lemma isMaximumClique_iff {G : SimpleGraph α} {s : Finset α} (h : G.isMaximumClique s) :
    #s = G.cliqueNum := sorry

lemma MaximumIndependentSetCard_ge_MaximalIndependentSetCard {G : SimpleGraph α}
    {s t : Finset α} (h : G.isMaximumIndependentSet s) (ht : G.isMaximalIndependentSet t) :
  #s ≤ #t := sorry

end Clique

end SimpleGraph
