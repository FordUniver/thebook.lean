import Mathlib.Data.Nat.Lattice
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.SetNotation
import TheBook.ToMathlib.IndependentSet



local prefix:100 "#" => Finset.card

namespace SimpleGraph

section CliqueNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximal number of vertices in a graph `G`. -/
noncomputable def cliqueNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNClique n s}

/-- A clique in a graph `G` such that there is no clique with more vertices. -/
def isMaximumClique (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsClique s ∧ ∀ (t : Finset α), G.IsClique t → #t ≤ #s

/-- A clique in a graph `G` that cannot be extended by adding vertices. -/
def isMaximalClique (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsClique s ∧ ¬ ∃ (t : Finset α), G.IsClique t ∧ s ⊂ t

lemma maximalClique_if_maximumClique {s : Finset α} (smax : G.isMaximumClique s) :
    G.isMaximalClique s := by
  rw [isMaximalClique, isMaximumClique] at *
  by_contra h
  simp_all only [not_exists, not_and, not_forall, Classical.not_imp, not_not, true_implies]
  let ⟨t, tc, tsub⟩ := h
  let ⟨_ , smaxf⟩ := smax
  sorry --exact (not_and_self_iff (#t ≤ #s)).mp ⟨not_le_of_lt (Set.card_lt_card tsub), smaxf t tc⟩

variable [fin : Fintype α]

lemma fintype_cliqueNum_bddAbove : BddAbove {n | ∃ s, G.IsNClique n s} := by
  rw [bddAbove_def]
  refine Exists.intro (Fintype.card α) ?_
  rintro y ⟨sy, syc⟩
  rw [isNClique_iff, ← And.right syc] at *
  exact Finset.card_le_card (Finset.subset_univ sy)

theorem clique_card_le_cliqueNum (t : Finset α) (tc : G.IsClique t) : #t ≤ G.cliqueNum :=
  le_csSup fintype_cliqueNum_bddAbove (Exists.intro t ⟨tc, rfl⟩)

theorem maximumClique_card_eq_cliqueNum (t : Finset α) (tmc : G.isMaximumClique t) :
    #t = G.cliqueNum := by
  let ⟨tclique, tmax⟩ := tmc
  refine eq_of_le_of_not_lt (clique_card_le_cliqueNum _ tclique) ?_
  have ⟨s, sclique, scn⟩ : G.cliqueNum ∈ {n | ∃ s, G.IsNClique n s} :=
    Nat.sSup_mem ⟨ 0, by simp[isNClique_empty.mpr rfl] ⟩ fintype_cliqueNum_bddAbove
  rw [cliqueNum, ← scn]
  exact LE.le.not_lt (tmax s sclique)

end CliqueNumber

section CocliqueNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximal number of vertices of an independent set in a graph `G`. -/
noncomputable def cocliqueNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNIndependentSet n s}

lemma cocliqueNum_eq_compl_cliqueNum : G.cocliqueNum = Gᶜ.cliqueNum := by
  simp [cliqueNum, ← isNIndependentSet_iff_isNClique_of_complement, cocliqueNum]

/-- An independent set in a graph `G` such that there is no independent set with more vertices. -/
def isMaximumIndependentSet (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsIndependentSet s ∧ ∀ (t : Finset α), G.IsIndependentSet t → #t ≤ #s

lemma isMaximumIndependentSet_iff_compl_isMaximumClique (s : Finset α)  :
    G.isMaximumIndependentSet s ↔ Gᶜ.isMaximumClique s := by
  simp [isMaximumIndependentSet, isIndependentSet_iff_isClique_of_complement] at *
  exact Iff.symm (Eq.to_iff rfl)

/-- An independent set in a graph `G` that cannot be extended by adding vertices. -/
def isMaximalIndependentSet (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsIndependentSet s ∧ ¬ ∃ (t : Finset α), G.IsIndependentSet t ∧ s ⊂ t

lemma isMaximalIndependentSet_iff_compl_isMaximalClique (s : Finset α)  :
    G.isMaximalIndependentSet s ↔ Gᶜ.isMaximalClique s := by
  simp [isMaximalIndependentSet, isIndependentSet_iff_isClique_of_complement, ← not_and,
  ← not_exists] at *
  exact Iff.symm (Eq.to_iff rfl)

lemma maximalIndependentSet_if_maximumIndependentSet
    {s : Finset α} (smax : G.isMaximumIndependentSet s) : G.isMaximalIndependentSet s := by
  simp [isMaximalIndependentSet, isMaximumIndependentSet,
  isIndependentSet_iff_isClique_of_complement, ← not_and, ← not_exists] at *
  exact maximalClique_if_maximumClique smax

variable [fin : Fintype α]

lemma fintype_cocliqueNum_bddAbove : BddAbove {n | ∃ s, G.IsNIndependentSet n s} := by
  simp [isNIndependentSet_iff_isNClique_of_complement, fintype_cliqueNum_bddAbove,
  cocliqueNum_eq_compl_cliqueNum]

theorem independentSet_card_le_cocliqueNum (t : Finset α) (tc : G.IsIndependentSet t) :
    #t ≤ G.cocliqueNum := by
  simp [isIndependentSet_iff_isClique_of_complement, cocliqueNum,
  isNIndependentSet_iff_isNClique_of_complement] at *
  exact clique_card_le_cliqueNum t tc

theorem maximumIndependentSet_card_eq_cocliqueNum
    (t : Finset α) (tmc : G.isMaximumIndependentSet t) : #t = G.cocliqueNum := by
  simp [isMaximumIndependentSet, isIndependentSet_iff_isClique_of_complement, cocliqueNum,
  isNIndependentSet_iff_isNClique_of_complement] at *
  exact maximumClique_card_eq_cliqueNum t tmc

end CocliqueNumber

end SimpleGraph
