import Mathlib.Data.Nat.Lattice
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.SetNotation

-- https://github.com/leanprover-community/mathlib4/pull/18608

local prefix:100 "#" => Finset.card

open Finset

namespace SimpleGraph


section CliqueNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximal number of vertices in a graph `G`. -/
noncomputable def cliqueNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNClique n s}

/-- A maximum clique in a graph `G` is a clique with the largest possible size. -/
structure IsMaximumClique (G : SimpleGraph α) (s : Finset α) : Prop where
  (clique : G.IsClique s)
  (maximum : ∀ t : Finset α, G.IsClique t → #t ≤ #s)

theorem isMaximumClique_iff {s : Finset α} :
    G.IsMaximumClique s ↔ G.IsClique s ∧ ∀ t : Finset α, G.IsClique t → #t ≤ #s :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- A maximal clique in a graph `G` is a clique that cannot be extended by adding more vertices. -/
structure IsMaximalClique (G : SimpleGraph α) (s : Finset α) : Prop where
  (clique : G.IsClique s)
  (maximal : ∀ t : Finset α, G.IsClique t → s ⊆ t → t = s)

theorem isMaximalClique_iff {s : Finset α} :
    G.IsMaximalClique s ↔ G.IsClique s ∧ ∀ t : Finset α, G.IsClique t → s ⊆ t → t = s :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma maximal_of_maximum (s : Finset α) (M : G.IsMaximumClique s) : G.IsMaximalClique s :=
  { clique := M.clique,
    maximal := fun t ht hsub => by
      by_contra hc
      push_neg at hc
      have hlt : #s < #t := card_lt_card (HasSubset.Subset.ssubset_of_ne hsub hc.symm)
      have hle : #t ≤ #s := M.maximum t ht
      exact lt_irrefl _ (lt_of_lt_of_le hlt hle)
  }


variable [Fintype α]

private lemma fintype_cliqueNum_bddAbove : BddAbove {n | ∃ s, G.IsNClique n s} := by
  use Fintype.card α
  rintro y ⟨s, syc⟩
  rw [isNClique_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)

lemma IsClique.card_le_cliqueNum {t : Finset α} {tc : G.IsClique t} : #t ≤ G.cliqueNum :=
  le_csSup G.fintype_cliqueNum_bddAbove (Exists.intro t ⟨tc, rfl⟩)

lemma exists_isNClique_cliqueNum : ∃ s, G.IsNClique G.cliqueNum s :=
    Nat.sSup_mem ⟨0, by simp[isNClique_empty.mpr rfl]⟩ G.fintype_cliqueNum_bddAbove

lemma maximumClique_card_eq_cliqueNum (s : Finset α) (sm : G.IsMaximumClique s) :
    #s = G.cliqueNum := by
  obtain ⟨sc, sm⟩ := sm
  obtain ⟨t, tc, tcard⟩ := G.exists_isNClique_cliqueNum
  exact eq_of_le_of_not_lt sc.card_le_cliqueNum (by simp [← tcard, sm t tc])

lemma maximumClique_exists : ∃ (s : Finset α), G.IsMaximumClique s := by
  obtain ⟨s, snc⟩ := G.exists_isNClique_cliqueNum
  exact ⟨s, ⟨snc.clique, fun t ht => snc.card_eq.symm ▸ ht.card_le_cliqueNum⟩⟩

end CliqueNumber

end SimpleGraph
