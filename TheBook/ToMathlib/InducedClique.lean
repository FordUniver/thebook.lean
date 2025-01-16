import Mathlib.Combinatorics.SimpleGraph.Clique

-- https://github.com/leanprover-community/mathlib4/pull/20705

namespace SimpleGraph

variable {α : Type*} (G : SimpleGraph α)

theorem induce_isClique {S : Subgraph G} {F : Set α} {A : Set F} (c : (S.induce F).coe.IsClique A) :
    G.IsClique (Subtype.val '' A) := by
  simp_all [Set.Pairwise]
  intro _ _ ainA _ _ binA anb
  exact S.adj_sub (c _ _ ainA _ _ binA anb)

theorem induce_isNClique {S : Subgraph G} {F : Set α} {s : Finset { x // x ∈ F }} {n : ℕ}
    (cc : (S.induce F).coe.IsNClique n ↑s) :
  G.IsNClique n (Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s) := by
simp_all [isNClique_iff]
exact induce_isClique G cc.left

theorem induce_isIndepSet_iff {F : Set α} {A : Set F} :
      (((⊤ : G.Subgraph).induce F).coe.IsIndepSet A) ↔
    G.IsIndepSet (Subtype.val '' A) := by
  simp_all [Set.Pairwise]

theorem induce_isNIndepSet {F : Set α} {s : Finset { x // x ∈ F }} {n : ℕ} :
    ( ((⊤ : G.Subgraph).induce F).coe.IsNIndepSet n ↑s) ↔
    G.IsNIndepSet n (Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s) := by
  simp [isNIndepSet_iff]
  intro
  exact induce_isIndepSet_iff G

end SimpleGraph
