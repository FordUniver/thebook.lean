import Mathlib.Combinatorics.SimpleGraph.Clique

-- https://github.com/leanprover-community/mathlib4/pull/20705

namespace SimpleGraph

variable {α : Type*} (G : SimpleGraph α)

theorem induce_isClique {S : Subgraph G} {F : Set α} {A : Set F} (iC : (S.induce F).coe.IsClique A) :
    G.IsClique (Subtype.val '' A) := by
  simp_all [Set.fmap_eq_image, Set.Pairwise]
  intro a ainF ainA b binF binA anb
  exact S.adj_sub (iC a ainF ainA b binF binA anb)

end SimpleGraph
