import Mathlib.Combinatorics.SimpleGraph.Subgraph

-- https://github.com/leanprover-community/mathlib4/pull/22080

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (G' : G.Subgraph)

instance instDecidableRel_induce_adj (s : Set V) [∀ a, Decidable (a ∈ s)] [DecidableRel G'.Adj] :
    DecidableRel (G'.induce s).Adj :=
  fun _ _ ↦ instDecidableAnd

end SimpleGraph
