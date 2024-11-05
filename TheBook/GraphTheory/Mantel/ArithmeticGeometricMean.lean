import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Pairwise
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.MeanInequalities -- has am-gm
import TheBook.ToMathlib.IndependentSet
import TheBook.ToMathlib.CliqueNumber


namespace AMGMMantelTheorem

variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

local notation "V" => @Finset.univ _ _
local notation "E" => G.edgeFinset
local notation "N(" v ")" => G.neighborFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card α

-- The degree of a vertex i is less or equal α, the size of a maximum independent set.
lemma degreeLeqa (h: G.CliqueFree 3): d(i) ≤ G.cocliqueNum := by
  have : G.IsIndependentSet N(i) :=
    by simp [Set.coe_toFinset, G.isIndependentSet_neighborSet_if_triangleFree h,
    SimpleGraph.neighborFinset, SimpleGraph]
  exact this.card_le_cocliqueNum

-- We count the edges of G by counting the endvertices in B.
lemma count_edges_by_B {A : Finset α} (indA : G.IsIndependentSet A) : Finset.card E ≤ ∑ i ∈ V \ A, d(i) := by

   -- The number of edges adjacent to i is the degree of i. -- TODO duh?
   have n_adj_edges_eq_deg : ∀ i, Finset.card {e ∈ E | i ∈ e} = d(i) := by
     intro i
     rw [Eq.symm (SimpleGraph.card_incidenceFinset_eq_degree G i)]
     rw [SimpleGraph.incidenceFinset_eq_filter]

   -- every edge is adjacent to at least one vertex in V \ A
   have one_geq_n_adj_verts : ∀ e ∈ G.edgeFinset, 1 ≤ Finset.card { i ∈ (V \ A) | i ∈ e } := by
     simp only [Finset.one_le_card, SimpleGraph.mem_edgeFinset]
     exact G.compl_independentSet_meets_every_edge indA

   calc
     Finset.card E = ∑ e ∈ E, 1                                := by simp
      _ ≤ ∑ e ∈ E, Finset.card { i ∈ (V \ A) | i ∈ e }         := Finset.sum_le_sum one_geq_n_adj_verts
      _ = ∑ e ∈ E, ∑ i ∈ {i ∈ (V \ A) | i ∈ e}, 1   := by simp
      _ = ∑ i ∈ V \ A, ∑ e ∈ {e ∈ E | i ∈ e}, 1     := Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _ _ _
      _ = ∑ i ∈ V \ A, Finset.card {e ∈ E | i ∈ e}             := by simp
      _ = ∑ i ∈ V \ A, d(i)                         := Finset.sum_congr
                                                         (by rfl) (fun i _ => n_adj_edges_eq_deg i)


-- The inequality of the arithmetic and geometric mean.
lemma am_gm (a b : ℕ) : 4 * a * b ≤ (a + b)^2 := by
  have := two_mul_le_add_sq a b -- mathlib version of the am-gm.
  linarith

-- Mantel's Theorem
theorem mantel (h: G.CliqueFree 3) (maxA : G.IsMaximumIndependentSet A) : Finset.card E ≤ (n^2 / 4) := by

  have := calc Finset.card E
   _ ≤ ∑ i ∈ V \ A, d(i)      := count_edges_by_B G maxA.independentSet
   _ ≤ ∑ _ ∈ V \ A, Finset.card A        := Finset.sum_le_sum (fun _ _ =>
                                  (le_of_le_of_eq (degreeLeqa G h)
                                    (Eq.symm (G.maximumIndependentSet_card_eq_cocliqueNum A maxA))))
   _ = Finset.card (V \ A) * Finset.card A          := Finset.sum_const _
   _ = (Finset.card V - Finset.card A) * Finset.card A         := by simp [Finset.card_sdiff _]; apply Or.inl; rfl

  have := calc Finset.card E * 4 -- TODO how annoying
   _ = 4 * Finset.card E                 := mul_comm _ _
   _ ≤ 4 * ((Finset.card V - Finset.card A) * Finset.card A)   := by simp_all; exact this
   _ = 4 * (Finset.card V - Finset.card A) * Finset.card A     := Eq.symm (mul_assoc _ _ _)
   _ ≤ ((Finset.card V - Finset.card A) + Finset.card A)^2     := am_gm (Finset.card V - Finset.card A) (Finset.card A)
   _ = (Finset.card V)^2                 := by rw [Nat.sub_add_cancel];
                                    exact (Finset.card_le_card (Finset.subset_univ A))
   _ = n^2                    := by simp only [Finset.card_univ]

  exact ((Nat.le_div_iff_mul_le' (by simp)).mpr this)

end AMGMMantelTheorem
