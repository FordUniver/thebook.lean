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
local notation "I(" v ")" => G.incidenceFinset v
local notation "d(" v ")" => G.degree v
local notation "α(" G ")" => SimpleGraph.cocliqueNum G
local notation "n" => Fintype.card α

open Finset

-- The degree of a vertex i is less or equal α, the size of a maximum independent set.
lemma nbhd_ind_of_triangle_free (h: G.CliqueFree 3): G.IsIndependentSet N(i) := by
  simp [Set.coe_toFinset, G.isIndependentSet_neighborSet_if_triangleFree h,
  SimpleGraph.neighborFinset, SimpleGraph]

-- We count the edges of G by counting the endvertices in B.
lemma count_edges_by_B {A : Finset α} (indA : G.IsIndependentSet A) : #E ≤ ∑ i ∈ V \ A, d(i) := by

  -- The number of edges adjacent to i is the degree of i. -- TODO duh?
  have n_adj_edges_eq_deg (i : α) : #{e ∈ E | i ∈ e} = d(i) := by
    rw [(G.card_incidenceFinset_eq_degree i).symm, G.incidenceFinset_eq_filter]

  -- every edge is adjacent to at least one vertex in V \ A
  have one_geq_n_adj_verts : ∀ e ∈ G.edgeFinset, 1 ≤ #{ i ∈ (V \ A) | i ∈ e } := by
    simp only [Finset.one_le_card, SimpleGraph.mem_edgeFinset]
    exact G.compl_independentSet_meets_every_edge indA

  calc
    #E = ∑ e ∈ E, 1                                := by simp
     _ ≤ ∑ e ∈ E, #{ i ∈ (V \ A) | i ∈ e }         := Finset.sum_le_sum one_geq_n_adj_verts
     _ = ∑ e ∈ E, ∑ i ∈ {i ∈ (V \ A) | i ∈ e}, 1   := by simp
     _ = ∑ i ∈ V \ A, ∑ e ∈ {e ∈ E | i ∈ e}, 1     := Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _
     _ = ∑ i ∈ V \ A, #{e ∈ E | i ∈ e}             := by simp
     _ = ∑ i ∈ V \ A, d(i)                         := Finset.sum_congr (by rfl) (fun i _ => n_adj_edges_eq_deg i)

-- The inequality of the arithmetic and geometric mean.
lemma am_gm (a b : ℕ) : 4 * a * b ≤ (a + b)^2 := by
  have := two_mul_le_add_sq a b -- mathlib version of the am-gm.
  linarith

-- Mantel's Theorem
theorem mantel (h: G.CliqueFree 3) (maxA : G.IsMaximumIndependentSet A) : #E ≤ (n^2 / 4) := by

  have := calc #E
   _ ≤ ∑ i ∈ V \ A, d(i)      := count_edges_by_B G maxA.independentSet
   _ ≤ ∑ _ ∈ V \ A, #A        := Finset.sum_le_sum (fun _ _ =>
                                  (le_of_le_of_eq ((nbhd_ind_of_triangle_free G h).card_le_cocliqueNum)
                                    (G.maximumIndependentSet_card_eq_cocliqueNum A maxA).symm))
   _ = #(V \ A) * #A          := Finset.sum_const _
   _ = (#V - #A) * #A         := by simp [Finset.card_sdiff _]; apply Or.inl; rfl

  have := calc #E * 4 -- TODO how annoying
   _ = 4 * #E                 := mul_comm _ _
   _ ≤ 4 * ((#V - #A) * #A)   := by simp_all; exact this
   _ = 4 * (#V - #A) * #A     := (mul_assoc _ _ _).symm
   _ ≤ ((#V - #A) + #A)^2     := am_gm (#V - #A) (#A)
   _ = (#V)^2                 := by rw [Nat.sub_add_cancel];
                                    exact (Finset.card_le_card (Finset.subset_univ A))
   _ = n^2                    := by simp only [Finset.card_univ]

  exact ((Nat.le_div_iff_mul_le' (by simp)).mpr this)

end AMGMMantelTheorem
