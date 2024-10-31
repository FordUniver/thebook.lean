import Mathlib.Data.Finset.Pairwise
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.MeanInequalities -- has am-gm
import TheBook.ToMathlib.WeightedDoubleCounting
import TheBook.ToMathlib.IndependentSet
import TheBook.ToMathlib.CliqueNumber


namespace AMGMMantelTheorem

variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {a b c : α} {A : Finset α}

-- TODO move to seperate file
local notation "V" => @Finset.univ _ _
local notation "E" => G.edgeFinset
local notation "N(" v ")" => G.neighborFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card α

-- TODO move to ToMathlib
prefix:100 "#" => Finset.card

-- The degree of a vertex i is less or equal α, the size of a maximum independent set.
lemma degreeLeqa (h: G.CliqueFree 3): d(i) ≤ G.cocliqueNum := by
  have : G.IsIndependentSet N(i) :=
    by simp only [Set.coe_toFinset, G.isIndependentSet_neighborSet_if_triangleFree h,
    SimpleGraph.neighborFinset]
  exact G.independentSet_card_le_cocliqueNum N(i) this

-- We count the edges of G by counting the endvertices in B.
lemma count_edges_by_B {A : Finset α} (indA : G.IsIndependentSet A) : #E ≤ ∑ i ∈ V \ A, d(i) := by

   -- The number of edges adjacent to i is the degree of i. -- TODO duh?
   have n_adj_edges_eq_deg : ∀ i, #{e ∈ E | i ∈ e} = d(i) := by
     intro i
     rw [Eq.symm (SimpleGraph.card_incidenceFinset_eq_degree G i)]
     rw [SimpleGraph.incidenceFinset_eq_filter]

   -- every edge is adjacent to at least one vertex in V \ A
   have one_geq_n_adj_verts : ∀ e ∈ G.edgeFinset, 1 ≤ #{ i ∈ (V \ A) | i ∈ e } := by
     simp only [Finset.one_le_card, SimpleGraph.mem_edgeFinset]
     exact G.compl_independentSet_meets_every_edge indA

   calc
     #E = ∑ e ∈ E, 1                                := by simp
      _ ≤ ∑ e ∈ E, #{ i ∈ (V \ A) | i ∈ e }         := Finset.sum_le_sum one_geq_n_adj_verts
      _ = ∑ e ∈ E, ∑ i ∈ {i ∈ (V \ A) | i ∈ e}, 1   := by simp
      _ = ∑ i ∈ V \ A, ∑ e ∈ {e ∈ E | i ∈ e}, 1     := Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _ _ _
      _ = ∑ i ∈ V \ A, #{e ∈ E | i ∈ e}             := by simp
      _ = ∑ i ∈ V \ A, d(i)                         := Finset.sum_congr
                                                         (by rfl) (fun i _ => n_adj_edges_eq_deg i)


-- The inequality of the arithmetic and geometric mean.
lemma am_gm (a b : ℕ) : 4 * a * b ≤ (a + b)^2 := by
  have := two_mul_le_add_sq a b -- mathlib version of the am-gm.
  linarith


-- Mantel's Theorem
theorem mantel (h: G.CliqueFree 3) (A : Finset α) (maxA : G.isMaximumIndependentSet A) :
    #E ≤ (n^2 / 4) := by

  have := calc #E
   _ ≤ ∑ i ∈ V \ A, d(i)      := count_edges_by_B G maxA.left
   _ ≤ ∑ _ ∈ V \ A, #A        := Finset.sum_le_sum (fun _ _ =>
                                  (le_of_le_of_eq (degreeLeqa G h)
                                    (Eq.symm (G.maximumIndependentSet_card_eq_cocliqueNum A maxA))))
   _ = #(V \ A) * #A          := Finset.sum_const _
   _ = (#V - #A) * #A         := by simp [Finset.card_sdiff _]; apply Or.inl; rfl

  have := calc #E * 4 -- TODO how annoying
   _ = 4 * #E                 := mul_comm _ _
   _ ≤ 4 * ((#V - #A) * #A)   := by simp_all only [Nat.ofNat_pos, mul_le_mul_left]; exact this
   _ = 4 * (#V - #A) * #A     := Eq.symm (mul_assoc _ _ _)
   _ ≤ ((#V - #A) + #A)^2     := am_gm (#V - #A) (#A)
   _ = (#V)^2                 := by rw [Nat.sub_add_cancel];
                                    exact (Finset.card_le_card (Finset.subset_univ A))
   _ = n^2                    := by simp only [Finset.card_univ]

  exact ((Nat.le_div_iff_mul_le' (by simp)).mpr this)

end AMGMMantelTheorem
