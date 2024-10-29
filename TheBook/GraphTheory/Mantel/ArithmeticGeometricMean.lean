import Mathlib.Data.Finset.Pairwise
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.MeanInequalities -- has am-gm
import TheBook.ToMathlib.WeightedDoubleCounting
import TheBook.ToMathlib.IndependentSet


namespace AMGMMantelTheorem

variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {a b c : α} {s : Finset α}

-- TODO move to seperate file
local notation "V" => @Finset.univ _ _
local notation "E" => G.edgeFinset
local notation "N(" v ")" => G.neighborFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card α

-- TODO move to ToMathlib
prefix:100 "#" => Finset.card

-- TODO can i say A is a maximal independent set in a less verbose way plz
-- The degree of a vertex i is less or equal α, the size of a largest independent set.
lemma degreeLeqa (h: G.CliqueFree 3) (A : Finset α) :
    (∀ I : Finset α , G.IsIndependentSet I → #I ≤ #A) → d(i) ≤ #A := by
  have : G.IsIndependentSet N(i) :=
    by simp only [Set.coe_toFinset, SimpleGraph.isIndependentSet_neighborSet_if_triangleFree _ h,
    SimpleGraph.neighborFinset]
  intro maxA
  apply maxA N(i) this


-- The set B = V \ A meets every edge of G.
lemma B_meets_every_edge {A : Finset α} (indA : G.IsIndependentSet A) :
    (∀ I : Finset α, G.IsIndependentSet I → #I ≤ #A) → (∀ e ∈ E, 1 ≤ #{ b ∈ (V \ A) | b ∈ e }) := by

    intro maxA e edgee

    by_contra c
    simp at c
    have b_nin_e : ∀ b ∈ (V \ A) , ¬ (b ∈ e) := Finset.filter_eq_empty_iff.mp c
    induction e with | _ v w => -- TODO is this really how we deconstruct?!
     by_cases vinA : v ∈ (V \ A) -- TODO uglyyy
     . have : w ∈ (V \ A) := by by_contra _; apply (b_nin_e _ vinA); simp
       apply (b_nin_e _ this)
       simp
     . have : w ∉ (V \ A) := by by_contra wninA; apply (b_nin_e _ wninA); simp
       rw [SimpleGraph.IsIndependentSet] at indA
       aesop


-- We count the edges of G by counting the endvertices in B.
lemma count_edges_by_B {A : Finset α} (indA : G.IsIndependentSet A) :
    (∀ I : Finset α, G.IsIndependentSet I → #I ≤ #A) → #E ≤ ∑ i ∈ V \ A, d(i) := by

   -- The number of edges adjacent to i is the degree of i. -- TODO duh?
   have n_adj_edges_eq_deg : ∀ i, #{e ∈ E | i ∈ e} = d(i) := by
     intro i
     rw [Eq.symm (SimpleGraph.card_incidenceFinset_eq_degree G i)]
     rw [SimpleGraph.incidenceFinset_eq_filter]

   intro maxA

   calc
     #E = ∑ e ∈ E, 1                                := by simp
      _ ≤ ∑ e ∈ E, #{ i ∈ (V \ A) | i ∈ e }         := Finset.sum_le_sum
                                                         (B_meets_every_edge _ indA maxA)
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
theorem mantel (h: G.CliqueFree 3) (A : Finset α) (indA : G.IsIndependentSet A) :
    (∀ I : Finset α, G.IsIndependentSet I → #I ≤ #A) → #E ≤ (n^2 / 4) := by

  intro maxA

  have := calc #E
   _ ≤ ∑ i ∈ V \ A, d(i)      := count_edges_by_B G indA maxA
   _ ≤ ∑ _ ∈ V \ A, #A        := Finset.sum_le_sum (fun a _ => degreeLeqa G h A maxA)
   _ = #(V \ A) * #A          := Finset.sum_const _
   _ = (#V - #A) * #A         := by simp [Finset.card_sdiff _]; aesop

  have := calc #E * 4 -- TODO how annoying
   _ = 4 * #E                 := mul_comm _ _
   _ ≤ 4 * ((#V - #A) * #A)   := by aesop
   _ = 4 * (#V - #A) * #A     := Eq.symm (mul_assoc _ _ _)
   _ ≤ ((#V - #A) + #A)^2     := am_gm (#V - #A) (#A)
   _ = (#V)^2                 := by rw [Nat.sub_add_cancel];
                                    exact (Finset.card_le_card (Finset.subset_univ A))
   _ = n^2                    := by simp

  exact ((Nat.le_div_iff_mul_le' (by simp)).mpr this)

end AMGMMantelTheorem
