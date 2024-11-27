import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import TheBook.ToMathlib.EdgeFinset
import Aesop


namespace CauchyMantelTheorem

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "I(" v ")" => G.incidenceFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card α

open Finset SimpleGraph


#check completeBipartiteGraph
#check SimpleGraph.completeMultipartiteGraph
#check SimpleGraph.cliqueFree_completeMultipartiteGraph

lemma completeBipartiteGraph_equiv_completeMultipartiteGraph (β γ : Type u) :
  Nonempty (completeBipartiteGraph β γ ≃g SimpleGraph.completeMultipartiteGraph (fun b => cond b β γ)) := by
  let φ : β ⊕ γ → Σ b : Bool, cond b β γ := λ v => match v with
    | Sum.inl b => ⟨true, b⟩
    | Sum.inr c => ⟨false, c⟩

  have φ_inj : Function.Injective φ := by
    rintro (b₁ | c₁) (b₂ | c₂) h <;> injection h with h₁ h₂ <;> aesop

  have φ_surj : Function.Surjective φ := by
    rintro ⟨b, a⟩; cases b <;> simp_all

  have φ_bij : Function.Bijective φ := ⟨φ_inj, φ_surj⟩

  have φ_adj (x y : β ⊕ γ) :
    (completeBipartiteGraph β γ).Adj x y ↔
    (SimpleGraph.completeMultipartiteGraph (fun b => cond b β γ)).Adj (φ x) (φ y) := by
    cases x <;> cases y <;> simp [completeBipartiteGraph, SimpleGraph.completeMultipartiteGraph]
    
  exact Nonempty.intro ⟨Equiv.ofBijective φ φ_bij, by simp [φ_adj]⟩

lemma cliqueFree_completeBipartiteGraph {β γ : Type u} {k : ℕ} (h: k ≥ 3) : (completeBipartiteGraph β γ).CliqueFree k := by
  have φ := completeBipartiteGraph_equiv_completeMultipartiteGraph β γ
  have hCliqueFree := cliqueFree_completeMultipartiteGraph (fun b => cond b β γ) h
  
  sorry


theorem mantel_maximal_iff : G.CliqueFree 3 ∧ #E = n^2 / 4 ↔ Nonempty (G ≃g completeBipartiteGraph (Fin (n / 2)) (Fin ((n + 1) / 2))) := by
  constructor
  · intro ⟨h, hE⟩
    -- if we have equality then in the above chain of inequalities we have
    --
    -- in the AM-GM proof we have an independent set A size α
    -- a set B of size n - α that is also an independent set
    -- since if we have equality then 4 * #E = n^2 and therefore
    -- #E = ∑ i ∈ B, d(i) and therefore 1 = #{ i ∈ B | i ∈ e } for all e ∈ E
    -- in order to get to n^2 / 4 edges we ned to have all edges between A and B
    -- and 4 * #A * #B = (#A + #B)^2 so that one one way or the other the cardinalities match
    sorry

  · intro ⟨φ, hφ⟩

    have hCliqueFree : G.CliqueFree 3 := by
      by_contra hc
      rw [SimpleGraph.CliqueFree] at hc
      push_neg at hc
      obtain ⟨t, ⟨tclique, tcard⟩⟩ := hc
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp tcard
      let a' := φ a
      let b' := φ b
      let c' := φ c
      -- by pigeonhole, two of a', b', c' must be in the same partite set
      -- but their sources are adjacent in G
      -- giving a contradiction in the complete bipartite graph
      sorry

    have hE : #E = n^2 / 4 := by
      -- the complete bipartite graph has order n/2 * (n + 1)/2 which evaluates to n^2/4
      -- so G has order n^2/4 by the automorphism φ
      sorry

    exact ⟨hCliqueFree, hE⟩
    

end CauchyMantelTheorem
