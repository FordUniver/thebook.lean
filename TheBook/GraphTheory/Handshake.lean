import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Aesop

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

prefix:100 "#" => Finset.card
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "d(" v ")" => G.degree v
local notation "I(" v ")" => G.incidenceFinset v
local notation "χ(" p ")" => if p then 1 else 0

lemma edge_card_eq_two (e : Sym2 α) (he : e ∈ E): #{v ∈ V | v ∈ e} = 2 := by
  rw [Finset.card_eq_two]
  induction e with | _ v w => use v, w, (by aesop); ext; simp

lemma handshake : ∑ v ∈ V, d(v) = 2 * #E := by
  calc  ∑ v ∈ V, d(v)
    _ = ∑ v ∈ V, #I(v)                := by simp [G.card_incidenceFinset_eq_degree]
    _ = ∑ v ∈ V, ∑ e ∈ E, χ(v ∈ e)    := by simp [G.incidenceFinset_eq_filter]
    _ = ∑ e ∈ E, ∑ v ∈ V, χ(v ∈ e)    := Finset.sum_comm
    _ = ∑ e ∈ E, #{v ∈ V | v ∈ e}     := by simp
    _ = ∑ e ∈ E, 2                    := Finset.sum_congr rfl (λ e he ↦ edge_card_eq_two e he)
    _ = 2 * ∑ e ∈ E, 1                := (Finset.mul_sum E (λ _ ↦ 1) 2).symm
    _ = 2 * #E                        := by rw [Finset.card_eq_sum_ones E]
