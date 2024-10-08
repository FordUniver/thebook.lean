import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Set.BoolIndicator
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
-- import Mathlib.Tactic.Basic
import Aesop

set_option trace.aesop true
set_option autoImplicit false

prefix:100 "#" => Finset.card
set_option linter.unusedSectionVars false

namespace CauchyMantelTheorem

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "N(" v ")" => G.neighborFinset v
local notation "d(" v ")" => G.degree v
local notation "χ(" p ")" => if p then 1 else 0
local notation "n" => Fintype.card α


attribute [simp] Nat.pow_two
attribute [simp] Finset.sum_congr
attribute [simp] Finset.one_lt_card
attribute [simp] Finset.card_ne_zero_of_mem
attribute [aesop safe] Finset.mul_sum
attribute [aesop safe] Finset.card_eq_sum_ones
attribute [aesop safe] SimpleGraph.adj_symm
attribute [aesop safe] SimpleGraph.Adj.ne
attribute [aesop safe] HMul.hMul
attribute [aesop safe] Sym2.Mem.other


-- edges have two vertices
-- lemma card_edge_eq_two (e : Sym2 α) (he : e ∈ E): #{v ∈ V | v ∈ e} = 2 := by
--   rw [Finset.card_eq_two]
--   induction e with | _ v w =>
--     use v, w, (by aesop)
--     ext; simp

-- degree of v is the sum of the indicator functions of the edges containing v
-- lemma aux (e : Sym2 α) (v : α) : #{w' ∈ V | s(v,w') = e} = χ(v ∈ e) := by
--   by_cases hve : v ∈ e
--   · let S := {w' ∈ V | s(v,w') = e}
--     have : Sym2.Mem.other hve ∈ S := by aesop
--     have : #S ≠ 0 := Finset.card_ne_zero_of_mem this
--     by_contra hc; simp [hve] at hc
--     have : ∃ a ∈ S, ∃ b ∈ S, a ≠ b := Finset.one_lt_card.mp ((Nat.two_le_iff (#S)).mpr ⟨this, hc⟩)
--     aesop
--   · aesop

-- lemma deg_sum_edges (v : α) : d(v) = ∑ e ∈ E, χ(v ∈ e) := by
--   calc d(v)
--     _ = #{w | G.Adj v w}.toFinset                := rfl
--     _ = ∑ w ∈ V, χ(G.Adj v w)                    := by simp
--     _ = ∑ w ∈ V, ∑ e ∈ E, χ(s(v,w) = e)          := by simp
--     _ = ∑ e ∈ E, ∑ w ∈ V, χ(s(v,w) = e)          := Finset.sum_comm
--     _ = ∑ e ∈ E, ∑ w ∈ {w' ∈ V | s(v,w') = e}, 1 := by simp
--     _ = ∑ e ∈ E, #{w' ∈ V | s(v,w') = e}         := by simp
--     _ = ∑ e ∈ E, χ(v ∈ e)                        := by simp [aux]

-- lemma handshake : ∑ v ∈ V, d(v) = 2 * #E := by
--   calc  ∑ v ∈ V, d(v)
--     _ = ∑ v ∈ V, ∑ e ∈ E, χ(v ∈ e)    := by simp [deg_sum_edges]
--     _ = ∑ e ∈ E, ∑ v ∈ V, χ(v ∈ e)    := Eq.symm Finset.sum_comm
--     _ = ∑ e ∈ E, #{v ∈ V | v ∈ e}     := Finset.sum_congr rfl (λ e _ ↦ (Finset.card_filter (λ v ↦ v ∈ e) _).symm)
--     _ = ∑ e ∈ E, 2                    := Finset.sum_congr rfl (λ e he ↦ card_edge_eq_two e he)
--     _ = 2 * ∑ e ∈ E, 1                := Eq.symm (Finset.mul_sum E (λ _ ↦ 1) 2)
--     _ = 2 * #E                        := by simp

-- Mantel's Theorem
theorem mantel (h: G.CliqueFree 3) : #E ≤ (n^2 / 4) := by

  -- The degrees of two adjacent vertices cannot sum to more than n
  have adj_degree_bnd (i j : α) (hij: G.Adj i j) : d(i) + d(j) ≤ n := by
    -- Assume the contrary ...
    by_contra hc; simp at hc

    -- ... then by pigeonhole there would exist a vertex k adjacent to both i and j ...
    obtain ⟨k, h⟩ := Finset.inter_nonempty_of_card_lt_card_add_card _ _ hc
    simp at h
    obtain ⟨hik, hjk⟩ := h

    -- ... but then i, j, k would form a triangle, contradicting that G is triangle-free
    exact h {k, j, i} ⟨by aesop, by simp [hij.ne', hik.ne', hjk.ne']⟩ 

  -- We need to define the sum of the degrees of the vertices of an edge ...
  let sum_deg (e : Sym2 α) : ℕ := Sym2.lift ⟨λ x y ↦ d(x) + d(y), by simp [Nat.add_comm]⟩ e

  -- ... and establish a variant of adj_degree_bnd ...
  have adj_degree_bnd' (e : Sym2 α) (he: e ∈ E) : sum_deg e ≤ n := by
    induction e with | _ v w => simp at he; exact adj_degree_bnd v w (by simp [he])

  -- ... as well as
  have sum_deg_eq (e : Sym2 α) (he: e ∈ E) : sum_deg e = ∑ v ∈ {v ∈ V | v ∈ e}, d(v) := by sorry

  have sum_sum_deg_eq_sum_sum_sq : ∑ e ∈ E, sum_deg e = ∑ v ∈ V, d(v)^2 := by
    let S (e : Sym2 α) := {v ∈ V | v ∈ e}
    calc  ∑ e ∈ E, sum_deg e
      _ = ∑ e ∈ E, ∑ v ∈ {v ∈ V | v ∈ e}, d(v)                  := Finset.sum_congr rfl sum_deg_eq
      _ = ∑ e ∈ E, (∑ v ∈ V, d(v) * χ(v ∈ {v ∈ V | v ∈ e}))     := sorry -- AESOP SHOULD SOLVE THIS
      _ = ∑ e ∈ E, (∑ v ∈ V, d(v) * χ(v ∈ e))              := by simp
      _ = ∑ v ∈ V, (∑ e ∈ E, (d(v) * χ(v ∈ e)))            := Finset.sum_comm
      _ = ∑ v ∈ V, (d(v) * (∑ e ∈ E, χ(v ∈ e)))            := Finset.sum_congr rfl (λ v a ↦ (Finset.mul_sum E (λ i ↦ χ(v ∈ i)) d(v)).symm)
      _ = ∑ v ∈ V, d(v)^2                                  := Finset.sum_congr rfl (by simp [adj_degree_bnd'])

  -- We slightly modify the argument to avoid division (in particular by zero)
  have := calc n^2 * #E
    _ = n * (n * ∑ e ∈ E, 1)                     := by simp [Nat.mul_assoc]
    _ = n * (∑ e ∈ E, n)                         := by rw [Finset.mul_sum]; simp
    _ ≥ n * ∑ e ∈ E, sum_deg e                   := Nat.mul_le_mul_left _ (Finset.sum_le_sum adj_degree_bnd')
    _ = (∑ v ∈ V, d(v)^2) * (∑ v ∈ V, 1^2)       := by simp [Nat.mul_comm, sum_sum_deg_eq_sum_sum_sq]
    _ ≥ (∑ v ∈ V, d(v) * 1)^2                    := (Finset.sum_mul_sq_le_sq_mul_sq V (λ v ↦ d(v)) 1)
    _ = (2 * #E)^2                               := by simp [G.sum_degrees_eq_twice_card_edges]
    _ = 4 * #E^2                                 := by ring

  sorry

  -- now show #E ≤ n^2 / 4 by "simply" dividing by 4 * #E
  by_cases hE : #E = 0
  · aesop
  · push_neg at hE
    have t₇ : n ^ 2 * #E ≥ (4 * #E) * #E := by linarith
    have : n ^ 2 ≥ 4 * #E := Nat.le_of_mul_le_mul_right t₇ (Nat.zero_lt_of_ne_zero hE) 
    have : 4 > 0 := Nat.zero_lt_succ 3
    sorry --FIX

-- Probably needs to use floor and ceil to be precise ...
theorem mantel_equality (h: G.CliqueFree 3) : 0 = 0 := by
  sorry


example ( a b : ℕ) (h : a ≤ b) : b ≥ a := by exact h

end CauchyMantelTheorem
