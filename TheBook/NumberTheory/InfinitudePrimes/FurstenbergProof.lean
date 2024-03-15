import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic

namespace FurstenbergInfinitudePrimes

def N (a b : ℤ) : Set ℤ := { a + b * n | n : ℤ}

lemma N_infinite (a b : ℤ) (h : b ≠ 0) : (N a b).Infinite := by
  let f (n : ℤ) : N a b := ⟨a + b * n, by simp [N]⟩
  have f_inj : Function.Injective f := λ a₁ a₂ f_eq ↦ by simp [f, h] at f_eq; exact f_eq
  exact Set.infinite_coe_iff.mp (Infinite.of_injective f f_inj)

lemma el_N_of_dvd (a b n : ℤ) : n ∈ N a b ↔ b ∣ (n - a) := by
  constructor <;> {intro ⟨c, _⟩; use c; linarith }

lemma N_sub (a b m: ℤ) : N a (b * m) ⊆ N a b := by
  intro n h
  rw [el_N_of_dvd] at *
  exact Int.dvd_trans (Exists.intro m rfl) h
  
instance int_topology : TopologicalSpace ℤ where
  IsOpen O := O = ∅ ∨ (∀ a : O, ∃ b, b ≠ 0 ∧ N a b ⊆ O)

  isOpen_univ := by simp; exact exists_ne 0

  isOpen_sUnion U := by
    simp; intro sets_open
    by_cases h: ∀ s ∈ U, s = ∅
    · exact Or.inl h
    · rw [or_iff_right h]
      intro a U₀ U₀_in_U a_in_U₀
      specialize sets_open U₀ U₀_in_U
      simp [or_iff_right (Set.Nonempty.ne_empty (Exists.intro a a_in_U₀))] at sets_open
      obtain ⟨b, b_ne_zero, N_contained⟩ := sets_open a a_in_U₀
      exact ⟨b, b_ne_zero, λ _ a ↦ Set.subset_sUnion_of_mem U₀_in_U (N_contained a)⟩

  isOpen_inter O₁ O₂ h₁ h₂ := by
    simp at *
    by_cases h: O₁ ∩ O₂ = ∅
    · exact Or.inl h
    · simp [h]
      intro a a_in_O₁ a_in_O₂
      simp [Set.Nonempty.ne_empty (Exists.intro a a_in_O₁)] at h₁
      simp [Set.Nonempty.ne_empty (Exists.intro a a_in_O₂)] at h₂
      obtain ⟨b₁, b₁_ne_zero, N₁_contained⟩ := h₁ a a_in_O₁
      obtain ⟨b₂, b₂_ne_zero, N₂_contained⟩ := h₂ a a_in_O₂
      use b₁ * b₂
      have Nab1b2_su_Nab1 := N_sub a b₁ b₂
      have Nab1b2_su_Nab2 := N_sub a b₂ b₁
      rw [mul_comm] at Nab1b2_su_Nab2
      exact ⟨mul_ne_zero b₁_ne_zero b₂_ne_zero, λ _ a => N₁_contained (Nab1b2_su_Nab1 a), λ _ a => N₂_contained (Nab1b2_su_Nab2 a)⟩

lemma N_open (a b : ℤ) (h : b ≠ 0): IsOpen (N a b) := by 
  simp [IsOpen, TopologicalSpace.IsOpen, N]
  apply Or.inr
  exact λ a' ↦ (by use b; exact ⟨h, λ a'' ↦ by use a' + a''; ring_nf⟩)

lemma A (O : Set ℤ) (h₁ : IsOpen O) (h₂ : O ≠ ∅) : O.Infinite := by
  simp [IsOpen, TopologicalSpace.IsOpen, h₂] at h₁
  obtain ⟨a, a_in_O⟩ := (by push_neg at h₂; exact h₂)
  obtain ⟨b, b_ne_zero, N_su_O⟩ := h₁ a a_in_O
  exact Set.Infinite.mono N_su_O (N_infinite a b b_ne_zero)

lemma B (a : ℤ) (b : ℕ) (h : b > 0) : IsClosed (N a b) := by
  let Ub := (⋃ i : {x : ℕ // 1 ≤ x ∧ x < b}, N (a + i) b)

  have N_eq_Ubc : N a b = Ubᶜ := by

    have N_disjoint : Ub ∩ N a b = ∅ := by
      rw [Set.iUnion_inter]; simp
      intro idx idx_lw idx_up
      apply Set.disjoint_iff_inter_eq_empty.mp
      apply Set.disjoint_right.mpr
      intro n b_dvd b_dvd'
      simp [el_N_of_dvd] at b_dvd b_dvd'
      have b_dvd_idx : b ∣ idx := by have := Int.dvd_sub b_dvd' b_dvd; simp [Int.ofNat_dvd] at this; exact this
      exact (Nat.not_dvd_of_pos_of_lt idx_lw idx_up) b_dvd_idx

    have N_covers : Ub ∪ N a b = Set.univ := by
      apply Set.Subset.antisymm_iff.mpr
      constructor
      · exact λ _ _ ↦ trivial
      · intro n _
        simp [el_N_of_dvd, Ub]
        let i := (n - a) % (b : ℤ)
        by_cases i_cases : i = 0
        · exact Or.inr (Int.modEq_zero_iff_dvd.mp (i_cases))
        · apply Or.inl
          use Int.toNat i
          have i_ge_0 : i ≥ 0 := Int.emod_nonneg (n - a) (Int.coe_nat_ne_zero_iff_pos.mpr h)
          have nat_i_ge_0 := Int.lt_toNat.mpr (Ne.lt_of_le' i_cases i_ge_0)
          have nat_i_lt_b := (Int.toNat_lt i_ge_0).mpr (Int.emod_lt_of_pos (n - a) (Int.ofNat_pos.mpr h))
          have minus_i_dvd: (b : ℤ) ∣ (n - (a + i)) := Int.sub_sub n a i ▸ Int.dvd_sub_of_emod_eq rfl
          exact ⟨ ⟨nat_i_ge_0, nat_i_lt_b⟩, Int.toNat_of_nonneg i_ge_0 ▸ minus_i_dvd⟩

    exact (compl_unique N_disjoint N_covers).symm

  rw [N_eq_Ubc]
  apply isClosed_compl_iff.mpr
  apply isOpen_iUnion
  exact λ i ↦ N_open (a + i) b (Int.coe_nat_ne_zero_iff_pos.mpr h)

theorem infinitude_primes : { p : ℕ | Nat.Prime p }.Infinite := by
  have Z_as_U : {1, -1}ᶜ = (⋃ p ∈ {p : ℕ | Nat.Prime p}, N 0 p) := by
    apply Set.ext; intro n

    constructor <;> intro n_el
    · obtain ⟨p, p_prime, p_dvd_n⟩ := Nat.exists_prime_and_dvd (λ c ↦ n_el (Int.natAbs_eq_iff.mp c))
      have n_in_Np : n ∈ N 0 p := by simp [el_N_of_dvd]; exact Int.ofNat_dvd_left.mpr p_dvd_n
      simp; exact ⟨p, p_prime, n_in_Np⟩

    · simp [el_N_of_dvd] at *
      obtain ⟨p, p_prime, p_dvd_n⟩ := n_el
      have p_ndvd_one := Int.ofNat_dvd.not.mpr (Prime.not_dvd_one (Nat.prime_iff.mp p_prime))
      push_neg; constructor
      all_goals {by_contra c; rw [c, ←Nat.cast_one] at p_dvd_n ; simp [Int.dvd_neg.mpr] at p_dvd_n; exact p_ndvd_one p_dvd_n}

  by_contra h
  
  have U_close : IsClosed (⋃ p ∈ {p : ℕ | Nat.Prime p}, N 0 p) := by
    have (p : ℕ) (p_prime : p ∈ {p : ℕ | Nat.Prime p}) : IsClosed (N 0 p) := by simp at p_prime; exact B 0 p (Nat.Prime.pos p_prime)
    exact Set.Finite.isClosed_biUnion (Set.not_infinite.mp h) this
  have one_open : IsOpen {1, -1} := isClosed_compl_iff.mp (Z_as_U ▸ U_close)
  have one_infinite := A {1, -1} one_open (Set.Nonempty.ne_empty (Set.insert_nonempty 1 {-1}))

  exact one_infinite (Set.toFinite {1, -1})
  
end FurstenbergInfinitudePrimes
