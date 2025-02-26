import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

open Nat Finset

-- Basic example of induction using Peano's axiom
example (n : Nat) : choose n 2 = n * (n - 1) / 2 := by
  induction' n with n ih
  · simp
  · rw [Nat.triangle_succ n]
    rw [Nat.choose, ih]
    simp [Nat.add_comm]

-- Explicitly using Nat.rec
example (n : Nat) : choose n 2 = n * (n - 1) / 2 := by
  induction' n using Nat.rec with n ih
  · simp
  · rw [Nat.triangle_succ n, Nat.choose, ih]
    simp [Nat.add_comm]

-- Using two-step induction
example (n : Nat) : choose n 2 = n * (n - 1) / 2 := by
  induction' n using Nat.twoStepInduction with n _ ih'
  · simp
  · simp
  · rw [Nat.triangle_succ (n + 1)]
    rw [Nat.choose, ih']
    simp [Nat.add_comm]

-- Using strong induction
example (n : Nat) : choose n 2 = n * (n - 1) / 2 := by
  induction' n using Nat.strong_induction_on with k ik
  by_cases h : k = 0
  · simp [h]  
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
    rw [Nat.triangle_succ n]
    rw [Nat.choose, ik n (Nat.lt_succ_self n)]
    simp [Nat.add_comm]

-- Basic example of induction using le_induction
example (n k : Nat) (h : n ≥ k) : ∑ m ∈ Icc k n, m.choose k = (n + 1).choose (k + 1) := by
  induction' n, h using le_induction with n _ ih
  · simp
  · rw [← Ico_insert_right (by omega), sum_insert (by simp),
      show Ico k (n + 1) = Icc k n by rfl, ih, choose_succ_succ' (n + 1)]
