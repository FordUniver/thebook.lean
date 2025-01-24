import Mathlib.Tactic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Slice
import Mathlib.Order.Antichain
import Mathlib.Order.Chain
import Mathlib.Data.List.Perm.Basic

open Function Finset Nat Set BigOperators List

variable {α : Type*} {n m : ℕ} {𝒜 : Finset (Finset α)} (r : α → α → Prop)

namespace Finset

/-- In this file, we use `≺` as a local notation for any relation `r`. -/
local infixl:50 " ≺ " => r

/-
  The following definitions match the ones in Mathlib.Order.Chain, but use Finset in order to be able to carry information on finiteness inside the chain property.
-/

def IsChain (s : Finset α) : Prop :=
  s.toSet.Pairwise fun x y => x ≺ y ∨ y ≺ x

/-- `SuperChain s t` means that `t` is a chain that strictly includes `s`. -/
def SuperChain (s t : Finset α) : Prop :=
  IsChain r t ∧ s ⊂ t

/-- A chain `s` is a maximal chain if there does not exists a chain strictly including `s`. -/
def IsMaxChain (s :  Finset α) : Prop :=
  IsChain r s ∧ ∀ ⦃t⦄, IsChain r t → s ⊆ t → s = t

def IsAntichain (r : α → α → Prop) (s : Finset α) : Prop :=
  s.toSet.Pairwise rᶜ

end Finset

variable (ℬ₀ : Set α) (ℬ₁ : Finset α) (r : α → α → Prop)

/- The usual definition of chains are compatible if used along the toSet method-/
example (h : Finset.IsChain r ℬ₁) : IsChain r ℬ₁.toSet := h
example (h : IsChain r ℬ₁.toSet) : Finset.IsChain r ℬ₁ := h

instance [Fintype ℬ₀] : Coe (IsChain r ℬ₀) (Finset.IsChain r ℬ₀.toFinset) :=
  ⟨fun h ↦ (fun _ hx _ hy xneqy ↦ h (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy) xneqy)⟩

example [Fintype ℬ₀] (h : IsChain r ℬ₀) : Finset.IsChain r ℬ₀.toFinset := h

instance [Fintype α] : Fintype (Finset α) := {
  elems := Finset.powerset (@Finset.univ α _),
  complete := by simp
}

noncomputable instance [Fintype α] : Fintype ℬ₀ := Fintype.ofFinite ↑ℬ₀
noncomputable instance [Fintype α] : Coe (Set α) (Finset α) := ⟨fun s ↦ s.toFinset⟩
noncomputable example [Fintype α] (𝒟 : Set α) : Finset α := 𝒟

instance [Fintype α] : Coe (_root_.IsChain r ℬ₀) (Finset.IsChain r ℬ₀.toFinset) :=
  ⟨fun h ↦ (fun _ hx _ hy xneqy ↦ h (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy) xneqy)⟩

instance [Fintype α] : Fintype (Set α) := {
  elems := (Finset.powerset (@Finset.univ α _)).map ⟨Finset.toSet, Finset.coe_injective⟩,
  complete := by intro x; simp; use x.toFinset; simp
}
