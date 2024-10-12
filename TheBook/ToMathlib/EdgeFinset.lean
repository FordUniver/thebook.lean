import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Operations

-- https://github.com/leanprover-community/mathlib4/pull/17587

variable {α : Type*}

namespace Sym2

@[coe]
protected def toMultiset (z : Sym2 α) : Multiset α :=
  Sym2.lift ⟨fun x y => {x, y}, Multiset.pair_comm⟩ z

instance : Coe (Sym2 α) (Multiset α) := ⟨Sym2.toMultiset⟩

@[simp] lemma toMultiset_mk {x y : α} : (s(x, y) : Multiset α) = {x, y} := rfl

variable [DecidableEq α]

@[coe]
protected def toFinset (z : Sym2 α) : Finset α := Multiset.toFinset z

instance : Coe (Sym2 α) (Finset α) := ⟨Sym2.toFinset⟩

@[simp] lemma toFinset_mk {x y : α} : (s(x, y) : Finset α) = {x, y} := by
  ext; rw [Sym2.toFinset, Sym2.toMultiset]; simp

@[simp] lemma toFinset_toMultiset {s : Sym2 α} : (s : Multiset α).toFinset = (s : Finset α) := rfl

@[simp] lemma mem_toFinset {z : Sym2 α} {x : α} : x ∈ (z : Finset α) ↔ x ∈ z := by
  induction z; simp

@[simp] lemma coe_toFinset {z : Sym2 α} : ((z : Finset α) : Set α) = z := by
  ext; simp

lemma toFinset_eq [Fintype α] {e : Sym2 α} : (e : Finset α) = {v | v ∈ e}.toFinset := by
  ext; simp

end Sym2


namespace SimpleGraph

variable [Fintype α] {G : SimpleGraph α} [DecidableRel G.Adj]

@[simp] lemma mem_incidenceSet_iff_mem_edge (v : α) {e : Sym2 α} (he : e ∈ G.edgeFinset) :
    v ∈ e ↔ e ∈ G.incidenceSet v := by
  simp [SimpleGraph.incidenceSet]
  exact λ _ ↦ SimpleGraph.mem_edgeFinset.mp he

variable [DecidableEq α]

@[simp] lemma mem_incidenceFinset_iff_mem_edge (v : α) {e : Sym2 α} (he : e ∈ G.edgeFinset) :
    v ∈ e ↔ e ∈ G.incidenceFinset v := by
  simp [SimpleGraph.incidenceFinset, SimpleGraph.incidenceSet]
  exact λ _ ↦ SimpleGraph.mem_edgeFinset.mp he

end SimpleGraph
