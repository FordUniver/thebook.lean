import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Pairwise

-- https://github.com/leanprover-community/mathlib4/pull/18218

open Finset Fintype

namespace SimpleGraph

variable {α β : Type*} (G H : SimpleGraph α)

section Clique

lemma isClique_compl_map_iff_isClique_map_compl {f : α ↪ β} {s : Set α} :
    (SimpleGraph.map f G)ᶜ.IsClique (f '' s) ↔ (SimpleGraph.map f Gᶜ).IsClique (f '' s) := by
  repeat rw [isClique_iff, Set.Pairwise]
  rw [forall₂_congr]; intro a ha
  rw [forall₂_congr]; intro b hb
  rw [←imp_congr_right]; intro hab
  obtain ⟨a', _, ha'a⟩ := ha
  obtain ⟨b', _, hb'b⟩ := hb
  subst ha'a hb'b
  simp only [map_adj_apply, compl_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]

theorem induce_compl_eq_compl_induce {s : Set α} : induce s Gᶜ = (induce s G)ᶜ := by sorry

end Clique


section IndependentSet

variable {s t : Set α}

/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
abbrev IsIndependentSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)

-- The neighbors of a vertex i form an independent set in a trianlge free graph G.
theorem isIndependentSet_neighborSet_if_triangleFree [DecidableEq α] (h: G.CliqueFree 3) (i : α) :
    G.IsIndependentSet (G.neighborSet i) := by
  by_contra nind
  simp [SimpleGraph.IsIndependentSet, Set.Pairwise] at nind
  obtain ⟨j, aij, k, aik, _, ajk⟩ := nind
  exact h {i, j, k} (is3Clique_triple_iff.mpr (by simp only [aij, aik, ajk, and_self]))

theorem isIndependentSet_iff : G.IsIndependentSet s ↔ s.Pairwise (fun v w ↦ ¬G.Adj v w) :=
  Iff.rfl

/-- An independent set is a clique in the complement graph and vice versa. -/
theorem isIndependentSet_iff_isClique_of_complement : G.IsIndependentSet s ↔ Gᶜ.IsClique s := by
  rw [isIndependentSet_iff, isClique_iff]; repeat rw [Set.Pairwise]
  simp_all only [compl_adj, ne_eq, not_false_eq_true, true_and]

/-- An independent set is a set of vertices whose induced graph is empty. -/
theorem isIndependentSet_iff_induce_eq : G.IsIndependentSet s ↔ G.induce s = ⊥ := by
  rw [isIndependentSet_iff_isClique_of_complement, isClique_iff_induce_eq, ← compl_eq_top,
  induce_compl_eq_compl_induce]

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsIndependentSet s) :=
  decidable_of_iff' _ G.isIndependentSet_iff

variable {G H} {a b : α}

lemma isIndependentSet_empty : G.IsIndependentSet ∅ := by simp

lemma isIndependentSet_singleton (a : α) : G.IsIndependentSet {a} := by simp

theorem IsIndependentSet.of_subsingleton {G : SimpleGraph α} (hs : s.Subsingleton) :
    G.IsIndependentSet s :=
  hs.pairwise (fun v w => ¬ G.Adj v w)

lemma isIndependentSet_pair : G.IsIndependentSet {a, b} ↔ ¬ G.Adj a b := by
  by_cases h : a = b
  · subst h; simp
  · rw [isIndependentSet_iff_isClique_of_complement, isClique_pair, compl_adj, ne_eq]
    simp only [h]
    rw [not_false_eq_true, true_and, true_implies]

@[simp]
lemma isIndependentSet_insert :
    G.IsIndependentSet (insert a s) ↔ G.IsIndependentSet s ∧ ∀ b ∈ s, ¬ G.Adj a b := by
  repeat rw [isIndependentSet_iff_isClique_of_complement]
  have hu : (∀ b ∈ s, (a ≠ b → Gᶜ.Adj a b)) ↔ ∀ b ∈ s, ¬ G.Adj a b := by aesop
  rw [isClique_insert, hu]

-- TODO why do we have this?
lemma IsIndependentSet.insert (hs : G.IsIndependentSet s) (h : ∀ b ∈ s, ¬ G.Adj a b) :
    G.IsIndependentSet (insert a s) := isIndependentSet_insert.mpr ⟨hs ,h⟩

theorem IsIndependentSet.anti (h : G ≤ H) : H.IsIndependentSet s → G.IsIndependentSet s := by
  repeat rw [isIndependentSet_iff_isClique_of_complement]
  apply IsClique.mono (compl_le_compl_iff_le.mpr h)

theorem IsIndependentSet.subset (h : t ⊆ s) : G.IsIndependentSet s → G.IsIndependentSet t :=
  Set.Pairwise.mono h

@[simp]
theorem isIndependentSet_top_iff :
    (⊤ : SimpleGraph α).IsIndependentSet s ↔ (s : Set α).Subsingleton := by
  rw [isIndependentSet_iff_isClique_of_complement]
  simp only [compl_top, isClique_bot_iff]

alias ⟨IsIndependentSet.subsingleton, _⟩ := isIndependentSet_top_iff

protected theorem IsIndependentSet.map (h : G.IsIndependentSet s) {f : α ↪ β} :
    (G.map f).IsIndependentSet (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  have haneb : a ≠ b := fun a' ↦ hab (congrArg (⇑f) a')
  simp [h ha hb haneb]

@[simp] theorem isIndependentSet_map_image_iff {f : α ↪ β} :
    (G.map f).IsIndependentSet (f '' s) ↔ G.IsIndependentSet s := by
  constructor
  · rintro h _ xs _ ys xny
    rw [isIndependentSet_iff_isClique_of_complement, isClique_compl_map_iff_isClique_map_compl,
    isClique_map_image_iff] at h
    have := (h xs ys xny)
    simp_all only [not_false_eq_true, compl_adj]
  · exact fun a ↦ IsIndependentSet.map a


protected theorem IsIndependentSet.finsetMap {f : α ↪ β} {s : Finset α} (h : G.IsIndependentSet s) :
    (G.map f).IsIndependentSet (s.map f) := by
  simpa

/- might be handy idk
lemma map_compl_le_compl_map {f : α ↪ β} : (SimpleGraph.map f Gᶜ) ≤ (SimpleGraph.map f G)ᶜ := by
  intro v w h
  simp only [compl_adj, ne_eq, map_adj, not_exists, not_and]
  refine ⟨Adj.ne h, ?_⟩
  intro x y xay fxv
  by_contra fyw
  subst fyw fxv

  have : ¬ Gᶜ.Adj x y := by simp only [compl_adj, not_and, not_not]; intro; exact xay
  have : ¬ (SimpleGraph.map f Gᶜ).Adj (f x) (f y) := by
    simp_all only [compl_adj, not_true_eq_false, not_false_eq_true, map_adj,
    EmbeddingLike.apply_eq_iff_eq, exists_eq_right_right, exists_eq_right]

  exact this h
-/

-- TODO this doesnt hold. the dual seems to be more complicated, like t = (f '' s) ∪ k where
-- k and (im f) are disjoint. same for isClique_map_iff and finset pendants
-- theorem isIndependentSet_map_iff_of_nontrivial {f : α ↪ β} {t : Set β} (ht : t.Nontrivial) :
--     (G.map f).IsIndependentSet t ↔ ∃ (s : Set α), G.IsIndependentSet s ∧ f '' s = t := by



end IndependentSet

-- TODO this is mostly just copy paste. ok?
section NIndependentSet

variable {n : ℕ} {s : Finset α}

/-- An `n`-IndependentSet in a graph is a set of `n` vertices which are pairwise nonadjacent. -/
structure IsNIndependentSet (n : ℕ) (s : Finset α) : Prop where
  IndependentSet : G.IsIndependentSet s
  card_eq : s.card = n

theorem isNIndependentSet_iff : G.IsNIndependentSet n s ↔ G.IsIndependentSet s ∧ s.card = n :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- An independent n-set is an n-clique in the complement graph and vice versa. -/
theorem isNIndependentSet_iff_isNClique_of_complement :
    G.IsNIndependentSet n s ↔ Gᶜ.IsNClique n s := by
  rw [isNIndependentSet_iff, isIndependentSet_iff_isClique_of_complement]
  simp [isNClique_iff]

instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNIndependentSet n s) :=
  decidable_of_iff' _ G.isNIndependentSet_iff

variable {G H} {a b c : α}

@[simp] lemma isNIndependentSet_empty : G.IsNIndependentSet n ∅ ↔ n = 0 := by
  simp [isNIndependentSet_iff, eq_comm]

@[simp]
lemma isNIndependentSet_singleton : G.IsNIndependentSet n {a} ↔ n = 1 := by
  simp [isNIndependentSet_iff, eq_comm]

theorem IsNIndependentSet.anti (h : G ≤ H) : H.IsNIndependentSet n s → G.IsNIndependentSet n s := by
  simp_rw [isNIndependentSet_iff]
  exact And.imp_left (IsIndependentSet.anti h)

protected theorem IsNIndependentSet.map (h : G.IsNIndependentSet n s) {f : α ↪ β} :
    (G.map f).IsNIndependentSet n (s.map f) :=
  ⟨by rw [coe_map]; exact h.1.map, (card_map _).trans h.2⟩

@[simp]
theorem isNIndependentSet_top_iff :
    (⊤ : SimpleGraph α).IsNIndependentSet n s ↔ n ≤ 1 ∧ s.card = n := by
  rw [isNIndependentSet_iff, isIndependentSet_top_iff]
  refine and_congr_left ?_
  rintro rfl
  exact card_le_one.symm

@[simp]
theorem isNIndependentSet_zero : G.IsNIndependentSet 0 s ↔ s = ∅ := by
  simp only [isNIndependentSet_iff, Finset.card_eq_zero, and_iff_right_iff_imp]; rintro rfl; simp

@[simp]
theorem isNIndependentSet_one : G.IsNIndependentSet 1 s ↔ ∃ a, s = {a} := by
  simp only [isNIndependentSet_iff, card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp

section DecidableEq

variable [DecidableEq α]

theorem IsNIndependentSet.insert (hs : G.IsNIndependentSet n s) (h : ∀ b ∈ s, ¬ G.Adj a b) :
    a ∉ s → G.IsNIndependentSet (n + 1) (insert a s) := by
  intro ans
  constructor
  · push_cast
    exact hs.1.insert fun b hb hab => h b hb hab
  · rw [card_insert_of_not_mem ans, hs.2]

theorem is3IndependentSet_triple_iff :
    G.IsNIndependentSet 3 {a, b, c} ↔
    (a ≠ b ∧ ¬ G.Adj a b) ∧ (a ≠ c ∧ ¬ G.Adj a c) ∧ (b ≠ c ∧ ¬ G.Adj b c) := by
  rw [isNIndependentSet_iff_isNClique_of_complement]
  repeat rw [← compl_adj]
  simp [is3Clique_triple_iff]

theorem is3IndependentSet_iff :
    G.IsNIndependentSet 3 s ↔
    ∃ a b c, (a ≠ b ∧ ¬ G.Adj a b) ∧ (a ≠ c ∧ ¬ G.Adj a c) ∧ (b ≠ c ∧ ¬ G.Adj b c) ∧
    s = {a, b, c} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨a, b, c, -, -, -, hs⟩ := card_eq_three.1 h.card_eq
    refine ⟨a, b, c, ?_⟩
    rwa [hs, eq_self_iff_true, and_true, is3IndependentSet_triple_iff.symm, ← hs]
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is3IndependentSet_triple_iff.2 ⟨hab, hbc, hca⟩

end DecidableEq

-- theorem is3IndependentSet_iff_exists_cycle_length_three :
-- (∃ s : Finset α, G.IsNIndependentSet 3 s) ↔ ∃ (u : α) (w : G.Walk u u), w.IsCycle ∧ w.length
-- TODO is there a dual to this one? if not, do we even need the other thrms about 3-sets?

end NIndependentSet


/-! ### Graphs without independent sets -/


section IndependentSetFree

variable {m n : ℕ}

/-- `G.IndependentSetFree n` means that `G` has no `n`-independent sets. -/
def IndependentSetFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNIndependentSet n t

/-- An graph is 'n'-independent set free iff its complement is n-clique free. -/
theorem isIndependentSetFree_iff_isCliqueFree_of_complement :
    G.IndependentSetFree n ↔ Gᶜ.CliqueFree n := by
  simp [IndependentSetFree, isNIndependentSet_iff_isNClique_of_complement, CliqueFree]

variable {G H} {s : Finset α}

theorem IsNIndependentSet.not_independentSetFree (hG : G.IsNIndependentSet n s) :
    ¬G.IndependentSetFree n :=
  fun h ↦ h _ hG

theorem not_independentSetFree_of_bot_embedding {n : ℕ} (f : (⊥ : SimpleGraph (Fin n)) ↪g G) :
    ¬G.IndependentSetFree n := by
  simp [isIndependentSetFree_iff_isCliqueFree_of_complement]
  exact not_cliqueFree_of_top_embedding ⟨ f.toEmbedding , by simp? ⟩

/-- An embedding of an empty graph that witnesses the fact that the graph is not independent set
free. -/
noncomputable def botEmbeddingOfNotIndependentSetFree {n : ℕ} (h : ¬G.IndependentSetFree n) :
    (⊥ : SimpleGraph (Fin n)) ↪g G := by
  simp [isIndependentSetFree_iff_isCliqueFree_of_complement] at h
  refine ⟨ (topEmbeddingOfNotCliqueFree h).toEmbedding, ?_⟩
  intro a b
  by_cases h : a = b
  · subst h; simp
  · simp; exact And.right ((compl_adj _ _ _).mp (by simp [← compl_adj]; exact h))

theorem not_independentSetFree_iff (n : ℕ) :
    ¬G.IndependentSetFree n ↔ Nonempty ((⊥ : SimpleGraph (Fin n)) ↪g G) :=
  ⟨fun h ↦ ⟨botEmbeddingOfNotIndependentSetFree h⟩,
   fun ⟨f⟩ ↦ not_independentSetFree_of_bot_embedding f⟩

theorem independentSetFree_iff {n : ℕ} :
    G.IndependentSetFree n ↔ IsEmpty ((⊥ : SimpleGraph (Fin n)) ↪g G) := by
  rw [← not_iff_not, not_independentSetFree_iff, not_isEmpty_iff]

theorem not_independentSetFree_card_of_bot_embedding [Fintype α] (f : (⊥ : SimpleGraph α) ↪g G) :
    ¬G.IndependentSetFree (card α) := by
  rw [isIndependentSetFree_iff_isCliqueFree_of_complement]
  exact (not_cliqueFree_card_of_top_embedding ⟨f.toEmbedding , by simp⟩)

@[simp]
theorem independentSetFree_top (h : 2 ≤ n) : (⊤ : SimpleGraph α).IndependentSetFree n := by
  intro t ht
  have := le_trans h (isNIndependentSet_top_iff.1 ht).1
  contradiction

theorem IndependentSetFree.mono (h : m ≤ n) : G.IndependentSetFree m → G.IndependentSetFree n := by
  repeat rw [isIndependentSetFree_iff_isCliqueFree_of_complement]
  apply CliqueFree.mono
  exact h

-- TODO naming
theorem IndependentSetFree.mono' (h : G ≤ H) : G.IndependentSetFree n → H.IndependentSetFree n :=
  forall_imp fun _ ↦ mt <| IsNIndependentSet.anti h

/-- If a graph is independent set free, any graph that embeds into it is also independent set
free. -/
theorem IndependentSetFree.comap {H : SimpleGraph β} (f : H ↪g G) :
    G.IndependentSetFree n → H.IndependentSetFree n := by
  intro h; contrapose h
  exact not_independentSetFree_of_bot_embedding <| f.comp (botEmbeddingOfNotIndependentSetFree h)

@[simp] theorem independentSetFree_map_if {f : α ↪ β} [Nonempty α] :
    (G.map f).IndependentSetFree n → G.IndependentSetFree n := by
  sorry

/-- See `SimpleGraph.independentSetFree_of_chromaticNumber_lt` for a tighter bound. -/
theorem independentSetFree_of_card_lt [Fintype α] (hc : card α < n) : G.IndependentSetFree n := by
  by_contra h
  refine Nat.lt_le_asymm hc ?_
  rw [independentSetFree_iff, not_isEmpty_iff] at h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding h.some.toEmbedding

-- TODO is there an interesting dual?
--theorem cliqueFree_completeMultipartiteGraph {ι : Type*} [Fintype ι] (V : ι → Type*)
--    (hc : card ι < n) : (completeMultipartiteGraph V).CliqueFree n := by


-- TODO
-- protected theorem IndependentSetFree.replaceVertex [DecidableEq α]
--    (h : G.IndependentSetFree n) (s t : α) :
--    (G.replaceVertex s t).IndependentSetFree n := by


@[simp]
theorem independentSetFree_two : G.IndependentSetFree 2 ↔ G = ⊤ := by
  rw [isIndependentSetFree_iff_isCliqueFree_of_complement, Iff.symm compl_eq_bot, cliqueFree_two]

/-- Removing an edge increases the coclique number by at most one. -/
protected theorem IndependentSetFree.sup_edge (h : G.IndependentSetFree n) (v w : α) :
    (G ⊓ edge v w).IndependentSetFree (n + 1) := by
  rw [isIndependentSetFree_iff_isCliqueFree_of_complement] at *
  have : (G ⊓ edge v w)ᶜ = (Gᶜ ⊔ edge v w) := by ext a b
                                                 rw [compl_adj]
                                                 sorry
  rw [this]
  exact (CliqueFree.sup_edge h v w)



end IndependentSetFree

/-
section IndependentSetFreeOn
variable {s s₁ s₂ : Set α} {t : Finset α} {a b : α} {m n : ℕ}

/-- `G.IndependentSetFreeOn s n` means that `G` has no `n`-cliques contained in `s`. -/
def IndependentSetFreeOn (G : SimpleGraph α) (s : Set α) (n : ℕ) : Prop :=
  ∀ ⦃t⦄, ↑t ⊆ s → ¬G.IsNIndependentSet n t

theorem IndependentSetFreeOn.subset (hs : s₁ ⊆ s₂) (h₂ : G.IndependentSetFreeOn s₂ n) : G.IndependentSetFreeOn s₁ n :=
  fun _t hts => h₂ <| hts.trans hs

theorem IndependentSetFreeOn.mono (hmn : m ≤ n) (hG : G.IndependentSetFreeOn s m) : G.IndependentSetFreeOn s n := by
  rintro t hts ht
  obtain ⟨u, hut, hu⟩ := exists_subset_card_eq (hmn.trans ht.card_eq.ge)
  exact hG ((coe_subset.2 hut).trans hts) ⟨ht.clique.subset hut, hu⟩

theorem IndependentSetFreeOn.anti (hGH : G ≤ H) (hH : H.IndependentSetFreeOn s n) : G.IndependentSetFreeOn s n :=
  fun _t hts ht => hH hts <| ht.mono hGH

@[simp]
theorem cliqueFreeOn_empty : G.IndependentSetFreeOn ∅ n ↔ n ≠ 0 := by
  simp [IndependentSetFreeOn, Set.subset_empty_iff]

@[simp]
theorem cliqueFreeOn_singleton : G.IndependentSetFreeOn {a} n ↔ 1 < n := by
  obtain _ | _ | n := n <;>
    simp [IndependentSetFreeOn, isNIndependentSet_iff, ← subset_singleton_iff', (Nat.succ_ne_zero _).symm]

@[simp]
theorem cliqueFreeOn_univ : G.IndependentSetFreeOn Set.univ n ↔ G.IndependentSetFree n := by
  simp [IndependentSetFree, IndependentSetFreeOn]

protected theorem IndependentSetFree.cliqueFreeOn (hG : G.IndependentSetFree n) : G.IndependentSetFreeOn s n :=
  fun _t _ ↦ hG _

theorem cliqueFreeOn_of_card_lt {s : Finset α} (h : s.card < n) : G.IndependentSetFreeOn s n :=
  fun _t hts ht => h.not_le <| ht.2.symm.trans_le <| card_mono hts

-- TODO: Restate using `SimpleGraph.IndepSet` once we have it
@[simp]
theorem cliqueFreeOn_two : G.IndependentSetFreeOn s 2 ↔ s.Pairwise (G.Adjᶜ) := by
  classical
  refine ⟨fun h a ha b hb _ hab => h ?_ ⟨by simpa [hab.ne], card_pair hab.ne⟩, ?_⟩
  · push_cast
    exact Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩
  simp only [IndependentSetFreeOn, isNIndependentSet_iff, card_eq_two, coe_subset, not_and, not_exists]
  rintro h t hst ht a b hab rfl
  simp only [coe_insert, coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff] at hst
  refine h hst.1 hst.2 hab (ht ?_ ?_ hab) <;> simp

theorem IndependentSetFreeOn.of_succ (hs : G.IndependentSetFreeOn s (n + 1)) (ha : a ∈ s) :
    G.IndependentSetFreeOn (s ∩ G.neighborSet a) n := by
  classical
  refine fun t hts ht => hs ?_ (ht.insert fun b hb => (hts hb).2)
  push_cast
  exact Set.insert_subset_iff.2 ⟨ha, hts.trans Set.inter_subset_left⟩

end IndependentSetFreeOn
-/

/-! ### Set of independent sets -/


section IndependentSetSet

variable {n : ℕ} {a b c : α} {s : Finset α}

/-- The `n`-independentSets in a graph as a set. -/
def independentSetSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNIndependentSet n s }

variable {G H}

@[simp]
theorem mem_independentSetSet_iff : s ∈ G.independentSetSet n ↔ G.IsNIndependentSet n s :=
  Iff.rfl

@[simp]
theorem independentSetSet_eq_empty_iff : G.independentSetSet n = ∅ ↔ G.IndependentSetFree n := by
  simp_rw [IndependentSetFree, Set.eq_empty_iff_forall_not_mem, mem_independentSetSet_iff]

protected alias ⟨_, IndependentSetFree.independentSetSet⟩ := independentSetSet_eq_empty_iff

--@[mono] TODO probably not @mono?
theorem independentSetSet_anti (h : G ≤ H) : H.independentSetSet n ⊆ G.independentSetSet n :=
  fun _ ↦ IsNIndependentSet.anti h

theorem independentSetSet_anti' (h : G ≤ H) : H.independentSetSet ≤ G.independentSetSet :=
  fun _ ↦ independentSetSet_anti h

@[simp]
theorem independentSetSet_zero (G : SimpleGraph α) : G.independentSetSet 0 = {∅} :=
  Set.ext fun s => by simp

@[simp]
theorem independentSetSet_one (G : SimpleGraph α) : G.independentSetSet 1 = Set.range singleton :=
  Set.ext fun s => by simp [eq_comm]

@[simp]
theorem independentSetSet_top (hn : 1 < n) : (⊤ : SimpleGraph α).independentSetSet n = ∅ :=
  (independentSetFree_top hn).independentSetSet

-- TODO equality does not hold. is this interesting still?
@[simp]
theorem independentSetSet_map (hn : n ≠ 1) (G : SimpleGraph α) (f : α ↪ β) :
    map f '' G.independentSetSet n ⊆ (G.map f).independentSetSet n := by
  sorry


@[simp]
theorem independentSetSet_map_of_equiv (G : SimpleGraph α) (e : α ≃ β) (n : ℕ) :
    map e.toEmbedding '' G.independentSetSet n ⊆ (G.map e.toEmbedding).independentSetSet n := by
  obtain rfl | hn := eq_or_ne n 1
  · sorry
  · exact independentSetSet_map hn _ _

end IndependentSetSet

/-! ### Finset of independentSets -/
-- TODO dual proofs instead of replicating

section IndependentSetFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {a b c : α} {s : Finset α}

/-- The `n`-independentSets in a graph as a finset. -/
def independentSetFinset (n : ℕ) : Finset (Finset α) := {s | G.IsNIndependentSet n s}

variable {G} in
@[simp]
theorem mem_independentSetFinset_iff : s ∈ G.independentSetFinset n ↔ G.IsNIndependentSet n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _

@[simp, norm_cast]
theorem coe_independentSetFinset (n : ℕ) :
    (G.independentSetFinset n : Set (Finset α)) = G.independentSetSet n :=
  Set.ext fun _ ↦ mem_independentSetFinset_iff

variable {G}

@[simp]
theorem independentSetFinset_eq_empty_iff :
    G.independentSetFinset n = ∅ ↔ G.IndependentSetFree n := by
  simp_rw [IndependentSetFree, eq_empty_iff_forall_not_mem, mem_independentSetFinset_iff]

protected alias ⟨_, IndependentSetFree.independentSetFinset⟩ := independentSetFinset_eq_empty_iff

/-
theorem card_independentSetFinset_le : #(G.independentSetFinset n) ≤ (card α).choose n := by
  rw [← card_univ, ← card_powersetCard]
  refine card_mono fun s => ?_
  simpa [mem_powersetCard_univ] using IsNIndependentSet.card_eq

variable [DecidableRel H.Adj]

@[mono]
theorem independentSetFinset_anti (h : G ≤ H) :
    H.independentSetFinset n ⊆ G.independentSetFinset n :=
  monotone_filter_right _ fun _ ↦ IsNIndependentSet.anti h

variable [Fintype β] [DecidableEq β] (G)

@[simp]
theorem independentSetFinset_map (f : α ↪ β) (hn : n ≠ 1) :
    (G.map f).independentSetFinset n =
    (G.independentSetFinset n).map ⟨map f, Finset.map_injective _⟩ :=
  coe_injective <| by
    simp_rw [coe_independentSetFinset, independentSetSet_map hn, coe_map, coe_independentSetFinset,
    Embedding.coeFn_mk]

@[simp]
theorem independentSetFinset_map_of_equiv (e : α ≃ β) (n : ℕ) :
    (G.map e.toEmbedding).independentSetFinset n =
      (G.independentSetFinset n).map ⟨map e.toEmbedding, Finset.map_injective _⟩ :=
  coe_injective <| by push_cast; exact independentSetSet_map_of_equiv _ _ _
-/
end IndependentSetFinset

end SimpleGraph
