import data.finset.basic
import data.finset.card
import tactic

variables {α β : Type*}

lemma pigeonhole {S : finset α} {T : finset β} (hc : T.card < S.card)
  {f : α → β} (hf : ∀ a ∈ S, f a ∈ T) :
  ∃ (x y ∈ S), x ≠ y ∧ f x = f y :=
begin
  sorry
  -- formulate proof not relying on finset.card_le_card_of_inj_on
end

-- alternative proof by induction (not in book)?

-- strong_pigeonhole with ceil(S.card / T.card) elements

-- possibly avoid finsets by establishing connection range of ints?