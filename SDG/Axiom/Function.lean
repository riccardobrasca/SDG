import Mathlib.Logic.Function.Basic

import SDG.Linters.choice

open Function
namespace SDG.Function

variable {α β : Type*} [DecidableEq α] (f : α → β) (a : α)

@[simp]
lemma update_eq_self : update f a (f a) = f := by
  ext x
  by_cases hx : x = a
  · rw [hx, update_self]
  · rw [update_of_ne hx]

lemma update_update_comm (f : α → β) {a₁ a₂ : α} (h : a₁ ≠ a₂) (b₁ b₂ : β) :
    update (update f a₁ b₁) a₂ b₂ = update (update f a₂ b₂) a₁ b₁ := by
  ext a
  rcases Decidable.eq_or_ne a a₁ with rfl | h
  · simp [update, h]
  · by_cases h' : a = a₂ <;>
    simp_all [update]

end SDG.Function
