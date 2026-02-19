import Mathlib.Logic.Function.Basic

import SDG.Linters.choice

namespace SDG.Function

variable {α β : Type*} [DecidableEq α] (f : α → β) (a : α)

@[simp]
lemma update_eq_self : Function.update f a (f a) = f := by
  ext x
  by_cases hx : x = a
  · rw [hx, Function.update_self]
  · rw [Function.update_of_ne hx]

lemma update_update_comm (f : α → β) {a₁ a₂ : α} (h : a₁ ≠ a₂) (b₁ b₂ : β) :
    Function.update (Function.update f a₁ b₁) a₂ b₂ =
      Function.update (Function.update f a₂ b₂) a₁ b₁ := by
  ext a
  rcases Decidable.eq_or_ne a a₁ with rfl | h
  · simp [Function.update, h]
  · by_cases h' : a = a₂ <;>
    simp_all [Function.update]

end SDG.Function
