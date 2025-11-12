import SDG.Linters.choice
import Mathlib.Data.Subtype

variable {α : Type*} {P : α → Prop}

axiom axiom_unique_choice (h : ∃! (_ : α), True) : α

lemma unique_subtype (h : ∃! (a : α), P a) : ∃! (_ : {a // P a}), True := by
  obtain ⟨a, h1, h2⟩ := h
  exact ⟨⟨a, h1⟩, by trivial, fun y _ ↦ Subtype.ext (h2 _ y.2)⟩

noncomputable def unique_choice (h : ∃! (a : α), P a) : α :=
  (axiom_unique_choice (unique_subtype h)).val

lemma unique_choice_spec (h : ∃! (a : α), P a) : P (unique_choice h) :=
  Subtype.prop _
