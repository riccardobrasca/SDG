import SDG.Linters.choice
import Mathlib.Data.Subtype

variable {α : Type*} {P : α → Prop}

/-!
# The axiom of unique choice.

We add in this file the axiom of unique choice, which is a weakening of the axiom of choice.

Given a type `α` such that there exists a unique element `a : α`, the axiom of unique choice allows
to select this element. It holds in set theory without any additional axiom, but it is not provable
in Lean's type theory.

## The axiom

* `axiom_unique_choice`: given a type `α` such that `h : ∃! (_ : α), True`, then
  `axiom_unique_choice h` gives the element.

## Main definition

* `unique_choice`: given a property `P : α → Prop` such that `h : ∃! a, P a`, then
  `unique_choice h` gives the unique `a : α` such that `P a`.

## Main lemmas

* `unique_choice_spec`: given `h : ∃! a, P a`, then `P (unique_choice h)` holds.
* `unique_choice_unique`: given `h : ∃! a, P a`, if `a : α` is such that `P a`, then
  `unique_choice h = a`.
-/

/-- Given a type `α` such that `h : ∃! (_ : α), True`, then `axiom_unique_choice h` gives the
element. -/
axiom axiom_unique_choice (h : ∃! (_ : α), True) : α

lemma unique_subtype (h : ∃! a, P a) : ∃! (_ : {a // P a}), True := by
  obtain ⟨a, h1, h2⟩ := h
  exact ⟨⟨a, h1⟩, by trivial, fun y _ ↦ Subtype.ext (h2 _ y.2)⟩

/-- Given a property `P : α → Prop` such that `h : ∃! a, P a`, then `unique_choice h` gives the
unique `a : α` such that `P a`. -/
noncomputable def unique_choice (h : ∃! a, P a) : α :=
  (axiom_unique_choice (unique_subtype h)).val

/-- Given `h : ∃! a, P a`, then `P (unique_choice h)` holds. -/
lemma unique_choice_spec (h : ∃! a, P a) : P (unique_choice h) :=
  Subtype.prop _

/-- Given `h : ∃! a, P a`, if `a : α` is such that `P a`, then `unique_choice h = a`. -/
lemma unique_choice_unique (h : ∃! a, P a) {a : α} (ha : P a) : unique_choice h = a :=
  h.unique (unique_choice_spec h) ha
