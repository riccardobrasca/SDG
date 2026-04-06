module

public import SDG.Linters.choice
public import Mathlib.Data.Subtype

variable {α β : Type*} {P : α → Prop}

/-!
# The axiom of unique choice.

We add in this file the axiom of unique choice, which is a weakening of the axiom of choice.

Given a type `α` such that there exists a unique element `a : α`, the axiom of unique choice allows
to select this element.

The only version we will actually use is the fact that, given a property
`P : α → β → Prop` such that
`(h : ∀ a, ∃! b, P a b)`, there is a function `unique_choice_fun h : α → β` such that
`∀ a, P a (unique_choice_fun h a)` (see `unique_choice_fun` and `unique_choice_fun_spec`). The
construction of `unique_choice_fun h` can be done unconditionally in set theory, but in
Lean's type theory we need an additional axiom.

## The axiom

* `axiom_unique_choice`: given a type `α` such that `h : ∃! (_ : α), True`, then
  `axiom_unique_choice h` gives the element.

## Main definitions

* `unique_choice`: given a property `P : α → Prop` such that `h : ∃! a, P a`, then
  `unique_choice h` gives the unique `a : α` such that `P a`.
* `unique_choice_fun`: given a property `P : α → β → Prop` such that for all `a : α`, there exists a
    unique `b : β` with `P a b`, then `unique_choice_fun h` gives a function `α → β` selecting this
    unique `b` for each `a`.

## Main lemmas

* `unique_choice_fun_spec`: given a property `P : α → β → Prop` such that for all `a : α`, there
    exists a unique `b : β` with `P a b`, then for each `a : α`, `P a (unique_choice_fun h a)`
    holds.
* `unique_choice_fun_unique`: given a property `P : α → β → Prop` such that for all `a : α`, there
    exists a unique `b : β` with `P a b`, then for each `a : α`, if `b : β` satisfies `P a b`, then
    `unique_choice_fun h a = b`.
-/

/-- Given a type `α` such that `h : ∃! (_ : α), True`, then `axiom_unique_choice h` gives the
element. -/
axiom axiom_unique_choice (h : ∃! (_ : α), True) : α

lemma unique_subtype (h : ∃! a, P a) : ∃! (_ : {a // P a}), True := by
  obtain ⟨a, h1, h2⟩ := h
  exact ⟨⟨a, h1⟩, trivial, fun y _ ↦ Subtype.ext (h2 _ y.2)⟩

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

public section

/-- Given a property `P : α → β → Prop` such that for all `a : α`, there exists a unique `b : β`
with `P a b`, then `unique_choice_fun h` gives a function `α → β` selecting this unique `b` for
each `a`. -/
noncomputable def unique_choice_fun {P : α → β → Prop} (h : ∀ a, ∃! b, P a b) : α → β :=
  fun a ↦ unique_choice (h a)

/-- Given a property `P : α → β → Prop` such that for all `a : α`, there exists a unique `b : β`
with `P a b`, then for each `a : α`, `P a (unique_choice_fun h a)` holds. -/
lemma unique_choice_fun_spec {P : α → β → Prop} (h : ∀ a, ∃! b, P a b) (a : α) :
    P a (unique_choice_fun h a) :=
  unique_choice_spec (h a)

/-- Given a property `P : α → β → Prop` such that for all `a : α`, there exists a unique `b : β`
with `P a b`, then for each `a : α`, if `b : β` satisfies `P a b`, then
`unique_choice_fun h a = b`. -/
lemma unique_choice_fun_unique {P : α → β → Prop} (h : ∀ a, ∃! b, P a b) {a : α} {b : β}
    (hb : P a b) : unique_choice_fun h a = b :=
  unique_choice_unique (h a) hb

end
