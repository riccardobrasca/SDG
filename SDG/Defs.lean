module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Derivation.Basic

public import SDG.Axiom.UniqueChoice
public import SDG.Axiom.Fin

@[expose] public section

-- things that have to be removed to avoid the axiom of choice
attribute [-instance] Fin.fintype

open BigOperators

namespace SDG

variable (R : Type*) [CommRing R]

abbrev D : Subsemigroup R where
 carrier := {(x : R) | x ^ 2 = 0}
 mul_mem' := fun hx hy ↦ by simp_all [mul_pow]

abbrev 𝔻 (k : ℕ) : Subsemigroup R where
 carrier := {(x : R) | x ^ (k + 1) = 0}
 mul_mem' := fun hx hy ↦ by simp_all [mul_pow]

lemma D_eq_𝔻_one : D R = 𝔻 R 1 := rfl

variable {R}

lemma D_mem_iff {x : R} : x ∈ D R ↔ x ^ 2 = 0 := by rfl

lemma 𝔻_mem_iff {x : R} {k : ℕ} : x ∈ 𝔻 R k ↔ x ^ (k + 1) = 0 := by rfl

variable (R) (k : ℕ)

lemma zero_mem_D : 0 ∈ D R := by
  simp

lemma zero_mem_𝔻 : 0 ∈ 𝔻 R k := by
  simp

instance : Zero (D R) where
  zero := ⟨0, zero_mem_D _⟩

instance : Zero (𝔻 R k) where
  zero := ⟨0, zero_mem_𝔻 _ _⟩

@[simp] lemma coe_zero : ((0 : D R) : R) = 0 := rfl

section IsKockLawvere

class IsKockLawvereone extends Nontrivial R where
  isKockLawvereone : ∀ g : D R → R, ∃! b, ∀ d, g d = g 0 + b * d

class IsKockLawvere (k : ℕ) extends Nontrivial R where
  isKockLawvere : ∀ g : 𝔻 R k → R, ∃! b : Fin k → R, ∀ d, g d = g 0 + ∑ i, b i * d ^ (i.val + 1)

variable [IsKockLawvereone R]

open IsKockLawvereone

variable {R}

noncomputable def derivFun (f : R → R) : R → R :=
  unique_choice_fun (fun x ↦ isKockLawvereone (fun d ↦ f (x + d)))

end IsKockLawvere

end SDG
