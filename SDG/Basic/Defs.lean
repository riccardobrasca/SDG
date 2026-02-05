import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Group.Subsemigroup.Defs

import SDG.Axiom.UniqueChoice
import SDG.Axiom.Fin

open BigOperators

namespace SDG

variable (R : Type*) [CommRing R]

abbrev 𝔻 (k : ℕ) : Subsemigroup R where
 carrier := {(x : R) | x ^ (k + 1) = 0}
 mul_mem' := fun hx hy ↦ by simp_all [mul_pow]

abbrev D := 𝔻 R 1

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

@[simp] lemma coe_zero (k : ℕ) : ((0 : 𝔻 R k) : R) = 0 := rfl

section IsKockLawvere

class IsKockLawvere_one extends Nontrivial R where
  isKockLawvere_one : ∀ g : D R → R, ∃! b, ∀ d, g d = g 0 + b * d

class IsKockLawvere extends Nontrivial R where
  isKockLawvere : ∀ k, ∀ g : 𝔻 R k → R,
    ∃! b : Fin k → R, ∀ d, g d = g 0 + ∑ i, b i * d ^ (i.val + 1)

instance [IsKockLawvere R] : IsKockLawvere_one R where
  isKockLawvere_one := fun g ↦ by
    obtain ⟨b, hb, hbunique⟩ := IsKockLawvere.isKockLawvere 1 g
    refine ⟨b 0, by simpa using hb, fun b' hb' ↦ ?_⟩
    specialize hbunique (fun _ ↦ b')
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero, zero_add,
      pow_one, Finset.sum_const, Finset.card_singleton, one_smul, Subtype.forall,
      Subsemigroup.mem_mk, Nat.reduceAdd, Set.mem_setOf_eq] at hbunique
    rw [← hbunique (by simpa using hb')]

variable [IsKockLawvere_one R]

open IsKockLawvere_one

variable {R}

noncomputable def derivFun (f : R → R) : R → R :=
  unique_choice_fun (fun x ↦ isKockLawvere_one (fun d ↦ f (x + d)))

end IsKockLawvere

end SDG
