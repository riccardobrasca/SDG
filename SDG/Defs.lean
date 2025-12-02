import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Derivation.Basic

import SDG.UniqueChoice

-- things that have to be removed to avoid the axiom of choice
attribute [-instance] Nat.instAtLeastTwoHAddOfNat

instance (n : ℕ) [NeZero n] : (n + 1).AtLeastTwo :=
  ⟨Nat.add_one_le_iff.2 <| Nat.succ_lt_succ <| Nat.pos_of_neZero n⟩

namespace SDG

variable (R : Type*) [CommRing R]

abbrev D : Subsemigroup R where
 carrier := {(x : R) | x ^ 2 = 0}
 mul_mem' := fun hx hy ↦ by simp_all [mul_pow]

variable {R}

lemma D_mem_iff {x : R} : x ∈ D R ↔ x ^ 2 = 0 := by rfl

variable (R)

lemma zero_mem_D : 0 ∈ D R := by
  rw [D_mem_iff, sq, mul_zero]

instance : Zero (D R) where
  zero := ⟨0, zero_mem_D _⟩

@[simp] lemma coe_zero : ((0 : D R) : R) = 0 := rfl

section IsKockLawvere

class IsKockLawvere extends Nontrivial R where
  isKockLawvere : ∀ g : D R → R, ∃! b, ∀ d, g d = g 0 + d * b

variable [IsKockLawvere R]

end IsKockLawvere

end SDG
