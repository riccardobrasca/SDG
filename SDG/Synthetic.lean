import Mathlib

namespace SDG

variable (R : Type*) [CommRing R] [Nontrivial R]

abbrev D := {(x : R) | x ^ 2 = 0}

instance : Zero (D R) where
  zero := ⟨0, by simp⟩

@[simp] lemma coe_zero : (↑(0 : D R) : R) = 0 := rfl

variable (one : ∀ g : D R → R, ∃! b, ∀ d, g d = g 0 + d * b)
include one

def α : R × R → (D R → R) := fun ⟨a, b⟩ ↦ (fun d ↦ a + d * b)

theorem consequence (b₁ b₂ : R) (h : ∀ d ∈ D R, d * b₁ = d * b₂) : b₁ = b₂ := by
  let g1 : D R → R := fun d ↦ d * b₁
  obtain ⟨b1, -, unique1⟩ := one g1
  let g2 : D R → R := fun d ↦ d * b₂
  obtain ⟨b2, -, unique2⟩ := one g2
  have h1 : b1 = b₁ := by
    specialize unique1 b₁
    simp at unique1
    rw [unique1]
    intro d hd
    simp [g1]
  have h2 : b2 = b₂ := by
    specialize unique2 b₂
    simp at unique2
    rw [unique2]
    intro b hb
    simp [g2]
  rw [← h1, ← h2]
  apply unique2
  intro d
  simp [g2, (h d d.2).symm, h1]

theorem Injective : Function.Injective (α R) := by
  intro ⟨a, b⟩ ⟨c, d⟩ h

  sorry

end SDG
