import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Set.CoeSort
import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.Coe
import Mathlib.Tactic.Use

namespace SDG

variable (R : Type*) [CommRing R]

abbrev D := {(x : R) | x ^ 2 = 0}

lemma zero_mem_D : (0 : R) ∈ D R := by
  show 0 ^ 2 = 0
  rw [sq, mul_zero]

instance : Zero (D R) where
  zero := ⟨0, zero_mem_D _⟩

@[simp] lemma coe_zero : ((0 : D R) : R) = 0 := rfl

class IsKockLawvere extends Nontrivial R where
  isKockLawvere : ∀ g : D R → R, ∃! b, ∀ d, g d = g 0 + d * b

def α : R × R → (D R → R) := fun ⟨a, b⟩ ↦ (fun d ↦ a + d * b)

@[simp] lemma α_apply (a b : R) (d : D R) : α R ⟨a, b⟩ d = a + d * b := rfl

variable [IsKockLawvere R] {R}

theorem exists_derivative (g : D R → R) : ∃! b, ∀ d, g d = g 0 + d * b :=
  IsKockLawvere.isKockLawvere g

theorem cancel_d (b₁ b₂ : R) (h : ∀ d ∈ D R, d * b₁ = d * b₂) : b₁ = b₂ := by
  let g1 : D R → R := fun d ↦ d * b₁
  obtain ⟨b1, -, unique1⟩ := exists_derivative g1
  let g2 : D R → R := fun d ↦ d * b₂
  obtain ⟨b2, -, unique2⟩ := exists_derivative g2
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

theorem injective_α : Function.Injective (α R) := by
  intro ⟨x, y⟩ ⟨z, t⟩ h
  have hxz := congr_fun h 0
  simp at hxz
  ext
  · assumption
  · simp
    replace h : ∀ d ∈ D R, d * y = d * t := by
      intro d hd
      have := congr_fun h ⟨d, hd⟩
      simpa [hxz]
    exact cancel_d _ _ h

theorem surjective_α : Function.Surjective (α R) := by
  intro f
  obtain ⟨b, hb, unique⟩ := exists_derivative f
  use ⟨f 0, b⟩
  ext d
  simp [hb d]

theorem bijective_α : Function.Bijective (α R) :=
  ⟨injective_α, surjective_α⟩

end SDG
