import SDG.IsKockLawvereone.Deriv

namespace SDG

open DualNumber Function

variable {R : Type*} [CommRing R]

def α : DualNumber R →ₐ[R] (D R → R) :=
  lift ⟨⟨Algebra.ofId _ _, (↑)⟩, coe_sq _, fun _ ↦ Commute.all _ _⟩

@[simp] lemma α_apply (a b : R) (d : D R) : α ⟨a, b⟩ d = a + b * d := by
  simp [α, lift_apply_apply, mul_comm]

variable [IsKockLawvereone R]

open IsKockLawvereone

lemma injective_α : Injective (α (R := R)) := by
  intro ⟨x, y⟩ ⟨z, t⟩ h
  have hxz := congr_fun h 0
  simp only [α_apply, coe_zero, mul_zero, add_zero] at hxz
  ext
  · assumption
  · refine cancel_d (fun d ↦ by simpa [hxz] using congr_fun h d)

lemma surjective_α : Surjective (α (R := R)) := by
  intro f
  obtain ⟨b, hb, unique⟩ := isKockLawvereone f
  use ⟨f 0, b⟩
  ext d
  simp [hb d]

lemma bijective_α : Bijective (α (R := R)) :=
  ⟨injective_α, surjective_α⟩

end SDG
