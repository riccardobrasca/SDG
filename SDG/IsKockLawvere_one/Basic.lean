import SDG.Basic.D

namespace SDG

variable {R : Type*} [CommRing R] [IsKockLawvere_one R]

open IsKockLawvere_one

lemma cancel_d {b₁ b₂ : R} (h : ∀ (d : D R), b₁ * d = b₂ * d) : b₁ = b₂ := by
  obtain ⟨b1, -, unique1⟩ := isKockLawvere_one (b₁ * · : D R → R)
  obtain ⟨b2, -, unique2⟩ := isKockLawvere_one (b₂ * · : D R → R)
  rw [unique1 b₁ (fun d ↦ by simp), unique2 b₂ (fun d ↦ by simp)]
  exact unique2 _ (fun d ↦ by simp [(h d).symm, unique1 b₁ (fun d ↦ by simp)])

variable (R) in
lemma D_neq_zero : ¬(∀ d ∈ D R, d = 0) := by
  intro h
  obtain ⟨b, hb, hbunique⟩ := isKockLawvere_one (fun _ ↦ (0 : R))
  exact one_ne_zero <| hbunique 0 (by simp) ▸ hbunique 1 (fun ⟨d, hd⟩ ↦ by simp [h _ hd])

end SDG
