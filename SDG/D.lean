import SDG.Defs

namespace SDG

open DualNumber Function

variable {R : Type*} [CommRing R]

lemma D_mul_mem {x : R} (y : R) (hx : x ∈ D R) : y * x ∈ D R := by
  simp [mul_pow, D_mem_iff.1 hx]

lemma D_mem_mul {x : R} (y : R) (hx : x ∈ D R) : x * y ∈ D R := by
  simp [mul_pow, D_mem_iff.1 hx]

@[simp] lemma D_sq (x : D R) : (x : R) ^ 2 = 0 :=
  x.2

lemma D_add_sq (d₁ d₂ : D R) : (d₁ + d₂ : R) ^ 2 = 2 * d₁ * d₂ :=
  calc (d₁ + d₂ : R) ^ 2 = d₁ ^ 2 + d₂ ^ 2 + (2 : ℕ) * d₁ * d₂ := by ring
                       _ = _ := by simp

lemma D_add_sq_dvd_two [Invertible (2 : R)] (d₁ d₂ : D R) :
    (d₁ + d₂ : R) ^ 2 * ⅟2 = d₁ * d₂ := by
  calc (d₁ + d₂ : R) ^ 2 * ⅟2 = (2 * d₁ * d₂) * ⅟2 := by rw [D_add_sq]
    _ = ((2 : ℕ) * d₁ * d₂) * ⅟2 := rfl
    _ = d₁ * d₂ * ((2 : ℕ) * ⅟2) := by ring
    _ = d₁ * d₂ := by simp

variable (R) in
lemma coe_sq : ((↑) : D R → R) * (↑) = 0 := by
  ext d
  simpa only [← pow_two, Pi.zero_apply] using d.2

end SDG
