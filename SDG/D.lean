import SDG.Defs

-- things that have to be removed to avoid the axiom of choice
attribute [-instance] Subsemigroup.instCompleteLattice
namespace SDG

open DualNumber Function

variable {R : Type*} [CommRing R] {k : ℕ}

lemma D_mul_mem {x : R} (y : R) (hx : x ∈ D R) : y * x ∈ D R := by
  simp [mul_pow, D_mem_iff.1 hx]

lemma D_mem_mul {x : R} (y : R) (hx : x ∈ D R) : x * y ∈ D R := by
  simp [mul_pow, D_mem_iff.1 hx]

lemma 𝔻_mul_mem {x : R} (y : R) (hx : x ∈ 𝔻 R k) : y * x ∈ 𝔻 R k := by
  simp [mul_pow, 𝔻_mem_iff.1 hx]

lemma 𝔻_mem_mul {x : R} (y : R) (hx : x ∈ 𝔻 R k) : x * y ∈ 𝔻 R k := by
  simp [mul_pow, 𝔻_mem_iff.1 hx]

@[simp] lemma D_sq (x : D R) : (x : R) ^ 2 = 0 :=
  x.2

@[simp] lemma 𝔻_pow (x : 𝔻 R k) : (x : R) ^ (k + 1) = 0 :=
  x.2

lemma 𝔻_le {k ℓ : ℕ} (h : k ≤ ℓ) : (𝔻 R k) ≤ 𝔻 R ℓ := by
  refine fun x hx ↦ 𝔻_mem_iff.2 ?_
  have hx' : x ^ (k + 1) = 0 := 𝔻_mem_iff.1 hx
  have hsum : k + 1 + (ℓ - k) = ℓ + 1 := by
      have h' : k + (ℓ - k) = ℓ := Nat.add_sub_of_le h
      calc
        k + 1 + (ℓ - k) = (k + (ℓ - k)) + 1 := by ac_rfl
        _ = ℓ + 1 := by simp [h']
  calc
    x ^ (ℓ + 1) = x ^ (k + 1 + (ℓ - k)) := by simp [hsum]
    _ = x ^ (k + 1) * x ^ (ℓ - k) := by simp [pow_add]
    _ = 0 := by simp [hx']

lemma D_add_sq (d₁ d₂ : D R) : (d₁ + d₂ : R) ^ 2 = 2 * d₁ * d₂ :=
  calc (d₁ + d₂ : R) ^ 2 = d₁ ^ 2 + d₂ ^ 2 + 2 * d₁ * d₂ := by ring
                       _ = _ := by simp

lemma D_add_sq_dvd_two [Invertible (2 : R)] (d₁ d₂ : D R) :
    (d₁ + d₂ : R) ^ 2 * ⅟2 = d₁ * d₂ := by
  calc (d₁ + d₂ : R) ^ 2 * ⅟2 = d₁ * d₂ * 2 * ⅟2 := by rw [D_add_sq]; ring
    _ = d₁ * d₂ := by simp

variable (R) in
lemma coe_sq : ((↑) : D R → R) * (↑) = 0 := by
  ext d
  simpa only [← pow_two, Pi.zero_apply] using d.2

variable (R) (k : ℕ) in
lemma coe_pow : ((↑) : 𝔻 R k → R) ^ (k + 1) = 0 := by
  ext d
  simp

end SDG
