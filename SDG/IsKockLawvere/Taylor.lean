import SDG.IsKockLawvere_one.Deriv

attribute [-instance] Fin.fintype

namespace SDG

open IsKockLawvere

variable {R : Type*} [CommRing R] [IsKockLawvere R]
theorem taylor_two [Invertible (2 : R)] (f : R → R) (x : R) (δ : 𝔻 R 2) :
    f (x + δ) = f x + ∂f x * δ + ∂∂f x * δ ^ 2 * ⅟2 := by
  let g_x : 𝔻 R 2 → R := fun d ↦ f (x + d)
  obtain ⟨B, hB, hBunique⟩ := isKockLawvere 2 g_x
  simp only [coe_zero, add_zero, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, zero_add, pow_one, Nat.mod_succ, Nat.reduceAdd, Subtype.forall,
    Subsemigroup.mem_mk, Set.mem_setOf_eq, g_x] at hB
  have hB_deriv : ∂f x = B 0 := derivative_unique
    (fun d ↦ by simpa using hB _ (𝔻_le (by decide) d.2))
  have : ∀ (d₁ d₂ : D R), B 1 * 2 * d₁ * d₂ = ∂∂f x * d₁ * d₂ := by
    intro d₁ d₂
    specialize hB (d₁ + d₂) sorry
    rw [taylor_two_aux f x d₁ d₂, ← hB_deriv, add_assoc, D_add_sq] at hB
    simp only [← mul_assoc, Fin.isValue, add_right_inj] at hB
    rw [← hB, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    congr 1
    rw [mul_comm 2, mul_assoc, mul_assoc]
    simp
  have : B 1 * 2 = ∂∂f x := cancel_d (fun _ ↦ cancel_d (fun _ ↦ this _ _))
  sorry

end SDG
