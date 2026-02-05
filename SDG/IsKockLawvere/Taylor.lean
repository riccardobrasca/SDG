import SDG.IsKockLawvere_one.Deriv
import SDG.Basic.FactorialInv

attribute [-instance] Fin.fintype

namespace SDG

open IsKockLawvere Nat

variable {R : Type*} [CommRing R] [IsKockLawvere R]

theorem taylor_two_aux [Invertible (2 : R)] (f : R → R) (x : R) (d₁ d₂ : D R) :
    letI δ : R := d₁ + d₂
    f (x + δ) = f x + ∂f x * δ + ∂∂f x * δ ^ 2 * ⅟2 :=
  calc f (x + (d₁ + d₂)) = f (x + d₁ + d₂) := by rw [add_assoc]
       _ = f (x + d₁) + ∂f (x + d₁) * d₂ := by rw [taylor_one f]
       _ = f x + ∂f x * d₁ + ∂f (x + d₁) * d₂ := by rw [taylor_one f]
       _ = f x + ∂f x * d₁ + (∂f x + ∂∂f x * d₁) * d₂ := by rw [taylor_one ∂f]
       _ = f x + (d₁ + d₂) * ∂f x + d₁ * d₂ * ∂∂f x := by ring
       _ = f x + (d₁ + d₂) * ∂f x + ((d₁ + d₂) ^ 2 * ⅟2) * ∂∂f x := by rw [D_add_sq_dvd_two]
       _ = _ := by ring

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
    specialize hB (d₁ + d₂) (mem_𝔻_of_mem_D_add_mem_D _ _)
    simp only [taylor_two_aux f x d₁ d₂, ← hB_deriv, add_assoc, D_add_sq, ← mul_assoc,
      Fin.isValue, add_right_inj] at hB
    rw [← hB, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_comm 2, mul_assoc, mul_assoc]
    simp
  rw [hB _ δ.2, add_assoc, hB_deriv]
  congr 2
  simp [((cancel_d (fun _ ↦ cancel_d (fun _ ↦ this _ _))).symm : ∂∂f x = B 1 * 2), mul_assoc,
    mul_comm ((δ : R) ^ 2)]

open Fin in
theorem taylor_k_aux (k : ℕ) [Divisible R] (f : R → R) (x : R) (d : Fin k → D R) :
    letI δ : R := ∑ n, d n
    f (x + δ) = ∑ n : Fin (k + 1), ∂^[n] f x * δ ^ (n : ℕ) * ⅟(n ! : R) :=
match k with
| 0 => by
  rw [zero_add, sum_univ_zero, add_zero, Fin.sum_univ_one, Fin.val_eq_zero,
    Function.iterate_zero, id_eq, pow_zero, mul_one, inv_zero_factorial, mul_one]
| k + 1 => by
  set δ : R := ∑ i : Fin k, (d i.succ) with hδ
  set δ₁ : R := ∑ n, d n with hδ₁
  have hδδ₁ : δ₁ = d 0 + δ := by simp [δ₁, δ, sum_univ_succ]
  calc f (x + δ₁) = f (x + ∑ n, (d n : R)) := by rfl
    _ = f (x + δ + d 0) := by rw [sum_univ_succ, add_comm (d 0 : R), ← add_assoc]
    _ = f (x + δ) + ∂f (x + δ) * d 0 := by rw [taylor_one f]
    _ = ∑ n : Fin (k + 1), ∂^[n] f x * δ ^ (n : ℕ) * ⅟(n ! : R) +
      (∑ n : Fin (k + 1), ∂^[n.succ] f x * δ ^ (n : ℕ) * ⅟(n ! : R)) * d 0 := by
      rw [taylor_k_aux k f, taylor_k_aux k ∂f]; rfl
  rw [Finset.sum_mul, ← sum_snoc_zero, ← sum_cons_zero (fun i ↦ _ * (d 0 : R)),
    ← Finset.sum_add_distrib]
  congr 1
  ext n
  rcases Decidable.eq_or_ne n 0 with rfl | h
  · simp
  rcases (Fin.eq_castSucc_or_eq_last n).symm with rfl | h
  · simp only [succ_eq_add_one, Fin.snoc_last, Fin.val_succ, Function.iterate_succ,
    Function.comp_apply, Fin.cons_last, Fin.val_last, zero_add, mul_assoc]
    congr 1
    rw [hδδ₁, mem_D_add_pow (d 0).2, nsmul_eq_mul, mem_D_sum_pow_succ, add_zero,
      mul_comm (↑(k + 1) : R), mul_assoc, mul_assoc, mul_comm (↑(k + 1) : R), mul_assoc,
      succ_mul_inv_factorial_succ R k]
    ring
  sorry
--    _ = ∑ n : Fin (k + 2), ∂^[n] f x * δ₁ ^ (n : ℕ) * ⅟(n ! : R) := by sorry

end SDG
