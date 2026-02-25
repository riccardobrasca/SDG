import SDG.IsKockLawvere_one.Deriv
import SDG.Basic.FactorialInv

open Fin
namespace SDG

open IsKockLawvere Nat

variable {R : Type*} [CommRing R] [IsKockLawvere R]

theorem taylor_two [Invertible (2 : R)] (f : R → R) (x : R) (δ : 𝔻 R 2) :
    f (x + δ) = f x + ∂f x * δ + ∂∂f x * δ ^ 2 * ⅟2 := by
  let g_x : 𝔻 R 2 → R := fun d ↦ f (x + d)
  obtain ⟨b, hb, -⟩ := isKockLawvere 2 g_x
  simp only [coe_zero, add_zero, sum_univ_two, Fin.isValue, coe_ofNat_eq_mod, Nat.zero_mod,
    zero_add, pow_one, Nat.mod_succ, Nat.reduceAdd, Subtype.forall, Subsemigroup.mem_mk,
    Set.mem_setOf_eq, g_x] at hb
  have hB_deriv : ∂f x = b 0 := derivative_unique
    (fun d ↦ by simpa using hb _ (𝔻_le (by decide) d.2))
  have : ∀ (d₁ d₂ : D R), b 1 * 2 * d₁ * d₂ = ∂∂f x * d₁ * d₂ := by
    intro d₁ d₂
    specialize hb (d₁ + d₂) (mem_𝔻_of_mem_D_add_mem_D _ _)
    rw [taylor_two_aux f x d₁ d₂, ← hB_deriv, add_assoc, D_add_sq, ← mul_assoc, ← mul_assoc,
      ← mul_assoc, ← mul_assoc, add_right_inj, add_right_inj] at hb
    rw [← hb, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_comm 2, mul_assoc, mul_assoc]
    simp
  rw [hb _ δ.2, add_assoc, hB_deriv]
  congr 2
  simp [((cancel_d (fun _ ↦ cancel_d (fun _ ↦ this _ _))).symm : ∂∂f x = b 1 * 2), mul_assoc,
    mul_comm ((δ : R) ^ 2)]

set_option backward.isDefEq.respectTransparency false in
theorem taylor_k_aux {k : ℕ} [Divisible R] (f : R → R) (x : R) (d : Fin k → D R) :
    letI δ : R := ∑ n, d n
    f (x + δ) = ∑ n : Fin (k + 1), ∂^[n] f x * δ ^ (n : ℕ) * ⅟(n ! : R) :=
match k with
| 0 => by
  rw [zero_add, sum_univ_zero, add_zero, sum_univ_one, val_eq_zero,
    Function.iterate_zero, id_eq, pow_zero, mul_one, inv_factorial_zero, mul_one]
| k + 1 => by
  set δ : R := ∑ i : Fin k, (d i.succ) with hδ
  set Δ : R := ∑ n, d n with hΔ
  have hδΔ : Δ = d 0 + δ := by simp [Δ, δ, sum_univ_succ]
  calc f (x + Δ) = f (x + ∑ n, (d n : R)) := by rfl
    _ = f (x + δ + d 0) := by rw [sum_univ_succ, add_comm (d 0 : R), ← add_assoc]
    _ = f (x + δ) + ∂f (x + δ) * d 0 := by rw [taylor_one f]
    _ = ∑ n : Fin (k + 1), ∂^[n] f x * δ ^ (n : ℕ) * ⅟(n ! : R) +
      (∑ n : Fin (k + 1), ∂^[n.succ] f x * δ ^ (n : ℕ) * ⅟(n ! : R)) * d 0 := by
      rw [taylor_k_aux f, taylor_k_aux ∂f]; rfl
  rw [Finset.sum_mul, ← sum_snoc_zero, ← sum_cons_zero (fun i ↦ _ * (d 0 : R)),
    ← Finset.sum_add_distrib]
  congr 1
  ext n
  rcases Decidable.eq_or_ne n 0 with rfl | h
  · simp
  rcases (eq_castSucc_or_eq_last n).symm with rfl | ⟨m', rfl⟩
  · simp only [succ_eq_add_one, snoc_last, val_succ, Function.iterate_succ,
    Function.comp_apply, cons_last, val_last, zero_add, mul_assoc]
    rw [hδΔ, mem_D_add_pow, mem_D_sum_pow_succ, add_zero,
      mul_comm (↑(k + 1) : R), mul_assoc, mul_assoc, mul_comm (↑(k + 1) : R), mul_assoc,
      succ_mul_inv_factorial_succ]
    ring
  obtain ⟨m, hm⟩ := eq_succ_of_ne_zero h
  simp only [succ_eq_add_one, snoc_castSucc, val_succ, Function.iterate_succ,
    Function.comp_apply, val_castSucc]
  simp only [hm, cons_succ, mul_assoc, ← val_castSucc m', ← Function.iterate_succ_apply,
    val_succ, ← mul_add]
  rw [hδΔ, mem_D_add_pow, pow_succ, mul_comm _ (δ ^ m.1), ← mul_add, mul_assoc, ← mul_add,
    mul_assoc, add_mul, add_comm _ (δ * _), mul_comm (↑(m.1 + 1) : R), mul_assoc,
    mul_comm (↑(m.1 + 1) : R), succ_mul_inv_factorial_succ]
  ring

theorem taylor_k_aux_zero (k : ℕ) (f : R → R) (x : R) (B : Fin (k + 1) → R)
    (hB : ∀ (d : (𝔻 R (k + 1))), f (x + d) = f x + ∑ i, B i * d ^ (i.1 + 1)) : B 0 = ∂f x := by
  refine (derivative_unique (fun d ↦ ?_)).symm
  rw [hB ⟨d, 𝔻_le (Nat.le_add_left ..) d.2⟩, add_right_inj, sum_univ_succ]
  convert add_zero _
  · refine Finset.sum_eq_zero (fun i _ ↦ ?_)
    convert mul_zero _
    exact 𝔻_le (Nat.le_add_left ..) d.2
  · simp

theorem taylor_k_aux' [Divisible R] (k : ℕ) (f : R → R) (x : R) (b : Fin (k + 1) → R)
    (hb : ∀ (d : (𝔻 R (k + 1))), f (x + d) = f x + ∑ i, b i * d ^ (i.1 + 1)) :
    ∀ (i : Fin (k + 1)), b i * i.succ ! = ∂^[i.succ] f x
| 0 => by
  rw [taylor_k_aux_zero k f x b hb]
  simp
| (Fin.mk (Nat.succ n) hn) => by
  refine cancel_d_fun (n + 2) (fun d ↦ ?_)
  set δ := ∑ n, (d n).1 with hδ_def
  have hb_deriv := taylor_k_aux_zero k f x b hb
  have Hb := hb ⟨δ, 𝔻_le (succ_le_of_lt hn) (mem_D_sum_pow_succ d)⟩
  rw [taylor_k_aux f, ← hδ_def, sum_univ_succ (n := n + 2), val_zero, Function.iterate_zero,
    id_eq, pow_zero, mul_one, inv_factorial_zero, mul_one, add_right_inj, sum_univ_succ
      (n := k), val_zero, zero_add, pow_one, hb_deriv, sum_univ_succ (n := n + 1),
      val_succ, val_zero, zero_add, Function.iterate_one, pow_one, inv_factorial_one,
      mul_one, add_right_inj, sum_castLe_of_eq_zero (le_of_lt_succ hn) _
      (fun _ h ↦ by convert mul_zero _; exact 𝔻_le (succ_le_succ h) (mem_D_sum_pow_succ d)),
      sum_univ_succAbove _ (last n), sum_univ_succAbove _ (last n)] at Hb
  replace Hb := (eq_iff_eq_of_add_eq_add Hb).mpr ?_
  · simp only [succ_eq_add_one, succ_mk, Function.iterate_succ, Function.comp_apply]
    simp only [succ_last, succ_eq_add_one, val_last, Function.iterate_succ,
      Function.comp_apply, val_succ, val_castLE] at Hb
    rw [mem_D_sum_pow d, mul_comm ((n + 2)! : R), mul_assoc, mul_assoc, mul_invOf_self',
      mul_one] at Hb
    rw [Hb, mul_comm (∏ i, (d i).1)]
    exact mul_assoc ..
  · congr
    ext j
    have := taylor_k_aux' k f x b hb ⟨j.succ, lt_trans j.succ.isLt hn⟩
    simp only [succAbove_last, val_succ, val_castSucc, Function.iterate_succ,
      Function.comp_apply, succ_eq_add_one, castLE_castSucc, val_castLE]
    simp only [val_succ, succ_mk, Function.iterate_succ, Function.comp_apply] at this
    rw [← this, mul_assoc, mul_assoc, mul_comm (δ ^ (j.1 + 1 + 1))]
    simp
    rfl
decreasing_by rw [Fin.sizeOf, Fin.sizeOf, Nat.succ_lt_succ_iff]
              exact succ_le_succ j.2

theorem taylor_k [Divisible R] (f : R → R) (x : R) : ∀ (k : ℕ) (δ : 𝔻 R k),
    f (x + δ) = ∑ n : Fin (k + 1), ∂^[n] f x * δ ^ (n : ℕ) * ⅟(n ! : R)
| 0 => by simp [-factorial_zero]
| k + 1 => fun Δ ↦ by
  let g_x : 𝔻 R (k + 1) → R := fun d ↦ f (x + d)
  obtain ⟨b, hb, -⟩ := isKockLawvere (k + 1) g_x
  simp only [coe_zero, add_zero, Subtype.forall, Subsemigroup.mem_mk, Set.mem_setOf_eq, g_x] at hb
  rw [hb _ Δ.2, sum_univ_succ (n := k + 1), val_zero, Function.iterate_zero, id_eq,
    pow_zero, mul_one, inv_factorial_zero, mul_one, add_right_inj]
  congr
  ext i
  rw [← taylor_k_aux' k f x b (fun d ↦ hb _ d.2) i, mul_assoc, mul_assoc, mul_comm ((i.succ)! : R)]
  simp

end SDG
