import Mathlib.RingTheory.Derivation.Basic

import SDG.Basic.D
import SDG.IsKockLawvere_one.Basic
import SDG.Axiom.Function

open Function SDG.IsKockLawvere_one SDG.Function

namespace SDG

variable {R : Type*} [CommRing R]

section IsKockLawvere_one

variable [IsKockLawvere_one R] {n : ℕ} (i : Fin n) (f : (Fin n → R) → R) {x : Fin n → R}

lemma partial_deriv_propr : ∀ (x : Fin n → R), ∃! b, ∀ (d : D R),
    f (update x i (x i + d)) = f x + b * d := by
  intro x
  let g : D R → R := fun d ↦ f (update x i (x i + d))
  obtain ⟨b, hb, hbunique⟩ := isKockLawvere_one g
  refine ⟨b, fun d ↦ ?_, fun b₁ hb₁ ↦ hbunique b₁ (fun d ↦ ?_)⟩
  · convert hb d
    rw [coe_zero, add_zero, SDG.Function.update_eq_self]
  · convert hb₁ d
    rw [coe_zero, add_zero, SDG.Function.update_eq_self]

noncomputable def partial_derivFun : (Fin n → R) → R :=
  unique_choice_fun (partial_deriv_propr i f)

lemma partial_derivFun_spec (d : D R) :
    f (update x i (x i + d)) = f x + (partial_derivFun i f x) * d :=
  unique_choice_fun_spec (partial_deriv_propr i f) ..

variable {f} in
lemma partial_derivFun_unique {b : R} (hb : ∀ (d : D R), f (update x i (x i + d)) = f x + b * d) :
      partial_derivFun i f x = b :=
  unique_choice_fun_unique (partial_deriv_propr i f) hb

noncomputable def partial_deriv : Derivation R ((Fin n → R) → R) ((Fin n → R) → R) where
  toFun := partial_derivFun i
  map_add' := fun f g ↦ funext fun x ↦ partial_derivFun_unique i <| fun d ↦
    calc _ = f (update x i (x i + d)) + g (update x i (x i + d)) := by simp
         _ = (f x + partial_derivFun i f x * d) + (g x + partial_derivFun i g x * d) := by
              simp only [partial_derivFun_spec]
         _ = (f + g) x + (partial_derivFun i f + partial_derivFun i g) x * d := by simp; ring
  map_smul' := fun r f ↦ funext fun x ↦ partial_derivFun_unique i <| fun d ↦
    calc (r • f) (update x i (x i + d)) = r * f (update x i (x i + d)) := by simp
      _ = r * (f x + partial_derivFun i f x * d) := by rw [partial_derivFun_spec i f]
      _ = (r • f) x + (r * partial_derivFun i f x) * d := by simp; ring
  map_one_eq_zero' := funext fun _ ↦ partial_derivFun_unique i (by simp)
  leibniz' := fun f g ↦ funext fun x ↦ partial_derivFun_unique i <| fun d ↦
    calc f (update x i (x i + d)) * g (update x i (x i + d))
          = (f x + partial_derivFun i f x * d) * (g x + partial_derivFun i g x * d) := by
              simp only [partial_derivFun_spec]
         _ = f x * g x + (f x * partial_derivFun i g x + partial_derivFun i f x * g x) * d +
            d ^ 2 * partial_derivFun i f x * partial_derivFun i g x := by ring
         _ = _ := by simp; ring

instance : FunLike (Derivation R ((Fin n → R) → R) ((Fin n → R) → R))
    ((Fin n → R) → R) ((Fin n → R) → R) where
  coe D := D.toFun
  coe_injective' := DFunLike.coe_injective

notation3:max "∂[" i "]" f:max => partial_deriv i f

variable (x)

lemma partial_taylor_one (d : D R) : f (update x i (x i + d)) = f x + ∂[i]f x * d :=
  partial_derivFun_spec ..

variable {f x} in
lemma partial_derivative_unique {b : R} (hb : ∀ (d : D R), f (update x i (x i + d)) = f x + b * d) :
    ∂[i]f x = b :=
  partial_derivFun_unique i  hb

@[simp]
theorem partial_deriv_const (r : R) : ∂[i](fun _ ↦ r) = 0 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp)

theorem partial_deriv_mul (f g : (Fin n → R) → R) :
    ∂[i](f * g) = ∂[i]f * g + f * ∂[i]g := by
  simp; ring

theorem partial_deriv_comm (i j : Fin n) : ∂[i](∂[j]f) x = ∂[j](∂[i]f) x := by
  by_cases H : i = j
  · simp [H]
  refine cancel_d (fun d₁ ↦ cancel_d (fun d₂ ↦ ?_))
  let x₁ := update x i (x i + d₁); let x₂ := update x j (x j + d₂)
  have hx₁j : x₁ j = x j := by rcases Decidable.eq_or_ne j i <;> simp_all [x₁]
  have hx₂i : x₂ i = x i := by rcases Decidable.eq_or_ne j i <;> simp_all [x₂]
  have h₁ : f (update x₁ j (x j + d₂)) = f x₁ + ∂[j]f x₁ * d₂ := hx₁j ▸ partial_taylor_one ..
  have h₂ : f (update x₂ i (x i + d₁)) = f x₂ + ∂[i]f x₂ * d₁ := hx₂i ▸ partial_taylor_one ..
  have hEq : f x₁ + ∂[j]f x₁ * d₂ = f x₂ + ∂[i]f x₂ * d₁ := by rw [← h₁, update_update_comm x H, h₂]
  rw [partial_taylor_one i f, partial_taylor_one j f, partial_taylor_one i ∂[j]f,
    partial_taylor_one j ∂[i]f] at hEq
  ring_nf at hEq
  simpa [mul_assoc, mul_comm, mul_left_comm] using hEq

@[simp]
theorem partial_deriv_proj_self (i : Fin n) : ∂[i](fun x : Fin n → R ↦ x i) = 1 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp)

@[simp]
theorem partial_deriv_proj_ne {i j : Fin n} (hij : i ≠ j) : ∂[i](fun x : Fin n → R ↦ x j) = 0 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp [hij.symm])

end IsKockLawvere_one

end SDG
