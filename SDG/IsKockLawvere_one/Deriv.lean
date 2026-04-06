module

public import Mathlib.RingTheory.Derivation.Basic

public import SDG.Basic.D
public import SDG.IsKockLawvere_one.Basic

@[expose] public section

namespace SDG

variable {R : Type*} [CommRing R]

section IsKockLawvere_one

variable [IsKockLawvere_one R]

open IsKockLawvere_one

/-- Notation for the synthetic derivative `deriv_fun f`. -/
notation3:max "∂" f:max => deriv_fun f

/-- Notation for the `n`-th iterate of the synthetic derivative. -/
notation3:max "∂^[" n "]" => Nat.iterate deriv_fun n

lemma derivative_spec (f : R → R) (d : D R) : f d = f 0 + ∂f 0 * d := by
  simpa [deriv_fun] using unique_choice_fun_spec (fun x ↦ isKockLawvere_one (fun d ↦ f (x + d))) 0 d

theorem taylor_one (f : R → R) (x : R) (d : D R) : f (x + d) = f x + ∂f x * d := by
  simpa [deriv_fun] using unique_choice_fun_spec (fun x ↦ isKockLawvere_one (fun d ↦ f (x + d))) x d

lemma derivative_unique {f : R → R} {r x : R} (hr : ∀ (d : D R), f (x + d) = f x + r * d) :
    ∂f x = r :=
  cancel_d (fun d ↦ by simpa [hr] using (taylor_one f x d).symm)

/-- The synthetic derivative as a `Derivation`,
i.e. an `R`-linear Leibniz map `(R → R) → (R → R)`. -/
noncomputable def deriv : Derivation R (R → R) (R → R) where
  toFun := deriv_fun
  map_add' := by
    intro f g
    ext x
    refine derivative_unique (fun d ↦ ?_)
    calc (f + g) (x + d) = (f x + ∂f x * d) + (g x + ∂g x * d) := by
          simp [taylor_one f, taylor_one g]
        _ = (f + g) x + (deriv_fun f + deriv_fun g) x * d := by simp; ring
  map_smul' := by
    intro r f
    ext x
    refine derivative_unique (fun d ↦ ?_)
    calc (r • f) (x + d) = r * (f x + ∂f x * d) := by simp [taylor_one f]
       _ = (r • f) x + (r * deriv_fun f x) * d := by simp; ring
  map_one_eq_zero' := by
    ext x
    exact derivative_unique (fun d ↦ by simp)
  leibniz' := by
    intro f g
    ext x
    refine derivative_unique (fun d ↦ ?_)
    simp only [Pi.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, Pi.add_apply]
    calc f (x + ↑d) * g (x + ↑d) = (f x + ∂f x * d) * (g x + ∂g x * d) := by
          rw [taylor_one f, taylor_one g]
         _ = f x * g x + (f x * deriv_fun g x + deriv_fun f x * g x) * d +
            d ^ 2 * deriv_fun f x * deriv_fun g x := by ring
         _ = f x * g x + (f x * deriv_fun g x + g x * deriv_fun f x) * d := by simp; ring

instance : FunLike (Derivation R (R → R) (R → R)) (R → R) (R → R) where
  coe D := D.toFun
  coe_injective' D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h

theorem deriv_mul (f g : R → R) : ∂(f * g) = ∂f * g + f * ∂g := by
  change deriv (f * g) = deriv f * g + f * deriv g
  simp [smul_eq_mul]; ring

@[simp]
theorem deriv_const (r : R) : ∂(fun _ ↦ r) = 0 := by
  ext x
  exact derivative_unique (fun d ↦ by simp)

@[simp]
lemma derivative_id : ∂(id : R → R) = 1 := by
  ext x
  exact derivative_unique (fun d ↦ by simp)

theorem chain_rule (f g : R → R) (x : R) : ∂(f ∘ g) x = ∂f (g x) * ∂g x := by
  refine derivative_unique (fun d ↦ ?_)
  calc (f ∘ g) (x + d) = f (g x + ∂g x * d) := by rw [Function.comp_apply, taylor_one g]
       _ = f (g x + (⟨_, 𝔻_mul_mem _ d.2⟩ : D R)) := by rfl
       _ = (f ∘ g) x + (∂f (g x) * ∂g x) * d := by rw [taylor_one f, Function.comp_apply]; ring

theorem chain_rule_fun (f g : R → R) : ∂(f ∘ g) = ∂f ∘ g * ∂g := by
  ext x
  simp [chain_rule]

theorem deriv_X_pow : ∀ (n : ℕ), ∂((id : R → R) ^ n) = n * (id : R → R) ^ (n - 1)
| 0 => by
    ext x
    exact derivative_unique (fun d ↦ by simp)
| 1 => by
    ext x
    exact derivative_unique (fun d ↦ by simp)
| n + 2 => by
    rw [pow_succ, deriv_mul, deriv_X_pow, Nat.add_one_sub_one]
    ext x
    simp
    ring

theorem deriv_inv (f : R → R) [Invertible f] : ∂⅟f = -⅟f ^ 2 * ∂f :=
  deriv.leibniz_invOf f

theorem deriv_equiv (f : R ≃ R) : ∂↑f⁻¹ * ∂f ∘ ↑f⁻¹ = 1 := by
  ext x
  have : ∂ (f.invFun ∘ f) = 1 := by simp
  rw [chain_rule_fun, funext_iff] at this
  simpa using this (f.invFun x)

section taylor

theorem taylor_two_aux [Invertible (2 : R)] (f : R → R) (x : R) (d₁ d₂ : D R) :
    letI δ : R := d₁ + d₂
    f (x + δ) = f x + ∂f x * δ + ∂∂f x * δ ^ 2 * ⅟2 :=
  calc f (x + (d₁ + d₂)) = f (x + d₁ + d₂) := by rw [add_assoc]
       _ = f (x + d₁) + ∂f (x + d₁) * d₂ := by rw [taylor_one f]
       _ = f x + ∂f x * d₁ + ∂f (x + d₁) * d₂ := by rw [taylor_one f]
       _ = f x + ∂f x * d₁ + (∂f x + ∂∂f x * d₁) * d₂ := by rw [taylor_one ∂f]
       _ = f x + ∂f x * (d₁ + d₂) + ∂∂f x * (d₁ * d₂) := by ring
       _ = f x + ∂f x * (d₁ + d₂) + ∂∂f x * ((d₁ + d₂) ^ 2 * ⅟2) := by rw [D_add_sq_dvd_two]
       _ = _ := by ring

end taylor

end IsKockLawvere_one

end SDG
