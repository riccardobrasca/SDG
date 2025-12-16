import SDG.D
import SDG.IsKockLawere

namespace SDG

open DualNumber Function

variable {R : Type*} [CommRing R]

section IsKockLawvere

variable [IsKockLawvereone R]

open IsKockLawvereone

lemma derivFun_spec (f : R → R) (d : D R) : f d = f 0 + d * derivFun f 0 := by
  simpa [derivFun] using unique_choice_fun_spec (fun x ↦ isKockLawvereone (fun d ↦ f (x + d))) 0 d

theorem derivFun_taylor_one (f : R → R) (x : R) (d : D R) : f (x + d) = f x + d * derivFun f x := by
  simpa [derivFun] using unique_choice_fun_spec (fun x ↦ isKockLawvereone (fun d ↦ f (x + d))) x d

lemma derivFun_unique {f : R → R} {r x : R} (hr : ∀ (d : D R), f (x + d) = f x + d * r) :
    derivFun f x = r := by
  refine cancel_d (fun d ↦ ?_)
  have := derivFun_taylor_one f x d
  simpa [hr] using this.symm

noncomputable def deriv : Derivation R (R → R) (R → R) where
  toFun := derivFun
  map_add' := by
    intro f g
    ext x
    refine derivFun_unique (fun d ↦ ?_)
    calc (f + g) (x + d) = (f x + d * derivFun f x) + (g x + d * derivFun g x) := by
          simp [derivFun_taylor_one f, derivFun_taylor_one g]
        _ = (f + g) x + d * (derivFun f + derivFun g) x := by simp; ring
  map_smul' := by
    intro r f
    ext x
    refine derivFun_unique (fun d ↦ ?_)
    calc (r • f) (x + d) = r * (f x + d * derivFun f x) := by simp [derivFun_taylor_one f]
       _ = (r • f) x + d * (r * derivFun f x) := by simp; ring
  map_one_eq_zero' := by
    ext x
    exact derivFun_unique (fun d ↦ by simp)
  leibniz' := by
    intro f g
    ext x
    refine derivFun_unique (fun d ↦ ?_)
    simp only [Pi.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, Pi.add_apply]
    calc f (x + ↑d) * g (x + ↑d) = (f x + d * derivFun f x) * (g x + d * derivFun g x) := by
          rw [derivFun_taylor_one f, derivFun_taylor_one g]
         _ = f x * g x + d * (f x * derivFun g x + derivFun f x * g x) +
            d ^ 2 * derivFun f x * derivFun g x := by ring
         _ = f x * g x + d * (f x * derivFun g x + g x * derivFun f x) := by simp; ring

instance : FunLike (Derivation R (R → R) (R → R)) (R → R) (R → R) where
  coe D := D.toFun
  coe_injective' D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h

notation3:max "∂" f:max => deriv f

lemma derivative_spec (f : R → R) (d : D R) : f d = f 0 + d * ∂f 0 :=
  derivFun_spec ..

theorem taylor_one (f : R → R) (x : R) (d : D R) : f (x + d) = f x + d * ∂f x :=
  derivFun_taylor_one ..

lemma derivative_unique {f : R → R} {r x : R} (hr : ∀ (d : D R), f (x + d) = f x + d * r) :
    ∂f x = r :=
  derivFun_unique hr

@[simp]
lemma derivative_id : ∂(id : R → R) = 1 := by
  ext x
  exact derivative_unique (fun d ↦ by simp)

@[simp]
theorem deriv_const (r : R) : ∂(fun _ ↦ r) = 0 := by
  ext x
  exact derivative_unique (fun d ↦ by simp)

theorem deriv_mul (f g : R → R) : ∂(f * g) = ∂f * g + f * ∂g := by
  simp; ring

theorem chain_rule (f g : R → R) (x : R) : ∂(f ∘ g) x = ∂f (g x) * ∂g x := by
  refine derivative_unique (fun d ↦ ?_)
  calc (f ∘ g) (x + d) = f (g x + d * ∂g x) := by rw [comp_apply, taylor_one g]
       _ = f (g x + (⟨_, D_mem_mul _ d.2⟩ : D R)) := by rfl
       _ = (f ∘ g) x + d * (∂f (g x) * ∂g x) := by rw [taylor_one f, comp_apply]; ring

theorem deriv_inv (f : R → R) [Invertible f] : ∂⅟f = -⅟f ^ 2 * ∂f := by
  simp [deriv.leibniz_invOf f]

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
    simp [-Nat.cast_ofNat] --to avoid choice
    ring

theorem taylor_two [Invertible (2 : R)] (f : R → R) (x : R) (d₁ d₂ : D R) :
    letI δ : R := d₁ + d₂
    f (x + δ) = f x + δ * ∂f x + δ ^ 2 * ∂∂f x * ⅟2 :=
  calc f (x + (d₁ + d₂)) = f (x + d₁ + d₂) := by rw [add_assoc]
       _ = f (x + d₁) + d₂ * ∂f (x + d₁) := by rw [taylor_one f]
       _ = f x + d₁ * ∂f x + d₂ * ∂f (x + d₁) := by rw [taylor_one f]
       _ = f x + d₁ * ∂f x + d₂ * (∂f x + d₁ * ∂∂f x) := by rw [taylor_one ∂f]
       _ = f x + (d₁ + d₂) * ∂f x + d₁ * d₂ * ∂∂f x := by ring
       _ = f x + (d₁ + d₂) * ∂f x + ((d₁ + d₂) ^ 2 * ⅟2) * ∂∂f x := by rw [D_add_sq_dvd_two]
       _ = _ := by ring

end IsKockLawvere

end SDG
