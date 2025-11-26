import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Choose.Sum

import SDG.UniqueChoice

-- things that have to be removed to avoid the axiom of choice
attribute [-instance] Nat.instAtLeastTwoHAddOfNat

instance (n : ℕ) [NeZero n] : (n + 1).AtLeastTwo :=
  ⟨Nat.add_one_le_iff.2 <| Nat.succ_lt_succ <| Nat.pos_of_neZero n⟩
namespace SDG

open DualNumber Function

variable (R : Type*) [CommRing R]

abbrev D : Subsemigroup R where
 carrier := {(x : R) | x ^ 2 = 0}
 mul_mem' := fun hx hy ↦ by simp_all [mul_pow]

variable {R}

lemma D_mem_iff {x : R} : x ∈ D R ↔ x ^ 2 = 0 := by rfl

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

variable (R)

lemma zero_mem_D : 0 ∈ D R := by
  rw [D_mem_iff, sq, mul_zero]

instance : Zero (D R) where
  zero := ⟨0, zero_mem_D _⟩

@[simp] lemma coe_zero : ((0 : D R) : R) = 0 := rfl

lemma coe_sq : ((↑) : D R → R) * (↑) = 0 := by
  ext d
  simpa only [← pow_two, Pi.zero_apply] using d.2

variable {R}

def α : DualNumber R →ₐ[R] (D R → R) :=
  lift ⟨⟨Algebra.ofId _ _, (↑)⟩, coe_sq _, fun _ ↦ Commute.all _ _⟩

@[simp] lemma α_apply (a b : R) (d : D R) : α ⟨a, b⟩ d = a + d * b := by
  simp [α, lift_apply_apply, mul_comm]

section IsKockLawvere

variable (R) in
class IsKockLawvere extends Nontrivial R where
  isKockLawvere : ∀ g : D R → R, ∃! b, ∀ d, g d = g 0 + d * b

variable [IsKockLawvere R]

open IsKockLawvere

lemma cancel_d {b₁ b₂ : R} (h : ∀ (d : D R), d * b₁ = d * b₂) : b₁ = b₂ := by
  obtain ⟨b1, -, unique1⟩ := isKockLawvere (· * b₁ : D R → R)
  obtain ⟨b2, -, unique2⟩ := isKockLawvere (· * b₂ : D R → R)
  rw [unique1 b₁ (fun d ↦ by simp), unique2 b₂ (fun d ↦ by simp)]
  exact unique2 _ (fun d ↦ by simp [(h d).symm, unique1 b₁ (fun d ↦ by simp)])

lemma injective_α : Injective (α (R := R)) := by
  intro ⟨x, y⟩ ⟨z, t⟩ h
  have hxz := congr_fun h 0
  simp only [α_apply, coe_zero, zero_mul, add_zero] at hxz
  ext
  · assumption
  · replace h : ∀ (d : D R), d * y = d * t := by
      intro d
      have := congr_fun h d
      simpa [hxz]
    exact cancel_d h

lemma surjective_α : Surjective (α (R := R)) := by
  intro f
  obtain ⟨b, hb, unique⟩ := isKockLawvere f
  use ⟨f 0, b⟩
  ext d
  simp [hb d]

lemma bijective_α : Bijective (α (R := R)) :=
  ⟨injective_α, surjective_α⟩

noncomputable def deriv (f : R → R) : R → R :=
  fun x ↦ unique_choice (isKockLawvere (fun d ↦ f (x + d)))

notation:max "∂" f:max => deriv f

lemma derivative_spec (f : R → R) (d : D R) : f d = f 0 + d * ∂f 0 := by
  simpa [deriv] using unique_choice_spec (isKockLawvere (fun d ↦ f (0 + d))) d

theorem taylor_one (f : R → R) (x : R) (d : D R) : f (x + d) = f x + d * ∂f x := by
  simpa [deriv] using unique_choice_spec (isKockLawvere (fun d ↦ f (x + d))) d

lemma derivative_unique {f : R → R} {r x : R} (hr : ∀ (d : D R), f (x + d) = f x + d * r) :
    ∂f x = r := by
  refine cancel_d (fun d ↦ ?_)
  have := taylor_one f x d
  simpa [hr] using this.symm

@[simp]
lemma derivative_id : ∂(id : R → R) = 1 := by
  ext x
  exact derivative_unique (fun d ↦ by simp)

@[simp]
theorem deriv_const (r : R) : ∂(fun _ ↦ r) = 0 := by
  ext x
  exact derivative_unique (fun d ↦ by simp)

theorem deriv_add (f g : R → R) : ∂(f + g) = ∂f + ∂g := by
  ext x
  refine derivative_unique (fun d ↦ ?_)
  calc (f + g) (x + d) = (f x + d * ∂f x) + (g x + d * ∂g x) := by simp [taylor_one f, taylor_one g]
       _ = (f + g) x + d * (∂f + ∂g) x := by simp; ring

theorem deriv_mul (f g : R → R) : ∂(f * g) = ∂f * g + f * ∂g := by
  ext x
  refine derivative_unique (fun d ↦ ?_)
  calc (f * g) (x + d) = (f x + d * ∂f x) * (g x + d * ∂g x) := by simp [taylor_one f, taylor_one g]
       _ = f x * g x + d * (f x * ∂g x + ∂f x * g x) + d ^ 2 * ∂f x * ∂g x := by ring
       _ = (f * g) x + d * (∂f * g + f * ∂g) x := by simp; ring

theorem chain_rule (f g : R → R) (x : R) : ∂(f ∘ g) x = ∂f (g x) * ∂g x := by
  refine derivative_unique (fun d ↦ ?_)
  calc (f ∘ g) (x + ↑d) = f (g x + d * ∂g x) := by rw [comp_apply, taylor_one g]
       _ = f (g x + (⟨_, D_mem_mul _ d.2⟩ : D R)) := by rfl
       _ = (f ∘ g) x + d * (∂f (g x) * ∂g x) := by rw [taylor_one f, comp_apply]; ring

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
