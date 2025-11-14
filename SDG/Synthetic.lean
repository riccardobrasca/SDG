import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Tactic.Ring

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

lemma D_mem_iff {x : R} : x ∈ D R ↔ x ^ 2 = 0 := by rfl

variable {R} in
@[simp] lemma D_sq (x : D R) : (x : R) ^ 2 = 0 :=
  x.2

variable {R} in
abbrev two := ((2 : ℕ) : R)

lemma D_add_sq (d₁ d₂ : D R) : (d₁ + d₂ : R) ^ 2 = 2 * d₁ * d₂ :=
  calc (d₁ + d₂ : R) ^ 2 = d₁ ^ 2 + d₂ ^ 2 + (2 : ℕ) * d₁ * d₂ := by ring
                       _ = _ := by simp

lemma D_add_sq_dvd_two [Invertible (2 : R)] (d₁ d₂ : D R) :
    (d₁ + d₂ : R) ^ 2 * ⅟2 = d₁ * d₂ := by
  calc (d₁ + d₂ : R) ^ 2 * ⅟2 = (2 * d₁ * d₂) * ⅟2 := by rw [D_add_sq]
    _ = d₁ * d₂ * (2 * ⅟2) := by rw [mul_comm 2, mul_assoc _ 2, mul_comm 2, ← mul_assoc,
      ← mul_assoc]
    _ = d₁ * d₂ := by simp

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

lemma exists_derivative (g : D R → R) : ∃! b, ∀ d, g d = g 0 + d * b :=
  IsKockLawvere.isKockLawvere g

lemma cancel_d {b₁ b₂ : R} (h : ∀ d ∈ D R, d * b₁ = d * b₂) : b₁ = b₂ := by
  let g1 : D R → R := fun d ↦ d * b₁
  obtain ⟨b1, -, unique1⟩ := exists_derivative g1
  let g2 : D R → R := fun d ↦ d * b₂
  obtain ⟨b2, -, unique2⟩ := exists_derivative g2
  have h1 : b1 = b₁ := by
    specialize unique1 b₁
    simp only [Subtype.forall, Subsemigroup.mem_mk, Set.mem_setOf_eq] at unique1
    rw [unique1]
    intro d hd
    simp [g1]
  have h2 : b2 = b₂ := by
    specialize unique2 b₂
    simp only [Subtype.forall, Subsemigroup.mem_mk, Set.mem_setOf_eq] at unique2
    rw [unique2]
    intro b hb
    simp [g2]
  rw [← h1, ← h2]
  apply unique2
  intro d
  simp [g2, (h d d.2).symm, h1]

lemma injective_α : Injective (α (R := R)) := by
  intro ⟨x, y⟩ ⟨z, t⟩ h
  have hxz := congr_fun h 0
  simp only [α_apply, coe_zero, zero_mul, add_zero] at hxz
  ext
  · assumption
  · replace h : ∀ d ∈ D R, d * y = d * t := by
      intro d hd
      have := congr_fun h ⟨d, hd⟩
      simpa [hxz]
    exact cancel_d h

lemma surjective_α : Surjective (α (R := R)) := by
  intro f
  obtain ⟨b, hb, unique⟩ := exists_derivative f
  use ⟨f 0, b⟩
  ext d
  simp [hb d]

lemma bijective_α : Bijective (α (R := R)) :=
  ⟨injective_α, surjective_α⟩

@[irreducible] noncomputable def deriv (f : R → R) : R → R :=
  fun x ↦ unique_choice (isKockLawvere (fun d ↦ f (x + d)))

notation:max "∂" f:max => deriv f

lemma derivative_spec (f : R → R) (d : D R) : f d = f 0 + d * ∂f 0 := by
  simpa [deriv] using unique_choice_spec (isKockLawvere (fun d ↦ f (0 + d))) d

theorem taylor_one (f : R → R) (x : R) (d : D R) : f (x + d) = f x + d * ∂f x := by
  simpa [deriv] using unique_choice_spec (isKockLawvere (fun d ↦ f (x + d))) d

theorem taylor_two [Invertible (2 : R)] (f : R → R) (x : R) (d₁ d₂ : D R) :
    letI δ : R := d₁ + d₂
    f (x + δ) = f x + δ * ∂f x + δ ^ 2 * ∂∂f x * ⅟2 :=
  calc f (x + (d₁ + d₂)) = f (x + d₁ + d₂) := by rw [add_assoc]
       _ = f (x + d₁) + d₂ * ∂f (x + d₁) := by rw [taylor_one f]
       _ = f x + d₁ * ∂f x + d₂ * ∂f (x + d₁) := by rw [taylor_one f]
       _ = f x + d₁ * ∂f x + d₂ * (∂f x + d₁ * ∂∂f x) := by rw [taylor_one ∂f]
       _ = f x + (d₁ + d₂) * ∂f x + d₁ * d₂ * ∂∂f x := by ring
       _ = f x + (d₁ + d₂) * ∂f x + ((d₁ + d₂) ^ 2 * ⅟2) * ∂∂f x := by
        rw [D_add_sq_dvd_two]
       _ = _ := by ring

end IsKockLawvere

end SDG
