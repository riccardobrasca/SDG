import Mathlib.Tactic.Zify
import Mathlib.Tactic.Ring

import SDG.Basic.Defs
namespace SDG

open Function BigOperators Nat

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
  calc
    x ^ (ℓ + 1) = x ^ (k + 1 + (ℓ - k)) := by congr 1; zify [h]; ring
              _ = x ^ (k + 1) * x ^ (ℓ - k) := by ring
              _ = 0 := by simp [𝔻_mem_iff.1 hx]

lemma D_add_sq (d₁ d₂ : D R) : (d₁ + d₂ : R) ^ 2 = 2 * d₁ * d₂ :=
  calc (d₁ + d₂ : R) ^ 2 = d₁ ^ 2 + d₂ ^ 2 + 2 * d₁ * d₂ := by ring
                       _ = _ := by simp

lemma mem_𝔻_of_mem_D_add_mem_D (d₁ d₂ : D R) : (d₁ + d₂ : R) ∈ 𝔻 R 2 :=
  calc
    (d₁ + d₂ : R) ^ 3 = d₁ ^ 2 * (d₁ + 3 * d₂) + d₂ ^ 2 * (3 * d₁ + d₂) := by ring
                    _ = 0 := by simp

open Multiset Finset

theorem mem_D_add_pow (x : D R) (y : R) : ∀ (k : ℕ), (x + y) ^ (k + 1) =
  (↑(k + 1) : R) * x * y ^ k + y ^ (k + 1)
| 0 => by simp
| n + 1 => by
  rw [pow_succ, mem_D_add_pow x]
  simp only [cast_add, cast_one]
  calc _ = y ^ (n + 2) + y ^ (n + 1) * x + (n + 1) * x * y ^ (n + 1) +
    (n + 1) * x ^ 2 * y ^ n := by ring
       _ = _ := by simp; ring

lemma mem_D_sum_pow_succ : ∀ {k : ℕ} (b : Fin k → D R), (∑ i, (b i : R)) ^ (k + 1) = 0
| 0 => fun b ↦ by
  rw [zero_add, pow_one]
  exact sum_empty
| n + 1 => fun b ↦ by
  rw [Fin.sum_univ_succ, mem_D_add_pow, mem_D_sum_pow_succ, mul_zero, zero_add, pow_succ,
    mem_D_sum_pow_succ, zero_mul]

lemma mem_D_sum_pow_of_gt {k : ℕ} {q : ℕ} (h : k < q) (b : Fin k → D R) :
    (∑ i, (b i : R)) ^ q = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [show k + n + 1 = k + 1 + n by ring, pow_add, mem_D_sum_pow_succ, zero_mul]

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
