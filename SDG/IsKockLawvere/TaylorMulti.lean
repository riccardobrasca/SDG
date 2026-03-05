import Mathlib

import SDG.IsKockLawvere.Taylor
import SDG.IsKockLawvere_one.PartialDeriv

open Function Finset Nat Fin

namespace SDG

variable {R : Type*} [CommRing R] [IsKockLawvere_one R]

variable {n : ℕ} (k : Fin n → ℕ) (f : (Fin n → R) → R) (d : Π i, 𝔻 R (k i)) (r : Fin n → R)

instance : HAdd (Fin n → R) (Π i, 𝔻 R (k i)) (Fin n → R) where
  hAdd := fun r d i ↦ r i + d i

omit [IsKockLawvere_one R] in
@[simp]
lemma R_add_D_fun (i : Fin n) : (r + d) i = r i + d i := by
  rfl

noncomputable abbrev Ψ (i : Fin n) := ∂_[i]^[k i]f

noncomputable def mixed_partial_deriv : (Fin n → R) → R := foldl n (Ψ k) f

notation3:max "∂[" k "]" f:max => mixed_partial_deriv k f

@[simp]
theorem mixed_partial_deriv_zero_var {k : Fin 0 → ℕ} {f : (Fin 0 → R) → R} :
    ∂[k] f = f :=
  foldl_zero _ _

theorem mixed_partial_deriv_succ {n : ℕ} {k : Fin (n + 1) → ℕ} {f : (Fin (n + 1) → R) → R} :
    ∂[k] f = foldl n (fun g i => ∂_[i.succ]^[k i.succ] g) (∂_[0]^[k 0] f) :=
  foldl_succ _ _

theorem mixed_partial_deriv_succ_last {n : ℕ} {k : Fin (n + 1) → ℕ} {f : (Fin (n + 1) → R) → R} :
    ∂[k] f = ∂_[last n]^[k (last n)] (foldl n (fun g i ↦ ∂_[i.castSucc]^[k i.castSucc] g) f) :=
  foldl_succ_last _ _

theorem mixed_partial_deriv_one_var {k : Fin 1 → ℕ} {f : (Fin 1 → R) → R} :
    ∂[k] f = ∂_[0]^[k 0] f := by
  rw [mixed_partial_deriv_succ, foldl_zero]

@[simp]
theorem mixed_partial_deriv_zero {n : ℕ} {f : (Fin n → R) → R} : ∂[0] f = f := by
  suffices h : ∀ m, foldl m (fun (a : (Fin n → R) → R) _ ↦ a) f = f by exact h n
  intro m
  induction m with
  | zero => simp
  | succ m ih => simp [foldl_succ, ih]

variable [Divisible R] [IsKockLawvere R]

theorem taylor_multi : f (r + d) = ∑ (α : Iic k), ∂[α]f r * ∏ i, d i * ⅟((α.1 i)! : R) := by
match n with
| 0 =>
  simp only [univ_eq_attach, mixed_partial_deriv_zero_var, univ_eq_empty, prod_empty, mul_one,
    Finset.sum_const, card_attach, nsmul_eq_mul]
  convert (one_mul _).symm
  exact cast_one
| n + 1 =>
  let g : R → R := fun x ↦ f (snoc (init (r + d)) x)
  have hg : f (r + d) = g (r (last n) + d (last n)) := by
    congr; ext i; by_cases hi : i = last n
    · simp [hi]
    · obtain ⟨j, rfl⟩ := exists_castSucc_eq.2 hi
      simp; rfl
  rw [hg, taylor_k g _ (k (last n))]
  sorry

end SDG
