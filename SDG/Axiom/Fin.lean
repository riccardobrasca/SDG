import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.DepRewrite
import Mathlib.Algebra.BigOperators.Fin

import SDG.Linters.choice

namespace SDG

section BigOperators

namespace Fin

open Finset

variable {n : ℕ} {M : Type*} [CommMonoid M] {A : Type*} [AddCommMonoid A]

attribute [to_additive existing] Fin.prod
set_option linter.existingAttributeWarning false in
attribute [to_additive (attr := simp) existing] Fin.prod_eq_prod_map_finRange
attribute [to_additive existing] Fin.prod_succ

@[to_additive]
theorem Fintype_prod_eq_prod (f : Fin n → M) : ∏ i, f i = Fin.prod f := by
  rw [Fin.prod_eq_prod_map_finRange, ← Fin.prod_univ_def]

@[to_additive]
theorem prod_univ_succ (f : Fin (n + 1) → M) : ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ := by
  exact Fin.prod_univ_succAbove f 0

@[to_additive (attr := simp)]
theorem prod_univ_zero (f : Fin 0 → M) : ∏ i : Fin 0, f i = 1 := rfl

@[to_additive sum_univ_one]
theorem prod_univ_one (f : Fin 1 → M) : ∏ i : Fin 1, f i = f 0 := by
  simp

@[to_additive]
theorem prod_univ_two (f : Fin 2 → M) : ∏ i : Fin 2, f i = f 0 * f 1 := by
  simp

@[to_additive]
theorem prod_cons_one (f : Fin n → M) :
    (∏ i : Fin n.succ, (Fin.cons 1 f : Fin n.succ → M) i) = ∏ i : Fin n, f i := by
  simp

@[to_additive]
theorem prod_univ_succAbove_last (f : Fin (n + 1) → M) :
    ∏ i, f i = f (Fin.last n) * ∏ i : Fin n, f (((Fin.last n)).succAbove i) := by
  simp only [Fin.succAbove_last, Fintype_prod_eq_prod, Fin.prod_eq_prod_map_finRange,
    List.finRange_succ_last, List.map_append, List.map_map, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_comm]
  rfl

@[to_additive]
theorem prod_snoc_one (f : Fin n → M) :
    (∏ i : Fin n.succ, (Fin.snoc f 1 : Fin n.succ → M) i) = ∏ i : Fin n, f i := by
  simp

@[to_additive]
theorem prod_natAdd_zero : ∀ a (f : Fin (0 + a) → M), ∏ i, f i = ∏ i, f (Fin.natAdd 0 i)
| 0 => by simp [-univ_eq_empty]
| (a + 1) => fun f ↦ by
  rw! (castMode := .all) [← add_assoc, prod_univ_succ, prod_univ_succ, prod_natAdd_zero]
  rfl

@[to_additive]
theorem prod_univ_add : ∀ a b (f : Fin (a + b) → M), (∏ i : Fin (a + b), f i) =
    (∏ i : Fin a, f (Fin.castAdd b i)) * ∏ i : Fin b, f (Fin.natAdd a i)
| 0, b => fun f ↦ by simp [-univ_eq_empty, prod_natAdd_zero]
| a, 0 => fun f ↦ by simp [-univ_eq_empty]; rfl
| a + 1, b + 1 => fun f ↦ by
  rw! (castMode := .all) [← add_assoc, prod_univ_succAbove_last (n := a + 1 + b),
    prod_univ_succAbove_last (n := b), ← mul_assoc, mul_comm (∏ i, f (Fin.castAdd (b + 1) i)),
    mul_assoc]
  congr 1
  rw [prod_univ_add (a + 1)]
  congr 1
  · simp; rfl
  · simp

@[to_additive]
theorem prod_trunc {a b : ℕ} (f : Fin (a + b) → M) (hf : ∀ j : Fin b, f (Fin.natAdd a j) = 1) :
    (∏ i : Fin (a + b), f i) = ∏ i : Fin a, f (Fin.castAdd b i) := by
  rw [prod_univ_add, Fintype.prod_eq_one _ hf, mul_one]

@[to_additive]
theorem prod_castLe_of_eq_one {a b : ℕ} (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ i, a ≤ i.1 → f i = 1) : ∏ i, f i = ∏ i, f (Fin.castLE h i) := by
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  rw [prod_univ_add]
  convert mul_one _
  exact Finset.prod_eq_one (fun i _ ↦ hf _ (Nat.le_add_right ..))

end Fin

end BigOperators

end SDG
