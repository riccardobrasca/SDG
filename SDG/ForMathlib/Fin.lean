module

public import Mathlib.Algebra.BigOperators.Fin

public import SDG.Linters.choice

/-!
# Fin product lemmas

The following are simplification lemmas for products over `Fin n` involving `cons`, `snoc`, and
`castLE`. These are candidates for upstreaming to Mathlib.
-/

@[expose] public section

open Fin

namespace Fin

variable {n : ℕ} {M : Type*} [CommMonoid M]

@[to_additive]
theorem prod_cons_one (f : Fin n → M) :
    (∏ i : Fin n.succ, (Fin.cons 1 f : Fin n.succ → M) i) = ∏ i : Fin n, f i := by
  simp only [Nat.succ_eq_add_one, prod_cons, one_mul]

@[to_additive]
theorem prod_snoc_one (f : Fin n → M) :
    (∏ i : Fin n.succ, (Fin.snoc f 1 : Fin n.succ → M) i) = ∏ i : Fin n, f i := by
  simp

@[to_additive]
theorem prod_castLE_of_eq_one {a b : ℕ} (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ i, a ≤ i.1 → f i = 1) : ∏ i, f i = ∏ i, f (Fin.castLE h i) := by
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  rw [prod_univ_add]
  convert mul_one _
  exact Finset.prod_eq_one (fun i _ ↦ hf _ (Nat.le_add_right ..))

end Fin
