module

public import Mathlib.Data.Pi.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Equivalence between `Iic k` and a product over the last coordinate

For `k : Fin (n + 1) → ℕ`, we construct an equivalence between `Iic k` (multi-indices bounded
by `k`) and the product `Fin (k (last n) + 1) × Iic (init k)`, splitting off the last coordinate.
This is used to reduce multivariate sums over `Iic k` to iterated sums.
-/

@[expose] public section

open Fin Pi Finset

namespace SDG

variable {n : ℕ} {T : Type*} {k : Fin (n + 1) → ℕ}

/-- The following converts a curried function over the last index and the remaining `Iic (init k)`
into a function over `Iic k`. -/
def Iic_of_prod (f : (Fin (k (last n) + 1)) → (Iic (init k)) → T) : Iic k → T := fun x ↦
  f ⟨x.1 _, Nat.lt_add_one_iff.mpr ((le_def.1 <| mem_Iic.1 x.2) _)⟩
    ⟨init x.1, mem_Iic.2 (le_def.2 fun i ↦ le_def.1 (mem_Iic.1 x.2) (castSucc i))⟩

/-- The following converts a function over `Iic k` into a curried function over the last index and
`Iic (init k)`. -/
def prod_of_Iic (f : Iic k → T) : (Fin (k (last n) + 1)) → (Iic (init k)) → T := fun x i ↦
    f ⟨fun j ↦ if h : j = last n then x.1 else i.1 (castPred _ h), by
  refine mem_Iic.2 (fun j ↦ ?_)
  by_cases h : j = last _
  · simp [h]; omega
  · simpa [init, castSucc_castPred j h, h] using le_def.1 (mem_Iic.1 i.2) _⟩

lemma prod_of_Iic_of_prod (f : (Fin (k (last n) + 1)) → (Iic (init k)) → T) :
    prod_of_Iic (Iic_of_prod f) = f := by
  ext x i; refine congr_arg₂ f (Fin.ext ?_) (Subtype.ext (funext fun m ↦ ?_)) <;>
  simp [init]

lemma Iic_of_prod_of_Iic (f : Iic k → T) : Iic_of_prod (prod_of_Iic f) = f := by
  ext y; refine congr_arg f ?_; ext j
  by_cases h : j = last _ <;>
  simp [h, init]

/-- Equivalence between `Fin (k (last n) + 1) × Iic (init k)` and `Iic k`. -/
def Iic_equiv : Fin (k (last n) + 1) × (Iic (init k)) ≃ (Iic k) where
  toFun p := ⟨fun j ↦ if h : j = last n then p.1.1 else p.2.1 (castPred _ h), by
    refine mem_Iic.2 (fun j ↦ ?_)
    by_cases h : j = last _
    · simp [h]; omega
    · simpa [init, castSucc_castPred j h, h] using le_def.1 (mem_Iic.1 p.2.2) _⟩
  invFun y := (⟨y.1 (last n), Nat.lt_add_one_iff.mpr ((le_def.1 <| mem_Iic.1 y.2) _)⟩,
    ⟨init y.1, mem_Iic.2 (le_def.2 fun i ↦ le_def.1 (mem_Iic.1 y.2) (castSucc i))⟩)
  left_inv p := Prod.ext (Fin.ext (by simp))
    (Subtype.ext (funext fun m ↦ by simp [init, castPred_castSucc]))
  right_inv y := Subtype.ext (funext fun j ↦ by by_cases h : j = last _ <;> simp [h, init])

lemma sum_prod_eq_sum_Iic [AddCommGroup T] (k : Fin (n + 1) → ℕ)
    (f : (Fin (k (last n) + 1)) → (Iic (init k)) → T) : ∑ x, ∑ i, f x i = ∑ i, Iic_of_prod f i := by
  rw [← Finset.sum_product']
  exact Fintype.sum_equiv Iic_equiv _ _ fun p ↦
    (congr_fun (congr_fun (prod_of_Iic_of_prod f) p.1) p.2).symm

end SDG
