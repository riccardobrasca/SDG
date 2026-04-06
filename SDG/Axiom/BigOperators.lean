module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.Defs

/-!
These declarations have to be reproven since Mathlib's version does not assume `DecidableEq ι` and
so it depends on the axiom of choice.
-/

@[expose] public section

set_option linter.unusedDecidableInType false

open Function Finset

variable {ι α N : Type*} [CommMonoid N] [Preorder N] {f g : ι → N} {s t : Finset ι} [DecidableEq ι]

namespace SDG.Finset

@[to_additive (attr := gcongr) sum_le_sum]
theorem prod_le_prod' [MulLeftMono N] (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  revert h
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    intro h
    rw [prod_insert ha, prod_insert ha]
    exact mul_le_mul' (h _ (mem_insert_self _ _)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

@[to_additive sum_nonneg]
theorem one_le_prod' [MulLeftMono N] (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  le_trans (by rw [prod_const_one]) (prod_le_prod' h)

@[to_additive (attr := gcongr) sum_le_sum_of_subset_of_nonneg]
theorem prod_le_prod_of_subset_of_one_le' [MulLeftMono N] (h : s ⊆ t)
    (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  calc
      ∏ i ∈ s, f i ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i :=
        le_mul_of_one_le_left' <| one_le_prod' <| by simpa only [mem_sdiff, and_imp]
      _ = ∏ i ∈ t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i ∈ t, f i := by rw [sdiff_union_of_subset h]

@[to_additive single_le_sum]
theorem single_le_prod' [MulLeftMono N] (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s) :
    f a ≤ ∏ x ∈ s, f x :=
  calc
    f a = ∏ i ∈ {a}, f i := (prod_singleton _ _).symm
    _ ≤ ∏ i ∈ s, f i :=
      prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ ↦ hf i hi

lemma prod_eq_zero {ι M₀ : Type*} [CommMonoidWithZero M₀] [DecidableEq ι] {f : ι → M₀}
    {s : Finset ι} {i : ι} (hi : i ∈ s) (h : f i = 0) : ∏ j ∈ s, f j = 0 := by
  rw [← prod_erase_mul _ _ hi, h, mul_zero]

end SDG.Finset
