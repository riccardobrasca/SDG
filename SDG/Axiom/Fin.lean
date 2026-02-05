import SDG.Linters.choice

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace SDG

section List

open List

theorem pairwise_lt_range' {s n} (step := 1) (pos : 0 < step := by simp) :
    Pairwise (· < ·) (range' s n step) :=
  match s, n, step, pos with
  | _, 0, _, _ => Pairwise.nil
  | s, n + 1, step, pos => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intro n m
      obtain ⟨a, -, rfl⟩ := mem_range'.1 m
      calc s < s + step := lt_add_of_pos_right _ pos
           _ ≤ s + step + step * a := Nat.le_add_right _ _
    · exact pairwise_lt_range' (s := s + step) step pos

theorem pairwise_le_range' {s n} (step := 1) :
    Pairwise (· ≤ ·) (range' s n step) :=
  match s, n, step with
  | _, 0, _ => Pairwise.nil
  | s, n + 1, step => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intro n m
      obtain ⟨a, -, rfl⟩ := mem_range'.1 m
      rw [add_assoc]
      exact Nat.le_add_right s (step + step * a)
    · exact pairwise_le_range' (s := s + step) step

theorem nodup_range' {s n : Nat} (step := 1) (h : 0 < step := by simp) : Nodup (range' s n step) :=
  (pairwise_lt_range' step h).imp Nat.ne_of_lt

theorem nodup_range {n : Nat} : Nodup (range n) := by
  simp +decide only [range_eq_range', nodup_range']

theorem nodup_finRange (n) : (finRange n).Nodup := by
  rw [finRange_eq_pmap_range]
  exact (Pairwise.pmap nodup_range _) fun _ _ _ _ => @Fin.ne_of_val_ne _ ⟨_, _⟩ ⟨_, _⟩

instance Fin.fintype (n : ℕ) : Fintype (Fin n) :=
  ⟨⟨finRange n, nodup_finRange n⟩, List.mem_finRange⟩

theorem Fin.univ_def (n : ℕ) : (Finset.univ : Finset (Fin n)) = ⟨finRange n, nodup_finRange n⟩ :=
  rfl

@[simp] theorem Fin.univ_val_map {α : Type*} {n : ℕ} (f : Fin n → α) :
    Finset.univ.val.map f = List.ofFn f := by
  simp [List.ofFn_eq_map, univ_def]

end List
section BigOperators

namespace Fin

open Finset

variable {n : ℕ} {M : Type*} [CommMonoid M] {A : Type*} [AddCommMonoid A]

@[to_additive]
theorem prod_ofFn (f : Fin n → M) : (List.ofFn f).prod = ∏ i, f i := by
  simp only [prod_eq_multiset_prod, Fin.univ_val_map, Multiset.prod_coe]

@[to_additive]
theorem prod_univ_def (f : Fin n → M) : ∏ i, f i = ((List.finRange n).map f).prod := by
  rw [← List.ofFn_eq_map, prod_ofFn]

attribute [to_additive existing] Fin.prod

theorem Fintype_sum_eq_sum (f : Fin n → A) :
    ∑ i, f i = Fin.sum f := by
  rw [Fin.sum_eq_sum_map_finRange, ← Fin.sum_univ_def]

@[to_additive existing]
theorem Fintype_prod_eq_prod (f : Fin n → M) :
    ∏ i, f i = Fin.prod f := by
  rw [Fin.prod_eq_prod_map_finRange, ← Fin.prod_univ_def]

theorem sum_univ_succ (f : Fin (n + 1) → A) :
    ∑ i, f i = f 0 + ∑ i : Fin n, f i.succ := by
  rw [Fintype_sum_eq_sum, Fintype_sum_eq_sum, Fin.sum_succ]

@[to_additive existing]
theorem prod_univ_succ (f : Fin (n + 1) → M) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ := by
  rw [Fintype_prod_eq_prod, Fintype_prod_eq_prod, Fin.prod_succ]

@[to_additive (attr := simp)]
theorem prod_univ_zero (f : Fin 0 → M) : ∏ i : Fin 0, f i = 1 := by
  rfl

@[to_additive (attr := simp) sum_univ_one]
theorem prod_univ_one (f : Fin 1 → M) : ∏ i : Fin 1, f i = f 0 := by
  rw [prod_univ_succ]
  exact mul_one _

@[to_additive (attr := simp)]
theorem prod_univ_two (f : Fin 2 → M) : ∏ i : Fin 2, f i = f 0 * f 1 := by
  rw [prod_univ_succ, prod_univ_one]
  rfl

@[to_additive (attr := simp)]
theorem prod_cons_one (f : Fin n → M) :
    (∏ i : Fin n.succ, (Fin.cons 1 f : Fin n.succ → M) i) = ∏ i : Fin n, f i := by
  rw [prod_univ_succ]
  simp

theorem sum_univ_succAbove_last (f : Fin (n + 1) → A) :
    ∑ i, f i = f (Fin.last n) + ∑ i : Fin n, f (((Fin.last n)).succAbove i) := by
  simp only [Fin.succAbove_last, Fintype_sum_eq_sum, Fin.sum_eq_sum_map_finRange,
    List.finRange_succ_last, List.map_append, List.map_map, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero, add_comm]
  rfl

@[to_additive existing]
theorem prod_univ_succAbove_last (f : Fin (n + 1) → M) :
    ∏ i, f i = f (Fin.last n) * ∏ i : Fin n, f (((Fin.last n)).succAbove i) := by
  simp only [Fin.succAbove_last, Fintype_prod_eq_prod, Fin.prod_eq_prod_map_finRange,
    List.finRange_succ_last, List.map_append, List.map_map, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_comm]
  rfl

@[to_additive (attr := simp)]
theorem prod_snoc_one (f : Fin n → M) :
    (∏ i : Fin n.succ, (Fin.snoc f 1 : Fin n.succ → M) i) = ∏ i : Fin n, f i := by
  rw [Fin.prod_univ_succAbove_last]
  simp

end Fin

end BigOperators

end SDG
