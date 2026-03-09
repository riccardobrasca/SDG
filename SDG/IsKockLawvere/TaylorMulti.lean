import Mathlib

import SDG.IsKockLawvere.Taylor
import SDG.IsKockLawvere_one.PartialDeriv

open Function Finset Nat Fin

namespace SDG

variable {R : Type*} [CommRing R] [IsKockLawvere_one R]

variable {n : ℕ} (k : Fin n → ℕ) (f : (Fin n → R) → R) (d : Π i, 𝔻 R (k i)) (r : Fin n → R)

omit [IsKockLawvere_one R] in
instance : HAdd (Fin n → R) (Π i, 𝔻 R (k i)) (Fin n → R) where
  hAdd := fun r d i ↦ r i + d i

omit [IsKockLawvere_one R] in
@[simp]
lemma R_add_D_fun (i : Fin n) : (r + d) i = r i + d i := rfl

omit [IsKockLawvere_one R] in
@[simp]
lemma init_R_add_D_fun (k : Fin (n + 1) → ℕ) (d : Π i, 𝔻 R (k i)) (r : Fin (n + 1) → R) :
    init (r + d) = init r + init d := rfl

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

section helper

open Pi

variable {T : Type*} {k : Fin (n + 1) → ℕ}

def foo (f : (Fin (k (last n) + 1)) → (Iic (init k)) → T) : Iic k → T := fun x ↦
  f ⟨x.1 _, Nat.lt_add_one_iff.mpr ((le_def.1 <| mem_Iic.1 x.2) _)⟩
    ⟨init x.1, mem_Iic.2 (le_def.2 fun i ↦ le_def.1 (mem_Iic.1 x.2) (castSucc i))⟩

def bar (f : Iic k → T) : (Fin (k (last n) + 1)) → (Iic (init k)) → T := fun x i ↦
    f ⟨fun j ↦ if h : j = last n then x.1 else i.1 (castPred _ h), by
  refine mem_Iic.2 (fun j ↦ ?_)
  by_cases h : j = last _
  · simp [h]; omega
  · simpa [init, castSucc_castPred j h, h] using le_def.1 (mem_Iic.1 i.2) _⟩

lemma barfoo (f : (Fin (k (last n) + 1)) → (Iic (init k)) → T) : bar (foo f) = f := by
  ext x i; refine congr_arg₂ f (Fin.ext ?_) (Subtype.ext (funext fun m ↦ ?_)) <;>
  simp [init]

lemma foobar (f : Iic k → T) : foo (bar f) = f := by
  ext y; refine congr_arg f ?_; ext j
  by_cases h : j = last _ <;>
  simp [h, init]

def iicEquiv : Fin (k (last n) + 1) × (Iic (init k)) ≃ (Iic k) where
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

lemma helper [AddCommGroup T] (k : Fin (n + 1) → ℕ)
    (f : (Fin (k (last n) + 1)) → (Iic (init k)) → T) : ∑ x, ∑ i, f x i = ∑ i, foo f i := by
  rw [← Finset.sum_product']
  exact Fintype.sum_equiv iicEquiv _ _ fun p ↦
    (congr_fun (congr_fun (barfoo f) p.1) p.2).symm

end helper

example (a₁ a₂ b c d : R) : a₁ * a₂ * b * c * d = (a₁ * a₂) * (b * d * c) := by
  rw [mul_assoc (a₁ * a₂), mul_assoc (a₁ * a₂)]
  sorry

theorem taylor_multi : ∀ {n} (k : Fin n → ℕ) (f : (Fin n → R) → R) (d : Π i, 𝔻 R (k i))
    (r : Fin n → R), f (r + d) = ∑ (α : Iic k), ∂[α]f r * ∏ i, (d i) ^ (α.1 i) * ⅟((α.1 i)! : R)
| 0 => fun k f d r ↦ by
  simp only [univ_eq_attach, mixed_partial_deriv_zero_var, univ_eq_empty, prod_empty, mul_one,
    Finset.sum_const, card_attach, nsmul_eq_mul]
  convert (one_mul _).symm
  exact cast_one
| n + 1 => fun k f d r ↦ by
  let g : R → R := fun x ↦ f (snoc (init (r + d)) x)
  let h (i : ℕ) : (Fin n → R) → R := fun x ↦ ∂_[last n]^[i] f (snoc x (r (last n)))
  have hfg : f (r + d) = g (r (last n) + d (last n)) := by
    congr; ext i; by_cases hi : i = last n
    · simp [hi]
    · obtain ⟨j, rfl⟩ := exists_castSucc_eq.2 hi; simp [init]
  have hg : ∀ i, ∂_[last n]^[i] f (snoc (init (r + d)) (r (last n))) = ∂^[i] g (r (last n)) :=
    fun i ↦ by simpa using partial_deriv_iterate_eq_deriv_snoc_init i f (snoc _ _)
  have hh : ∀ i, ∂_[last n]^[i] f (snoc (init (r + d)) (r (last n))) = h i (init (r + d)) :=
    fun _ ↦ rfl
  simp_rw [hfg, taylor_k g _ (k (last n)), ← hg, hh, init_R_add_D_fun,]
  conv => enter [1, 2, x, 1, 1]; exact taylor_multi (init k) ..
  simp_rw [Finset.sum_mul, helper, foo]
  congr
  ext α
  rw [mul_rotate _ (∏ _, _), mul_comm (∂[α]f r), mul_right_comm, mul_right_comm (∏ _, _), mul_comm
    (∏ _, _), prod_mul_distrib, mul_comm (∏ _, _), ← mul_assoc, mul_assoc (_ * (∏ _, _)),
    mul_assoc (_ * (∏ _, _)), prod_mul_distrib, mul_comm (∏ _, _) (∏ _, _), mul_assoc (∏ _, _)]
  congr 1
  · rw [mul_comm, prod_univ_castSucc]
    rfl
  rw [prod_univ_castSucc, mul_assoc]
  congr 2
  sorry

end SDG
