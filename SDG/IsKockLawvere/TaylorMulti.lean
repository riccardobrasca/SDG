import Mathlib

import SDG.IsKockLawvere.Taylor
import SDG.IsKockLawvere_one.PartialDeriv

open Function Finset Nat Fin

namespace SDG

variable {R : Type*} [CommRing R] [IsKockLawvere_one R]

variable {n m : ℕ} [h : Fact (m ≤ n)] (k : Fin m → ℕ)
  (f : (Fin n → R) → R) (d : Π i, 𝔻 R (k i)) (r : Fin n → R)

instance : Fact (m + 1 ≤ n + 1) := ⟨Nat.add_le_add_right h.1 1⟩
instance : Fact (m ≤ n + 1) := ⟨le_add_right_of_le h.1⟩
instance : Fact (0 ≤ n) := ⟨Nat.zero_le n⟩
instance : Fact (n ≤ n) := ⟨le_rfl⟩

omit [IsKockLawvere_one R] in
instance : HAdd (Fin m → R) (Π i, 𝔻 R (k i)) (Fin m → R) where
  hAdd := fun r d i ↦ r i + d i

omit [IsKockLawvere_one R] in
@[simp]
lemma R_add_D_fun (r : Fin m → R) (i : Fin m) : (r + d) i = r i + d i := rfl

omit [IsKockLawvere_one R] in
@[simp]
lemma init_R_add_D_fun (k : Fin (m + 1) → ℕ) (d : Π i, 𝔻 R (k i)) (r : Fin (m + 1) → R) :
    init (r + d) = init r + init d := rfl

noncomputable def Ψl (i : Fin m) := ∂_[castLE h.1 i]^[k i]f

lemma Ψl_def (i : Fin m) : Ψl k f i = ∂_[castLE h.1 i]^[k i]f := rfl

@[simp]
lemma Ψl_zero (k : Fin (m + 1) → ℕ) (f : (Fin (n + 1) → R) → R) : Ψl k f 0 = ∂_[0]^[k 0]f := by
  rfl

lemma Ψl_castSucc (k : Fin (m + 1) → ℕ) (i : Fin m) (f : (Fin (n + 1) → R) → R) :
    Ψl k f i.castSucc = Ψl (init k) f i := rfl

noncomputable def mixed_partial_deriv : (Fin n → R) → R := foldl m (Ψl k) f

notation3:max "∂[" k "]" f:max => mixed_partial_deriv k f

lemma mixed_partial_deriv_def (f : (Fin n → R) → R) : ∂[k] f = foldl m (Ψl k) f := rfl

noncomputable def Ψr (i : Fin m) (f : (Fin n → R) → R) := ∂_[castLE h.1 i]^[k i]f

lemma Ψr_def (i : Fin m) : Ψr k i f = ∂_[castLE h.1 i]^[k i]f := rfl

lemma Ψr_castSucc (k : Fin (m + 1) → ℕ) (i : Fin m) (f : (Fin (n + 1) → R) → R) :
    Ψr k i.castSucc f = Ψr (init k) i f := rfl

lemma mixed_partial_deriv_foldr (f : (Fin n → R) → R) : ∂[k] f = foldr m (Ψr k) f := by
  rw [mixed_partial_deriv_def, foldl_eq_finRange_foldl, foldr_eq_finRange_foldr,
    List.foldr_eq_foldl_reverse]
  refine List.Perm.foldl_eq' (List.reverse_perm _).symm (fun i hi j hj f ↦ ?_) _
  simp only [Ψl_def]
  exact partial_deriv_iterate_comm f (castLE Fact.out j) (castLE Fact.out i) _ _

theorem mixed_partial_deriv_succ_eq_deriv_init (k : Fin (m + 1) → ℕ) (f : (Fin (n + 1) → R) → R) :
    ∂[k] f = ∂_[castLE (Nat.add_le_add_right h.1 1) (last m)]^[k (last m)]∂[init k]f := by
  simp_rw [mixed_partial_deriv_def, foldl_succ_last, Ψl_castSucc, ← mixed_partial_deriv_def,
    Ψl_def]

theorem mixed_partial_deriv_succ_eq_init_deriv (k : Fin (m + 1) → ℕ) (f : (Fin (n + 1) → R) → R) :
    ∂[k] f = ∂[init k]∂_[castLE (Nat.add_le_add_right h.1 1) (last m)]^[k (last m)]f := by
  simp_rw [mixed_partial_deriv_foldr (m := m + 1), foldr_succ_last]
  conv => enter [1, 2, x, f]; rw [Ψr_castSucc k x f]
  rw [← mixed_partial_deriv_foldr, Ψr_def]

@[simp]
theorem mixed_partial_deriv_zero (k : Fin 0 → ℕ) (f : (Fin n → R) → R) : ∂[k] f = f :=
  foldl_zero _ _

@[simp]
theorem mixed_partial_deriv_one (k : Fin 1 → ℕ) (f : (Fin (n + 1) → R) → R) :
    ∂[k] f = ∂_[0]^[k 0]f := by
  simp [mixed_partial_deriv_succ_eq_deriv_init]

private lemma mixed_partial_deriv_comm_partial_deriv_aux :
    ∀ {n m : ℕ} [Fact (m ≤ n)] (k : Fin m → ℕ) (f : (Fin n → R) → R) (i : Fin n),
    ∂[k] (∂_[i] f) = ∂_[i] (∂[k] f)
| _, 0, _, k, f, i => by simp
| n + 1, m + 1, hle, k, f, i => by
  haveI hm : Fact (m ≤ n) := ⟨Nat.le_of_succ_le_succ hle.out⟩
  simpa [mixed_partial_deriv_succ_eq_deriv_init,
    mixed_partial_deriv_comm_partial_deriv_aux (init k) f i] using
    partial_deriv_iterate_comm _ (castLE (Nat.add_le_add_right hm.out 1) (last m)) i (k (last m)) 1

lemma mixed_partial_deriv_comm_partial_deriv_iterate (i : Fin n) (j : ℕ) :
    ∂[k] (∂_[i]^[j]f) = ∂_[i]^[j](∂[k] f) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ', Function.comp_def, mixed_partial_deriv_comm_partial_deriv_aux, ih]

lemma mixed_partial_deriv_comm_partial_deriv (i : Fin n) :
    ∂[k] (∂_[i] f) = ∂_[i] (∂[k] f) := by
  simpa [Function.iterate_one] using mixed_partial_deriv_comm_partial_deriv_iterate k f i 1

lemma partial_deriv_iterate_castSucc_snoc (f : (Fin (n + 1) → R) → R) (i : Fin n) (s : Fin n → R)
    (c : R) (j : ℕ) : ∂_[castSucc i]^[j] f (snoc s c) = ∂_[i]^[j] (fun t ↦ f (snoc t c)) s := by
  induction j generalizing f s with
  | zero => simp
  | succ j ih =>
    simp only [Function.iterate_succ', Function.comp_def, ← partial_deriv_snoc_castSucc]
    congr; ext; exact ih f _

lemma mixed_partial_deriv_snoc : ∀ {n m : ℕ} [Fact (m ≤ n)] [Fact (m ≤ n + 1)] (k : Fin m → ℕ)
    (f : (Fin (n + 1) → R) → R) (s : Fin n → R) (c : R),
    ∂[k] f (snoc s c) = ∂[k] (fun t ↦ f (snoc t c)) s
| _, 0, _, _, _, _, _, _ => by simp
| n + 1, m + 1, hle, hle', k, f, s, c => by
  have hm : Fact (m ≤ n) := ⟨Nat.le_of_succ_le_succ hle.1⟩
  have hm' : Fact (m ≤ n + 1) := ⟨le_add_right_of_le hm.1⟩
  have key : (fun t ↦ ∂[init k] f (snoc t c)) = ∂[init k] (fun t ↦ f (snoc t c)) := by
    ext; exact mixed_partial_deriv_snoc ..
  have : castLE (Nat.add_le_add_right hm'.1 1) _ =
    castSucc (castLE (Nat.add_le_add_right hm.1 1) (last m)) := rfl
  rw [mixed_partial_deriv_succ_eq_deriv_init, this, partial_deriv_iterate_castSucc_snoc, key,
    ← mixed_partial_deriv_succ_eq_deriv_init]

theorem mixed_partial_deriv_initial (k : Fin (n + 1) → ℕ) (f : (Fin (n + 1) → R) → R)
  (r : Fin (n + 1) → R) : ∂[k] f r =
    letI g : (Fin n → R) → R := fun s ↦ ∂^[k (last n)] (fun y ↦ f (snoc s y)) (r (last n))
    ∂[init k]g (init r) := by
  set g : (Fin n → R) → R := fun s ↦ ∂^[k (last n)] (fun y ↦ f (snoc s y)) (r (last n)) with hg
  simp_rw [← partial_deriv_iterate_snoc_last] at hg
  rw [hg]
  conv_lhs =>
    rw [mixed_partial_deriv_succ_eq_init_deriv, ← snoc_init_self r, mixed_partial_deriv_snoc]
  rfl

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

theorem taylor_multi_aux : ∀ {n} (k : Fin n → ℕ) (f : (Fin n → R) → R) (d : Π i, 𝔻 R (k i))
    (r : Fin n → R), f (r + d) = ∑ (α : Iic k), ∂[α.1]f r * ∏ i, (d i) ^ (α.1 i) * ⅟((α.1 i)! : R)
| 0 => fun k f d r ↦ by
  simp only [univ_eq_attach, mixed_partial_deriv_zero, univ_eq_empty, prod_empty, mul_one,
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
  conv => enter [1, 2, x, 1, 1]; exact taylor_multi_aux (init k) ..
  simp_rw [Finset.sum_mul, helper, foo]
  congr
  ext α
  rw [mul_rotate _ (∏ _, _), mul_comm (∂[α.1]f r), mul_right_comm, mul_right_comm (∏ _, _), mul_comm
    (∏ _, _), prod_mul_distrib, mul_comm (∏ _, _), ← mul_assoc, mul_assoc (_ * (∏ _, _)),
    mul_assoc (_ * (∏ _, _)), prod_mul_distrib, mul_comm (∏ _, _) (∏ _, _), mul_assoc (∏ _, _)]
  congr 1
  · rw [mul_comm, prod_univ_castSucc]
    rfl
  rw [prod_univ_castSucc, mul_assoc]
  congr 2
  simp [h, partial_deriv_iterate_snoc_last, mixed_partial_deriv_initial]

theorem taylor_multi (k : Fin n → ℕ) (f : (Fin n → R) → R) (d : Π i, 𝔻 R (k i))
    (r : Fin n → R) : f (r + d) =
    ∑ α ∈ Iic k, ∂[α]f r * ∏ i, (d i) ^ (α i) * ⅟((α i)! : R) := by
  convert taylor_multi_aux k f d r
  rw [Finset.sum_subtype]
  intro α
  rfl

end SDG
