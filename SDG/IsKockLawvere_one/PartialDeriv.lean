module

public import Mathlib.RingTheory.Derivation.Basic

public import SDG.Basic.D
public import SDG.IsKockLawvere_one.Basic
public import SDG.IsKockLawvere_one.Deriv

@[expose] public section

open Function SDG.IsKockLawvere_one Finset Fin

namespace SDG

variable {R : Type*} [CommRing R]

section IsKockLawvere_one

variable [IsKockLawvere_one R] {n : ℕ} (i : Fin n) (f : (Fin n → R) → R) {x : Fin n → R}

lemma partial_deriv_propr : ∀ (x : Fin n → R), ∃! b, ∀ (d : D R),
    f (update x i (x i + d)) = f x + b * d := by
  intro x
  let g : D R → R := fun d ↦ f (update x i (x i + d))
  obtain ⟨b, hb, hbunique⟩ := isKockLawvere_one g
  refine ⟨b, fun d ↦ ?_, fun b₁ hb₁ ↦ hbunique b₁ (fun d ↦ ?_)⟩
  · convert hb d
    rw [coe_zero, add_zero, update_eq_self]
  · convert hb₁ d
    rw [coe_zero, add_zero, update_eq_self]

/-- The partial derivative of `f : (Fin n → R) → R` with respect to coordinate `i`. -/
noncomputable def partial_deriv_fun : (Fin n → R) → R :=
  unique_choice_fun (partial_deriv_propr i f)

/-- Notation for the partial derivative of `f` with respect to coordinate `i`. -/
notation3:max "∂_[" i "]" f:max => partial_deriv_fun i f

/-- Notation for the `n`-th iterated partial derivative with respect to coordinate `i`. -/
notation3:max "∂_[" i "]^[" n "]" f:max => (partial_deriv_fun i)^[n] f

variable (x) in
lemma partial_taylor_one (d : D R) :
    f (update x i (x i + d)) = f x + ∂_[i]f x * d :=
  unique_choice_fun_spec (partial_deriv_propr i f) ..

variable {f} in
lemma partial_derivative_unique {b : R}
    (hb : ∀ (d : D R), f (update x i (x i + d)) = f x + b * d) :
    ∂_[i]f x = b :=
  unique_choice_fun_unique (partial_deriv_propr i f) hb

/-- The partial derivative with respect to coordinate `i` as a `Derivation`. -/
noncomputable def partial_deriv : Derivation R ((Fin n → R) → R) ((Fin n → R) → R) where
  toFun := partial_deriv_fun i
  map_add' := fun f g ↦ funext fun x ↦ partial_derivative_unique i <| fun d ↦
    calc _ = f (update x i (x i + d)) + g (update x i (x i + d)) := by simp
         _ = (f x + ∂_[i]f x * d) + (g x + ∂_[i]g x * d) := by
              simp only [partial_taylor_one]
         _ = (f + g) x + (partial_deriv_fun i f + partial_deriv_fun i g) x * d := by simp; ring
  map_smul' := fun r f ↦ funext fun x ↦ partial_derivative_unique i <| fun d ↦
    calc (r • f) (update x i (x i + d)) = r * f (update x i (x i + d)) := by simp
      _ = r * (f x + ∂_[i]f x * d) := by simp only [partial_taylor_one]
      _ = (r • f) x + (r * partial_deriv_fun i f x) * d := by simp; ring
  map_one_eq_zero' := funext fun _ ↦ partial_derivative_unique i (by simp)
  leibniz' := fun f g ↦ funext fun x ↦ partial_derivative_unique i <| fun d ↦
    calc f (update x i (x i + d)) * g (update x i (x i + d))
          = (f x + ∂_[i]f x * d) * (g x + ∂_[i]g x * d) := by
              simp only [partial_taylor_one]
         _ = f x * g x + (f x * partial_deriv_fun i g x + partial_deriv_fun i f x * g x) * d +
            d ^ 2 * partial_deriv_fun i f x * partial_deriv_fun i g x := by ring
         _ = _ := by simp; ring

instance : FunLike (Derivation R ((Fin n → R) → R) ((Fin n → R) → R))
    ((Fin n → R) → R) ((Fin n → R) → R) where
  coe D := D.toFun
  coe_injective' := DFunLike.coe_injective

variable (x)

lemma partial_deriv_eq_deriv (r : Fin n → R) :
    ∂_[i] f r = ∂(fun y ↦ f (Function.update r i y)) (r i) := by
  apply cancel_d; intro d
  have h1 := partial_taylor_one i f r d
  have h2 : f (Function.update r i (r i + ↑d)) =
            f r + ∂(fun y ↦ f (Function.update r i y)) (r i) * ↑d := by
    have := taylor_one (fun y ↦ f (Function.update r i y)) (r i) d
    simp only [Function.update_eq_self] at this
    exact this
  exact add_left_cancel (h1.symm.trans h2)

lemma partial_deriv_eq_deriv_one_var (f : (Fin 1 → R) → R) (x : Fin 1 → R) :
    ∂_[0] f x = ∂(fun y ↦ f (fun _ ↦ y)) (x 0) := by
  rw [partial_deriv_eq_deriv]
  congr; ext; congr; ext i
  rw [fin_one_eq_zero i]
  simp

lemma partial_deriv_iterate_eq_deriv_one_var : ∀ k (f : (Fin 1 → R) → R) (x : Fin 1 → R),
    ∂_[0]^[k] f x = ∂^[k] (fun y ↦ f (fun _ ↦ y)) (x 0)
| 0 => fun f x ↦ congrArg f (funext fun i ↦ by rw [fin_one_eq_zero i])
| k + 1 => fun f x ↦ by
  simp only [Function.iterate_succ', Function.comp_def, partial_deriv_eq_deriv_one_var]
  congr; ext
  exact partial_deriv_iterate_eq_deriv_one_var ..

lemma partial_deriv_eq_deriv_snoc_init (f : (Fin (n + 1) → R) → R) (r : Fin (n + 1) → R) :
    ∂_[last n] f r = ∂(fun t ↦ f (snoc (init r) t)) (r (last n)) := by
  convert partial_deriv_eq_deriv .. using 2
  ext; congr; ext j
  rcases eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl <;>
  simp [init]

lemma partial_deriv_iterate_eq_deriv_snoc_init (k : ℕ) (f : (Fin (n + 1) → R) → R)
  (r : Fin (n + 1) → R) :
    ∂_[last n]^[k] f r = ∂^[k] (fun t ↦ f (snoc (init r) t)) (r (last n)) := by
match k with
| 0 => simp [snoc_init_self]
| k + 1 =>
  simp only [Function.iterate_succ', Function.comp_def]
  simp [partial_deriv_eq_deriv_snoc_init, partial_deriv_iterate_eq_deriv_snoc_init]

lemma partial_deriv_snoc_castSucc (i : Fin n) (f : (Fin (n + 1) → R) → R)
    (r : Fin n → R) (c : R) :
    ∂_[i] (fun x ↦ f (snoc x c)) r = ∂_[i.castSucc] f (snoc r c) := by
  refine partial_derivative_unique _ (fun d ↦ ?_)
  convert partial_taylor_one (castSucc i) f (snoc r c) d using 2
  ext j; rcases eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
  · rcases Decidable.eq_or_ne k i with rfl | hki <;>
    simp_all
  · simp [(castSucc_ne_last i).symm]

lemma partial_deriv_snoc_last (f : (Fin (n + 1) → R) → R) (r : Fin n → R) (c : R) :
    ∂_[last n] f (snoc r c) = ∂(fun x ↦ f (snoc r x)) c := by
  rw [partial_deriv_eq_deriv_snoc_init]
  simp [init_snoc, snoc_last]

lemma partial_deriv_iterate_snoc_last (k : ℕ) (f : (Fin (n + 1) → R) → R) (r : Fin n → R) (c : R) :
    ∂_[last n]^[k] f (snoc r c) = ∂^[k] (fun x ↦ f (snoc r x)) c := by
  simp [partial_deriv_iterate_eq_deriv_snoc_init, init_snoc, snoc_last]

lemma partial_deriv_iterate_snoc_castSucc (k : ℕ) (i : Fin n) (f : (Fin (n + 1) → R) → R)
    (r : Fin n → R) (c : R) :
    ∂_[i]^[k] (fun x ↦ f (snoc x c)) r = ∂_[i.castSucc]^[k] f (snoc r c) :=
match k with
| 0 => by simp
| k + 1 => by
  simp only [Function.iterate_succ', Function.comp_def]
  have hk : ∂_[i]^[k] (fun x ↦ f (snoc x c)) = fun r' ↦ ∂_[castSucc i]^[k] f (snoc r' c) :=
    funext fun r' ↦ partial_deriv_iterate_snoc_castSucc ..
  rw [hk, partial_deriv_snoc_castSucc]

@[simp]
theorem partial_deriv_const (r : R) : ∂_[i](fun _ ↦ r) = 0 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp)

theorem partial_deriv_mul (f g : (Fin n → R) → R) :
    ∂_[i](f * g) = ∂_[i]f * g + f * ∂_[i]g := by
  change (partial_deriv i) (f * g) = (partial_deriv i) f * g + f * (partial_deriv i) g
  simp [smul_eq_mul]; ring

theorem partial_deriv_comm (i j : Fin n) : ∂_[i](∂_[j]f) x = ∂_[j](∂_[i]f) x := by
  by_cases H : i = j
  · simp [H]
  refine cancel_d (fun d₁ ↦ cancel_d (fun d₂ ↦ ?_))
  let x₁ := update x i (x i + d₁); let x₂ := update x j (x j + d₂)
  have hx₁j : x₁ j = x j := by rcases Decidable.eq_or_ne j i <;> simp_all [x₁]
  have hx₂i : x₂ i = x i := by rcases Decidable.eq_or_ne j i <;> simp_all [x₂]
  have h₁ : f (update x₁ j (x j + d₂)) = f x₁ + ∂_[j]f x₁ * d₂ := hx₁j ▸ partial_taylor_one ..
  have h₂ : f (update x₂ i (x i + d₁)) = f x₂ + ∂_[i]f x₂ * d₁ := hx₂i ▸ partial_taylor_one ..
  have hEq : f x₁ + ∂_[j]f x₁ * d₂ = f x₂ + ∂_[i]f x₂ * d₁ := by rw [← h₁, update_comm H, h₂]
  rw [partial_taylor_one i f, partial_taylor_one j f, partial_taylor_one i ∂_[j]f,
    partial_taylor_one j ∂_[i]f] at hEq
  ring_nf at hEq
  simpa [mul_assoc, mul_comm, mul_left_comm] using hEq

private lemma partial_deriv_comm_iterate_aux (i j : Fin n) (g : (Fin n → R) → R) :
    ∀ q : ℕ, ∂_[i] (∂_[j]^[q] g) = ∂_[j]^[q] (∂_[i] g)
| 0 => rfl
| q + 1 => by
  simp only [Function.iterate_succ', Function.comp_def]
  rw [(funext fun y ↦ partial_deriv_comm .. : ∂_[i] _ = _), partial_deriv_comm_iterate_aux]

theorem partial_deriv_iterate_comm (i j : Fin n) (p q : ℕ) :
    ∂_[i]^[p] (∂_[j]^[q] f) = ∂_[j]^[q] (∂_[i]^[p] f) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simpa only [Function.iterate_succ', Function.comp_def, ih] using
      partial_deriv_comm_iterate_aux ..

@[simp]
theorem partial_deriv_proj_self (i : Fin n) : ∂_[i](fun x : Fin n → R ↦ x i) = 1 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp)

@[simp]
theorem partial_deriv_proj_ne {i j : Fin n} (hij : i ≠ j) : ∂_[i](fun x : Fin n → R ↦ x j) = 0 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp [hij.symm])

end IsKockLawvere_one

end SDG
