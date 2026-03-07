import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

import SDG.Basic.D
import SDG.IsKockLawvere_one.Basic
import SDG.IsKockLawvere_one.Deriv

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


noncomputable def partial_derivFun : (Fin n → R) → R :=
  unique_choice_fun (partial_deriv_propr i f)

lemma partial_derivFun_spec (d : D R) :
    f (update x i (x i + d)) = f x + (partial_derivFun i f x) * d :=
  unique_choice_fun_spec (partial_deriv_propr i f) ..

variable {f} in
lemma partial_derivFun_unique {b : R} (hb : ∀ (d : D R), f (update x i (x i + d)) = f x + b * d) :
      partial_derivFun i f x = b :=
  unique_choice_fun_unique (partial_deriv_propr i f) hb

noncomputable def partial_deriv : Derivation R ((Fin n → R) → R) ((Fin n → R) → R) where
  toFun := partial_derivFun i
  map_add' := fun f g ↦ funext fun x ↦ partial_derivFun_unique i <| fun d ↦
    calc _ = f (update x i (x i + d)) + g (update x i (x i + d)) := by simp
         _ = (f x + partial_derivFun i f x * d) + (g x + partial_derivFun i g x * d) := by
              simp only [partial_derivFun_spec]
         _ = (f + g) x + (partial_derivFun i f + partial_derivFun i g) x * d := by simp; ring
  map_smul' := fun r f ↦ funext fun x ↦ partial_derivFun_unique i <| fun d ↦
    calc (r • f) (update x i (x i + d)) = r * f (update x i (x i + d)) := by simp
      _ = r * (f x + partial_derivFun i f x * d) := by rw [partial_derivFun_spec i f]
      _ = (r • f) x + (r * partial_derivFun i f x) * d := by simp; ring
  map_one_eq_zero' := funext fun _ ↦ partial_derivFun_unique i (by simp)
  leibniz' := fun f g ↦ funext fun x ↦ partial_derivFun_unique i <| fun d ↦
    calc f (update x i (x i + d)) * g (update x i (x i + d))
          = (f x + partial_derivFun i f x * d) * (g x + partial_derivFun i g x * d) := by
              simp only [partial_derivFun_spec]
         _ = f x * g x + (f x * partial_derivFun i g x + partial_derivFun i f x * g x) * d +
            d ^ 2 * partial_derivFun i f x * partial_derivFun i g x := by ring
         _ = _ := by simp; ring

instance : FunLike (Derivation R ((Fin n → R) → R) ((Fin n → R) → R))
    ((Fin n → R) → R) ((Fin n → R) → R) where
  coe D := D.toFun
  coe_injective' := DFunLike.coe_injective

notation3:max "∂_[" i "]" f:max => partial_derivFun i f
notation3:max "∂_[" i "]^[" n "]" f:max => (partial_derivFun i)^[n] f

variable (x)

lemma partial_taylor_one (d : D R) : f (update x i (x i + d)) = f x + ∂_[i]f x * d :=
  partial_derivFun_spec ..

variable {f x} in
lemma partial_derivative_unique {b : R} (hb : ∀ (d : D R), f (update x i (x i + d)) = f x + b * d) :
    ∂_[i]f x = b :=
  partial_derivFun_unique i  hb

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

@[simp]
theorem partial_deriv_const (r : R) : ∂_[i](fun _ ↦ r) = 0 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp)

theorem partial_deriv_mul (f g : (Fin n → R) → R) :
    ∂_[i](f * g) = ∂_[i]f * g + f * ∂_[i]g := by
  change ⇑(partial_deriv i) (f * g) = ⇑(partial_deriv i) f * g + f * ⇑(partial_deriv i) g
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
  have hEq : f x₁ + ∂_[j]f x₁ * d₂ = f x₂ + ∂_[i]f x₂ * d₁ := by rw [← h₁, update_comm  H, h₂]
  rw [partial_taylor_one i f, partial_taylor_one j f, partial_taylor_one i ∂_[j]f,
    partial_taylor_one j ∂_[i]f] at hEq
  ring_nf at hEq
  simpa [mul_assoc, mul_comm, mul_left_comm] using hEq

@[simp]
theorem partial_deriv_proj_self (i : Fin n) : ∂_[i](fun x : Fin n → R ↦ x i) = 1 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp)

@[simp]
theorem partial_deriv_proj_ne {i j : Fin n} (hij : i ≠ j) : ∂_[i](fun x : Fin n → R ↦ x j) = 0 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp [hij.symm])

theorem prop41_ex : ∀ n (τ : (Fin n → D R) → R), ∃ (a : Finset (Fin n) → R), ∀ (d : Fin n → D R),
    τ d = ∑ H, a H * ∏ j ∈ H, (d j : R)
| 0 => fun τ ↦ ⟨fun _ ↦ τ elim0, fun d ↦ by
    rw [← singleton_eq_univ, sum_singleton, prod_empty, mul_one]
    exact (funext_iff_of_subsingleton d elim0).2 rfl⟩
| n + 1 => fun τ ↦ by
  let τ0 := fun d ↦ τ (cons 0 d)
  let h₁ : ∀ d : Fin n → D R, ∃! b : R, ∀ d₀ : D R,
    τ (cons d₀ d) = τ (cons 0 d) + b * d₀ := fun d ↦
    isKockLawvere_one (fun d₀ : D R ↦ τ (cons d₀ d))
  let τ1 := unique_choice_fun h₁
  have hτ1 : ∀ d d₀, τ (cons d₀ d) = τ (cons 0 d) + τ1 d * d₀ := unique_choice_fun_spec h₁
  obtain ⟨a0, ha0⟩ := prop41_ex _ τ0
  obtain ⟨a1, ha1⟩ := prop41_ex _ τ1
  let up := map ⟨succ, succ_injective n⟩
  let down : Finset (Fin (n + 1)) → Finset (Fin n) := fun H ↦ {i | i.succ ∈ H}
  let a := fun H ↦ if 0 ∈ H then a1 (down H) else a0 (down H)
  refine ⟨a, fun d ↦ ?_⟩
  let rest : Fin n → D R := fun i ↦ d i.succ
  have h0 : τ (cons 0 rest) = ∑ H, a0 H * ∏ j ∈ H, (rest j : R) := ha0 rest
  have h1 : τ1 rest = ∑ H, a1 H * ∏ j ∈ H, (rest j : R) := ha1 rest
  have hs : 0 ∉ up univ := fun h ↦ by
    rcases mem_map.mp h with ⟨i, -, hi⟩; exact succ_ne_zero i hi
  have huniv : insert 0 (up univ) = univ := by
    ext i; rcases eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;> simp [up]
  have hup_inj : Function.Injective up := by
    simpa [up] using (map_injective ⟨succ, succ_injective n⟩)
  have hpow : (up univ).powerset = univ.image up := by
    have hUpImage : (fun H ↦ H.image succ) = up := by
      ext; simp [up, map_eq_image]
    calc
      (up univ).powerset = ((univ.image succ)).powerset := by simp [up, map_eq_image]
      _ = univ.image (fun H : Finset (Fin n) ↦ H.image succ) := by
            simpa using (powerset_image (s := univ) (f := succ))
      _ = univ.image up := by simp [hUpImage]
  have hprod_up : ∀ H : Finset (Fin n), (∏ j ∈ up H, (d j : R)) = ∏ j ∈ H, (rest j : R) :=
    fun H ↦ by simp [up, rest]
  let mon : Finset (Fin (n + 1)) → R := fun H ↦ a H * ∏ j ∈ H, (d j : R)
  have hsum_repr :
      ∑ H, a0 H * ∏ j ∈ H, (rest j : R) + (∑ H, a1 H * ∏ j ∈ H, (rest j : R)) * d 0 =
      ∑ H ∈ (up univ).powerset, mon H + ∑ H ∈ (up univ).powerset, mon (insert 0 H) := by
    congr 1
    · rw [hpow, sum_image]
      · simp [mon, a, up, down, hprod_up]
      · intro s hs t ht hst
        exact hup_inj hst
    · rw [hpow, sum_image]
      · rw [sum_mul]
        refine sum_congr rfl (fun H hH ↦ ?_)
        have h0not : 0 ∉ up H := fun h ↦ by
         rcases mem_map.mp h with ⟨i, -, hi⟩
         exact succ_ne_zero i hi
        simp [mon, a, up, down, hprod_up H, h0not, prod_insert, mul_comm, mul_left_comm]
      · intro s hs t ht hst
        exact hup_inj hst
  have hcons : d = cons (d 0) rest := by
    ext i; rcases eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;> simp [rest]
  calc
    τ d = τ (cons 0 rest) + τ1 rest * d 0 := by rw [hcons]; simpa [rest] using hτ1 rest (d 0)
    _ = ∑ H, a0 H * ∏ j ∈ H, (rest j : R) + (∑ H, a1 H * ∏ j ∈ H, (rest j : R)) * d 0 := by
      rw [h0, h1]
    _ = ∑ H ∈ (up univ).powerset, mon H + (∑ H ∈ (up univ).powerset, mon (insert 0 H)) := hsum_repr
    _ = ∑ H ∈ (insert 0 (up univ)).powerset, mon H := (sum_powerset_insert hs mon).symm
    _ = ∑ H, a H * ∏ j ∈ H, (d j : R) := by rw [huniv, powerset_univ]

end IsKockLawvere_one

end SDG
