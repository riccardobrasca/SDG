import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

import SDG.Basic.D
import SDG.IsKockLawvere_one.Basic
import SDG.Axiom.Function

open Function SDG.IsKockLawvere_one SDG.Function

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
    rw [coe_zero, add_zero, SDG.Function.update_eq_self]
  · convert hb₁ d
    rw [coe_zero, add_zero, SDG.Function.update_eq_self]

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

notation3:max "∂[" i "]" f:max => partial_deriv i f

variable (x)

lemma partial_taylor_one (d : D R) : f (update x i (x i + d)) = f x + ∂[i]f x * d :=
  partial_derivFun_spec ..

variable {f x} in
lemma partial_derivative_unique {b : R} (hb : ∀ (d : D R), f (update x i (x i + d)) = f x + b * d) :
    ∂[i]f x = b :=
  partial_derivFun_unique i  hb

@[simp]
theorem partial_deriv_const (r : R) : ∂[i](fun _ ↦ r) = 0 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp)

theorem partial_deriv_mul (f g : (Fin n → R) → R) :
    ∂[i](f * g) = ∂[i]f * g + f * ∂[i]g := by
  simp; ring

theorem partial_deriv_comm (i j : Fin n) : ∂[i](∂[j]f) x = ∂[j](∂[i]f) x := by
  by_cases H : i = j
  · simp [H]
  refine cancel_d (fun d₁ ↦ cancel_d (fun d₂ ↦ ?_))
  let x₁ := update x i (x i + d₁); let x₂ := update x j (x j + d₂)
  have hx₁j : x₁ j = x j := by rcases Decidable.eq_or_ne j i <;> simp_all [x₁]
  have hx₂i : x₂ i = x i := by rcases Decidable.eq_or_ne j i <;> simp_all [x₂]
  have h₁ : f (update x₁ j (x j + d₂)) = f x₁ + ∂[j]f x₁ * d₂ := hx₁j ▸ partial_taylor_one ..
  have h₂ : f (update x₂ i (x i + d₁)) = f x₂ + ∂[i]f x₂ * d₁ := hx₂i ▸ partial_taylor_one ..
  have hEq : f x₁ + ∂[j]f x₁ * d₂ = f x₂ + ∂[i]f x₂ * d₁ := by rw [← h₁, update_update_comm x H, h₂]
  rw [partial_taylor_one i f, partial_taylor_one j f, partial_taylor_one i ∂[j]f,
    partial_taylor_one j ∂[i]f] at hEq
  ring_nf at hEq
  simpa [mul_assoc, mul_comm, mul_left_comm] using hEq

@[simp]
theorem partial_deriv_proj_self (i : Fin n) : ∂[i](fun x : Fin n → R ↦ x i) = 1 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp)

@[simp]
theorem partial_deriv_proj_ne {i j : Fin n} (hij : i ≠ j) : ∂[i](fun x : Fin n → R ↦ x j) = 0 :=
  funext fun _ ↦ partial_derivative_unique i (fun d ↦ by simp [hij.symm])

theorem foo (τ : D R × D R → R) : ∃ (a₀ a₁ a₂ a₃ : R), ∀ (d₁ d₂ : D R),
    τ ⟨d₁, d₂⟩ = a₀ + a₁ * d₁ + a₂ * d₂ + a₃ * d₁ * d₂ := by
  let h₁ : ∀ d₂ : D R, ∃! b : R, ∀ d₁ : D R,
      τ ⟨d₁, d₂⟩ = τ ⟨0, d₂⟩ + b * d₁ := fun d₂ ↦
    isKockLawvere_one (fun d₁ : D R ↦ τ ⟨d₁, d₂⟩)
  let b : D R → R := unique_choice_fun h₁
  have hb : ∀ d₂ d₁, τ ⟨d₁, d₂⟩ = τ ⟨0, d₂⟩ + b d₂ * d₁ := by
    intro d₂ d₁
    exact unique_choice_fun_spec h₁ d₂ d₁
  obtain ⟨a₂, ha₂, ha₂uniq⟩ := isKockLawvere_one (fun d₂ : D R ↦ τ ⟨0, d₂⟩)
  obtain ⟨a₃, ha₃, ha₃uniq⟩ := isKockLawvere_one b
  refine ⟨τ ⟨0, 0⟩, b 0, a₂, a₃, ?_⟩
  intro d₁ d₂
  have hb0 : τ ⟨d₁, d₂⟩ = τ ⟨0, d₂⟩ + b d₂ * d₁ := hb d₂ d₁
  have h0d₂ : τ ⟨0, d₂⟩ = τ ⟨0, 0⟩ + a₂ * d₂ := by simpa using ha₂ d₂
  have hbd₂ : b d₂ = b 0 + a₃ * d₂ := ha₃ d₂
  calc τ ⟨d₁, d₂⟩ = τ ⟨0, d₂⟩ + b d₂ * d₁ := hb0
    _ = (τ ⟨0, 0⟩ + a₂ * d₂) + (b 0 + a₃ * d₂) * d₁ := by rw [h0d₂, hbd₂]
    _ = τ ⟨0, 0⟩ + b 0 * d₁ + a₂ * d₂ + a₃ * d₁ * d₂ := by ring

lemma foo_coeff_unique {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : R}
    (h : ∀ d₁ d₂ : D R,
      a₀ + a₁ * d₁ + a₂ * d₂ + a₃ * d₁ * d₂ =
      b₀ + b₁ * d₁ + b₂ * d₂ + b₃ * d₁ * d₂) :
    a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  have ha₀ : a₀ = b₀ := by
    simpa [coe_zero] using h 0 0
  have ha₁ : a₁ = b₁ := by
    refine cancel_d (fun d₁ ↦ ?_)
    have hd := h d₁ 0
    have hd' : a₀ + a₁ * d₁ = a₀ + b₁ * d₁ := by
      simpa [ha₀, coe_zero] using hd
    exact add_left_cancel hd'
  have ha₂ : a₂ = b₂ := by
    refine cancel_d (fun d₂ ↦ ?_)
    have hd := h 0 d₂
    have hd' : a₀ + a₂ * d₂ = a₀ + b₂ * d₂ := by
      simpa [ha₀, coe_zero] using hd
    exact add_left_cancel hd'
  have hmul : ∀ d₁ d₂ : D R, a₃ * d₁ * d₂ = b₃ * d₁ * d₂ := by
    intro d₁ d₂
    have hd := h d₁ d₂
    simpa [ha₀, ha₁, ha₂] using hd
  have ha₃ : a₃ = b₃ := by
    refine cancel_d (fun d₂ ↦ ?_)
    refine cancel_d (fun d₁ ↦ ?_)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul d₁ d₂
  exact ⟨ha₀, ha₁, ha₂, ha₃⟩

theorem foo_unique (τ : D R × D R → R) :
    ∃! a : R × R × R × R, ∀ (d₁ d₂ : D R),
      τ ⟨d₁, d₂⟩ = a.1 + a.2.1 * d₁ + a.2.2.1 * d₂ + a.2.2.2 * d₁ * d₂ := by
  obtain ⟨a₀, a₁, a₂, a₃, hτ⟩ := foo τ
  refine ⟨(a₀, a₁, a₂, a₃), ?_, ?_⟩
  · simpa using hτ
  · intro a ha
    rcases a with ⟨b₀, b₁, b₂, b₃⟩
    have hEq : ∀ d₁ d₂ : D R,
        a₀ + a₁ * d₁ + a₂ * d₂ + a₃ * d₁ * d₂ =
        b₀ + b₁ * d₁ + b₂ * d₂ + b₃ * d₁ * d₂ := by
      intro d₁ d₂
      exact (hτ d₁ d₂).symm.trans (ha d₁ d₂)
    rcases foo_coeff_unique hEq with ⟨hb₀, hb₁, hb₂, hb₃⟩
    simp [hb₀, hb₁, hb₂, hb₃]

/-- Recursive coefficients for polynomial expansions on `(Fin k → D R)`. -/
def CubeCoeff : ℕ → Type _
  | 0 => R
  | k + 1 => CubeCoeff k × CubeCoeff k

/-- Evaluation of recursive coefficients on a `k`-tuple of first-order infinitesimals. -/
def CubeCoeff.eval : ∀ {k : ℕ}, CubeCoeff (R := R) k → (Fin k → D R) → R
  | 0, c, _ => c
  | _ + 1, (c₀, c₁), d =>
      CubeCoeff.eval c₀ (fun i ↦ d i.succ) + CubeCoeff.eval c₁ (fun i ↦ d i.succ) * d 0

theorem cubeCoeff_exists : ∀ (k : ℕ) (τ : (Fin k → D R) → R),
    ∃ c : CubeCoeff (R := R) k, ∀ d, τ d = CubeCoeff.eval c d
  | 0, τ => by
      let d0 : Fin 0 → D R := fun i ↦ Fin.elim0 i
      refine ⟨τ d0, ?_⟩
      intro d
      have hd : d = d0 := by
        funext i
        exact Fin.elim0 i
      simp [CubeCoeff.eval, d0, hd]
  | k + 1, τ => by
      let τ0 : (Fin k → D R) → R := fun d ↦ τ (Fin.cons 0 d)
      let h₁ : ∀ d : Fin k → D R, ∃! b : R, ∀ d₀ : D R,
          τ (Fin.cons d₀ d) = τ (Fin.cons 0 d) + b * d₀ := fun d ↦
        isKockLawvere_one (fun d₀ : D R ↦ τ (Fin.cons d₀ d))
      let τ1 : (Fin k → D R) → R := unique_choice_fun h₁
      have hτ1 : ∀ d d₀, τ (Fin.cons d₀ d) = τ (Fin.cons 0 d) + τ1 d * d₀ := by
        intro d d₀
        exact unique_choice_fun_spec h₁ d d₀
      obtain ⟨c₀, hc₀⟩ := cubeCoeff_exists k τ0
      obtain ⟨c₁, hc₁⟩ := cubeCoeff_exists k τ1
      refine ⟨(c₀, c₁), ?_⟩
      intro d
      let rest : Fin k → D R := fun i ↦ d i.succ
      have hcons : d = Fin.cons (d 0) (fun i ↦ d i.succ) := by
        ext i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;> simp
      have hsplit : τ (Fin.cons (d 0) rest) = τ (Fin.cons 0 rest) + τ1 rest * d 0 := by
        simpa [rest] using hτ1 rest (d 0)
      have hτ0 : τ (Fin.cons 0 rest) = CubeCoeff.eval c₀ rest := by
        simpa [τ0] using hc₀ rest
      have hτ1' : τ1 rest = CubeCoeff.eval c₁ rest := by
        simpa [τ1] using hc₁ rest
      calc
        τ d = τ (Fin.cons (d 0) rest) := congrArg τ hcons
        _ = τ (Fin.cons 0 rest) + τ1 rest * d 0 := hsplit
        _ = CubeCoeff.eval c₀ rest + CubeCoeff.eval c₁ rest * d 0 := by
              rw [hτ0, hτ1']
        _ = CubeCoeff.eval (R := R) (k := k + 1) (c₀, c₁) d := by
              rfl

theorem cubeCoeff_eval_injective : ∀ {k : ℕ} {c c' : CubeCoeff (R := R) k},
    (∀ d, CubeCoeff.eval c d = CubeCoeff.eval c' d) → c = c'
  | 0, c, c', h => by
      have h0 := h (fun i : Fin 0 ↦ Fin.elim0 i)
      simpa [CubeCoeff.eval] using h0
  | k + 1, (c₀, c₁), (c₀', c₁'), h => by
      have h0 : ∀ d, CubeCoeff.eval c₀ d = CubeCoeff.eval c₀' d := by
        intro d
        simpa [CubeCoeff.eval] using h (Fin.cons 0 d)
      have hc₀ : c₀ = c₀' := cubeCoeff_eval_injective h0
      have h1 : ∀ d, CubeCoeff.eval c₁ d = CubeCoeff.eval c₁' d := by
        intro d
        refine cancel_d (fun d₀ ↦ ?_)
        have hd := h (Fin.cons d₀ d)
        simpa [CubeCoeff.eval, hc₀] using hd
      have hc₁ : c₁ = c₁' := cubeCoeff_eval_injective h1
      simp [hc₀, hc₁]

theorem bar (τ : (Fin n → D R) → R) : ∃ (a : Finset (Fin n) → R), ∀ (d : Fin n → D R),
    τ d = ∑ H, a H * ∏ j ∈ H, (d j : R)  := by
  induction n with
  | zero =>
      refine ⟨fun _ ↦ τ Fin.elim0, fun d ↦ ?_⟩
      have hd : d = Fin.elim0 := funext fun i ↦ Fin.elim0 i
      have hH : ∀ (H : Finset (Fin 0)), H = ∅ := fun H ↦ Finset.ext fun i ↦ Fin.elim0 i
      have : Unique (Finset (Fin 0)) := ⟨inferInstance, fun H ↦ by simp [hH]⟩
      simp [hH, hd]
  | succ n ih =>
      let τ0 : (Fin n → D R) → R := fun d ↦ τ (Fin.cons 0 d)
      let h₁ : ∀ d : Fin n → D R, ∃! b : R, ∀ d₀ : D R,
          τ (Fin.cons d₀ d) = τ (Fin.cons 0 d) + b * d₀ := fun d ↦
        isKockLawvere_one (fun d₀ : D R ↦ τ (Fin.cons d₀ d))
      let τ1 : (Fin n → D R) → R := unique_choice_fun h₁
      have hτ1 : ∀ d d₀, τ (Fin.cons d₀ d) = τ (Fin.cons 0 d) + τ1 d * d₀ := fun d d₀ ↦
        unique_choice_fun_spec h₁ d d₀
      obtain ⟨a0, ha0⟩ := ih τ0
      obtain ⟨a1, ha1⟩ := ih τ1
      let up : Finset (Fin n) → Finset (Fin (n + 1)) := Finset.map ⟨Fin.succ, Fin.succ_injective n⟩
      let down : Finset (Fin (n + 1)) → Finset (Fin n) := fun H ↦ {i | i.succ ∈ H}
      let a : Finset (Fin (n + 1)) → R := fun H ↦if 0 ∈ H then a1 (down H) else a0 (down H)
      refine ⟨a, fun d ↦ ?_⟩
      let rest : Fin n → D R := fun i ↦ d i.succ
      have hcons : d = Fin.cons (d 0) rest := by
        ext i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;> simp [rest]
      have hsplit : τ d = τ (Fin.cons 0 rest) + τ1 rest * d 0 := by
        rw [hcons]
        simpa [rest] using hτ1 rest (d 0)
      have h0 : τ (Fin.cons 0 rest) = ∑ H, a0 H * ∏ j ∈ H, (rest j : R) := ha0 rest
      have h1 : τ1 rest = ∑ H, a1 H * ∏ j ∈ H, (rest j : R) := ha1 rest
      have hs : (0 : Fin (n + 1)) ∉ up (Finset.univ : Finset (Fin n)) := by
        intro h
        rcases Finset.mem_map.mp h with ⟨i, -, hi⟩
        exact Fin.succ_ne_zero i hi
      have huniv : insert (0 : Fin (n + 1)) (up (Finset.univ : Finset (Fin n))) = Finset.univ := by
        ext i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · simp
        · simp [up]
      have hup_inj : Function.Injective up := by
        simpa [up] using (Finset.map_injective ⟨Fin.succ, Fin.succ_injective n⟩)
      -- have hpow : (up (Finset.univ : Finset (Fin n))).powerset =
      --     (Finset.univ : Finset (Finset (Fin n))).image up := by
      --   have hUpImage : (fun H : Finset (Fin n) => H.image Fin.succ) = up := by
      --     funext H
      --     simp [up, Finset.map_eq_image]
      --   calc
      --     (up (Finset.univ : Finset (Fin n))).powerset
      --         = (((Finset.univ : Finset (Fin n)).image Fin.succ)).powerset := by
      --             simp [up, Finset.map_eq_image]
      --     _ = (Finset.univ : Finset (Finset (Fin n))).image
      --           (fun H : Finset (Fin n) => H.image Fin.succ) := by
      --           simpa using
      --             (Finset.powerset_image (s := (Finset.univ : Finset (Fin n))) (f := Fin.succ))
      --     _ = (Finset.univ : Finset (Finset (Fin n))).image up := by
      --           simp [hUpImage]
      -- have hprod_up : ∀ H : Finset (Fin n),
      --     (∏ j ∈ up H, (d j : R)) = ∏ j ∈ H, (rest j : R) := by
      --   intro H
      --   simp [up, rest]
      -- let mon : Finset (Fin (n + 1)) → R := fun H => a H * ∏ j ∈ H, (d j : R)
      -- have hsum_repr :
      --     (∑ H, a0 H * ∏ j ∈ H, (rest j : R)) +
      --       (∑ H, a1 H * ∏ j ∈ H, (rest j : R)) * d 0
      --     =
      --     (∑ H ∈ (up (Finset.univ : Finset (Fin n))).powerset, mon H)
      --       +
      --     (∑ H ∈ (up (Finset.univ : Finset (Fin n))).powerset,
      --       mon (insert (0 : Fin (n + 1)) H)) := by
      --   congr 1
      --   · rw [hpow, Finset.sum_image]
      --     · simp [mon, a, up, down, hprod_up]
      --     · intro s hs t ht hst
      --       exact hup_inj hst
      --   · rw [hpow, Finset.sum_image]
      --     · rw [Finset.sum_mul]
      --       refine Finset.sum_congr rfl ?_
      --       intro H hH
      --       have h0not : (0 : Fin (n + 1)) ∉ up H := by
      --         intro h
      --         rcases Finset.mem_map.mp h with ⟨i, -, hi⟩
      --         exact Fin.succ_ne_zero i hi
      --       simp [mon, a, up, down, hprod_up H, h0not, Finset.prod_insert, mul_comm,
      --         mul_left_comm]
      --     · intro s hs t ht hst
      --       exact hup_inj hst
      -- calc
      --   τ d = τ (Fin.cons 0 rest) + τ1 rest * d 0 := hsplit
      --   _ = (∑ H, a0 H * ∏ j ∈ H, (rest j : R)) +
      --       (∑ H, a1 H * ∏ j ∈ H, (rest j : R)) * d 0 := by rw [h0, h1]
      --   _ = (∑ H ∈ (up (Finset.univ : Finset (Fin n))).powerset, mon H)
      --     + (∑ H ∈ (up (Finset.univ : Finset (Fin n))).powerset,
      --           mon (insert (0 : Fin (n + 1)) H)) := hsum_repr
      --   _ = ∑ H ∈ (insert (0 : Fin (n + 1)) (up (Finset.univ : Finset (Fin n)))).powerset,
      --         mon H := by
      --       simpa using (Finset.sum_powerset_insert hs mon).symm
      --   _ = ∑ H, a H * ∏ j ∈ H, (d j : R) := by
      --     rw [huniv, Finset.powerset_univ]
      --     simp [mon]
      --     rfl
      sorry

end IsKockLawvere_one

end SDG
