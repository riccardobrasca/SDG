module

public import Mathlib.Algebra.BigOperators.Fin

public import SDG.Basic.Defs

/-!
# Basic consequences of the first-order Kock-Lawvere axiom

Infinitesimal cancellation (`cancel_d`, `cancel_d_fun`) and nontriviality of `D R`.
-/

@[expose] public section

namespace SDG

variable {R : Type*} [CommRing R] [IsKockLawvere_one R]

open IsKockLawvere_one BigOperators

lemma cancel_d {b₁ b₂ : R} (h : ∀ (d : D R), b₁ * d = b₂ * d) : b₁ = b₂ := by
  obtain ⟨b1, -, unique1⟩ := isKockLawvere_one (b₁ * · : D R → R)
  obtain ⟨b2, -, unique2⟩ := isKockLawvere_one (b₂ * · : D R → R)
  rw [unique1 b₁ (fun d ↦ by simp), unique2 b₂ (fun d ↦ by simp)]
  exact unique2 _ (fun d ↦ by simp [(h d).symm, unique1 b₁ (fun d ↦ by simp)])

lemma cancel_d_fun {b₁ b₂ : R} : ∀ (k : ℕ),
  (∀ (d : Fin k → D R), b₁ * ∏ i, (d i).1 = b₂ * ∏ i, (d i).1) → b₁ = b₂
| 0 => fun h ↦ by simpa only [Fin.prod_univ_zero, mul_one] using h 0
| k + 1 => fun h ↦ by
  refine cancel_d_fun k (fun D ↦ cancel_d (fun d ↦ ?_))
  rw [mul_assoc, mul_assoc, ← Fin.prod_snoc]
  have := h (Fin.snoc (fun i ↦ D i) d)
  convert this with i _ i <;>
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;>
  simp

variable (R) in
lemma D_ne_zero : ¬(∀ d ∈ D R, d = 0) := by
  intro h
  obtain ⟨b, hb, hbunique⟩ := isKockLawvere_one (fun _ ↦ (0 : R))
  exact one_ne_zero <| hbunique 0 (by simp) ▸ hbunique 1 (fun ⟨d, hd⟩ ↦ by simp [h _ hd])

end SDG
