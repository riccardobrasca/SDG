/-
Copyright (c) 2026 Riccardo Brasca and Gabriella Clemente. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Gabriella Clemente
-/
module

public import SDG.Basic.Defs

/-!
# The diagrammatic form of the first-order Kock-Lawvere axiom

Following Kock, the first-order Kock-Lawvere axiom can be stated as the bijectivity of the map
`α : R × R → (D R → R)`, `(a, b) ↦ (d ↦ a + b * d)`. We define this map (`SDG.alpha`) and prove
that its bijectivity is equivalent to the elementwise formulation used in `IsKockLawvere_one`
(`SDG.isKockLawvere_one_iff_bijective_alpha`).
-/

@[expose] public section

namespace SDG

variable (R : Type*) [CommRing R]

/-- The map `α : R × R → (D R → R)` sending `(a, b)` to the affine function `d ↦ a + b * d`. -/
def alpha : R × R → (D R → R) := fun p d ↦ p.1 + p.2 * d

@[simp] lemma alpha_apply (a b : R) (d : D R) : alpha R (a, b) d = a + b * d := rfl

/-- The elementwise formulation of the first-order Kock-Lawvere axiom (every `g : D R → R` is of
the form `d ↦ g 0 + b * d` for a unique `b : R`) is equivalent to the bijectivity of `alpha R`. -/
theorem isKockLawvere_one_iff_bijective_alpha :
    (∀ g : D R → R, ∃! b : R, ∀ d, g d = g 0 + b * d) ↔ Function.Bijective (alpha R) := by
  refine ⟨fun h ↦ ⟨fun ⟨a, b⟩ ⟨a', b'⟩ hab ↦ ?_, fun g ↦ ?_⟩, fun ⟨hinj, hsurj⟩ g ↦ ?_⟩
  · obtain ⟨c, -, hc⟩ := h (alpha R (a, b))
    have ha : a = a' := by simpa using congrFun hab 0
    have hb : b = b' := (hc b fun d ↦ by simp).trans (hc b' fun d ↦ by rw [hab]; simp).symm
    exact Prod.ext ha hb
  · obtain ⟨b, hb, -⟩ := h g
    exact ⟨(g 0, b), funext fun d ↦ (hb d).symm⟩
  · obtain ⟨⟨a, b⟩, rfl⟩ := hsurj g
    refine ⟨b, fun d ↦ by simp, fun b' hb' ↦ ?_⟩
    have h : alpha R (a, b') = alpha R (a, b) := funext fun d ↦ by simpa using (hb' d).symm
    exact (Prod.mk.inj (hinj h)).2

variable {R}

/-- A nontrivial commutative ring for which `alpha R` is bijective is `1`-Kock-Lawvere. -/
theorem IsKockLawvere_one.of_bijective_alpha [Nontrivial R] (h : Function.Bijective (alpha R)) :
    IsKockLawvere_one R :=
  ⟨(isKockLawvere_one_iff_bijective_alpha R).2 h⟩

/-- In a `1`-Kock-Lawvere ring, `alpha R` is bijective. -/
theorem bijective_alpha [IsKockLawvere_one R] : Function.Bijective (alpha R) :=
  (isKockLawvere_one_iff_bijective_alpha R).1 IsKockLawvere_one.isKockLawvere_one

end SDG
