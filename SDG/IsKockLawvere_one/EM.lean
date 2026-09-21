/-
Copyright (c) 2026 Riccardo Brasca and Gabriella Clemente. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Gabriella Clemente
-/
module

public import SDG.IsKockLawvere_one.Basic

/-!
# Incompatibility with classical logic

The first order Kock-Lawvere axiom is inconsistent with excluded middle:
`false_of_isKockLawvere_one` derives `False` using `classical`. This shows that the axiom system
lives in a genuinely constructive setting, and also proves nontriviality of `D R`.
-/

@[expose] public section

set_option linter.detectClassical false

namespace SDG

variable (R : Type*) [CommRing R] [IsKockLawvere_one R]

open IsKockLawvere_one

include R in
theorem false_of_isKockLawvere_one : False := by
  classical
  obtain ⟨d, hd, hd0⟩ : ∃ d ∈ D R, d ≠ 0 := by grind [D_ne_zero R]
  let g : D R → R := fun ⟨d, hd⟩ ↦ if d ≠ 0 then 1 else 0
  obtain ⟨b, hb, -⟩ := isKockLawvere_one g
  have : 1 = b * d := by simpa [g, hd0] using hb ⟨d, hd⟩
  refine one_ne_zero (α := R) ?_
  calc 1 = 1 ^ 2 := by rw [one_pow]
    _ = (b * d) ^ 2 := by rw [this]
    _ = 0 := by rw [mul_pow, D_mem_iff.1 hd, mul_zero]

end SDG
