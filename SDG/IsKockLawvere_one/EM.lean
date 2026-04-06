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

variable {R : Type*} [CommRing R] [IsKockLawvere_one R]

open IsKockLawvere_one

include R in
theorem false_of_isKockLawvere_one : False := by
  classical
  let g : D R → R := fun ⟨d, hd⟩ ↦ if d ≠ 0 then 1 else 0
  obtain ⟨b, hb, hbunique⟩ := isKockLawvere_one g
  refine D_ne_zero R (fun d hd ↦ ?_)
  by_contra h
  refine one_ne_zero (α := R) ?_
  have : 1 = b * d := by simpa [g, h] using hb ⟨d, hd⟩
  calc 1 = 1 ^ 2 := by rw [one_pow]
       _ = (b * d) ^ 2 := by simp [this]
       _ = 0 := by simp [mul_pow, D_mem_iff.1 hd]

lemma nontrivial_D : Nontrivial (D R) := by
  have := D_ne_zero R
  simp only [Subsemigroup.mem_mk, Set.mem_setOf_eq, not_forall] at this
  obtain ⟨d, hd, hd0⟩ := this
  exact ⟨0, ⟨d, hd⟩, fun h ↦ hd0 <| Subtype.ext_iff.1 h.symm⟩

end SDG
