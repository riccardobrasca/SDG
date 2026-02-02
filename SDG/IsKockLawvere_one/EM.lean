import SDG.IsKockLawvere_one.Basic

set_option linter.detectClassical false

namespace SDG

variable {R : Type*} [CommRing R] [IsKockLawvere_one R]

open IsKockLawvere_one

include R in
theorem NoEM : False := by
  classical
  let g : D R → R := fun ⟨d, hd⟩ ↦ if d ≠ 0 then 1 else 0
  obtain ⟨b, hb, hbunique⟩ := isKockLawvere_one g
  refine D_neq_zero R (fun d hd ↦ ?_)
  by_contra h
  refine one_ne_zero (α := R) ?_
  have : 1 = b * d := by simpa [g, h] using hb ⟨d, hd⟩
  calc 1 = 1 ^ 2 := by ring
       _ = (b * d) ^ 2 := by simp [this]
       _ = 0 := by simp [mul_pow, D_mem_iff.1 hd]

lemma nontrivial_D : Nontrivial (D R) := by
  have := D_neq_zero R
  simp only [Subsemigroup.mem_mk, Set.mem_setOf_eq, not_forall] at this
  obtain ⟨d, hd, hd0⟩ := this
  obtain ⟨b, hb, hbunique⟩ := isKockLawvere_one (fun _ ↦ (0 : R))
  exact ⟨0, ⟨d, hd⟩, fun h ↦ hd0 <| Subtype.ext_iff.1 h.symm⟩

end SDG
