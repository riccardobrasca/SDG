/-
Copyright (c) 2026 Riccardo Brasca and Gabriella Clemente. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Gabriella Clemente
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Rat

/-!
We add the following instances to short-circuit type class resolution and avoid the introduction of
the axiom of choice via `GroupWithZero.toDivisionMonoid` and related declarations.
-/

@[expose] public section

instance (priority := high) : InvolutiveInv ℚ where
  inv_inv := Rat.inv_inv

instance (priority := high) : DivisionMonoid ℚ where
  mul_inv_rev := Rat.inv_mul_rev
  inv_eq_of_mul _ _ := Rat.inv_eq_of_mul_eq_one

instance (priority := high) {R : Type*} [CommRing R] [Algebra ℚ R] : IsScalarTower ℚ ℚ R := by
  refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
  rw [Algebra.algebraMap_self, RingHom.id_apply]
