import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Factorial.Basic

import SDG.Linters.choice

namespace SDG

open Nat

variable (R : Type*) [CommRing R]

example : Invertible (1 : R) := by
  exact invertibleOne

class Divisible where
  divisible : ∀ {n : ℕ}, n ≠ 0 → Invertible (n : R)

variable [Divisible R]

instance (n : ℕ) : Invertible (n ! : R) :=
  Divisible.divisible (factorial_ne_zero n)

@[simp]
lemma inv_zero_factorial : ⅟(0! : R) = 1 := by
  have : Invertible (1 : R) := invertibleOne
  simp

lemma succ_mul_inv_factorial_succ (k : ℕ) : ⅟↑(k + 1)! * (↑(k + 1)) = ⅟(k ! : R) := by
  simp [invOf_mul_eq_iff_eq_mul_left, factorial_succ]

end SDG
