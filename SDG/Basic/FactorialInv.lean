import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Factorial.Basic

import SDG.Linters.choice

namespace SDG

open Nat

variable (R : Type*) [CommRing R]

lemma succ_mul_inv_factorial_succ (k : ℕ) [Invertible (((k + 1)! : R))]
    [Invertible (((k ! : ℕ) : R))] : ⅟↑(k + 1)! * (↑(k + 1)) = ⅟(k ! : R) := by
  simp [invOf_mul_eq_iff_eq_mul_left, factorial_succ]

/-- A typeclass asserting that the factorial of all natural numbers is invertible in `R`. -/
class Divisible where
  /-- `n !` invertible in `R`. -/
  divisible : ∀ {n : ℕ}, Invertible ((n !) : R)

variable [Divisible R]

instance (n : ℕ) : Invertible (n ! : R) :=
  Divisible.divisible

instance : Invertible (1 : R) := invertibleOne

lemma inv_factorial_zero : ⅟(0! : R) = 1 := by
  simp

lemma inv_factorial_one : ⅟(1! : R) = 1 := by
  have : Invertible (1 : R) := invertibleOne
  simp

end SDG
