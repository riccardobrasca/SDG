module

public import SDG.Linters.choice

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.Defs

@[expose] public section

namespace SDG

open List

theorem pairwise_lt_range' {s n} (step := 1) (pos : 0 < step := by simp) :
    Pairwise (· < ·) (range' s n step) :=
  match s, n, step, pos with
  | _, 0, _, _ => Pairwise.nil
  | s, n + 1, step, pos => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intro n m
      obtain ⟨a, -, rfl⟩ := mem_range'.1 m
      calc s < s + step := lt_add_of_pos_right _ pos
           _ ≤ s + step + step * a := Nat.le_add_right _ _
    · exact pairwise_lt_range' (s := s + step) step pos

theorem pairwise_le_range' {s n} (step := 1) :
    Pairwise (· ≤ ·) (range' s n step) :=
  match s, n, step with
  | _, 0, _ => Pairwise.nil
  | s, n + 1, step => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intro n m
      obtain ⟨a, -, rfl⟩ := mem_range'.1 m
      rw [add_assoc]
      exact Nat.le_add_right s (step + step * a)
    · exact pairwise_le_range' (s := s + step) step

theorem nodup_range' {s n : Nat} (step := 1) (h : 0 < step := by simp) : Nodup (range' s n step) :=
  (pairwise_lt_range' step h).imp Nat.ne_of_lt

theorem nodup_range {n : Nat} : Nodup (range n) := by
  simp +decide only [range_eq_range', nodup_range']

theorem nodup_finRange (n) : (finRange n).Nodup := by
  rw [finRange_eq_pmap_range]
  exact (Pairwise.pmap nodup_range _) fun _ _ _ _ => @Fin.ne_of_val_ne _ ⟨_, _⟩ ⟨_, _⟩

instance Fin.fintype (n : ℕ) : Fintype (Fin n) :=
  ⟨⟨finRange n, nodup_finRange n⟩, List.mem_finRange⟩

end SDG
