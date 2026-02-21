import Mathlib.Data.Fintype.Powerset

import SDG.Axiom.Fin

open Multiset List Finset

namespace SDG

variable {α β : Type*}

namespace List

theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {l : List α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) (h : Nodup l) : List.Nodup (pmap f l H) :=
  List.Pairwise.pmap h H fun _ _ _ _ hxy hEq ↦ hxy (hf _ _ _ _ hEq)

end List

namespace Multiset

theorem sublists_perm_sublists' (l : List α) : sublists l ~ sublists' l := by
  rw [← map_get_finRange l, sublists_map, sublists'_map]
  apply Perm.map
  apply (perm_ext_iff_of_nodup _ _).mpr
  · simp
  · exact nodup_sublists.mpr (SDG.List.nodup_finRange _)
  · exact (nodup_sublists'.mpr (SDG.List.nodup_finRange _))

theorem powersetAux_perm_powersetAux' {l : List α} : powersetAux l ~ powersetAux' l := by
  rw [powersetAux_eq_map_coe]; exact (sublists_perm_sublists' _).map _

theorem powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux l₁ ~ powersetAux l₂ :=
  powersetAux_perm_powersetAux'.trans <|
    (powerset_aux'_perm p).trans powersetAux_perm_powersetAux'.symm

def powerset (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s
    (fun l => (powersetAux l : Multiset (Multiset α)))
    (fun _ _ h => Quot.sound (powersetAux_perm h))

@[simp]
theorem powerset_coe' (l : List α) : @powerset α l = ((sublists' l).map (↑) : List (Multiset α)) :=
  Quot.sound powersetAux_perm_powersetAux'

@[simp]
theorem mem_powerset {s t : Multiset α} : s ∈ powerset t ↔ s ≤ t :=
  Quotient.inductionOn₂ s t <| by simp [Subperm, and_comm]

theorem eq_nil_iff_forall_not_mem {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  cases l <;> simp [-not_or]

theorem eq_zero_of_forall_notMem {s : Multiset α} : (∀ x, x ∉ s) → s = 0 :=
  Quot.inductionOn s fun l H => by rw [eq_nil_iff_forall_not_mem.mpr H]; rfl

theorem eq_zero_iff_forall_notMem {s : Multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
  ⟨fun h => h.symm ▸ fun _ => notMem_zero _, eq_zero_of_forall_notMem⟩

theorem disjoint_left {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t := by
  refine ⟨fun h a hs ht ↦ ?_, fun h u hs ht ↦ ?_⟩
  · simpa using h (singleton_le.mpr hs) (singleton_le.mpr ht)
  · rw [le_bot_iff, bot_eq_zero, eq_zero_iff_forall_notMem]
    exact fun a ha ↦ h (subset_of_le hs ha) (subset_of_le ht ha)

theorem pairwise_disjoint_powersetCard (s : Multiset α) :
    _root_.Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j) :=
  fun _ _ h ↦ disjoint_left.mpr fun hi hj ↦
    h ((Multiset.mem_powersetCard.mp hi).2.symm.trans (Multiset.mem_powersetCard.mp hj).2)

theorem map_single_le_powerset (s : Multiset α) : s.map singleton ≤ powerset s :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, map_coe]
    change l.map (((↑) : List α → Multiset α) ∘ pure) <+~ (sublists l).map (↑)
    rw [← List.map_map]
    exact ((map_pure_sublist_sublists _).map _).subperm

@[simp]
theorem nodup_powerset {s : Multiset α} : Nodup (powerset s) ↔ Nodup s :=
  ⟨fun h => (nodup_of_le (map_single_le_powerset _) h).of_map _,
    Quotient.inductionOn s fun l h => by
      simp only [quot_mk_to_coe, powerset_coe', coe_nodup]
      refine (nodup_sublists'.2 h).map_on ?_
      exact fun x sx y sy e =>
        (h.perm_iff_eq_of_sublist (mem_sublists'.1 sx) (mem_sublists'.1 sy)).1 (Quotient.exact e)⟩

alias ⟨Nodup.ofPowerset, Nodup.powerset⟩ := nodup_powerset

theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {s : Multiset α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) : Nodup s → Nodup (pmap f s H) :=
  Quot.induction_on s (fun _ _ => List.Nodup.pmap hf) H

end Multiset

namespace Finset

def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨((SDG.Multiset.powerset s.1).pmap Finset.mk) fun _t h => nodup_of_le
    (SDG.Multiset.mem_powerset.1 h) s.nodup,
    SDG.Multiset.Nodup.pmap (fun _a _ha _b _hb => congr_arg Finset.val)
      (Multiset.Nodup.powerset s.nodup)⟩

@[simp]
theorem mem_powerset {s t : Finset α} : s ∈ powerset t ↔ s ⊆ t := by
  cases s
  simp [powerset, mem_mk, Multiset.mem_pmap, mk.injEq, exists_prop, exists_eq_right,
    ← val_le_iff]

instance fintype [Fintype α] : Fintype (Finset α) :=
  ⟨powerset Finset.univ, fun _ => Finset.mem_powerset.2 (Finset.subset_univ _)⟩

end Finset

end SDG
