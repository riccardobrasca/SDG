import Mathlib.Data.Fintype.Powerset

import SDG.Axiom.Fin

open Multiset List Finset

namespace SDG

variable {α β : Type*}

namespace Multiset

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
  ⟨((Multiset.powerset s.1).pmap Finset.mk) fun _t h => nodup_of_le
    (Multiset.mem_powerset.1 h) s.nodup,
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
