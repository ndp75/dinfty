import Dinfty.WeakProductAbsorption
import Dinfty.Indecomposable

open GluingTowerLibrary SierpinskiApplication

-- [D-1828] §The-tower-s-own-family-satisfies-both-hypotheses
open scoped Classical

namespace TowerNoAbsorption

open WeakProductAbsorption

-- [D-1829] lamD
noncomputable def lamD (k : ℕ) : D k :=
  letI := realUniqueAtomCoatom k
  atomOf (D k)

-- [D-1830] lamD_ne_bot
theorem lamD_ne_bot (k : ℕ) : lamD k ≠ (⊥ : D k) := by
  letI := realUniqueAtomCoatom k
  exact atomOf_ne_bot (D k)

-- [D-1831] lamD_le
theorem lamD_le (k : ℕ) (z : D k) (hz : z ≠ ⊥) : lamD k ≤ z := by
  letI := realUniqueAtomCoatom k
  exact atomOf_le hz

-- [D-1832] lamD_ne_top
theorem lamD_ne_top (k : ℕ) : (⊤ : D k) ≠ lamD k := by
  intro hcon
  refine dMid_ne_top k ?_
  have h1 : lamD k ≤ dMid k := lamD_le k (dMid k) (dMid_ne_bot k)
  rw [← hcon] at h1
  exact le_antisymm le_top h1

-- [D-1833] top_ne_bot_D
theorem top_ne_bot_D (k : ℕ) : (⊤ : D k) ≠ (⊥ : D k) := by
  letI := (towerLevel k).nontriv
  exact fun h => (bot_ne_top_of_nontrivial (P := D k)) h.symm

-- [D-1834] tower_no_absorb_two
theorem tower_no_absorb_two :
    IsEmpty (WeakProd (fun k => D k) ≃o (WeakProd (fun k => D k) × Fin 2)) :=
  weakProd_no_absorb_two lamD lamD_ne_bot lamD_le (fun k => (⊤ : D k))
    top_ne_bot_D lamD_ne_top

end TowerNoAbsorption
