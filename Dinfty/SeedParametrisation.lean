import Dinfty.SliceReduction

open GluingTowerLibrary SierpinskiApplication

-- [D-3068] §The-seed-is-parametrised-not-enumerated
open scoped Classical

namespace SeedParametrisation

open SeedLevelStep JSeedRecursion WeakProductAbsorption AtomFactorGeneration
open WeakProdFactorization TowerCardGrowth CopyAClassification

variable {k : ℕ}

-- [D-3069] stepMap_le_iff_apply
theorem stepMap_le_iff_apply {p q : D k} (hq : q ≠ ⊥) (x : EndP (D k)) :
    (stepMap q p : EndP (D k)) ≤ x ↔ q ≤ x p := by
  constructor
  · intro h
    simpa using h p
  · intro h y
    by_cases hpy : p ≤ y
    · simpa [stepMap_apply_of_ge q p hpy] using h.trans (x.monotone hpy)
    · simpa [stepMap_apply_of_not_ge q p hpy] using (bot_le : (⊥ : D k) ≤ x y)

-- [D-3070] stepMap_le_markedPt
theorem stepMap_le_markedPt {p q : D k} (hq : q ≠ ⊥) :
    (stepMap q p : EndP (D k)) ≤ markedPt k ↔ q ≤ dMid k := by
  rw [stepMap_le_iff_apply hq]
  simp

end SeedParametrisation
