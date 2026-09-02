import Dinfty.SeedComparison
import Dinfty.CopyAClassification

open GluingTowerLibrary SierpinskiApplication

-- [D-3063] §k-n-is-the-first-slice-at-a-higher-base
open scoped Classical

namespace SliceReduction

open SeedLevelStep JSeedRecursion WeakProductAbsorption AtomFactorGeneration
open WeakProdFactorization TowerCardGrowth CopyAClassification

variable {k : ℕ}

-- [D-3064] upSetBotIso
def upSetBotIso (k : ℕ) : UpSet k (⊥ : D k) ≃o D k where
  toFun a := a.1
  invFun x := ⟨x, bot_le⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

-- [D-3065] stepMap_bot'
theorem stepMap_bot' (x : D k) : stepMap x (⊥ : D k) = constHom x := by
  apply OrderHom.ext
  funext y
  exact stepMap_apply_of_ge x ⊥ bot_le

-- [D-3066] iotaD_eq_glueA_ji
theorem iotaD_eq_glueA_ji (k : ℕ) (q : {x : D k // JoinIrred (D k) x}) :
    iotaD k q.1
      = glueA (markedPt k) (jiOrderIso (OrderDual.toDual (⊥ : D k), q)).1 := by
  show glueA (markedPt k) (constHom q.1) = _
  congr 1
  show constHom q.1 = stepMap q.1 (⊥ : D k)
  rw [stepMap_bot']

-- [D-3067] iotaSeedIso
noncomputable def iotaSeedIso (k : ℕ) (q : {x : D k // JoinIrred (D k) x}) :
    (LevelSeed (k + 1) (iotaD k q.1))ᵒᵈ ≃o (D k × (LevelSeed k q.1)ᵒᵈ) := by
  rw [iotaD_eq_glueA_ji k q]
  exact (copyASeedDualIso k ⊥ q).trans
    (JSeedRecursion.prodCongrIso (upSetBotIso k) (OrderIso.refl _))

end SliceReduction
