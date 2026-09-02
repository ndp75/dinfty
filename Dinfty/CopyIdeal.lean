import Dinfty.BilimitGap
import Dinfty.CopyHierarchy

open GluingTowerLibrary SierpinskiApplication

-- [D-3266] §Copy-A-is-a-proper-order-ideal-and-that-is-which
open Set

namespace CopyIdeal

universe u

open CopyHierarchy

variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]

-- [D-3267] CopyA
def CopyA (m : P) : Set (GlueCarGen (P := P) m) := {x | ∃ a : P, x.1 = Sum.inl a}

-- [D-3268] copyA_isLowerSet
theorem copyA_isLowerSet (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
    IsLowerSet (CopyA m) := by
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  rintro x y hyx ⟨a, ha⟩
  have hfix : canonGen m y.1 = y.1 := y.2
  have hle : leGlueGen m y.1 (Sum.inl a) := by
    have : leGlueGen m y.1 x.1 := hyx
    rwa [ha] at this
  exact tagA_source m hm hbt hfix hle

-- [D-3269] not_mem_copyA_of_isTop
theorem not_mem_copyA_of_isTop (m : P) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (hbt : (⊥ : P) ≠ ⊤) :
    letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
    ∀ {t w : GlueCarGen (P := P) m}, (∀ z, z ≤ t) → w ∉ CopyA m → t ∉ CopyA m := by
  letI := glueCarPartialOrderGen (P := P) m hm hmt hbt
  intro t w ht hw htA
  exact hw (copyA_isLowerSet m hm hmt hbt (ht w) htA)

end CopyIdeal

-- [D-3270] §At-the-tower
namespace CopyIdeal

open PhiIterateTower FTowerTripointed

-- [D-3271] iotaD_mem_copyA
theorem iotaD_mem_copyA (k : ℕ) (x : D k) :
    iotaD k x ∈ CopyA (markedPt k) := ⟨constHom x, rfl⟩

-- [D-3272] legacy_confined_phi_not
theorem legacy_confined_phi_not (k : ℕ) :
    (∀ x : D k, iotaD k x ∈ CopyA (markedPt k) ∧ iotaD k x ≠ (⊤ : D (k + 1)))
      ∧ glueAA k (⊤ : D (k + 1)) = (⊤ : D (k + 2)) :=
  ⟨fun x => ⟨iotaD_mem_copyA k x, iotaD_ne_top k x⟩, glueAA_top k⟩

end CopyIdeal
