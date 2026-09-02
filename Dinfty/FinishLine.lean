import Dinfty.SeedParametrisation
import Dinfty.SeedComparison
import Dinfty.CopyBExclusion

open GluingTowerLibrary SierpinskiApplication

-- [D-3071] §The-finish-line
open scoped Classical

namespace FinishLine

open SeedLevelStep JSeedRecursion WeakProductAbsorption AtomFactorGeneration
open WeakProdFactorization TowerCardGrowth CopyAClassification CopyBExclusion

-- [D-3072] FirstSlice
def FirstSlice (n : ℕ) : Prop :=
  ∀ (x : D n), JoinIrred (D n) x →
    ∀ (y : D (n + 1)), JoinIrred (D (n + 1)) y →
      (¬ ∃ F : EndP (D n), y = glueA (markedPt n) F) →
        IsEmpty ((LevelSeed (n + 1) y)ᵒᵈ ≃o (D n × (LevelSeed n x)ᵒᵈ))

-- [D-3073] FirstSliceB
def FirstSliceB (n : ℕ) : Prop :=
  ∀ (x : D n), JoinIrred (D n) x →
    ∀ (b : EndP (D n)) (hb : b ≠ ⊥),
      JoinIrred (D (n + 1)) (glueB (markedPt n) b hb) →
        IsEmpty ((LevelSeed (n + 1) (glueB (markedPt n) b hb))ᵒᵈ
          ≃o (D n × (LevelSeed n x)ᵒᵈ))

-- [D-3074] FirstSliceC
def FirstSliceC (n : ℕ) : Prop :=
  ∀ (x : D n), JoinIrred (D n) x →
    ∀ (c : EndP (D n)) (hc : c ≠ ⊥) (hcm : c ≠ markedPt n),
      JoinIrred (D (n + 1)) (glueC (markedPt n) c hc hcm) →
        IsEmpty ((LevelSeed (n + 1) (glueC (markedPt n) c hc hcm))ᵒᵈ
          ≃o (D n × (LevelSeed n x)ᵒᵈ))

-- [D-3075] firstSlice_of
theorem firstSlice_of {n : ℕ} (hB : FirstSliceB n) (hC : FirstSliceC n) :
    FirstSlice n := by
  intro x hx y hy hnotA
  rcases dSuccCases n y with ⟨v, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, hcm, rfl⟩
  · exact absurd ⟨v, rfl⟩ hnotA
  · exact hB x hx b hb hy
  · exact hC x hx c hc hcm hy

end FinishLine
