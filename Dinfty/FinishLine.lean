import Dinfty.SeedParametrisation
import Dinfty.SeedComparison
import Dinfty.CopyBExclusion

open GluingTowerLibrary SierpinskiApplication

/-!
# The finish line

This file states, literally, the one thing left to prove.

## The chain, and where each link stands

```
Subsingleton (DInfty ≃o DInfty)                       -- colimit_compat, pillar B
  ⇐ colimit_compat_of_multiAtom                       -- PROVED (CopyBCAtBase)
  ⇐ CopyBCMultiAtomExcludedAt at every point
  ⇐ FirstSlice n, for every n                         -- reduction: SliceReduction §66
  ⇐ FirstSliceB n ∧ FirstSliceC n                     -- PROVED here (firstSlice_of)
```

The middle reduction is §66: regrouping the truncation equation
`S ≅ D n × … × D k × T` as `S ≅ D k × (D n × … × D (k-1) × T)`, the right factor
is `Base k (ι^{k-n} x)` by `SliceReduction.iotaSeedIso`, so a comparison at
`(base n, level k+1)` **is** a first-slice instance at base `k`.  `∀ k ≥ n`
collapses to `∀ n`.

## What `FirstSlice` says, and why it is now finite to check

`FirstSlice n` compares a competitor seed at level `n+1` against `D n × Base n x`.
By §67 the competitor seed is **parametrised, not enumerated**: for copy `B`,

```
LevelSeed (n+1) (glueB (markedPt n) b)
   =  {(p, q) | q ≤ dMid n}      -- product, INDEPENDENT of b
   ⊕  {(p, q) | q ≤ b p}         -- hypograph of b
```

over the index `(D n)ᵒᵈ × J (D n)` of `jiOrderIso`, both conditions pointwise
(`stepMap_le_iff_apply`, `stepMap_le_markedPt`).  The §63 product invariants —
cardinality multiplicative, atom count and height additive
(`Truncation.card_eq_prod`, `SeedComparison.card_atoms_eq`,
`SeedComparison.htP_eq`) — are then evaluated on that description.

Copy `A` needs no case: with threshold `p ≠ ⊥` it is excluded by
`copyA_forces_bot_at`, and with `p = ⊥` it is the genuine embedding of the *same*
point, not a competitor.
-/

open scoped Classical

namespace FinishLine

open SeedLevelStep JSeedRecursion WeakProductAbsorption AtomFactorGeneration
open WeakProdFactorization TowerCardGrowth CopyAClassification CopyBExclusion

/-- **The finish line.**  No non-copy-`A` join-irreducible of `D (n+1)` carries
the seed of a stage-`n` point. -/
def FirstSlice (n : ℕ) : Prop :=
  ∀ (x : D n), JoinIrred (D n) x →
    ∀ (y : D (n + 1)), JoinIrred (D (n + 1)) y →
      (¬ ∃ F : EndP (D n), y = glueA (markedPt n) F) →
        IsEmpty ((LevelSeed (n + 1) y)ᵒᵈ ≃o (D n × (LevelSeed n x)ᵒᵈ))

/-- The copy-`B` half. -/
def FirstSliceB (n : ℕ) : Prop :=
  ∀ (x : D n), JoinIrred (D n) x →
    ∀ (b : EndP (D n)) (hb : b ≠ ⊥),
      JoinIrred (D (n + 1)) (glueB (markedPt n) b hb) →
        IsEmpty ((LevelSeed (n + 1) (glueB (markedPt n) b hb))ᵒᵈ
          ≃o (D n × (LevelSeed n x)ᵒᵈ))

/-- The copy-`C` half. -/
def FirstSliceC (n : ℕ) : Prop :=
  ∀ (x : D n), JoinIrred (D n) x →
    ∀ (c : EndP (D n)) (hc : c ≠ ⊥) (hcm : c ≠ markedPt n),
      JoinIrred (D (n + 1)) (glueC (markedPt n) c hc hcm) →
        IsEmpty ((LevelSeed (n + 1) (glueC (markedPt n) c hc hcm))ᵒᵈ
          ≃o (D n × (LevelSeed n x)ᵒᵈ))

/-- **The two halves suffice.**  `dSuccCases` splits `D (n+1)` into the three
copies, and copy `A` is excluded by hypothesis. -/
theorem firstSlice_of {n : ℕ} (hB : FirstSliceB n) (hC : FirstSliceC n) :
    FirstSlice n := by
  intro x hx y hy hnotA
  rcases dSuccCases n y with ⟨v, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, hcm, rfl⟩
  · exact absurd ⟨v, rfl⟩ hnotA
  · exact hB x hx b hb hy
  · exact hC x hx c hc hcm hy

end FinishLine
