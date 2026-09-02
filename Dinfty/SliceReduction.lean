import Dinfty.SeedComparison
import Dinfty.CopyAClassification

open GluingTowerLibrary SierpinskiApplication

/-!
# `k > n` is the first slice at a higher base

The truncation (§61–§62) gives, for a comparison at base `n` against level
`k + 1`, the exact finite equation

```
S  ≅  D n × D (n+1) × … × D k × T.
```

That looks like a family of problems indexed by `k`.  It is not.  Regroup it as

```
S  ≅  D k × (D n × … × D (k-1) × T)
```

and the parenthesised factor is itself a seed: the copy-`A` embedding at
threshold `⊥` satisfies

```lean
iotaSeedIso : Base (k+1) (iotaD k q)  ≃o  D k × Base k q
```

so iterating from `n` up to `k` identifies `D n × … × D (k-1) × T` with
`Base k (ι^{k-n} x)` — the seed of the **same `DInfty` point**, pushed up to
level `k`.  Hence the comparison at `(base n, level k+1)` is exactly the
comparison at `(base k, level k+1)`: the **first slice**, at a higher base.

**`∀ k ≥ n` collapses to `∀ n`.**  There is no separate `k > n` problem; there is
one problem, the first slice, quantified over the base.

The identity that pins this is `stepMap x ⊥ = constHom x` (§59): the tower embeds
level `k` as the threshold-`⊥` slice of `EndP (D k)`, which is precisely the
`p = ⊥` case of `copyASeedDualIso`, where `UpSet k ⊥` is all of `D k`.
-/

open scoped Classical

namespace SliceReduction

open SeedLevelStep JSeedRecursion WeakProductAbsorption AtomFactorGeneration
open WeakProdFactorization TowerCardGrowth CopyAClassification

variable {k : ℕ}

/-- `UpSet k ⊥` is all of `D k`. -/
def upSetBotIso (k : ℕ) : UpSet k (⊥ : D k) ≃o D k where
  toFun a := a.1
  invFun x := ⟨x, bot_le⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- A constant endomorphism is the `⊥` threshold. -/
theorem stepMap_bot' (x : D k) : stepMap x (⊥ : D k) = constHom x := by
  apply OrderHom.ext
  funext y
  exact stepMap_apply_of_ge x ⊥ bot_le

/-- The copy-`A` embedding is the `p = ⊥` point of the join-irreducible
correspondence. -/
theorem iotaD_eq_glueA_ji (k : ℕ) (q : {x : D k // JoinIrred (D k) x}) :
    iotaD k q.1
      = glueA (markedPt k) (jiOrderIso (OrderDual.toDual (⊥ : D k), q)).1 := by
  show glueA (markedPt k) (constHom q.1) = _
  congr 1
  show constHom q.1 = stepMap q.1 (⊥ : D k)
  rw [stepMap_bot']

/-- **The push-up lemma.**  Pushing a point up one level multiplies its seed by
that level. -/
noncomputable def iotaSeedIso (k : ℕ) (q : {x : D k // JoinIrred (D k) x}) :
    (LevelSeed (k + 1) (iotaD k q.1))ᵒᵈ ≃o (D k × (LevelSeed k q.1)ᵒᵈ) := by
  rw [iotaD_eq_glueA_ji k q]
  exact (copyASeedDualIso k ⊥ q).trans
    (JSeedRecursion.prodCongrIso (upSetBotIso k) (OrderIso.refl _))

end SliceReduction
