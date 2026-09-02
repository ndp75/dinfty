import Dinfty.SliceReduction

open GluingTowerLibrary SierpinskiApplication

/-!
# The seed is parametrised, not enumerated

Enumerating `J (D (k+1))` to check the first slice is the wrong move: at `k = 2`
that is `≈ 4.8 × 10¹⁹` elements.  But the join-irreducibles are **indexed**, not
opaque —

```lean
jiOrderIso : (D k)ᵒᵈ × {x : D k // JoinIrred (D k) x} ≃o J (EndP (D k))
             (p, q)  ↦  stepMap q p
```

with the **product** order (`stepMap_le_stepMap_iff`).  So a seed is cut out of a
product by a *condition on the index*, and the two conditions that arise are both
pointwise:

* `stepMap q p ≤ x`        ↔  `q ≤ x p`        (`stepMap_le_iff_apply`)
* `stepMap q p ≤ markedPt k` ↔  `q ≤ dMid k`   (`stepMap_le_markedPt`)

Combined with `CopyBAtoms.seed_cases` and `copyA_le_copyB`, this describes the
copy-`B` seed completely and symbolically:

```
LevelSeed (k+1) (glueB (markedPt k) x)
    =  { (p, q) | q ≤ dMid k }            -- the copy-A part: a PRODUCT,
                                          --   (D k)ᵒᵈ × {q ∈ J (D k) | q ≤ dMid k},
                                          --   and independent of x
    ⊕  { (p, q) | q ≤ x p }               -- the copy-B part: the "hypograph" of x
```

an **ordinal sum**, the first part lying entirely below the second.  Nothing here
enumerates `J (D (k+1))`: the seed is a definable subset of `(D k)ᵒᵈ × J (D k)`,
so the first-slice comparison against `D k × Base k x'` is a symbolic question in
`x` and `x'`.
-/

open scoped Classical

namespace SeedParametrisation

open SeedLevelStep JSeedRecursion WeakProductAbsorption AtomFactorGeneration
open WeakProdFactorization TowerCardGrowth CopyAClassification

variable {k : ℕ}

/-- **The copy-`B` membership condition is pointwise.**  A join-irreducible
`stepMap q p` of `EndP (D k)` lies below `x` exactly when `q` lies below `x`'s
value at the threshold `p`. -/
theorem stepMap_le_iff_apply {p q : D k} (hq : q ≠ ⊥) (x : EndP (D k)) :
    (stepMap q p : EndP (D k)) ≤ x ↔ q ≤ x p := by
  constructor
  · intro h
    simpa using h p
  · intro h y
    by_cases hpy : p ≤ y
    · simpa [stepMap_apply_of_ge q p hpy] using h.trans (x.monotone hpy)
    · simpa [stepMap_apply_of_not_ge q p hpy] using (bot_le : (⊥ : D k) ≤ x y)

/-- **The copy-`A` membership condition does not mention the threshold.**  So the
copy-`A` part of a copy-`B` seed is a product, and is the *same* poset for every
copy-`B` point. -/
theorem stepMap_le_markedPt {p q : D k} (hq : q ≠ ⊥) :
    (stepMap q p : EndP (D k)) ≤ markedPt k ↔ q ≤ dMid k := by
  rw [stepMap_le_iff_apply hq]
  simp

end SeedParametrisation
