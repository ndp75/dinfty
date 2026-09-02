import Dinfty.SeamCut

open GluingTowerLibrary SierpinskiApplication

/-!
# The global invariants, applied to the seam

§122 stopped because every *local* description of `cSeamB` dies at the bilimit.
So use the global ones.  An automorphism of `B` cannot be assumed to respect the
tower, but it must respect anything defined from the order alone, and there are
exactly two such handles worth having:

* **compactness.**  `OmegaCompact` is order-theoretic, so `θ` permutes the
  compacts — already in the repo as `PhiStagePipe.stages_union_preserved`, with
  `omegaCompact_iff_stage` identifying them with `⋃ S_k`.
* **the principal-ideal isomorphism type.**  `θ` restricts to an order
  isomorphism `↓c ≃o ↓(θ c)` (`idealIso`).  So the iso type of `↓c` is an
  invariant of `c`, and it is *global*: it looks at all of `↓c`, not at a
  neighbourhood.

## The tripoint supplies the special ideal

`cSeamB` is a stage point, hence compact, so `θ cSeamB` is a stage point too
(`theta_cSeamB_stage`).  And `↓cSeamB` is not an arbitrary ideal: by
`SeamCut.cSeam_le_iff` it is exactly **copy `A`**, one of the three glue copies
that the tripointed structure `B ≅ Φ(B)` cuts `B` into.  Hence

```lean
cSeamFixed_of_ideal_pins :
  (∀ z : B, Nonempty ({y // y ≤ z} ≃o {y // y ≤ cSeamB}) → z = cSeamB)
    → CanonicalChain.CSeamFixed
```

`CSeamFixed` is now: **no other element of `B` has a principal ideal isomorphic
to copy `A`.**  That is a global statement about `B`, with no neighbourhood, no
cover, and no atom in it — the three things §122 ruled out.

## What the levels already give

Inside a level the invariant decides every *comparable* case outright: a `z`
strictly below the seam has a strictly smaller ideal, a `z` strictly above it a
strictly larger one, and levels are finite, so neither can be isomorphic
(`ideal_ncard_lt_of_lt`, `ideal_ncard_lt_of_gt`, `not_idealIso_of_ne_of_comp`).

What survives is the **incomparable** case: `z` in copy `B`.  There
`↓z = (↓ m in EndP) ∪ (↓ y in copy B)`, whose size is
`|↓m| + |↓y| - 1`, and nothing forbids that from matching `|EndP (D k)|` by
accident.  So the level-wise statement is settled except across copy `B`, and
the bilimit statement needs that case plus the level shift.

**STATUS: `CSeamFixed` remains OPEN.**  This module changes its *shape* — from a
local question to a global one — and closes the comparable half at every level.
It does not decide it.
-/

open scoped Classical

namespace IdealInvariant

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding
open SeamFixed CanonicalChain SeamCut

/-! ## 1.  The invariant -/

/-- **An automorphism carries a principal ideal onto a principal ideal.**  So
the order-isomorphism type of `↓c` is an invariant of `c` — a *global* one. -/
noncomputable def idealIso (θ : B ≃o B) (c : B) :
    {y : B // y ≤ c} ≃o {y : B // y ≤ θ c} where
  toFun := fun y => ⟨θ y.1, θ.monotone y.2⟩
  invFun := fun y => ⟨θ.symm y.1, by
    have h := θ.symm.monotone y.2
    rwa [OrderIso.symm_apply_apply] at h⟩
  left_inv := fun y => Subtype.ext (θ.symm_apply_apply y.1)
  right_inv := fun y => Subtype.ext (θ.apply_symm_apply y.1)
  map_rel_iff' := θ.le_iff_le

/-- `θ cSeamB` is again a stage point: compactness is order-theoretic. -/
theorem theta_cSeamB_stage (θ : B ≃o B) :
    ∃ (n : ℕ) (y : D (n + 1)), θ cSeamB = insD n y := by
  have h : θ (insD 1 (cSeam 1)) = θ cSeamB := rfl
  obtain ⟨n, y, hy⟩ := PhiStagePipe.stages_union_preserved θ 1 (cSeam 1)
  exact ⟨n, y, h ▸ hy⟩

/-- **`CSeamFixed`, as a statement about ideals.**  No neighbourhood, no cover,
no atom — the three handles §122 ruled out. -/
theorem cSeamFixed_of_ideal_pins
    (h : ∀ z : B, Nonempty ({y : B // y ≤ z} ≃o {y : B // y ≤ cSeamB}) → z = cSeamB) :
    CanonicalChain.CSeamFixed := by
  intro θ
  refine h (θ cSeamB) ⟨?_⟩
  exact (idealIso θ cSeamB).symm

/-! ## 2.  Inside a level, the invariant decides every comparable case -/

theorem ideal_ncard_lt_of_lt {k : ℕ} {z : D (k + 1)} (hz : z < cSeam k) :
    {w : D (k + 1) | w ≤ z}.ncard < {w : D (k + 1) | w ≤ cSeam k}.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  refine ⟨fun w hw => le_trans hw (le_of_lt hz), ?_⟩
  intro hsub
  exact absurd (hsub (le_refl (cSeam k))) (not_le_of_gt hz)

theorem ideal_ncard_lt_of_gt {k : ℕ} {z : D (k + 1)} (hz : cSeam k < z) :
    {w : D (k + 1) | w ≤ cSeam k}.ncard < {w : D (k + 1) | w ≤ z}.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  refine ⟨fun w hw => le_trans hw (le_of_lt hz), ?_⟩
  intro hsub
  exact absurd (hsub (le_refl z)) (not_le_of_gt hz)

/-- **The comparable half, at every level.**  A level point comparable to the
seam and different from it has an ideal of a different size, hence a different
ideal isomorphism type. -/
theorem not_idealIso_of_ne_of_comp {k : ℕ} {z : D (k + 1)} (hne : z ≠ cSeam k)
    (hcomp : z ≤ cSeam k ∨ cSeam k ≤ z) :
    ¬ Nonempty ({w : D (k + 1) // w ≤ z} ≃o {w : D (k + 1) // w ≤ cSeam k}) := by
  rintro ⟨e⟩
  have hcard : Nat.card {w : D (k + 1) // w ≤ z}
      = Nat.card {w : D (k + 1) // w ≤ cSeam k} := Nat.card_congr e.toEquiv
  have hz : {w : D (k + 1) | w ≤ z}.ncard = Nat.card {w : D (k + 1) // w ≤ z} := rfl
  have hs : {w : D (k + 1) | w ≤ cSeam k}.ncard
      = Nat.card {w : D (k + 1) // w ≤ cSeam k} := rfl
  rcases hcomp with hle | hge
  · have hlt : z < cSeam k := lt_of_le_of_ne hle hne
    have := ideal_ncard_lt_of_lt hlt
    rw [hz, hs, hcard] at this
    exact lt_irrefl _ this
  · have hlt : cSeam k < z := lt_of_le_of_ne hge (Ne.symm hne)
    have := ideal_ncard_lt_of_gt hlt
    rw [hz, hs, hcard] at this
    exact lt_irrefl _ this

/-! ## 3.  What is left, named

The incomparable case is exactly copy `B`: by `mem_copyA_iff_le_cSeam` and
`SeamCut.cSeam_le_iff`, a level point is comparable to `cSeam k` unless its
canonical form is `inr (inl y)` with `y ≠ ⊥` and `y ≠ ⊤`. -/

theorem comparable_or_tagB {k : ℕ} (z : D (k + 1)) :
    (z ≤ cSeam k ∨ cSeam k ≤ z) ∨ ∃ y : EndP (D k), z.1 = Sum.inr (Sum.inl y) := by
  rcases hz : z.1 with u | w
  · exact Or.inl (Or.inl ((mem_copyA_iff_le_cSeam k z).mp ⟨u, hz⟩))
  · rcases w with y | c
    · exact Or.inr ⟨y, rfl⟩
    · exact Or.inl (Or.inr ((cSeam_le_iff k z).mpr (Or.inr (Or.inr ⟨c, hz⟩))))

end IdealInvariant
