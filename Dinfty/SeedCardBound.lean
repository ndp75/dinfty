import Dinfty.CopyCLow

open GluingTowerLibrary SierpinskiApplication

/-!
# The base-independent replacement for `4 ≤ card S`

`CopyBAtoms.four_le_card_seed` closes copy-`B`'s single-atom case by counting:
the seed of a copy-`B` point has at least four elements, against
`Fintype.card (D 0) = 3`.  That is the only step of the copy-`B`/`C` closure that
does **not** survive a change of base stage — from base `n` the same argument
needs `card (D n) < 4`, true only at `n = 0` (`card (D 1) = 27`).  Handoff §49
located it as the single obstacle to carrying the closure from the two points to
every point.

The replacement is the same count done honestly:

```lean
card_D_lt_card_seed : Fintype.card (D k) < Fintype.card (LevelSeed (k + 1) y)
```

for every join-irreducible `y` of `D (k+1)` that is **not** copy `A`.  The seed
contains a whole copy of `D k`,

```
t ↦ glueA (markedPt k) (stepMap (dMid k) t)
```

— injective because `stepMap` is injective in its threshold
(`stepMap_inj_of_ne_bot`, available since `dMid k ≠ ⊥`), join-irreducible because
`dMid k` is, and below `y` because every one of them is `≤ markedPt k`, which
copy `B` and copy `C` both dominate.  And `y` itself is not in the image, being
copy `B` or `C` rather than copy `A`.  So the seed has at least `card (D k) + 1`
elements.

At `k = 0` that lower bound is `4` — exactly `four_le_card_seed`, which is the
`n = 0` instance of this.  The computation
(`_archive/check_stage_slice_search.py`'s companion) confirms it: over `D 1` the
minimum is `4` and the bound is attained; over `D 2` the minimum is `82` against
`card (D 1) = 27`, so the bound is loose but valid.
-/

open scoped Classical

namespace SeedCardBound

open TwoPointAssembly CopyAClassification CopyBCStructure SeedLevelStep
open SeedSeparation MidAnchor TwoPointHypothesis CopyBExclusion CopyBAtoms
open CopyCLow

private theorem hmk' (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hmtk' (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
private theorem hbtk' (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

variable (k : ℕ)

/-- The threshold family: `stepMap (dMid k) t` for `t` running over `D k`. -/
noncomputable def thr (t : D k) : EndP (D k) := stepMap (dMid k) t

theorem thr_joinIrred (t : D k) : JoinIrred (EndP (D k)) (thr k t) :=
  (jiEquiv (t, (⟨dMid k, D_mid_joinIrred k⟩ : {v : D k // JoinIrred (D k) v}))).2

theorem thr_le (t : D k) : thr k t ≤ markedPt k := by
  intro y
  show stepMap (dMid k) t y ≤ (constHom (dMid k) : EndP (D k)) y
  by_cases h : t ≤ y
  · rw [stepMap_apply_of_ge (dMid k) t h]
    exact le_refl _
  · rw [stepMap_apply_of_not_ge (dMid k) t h]
    exact bot_le

theorem thr_injective : Function.Injective (thr k) := by
  intro a b h
  exact ((stepMap_inj_of_ne_bot (dMid_ne_bot k) (dMid_ne_bot k) h).2)

/-- The copy of `D k` sitting inside the seed of any non-copy-`A` point. -/
noncomputable def seedCopy {y : D (k + 1)}
    (hle : ∀ v : EndP (D k), v ≤ markedPt k →
      (glueA (markedPt k) v : D (k + 1)) ≤ y) (t : D k) : LevelSeed (k + 1) y :=
  ⟨glueA (markedPt k) (thr k t),
   (joinIrred_glueA_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) (thr k t)).mpr
     (thr_joinIrred k t),
   hle (thr k t) (thr_le k t)⟩

theorem seedCopy_injective {y : D (k + 1)}
    (hle : ∀ v : EndP (D k), v ≤ markedPt k →
      (glueA (markedPt k) v : D (k + 1)) ≤ y) :
    Function.Injective (seedCopy k hle) := by
  intro a b h
  refine thr_injective k ?_
  exact glueA_injective (markedPt k) (congrArg Subtype.val h)

/-- **The bound.**  A non-copy-`A` join-irreducible's seed is strictly bigger
than the level below. -/
theorem card_D_lt_card_seed {y : D (k + 1)} (hy : JoinIrred (D (k + 1)) y)
    (hle : ∀ v : EndP (D k), v ≤ markedPt k →
      (glueA (markedPt k) v : D (k + 1)) ≤ y)
    (hnotA : ¬ ∃ v : EndP (D k), y = glueA (markedPt k) v) :
    Fintype.card (D k) < Fintype.card (LevelSeed (k + 1) y) := by
  refine Fintype.card_lt_of_injective_of_notMem (seedCopy k hle)
    (seedCopy_injective k hle) (b := (⟨y, hy, le_refl y⟩ : LevelSeed (k + 1) y)) ?_
  rintro ⟨t, ht⟩
  exact hnotA ⟨thr k t, (congrArg Subtype.val ht).symm⟩

/-! ## The two instances -/

theorem card_D_lt_card_seed_B {x : EndP (D k)} (hx : x ≠ ⊥)
    (hy : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx)) :
    Fintype.card (D k)
      < Fintype.card (LevelSeed (k + 1) (glueB (markedPt k) x hx)) := by
  refine card_D_lt_card_seed k hy
    (fun v hv => leGlue_tagA_tagB_of_le (markedPt k) v x hv) ?_
  rintro ⟨v, hv⟩
  have h2 : (Sum.inr (Sum.inl x) : GlueBase (EndP (D k))) = Sum.inl v :=
    congrArg Subtype.val hv
  simp at h2

theorem card_D_lt_card_seed_C {x : EndP (D k)} (hx : x ≠ ⊥) (hxm : x ≠ markedPt k)
    (hy : JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm)) :
    Fintype.card (D k)
      < Fintype.card (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm)) := by
  refine card_D_lt_card_seed k hy
    (fun v _ => leGlue_tagA_tagC (markedPt k) v x) ?_
  rintro ⟨v, hv⟩
  have h2 : (Sum.inr (Sum.inr x) : GlueBase (EndP (D k))) = Sum.inl v :=
    congrArg Subtype.val hv
  simp at h2


/-- **The bound, for any non-copy-`A` point.**  `dSuccCases` splits the two
cases and both dominate `markedPt k`. -/
theorem card_D_lt_card_seed_notA {y : D (k + 1)} (hy : JoinIrred (D (k + 1)) y)
    (hnotA : ¬ ∃ F : EndP (D k), y = glueA (markedPt k) F) :
    Fintype.card (D k) < Fintype.card (LevelSeed (k + 1) y) := by
  rcases dSuccCases k y with ⟨v, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, hxm, rfl⟩
  · exact absurd ⟨v, rfl⟩ hnotA
  · exact card_D_lt_card_seed_B k hx hy
  · exact card_D_lt_card_seed_C k hx hxm hy

/-- At `k = 0` this is `CopyBAtoms.four_le_card_seed`. -/
theorem four_le_card_seed_zero {x : EndP (D 0)} (hx : x ≠ ⊥)
    (hy : JoinIrred (D (0 + 1)) (glueB (markedPt 0) x hx)) :
    4 ≤ Fintype.card (LevelSeed (0 + 1) (glueB (markedPt 0) x hx)) := by
  have h := card_D_lt_card_seed_B 0 hx hy
  rw [CopyBAtoms.card_D_zero] at h
  omega

end SeedCardBound
