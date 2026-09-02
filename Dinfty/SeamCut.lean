import Dinfty.CanonicalChain

open GluingTowerLibrary SierpinskiApplication

/-!
# `CSeamFixed`: the seam is a cut point — and the decision is NOT reached

§121 posed `CSeamFixed : ∀ θ : B ≃o B, θ cSeamB = cSeamB`.  This module carries
the attempt.  It settles the *structure* of the question and records, honestly,
that the question itself is **not decided here**.

## What is settled: the seam cuts every stage in two

`cSeam k` is not only the top of copy `A` (`mem_copyA_iff_le_cSeam`); by the
`canonGen` collapse `tag_C ⊥ ↦ inl ⊤` it is also the **bottom of copy `C`**, and

```lean
cSeam_le_iff : cSeam k ≤ z ↔ z is `inl ⊤`, `inr (inl ⊤)`, or a copy-`C` point
```

so `↓ cSeam = copy A` and `↑ cSeam = copy C` exactly.  At the bilimit:

```lean
cSeamFixed_iff_ideal_stable :
  CSeamFixed ↔ ∀ θ : B ≃o B, ∀ y, y ≤ cSeamB ↔ θ y ≤ cSeamB
```

`cSeamB` is the greatest element of its own down-set, so fixing it and
preserving the copy-`A` ideal are the same statement.  That is the real content
of §121's split: **`CSeamFixed` is exactly "every automorphism preserves the
three-copy decomposition".**

## What is NOT settled, and the precise reason

Every local handle on `cSeamB` dies at the bilimit, and always by §119's
mechanism:

* **unique upper cover.**  At a *level* the seam has one: every non-`⊥` element
  of `EndP (D k)` is above `spikeHom (atomOf (D k))`, so `glueC` of that atom is
  the unique cover of `cSeam k`.  At the bilimit the cover is destroyed — the
  copy-`C` bilimit is atomless above its bottom by exactly the argument of
  `AtomlessBilimit.no_isAtom`, because `iotaD` fattens the spike at the base.
* **meet-irreducibility.**  Same source: it holds at every level (two non-`⊥`
  elements of `EndP` meet above the atom) and is not inherited, for the same
  reason.
* **cardinality.**  `|D (k+1)|` grows too fast for a stage map's image to be
  constrained by counting; `|EndP (D 1)|` alone is `12 301 264 685 471 857`.

So `cSeamB` has no order-theoretic *neighbourhood* description, and any decision
must come from a **non-local** invariant.  That is precisely what
[[project_dinfty_definability_terminus]] predicted for this pillar, and it is
where the attempt stops: not at a missing lemma, but at a missing kind of
argument.

**Status: `CSeamFixed` is OPEN.**  Nothing below asserts it, and nothing below
refutes it.
-/

open scoped Classical

namespace SeamCut

open PhiIterateTower PhiBilimit EpPairTower StageRigidity PhiStagePipe StageEmbedding
open GenContinuity SeamFixed CanonicalChain

/-! ## 1.  The seam is the bottom of copy `C` -/

/-- The `canonGen` collapse that makes the seam two-sided: a copy-`C` point at
`⊥` *is* the top of copy `A`. -/
theorem canon_tagC_bot (k : ℕ) :
    canonGen (markedPt k) (Sum.inr (Sum.inr (⊥ : EndP (D k))))
      = Sum.inl (⊤ : EndP (D k)) := by
  rw [canonGen, if_pos rfl]

/-- **The up-set of the seam is copy `C`.**  Together with
`mem_copyA_iff_le_cSeam` (`↓ cSeam = copy A`) this makes `cSeam` a cut point of
the level. -/
theorem cSeam_le_iff (k : ℕ) (z : D (k + 1)) :
    cSeam k ≤ z ↔ (z.1 = Sum.inl (⊤ : EndP (D k))
      ∨ z.1 = Sum.inr (Sum.inl (⊤ : EndP (D k)))
      ∨ ∃ c : EndP (D k), z.1 = Sum.inr (Sum.inr c)) := by
  have hnd := D_marked_point_nondegenerate k
  constructor
  · intro h
    have hle : leGlueGen (markedPt k) (Sum.inl (⊤ : EndP (D k))) z.1 := h
    rcases hz : z.1 with u | w
    · left
      rw [hz] at hle
      have hu : (⊤ : EndP (D k)) ≤ u :=
        (leGlueGen_tagA_tagA_iff (markedPt k) hnd.1 _ u).mp hle
      rw [top_le_iff.mp hu]
    · rcases w with y | c
      · rcases eq_or_ne y (⊤ : EndP (D k)) with hy | hy
        · right; left; rw [hy]
        · exfalso
          rw [hz] at hle
          exact hnd.2.1
            (top_le_iff.mp ((leGlue_tagA_tagB_iffGen (markedPt k) _ y hy).mp hle))
      · right; right; exact ⟨c, rfl⟩
  · intro h
    show leGlueGen (markedPt k) (cSeam k).1 z.1
    rw [cSeam_val]
    rcases h with h | h | ⟨c, h⟩
    · rw [h]
      exact (leGlueGen_tagA_tagA_iff (markedPt k) hnd.1 _ _).mpr (le_refl _)
    · rw [h]
      exact leGlue_tagA_tagB_topGen (markedPt k) (⊤ : EndP (D k))
    · rw [h]
      exact leGlueGen_tagA_tagC (markedPt k) _ c

/-! ## 2.  Fixing the seam = preserving the copy-`A` ideal -/

/-- `cSeamB` is the greatest element of its own down-set, so an automorphism
fixes it exactly when it preserves that down-set. -/
theorem cSeamFixed_iff_ideal_stable :
    CanonicalChain.CSeamFixed ↔ ∀ (θ : B ≃o B) (y : B), y ≤ cSeamB ↔ θ y ≤ cSeamB := by
  constructor
  · intro h θ y
    constructor
    · intro hy
      rw [← h θ]
      exact θ.monotone hy
    · intro hy
      rw [← h θ] at hy
      exact θ.le_iff_le.mp hy
  · intro h θ
    have h1 : θ cSeamB ≤ cSeamB := (h θ cSeamB).mp (le_refl _)
    have h2 : cSeamB ≤ θ cSeamB := by
      have h3 : θ.symm cSeamB ≤ cSeamB := by
        have := (h θ (θ.symm cSeamB)).mpr (by rw [OrderIso.apply_symm_apply])
        exact this
      have h4 := θ.monotone h3
      rwa [OrderIso.apply_symm_apply] at h4
    exact le_antisymm h1 h2

/-! ## 3.  Why the local handles fail

Recorded as theorems where they are cheap, so the negative is on file rather
than in prose. -/

/-- At a **level** the seam does have a unique upper cover, and this is the
ingredient: every non-`⊥` endomorphism dominates the spike at the level's atom.
So every strict upper bound of `cSeam k` inside copy `C` dominates
`glueC (spikeHom (lamD k))`.

At the **bilimit** this is exactly what fails, because the stage atoms strictly
decrease (`AtomlessBilimit.stage_atom_lt`) — the same fattening that made `B`
atomless kills the seam's cover. -/
theorem spikeHom_lamD_le (k : ℕ) (u : EndP (D k)) (hu : u ≠ ⊥) :
    spikeHom (TowerNoAbsorption.lamD k) ≤ u := by
  have hut : u ⊤ ≠ (⊥ : D k) := fun hc => hu (AtomlessBilimit.eq_bot_of_apply_top hc)
  rw [OrderHom.le_def]
  intro x
  rcases eq_or_ne x (⊤ : D k) with hx | hx
  · subst hx
    rw [spikeHom_apply_top]
    exact TowerNoAbsorption.lamD_le k _ hut
  · rw [spikeHom_apply_of_ne _ hx]
    exact bot_le

end SeamCut
