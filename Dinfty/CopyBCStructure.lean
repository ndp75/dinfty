import Dinfty.CopyAClassification

open GluingTowerLibrary SierpinskiApplication

/-!
# Copies `B` and `C` are not alike — the seed structure, and a correction

§34 recorded `CopyBCExcluded` as one obligation, on the reading that copies `B`
and `C` both have **ordinal-sum** seeds, so that
`AtomFactorGeneration.not_genByFactors_of_strict_upper` would dispose of both
with `t = dMid (k+1)`.

**That is right for copy `B` and wrong for copy `C`**, and this module makes the
difference precise.

## What both copies share

Everything outside copy `A` sits above the marked point:

```lean
dMid_le_glueB : dMid (k+1) ≤ glueB (markedPt k) x hx
dMid_le_glueC : dMid (k+1) ≤ glueC (markedPt k) x hx hxm
```

because `glueA m a ≤ glueB m x` needs only `a ≤ m` (`leGlue_tagA_tagB_of_le`),
and `glueA m a ≤ glueC m c` needs nothing at all (`leGlue_tagA_tagC`).

## Where they differ — and it is that second "nothing at all"

For a copy-`B` point, the copy-`A` part of the seed is **bounded by the marked
point**: `glueA m a ≤ glueB m x` forces `a ≤ m` (`leGlue_tagA_tagB_iff`, for
`x ≠ ⊤`), so

```lean
copyA_of_le_glueB_le_dMid : glueA m a ≤ glueB m x hx → glueA m a ≤ dMid (k+1)
```

— the seed really is `(copy-A below the marked point) ⊕ (copy B)`, an ordinal
sum, and `t = dMid (k+1)` bounds the lower part.

For a copy-`C` point the copy-`A` part is **all of copy `A`**, and in particular
reaches strictly above the marked point:

```lean
dMid_lt_iotaD_top : dMid (k+1) < iotaD k ⊤
iotaD_top_le_glueC : iotaD k ⊤ ≤ glueC (markedPt k) x hx hxm
```

So a copy-`C` seed contains copy-`A` elements that `dMid (k+1)` does **not**
bound, and `not_genByFactors_of_strict_upper` cannot be run with
`t = dMid (k+1)`.  Nor with `t = iotaD k ⊤` — *but only when `markedPt k ≤ x`*:
that is exactly when copy-`B` elements are in the seed as well, and
`iotaD k ⊤` does not bound *them*, since copy `A` reaches copy `B` only below
the marked point.  **When `markedPt k ≤ x`, copy `C`'s seed is not an ordinal
sum: its copy-`A` and copy-`B` parts interleave.**

**REFINEMENT (2026-08-30).**  When `¬ (markedPt k ≤ x)` the copy-`B` part is
*empty* (`leGlue_tagB_tagC_iff`), the seed **is** the ordinal sum
`J(EndP (D k)) ⊕ (copy C below x)`, and `t = iotaD k ⊤` **does** work.  That
half of copy `C` is closed in `Dinfty/CopyCLow.lean`; `markedPt k ≤ x` is what
remains.

## Status

Copy `B` is therefore ready to be closed by the `GenByFactors` route (with the
single-atom case falling to counting, as §34 describes).  **Copy `C` needs a
different argument**, and that is a correction to §34's plan, not a detail of
it.  Neither is proved here; what is proved is the structure that decides which
argument applies.
-/

open scoped Classical

namespace CopyBCStructure

open CopyAClassification SeedLevelStep

variable (k : ℕ)

private theorem hm' : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hmt' : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
private theorem hbt' : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

/-! ## The marked point is below everything outside copy `A` -/

theorem dMid_eq_glueA : dMid (k + 1) = glueA (markedPt k) (markedPt k) := rfl

theorem dMid_le_glueB {x : EndP (D k)} (hx : x ≠ ⊥) :
    dMid (k + 1) ≤ glueB (markedPt k) x hx :=
  leGlue_tagA_tagB_of_le (markedPt k) (markedPt k) x (le_refl _)

theorem dMid_le_glueC {x : EndP (D k)} (hx : x ≠ ⊥) (hxm : x ≠ markedPt k) :
    dMid (k + 1) ≤ glueC (markedPt k) x hx hxm :=
  leGlue_tagA_tagC (markedPt k) (markedPt k) x

/-! ## Copy `B`: the copy-`A` part of the seed is bounded by the marked point -/

/-- **Copy `A` reaches copy `B` only below the marked point.** -/
theorem copyA_of_le_glueB_le_dMid {a x : EndP (D k)} (hx : x ≠ ⊥) (hxt : x ≠ ⊤)
    (h : glueA (markedPt k) a ≤ glueB (markedPt k) x hx) :
    glueA (markedPt k) a ≤ dMid (k + 1) := by
  have ham : a ≤ markedPt k := (leGlue_tagA_tagB_iff (markedPt k) a x hxt).mp h
  exact (glueA_le_iff (markedPt k) (hm' k) a (markedPt k)).mpr ham

/-! ## Copy `C`: the copy-`A` part reaches strictly above the marked point -/

theorem iotaD_top_eq_glueA : iotaD k (⊤ : D k) = glueA (markedPt k) (⊤ : EndP (D k)) := by
  show glueA (markedPt k) (constHom (⊤ : D k)) = glueA (markedPt k) (⊤ : EndP (D k))
  rw [← endP_top_eq_constHom_top]

/-- **The copy-`A` top is above the marked point, strictly.** -/
theorem dMid_lt_iotaD_top : dMid (k + 1) < iotaD k (⊤ : D k) := by
  rw [dMid_eq_glueA, iotaD_top_eq_glueA]
  refine lt_of_le_of_ne
    ((glueA_le_iff (markedPt k) (hm' k) (markedPt k) (⊤ : EndP (D k))).mpr le_top) ?_
  intro hcon
  exact hmt' k (glueA_injective (markedPt k) hcon)

/-- …and it is in every copy-`C` seed. -/
theorem iotaD_top_le_glueC {x : EndP (D k)} (hx : x ≠ ⊥) (hxm : x ≠ markedPt k) :
    iotaD k (⊤ : D k) ≤ glueC (markedPt k) x hx hxm := by
  rw [iotaD_top_eq_glueA]
  exact leGlue_tagA_tagC (markedPt k) (⊤ : EndP (D k)) x

/-- **The correction, as a theorem.**  A copy-`C` seed contains a copy-`A`
element that the marked point does not bound — so the copy-`B` argument does not
transfer. -/
theorem copyC_seed_not_bounded_by_dMid {x : EndP (D k)} (hx : x ≠ ⊥)
    (hxm : x ≠ markedPt k) :
    ∃ w : D (k + 1), w ≤ glueC (markedPt k) x hx hxm ∧ ¬ (w ≤ dMid (k + 1)) :=
  ⟨iotaD k (⊤ : D k), iotaD_top_le_glueC k hx hxm,
   fun hle => absurd (le_antisymm hle (le_of_lt (dMid_lt_iotaD_top k)))
     (ne_of_gt (dMid_lt_iotaD_top k))⟩

/-- And copy `B` is genuinely inside the seed of a copy-`C` point whenever the
marked point is below it — so `iotaD k ⊤` is not a bound either. -/
theorem glueB_le_glueC_of_marked_le {b x : EndP (D k)} (hb : b ≠ ⊥) (hx : x ≠ ⊥)
    (hxm : x ≠ markedPt k) (hmx : markedPt k ≤ x) :
    glueB (markedPt k) b hb ≤ glueC (markedPt k) x hx hxm :=
  (leGlue_tagB_tagC_iff (markedPt k) b x).mpr hmx

theorem not_iotaD_top_le_glueB {b : EndP (D k)} (hb : b ≠ ⊥) (hbt : b ≠ ⊤) :
    ¬ (iotaD k (⊤ : D k) ≤ glueB (markedPt k) b hb) := by
  rw [iotaD_top_eq_glueA]
  intro h
  have := (leGlue_tagA_tagB_iff (markedPt k) (⊤ : EndP (D k)) b hbt).mp h
  exact hmt' k (le_antisymm le_top this)

end CopyBCStructure
