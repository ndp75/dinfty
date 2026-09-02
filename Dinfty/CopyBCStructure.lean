import Dinfty.CopyAClassification

open GluingTowerLibrary SierpinskiApplication

-- [D-1905] §Copies-B-and-C-are-not-alike-the-seed-structure
open scoped Classical

namespace CopyBCStructure

open CopyAClassification SeedLevelStep

variable (k : ℕ)

-- [D-1906] hm'
private theorem hm' : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-1907] hmt'
private theorem hmt' : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
-- [D-1908] hbt'
private theorem hbt' : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

-- [D-1909] §The-marked-point-is-below-everything-outside
-- [D-1910] dMid_eq_glueA
theorem dMid_eq_glueA : dMid (k + 1) = glueA (markedPt k) (markedPt k) := rfl

-- [D-1911] dMid_le_glueB
theorem dMid_le_glueB {x : EndP (D k)} (hx : x ≠ ⊥) :
    dMid (k + 1) ≤ glueB (markedPt k) x hx :=
  leGlue_tagA_tagB_of_le (markedPt k) (markedPt k) x (le_refl _)

-- [D-1912] dMid_le_glueC
theorem dMid_le_glueC {x : EndP (D k)} (hx : x ≠ ⊥) (hxm : x ≠ markedPt k) :
    dMid (k + 1) ≤ glueC (markedPt k) x hx hxm :=
  leGlue_tagA_tagC (markedPt k) (markedPt k) x

-- [D-1913] §Copy-B-the-copy-A-part-of-the-seed-is-bounded-by
-- [D-1914] copyA_of_le_glueB_le_dMid
theorem copyA_of_le_glueB_le_dMid {a x : EndP (D k)} (hx : x ≠ ⊥) (hxt : x ≠ ⊤)
    (h : glueA (markedPt k) a ≤ glueB (markedPt k) x hx) :
    glueA (markedPt k) a ≤ dMid (k + 1) := by
  have ham : a ≤ markedPt k := (leGlue_tagA_tagB_iff (markedPt k) a x hxt).mp h
  exact (glueA_le_iff (markedPt k) (hm' k) a (markedPt k)).mpr ham

-- [D-1915] §Copy-C-the-copy-A-part-reaches-strictly-above
-- [D-1916] iotaD_top_eq_glueA
theorem iotaD_top_eq_glueA : iotaD k (⊤ : D k) = glueA (markedPt k) (⊤ : EndP (D k)) := by
  show glueA (markedPt k) (constHom (⊤ : D k)) = glueA (markedPt k) (⊤ : EndP (D k))
  rw [← endP_top_eq_constHom_top]

-- [D-1917] dMid_lt_iotaD_top
theorem dMid_lt_iotaD_top : dMid (k + 1) < iotaD k (⊤ : D k) := by
  rw [dMid_eq_glueA, iotaD_top_eq_glueA]
  refine lt_of_le_of_ne
    ((glueA_le_iff (markedPt k) (hm' k) (markedPt k) (⊤ : EndP (D k))).mpr le_top) ?_
  intro hcon
  exact hmt' k (glueA_injective (markedPt k) hcon)

-- [D-1918] iotaD_top_le_glueC
theorem iotaD_top_le_glueC {x : EndP (D k)} (hx : x ≠ ⊥) (hxm : x ≠ markedPt k) :
    iotaD k (⊤ : D k) ≤ glueC (markedPt k) x hx hxm := by
  rw [iotaD_top_eq_glueA]
  exact leGlue_tagA_tagC (markedPt k) (⊤ : EndP (D k)) x

-- [D-1919] copyC_seed_not_bounded_by_dMid
theorem copyC_seed_not_bounded_by_dMid {x : EndP (D k)} (hx : x ≠ ⊥)
    (hxm : x ≠ markedPt k) :
    ∃ w : D (k + 1), w ≤ glueC (markedPt k) x hx hxm ∧ ¬ (w ≤ dMid (k + 1)) :=
  ⟨iotaD k (⊤ : D k), iotaD_top_le_glueC k hx hxm,
   fun hle => absurd (le_antisymm hle (le_of_lt (dMid_lt_iotaD_top k)))
     (ne_of_gt (dMid_lt_iotaD_top k))⟩

-- [D-1920] glueB_le_glueC_of_marked_le
theorem glueB_le_glueC_of_marked_le {b x : EndP (D k)} (hb : b ≠ ⊥) (hx : x ≠ ⊥)
    (hxm : x ≠ markedPt k) (hmx : markedPt k ≤ x) :
    glueB (markedPt k) b hb ≤ glueC (markedPt k) x hx hxm :=
  (leGlue_tagB_tagC_iff (markedPt k) b x).mpr hmx

-- [D-1921] not_iotaD_top_le_glueB
theorem not_iotaD_top_le_glueB {b : EndP (D k)} (hb : b ≠ ⊥) (hbt : b ≠ ⊤) :
    ¬ (iotaD k (⊤ : D k) ≤ glueB (markedPt k) b hb) := by
  rw [iotaD_top_eq_glueA]
  intro h
  have := (leGlue_tagA_tagB_iff (markedPt k) (⊤ : EndP (D k)) b hbt).mp h
  exact hmt' k (le_antisymm le_top this)

end CopyBCStructure
