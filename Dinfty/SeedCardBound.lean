import Dinfty.CopyCLow

open GluingTowerLibrary SierpinskiApplication

-- [D-3103] §The-base-independent-replacement-for-4-card-S
open scoped Classical

namespace SeedCardBound

open TwoPointAssembly CopyAClassification CopyBCStructure SeedLevelStep
open SeedSeparation MidAnchor TwoPointHypothesis CopyBExclusion CopyBAtoms
open CopyCLow

-- [D-3104] hmk'
private theorem hmk' (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-3105] hmtk'
private theorem hmtk' (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
-- [D-3106] hbtk'
private theorem hbtk' (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

variable (k : ℕ)

-- [D-3107] thr
noncomputable def thr (t : D k) : EndP (D k) := stepMap (dMid k) t

-- [D-3108] thr_joinIrred
theorem thr_joinIrred (t : D k) : JoinIrred (EndP (D k)) (thr k t) :=
  (jiEquiv (t, (⟨dMid k, D_mid_joinIrred k⟩ : {v : D k // JoinIrred (D k) v}))).2

-- [D-3109] thr_le
theorem thr_le (t : D k) : thr k t ≤ markedPt k := by
  intro y
  show stepMap (dMid k) t y ≤ (constHom (dMid k) : EndP (D k)) y
  by_cases h : t ≤ y
  · rw [stepMap_apply_of_ge (dMid k) t h]
    exact le_refl _
  · rw [stepMap_apply_of_not_ge (dMid k) t h]
    exact bot_le

-- [D-3110] thr_injective
theorem thr_injective : Function.Injective (thr k) := by
  intro a b h
  exact ((stepMap_inj_of_ne_bot (dMid_ne_bot k) (dMid_ne_bot k) h).2)

-- [D-3111] seedCopy
noncomputable def seedCopy {y : D (k + 1)}
    (hle : ∀ v : EndP (D k), v ≤ markedPt k →
      (glueA (markedPt k) v : D (k + 1)) ≤ y) (t : D k) : LevelSeed (k + 1) y :=
  ⟨glueA (markedPt k) (thr k t),
   (joinIrred_glueA_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) (thr k t)).mpr
     (thr_joinIrred k t),
   hle (thr k t) (thr_le k t)⟩

-- [D-3112] seedCopy_injective
theorem seedCopy_injective {y : D (k + 1)}
    (hle : ∀ v : EndP (D k), v ≤ markedPt k →
      (glueA (markedPt k) v : D (k + 1)) ≤ y) :
    Function.Injective (seedCopy k hle) := by
  intro a b h
  refine thr_injective k ?_
  exact glueA_injective (markedPt k) (congrArg Subtype.val h)

-- [D-3113] card_D_lt_card_seed
theorem card_D_lt_card_seed {y : D (k + 1)} (hy : JoinIrred (D (k + 1)) y)
    (hle : ∀ v : EndP (D k), v ≤ markedPt k →
      (glueA (markedPt k) v : D (k + 1)) ≤ y)
    (hnotA : ¬ ∃ v : EndP (D k), y = glueA (markedPt k) v) :
    Fintype.card (D k) < Fintype.card (LevelSeed (k + 1) y) := by
  refine Fintype.card_lt_of_injective_of_notMem (seedCopy k hle)
    (seedCopy_injective k hle) (b := (⟨y, hy, le_refl y⟩ : LevelSeed (k + 1) y)) ?_
  rintro ⟨t, ht⟩
  exact hnotA ⟨thr k t, (congrArg Subtype.val ht).symm⟩

-- [D-3114] §The-two-instances
-- [D-3115] card_D_lt_card_seed_B
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

-- [D-3116] card_D_lt_card_seed_C
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

-- [D-3117] card_D_lt_card_seed_notA
theorem card_D_lt_card_seed_notA {y : D (k + 1)} (hy : JoinIrred (D (k + 1)) y)
    (hnotA : ¬ ∃ F : EndP (D k), y = glueA (markedPt k) F) :
    Fintype.card (D k) < Fintype.card (LevelSeed (k + 1) y) := by
  rcases dSuccCases k y with ⟨v, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, hxm, rfl⟩
  · exact absurd ⟨v, rfl⟩ hnotA
  · exact card_D_lt_card_seed_B k hx hy
  · exact card_D_lt_card_seed_C k hx hxm hy

-- [D-3118] four_le_card_seed_zero
theorem four_le_card_seed_zero {x : EndP (D 0)} (hx : x ≠ ⊥)
    (hy : JoinIrred (D (0 + 1)) (glueB (markedPt 0) x hx)) :
    4 ≤ Fintype.card (LevelSeed (0 + 1) (glueB (markedPt 0) x hx)) := by
  have h := card_D_lt_card_seed_B 0 hx hy
  rw [CopyBAtoms.card_D_zero] at h
  omega

end SeedCardBound
