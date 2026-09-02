import Dinfty.TwoPointAssembly

open GluingTowerLibrary SierpinskiApplication

-- [D-1945] §Copy-B-part-1-the-split-and-the-pieces
open scoped Classical

namespace CopyBExclusion

open TwoPointAssembly CopyAClassification CopyBCStructure SeedShapeProof
open SeedLevelStep WeakProductAbsorption AtomFactorGeneration
open SeedSeparation MidAnchor SeedChain TwoPointHypothesis

-- [D-1946] hmk'
private theorem hmk' (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-1947] hmtk'
private theorem hmtk' (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
-- [D-1948] hbtk'
private theorem hbtk' (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

-- [D-1949] obMid
noncomputable local instance obMid : OrderBot (Base 0 (dMid 0)) :=
  TwoPointAssembly.levelSeedDualBot SeedsDiffer.joinIrred_D0_mid
-- [D-1950] obTop
noncomputable local instance obTop : OrderBot (Base 0 (⊤ : D 0)) :=
  TwoPointAssembly.levelSeedDualBot joinIrred_D0_top

-- [D-1951] §The-case-split-restated-at-the-tower
-- [D-1952] canonBFix
theorem canonBFix {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P]
    {m w : P} (h : canon m (Sum.inr (Sum.inl w)) = Sum.inr (Sum.inl w)) : w ≠ ⊥ := by
  intro hw
  subst hw
  simp only [canon] at h
  split_ifs at h <;> simp at h

-- [D-1953] canonCFixBot
theorem canonCFixBot {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P]
    {m w : P} (h : canon m (Sum.inr (Sum.inr w)) = Sum.inr (Sum.inr w)) : w ≠ ⊥ := by
  intro hw
  subst hw
  simp only [canon] at h
  split_ifs at h <;> simp at h

-- [D-1954] dSuccCases
theorem dSuccCases (k : ℕ) (y : D (k + 1)) :
    (∃ v : EndP (D k), y = glueA (markedPt k) v)
      ∨ (∃ (x : EndP (D k)) (hx : x ≠ ⊥), y = glueB (markedPt k) x hx)
      ∨ (∃ (x : EndP (D k)) (hx : x ≠ ⊥) (hxm : x ≠ markedPt k),
          y = glueC (markedPt k) x hx hxm) := by
  obtain ⟨val, hval⟩ := y
  rcases val with v | w | w
  · exact Or.inl ⟨v, Subtype.ext rfl⟩
  · exact Or.inr (Or.inl ⟨w, canonBFix hval, Subtype.ext rfl⟩)
  · refine Or.inr (Or.inr ⟨w, canonCFixBot hval, ?_, Subtype.ext rfl⟩)
    intro hcon
    rw [hcon] at hval
    simp only [canon] at hval
    split_ifs at hval with h1 h2
    · simp at hval
    · exact h2 rfl

-- [D-1955] §Splitting-the-obligation
-- [D-1956] copyBC_of_B_and_C
theorem copyBC_of_B_and_C (z : DInfty)
    (hB : ∀ (k : ℕ) (x : EndP (D k)) (hx : x ≠ ⊥),
      JoinIrred (D (k + 1)) (glueB (markedPt k) x hx) →
      ¬ Nonempty (JBelow (toD (k + 1) (glueB (markedPt k) x hx)) ≃o JBelow z))
    (hC : ∀ (k : ℕ) (x : EndP (D k)) (hx : x ≠ ⊥) (hxm : x ≠ markedPt k),
      JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm) →
      ¬ Nonempty (JBelow (toD (k + 1) (glueC (markedPt k) x hx hxm)) ≃o JBelow z)) :
    CopyBCExcludedFor z := by
  intro k y hy hnotA
  rcases dSuccCases k y with ⟨v, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, hxm, rfl⟩
  · exact absurd ⟨v, rfl⟩ hnotA
  · exact hB k x hx hy
  · exact hC k x hx hxm hy

-- [D-1957] §Generation-at-the-two-left-hand-pieces
-- [D-1958] genByFactors_of_subsingleton
theorem genByFactors_of_subsingleton {L : Type} [PartialOrder L] [OrderBot L]
    [Subsingleton L] : GenByFactors L := by
  intro w
  refine ⟨fun u hu => hu.2, ?_⟩
  intro v _
  exact le_of_eq (Subsingleton.elim w v)

-- [D-1959] genByFactors_of_atom_unique
theorem genByFactors_of_atom_unique {L : Type} [PartialOrder L] [OrderBot L] {α : L}
    (hα : IsAtom α) (huniq : ∀ β : L, IsAtom β → β = α) : GenByFactors L := by
  have hfp : ∀ w : L, w ∈ factorPart L := fun _ => ⟨α, hα, fun β hβ _ => huniq β hβ⟩
  intro w
  refine ⟨fun u hu => hu.2, ?_⟩
  intro v hv
  exact hv ⟨hfp w, le_refl w⟩

-- [D-1960] genByFactors_base_midInf
theorem genByFactors_base_midInf : GenByFactors (Base 0 (dMid 0)) :=
  genByFactors_of_subsingleton

-- [D-1961] §topJ-s-left-hand-piece-is-a-two-chain-so-it-has
-- [D-1962] topAtom
noncomputable def topAtom : Base 0 (⊤ : D 0) := OrderDual.toDual SeedsDiffer.topSeedOne

-- [D-1963] isAtom_topAtom
theorem isAtom_topAtom : IsAtom topAtom := by
  constructor
  · intro hcon
    exact SeedsDiffer.topSeed_ne (congrArg OrderDual.ofDual hcon).symm
  · intro b hb
    rcases SeedsDiffer.mem_levelSeedZeroTop (OrderDual.ofDual b) with h | h
    · exfalso
      have hb2 : b = topAtom := Subtype.ext h
      exact absurd hb2 (ne_of_lt hb)
    · exact Subtype.ext h

-- [D-1964] atom_base_top_unique
theorem atom_base_top_unique (β : Base 0 (⊤ : D 0)) (hβ : IsAtom β) : β = topAtom := by
  rcases SeedsDiffer.mem_levelSeedZeroTop (OrderDual.ofDual β) with h | h
  · exact Subtype.ext h
  · exact absurd (Subtype.ext h : β = (⊥ : Base 0 (⊤ : D 0))) hβ.1

-- [D-1965] genByFactors_base_topJ
theorem genByFactors_base_topJ : GenByFactors (Base 0 (⊤ : D 0)) :=
  genByFactors_of_atom_unique isAtom_topAtom atom_base_top_unique

-- [D-1966] §The-two-witnesses-inside-a-copy-B-seed
section Witnesses

variable (k : ℕ) {x : EndP (D k)} (hx : x ≠ ⊥)

-- [D-1967] dMidSeed
noncomputable def dMidSeed : LevelSeed (k + 1) (glueB (markedPt k) x hx) :=
  ⟨dMid (k + 1), D_mid_joinIrred (k + 1), dMid_le_glueB k hx⟩

-- [D-1968] gLow
noncomputable def gLow : EndP (D k) := stepMap (dMid k) (⊤ : D k)

-- [D-1969] gLow_joinIrred
theorem gLow_joinIrred : JoinIrred (EndP (D k)) (gLow k) :=
  (jiEquiv ((⊤ : D k), (⟨dMid k, D_mid_joinIrred k⟩ : {v : D k // JoinIrred (D k) v}))).2

-- [D-1970] gLow_le
theorem gLow_le : gLow k ≤ markedPt k := by
  intro y
  show stepMap (dMid k) (⊤ : D k) y ≤ (constHom (dMid k) : EndP (D k)) y
  by_cases h : (⊤ : D k) ≤ y
  · rw [stepMap_apply_of_ge (dMid k) (⊤ : D k) h]
    exact le_refl _
  · rw [stepMap_apply_of_not_ge (dMid k) (⊤ : D k) h]
    exact bot_le

-- [D-1971] gLow_ne
theorem gLow_ne : gLow k ≠ markedPt k := by
  intro hcon
  have hbt : (⊥ : D k) ≠ (⊤ : D k) := by
    letI := (towerLevel k).nontriv
    exact bot_ne_top_of_nontrivial (P := D k)
  have h1 : gLow k (⊥ : D k) = (⊥ : D k) :=
    stepMap_apply_of_not_ge (dMid k) (⊤ : D k) (fun h => hbt (le_antisymm bot_le h))
  rw [hcon] at h1
  exact dMid_ne_bot k h1

-- [D-1972] gLow_lt
theorem gLow_lt : gLow k < markedPt k := lt_of_le_of_ne (gLow_le k) (gLow_ne k)

-- [D-1973] wSeed
noncomputable def wSeed : LevelSeed (k + 1) (glueB (markedPt k) x hx) :=
  ⟨glueA (markedPt k) (gLow k),
   (joinIrred_glueA_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) (gLow k)).mpr
     (gLow_joinIrred k),
   leGlue_tagA_tagB_of_le (markedPt k) (gLow k) x (gLow_le k)⟩

-- [D-1974] wSeed_lt_dMidSeed
theorem wSeed_lt_dMidSeed : wSeed k hx < dMidSeed k hx := by
  refine lt_of_le_of_ne ?_ ?_
  · show glueA (markedPt k) (gLow k) ≤ dMid (k + 1)
    rw [dMid_eq_glueA]
    exact (glueA_le_iff (markedPt k) (hmk' k) (gLow k) (markedPt k)).mpr (gLow_le k)
  · intro hcon
    refine gLow_ne k ?_
    have h := congrArg Subtype.val hcon
    show gLow k = markedPt k
    exact glueA_injective (markedPt k) (h.trans (dMid_eq_glueA k))

end Witnesses

-- [D-1975] §What-copy-B-needs-now-supplied-in-Dinfty
-- [D-1976] §The-seam-is-not-join-irreducible
section Seam

variable (k : ℕ)

-- [D-1977] seam_not_joinIrred
theorem seam_not_joinIrred :
    ¬ JoinIrred (D (k + 1))
      (glueB (markedPt k) (⊤ : EndP (D k)) (Ne.symm (hbtk' k))) := by
  intro hji
  set Y : D (k + 1) := glueB (markedPt k) (⊤ : EndP (D k)) (Ne.symm (hbtk' k)) with hYdef
  set A : D (k + 1) := glueA (markedPt k) (⊤ : EndP (D k)) with hAdef
  set B : D (k + 1) := glueB (markedPt k) (markedPt k) (hmk' k) with hBdef
  have hAY : A ≤ Y := by
    show leGlue (markedPt k) (Sum.inl (⊤ : EndP (D k)))
      (Sum.inr (Sum.inl (⊤ : EndP (D k))))
    exact ⟨Sum.inl (⊤ : EndP (D k)), self_mem_occs _ _,
      Sum.inr (Sum.inr (markedPt k)), by simp [occs], trivial⟩
  have hBY : B ≤ Y := by
    show leGlue (markedPt k) (Sum.inr (Sum.inl (markedPt k)))
      (Sum.inr (Sum.inl (⊤ : EndP (D k))))
    exact ⟨Sum.inr (Sum.inl (markedPt k)), self_mem_occs _ _,
      Sum.inr (Sum.inl (⊤ : EndP (D k))), self_mem_occs _ _, le_top⟩
  have hlub : ∀ u : D (k + 1), A ≤ u → B ≤ u → Y ≤ u := by
    intro u h1 h2
    rcases dSuccCases k u with ⟨v, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, hcm, rfl⟩
    · exact absurd h2 (not_leGlue_tagB_tagA (markedPt k) (markedPt k) v
        (hmk' k) (hbtk' k) (hmk' k))
    · by_cases hbt : b = (⊤ : EndP (D k))
      · show leGlue (markedPt k) (Sum.inr (Sum.inl (⊤ : EndP (D k))))
          (Sum.inr (Sum.inl b))
        exact ⟨Sum.inr (Sum.inl (⊤ : EndP (D k))), self_mem_occs _ _,
          Sum.inr (Sum.inl b), self_mem_occs _ _, le_of_eq hbt.symm⟩
      · exact absurd ((leGlue_tagA_tagB_iff (markedPt k) (⊤ : EndP (D k)) b hbt).mp h1)
          (fun hcon => hmtk' k (le_antisymm le_top hcon))
    · exact (leGlue_tagB_tagC_iff (markedPt k) (⊤ : EndP (D k)) c).mpr
        ((leGlue_tagB_tagC_iff (markedPt k) (markedPt k) c).mp h2)
  have hsup : A ⊔ B = Y :=
    le_antisymm (sup_le hAY hBY) (hlub (A ⊔ B) le_sup_left le_sup_right)
  rcases hji.2 A B hsup.symm with h | h
  · have hv : (Sum.inr (Sum.inl (⊤ : EndP (D k))) : GlueBase (EndP (D k)))
        = Sum.inl (⊤ : EndP (D k)) := congrArg Subtype.val h
    simp at hv
  · refine hmtk' k ?_
    have hv := congrArg Subtype.val h
    simp only [hYdef, hBdef] at hv
    exact (Sum.inl.inj (Sum.inr.inj hv)).symm

-- [D-1978] copyB_ne_top
theorem copyB_ne_top {x : EndP (D k)} (hx : x ≠ ⊥)
    (hji : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx)) : x ≠ (⊤ : EndP (D k)) := by
  intro hcon
  subst hcon
  exact seam_not_joinIrred k hji

end Seam

end CopyBExclusion
