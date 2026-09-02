import Dinfty.CopyBExclusion

open GluingTowerLibrary SierpinskiApplication

-- [D-2957] §Copy-B-part-2-the-atoms-of-the-seed
open scoped Classical

namespace CopyBAtoms

open TwoPointAssembly CopyAClassification CopyBCStructure SeedShapeProof
open SeedLevelStep WeakProductAbsorption AtomFactorGeneration WeakProdFactorization
open SeedSeparation MidAnchor SeedChain TwoPointHypothesis CopyBExclusion
open TowerNoAbsorption TowerCardGrowth

-- [D-2958] hmk'
private theorem hmk' (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-2959] hmtk'
private theorem hmtk' (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
-- [D-2960] hbtk'
private theorem hbtk' (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

-- [D-2961] §Everything-below-a-copy-B-point-is-copy
section Seed

variable {k : ℕ} {x : EndP (D k)} (hx : x ≠ ⊥) (hxt : x ≠ ⊤)

-- [D-2962] seed_cases
include hxt in
theorem seed_cases (u : D (k + 1)) (hu : u ≤ glueB (markedPt k) x hx) :
    (∃ v : EndP (D k), v ≤ markedPt k ∧ u = glueA (markedPt k) v)
      ∨ (∃ (b : EndP (D k)) (hb : b ≠ ⊥), u = glueB (markedPt k) b hb) := by
  rcases dSuccCases k u with ⟨v, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, hcm, rfl⟩
  · exact Or.inl ⟨v, (leGlue_tagA_tagB_iff (markedPt k) v x hxt).mp hu, rfl⟩
  · exact Or.inr ⟨b, hb, rfl⟩
  · exact absurd hu (not_leGlue_tagC_tagB (markedPt k) c x hxt)

-- [D-2963] copyA_le_copyB
theorem copyA_le_copyB {v b : EndP (D k)} (hvm : v ≤ markedPt k) (hb : b ≠ ⊥) :
    (glueA (markedPt k) v : D (k + 1)) ≤ glueB (markedPt k) b hb :=
  leGlue_tagA_tagB_of_le (markedPt k) v b hvm

-- [D-2964] dMid_ne_copyB
theorem dMid_ne_copyB : dMid (k + 1) ≠ glueB (markedPt k) x hx := by
  intro hcon
  have h2 : (Sum.inl (markedPt k) : GlueBase (EndP (D k))) = Sum.inr (Sum.inl x) :=
    congrArg Subtype.val hcon
  simp at h2

end Seed

-- [D-2965] §The-atoms-of-the-dualised-seed
section Atoms

variable {k : ℕ} {x : EndP (D k)} {hx : x ≠ ⊥} (hxt : x ≠ ⊤)
variable [OrderBot ((LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)]
variable (hbot : (OrderDual.ofDual
    (⊥ : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)).1 = glueB (markedPt k) x hx)

include hxt hbot

-- [D-2966] copyA_atom_eq
omit hxt in
theorem copyA_atom_eq (α : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)
    (hα : IsAtom α) {v : EndP (D k)} (hvm : v ≤ markedPt k)
    (hv : (OrderDual.ofDual α).1 = glueA (markedPt k) v) :
    α = OrderDual.toDual (dMidSeed k hx) := by
  have hle : (OrderDual.toDual (dMidSeed k hx)) ≤ α := by
    show (OrderDual.ofDual α).1 ≤ dMid (k + 1)
    rw [hv, dMid_eq_glueA]
    exact (glueA_le_iff (markedPt k) (hmk' k) v (markedPt k)).mpr hvm
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hb : dMid (k + 1) = (OrderDual.ofDual
        (⊥ : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)).1 :=
      congrArg (fun w => (OrderDual.ofDual w).1) (hα.2 _ hlt)
    rw [hbot] at hb
    exact dMid_ne_copyB hx hb
  · exact heq.symm

-- [D-2967] atom_unique_of_dMid_atom
theorem atom_unique_of_dMid_atom (hd : IsAtom (OrderDual.toDual (dMidSeed k hx)))
    (β : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ) (hβ : IsAtom β) :
    β = OrderDual.toDual (dMidSeed k hx) := by
  rcases seed_cases hx hxt (OrderDual.ofDual β).1 (OrderDual.ofDual β).2.2 with
    ⟨v, hvm, hv⟩ | ⟨b, hb, hv⟩
  · exact copyA_atom_eq hbot β hβ hvm hv
  · have hle : β ≤ OrderDual.toDual (dMidSeed k hx) := by
      show dMid (k + 1) ≤ (OrderDual.ofDual β).1
      rw [hv]
      exact dMid_le_glueB k hb
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact absurd (hd.2 _ hlt) hβ.1
    · exact heq

-- [D-2968] atom_copyB_of_two
theorem atom_copyB_of_two (α₁ α₂ : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)
    (h1 : IsAtom α₁) (h2 : IsAtom α₂) (hne : α₁ ≠ α₂)
    (α : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ) (hα : IsAtom α) :
    ∃ (b : EndP (D k)) (hb : b ≠ ⊥),
      (OrderDual.ofDual α).1 = glueB (markedPt k) b hb := by
  rcases seed_cases hx hxt (OrderDual.ofDual α).1 (OrderDual.ofDual α).2.2 with
    ⟨v, hvm, hv⟩ | h
  · exfalso
    have hαd := copyA_atom_eq hbot α hα hvm hv
    have hd : IsAtom (OrderDual.toDual (dMidSeed k hx)) := hαd ▸ hα
    exact hne ((atom_unique_of_dMid_atom hxt hbot hd α₁ h1).trans
      (atom_unique_of_dMid_atom hxt hbot hd α₂ h2).symm)
  · exact h

-- [D-2969] factorPart_le_dMid
theorem factorPart_le_dMid (α₁ α₂ : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)
    (h1 : IsAtom α₁) (h2 : IsAtom α₂) (hne : α₁ ≠ α₂)
    (u : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)
    (hu : u ∈ factorPart ((LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)) :
    u ≤ OrderDual.toDual (dMidSeed k hx) := by
  rcases seed_cases hx hxt (OrderDual.ofDual u).1 (OrderDual.ofDual u).2.2 with
    ⟨v, hvm, hv⟩ | ⟨b, hb, hv⟩
  · exfalso
    obtain ⟨γ, hγ, hmem⟩ := hu
    obtain ⟨b1, hb1, hv1⟩ := atom_copyB_of_two hxt hbot α₁ α₂ h1 h2 hne α₁ h1
    obtain ⟨b2, hb2, hv2⟩ := atom_copyB_of_two hxt hbot α₁ α₂ h1 h2 hne α₂ h2
    have e1 : α₁ ≤ u := by
      show (OrderDual.ofDual u).1 ≤ (OrderDual.ofDual α₁).1
      rw [hv, hv1]
      exact copyA_le_copyB hvm hb1
    have e2 : α₂ ≤ u := by
      show (OrderDual.ofDual u).1 ≤ (OrderDual.ofDual α₂).1
      rw [hv, hv2]
      exact copyA_le_copyB hvm hb2
    exact hne ((hmem α₁ h1 e1).trans (hmem α₂ h2 e2).symm)
  · show dMid (k + 1) ≤ (OrderDual.ofDual u).1
    rw [hv]
    exact dMid_le_glueB k hb

-- [D-2970] not_genByFactors_of_two_atoms
theorem not_genByFactors_of_two_atoms
    (α₁ α₂ : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)
    (h1 : IsAtom α₁) (h2 : IsAtom α₂) (hne : α₁ ≠ α₂) :
    ¬ GenByFactors ((LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ) :=
  not_genByFactors_of_strict_upper
    (t := OrderDual.toDual (dMidSeed k hx)) (w := OrderDual.toDual (wSeed k hx))
    (factorPart_le_dMid hxt hbot α₁ α₂ h1 h2 hne)
    (OrderDual.toDual_lt_toDual.mpr (wSeed_lt_dMidSeed k hx))

end Atoms

-- [D-2971] §The-seed-has-at-least-four-elements
section Count

variable (k : ℕ)

-- [D-2972] gMid
noncomputable def gMid : EndP (D k) := stepMap (dMid k) (dMid k)

-- [D-2973] gMid_joinIrred
theorem gMid_joinIrred : JoinIrred (EndP (D k)) (gMid k) :=
  (jiEquiv ((dMid k), (⟨dMid k, D_mid_joinIrred k⟩ : {v : D k // JoinIrred (D k) v}))).2

-- [D-2974] gMid_le
theorem gMid_le : gMid k ≤ markedPt k := by
  intro y
  show stepMap (dMid k) (dMid k) y ≤ (constHom (dMid k) : EndP (D k)) y
  by_cases h : dMid k ≤ y
  · rw [stepMap_apply_of_ge (dMid k) (dMid k) h]
    exact le_refl _
  · rw [stepMap_apply_of_not_ge (dMid k) (dMid k) h]
    exact bot_le

-- [D-2975] gMid_ne_marked
theorem gMid_ne_marked : gMid k ≠ markedPt k := by
  intro hcon
  have h1 : gMid k (⊥ : D k) = (⊥ : D k) :=
    stepMap_apply_of_not_ge (dMid k) (dMid k)
      (fun h => dMid_ne_bot k (le_antisymm h bot_le))
  rw [hcon] at h1
  exact dMid_ne_bot k h1

-- [D-2976] gMid_ne_gLow
theorem gMid_ne_gLow : gMid k ≠ gLow k := by
  intro hcon
  have h1 : gMid k (dMid k) = dMid k :=
    stepMap_apply_of_ge (dMid k) (dMid k) (le_refl _)
  have h2 : gLow k (dMid k) = (⊥ : D k) :=
    stepMap_apply_of_not_ge (dMid k) (⊤ : D k)
      (fun h => dMid_ne_top k (le_antisymm le_top h))
  rw [hcon, h2] at h1
  exact dMid_ne_bot k h1.symm

variable {x : EndP (D k)} (hx : x ≠ ⊥)

-- [D-2977] gMidSeed
noncomputable def gMidSeed : LevelSeed (k + 1) (glueB (markedPt k) x hx) :=
  ⟨glueA (markedPt k) (gMid k),
   (joinIrred_glueA_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) (gMid k)).mpr
     (gMid_joinIrred k),
   leGlue_tagA_tagB_of_le (markedPt k) (gMid k) x (gMid_le k)⟩

-- [D-2978] four_le_card_seed
theorem four_le_card_seed (hy : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx)) :
    4 ≤ Fintype.card (LevelSeed (k + 1) (glueB (markedPt k) x hx)) := by
  have hval : ∀ a b : LevelSeed (k + 1) (glueB (markedPt k) x hx),
      (a.1.1 : GlueBase (EndP (D k))) ≠ b.1.1 → a ≠ b :=
    fun a b h hcon => h (congrArg (fun w =>
      (Subtype.val (Subtype.val w) : GlueBase (EndP (D k)))) hcon)
  set e1 : LevelSeed (k + 1) (glueB (markedPt k) x hx) := dMidSeed k hx with he1
  set e2 : LevelSeed (k + 1) (glueB (markedPt k) x hx) := gMidSeed k hx with he2
  set e3 : LevelSeed (k + 1) (glueB (markedPt k) x hx) := wSeed k hx with he3
  set e4 : LevelSeed (k + 1) (glueB (markedPt k) x hx) :=
    ⟨glueB (markedPt k) x hx, hy, le_refl _⟩ with he4
  have h12 : e1 ≠ e2 := hval _ _ (by
    intro hcon
    have h2 : (Sum.inl (markedPt k) : GlueBase (EndP (D k))) = Sum.inl (gMid k) := hcon
    exact gMid_ne_marked k (Sum.inl.inj h2).symm)
  have h13 : e1 ≠ e3 := hval _ _ (by
    intro hcon
    have h2 : (Sum.inl (markedPt k) : GlueBase (EndP (D k))) = Sum.inl (gLow k) := hcon
    exact gLow_ne k (Sum.inl.inj h2).symm)
  have h23 : e2 ≠ e3 := hval _ _ (by
    intro hcon
    have h2 : (Sum.inl (gMid k) : GlueBase (EndP (D k))) = Sum.inl (gLow k) := hcon
    exact gMid_ne_gLow k (Sum.inl.inj h2))
  have h14 : e1 ≠ e4 := hval _ _ (by
    intro hcon
    have h2 : (Sum.inl (markedPt k) : GlueBase (EndP (D k))) = Sum.inr (Sum.inl x) := hcon
    simp at h2)
  have h24 : e2 ≠ e4 := hval _ _ (by
    intro hcon
    have h2 : (Sum.inl (gMid k) : GlueBase (EndP (D k))) = Sum.inr (Sum.inl x) := hcon
    simp at h2)
  have h34 : e3 ≠ e4 := hval _ _ (by
    intro hcon
    have h2 : (Sum.inl (gLow k) : GlueBase (EndP (D k))) = Sum.inr (Sum.inl x) := hcon
    simp at h2)
  have hcard : ({e1, e2, e3, e4} :
      Finset (LevelSeed (k + 1) (glueB (markedPt k) x hx))).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_insert_of_notMem (by simp [h23, h24]),
      Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
  calc (4 : ℕ) = ({e1, e2, e3, e4} : Finset _).card := hcard.symm
    _ ≤ Fintype.card (LevelSeed (k + 1) (glueB (markedPt k) x hx)) := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ _)

end Count

-- [D-2979] §The-base-level-has-three-elements
-- [D-2980] card_D_zero
theorem card_D_zero : Fintype.card (D 0) = 3 := rfl

-- [D-2981] §The-copy-B-exclusion
-- [D-2982] copyB_forces_false
theorem copyB_forces_false {T : Type} [PartialOrder T] [OrderBot T] [IsAtomic T]
    (hT : GenByFactors T) (k : ℕ) {x : EndP (D k)} (hx : x ≠ ⊥)
    (hy : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx))
    (e : (WeakProd (Fam 0) × T) ≃o
      (WeakProd (Fam (k + 1)) × (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)) :
    False := by
  letI := levelSeedDualBot hy
  haveI : IsAtomic ((LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ) :=
    GluingTowerLibrary.isAtomic_of_finite
  have hxt : x ≠ ⊤ := copyB_ne_top k hx hy
  have hbot : (OrderDual.ofDual
      (⊥ : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ)).1
      = glueB (markedPt k) x hx := rfl
  by_cases hmulti : ∃ α β : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ,
      IsAtom α ∧ IsAtom β ∧ α ≠ β
  · obtain ⟨α, β, hα, hβ, hne⟩ := hmulti
    haveI : IsAtomic (WeakProd (Fam 0)) :=
      isAtomic_weakProd (fun j => lamD (0 + j)) (fun j => lamD_ne_bot (0 + j))
        (fun j => lamD_le (0 + j))
    haveI : IsAtomic (WeakProd (Fam (k + 1))) :=
      isAtomic_weakProd (fun j => lamD (k + 1 + j)) (fun j => lamD_ne_bot (k + 1 + j))
        (fun j => lamD_le (k + 1 + j))
    have hsrc : GenByFactors (WeakProd (Fam 0) × T) :=
      genByFactors_prod_iff.mpr
        ⟨genByFactors_weakProd (D := Fam 0) (fun j => lamD (0 + j))
          (fun j => lamD_ne_bot (0 + j)) (fun j => lamD_le (0 + j)), hT⟩
    have htgt := genByFactors_prod_iff.mp (genByFactors_orderIso e hsrc)
    exact not_genByFactors_of_two_atoms hxt hbot α β hα hβ hne htgt.2
  · push_neg at hmulti
    have huniq : ∀ α β : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ,
        IsAtom α → IsAtom β → α = β := fun α β hα hβ => hmulti α β hα hβ
    have hsmall : ∀ (j : ℕ), j ≤ k →
        ∀ i, Fintype.card (Fam 0 j) < Fintype.card (Fam (k + 1) i) := by
      intro j hj i
      show Fintype.card (D (0 + j)) < Fintype.card (D (k + 1 + i))
      exact card_D_strictMono (by omega)
    obtain ⟨β0, hβ0, ⟨iso0⟩⟩ := factor_in_finite_pieceL
      (D := Fam 0) (E := Fam (k + 1)) (T := T)
      (fun j => lamD (0 + j)) (fun j => lamD (k + 1 + j))
      (fun j => lamD_ne_bot (0 + j)) (fun j => lamD_le (0 + j))
      (fun j => lamD_ne_bot (k + 1 + j)) (fun j => lamD_le (k + 1 + j))
      e 0 (hsmall 0 (Nat.zero_le k))
    obtain ⟨βk, hβk, ⟨isok⟩⟩ := factor_in_finite_pieceL
      (D := Fam 0) (E := Fam (k + 1)) (T := T)
      (fun j => lamD (0 + j)) (fun j => lamD (k + 1 + j))
      (fun j => lamD_ne_bot (0 + j)) (fun j => lamD_le (0 + j))
      (fun j => lamD_ne_bot (k + 1 + j)) (fun j => lamD_le (k + 1 + j))
      e k (hsmall k (le_refl k))
    have hββ : βk = β0 := huniq βk β0 hβk hβ0
    subst hββ
    have hc0 : Fintype.card (D (0 + 0))
        = Fintype.card ↥(atomFactor
            ((LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ) βk) :=
      Fintype.card_congr iso0.toEquiv
    have hck : Fintype.card (D (0 + k))
        = Fintype.card ↥(atomFactor
            ((LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ) βk) :=
      Fintype.card_congr isok.toEquiv
    have hk0 : k = 0 := by
      have hinj := card_D_strictMono.injective
        (a₁ := 0 + 0) (a₂ := 0 + k) (hc0.trans hck.symm)
      omega
    subst hk0
    have huniv : ∀ w : (LevelSeed (0 + 1) (glueB (markedPt 0) x hx))ᵒᵈ,
        w ∈ atomFactor ((LevelSeed (0 + 1) (glueB (markedPt 0) x hx))ᵒᵈ) βk :=
      fun w γ hγ _ => huniq γ βk hγ hβk
    have hcS : Fintype.card ↥(atomFactor
        ((LevelSeed (0 + 1) (glueB (markedPt 0) x hx))ᵒᵈ) βk)
        = Fintype.card ((LevelSeed (0 + 1) (glueB (markedPt 0) x hx))ᵒᵈ) :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv huniv)
    have hdual : Fintype.card ((LevelSeed (0 + 1) (glueB (markedPt 0) x hx))ᵒᵈ)
        = Fintype.card (LevelSeed (0 + 1) (glueB (markedPt 0) x hx)) :=
      Fintype.card_congr (OrderDual.ofDual)
    have hc0' : Fintype.card (D 0)
        = Fintype.card ↥(atomFactor
            ((LevelSeed (0 + 1) (glueB (markedPt 0) x hx))ᵒᵈ) βk) := hc0
    rw [card_D_zero] at hc0'
    have h4 := four_le_card_seed 0 hx hy
    omega

-- [D-2983] §The-copy-B-half-of-CopyBCExcludedFor
-- [D-2984] copyB_excluded_gen
theorem copyB_excluded_gen (z : DInfty) {T : Type} [PartialOrder T] [OrderBot T]
    [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam 0) × T)) (hT : GenByFactors T)
    (k : ℕ) (x : EndP (D k)) (hx : x ≠ ⊥)
    (hji : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx)) :
    ¬ Nonempty (JBelow (toD (k + 1) (glueB (markedPt k) x hx)) ≃o JBelow z) := by
  rintro ⟨e⟩
  exact copyB_forces_false hT k hx hji
    (hz.symm.trans (e.dual.symm.trans (seedShape (k + 1) (glueB (markedPt k) x hx) hji)))

-- [D-2985] copyBCExcluded_of_C
theorem copyBCExcluded_of_C (z : DInfty) {T : Type} [PartialOrder T] [OrderBot T]
    [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam 0) × T)) (hT : GenByFactors T)
    (hC : ∀ (k : ℕ) (x : EndP (D k)) (hx : x ≠ ⊥) (hxm : x ≠ markedPt k),
      JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm) →
      ¬ Nonempty (JBelow (toD (k + 1) (glueC (markedPt k) x hx hxm)) ≃o JBelow z)) :
    CopyBCExcludedFor z :=
  copyBC_of_B_and_C z (fun k x hx hji => copyB_excluded_gen z hz hT k x hx hji) hC

-- [D-2986] CopyCExcludedFor
def CopyCExcludedFor (z : DInfty) : Prop :=
  ∀ (k : ℕ) (x : EndP (D k)) (hx : x ≠ ⊥) (hxm : x ≠ markedPt k),
    JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm) →
    ¬ Nonempty (JBelow (toD (k + 1) (glueC (markedPt k) x hx hxm)) ≃o JBelow z)

-- [D-2987] copyBC_midInf_of_C
theorem copyBC_midInf_of_C (hC : CopyCExcludedFor midInf) : CopyBCExcludedFor midInf :=
  copyBCExcluded_of_C midInf (seedShape 0 (dMid 0) SeedsDiffer.joinIrred_D0_mid)
    genByFactors_base_midInf hC

-- [D-2988] copyBC_topJ_of_C
theorem copyBC_topJ_of_C (hC : CopyCExcludedFor (toD 0 (⊤ : D 0))) :
    CopyBCExcludedFor (toD 0 (⊤ : D 0)) :=
  copyBCExcluded_of_C (toD 0 (⊤ : D 0)) (seedShape 0 (⊤ : D 0) joinIrred_D0_top)
    genByFactors_base_topJ hC

-- [D-2989] twoPointFixed_of_C
theorem twoPointFixed_of_C (h₁ : CopyCExcludedFor midInf)
    (h₂ : CopyCExcludedFor (toD 0 (⊤ : D 0))) : TwoPointFixed :=
  twoPointFixed (copyBC_midInf_of_C h₁) (copyBC_topJ_of_C h₂)

end CopyBAtoms
