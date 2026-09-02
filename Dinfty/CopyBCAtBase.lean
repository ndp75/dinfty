import Dinfty.SeedCardBound
import Dinfty.StageAssembly

open GluingTowerLibrary SierpinskiApplication

-- [D-3146] §Copy-B-and-copy-C-low-from-an-arbitrary-base
open scoped Classical

namespace CopyBCAtBase

open TwoPointAssembly CopyAClassification CopyBCStructure SeedShapeProof
open SeedLevelStep WeakProductAbsorption AtomFactorGeneration WeakProdFactorization
open SeedSeparation MidAnchor SeedChain TwoPointHypothesis CopyBExclusion
open CopyBAtoms CopyCLow TowerNoAbsorption TowerCardGrowth
open SeedCardBound StageAssembly

-- [D-3147] §The-single-atom-contradiction-at-an-arbitrary
-- [D-3148] single_atom_absurd
private theorem single_atom_absurd {T : Type} [PartialOrder T] [OrderBot T]
    [IsAtomic T] (n k : ℕ) (hnk : n ≤ k) {y : D (k + 1)}
    [OrderBot ((LevelSeed (k + 1) y)ᵒᵈ)] [IsAtomic ((LevelSeed (k + 1) y)ᵒᵈ)]
    (hbound : ∀ hnk' : n = k, Fintype.card (D n)
      < Fintype.card (LevelSeed (k + 1) y))
    (huniq : ∀ α β : (LevelSeed (k + 1) y)ᵒᵈ, IsAtom α → IsAtom β → α = β)
    (e : (WeakProd (Fam n) × T) ≃o
      (WeakProd (Fam (k + 1)) × (LevelSeed (k + 1) y)ᵒᵈ)) : False := by
  have hsmall : ∀ (j : ℕ), n + j ≤ k →
      ∀ i, Fintype.card (Fam n j) < Fintype.card (Fam (k + 1) i) := by
    intro j hj i
    show Fintype.card (D (n + j)) < Fintype.card (D (k + 1 + i))
    exact card_D_strictMono (by omega)
  obtain ⟨β0, hβ0, ⟨iso0⟩⟩ := WeakProdFactorization.factor_in_finite_pieceL
    (D := Fam n) (E := Fam (k + 1)) (T := T)
    (fun j => lamD (n + j)) (fun j => lamD (k + 1 + j))
    (fun j => lamD_ne_bot (n + j)) (fun j => lamD_le (n + j))
    (fun j => lamD_ne_bot (k + 1 + j)) (fun j => lamD_le (k + 1 + j))
    e 0 (hsmall 0 (by omega))
  obtain ⟨βk, hβk, ⟨isok⟩⟩ := WeakProdFactorization.factor_in_finite_pieceL
    (D := Fam n) (E := Fam (k + 1)) (T := T)
    (fun j => lamD (n + j)) (fun j => lamD (k + 1 + j))
    (fun j => lamD_ne_bot (n + j)) (fun j => lamD_le (n + j))
    (fun j => lamD_ne_bot (k + 1 + j)) (fun j => lamD_le (k + 1 + j))
    e (k - n) (hsmall (k - n) (by omega))
  have hββ : βk = β0 := huniq βk β0 hβk hβ0
  subst hββ
  have hc0 : Fintype.card (D (n + 0))
      = Fintype.card ↥(atomFactor ((LevelSeed (k + 1) y)ᵒᵈ) βk) :=
    Fintype.card_congr iso0.toEquiv
  have hck : Fintype.card (D (n + (k - n)))
      = Fintype.card ↥(atomFactor ((LevelSeed (k + 1) y)ᵒᵈ) βk) :=
    Fintype.card_congr isok.toEquiv
  have hnk2 : n = k := by
    have hinj := card_D_strictMono.injective
      (a₁ := n + 0) (a₂ := n + (k - n)) (hc0.trans hck.symm)
    omega
  have huniv : ∀ w : (LevelSeed (k + 1) y)ᵒᵈ,
      w ∈ atomFactor ((LevelSeed (k + 1) y)ᵒᵈ) βk :=
    fun w γ hγ _ => huniq γ βk hγ hβk
  have hcS : Fintype.card ↥(atomFactor ((LevelSeed (k + 1) y)ᵒᵈ) βk)
      = Fintype.card ((LevelSeed (k + 1) y)ᵒᵈ) :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv huniv)
  have hdual : Fintype.card ((LevelSeed (k + 1) y)ᵒᵈ)
      = Fintype.card (LevelSeed (k + 1) y) :=
    Fintype.card_congr (OrderDual.ofDual)
  have hb := hbound hnk2
  have hc0' : Fintype.card (D n)
      = Fintype.card ↥(atomFactor ((LevelSeed (k + 1) y)ᵒᵈ) βk) := hc0
  omega

-- [D-3149] §Copy-B
-- [D-3150] copyB_forces_false_at
theorem copyB_forces_false_at {T : Type} [PartialOrder T] [OrderBot T] [IsAtomic T]
    (hT : GenByFactors T) (n k : ℕ) (hnk : n ≤ k) {x : EndP (D k)} (hx : x ≠ ⊥)
    (hy : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx))
    (e : (WeakProd (Fam n) × T) ≃o
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
    haveI : IsAtomic (WeakProd (Fam n)) :=
      isAtomic_weakProd (fun j => lamD (n + j)) (fun j => lamD_ne_bot (n + j))
        (fun j => lamD_le (n + j))
    haveI : IsAtomic (WeakProd (Fam (k + 1))) :=
      isAtomic_weakProd (fun j => lamD (k + 1 + j)) (fun j => lamD_ne_bot (k + 1 + j))
        (fun j => lamD_le (k + 1 + j))
    have hsrc : GenByFactors (WeakProd (Fam n) × T) :=
      genByFactors_prod_iff.mpr
        ⟨genByFactors_weakProd (D := Fam n) (fun j => lamD (n + j))
          (fun j => lamD_ne_bot (n + j)) (fun j => lamD_le (n + j)), hT⟩
    have htgt := genByFactors_prod_iff.mp (genByFactors_orderIso e hsrc)
    exact not_genByFactors_of_two_atoms hxt hbot α β hα hβ hne htgt.2
  · push_neg at hmulti
    exact single_atom_absurd n k hnk
      (fun hnk' => hnk' ▸ card_D_lt_card_seed_B k hx hy)
      (fun α β hα hβ => hmulti α β hα hβ) e

-- [D-3151] §Copy-C-below-the-marked-point
-- [D-3152] copyC_low_forces_false_at
theorem copyC_low_forces_false_at {T : Type} [PartialOrder T] [OrderBot T]
    [IsAtomic T] (hT : GenByFactors T) (n k : ℕ) (hnk : n ≤ k) {x : EndP (D k)}
    (hx : x ≠ ⊥) (hxm : x ≠ markedPt k) (hmx : ¬ (markedPt k ≤ x))
    (hy : JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm))
    (e : (WeakProd (Fam n) × T) ≃o
      (WeakProd (Fam (k + 1)) × (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)) :
    False := by
  letI := levelSeedDualBot hy
  haveI : IsAtomic ((LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ) :=
    GluingTowerLibrary.isAtomic_of_finite
  have hbot : (OrderDual.ofDual
      (⊥ : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)).1
      = glueC (markedPt k) x hx hxm := rfl
  by_cases hmulti : ∃ α β : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ,
      IsAtom α ∧ IsAtom β ∧ α ≠ β
  · obtain ⟨α, β, hα, hβ, hne⟩ := hmulti
    haveI : IsAtomic (WeakProd (Fam n)) :=
      isAtomic_weakProd (fun j => lamD (n + j)) (fun j => lamD_ne_bot (n + j))
        (fun j => lamD_le (n + j))
    haveI : IsAtomic (WeakProd (Fam (k + 1))) :=
      isAtomic_weakProd (fun j => lamD (k + 1 + j)) (fun j => lamD_ne_bot (k + 1 + j))
        (fun j => lamD_le (k + 1 + j))
    have hsrc : GenByFactors (WeakProd (Fam n) × T) :=
      genByFactors_prod_iff.mpr
        ⟨genByFactors_weakProd (D := Fam n) (fun j => lamD (n + j))
          (fun j => lamD_ne_bot (n + j)) (fun j => lamD_le (n + j)), hT⟩
    have htgt := genByFactors_prod_iff.mp (genByFactors_orderIso e hsrc)
    exact not_genByFactors_of_two_atomsC hmx hbot α β hα hβ hne htgt.2
  · push_neg at hmulti
    exact single_atom_absurd n k hnk
      (fun hnk' => hnk' ▸ card_D_lt_card_seed_C k hx hxm hy)
      (fun α β hα hβ => hmulti α β hα hβ) e

-- [D-3153] §The-single-atom-half-is-unconditional
-- [D-3154] CopyBCMultiAtomExcludedAt
def CopyBCMultiAtomExcludedAt (n : ℕ) (z : DInfty) : Prop :=
  ∀ (k : ℕ), n ≤ k → ∀ (y : D (k + 1)) (hy : JoinIrred (D (k + 1)) y),
    (¬ ∃ F : EndP (D k), y = glueA (markedPt k) F) →
    (∃ α β : (LevelSeed (k + 1) y)ᵒᵈ,
      @IsAtom _ _ (levelSeedDualBot hy) α ∧ @IsAtom _ _ (levelSeedDualBot hy) β
      ∧ α ≠ β) →
    ¬ Nonempty (JBelow (toD (k + 1) y) ≃o JBelow z)

-- [D-3155] copyBCExcludedAt_of_multiAtom
theorem copyBCExcludedAt_of_multiAtom (n : ℕ) (z : DInfty) {T : Type}
    [PartialOrder T] [OrderBot T] [IsAtomic T]
    (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam n) × T))
    (h : CopyBCMultiAtomExcludedAt n z) : StageAssembly.CopyBCExcludedAt n z := by
  intro k hnk y hy hnotA
  letI := levelSeedDualBot hy
  haveI : IsAtomic ((LevelSeed (k + 1) y)ᵒᵈ) := GluingTowerLibrary.isAtomic_of_finite
  by_cases hmulti : ∃ α β : (LevelSeed (k + 1) y)ᵒᵈ, IsAtom α ∧ IsAtom β ∧ α ≠ β
  · exact h k hnk y hy hnotA hmulti
  · push_neg at hmulti
    rintro ⟨e0⟩
    exact single_atom_absurd n k hnk
      (fun hnk' => hnk' ▸ card_D_lt_card_seed_notA k hy hnotA)
      (fun α β hα hβ => hmulti α β hα hβ)
      (hz.symm.trans (e0.dual.symm.trans (seedShape (k + 1) y hy)))

-- [D-3156] colimit_compat_of_multiAtom
theorem colimit_compat_of_multiAtom
    (h : ∀ (k : ℕ) (x : D k), JoinIrred (D k) x →
      CopyBCMultiAtomExcludedAt k (toD k x)) :
    Subsingleton (DInfty ≃o DInfty) := by
  refine StageAssembly.colimit_compat_of (fun k x hx => ?_)
  letI : OrderBot (Base k x) := levelSeedDualBot hx
  haveI : IsAtomic (Base k x) := GluingTowerLibrary.isAtomic_of_finite
  exact copyBCExcludedAt_of_multiAtom k (toD k x) (seedShape k x hx) (h k x hx)

-- [D-3157] §What-GenByFactors-buys-stated-where-it-is-true
-- [D-3158] CopyCHighExcludedAt
def CopyCHighExcludedAt (n : ℕ) (z : DInfty) : Prop :=
  ∀ (k : ℕ), n ≤ k → ∀ (x : EndP (D k)) (hx : x ≠ ⊥) (hxm : x ≠ markedPt k),
    markedPt k ≤ x → JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm) →
    ¬ Nonempty (JBelow (toD (k + 1) (glueC (markedPt k) x hx hxm)) ≃o JBelow z)

-- [D-3159] copyBCMultiAtom_of_gen
theorem copyBCMultiAtom_of_gen (n : ℕ) (z : DInfty) {T : Type} [PartialOrder T]
    [OrderBot T] [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam n) × T))
    (hT : GenByFactors T) (hH : CopyCHighExcludedAt n z) :
    CopyBCMultiAtomExcludedAt n z := by
  intro k hnk y hy hnotA _
  rcases dSuccCases k y with ⟨v, hv⟩ | ⟨x, hx, hv⟩ | ⟨x, hx, hxm, hv⟩
  · exact absurd ⟨v, hv⟩ hnotA
  · subst hv
    rintro ⟨e0⟩
    exact copyB_forces_false_at hT n k hnk hx hy
      (hz.symm.trans (e0.dual.symm.trans
        (seedShape (k + 1) (glueB (markedPt k) x hx) hy)))
  · subst hv
    by_cases hmx : markedPt k ≤ x
    · exact hH k hnk x hx hxm hmx hy
    · rintro ⟨e0⟩
      exact copyC_low_forces_false_at hT n k hnk hx hxm hmx hy
        (hz.symm.trans (e0.dual.symm.trans
          (seedShape (k + 1) (glueC (markedPt k) x hx hxm) hy)))

-- [D-3160] §The-remaining-obligation-split-into-its-three
-- [D-3161] MultiAtomB
def MultiAtomB (n : ℕ) (z : DInfty) : Prop :=
  ∀ (k : ℕ), n ≤ k → ∀ (x : EndP (D k)) (hx : x ≠ ⊥)
    (hy : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx)),
    (∃ α β : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ,
      @IsAtom _ _ (levelSeedDualBot hy) α ∧ @IsAtom _ _ (levelSeedDualBot hy) β
      ∧ α ≠ β) →
    ¬ Nonempty (JBelow (toD (k + 1) (glueB (markedPt k) x hx)) ≃o JBelow z)

-- [D-3162] MultiAtomCLow
def MultiAtomCLow (n : ℕ) (z : DInfty) : Prop :=
  ∀ (k : ℕ), n ≤ k → ∀ (x : EndP (D k)) (hx : x ≠ ⊥) (hxm : x ≠ markedPt k),
    ¬ (markedPt k ≤ x) →
    ∀ (hy : JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm)),
    (∃ α β : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ,
      @IsAtom _ _ (levelSeedDualBot hy) α ∧ @IsAtom _ _ (levelSeedDualBot hy) β
      ∧ α ≠ β) →
    ¬ Nonempty (JBelow (toD (k + 1) (glueC (markedPt k) x hx hxm)) ≃o JBelow z)

-- [D-3163] copyBCMultiAtom_of_parts
theorem copyBCMultiAtom_of_parts (n : ℕ) (z : DInfty)
    (hB : MultiAtomB n z) (hL : MultiAtomCLow n z) (hH : CopyCHighExcludedAt n z) :
    CopyBCMultiAtomExcludedAt n z := by
  intro k hnk y hy hnotA hmulti
  rcases dSuccCases k y with ⟨v, hv⟩ | ⟨x, hx, hv⟩ | ⟨x, hx, hxm, hv⟩
  · exact absurd ⟨v, hv⟩ hnotA
  · subst hv; exact hB k hnk x hx hy hmulti
  · subst hv
    by_cases hmx : markedPt k ≤ x
    · exact hH k hnk x hx hxm hmx hy
    · exact hL k hnk x hx hxm hmx hy hmulti

-- [D-3164] multiAtomB_of_gen
theorem multiAtomB_of_gen (n : ℕ) (z : DInfty) {T : Type} [PartialOrder T]
    [OrderBot T] [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam n) × T))
    (hT : GenByFactors T) : MultiAtomB n z := by
  intro k hnk x hx hy _
  rintro ⟨e0⟩
  exact copyB_forces_false_at hT n k hnk hx hy
    (hz.symm.trans (e0.dual.symm.trans
      (seedShape (k + 1) (glueB (markedPt k) x hx) hy)))

-- [D-3165] multiAtomCLow_of_gen
theorem multiAtomCLow_of_gen (n : ℕ) (z : DInfty) {T : Type} [PartialOrder T]
    [OrderBot T] [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam n) × T))
    (hT : GenByFactors T) : MultiAtomCLow n z := by
  intro k hnk x hx hxm hmx hy _
  rintro ⟨e0⟩
  exact copyC_low_forces_false_at hT n k hnk hx hxm hmx hy
    (hz.symm.trans (e0.dual.symm.trans
      (seedShape (k + 1) (glueC (markedPt k) x hx hxm) hy)))

-- [D-3166] §Which-pieces-fail-GenByFactors-as-a-theorem
-- [D-3167] notGen_base_of_two_atoms_B
theorem notGen_base_of_two_atoms_B (m : ℕ) {x : EndP (D m)} (hx : x ≠ ⊥)
    (hji : JoinIrred (D (m + 1)) (glueB (markedPt m) x hx))
    {α β : (LevelSeed (m + 1) (glueB (markedPt m) x hx))ᵒᵈ}
    (hα : @IsAtom _ _ (levelSeedDualBot hji) α)
    (hβ : @IsAtom _ _ (levelSeedDualBot hji) β) (hne : α ≠ β) :
    ¬ @GenByFactors _ _ (levelSeedDualBot hji) := by
  letI := levelSeedDualBot hji
  exact not_genByFactors_of_two_atoms (copyB_ne_top m hx hji) rfl α β hα hβ hne

-- [D-3168] notGen_base_of_two_atoms_CLow
theorem notGen_base_of_two_atoms_CLow (m : ℕ) {x : EndP (D m)} (hx : x ≠ ⊥)
    (hxm : x ≠ markedPt m) (hmx : ¬ (markedPt m ≤ x))
    (hji : JoinIrred (D (m + 1)) (glueC (markedPt m) x hx hxm))
    {α β : (LevelSeed (m + 1) (glueC (markedPt m) x hx hxm))ᵒᵈ}
    (hα : @IsAtom _ _ (levelSeedDualBot hji) α)
    (hβ : @IsAtom _ _ (levelSeedDualBot hji) β) (hne : α ≠ β) :
    ¬ @GenByFactors _ _ (levelSeedDualBot hji) := by
  letI := levelSeedDualBot hji
  exact not_genByFactors_of_two_atomsC hmx rfl α β hα hβ hne

end CopyBCAtBase
