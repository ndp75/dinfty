import Dinfty.SeedCardBound
import Dinfty.StageAssembly

open GluingTowerLibrary SierpinskiApplication

/-!
# Copy `B` and copy-`C`-low, from an arbitrary base stage

With `SeedCardBound.card_D_lt_card_seed` replacing the `4 ≤ card S` count, every
step of the copy-`B` and copy-`C`-low closures becomes base-independent:

* the **multi-atom** branch is `not_genByFactors_of_two_atoms(C)`, which never
  mentioned the base;
* the **single-atom** branch ran `factor_in_finite_pieceL` at `j = 0` and
  `j = k`, concluded `k = 0`, and contradicted `card (D 0) = 3` against
  `4 ≤ card S`.  From base `n` it runs at `j = 0` and `j = k - n`, concludes
  `n = k`, and contradicts `card (D n) = card S` against
  `card (D n) < card (LevelSeed (n+1) y)`.

So `copyB_forces_false_at` and `copyC_low_forces_false_at` hold at every base,
and `copyBCExcludedAt_of_high` reduces `StageAssembly.CopyBCExcludedAt n z` to
copy-`C`-high alone — exactly what `CopyCLow.twoPointFixed_of_CHigh` did at
stage `0`.

## Where the hypothesis actually goes

The **single-atom** half needs nothing about the left-hand piece:
`single_atom_absurd` uses only `factor_in_finite_pieceL`, uniqueness of the atom,
and `card_D_lt_card_seed`.  So it is a theorem at every base and every point, and

```lean
colimit_compat_of_multiAtom :
  (∀ k x, JoinIrred x → CopyBCMultiAtomExcludedAt k (toD k x))
    → Subsingleton (DInfty ≃o DInfty)
```

carries **no side condition**.  `CopyBCMultiAtomExcludedAt` asks only about
competitors whose seed has two distinct atoms.

`GenByFactors T` is what the **multi-atom** half needs, and it is *not* free once
`T` ranges over `Base n x`: it holds at both stage-`0` pieces and at **14 of the
16** stage-`1` pieces, failing at `Base 1 (tag_B 5)` and `Base 1 (tag_C 5)`
(`_archive/check_genByFactors_level1_pieces.py`).  So it appears only in
`copyBCMultiAtom_of_gen`, as an implication *at a point* — never quantified over
all points, which would be false.

-/

open scoped Classical

namespace CopyBCAtBase

open TwoPointAssembly CopyAClassification CopyBCStructure SeedShapeProof
open SeedLevelStep WeakProductAbsorption AtomFactorGeneration WeakProdFactorization
open SeedSeparation MidAnchor SeedChain TwoPointHypothesis CopyBExclusion
open CopyBAtoms CopyCLow TowerNoAbsorption TowerCardGrowth
open SeedCardBound StageAssembly

/-! ## The single-atom contradiction, at an arbitrary base -/

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

/-! ## Copy `B` -/

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

/-! ## Copy `C`, below the marked point -/

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

/-! ## The single-atom half is unconditional

`single_atom_absurd` uses only `factor_in_finite_pieceL`, uniqueness of the atom
and `card_D_lt_card_seed` — **nothing about the left-hand piece**.  So the
competitors whose seed has one atom are excluded at every base and every point,
with no hypothesis at all.  What remains is the multi-atom half. -/

/-- The remaining obligation: competitors whose seed has **two distinct
atoms**. -/
def CopyBCMultiAtomExcludedAt (n : ℕ) (z : DInfty) : Prop :=
  ∀ (k : ℕ), n ≤ k → ∀ (y : D (k + 1)) (hy : JoinIrred (D (k + 1)) y),
    (¬ ∃ F : EndP (D k), y = glueA (markedPt k) F) →
    (∃ α β : (LevelSeed (k + 1) y)ᵒᵈ,
      @IsAtom _ _ (levelSeedDualBot hy) α ∧ @IsAtom _ _ (levelSeedDualBot hy) β
      ∧ α ≠ β) →
    ¬ Nonempty (JBelow (toD (k + 1) y) ≃o JBelow z)

/-- **The reduction, with no side condition on the piece.** -/
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

/-- **`colimit_compat` from the multi-atom obligation alone.**  This is the
honest form: no hypothesis on the left-hand pieces, because the single-atom half
is now a theorem. -/
theorem colimit_compat_of_multiAtom
    (h : ∀ (k : ℕ) (x : D k), JoinIrred (D k) x →
      CopyBCMultiAtomExcludedAt k (toD k x)) :
    Subsingleton (DInfty ≃o DInfty) := by
  refine StageAssembly.colimit_compat_of (fun k x hx => ?_)
  letI : OrderBot (Base k x) := levelSeedDualBot hx
  haveI : IsAtomic (Base k x) := GluingTowerLibrary.isAtomic_of_finite
  exact copyBCExcludedAt_of_multiAtom k (toD k x) (seedShape k x hx) (h k x hx)

/-! ## What `GenByFactors` buys, stated where it is true -/

/-- The copy-`C`-high obligation at base stage `n`. -/
def CopyCHighExcludedAt (n : ℕ) (z : DInfty) : Prop :=
  ∀ (k : ℕ), n ≤ k → ∀ (x : EndP (D k)) (hx : x ≠ ⊥) (hxm : x ≠ markedPt k),
    markedPt k ≤ x → JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm) →
    ¬ Nonempty (JBelow (toD (k + 1) (glueC (markedPt k) x hx hxm)) ≃o JBelow z)

/-- **Generation of the piece discharges the multi-atom obligation for copy `B`
and copy-`C`-low**, leaving copy-`C`-high.

`GenByFactors T` is *not* free — it fails at `Base 1 (tag_B 5)` and
`Base 1 (tag_C 5)`, 2 of the 16 stage-`1` pieces — so this is stated as an
implication at a point, not quantified over all points. -/
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

/-! ## The remaining obligation, split into its three cases

`copyBCMultiAtom_of_gen` bundles copy `B`, copy-`C`-low and copy-`C`-high behind
one `GenByFactors` hypothesis.  They are independent, and only the first two use
it, so here they are separately. -/

/-- Copy-`B` competitors with two distinct atoms. -/
def MultiAtomB (n : ℕ) (z : DInfty) : Prop :=
  ∀ (k : ℕ), n ≤ k → ∀ (x : EndP (D k)) (hx : x ≠ ⊥)
    (hy : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx)),
    (∃ α β : (LevelSeed (k + 1) (glueB (markedPt k) x hx))ᵒᵈ,
      @IsAtom _ _ (levelSeedDualBot hy) α ∧ @IsAtom _ _ (levelSeedDualBot hy) β
      ∧ α ≠ β) →
    ¬ Nonempty (JBelow (toD (k + 1) (glueB (markedPt k) x hx)) ≃o JBelow z)

/-- Copy-`C` competitors below the marked point, with two distinct atoms. -/
def MultiAtomCLow (n : ℕ) (z : DInfty) : Prop :=
  ∀ (k : ℕ), n ≤ k → ∀ (x : EndP (D k)) (hx : x ≠ ⊥) (hxm : x ≠ markedPt k),
    ¬ (markedPt k ≤ x) →
    ∀ (hy : JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm)),
    (∃ α β : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ,
      @IsAtom _ _ (levelSeedDualBot hy) α ∧ @IsAtom _ _ (levelSeedDualBot hy) β
      ∧ α ≠ β) →
    ¬ Nonempty (JBelow (toD (k + 1) (glueC (markedPt k) x hx hxm)) ≃o JBelow z)

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

theorem multiAtomB_of_gen (n : ℕ) (z : DInfty) {T : Type} [PartialOrder T]
    [OrderBot T] [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam n) × T))
    (hT : GenByFactors T) : MultiAtomB n z := by
  intro k hnk x hx hy _
  rintro ⟨e0⟩
  exact copyB_forces_false_at hT n k hnk hx hy
    (hz.symm.trans (e0.dual.symm.trans
      (seedShape (k + 1) (glueB (markedPt k) x hx) hy)))

theorem multiAtomCLow_of_gen (n : ℕ) (z : DInfty) {T : Type} [PartialOrder T]
    [OrderBot T] [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam n) × T))
    (hT : GenByFactors T) : MultiAtomCLow n z := by
  intro k hnk x hx hxm hmx hy _
  rintro ⟨e0⟩
  exact copyC_low_forces_false_at hT n k hnk hx hxm hmx hy
    (hz.symm.trans (e0.dual.symm.trans
      (seedShape (k + 1) (glueC (markedPt k) x hx hxm) hy)))

/-! ## Which pieces fail `GenByFactors`, as a theorem

The computation says generation fails at exactly two of the sixteen stage-`1`
pieces.  It is not an accident of that level: the same lemmas that exclude a
multi-atom competitor say, one level down, that a multi-atom copy-`B` or
copy-`C`-low *point* has an ungenerated piece.  So the exceptional set is
characterised, not merely enumerated. -/

theorem notGen_base_of_two_atoms_B (m : ℕ) {x : EndP (D m)} (hx : x ≠ ⊥)
    (hji : JoinIrred (D (m + 1)) (glueB (markedPt m) x hx))
    {α β : (LevelSeed (m + 1) (glueB (markedPt m) x hx))ᵒᵈ}
    (hα : @IsAtom _ _ (levelSeedDualBot hji) α)
    (hβ : @IsAtom _ _ (levelSeedDualBot hji) β) (hne : α ≠ β) :
    ¬ @GenByFactors _ _ (levelSeedDualBot hji) := by
  letI := levelSeedDualBot hji
  exact not_genByFactors_of_two_atoms (copyB_ne_top m hx hji) rfl α β hα hβ hne

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
