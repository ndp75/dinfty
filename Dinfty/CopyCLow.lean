import Dinfty.CopyBAtoms

open GluingTowerLibrary SierpinskiApplication

/-!
# Copy `C`, the half where the copy-`B` part is absent

§35 recorded copy `C` as needing a *different* argument, because a copy-`C` seed
contains all of copy `A` — including `iotaD k ⊤ > dMid (k+1)` — so `t = dMid (k+1)`
does not bound `factorPart`, and `t = iotaD k ⊤` fails too since copy-`B`
elements are in the seed as well.

**That second failure is conditional, and the condition is `m ≤ x`.**
`leGlue_tagB_tagC_iff` says `glueB m b ≤ glueC m x ↔ m ≤ x`: when `m ≰ x` the
copy-`B` part of the seed is *empty*, the seed really is the ordinal sum
`J(EndP (D k)) ⊕ (copy C below x)`, and `t = iotaD k ⊤` **is** a valid witness —
because `glueA m a ≤ glueC m c` holds unconditionally, so every copy-`A` element
is below every copy-`C` one.

So copy `C` splits on the *local `A`–`B` relation*, and this module closes the
half where that relation is vacuous.  The argument is `CopyBAtoms` with
`dMidSeed` replaced by `topSeedC = iotaD k ⊤`:

* a copy-`A` atom must be `topSeedC` (`copyA_atom_eqC`) — because
  `glueA m ⊤` is the greatest copy-`A` element of the seed, and it *is* in the
  seed, since `⊤ : EndP (D k)` is join-irreducible (`joinIrred_endP_top`, from
  `D_top_hasUniqueDownCover`);
* if `topSeedC` is an atom it is the only one (`atom_uniqueC`);
* so **≥ 2 atoms** ⟹ every atom is copy `C` ⟹ no copy-`A` element is in
  `factorPart` ⟹ `factorPart` is bounded by `topSeedC`, with `dMid (k+1)`
  strictly below it (`dMid_lt_iotaD_top`, §35) ⟹ `¬ GenByFactors`;
* **exactly 1 atom** ⟹ counting, exactly as for copy `B`: the three thresholds
  give three copy-`A` seed elements and `y` is a fourth, against
  `Fintype.card (D 0) = 3`.

`⊤` being join-irreducible in the base is not decoration: over `C₂ × C₂`, where
it fails, `glueA m ⊤` is not in the seed at all and the witness disappears.  See
`_archive/check_copyC_seed_generation.py`, which sweeps chains, products,
products-with-a-top, `EndP (D 0)`, `EndP (C₄)` and `D 1`, and finds the claim
holds exactly on the bases whose top is join-irreducible.

**What is left of copy `C` is `m ≤ x`** — there the copy-`A` and copy-`B` parts
genuinely interleave, `GenByFactors` can hold, and no witness exists.
-/

open scoped Classical

namespace CopyCLow

open TwoPointAssembly CopyAClassification CopyBCStructure SeedShapeProof
open SeedLevelStep WeakProductAbsorption AtomFactorGeneration WeakProdFactorization
open SeedSeparation MidAnchor SeedChain TwoPointHypothesis CopyBExclusion CopyBAtoms
open TowerNoAbsorption TowerCardGrowth

private theorem hmk' (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hmtk' (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
private theorem hbtk' (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

/-- **`⊤` is join-irreducible in `EndP (D k)`** — `D k`'s own top has a unique
down-cover, and `constHom` reflects join-irreducibility. -/
theorem joinIrred_endP_top (k : ℕ) : JoinIrred (EndP (D k)) (⊤ : EndP (D k)) := by
  letI := realUniqueAtomCoatom k
  rw [endP_top_eq_constHom_top, joinIrred_constHom_iff]
  exact (hasUniqueDownCover_iff_joinIrred (⊤ : D k)).mp (D_top_hasUniqueDownCover k)

/-! ## The seed of a copy-`C` point with `m ≰ x` -/

section Seed

variable {k : ℕ} {x : EndP (D k)} (hx : x ≠ ⊥) (hxm : x ≠ markedPt k)
variable (hmx : ¬ (markedPt k ≤ x))

include hmx in
/-- With `m ≰ x` there is **no copy-`B` element** below `y`. -/
theorem seedC_cases (u : D (k + 1)) (hu : u ≤ glueC (markedPt k) x hx hxm) :
    (∃ v : EndP (D k), u = glueA (markedPt k) v)
      ∨ (∃ (c : EndP (D k)) (hc : c ≠ ⊥) (hcm : c ≠ markedPt k),
          u = glueC (markedPt k) c hc hcm) := by
  rcases dSuccCases k u with ⟨v, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, hcm, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · exact absurd ((leGlue_tagB_tagC_iff (markedPt k) b x).mp hu) hmx
  · exact Or.inr ⟨c, hc, hcm, rfl⟩

/-- Copy `A` is below copy `C` unconditionally. -/
theorem copyA_le_copyC (v : EndP (D k)) {c : EndP (D k)} (hc : c ≠ ⊥)
    (hcm : c ≠ markedPt k) :
    (glueA (markedPt k) v : D (k + 1)) ≤ glueC (markedPt k) c hc hcm :=
  leGlue_tagA_tagC (markedPt k) v c

theorem glueA_ne_copyC (v : EndP (D k)) :
    (glueA (markedPt k) v : D (k + 1)) ≠ glueC (markedPt k) x hx hxm := by
  intro hcon
  have h2 : (Sum.inl v : GlueBase (EndP (D k))) = Sum.inr (Sum.inr x) :=
    congrArg Subtype.val hcon
  simp at h2

/-- The copy-`A` top, as an element of the seed: the witness that replaces
`dMidSeed`. -/
noncomputable def topSeedC : LevelSeed (k + 1) (glueC (markedPt k) x hx hxm) :=
  ⟨glueA (markedPt k) (⊤ : EndP (D k)),
   (joinIrred_glueA_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k)
     (⊤ : EndP (D k))).mpr (joinIrred_endP_top k),
   leGlue_tagA_tagC (markedPt k) (⊤ : EndP (D k)) x⟩

/-- The marked point, as an element of the seed. -/
noncomputable def midSeedC : LevelSeed (k + 1) (glueC (markedPt k) x hx hxm) :=
  ⟨dMid (k + 1), D_mid_joinIrred (k + 1), dMid_le_glueC k hx hxm⟩

theorem midSeedC_lt_topSeedC : midSeedC hx hxm < topSeedC hx hxm := by
  have h : dMid (k + 1) < glueA (markedPt k) (⊤ : EndP (D k)) := by
    have := dMid_lt_iotaD_top k
    rwa [iotaD_top_eq_glueA k] at this
  exact h

end Seed

/-! ## The atoms -/

section Atoms

variable {k : ℕ} {x : EndP (D k)} {hx : x ≠ ⊥} {hxm : x ≠ markedPt k}
variable (hmx : ¬ (markedPt k ≤ x))
variable [OrderBot ((LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)]
variable (hbot : (OrderDual.ofDual
    (⊥ : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)).1
    = glueC (markedPt k) x hx hxm)

include hbot

omit hbot in
theorem le_topSeedC (u : LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))
    {v : EndP (D k)} (hv : u.1 = glueA (markedPt k) v) : u ≤ topSeedC hx hxm := by
  show u.1 ≤ glueA (markedPt k) (⊤ : EndP (D k))
  rw [hv]
  exact (glueA_le_iff (markedPt k) (hmk' k) v (⊤ : EndP (D k))).mpr le_top

/-- **A copy-`A` atom is the copy-`A` top.** -/
theorem copyA_atom_eqC (α : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)
    (hα : IsAtom α) {v : EndP (D k)}
    (hv : (OrderDual.ofDual α).1 = glueA (markedPt k) v) :
    α = OrderDual.toDual (topSeedC hx hxm) := by
  have hle : (OrderDual.toDual (topSeedC hx hxm)) ≤ α :=
    le_topSeedC (OrderDual.ofDual α) hv
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hb : (glueA (markedPt k) (⊤ : EndP (D k)) : D (k + 1))
        = (OrderDual.ofDual
            (⊥ : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)).1 :=
      congrArg (fun w => (OrderDual.ofDual w).1) (hα.2 _ hlt)
    rw [hbot] at hb
    exact glueA_ne_copyC hx hxm (⊤ : EndP (D k)) hb
  · exact heq.symm

include hmx in
/-- If the copy-`A` top is an atom it is the only one. -/
theorem atom_uniqueC (hd : IsAtom (OrderDual.toDual (topSeedC hx hxm)))
    (β : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ) (hβ : IsAtom β) :
    β = OrderDual.toDual (topSeedC hx hxm) := by
  rcases seedC_cases hx hxm hmx (OrderDual.ofDual β).1 (OrderDual.ofDual β).2.2 with
    ⟨v, hv⟩ | ⟨c, hc, hcm, hv⟩
  · exact copyA_atom_eqC hbot β hβ hv
  · have hle : β ≤ OrderDual.toDual (topSeedC hx hxm) := by
      show (glueA (markedPt k) (⊤ : EndP (D k)) : D (k + 1)) ≤ (OrderDual.ofDual β).1
      rw [hv]
      exact copyA_le_copyC (⊤ : EndP (D k)) hc hcm
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact absurd (hd.2 _ hlt) hβ.1
    · exact heq

include hmx in
/-- With two distinct atoms, every atom is copy `C`. -/
theorem atom_copyC_of_two
    (α₁ α₂ : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)
    (h1 : IsAtom α₁) (h2 : IsAtom α₂) (hne : α₁ ≠ α₂)
    (α : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ) (hα : IsAtom α) :
    ∃ (c : EndP (D k)) (hc : c ≠ ⊥) (hcm : c ≠ markedPt k),
      (OrderDual.ofDual α).1 = glueC (markedPt k) c hc hcm := by
  rcases seedC_cases hx hxm hmx (OrderDual.ofDual α).1 (OrderDual.ofDual α).2.2 with
    ⟨v, hv⟩ | h
  · exfalso
    have hαd := copyA_atom_eqC hbot α hα hv
    have hd : IsAtom (OrderDual.toDual (topSeedC hx hxm)) := hαd ▸ hα
    exact hne ((atom_uniqueC hmx hbot hd α₁ h1).trans
      (atom_uniqueC hmx hbot hd α₂ h2).symm)
  · exact h

include hmx in
/-- **The factor part is bounded by the copy-`A` top**, once there are two
distinct atoms. -/
theorem factorPart_le_topC
    (α₁ α₂ : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)
    (h1 : IsAtom α₁) (h2 : IsAtom α₂) (hne : α₁ ≠ α₂)
    (u : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)
    (hu : u ∈ factorPart ((LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)) :
    u ≤ OrderDual.toDual (topSeedC hx hxm) := by
  rcases seedC_cases hx hxm hmx (OrderDual.ofDual u).1 (OrderDual.ofDual u).2.2 with
    ⟨v, hv⟩ | ⟨c, hc, hcm, hv⟩
  · exfalso
    obtain ⟨γ, hγ, hmem⟩ := hu
    obtain ⟨c1, hc1, hcm1, hv1⟩ := atom_copyC_of_two hmx hbot α₁ α₂ h1 h2 hne α₁ h1
    obtain ⟨c2, hc2, hcm2, hv2⟩ := atom_copyC_of_two hmx hbot α₁ α₂ h1 h2 hne α₂ h2
    have e1 : α₁ ≤ u := by
      show (OrderDual.ofDual u).1 ≤ (OrderDual.ofDual α₁).1
      rw [hv, hv1]
      exact copyA_le_copyC v hc1 hcm1
    have e2 : α₂ ≤ u := by
      show (OrderDual.ofDual u).1 ≤ (OrderDual.ofDual α₂).1
      rw [hv, hv2]
      exact copyA_le_copyC v hc2 hcm2
    exact hne ((hmem α₁ h1 e1).trans (hmem α₂ h2 e2).symm)
  · show (glueA (markedPt k) (⊤ : EndP (D k)) : D (k + 1)) ≤ (OrderDual.ofDual u).1
    rw [hv]
    exact copyA_le_copyC (⊤ : EndP (D k)) hc hcm

include hmx in
/-- **Two atoms defeat generation**, with `t = iotaD k ⊤` and `w = dMid (k+1)`. -/
theorem not_genByFactors_of_two_atomsC
    (α₁ α₂ : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ)
    (h1 : IsAtom α₁) (h2 : IsAtom α₂) (hne : α₁ ≠ α₂) :
    ¬ GenByFactors ((LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ) :=
  not_genByFactors_of_strict_upper
    (t := OrderDual.toDual (topSeedC hx hxm)) (w := OrderDual.toDual (midSeedC hx hxm))
    (factorPart_le_topC hmx hbot α₁ α₂ h1 h2 hne)
    (OrderDual.toDual_lt_toDual.mpr (midSeedC_lt_topSeedC hx hxm))

end Atoms

/-! ## Four elements, again -/

section Count

variable (k : ℕ) {x : EndP (D k)} (hx : x ≠ ⊥) (hxm : x ≠ markedPt k)

theorem four_le_card_seedC
    (hy : JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm)) :
    4 ≤ Fintype.card (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm)) := by
  have hval : ∀ a b : LevelSeed (k + 1) (glueC (markedPt k) x hx hxm),
      (a.1.1 : GlueBase (EndP (D k))) ≠ b.1.1 → a ≠ b :=
    fun a b h hcon => h (congrArg (fun w =>
      (Subtype.val (Subtype.val w) : GlueBase (EndP (D k)))) hcon)
  set e1 : LevelSeed (k + 1) (glueC (markedPt k) x hx hxm) := midSeedC hx hxm with he1
  set e2 : LevelSeed (k + 1) (glueC (markedPt k) x hx hxm) :=
    ⟨glueA (markedPt k) (gMid k),
     (joinIrred_glueA_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) (gMid k)).mpr
       (gMid_joinIrred k),
     leGlue_tagA_tagC (markedPt k) (gMid k) x⟩ with he2
  set e3 : LevelSeed (k + 1) (glueC (markedPt k) x hx hxm) :=
    ⟨glueA (markedPt k) (gLow k),
     (joinIrred_glueA_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) (gLow k)).mpr
       (gLow_joinIrred k),
     leGlue_tagA_tagC (markedPt k) (gLow k) x⟩ with he3
  set e4 : LevelSeed (k + 1) (glueC (markedPt k) x hx hxm) :=
    ⟨glueC (markedPt k) x hx hxm, hy, le_refl _⟩ with he4
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
    have h2 : (Sum.inl (markedPt k) : GlueBase (EndP (D k)))
        = Sum.inr (Sum.inr x) := hcon
    simp at h2)
  have h24 : e2 ≠ e4 := hval _ _ (by
    intro hcon
    have h2 : (Sum.inl (gMid k) : GlueBase (EndP (D k))) = Sum.inr (Sum.inr x) := hcon
    simp at h2)
  have h34 : e3 ≠ e4 := hval _ _ (by
    intro hcon
    have h2 : (Sum.inl (gLow k) : GlueBase (EndP (D k))) = Sum.inr (Sum.inr x) := hcon
    simp at h2)
  have hcard : ({e1, e2, e3, e4} :
      Finset (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_insert_of_notMem (by simp [h23, h24]),
      Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
  calc (4 : ℕ) = ({e1, e2, e3, e4} : Finset _).card := hcard.symm
    _ ≤ Fintype.card (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm)) := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ _)

end Count

/-! ## The copy-`C` exclusion, on the `m ≰ x` half -/

theorem copyC_low_forces_false {T : Type} [PartialOrder T] [OrderBot T] [IsAtomic T]
    (hT : GenByFactors T) (k : ℕ) {x : EndP (D k)} (hx : x ≠ ⊥)
    (hxm : x ≠ markedPt k) (hmx : ¬ (markedPt k ≤ x))
    (hy : JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm))
    (e : (WeakProd (Fam 0) × T) ≃o
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
    exact not_genByFactors_of_two_atomsC hmx hbot α β hα hβ hne htgt.2
  · push_neg at hmulti
    have huniq : ∀ α β : (LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ,
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
            ((LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ) βk) :=
      Fintype.card_congr iso0.toEquiv
    have hck : Fintype.card (D (0 + k))
        = Fintype.card ↥(atomFactor
            ((LevelSeed (k + 1) (glueC (markedPt k) x hx hxm))ᵒᵈ) βk) :=
      Fintype.card_congr isok.toEquiv
    have hk0 : k = 0 := by
      have hinj := card_D_strictMono.injective
        (a₁ := 0 + 0) (a₂ := 0 + k) (hc0.trans hck.symm)
      omega
    subst hk0
    have huniv : ∀ w : (LevelSeed (0 + 1) (glueC (markedPt 0) x hx hxm))ᵒᵈ,
        w ∈ atomFactor ((LevelSeed (0 + 1) (glueC (markedPt 0) x hx hxm))ᵒᵈ) βk :=
      fun w γ hγ _ => huniq γ βk hγ hβk
    have hcS : Fintype.card ↥(atomFactor
        ((LevelSeed (0 + 1) (glueC (markedPt 0) x hx hxm))ᵒᵈ) βk)
        = Fintype.card ((LevelSeed (0 + 1) (glueC (markedPt 0) x hx hxm))ᵒᵈ) :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv huniv)
    have hdual : Fintype.card ((LevelSeed (0 + 1) (glueC (markedPt 0) x hx hxm))ᵒᵈ)
        = Fintype.card (LevelSeed (0 + 1) (glueC (markedPt 0) x hx hxm)) :=
      Fintype.card_congr (OrderDual.ofDual)
    have hc0' : Fintype.card (D 0)
        = Fintype.card ↥(atomFactor
            ((LevelSeed (0 + 1) (glueC (markedPt 0) x hx hxm))ᵒᵈ) βk) := hc0
    rw [card_D_zero] at hc0'
    have h4 := four_le_card_seedC 0 hx hxm hy
    omega

theorem copyC_excluded_low (z : DInfty) {T : Type} [PartialOrder T] [OrderBot T]
    [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam 0) × T)) (hT : GenByFactors T)
    (k : ℕ) (x : EndP (D k)) (hx : x ≠ ⊥) (hxm : x ≠ markedPt k)
    (hmx : ¬ (markedPt k ≤ x))
    (hji : JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm)) :
    ¬ Nonempty (JBelow (toD (k + 1) (glueC (markedPt k) x hx hxm)) ≃o JBelow z) := by
  rintro ⟨e⟩
  exact copyC_low_forces_false hT k hx hxm hmx hji
    (hz.symm.trans (e.dual.symm.trans
      (seedShape (k + 1) (glueC (markedPt k) x hx hxm) hji)))

/-- **The remaining half of copy `C`**: the marked point below the copy-`C`
index, where the copy-`B` part of the seed is present and the copy-`A` and
copy-`B` parts interleave. -/
def CopyCHighExcludedFor (z : DInfty) : Prop :=
  ∀ (k : ℕ) (x : EndP (D k)) (hx : x ≠ ⊥) (hxm : x ≠ markedPt k),
    markedPt k ≤ x → JoinIrred (D (k + 1)) (glueC (markedPt k) x hx hxm) →
    ¬ Nonempty (JBelow (toD (k + 1) (glueC (markedPt k) x hx hxm)) ≃o JBelow z)

theorem copyC_of_high (z : DInfty) {T : Type} [PartialOrder T] [OrderBot T]
    [IsAtomic T] (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam 0) × T)) (hT : GenByFactors T)
    (hH : CopyCHighExcludedFor z) : CopyCExcludedFor z := by
  intro k x hx hxm hji
  by_cases hmx : markedPt k ≤ x
  · exact hH k x hx hxm hmx hji
  · exact copyC_excluded_low z hz hT k x hx hxm hmx hji

/-- **`TwoPointFixed`, reduced to the `m ≤ x` half of copy `C`.** -/
theorem twoPointFixed_of_CHigh (h₁ : CopyCHighExcludedFor midInf)
    (h₂ : CopyCHighExcludedFor (toD 0 (⊤ : D 0))) : TwoPointFixed :=
  twoPointFixed_of_C
    (copyC_of_high midInf (seedShape 0 (dMid 0) SeedsDiffer.joinIrred_D0_mid)
      genByFactors_base_midInf h₁)
    (copyC_of_high (toD 0 (⊤ : D 0)) (seedShape 0 (⊤ : D 0) joinIrred_D0_top)
      genByFactors_base_topJ h₂)

end CopyCLow
