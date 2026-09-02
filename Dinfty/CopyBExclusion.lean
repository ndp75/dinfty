import Dinfty.TwoPointAssembly

open GluingTowerLibrary SierpinskiApplication

/-!
# Copy `B`, part 1: the split, and the pieces the argument needs

`TwoPointAssembly` reduced `TwoPointFixed` to `CopyBCExcludedFor` at the two
points.  `CopyBCExcludedFor` splits along `glueCar_cases` into a copy-`B` and a
copy-`C` obligation (`copyBC_of_B_and_C`), and §35 showed those need different
arguments.  This module assembles what the copy-`B` argument needs.

* **`GenByFactors` holds at both left-hand pieces.**  The comparison is
  `(WeakProd (Fam 0) × T) ≃o (WeakProd (Fam (k+1)) × S_y)`, and generation is
  multiplicative, so `GenByFactors S_y` is *forced* by the isomorphism — provided
  `T` itself is generated.  For `midInf`, `T` is a one-point poset
  (`genByFactors_of_subsingleton`); for `toD 0 ⊤` it is a two-chain, which has a
  unique atom (`genByFactors_of_atom_unique`).  So refuting `GenByFactors S_y`
  refutes the isomorphism.
* **The two witnesses.**  `dMid (k+1)` is in every copy-`B` seed
  (`CopyBCStructure.dMid_le_glueB`), and so is a copy-`A` element strictly below
  it — `glueA m (stepMap (dMid k) ⊤)`, whose value is the marked point's own but
  whose threshold is `⊤`, so it sits strictly under `constHom (dMid k)`.

Those are the `t` and the `w` of
`AtomFactorGeneration.not_genByFactors_of_strict_upper`.
-/

open scoped Classical

namespace CopyBExclusion

open TwoPointAssembly CopyAClassification CopyBCStructure SeedShapeProof
open SeedLevelStep WeakProductAbsorption AtomFactorGeneration
open SeedSeparation MidAnchor SeedChain TwoPointHypothesis

private theorem hmk' (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hmtk' (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
private theorem hbtk' (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

noncomputable local instance obMid : OrderBot (Base 0 (dMid 0)) :=
  TwoPointAssembly.levelSeedDualBot SeedsDiffer.joinIrred_D0_mid
noncomputable local instance obTop : OrderBot (Base 0 (⊤ : D 0)) :=
  TwoPointAssembly.levelSeedDualBot joinIrred_D0_top

/-! ## The case split, restated at the tower

`glueCar_cases` cannot be used here: it carries `[Fintype P]`, and
`Fintype (EndP (D k))` is not globally synthesizable — the library instance
(`GluingTowerLibrary.lean:485`) asks for `[DecidableRel ((· ≤ ·))]`, a field
`TowerLevel` does not have.  Supplying it classically then makes the resulting
`DecidableEq` differ from the one `towerLevelSucc` bakes in, and `canon`'s
branches are guarded by that instance.

The way round is not to add instances but to **avoid needing them**: the case
split is about `canon`-fixedness alone, so restating it at `D (k+1)` and proving
it from `canon` directly needs no `Fintype` at all. -/

/-- `canon_inr_inl_ne_bot` with `m`, `w` **implicit** and no `[Fintype P]`.

Both changes matter.  Dropping `Fintype` is needed because
`Fintype (EndP (D k))` is not globally synthesizable; making `m` and `w`
implicit is needed because the tower carries **two** `DecidableEq (EndP (D k))`
instances (`endPDecidableEq`, baked into `D (k+1)` by `towerLevelSucc`, and
Mathlib's `OrderHom.instDecidableEqOfForall`, which is what synthesis finds).
With the arguments implicit, unification reads the instances off the hypothesis
instead of re-synthesizing them, and the mismatch never arises. -/
theorem canonBFix {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P]
    {m w : P} (h : canon m (Sum.inr (Sum.inl w)) = Sum.inr (Sum.inl w)) : w ≠ ⊥ := by
  intro hw
  subst hw
  simp only [canon] at h
  split_ifs at h <;> simp at h

theorem canonCFixBot {P : Type u} [DecidableEq P] [Lattice P] [BoundedOrder P]
    {m w : P} (h : canon m (Sum.inr (Sum.inr w)) = Sum.inr (Sum.inr w)) : w ≠ ⊥ := by
  intro hw
  subst hw
  simp only [canon] at h
  split_ifs at h <;> simp at h

/-- **The case split, at the tower.** -/
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

/-! ## Splitting the obligation -/

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

/-! ## Generation at the two left-hand pieces -/

theorem genByFactors_of_subsingleton {L : Type} [PartialOrder L] [OrderBot L]
    [Subsingleton L] : GenByFactors L := by
  intro w
  refine ⟨fun u hu => hu.2, ?_⟩
  intro v _
  exact le_of_eq (Subsingleton.elim w v)

theorem genByFactors_of_atom_unique {L : Type} [PartialOrder L] [OrderBot L] {α : L}
    (hα : IsAtom α) (huniq : ∀ β : L, IsAtom β → β = α) : GenByFactors L := by
  have hfp : ∀ w : L, w ∈ factorPart L := fun _ => ⟨α, hα, fun β hβ _ => huniq β hβ⟩
  intro w
  refine ⟨fun u hu => hu.2, ?_⟩
  intro v hv
  exact hv ⟨hfp w, le_refl w⟩

/-- `midInf`'s left-hand piece is a single point. -/
theorem genByFactors_base_midInf : GenByFactors (Base 0 (dMid 0)) :=
  genByFactors_of_subsingleton

/-! ### `topJ`'s left-hand piece is a two-chain, so it has a unique atom -/

/-- The unique atom of `topJ`'s left-hand piece. -/
noncomputable def topAtom : Base 0 (⊤ : D 0) := OrderDual.toDual SeedsDiffer.topSeedOne

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

theorem atom_base_top_unique (β : Base 0 (⊤ : D 0)) (hβ : IsAtom β) : β = topAtom := by
  rcases SeedsDiffer.mem_levelSeedZeroTop (OrderDual.ofDual β) with h | h
  · exact Subtype.ext h
  · exact absurd (Subtype.ext h : β = (⊥ : Base 0 (⊤ : D 0))) hβ.1

theorem genByFactors_base_topJ : GenByFactors (Base 0 (⊤ : D 0)) :=
  genByFactors_of_atom_unique isAtom_topAtom atom_base_top_unique

/-! ## The two witnesses inside a copy-`B` seed -/

section Witnesses

variable (k : ℕ) {x : EndP (D k)} (hx : x ≠ ⊥)

/-- The marked point of level `k+1`, as an element of the copy-`B` seed. -/
noncomputable def dMidSeed : LevelSeed (k + 1) (glueB (markedPt k) x hx) :=
  ⟨dMid (k + 1), D_mid_joinIrred (k + 1), dMid_le_glueB k hx⟩

/-- A join-irreducible of `EndP (D k)` strictly below the marked point: the same
value, but thresholded at `⊤`. -/
noncomputable def gLow : EndP (D k) := stepMap (dMid k) (⊤ : D k)

theorem gLow_joinIrred : JoinIrred (EndP (D k)) (gLow k) :=
  (jiEquiv ((⊤ : D k), (⟨dMid k, D_mid_joinIrred k⟩ : {v : D k // JoinIrred (D k) v}))).2

theorem gLow_le : gLow k ≤ markedPt k := by
  intro y
  show stepMap (dMid k) (⊤ : D k) y ≤ (constHom (dMid k) : EndP (D k)) y
  by_cases h : (⊤ : D k) ≤ y
  · rw [stepMap_apply_of_ge (dMid k) (⊤ : D k) h]
    exact le_refl _
  · rw [stepMap_apply_of_not_ge (dMid k) (⊤ : D k) h]
    exact bot_le

theorem gLow_ne : gLow k ≠ markedPt k := by
  intro hcon
  have hbt : (⊥ : D k) ≠ (⊤ : D k) := by
    letI := (towerLevel k).nontriv
    exact bot_ne_top_of_nontrivial (P := D k)
  have h1 : gLow k (⊥ : D k) = (⊥ : D k) :=
    stepMap_apply_of_not_ge (dMid k) (⊤ : D k) (fun h => hbt (le_antisymm bot_le h))
  rw [hcon] at h1
  exact dMid_ne_bot k h1

theorem gLow_lt : gLow k < markedPt k := lt_of_le_of_ne (gLow_le k) (gLow_ne k)

/-- The copy-`A` witness strictly below the marked point, inside the seed. -/
noncomputable def wSeed : LevelSeed (k + 1) (glueB (markedPt k) x hx) :=
  ⟨glueA (markedPt k) (gLow k),
   (joinIrred_glueA_iff (markedPt k) (hmk' k) (hmtk' k) (hbtk' k) (gLow k)).mpr
     (gLow_joinIrred k),
   leGlue_tagA_tagB_of_le (markedPt k) (gLow k) x (gLow_le k)⟩

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

/-! ## What copy `B` needs — now supplied in `Dinfty/CopyBAtoms.lean`

The argument, for the record.  Let `y = glueB m x hx` be join-irreducible and
`S_y = (LevelSeed (k+1) y)ᵒᵈ`.  An isomorphism with `z`'s seed forces
`GenByFactors S_y` (the left-hand pieces are generated — above — and generation
is multiplicative).  Then:

* **`S_y` has ≥ 2 atoms.**  `not_genByFactors_of_strict_upper` applies with
  `t = dMidSeed`, `w = wSeed` (both built below, `wSeed_lt_dMidSeed`), because
  every element of `factorPart S_y` is `≥ dMid (k+1)`: copy-`B` elements are
  (`dMid_le_glueB`), copy-`C` elements are not in the seed at all
  (`not_leGlue_tagC_tagB`), and a copy-`A` element `glueA m v` with `v ≤ m` lies
  below **every** copy-`B` atom, so being in some `atomFactor α` would force the
  atoms to coincide.  That all atoms *are* copy-`B` follows from: a copy-`A`
  atom must be `dMidSeed` (anything smaller is under it and so not covered by
  `y`), and if `dMidSeed` were an atom it would be the only one.
* **`S_y` has exactly 1 atom** (this happens — take `x = atomOf (EndP (D k))`).
  Then `factorPart S_y = S_y`, so there is exactly **one** atom-factor.
  `factor_in_finite_pieceL` demands one for each `j ≤ k`, all of them that same
  set, so `D 0 ≃o D k` and `k = 0`; and then `D 0 ≃o S_y`, against
  `4 ≤ card S_y` (the three thresholds `⊥ < dMid 0 < ⊤` give three copy-`A`
  elements, and `y` is the fourth).

Both cases need `x ≠ ⊤`, which the seam section below supplies.

`CopyBAtoms.copyB_excluded_gen` is the result; `CopyBAtoms.twoPointFixed_of_C`
reduces `TwoPointFixed` to copy `C` alone. -/

/-! ## The seam is not join-irreducible

Copy `B`'s argument needs `x ≠ ⊤`: at `x = ⊤` the point is the seam
`tag_B ⊤ = tag_C m`, whose seed contains **all** of copy `A`, so it behaves like
copy `C` and the bound `t = dMid (k+1)` fails.

`not_hasUniqueDownCover_glueB_top` says exactly this but carries `[Fintype P]`
and `3 ≤ Fintype.card P`, unusable at `P = EndP (D k)`.  Proved from the
definition instead: `glueA m ⊤` and `glueB m m` are both strictly below the seam
and their join **is** the seam, because every upper bound of the pair is above
it.

Every step is ascribed at `D (k+1)`.  Without that the elaborator drops to the
bare `GlueCar (markedPt k)`, where neither `Max` nor `PartialOrder` is found —
the same instance diamond as `canonBFix`. -/

section Seam

variable (k : ℕ)

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

/-- A join-irreducible copy-`B` point is not the seam. -/
theorem copyB_ne_top {x : EndP (D k)} (hx : x ≠ ⊥)
    (hji : JoinIrred (D (k + 1)) (glueB (markedPt k) x hx)) : x ≠ (⊤ : EndP (D k)) := by
  intro hcon
  subst hcon
  exact seam_not_joinIrred k hji

end Seam

end CopyBExclusion
