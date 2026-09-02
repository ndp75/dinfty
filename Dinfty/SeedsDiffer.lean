import Dinfty.SeedShapeProof
import Dinfty.TowerNoAbsorption

open GluingTowerLibrary SierpinskiApplication

/-!
# The two seeds are not isomorphic — inside `DInfty`

`SeedShapeProof.seedShape` supplies the identification the whole argument was
waiting on.  This module cashes it in at the two points pillar B's base case is
about:

```lean
jBelow_midInf_not_iso_topJ : IsEmpty (JBelow midInf ≃o JBelow (toD 0 ⊤))
```

The seeds of `midInf` and of `toD 0 ⊤` are **not** order-isomorphic.  That is a
statement about `DInfty` itself, not about restricted products, and it is the
first consequence of the shape that could not be stated before.

## How the two differ

Both dualise to `WeakProd (fun j => D (0 + j)) × S`, and the shape says exactly
what `S` is: the dual of the level-`0` seed.

* for `midInf = toD 0 (dMid 0)`: `{u : Fin 3 // JoinIrred u ∧ u ≤ 1}` is the
  **one-point** poset (`levelSeedZeroMid_unique`) — `u ≠ ⊥` forces `u = 1`;
* for `toD 0 ⊤`: `{u : Fin 3 // JoinIrred u ∧ u ≤ 2}` is `{1, 2}`, a **two-chain**
  (`levelSeedZeroTop_iso`).

So an isomorphism of the two seeds would give `WeakProd F ≃o WeakProd F × C₂`,
and `WeakProductAbsorption.weakProd_no_absorb_two` says there is none: a
two-element factor is visible from the atom alone, and every `D j` has more than
two elements.

## Scope

This closes the *two-point* case of seed separation.  It is **not**
`TwoPointFixed`, which additionally needs that no **other** element of any stage
shares `midInf`'s seed — the copy-`A`/`B`/`C` classification, whose engine is in
`AtomFactorGeneration` and `WeakProdFactorization` but whose instantiation needs
the level-`N` seeds classified.
-/

open scoped Classical

namespace SeedsDiffer

open SeedShapeProof SeedChain SeedLevelStep SeedSeparation MidAnchor
open WeakProductAbsorption TowerNoAbsorption
open TwoPointHypothesis

/-! ## Dropping a trivial factor -/

private theorem prodEq' {A B : Type*} {p q : A × B} (h1 : p.1 = q.1) (h2 : p.2 = q.2) :
    p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- A one-point second factor can be dropped. -/
def prodUniqueIso {A B : Type*} [PartialOrder A] [PartialOrder B] [Subsingleton B]
    [Inhabited B] : (A × B) ≃o A where
  toFun p := p.1
  invFun a := (a, default)
  left_inv p := prodEq' rfl (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      exact ⟨h, le_of_eq (Subsingleton.elim _ _)⟩
    · intro h
      exact h.1

/-! ## The two level-`0` seeds

`D 0` is `Fin 3`, but `open scoped Classical` freezes `Classical.propDecidable`
into its `≤`, so `decide` cannot be used here (see the `DecidabilityBoundary`
note).  Everything below goes through `Fin.val` and `omega` instead. -/

theorem joinIrred_D0_mid : JoinIrred (D 0) (dMid 0) := D_mid_joinIrred 0

theorem val_bot : ((⊥ : D 0) : Fin 3).val = 0 := rfl
theorem val_mid : ((dMid 0 : D 0) : Fin 3).val = 1 := rfl
theorem val_top : ((⊤ : D 0) : Fin 3).val = 2 := rfl

theorem ne_bot_val {t : D 0} (h : t ≠ (⊥ : D 0)) : (t : Fin 3).val ≠ 0 := by
  intro hv
  exact h (Fin.ext hv)

/-- `midInf`'s level-`0` seed is a single point: `u ≠ ⊥` and `u ≤ dMid 0` force
`u = dMid 0`. -/
instance levelSeedZeroMid_subsingleton : Subsingleton (LevelSeed 0 (dMid 0)) := by
  have key : ∀ u : LevelSeed 0 (dMid 0), u.1 = dMid 0 := by
    intro u
    have h1 := ne_bot_val u.2.1.1
    have h2 : (u.1 : Fin 3).val ≤ 1 := Fin.le_def.mp u.2.2
    refine Fin.ext ?_
    rw [val_mid]
    omega
  exact ⟨fun a b => Subtype.ext ((key a).trans (key b).symm)⟩

noncomputable instance levelSeedZeroMid_inhabited : Inhabited (LevelSeed 0 (dMid 0)) :=
  ⟨⟨dMid 0, joinIrred_D0_mid, le_refl _⟩⟩

noncomputable instance : Subsingleton (Base 0 (dMid 0)) := levelSeedZeroMid_subsingleton
noncomputable instance : Inhabited (Base 0 (dMid 0)) := levelSeedZeroMid_inhabited

/-! ## The level-`0` seed of the top is a two-chain -/

theorem mem_levelSeedZeroTop (u : LevelSeed 0 (⊤ : D 0)) :
    u.1 = dMid 0 ∨ u.1 = (⊤ : D 0) := by
  have h1 : (u.1 : Fin 3).val ≠ 0 := ne_bot_val u.2.1.1
  have h2 : (u.1 : Fin 3).val < 3 := (u.1 : Fin 3).isLt
  have key : (u.1 : Fin 3).val = 1 ∨ (u.1 : Fin 3).val = 2 := by omega
  rcases key with h | h
  · refine Or.inl (Fin.ext ?_)
    rw [val_mid]
    exact h
  · refine Or.inr (Fin.ext ?_)
    rw [val_top]
    exact h

noncomputable def topSeedOne : LevelSeed 0 (⊤ : D 0) :=
  ⟨dMid 0, joinIrred_D0_mid, le_top⟩

noncomputable def topSeedTwo : LevelSeed 0 (⊤ : D 0) :=
  ⟨(⊤ : D 0), joinIrred_D0_top, le_refl _⟩

theorem topSeed_ne : topSeedTwo ≠ topSeedOne := by
  intro h
  exact dMid_ne_top 0 (congrArg Subtype.val h).symm

theorem fin2_one_ne_zero : (1 : Fin 2) ≠ 0 := fun h => Nat.one_ne_zero (congrArg Fin.val h)

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have h := i.isLt
  rcases (by omega : i.val = 0 ∨ i.val = 1) with hv | hv
  · exact Or.inl (Fin.ext hv)
  · exact Or.inr (Fin.ext hv)

/-- `Fin 2` into the dualised level-`0` seed of the top: `0 ↦ ⊤`, `1 ↦ dMid 0`
(the dual reverses, so `⊤` is the bottom). -/
noncomputable def finTwoToBase (i : Fin 2) : Base 0 (⊤ : D 0) :=
  if i = 0 then topSeedTwo else topSeedOne

theorem finTwoToBase_zero : finTwoToBase 0 = topSeedTwo := if_pos rfl

theorem finTwoToBase_one : finTwoToBase 1 = topSeedOne := if_neg fin2_one_ne_zero

theorem finTwoToBase_bijective : Function.Bijective finTwoToBase := by
  constructor
  · intro i j h
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl
    · rfl
    · rw [finTwoToBase_zero, finTwoToBase_one] at h
      exact absurd h topSeed_ne
    · rw [finTwoToBase_zero, finTwoToBase_one] at h
      exact absurd h.symm topSeed_ne
    · rfl
  · intro u
    rcases mem_levelSeedZeroTop u with h | h
    · exact ⟨1, by rw [finTwoToBase_one]; exact Subtype.ext h.symm⟩
    · exact ⟨0, by rw [finTwoToBase_zero]; exact Subtype.ext h.symm⟩

theorem finTwoToBase_le_iff (i j : Fin 2) :
    finTwoToBase i ≤ finTwoToBase j ↔ i ≤ j := by
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl
  · exact ⟨fun _ => le_refl _, fun _ => le_refl _⟩
  · rw [finTwoToBase_zero, finTwoToBase_one]
    refine ⟨fun _ => Fin.le_def.mpr (by omega), fun _ => ?_⟩
    exact (le_top : (dMid 0 : D 0) ≤ (⊤ : D 0))
  · rw [finTwoToBase_zero, finTwoToBase_one]
    constructor
    · intro h
      exfalso
      have h' : (⊤ : D 0) ≤ dMid 0 := h
      exact dMid_ne_top 0 (le_antisymm le_top h')
    · intro h
      exact absurd (Fin.le_def.mp h) (by omega)
  · exact ⟨fun _ => le_refl _, fun _ => le_refl _⟩

noncomputable def finTwoToBaseIso : Fin 2 ≃o Base 0 (⊤ : D 0) where
  toEquiv := Equiv.ofBijective finTwoToBase finTwoToBase_bijective
  map_rel_iff' := fun {i j} => finTwoToBase_le_iff i j

/-- **The level-`0` seed of the top, dualised, is `Fin 2`.** -/
noncomputable def baseTopIso : Base 0 (⊤ : D 0) ≃o Fin 2 := finTwoToBaseIso.symm

/-! ## The two seeds are not isomorphic -/

/-- **The seeds of `midInf` and of `toD 0 ⊤` are not order-isomorphic.** -/
theorem jBelow_midInf_not_iso_topJ :
    IsEmpty (JBelow midInf ≃o JBelow (toD 0 (⊤ : D 0))) := by
  refine ⟨fun e => ?_⟩
  have hmid : (JBelow (toD 0 (dMid 0)))ᵒᵈ ≃o (WeakProd (Fam 0) × Base 0 (dMid 0)) :=
    seedShape 0 (dMid 0) joinIrred_D0_mid
  have htop : (JBelow (toD 0 (⊤ : D 0)))ᵒᵈ ≃o (WeakProd (Fam 0) × Base 0 (⊤ : D 0)) :=
    seedShape 0 (⊤ : D 0) joinIrred_D0_top
  have edual : (JBelow (toD 0 (dMid 0)))ᵒᵈ ≃o (JBelow (toD 0 (⊤ : D 0)))ᵒᵈ := e.dual
  have hcomp : WeakProd (Fam 0) ≃o (WeakProd (Fam 0) × Fin 2) :=
    ((prodUniqueIso (A := WeakProd (Fam 0)) (B := Base 0 (dMid 0))).symm.trans
      (hmid.symm.trans (edual.trans htop))).trans
      (JSeedRecursion.prodCongrIso (OrderIso.refl _) baseTopIso)
  exact (weakProd_no_absorb_two (D := Fam 0) (fun j => lamD (0 + j))
    (fun j => lamD_ne_bot (0 + j)) (fun j => lamD_le (0 + j))
    (fun j => (⊤ : D (0 + j))) (fun j => top_ne_bot_D (0 + j))
    (fun j => lamD_ne_top (0 + j))).elim hcomp

end SeedsDiffer
