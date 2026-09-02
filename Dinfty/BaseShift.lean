import Dinfty.FinishLine
import Dinfty.JoinIrredLevelStable
import Dinfty.SeedCardBound
import Dinfty.TwoPointAssembly
import Dinfty.TowerNoAbsorption

open GluingTowerLibrary SierpinskiApplication

/-!
# Paying the bookkeeping debt: shifting the base

§66 argued that a comparison at `(base n, level k+1)` is a first-slice instance at
base `k`, and §68 recorded the wiring as the one gap between `FirstSlice` and
`colimit_compat`.  This file closes the first half of it.

The shift needs **no index arithmetic**.  Both sides are `seedShape` of the *same*
`DInfty` point:

```
WeakProd (Fam n) × Base n x  ≅  (JBelow (toD n x))ᵒᵈ
                             =  (JBelow (toD (n+1) (iotaD n x)))ᵒᵈ   -- toD_iotaD
                             ≅  WeakProd (Fam (n+1)) × Base (n+1) (iotaD n x)
```

so one `rw [← toD_iotaD]` between two applications of `seedShape` does it.  That
is much cheaper than reindexing `WeakProd` along `n + (j+1) = (n+1) + j`, which is
not definitional.
-/

open scoped Classical

universe u

namespace BaseShift

open SeedLevelStep JSeedRecursion WeakProductAbsorption AtomFactorGeneration
open WeakProdFactorization SeedShapeProof SeedSeparation JoinIrredLevelStable

/-- Push a point up the tower by `m` levels. -/
noncomputable def push (n : ℕ) : (m : ℕ) → D n → D (n + m)
  | 0, x => x
  | (m + 1), x => iotaD (n + m) (push n m x)

theorem joinIrred_push (n m : ℕ) {x : D n} (hx : JoinIrred (D n) x) :
    JoinIrred (D (n + m)) (push n m x) := by
  induction m with
  | zero => exact hx
  | succ m ih => exact (joinIrred_iotaD_iff (n + m) (push n m x)).mpr ih

/-- **One base shift, free from `seedShape`.** -/
noncomputable def shiftStep (n : ℕ) (x : D n) (hx : JoinIrred (D n) x) :
    (WeakProd (Fam n) × Base n x)
      ≃o (WeakProd (Fam (n + 1)) × Base (n + 1) (iotaD n x)) := by
  refine (seedShape n x hx).symm.trans ?_
  rw [← toD_iotaD n x]
  exact seedShape (n + 1) (iotaD n x) ((joinIrred_iotaD_iff n x).mpr hx)

/-- **The base shifts all the way up.**  A comparison stated at base `n` is the
same comparison stated at base `n + m`, for the point pushed up. -/
noncomputable def shiftMany (n : ℕ) (x : D n) (hx : JoinIrred (D n) x) :
    (m : ℕ) → ((WeakProd (Fam n) × Base n x)
      ≃o (WeakProd (Fam (n + m)) × Base (n + m) (push n m x)))
  | 0 => OrderIso.refl _
  | (m + 1) =>
      (shiftMany n x hx m).trans
        (shiftStep (n + m) (push n m x) (joinIrred_push n m hx))

/-! ## The other half: only the bottom factor survives

At base `k` against level `k + 1`, the truncation threshold `N = card S` admits
exactly one left-hand axis: `card (D k) < card S` (`card_D_lt_card_seed_notA`) and
`card S < card (D (k+1))` (`card_levelSeed_lt`).  So `weakBelow` collapses to a
single factor, and no product-over-a-finset bookkeeping is needed. -/

section Singleton

variable {E : ℕ → Type u} [∀ j, PartialOrder (E j)] [∀ j, OrderBot (E j)]

open Truncation

/-- **One surviving axis.**  If every factor above the bottom exceeds the
threshold and the bottom one does not, `weakBelow` is that bottom factor. -/
def weakBelowSingletonIso (N : ℕ) (h0 : Nat.card (E 0) ≤ N)
    (h1 : ∀ i, N < Nat.card (E (i + 1))) :
    ↥(weakBelow E N) ≃o E 0 where
  toFun w := w.1.1 0
  invFun d := ⟨single 0 d, by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0; exact h0
    · exact absurd (single_apply_ne (D := E) hj0 d) hj⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    match j with
    | 0 => exact single_apply_self 0 _
    | (i + 1) =>
        have hbot : w.1.1 (i + 1) = ⊥ := by
          by_contra hne
          exact absurd (w.2 (i + 1) hne) (not_le.mpr (h1 i))
        rw [hbot, single_apply_ne (D := E) (by omega)]
  right_inv d := single_apply_self 0 d
  map_rel_iff' {w w'} := by
    constructor
    · intro h j
      match j with
      | 0 => exact h
      | (i + 1) =>
          have hbot : w.1.1 (i + 1) = ⊥ := by
            by_contra hne
            exact absurd (w.2 (i + 1) hne) (not_le.mpr (h1 i))
          rw [hbot]
          exact bot_le
    · intro h
      exact h 0

end Singleton

/-! ## The assembly: `FirstSlice` closes every comparison

Shift the base up to `k`, truncate at `N = card S` — where exactly one left axis
survives — and read off a `FirstSlice k` instance.  This is the wiring §68 listed
as the remaining bookkeeping gap. -/

section Assembly

open FinishLine Truncation TowerCardGrowth SeedCardBound TwoPointAssembly
open CopyAClassification TowerNoAbsorption

theorem no_comparison_of_firstSlice (n k : ℕ) (hnk : n ≤ k)
    (x : D n) (hx : JoinIrred (D n) x)
    (y : D (k + 1)) (hy : JoinIrred (D (k + 1)) y)
    (hnotA : ¬ ∃ F : EndP (D k), y = glueA (markedPt k) F)
    (hFS : FirstSlice k) :
    IsEmpty ((WeakProd (Fam n) × Base n x)
      ≃o (WeakProd (Fam (k + 1)) × Base (k + 1) y)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnk
  refine ⟨fun e => ?_⟩
  letI : OrderBot (Base (n + m) (push n m x)) :=
    levelSeedDualBot (joinIrred_push n m hx)
  letI : OrderBot (Base (n + m + 1) y) := levelSeedDualBot hy
  haveI : IsAtomic (Base (n + m) (push n m x)) := GluingTowerLibrary.isAtomic_of_finite
  haveI : IsAtomic (Base (n + m + 1) y) := GluingTowerLibrary.isAtomic_of_finite
  have e2 := (shiftMany n x hx m).symm.trans e
  set T := Base (n + m) (push n m x) with hT
  set S := Base (n + m + 1) y with hS
  have hTlt : Fintype.card T < Fintype.card (D (n + m)) :=
    card_levelSeed_lt (n + m) (push n m x)
  have hDlt : Fintype.card (D (n + m)) < Fintype.card S :=
    card_D_lt_card_seed_notA (n + m) hy hnotA
  have hSlt : Fintype.card S < Fintype.card (D (n + m + 1)) :=
    card_levelSeed_lt (n + m + 1) y
  set N := Nat.card S with hNdef
  have hNc : N = Fintype.card S := Nat.card_eq_fintype_card
  have hbig : ∀ i, N < Nat.card (Fam (n + m + 1) i) := by
    intro i
    rw [hNc, Nat.card_eq_fintype_card]
    exact lt_of_lt_of_le hSlt (card_D_strictMono.monotone (by omega))
  have hsub : ∀ {L : Type} [PartialOrder L] [OrderBot L] [Fintype L] (β : L),
      Nat.card ↥(atomFactor L β) ≤ Nat.card L :=
    fun β => Nat.card_le_card_of_injective _ Subtype.val_injective
  have hSat : ∀ β : S, IsAtom β → Nat.card ↥(atomFactor S β) ≤ N :=
    fun β _ => hsub β
  have hTat : ∀ τ : T, IsAtom τ → Nat.card ↥(atomFactor T τ) ≤ N := by
    intro τ _
    refine le_trans (hsub τ) ?_
    rw [Nat.card_eq_fintype_card, hNc]
    omega
  obtain ⟨f⟩ := seed_iso_prod (D := Fam (n + m)) (E := Fam (n + m + 1))
    (fun j => lamD (n + m + j)) (fun i => lamD (n + m + 1 + i))
    (fun j => lamD_ne_bot (n + m + j)) (fun j => lamD_le (n + m + j))
    (fun i => lamD_ne_bot (n + m + 1 + i)) (fun i => lamD_le (n + m + 1 + i))
    e2 N hbig hSat hTat
  have h0 : Nat.card (Fam (n + m) 0) ≤ N := by
    rw [hNc, Nat.card_eq_fintype_card]
    exact le_of_lt hDlt
  have h1 : ∀ i, N < Nat.card (Fam (n + m) (i + 1)) := by
    intro i
    rw [hNc, Nat.card_eq_fintype_card]
    exact lt_of_lt_of_le hSlt (card_D_strictMono.monotone (by omega))
  have g : (D (n + m) × T) ≃o S :=
    (JSeedRecursion.prodCongrIso
      (weakBelowSingletonIso (E := Fam (n + m)) N h0 h1).symm (OrderIso.refl T)).trans f
  exact (hFS (push n m x) (joinIrred_push n m hx) y hy hnotA).elim g.symm

end Assembly

end BaseShift
