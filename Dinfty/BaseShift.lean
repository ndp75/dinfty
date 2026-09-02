import Dinfty.FinishLine
import Dinfty.JoinIrredLevelStable
import Dinfty.SeedCardBound
import Dinfty.TwoPointAssembly
import Dinfty.TowerNoAbsorption

open GluingTowerLibrary SierpinskiApplication

-- [D-3119] §Paying-the-bookkeeping-debt-shifting-the-base
open scoped Classical

universe u

namespace BaseShift

open SeedLevelStep JSeedRecursion WeakProductAbsorption AtomFactorGeneration
open WeakProdFactorization SeedShapeProof SeedSeparation JoinIrredLevelStable

-- [D-3120] push
noncomputable def push (n : ℕ) : (m : ℕ) → D n → D (n + m)
  | 0, x => x
  | (m + 1), x => iotaD (n + m) (push n m x)

-- [D-3121] joinIrred_push
theorem joinIrred_push (n m : ℕ) {x : D n} (hx : JoinIrred (D n) x) :
    JoinIrred (D (n + m)) (push n m x) := by
  induction m with
  | zero => exact hx
  | succ m ih => exact (joinIrred_iotaD_iff (n + m) (push n m x)).mpr ih

-- [D-3122] shiftStep
noncomputable def shiftStep (n : ℕ) (x : D n) (hx : JoinIrred (D n) x) :
    (WeakProd (Fam n) × Base n x)
      ≃o (WeakProd (Fam (n + 1)) × Base (n + 1) (iotaD n x)) := by
  refine (seedShape n x hx).symm.trans ?_
  rw [← toD_iotaD n x]
  exact seedShape (n + 1) (iotaD n x) ((joinIrred_iotaD_iff n x).mpr hx)

-- [D-3123] shiftMany
noncomputable def shiftMany (n : ℕ) (x : D n) (hx : JoinIrred (D n) x) :
    (m : ℕ) → ((WeakProd (Fam n) × Base n x)
      ≃o (WeakProd (Fam (n + m)) × Base (n + m) (push n m x)))
  | 0 => OrderIso.refl _
  | (m + 1) =>
      (shiftMany n x hx m).trans
        (shiftStep (n + m) (push n m x) (joinIrred_push n m hx))

-- [D-3124] §The-other-half-only-the-bottom-factor-survives
section Singleton

variable {E : ℕ → Type u} [∀ j, PartialOrder (E j)] [∀ j, OrderBot (E j)]

open Truncation

-- [D-3125] weakBelowSingletonIso
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

-- [D-3126] §The-assembly-FirstSlice-closes-every-comparison
section Assembly

open FinishLine Truncation TowerCardGrowth SeedCardBound TwoPointAssembly
open CopyAClassification TowerNoAbsorption

-- [D-3127] no_comparison_of_firstSlice
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
