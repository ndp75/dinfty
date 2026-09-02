import Dinfty.CopyBCStructure

open GluingTowerLibrary SierpinskiApplication

/-!
# Both halves of `TwoPointFixed`, from one theorem

§34 did the `midInf` half and §35 noted that the `toD 0 ⊤` half needed
`no_iso_of_small_pieces` generalised to a finite piece on the **left**, because
`topJ`'s seed is `WeakProd (Fam 0) × C₂` rather than a bare `WeakProd`.

With `WeakProdFactorization.no_iso_of_small_piecesL` in hand, the two halves are
**the same theorem**: the copy-`A` argument never looks at the finite piece `T`
on the left beyond needing it to be atomic, so it can be run against any point
whose seed has the product shape.  `midInf` takes `T` = its one-point level-`0`
seed and `topJ` takes `T` = its two-chain — and neither has to be identified with
anything.

```lean
seedSeparates_gen (z) (hz : (JBelow z)ᵒᵈ ≃o WeakProd (Fam 0) × T)
    (hbase) (h : CopyBCExcludedFor z) :
    ∀ N y, JoinIrred (D N) y → Nonempty (JBelow (toD N y) ≃o JBelow z) → toD N y = z
```

so

```lean
twoPointFixed (h₁ : CopyBCExcludedFor midInf) (h₂ : CopyBCExcludedFor (toD 0 ⊤)) :
    TwoPointFixed
```

**`TwoPointFixed` is now exactly two `Prop`s**, one per point, both about copies
`B` and `C`.  §35's item 3 is closed; items 1 and 2 remain.
-/

open scoped Classical

namespace TwoPointAssembly

open CopyAClassification SeedShapeProof SeedLevelStep WeakProductAbsorption
open WeakProdFactorization TowerCardGrowth TowerNoAbsorption ChainUnion
open SeedSeparation MidAnchor SeedChain JSeedRecursion AtomFactorGeneration
open JoinIrredLevelStable JoinIrredDInfty TwoPointHypothesis

private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
private theorem hmtk (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
private theorem hbtk (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

/-! ## The dualised seed of a join-irreducible has a bottom -/

noncomputable def levelSeedDualBot {N : ℕ} {y : D N} (hy : JoinIrred (D N) y) :
    OrderBot ((LevelSeed N y)ᵒᵈ) :=
  { bot := (⟨y, hy, le_refl y⟩ : LevelSeed N y)
    bot_le := fun a => a.2.2 }

/-! ## The copy-`A` exclusion, with an arbitrary finite piece on the left -/

theorem copyA_forces_bot_gen {T : Type} [PartialOrder T] [OrderBot T] [IsAtomic T]
    (k : ℕ) {p : D k} (hp : p ≠ ⊥) (q : {x : D k // JoinIrred (D k) x})
    (e : (WeakProd (Fam 0) × T) ≃o (WeakProd (Fam (k + 1)) ×
      ((LevelSeed (k + 1) (glueA (markedPt k)
        (jiOrderIso (OrderDual.toDual p, q)).1))ᵒᵈ))) : False := by
  haveI : OrderBot (UpSet k p) :=
    { bot := ⟨p, le_refl p⟩
      bot_le := fun a => a.2 }
  haveI : IsAtomic (UpSet k p) := GluingTowerLibrary.isAtomic_of_finite
  haveI := levelSeedDualBot q.2
  haveI : IsAtomic ((LevelSeed k q.1)ᵒᵈ) := GluingTowerLibrary.isAtomic_of_finite
  have e' : (WeakProd (Fam 0) × T)
      ≃o (WeakProd (Fam (k + 1)) × (UpSet k p × (LevelSeed k q.1)ᵒᵈ)) :=
    e.trans (prodCongrIso (OrderIso.refl _) (copyASeedDualIso k p q))
  have hsmall : ∀ i, Fintype.card (Fam 0 k) < Fintype.card (Fam (k + 1) i) := by
    intro i
    show Fintype.card (D (0 + k)) < Fintype.card (D (k + 1 + i))
    exact card_D_strictMono (by omega)
  have hA : Fintype.card (UpSet k p) < Fintype.card (Fam 0 k) := by
    show Fintype.card (UpSet k p) < Fintype.card (D (0 + k))
    simpa using card_upSet_lt_D k hp
  have hB : Fintype.card ((LevelSeed k q.1)ᵒᵈ) < Fintype.card (Fam 0 k) := by
    show Fintype.card ((LevelSeed k q.1)ᵒᵈ) < Fintype.card (D (0 + k))
    simpa using card_levelSeed_lt k q.1
  have hempty := no_iso_of_small_piecesL (D := Fam 0) (E := Fam (k + 1)) (T := T)
    (A := UpSet k p) (B := (LevelSeed k q.1)ᵒᵈ)
    (fun j => lamD (0 + j)) (fun j => lamD (k + 1 + j))
    (fun j => lamD_ne_bot (0 + j)) (fun j => lamD_le (0 + j))
    (fun j => lamD_ne_bot (k + 1 + j)) (fun j => lamD_le (k + 1 + j))
    k hsmall hA hB
  exact hempty.elim e'

/-! ## The induction step, for any point with the product shape -/

theorem copyA_step_gen (z : DInfty) {T : Type} [PartialOrder T] [OrderBot T] [IsAtomic T]
    (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam 0) × T))
    (k : ℕ) (F : EndP (D k)) (hF : JoinIrred (EndP (D k)) F)
    (e : JBelow (toD (k + 1) (glueA (markedPt k) F)) ≃o JBelow z) :
    ∃ q : D k, JoinIrred (D k) q ∧ glueA (markedPt k) F = iotaD k q
      ∧ Nonempty (JBelow (toD k q) ≃o JBelow z) := by
  letI := realUniqueAtomCoatom k
  set aq := jiOrderIso.symm (⟨F, hF⟩ : {f : EndP (D k) // JoinIrred (EndP (D k)) f}) with haq
  have hFval : F = (jiOrderIso aq).1 := by
    rw [haq, OrderIso.apply_symm_apply]
  have hyji : JoinIrred (D (k + 1)) (glueA (markedPt k) F) :=
    (joinIrred_glueA_iff (markedPt k) (hmk k) (hmtk k) (hbtk k) F).mpr hF
  have ecmp : (WeakProd (Fam 0) × T)
      ≃o (WeakProd (Fam (k + 1)) × (LevelSeed (k + 1) (glueA (markedPt k) F))ᵒᵈ) :=
    hz.symm.trans (e.dual.symm.trans (seedShape (k + 1) (glueA (markedPt k) F) hyji))
  rw [hFval] at ecmp
  have hp : OrderDual.ofDual aq.1 = (⊥ : D k) := by
    by_contra hne
    exact copyA_forces_bot_gen (T := T) k hne aq.2 ecmp
  have haq1 : aq.1 = OrderDual.toDual (⊥ : D k) := hp
  have hFc : F = constHom aq.2.1 := by
    rw [hFval]
    have hswap : (jiOrderIso aq).1
        = (jiOrderIso (OrderDual.toDual (⊥ : D k), aq.2)).1 := by
      rw [← haq1]
    rw [hswap, jiOrderIso_bot_val (P := D k) aq.2]
  have hiota : glueA (markedPt k) F = iotaD k aq.2.1 := by
    rw [hFc]
    rfl
  have hstep : toD (k + 1) (glueA (markedPt k) F) = toD k aq.2.1 := by
    rw [hiota]
    have h2 := toD_iotaLe (Nat.le_succ k) aq.2.1
    rwa [iotaLe_succ (le_refl k) (Nat.le_succ k) aq.2.1,
         iotaLe_self (le_refl k) aq.2.1] at h2
  exact ⟨aq.2.1, aq.2.2, hiota, ⟨hstep ▸ e⟩⟩

/-! ## The induction -/

/-- The remaining input, for a point `z`.

**The join-irreducibility hypothesis is not decoration.**  Without it the seed
`LevelSeed (k+1) y` has no maximum, so its dual has no `⊥` and `seedShape` does
not apply — the statement would not be provable.  It costs nothing: the only
place this `Prop` is used (`seedSeparates_gen`) has `JoinIrred` in hand, because
an order-automorphism carries join-irreducibles to join-irreducibles. -/
def CopyBCExcludedFor (z : DInfty) : Prop :=
  ∀ (k : ℕ) (y : D (k + 1)), JoinIrred (D (k + 1)) y →
    (¬ ∃ F : EndP (D k), y = glueA (markedPt k) F) →
    ¬ Nonempty (JBelow (toD (k + 1) y) ≃o JBelow z)

theorem seedSeparates_gen (z : DInfty) {T : Type} [PartialOrder T] [OrderBot T] [IsAtomic T]
    (hz : (JBelow z)ᵒᵈ ≃o (WeakProd (Fam 0) × T))
    (hbase : ∀ y : D 0, JoinIrred (D 0) y →
      Nonempty (JBelow (toD 0 y) ≃o JBelow z) → toD 0 y = z)
    (h : CopyBCExcludedFor z) :
    ∀ (N : ℕ) (y : D N), JoinIrred (D N) y →
      Nonempty (JBelow (toD N y) ≃o JBelow z) → toD N y = z := by
  intro N
  induction N with
  | zero => exact hbase
  | succ k ih =>
      intro y hy he
      by_cases hA : ∃ F : EndP (D k), y = glueA (markedPt k) F
      · obtain ⟨F, rfl⟩ := hA
        have hF : JoinIrred (EndP (D k)) F :=
          (joinIrred_glueA_iff (markedPt k) (hmk k) (hmtk k) (hbtk k) F).mp hy
        obtain ⟨q, hq, hiota, hqe⟩ := copyA_step_gen z hz k F hF he.some
        have hstep : toD (k + 1) (glueA (markedPt k) F) = toD k q := by
          rw [hiota]
          have h2 := toD_iotaLe (Nat.le_succ k) q
          rwa [iotaLe_succ (le_refl k) (Nat.le_succ k) q, iotaLe_self (le_refl k) q] at h2
        rw [hstep]
        exact ih q hq hqe
      · exact absurd he (h k y hy hA)

/-! ## The two instances -/

noncomputable instance : OrderBot (Base 0 (dMid 0)) :=
  levelSeedDualBot SeedsDiffer.joinIrred_D0_mid

noncomputable instance : IsAtomic (Base 0 (dMid 0)) := GluingTowerLibrary.isAtomic_of_finite

noncomputable instance : OrderBot (Base 0 (⊤ : D 0)) := levelSeedDualBot joinIrred_D0_top

noncomputable instance : IsAtomic (Base 0 (⊤ : D 0)) := GluingTowerLibrary.isAtomic_of_finite

theorem base_midInf : ∀ y : D 0, JoinIrred (D 0) y →
    Nonempty (JBelow (toD 0 y) ≃o JBelow midInf) → toD 0 y = midInf := by
  intro y hy he
  rcases D0_joinIrred_cases hy with rfl | rfl
  · rfl
  · exact SeedsDiffer.jBelow_midInf_not_iso_topJ.elim he.some.symm

theorem base_topJ : ∀ y : D 0, JoinIrred (D 0) y →
    Nonempty (JBelow (toD 0 y) ≃o JBelow (toD 0 (⊤ : D 0))) → toD 0 y = toD 0 (⊤ : D 0) := by
  intro y hy he
  rcases D0_joinIrred_cases hy with rfl | rfl
  · exact SeedsDiffer.jBelow_midInf_not_iso_topJ.elim he.some
  · rfl

/-- **Every automorphism fixes the seam**, given the copy-`B`/`C` exclusion. -/
theorem midInf_fixed (h : CopyBCExcludedFor midInf) (θ : DInfty ≃o DInfty) :
    θ midInf = midInf :=
  fixed_of_seedSeparates_ji joinIrred_midInf
    (seedSeparates_gen midInf (seedShape 0 (dMid 0) SeedsDiffer.joinIrred_D0_mid)
      base_midInf h) θ

/-- **…and the stage-`0` top.** -/
theorem topJ_fixed (h : CopyBCExcludedFor (toD 0 (⊤ : D 0))) (θ : DInfty ≃o DInfty) :
    θ (toD 0 (⊤ : D 0)) = toD 0 (⊤ : D 0) :=
  fixed_of_seedSeparates_ji joinIrred_toD_zero_top
    (seedSeparates_gen (toD 0 (⊤ : D 0)) (seedShape 0 (⊤ : D 0) joinIrred_D0_top)
      base_topJ h) θ

/-- **`TwoPointFixed`, reduced to two `Prop`s.** -/
theorem twoPointFixed (h₁ : CopyBCExcludedFor midInf)
    (h₂ : CopyBCExcludedFor (toD 0 (⊤ : D 0))) : TwoPointFixed :=
  fun θ => ⟨midInf_fixed h₁ θ, topJ_fixed h₂ θ⟩

end TwoPointAssembly
