import Dinfty.CopyBCStructure

open GluingTowerLibrary SierpinskiApplication

-- [D-1922] §Both-halves-of-TwoPointFixed-from-one-theorem
open scoped Classical

namespace TwoPointAssembly

open CopyAClassification SeedShapeProof SeedLevelStep WeakProductAbsorption
open WeakProdFactorization TowerCardGrowth TowerNoAbsorption ChainUnion
open SeedSeparation MidAnchor SeedChain JSeedRecursion AtomFactorGeneration
open JoinIrredLevelStable JoinIrredDInfty TwoPointHypothesis

-- [D-1923] hmk
private theorem hmk (k : ℕ) : (markedPt k) ≠ ⊥ := (D_marked_point_nondegenerate k).1
-- [D-1924] hmtk
private theorem hmtk (k : ℕ) : (markedPt k) ≠ ⊤ := (D_marked_point_nondegenerate k).2.1
-- [D-1925] hbtk
private theorem hbtk (k : ℕ) : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2

-- [D-1926] §The-dualised-seed-of-a-join-irreducible-has
-- [D-1927] levelSeedDualBot
noncomputable def levelSeedDualBot {N : ℕ} {y : D N} (hy : JoinIrred (D N) y) :
    OrderBot ((LevelSeed N y)ᵒᵈ) :=
  { bot := (⟨y, hy, le_refl y⟩ : LevelSeed N y)
    bot_le := fun a => a.2.2 }

-- [D-1928] §The-copy-A-exclusion-with-an-arbitrary-finite
-- [D-1929] copyA_forces_bot_gen
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

-- [D-1930] §The-induction-step-for-any-point-with
-- [D-1931] copyA_step_gen
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

-- [D-1932] §The-induction
-- [D-1933] CopyBCExcludedFor
def CopyBCExcludedFor (z : DInfty) : Prop :=
  ∀ (k : ℕ) (y : D (k + 1)), JoinIrred (D (k + 1)) y →
    (¬ ∃ F : EndP (D k), y = glueA (markedPt k) F) →
    ¬ Nonempty (JBelow (toD (k + 1) y) ≃o JBelow z)

-- [D-1934] seedSeparates_gen
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

-- [D-1935] §The-two-instances
-- [D-1936] inst-OrderBot
noncomputable instance : OrderBot (Base 0 (dMid 0)) :=
  levelSeedDualBot SeedsDiffer.joinIrred_D0_mid

-- [D-1937] inst-IsAtomic
noncomputable instance : IsAtomic (Base 0 (dMid 0)) := GluingTowerLibrary.isAtomic_of_finite

-- [D-1938] inst-OrderBot
noncomputable instance : OrderBot (Base 0 (⊤ : D 0)) := levelSeedDualBot joinIrred_D0_top

-- [D-1939] inst-IsAtomic
noncomputable instance : IsAtomic (Base 0 (⊤ : D 0)) := GluingTowerLibrary.isAtomic_of_finite

-- [D-1940] base_midInf
theorem base_midInf : ∀ y : D 0, JoinIrred (D 0) y →
    Nonempty (JBelow (toD 0 y) ≃o JBelow midInf) → toD 0 y = midInf := by
  intro y hy he
  rcases D0_joinIrred_cases hy with rfl | rfl
  · rfl
  · exact SeedsDiffer.jBelow_midInf_not_iso_topJ.elim he.some.symm

-- [D-1941] base_topJ
theorem base_topJ : ∀ y : D 0, JoinIrred (D 0) y →
    Nonempty (JBelow (toD 0 y) ≃o JBelow (toD 0 (⊤ : D 0))) → toD 0 y = toD 0 (⊤ : D 0) := by
  intro y hy he
  rcases D0_joinIrred_cases hy with rfl | rfl
  · exact SeedsDiffer.jBelow_midInf_not_iso_topJ.elim he.some
  · rfl

-- [D-1942] midInf_fixed
theorem midInf_fixed (h : CopyBCExcludedFor midInf) (θ : DInfty ≃o DInfty) :
    θ midInf = midInf :=
  fixed_of_seedSeparates_ji joinIrred_midInf
    (seedSeparates_gen midInf (seedShape 0 (dMid 0) SeedsDiffer.joinIrred_D0_mid)
      base_midInf h) θ

-- [D-1943] topJ_fixed
theorem topJ_fixed (h : CopyBCExcludedFor (toD 0 (⊤ : D 0))) (θ : DInfty ≃o DInfty) :
    θ (toD 0 (⊤ : D 0)) = toD 0 (⊤ : D 0) :=
  fixed_of_seedSeparates_ji joinIrred_toD_zero_top
    (seedSeparates_gen (toD 0 (⊤ : D 0)) (seedShape 0 (⊤ : D 0) joinIrred_D0_top)
      base_topJ h) θ

-- [D-1944] twoPointFixed
theorem twoPointFixed (h₁ : CopyBCExcludedFor midInf)
    (h₂ : CopyBCExcludedFor (toD 0 (⊤ : D 0))) : TwoPointFixed :=
  fun θ => ⟨midInf_fixed h₁ θ, topJ_fixed h₂ θ⟩

end TwoPointAssembly
