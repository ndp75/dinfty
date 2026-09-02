import Dinfty.MidAnchor

open GluingTowerLibrary SierpinskiApplication

-- [D-1673] §The-two-point-hypothesis
open scoped Classical

namespace TwoPointHypothesis

open Assembly ColimitCompatPipe JoinIrredDInfty MidAnchor

-- [D-1674] §The-two-Props
-- [D-1675] StageFixedZero
def StageFixedZero : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (x : D 0), ∃ y : D 0, θ (toD 0 x) = toD 0 y

-- [D-1676] TwoPointFixed
def TwoPointFixed : Prop :=
  ∀ θ : DInfty ≃o DInfty,
    θ midInf = midInf ∧ θ (toD 0 (⊤ : D 0)) = toD 0 (⊤ : D 0)

-- [D-1677] §The-equivalence
-- [D-1678] orderIso_map_bot
theorem orderIso_map_bot (θ : DInfty ≃o DInfty) : θ (⊥ : DInfty) = (⊥ : DInfty) :=
  θ.map_bot

-- [D-1679] stageFixedZero_iff_twoPointFixed
theorem stageFixedZero_iff_twoPointFixed : StageFixedZero ↔ TwoPointFixed := by
  constructor
  · intro h θ
    exact ⟨fixes_midInf_of_maps_into θ (h θ),
           fixes_toD_zero_top_of_maps_into θ (h θ)⟩
  · intro h θ x
    have hx : x = (⊥ : D 0) ∨ x = dMid 0 ∨ x = (⊤ : D 0) := by
      show x = (0 : Fin 3) ∨ x = (1 : Fin 3) ∨ x = (2 : Fin 3)
      revert x; decide
    rcases hx with rfl | rfl | rfl
    · refine ⟨(⊥ : D 0), ?_⟩
      rw [← bot_eq_toD 0, orderIso_map_bot]
    · exact ⟨dMid 0, (h θ).1⟩
    · exact ⟨(⊤ : D 0), (h θ).2⟩

-- [D-1680] §Necessity-so-the-hypothesis-is-falsifiable
-- [D-1681] joinIrred_D0_top
theorem joinIrred_D0_top : JoinIrred (D 0) (⊤ : D 0) := by
  show JoinIrred (Fin 3) (2 : Fin 3)
  exact ⟨by decide, by decide⟩

-- [D-1682] stageFixed_imp_stageFixedZero
theorem stageFixed_imp_stageFixedZero (h : StageFixed) : StageFixedZero := by
  intro θ x
  have hx : x = (⊥ : D 0) ∨ x = dMid 0 ∨ x = (⊤ : D 0) := by
    show x = (0 : Fin 3) ∨ x = (1 : Fin 3) ∨ x = (2 : Fin 3)
    revert x; decide
  rcases hx with rfl | rfl | rfl
  · refine ⟨(⊥ : D 0), ?_⟩
    rw [← bot_eq_toD 0, orderIso_map_bot]
  · exact h θ 0 (dMid 0) (D_mid_joinIrred 0)
  · exact h θ 0 (⊤ : D 0) joinIrred_D0_top

-- [D-1683] stageFixed_imp_twoPointFixed
theorem stageFixed_imp_twoPointFixed (h : StageFixed) : TwoPointFixed :=
  stageFixedZero_iff_twoPointFixed.mp (stageFixed_imp_stageFixedZero h)

-- [D-1684] not_stageFixed_of_not_twoPointFixed
theorem not_stageFixed_of_not_twoPointFixed (h : ¬ TwoPointFixed) : ¬ StageFixed :=
  fun hs => h (stageFixed_imp_twoPointFixed hs)

-- [D-1685] §Both-points-are-join-irreducible-in-the-colimit
-- [D-1686] joinIrred_midInf
theorem joinIrred_midInf : JoinIrred DInfty midInf := by
  rw [midInf]
  exact (joinIrred_toD_iff 0 (dMid 0)).mpr (D_mid_joinIrred 0)

-- [D-1687] joinIrred_toD_zero_top
theorem joinIrred_toD_zero_top : JoinIrred DInfty (toD 0 (⊤ : D 0)) :=
  (joinIrred_toD_iff 0 (⊤ : D 0)).mpr joinIrred_D0_top

-- [D-1688] midInf_lt_top_zero
theorem midInf_lt_top_zero : midInf < toD 0 (⊤ : D 0) := midInf_lt_toD_top 0

end TwoPointHypothesis
