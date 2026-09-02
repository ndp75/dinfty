import Dinfty.SigmaRebuild

open GluingTowerLibrary SierpinskiApplication

-- [D-2591] §qAA-explicitly-and-a-retraction
namespace QAAExplicit

open PhiIterateTower PhiBilimit GlueAAEpPartner GlueTag GenContinuity

attribute [-instance] OrderHom.instDecidableEqOfForall

-- [D-2592] §qAA-is-a-definition-not-a-choice
-- [D-2593] qAA_eq
theorem qAA_eq (k : ℕ) : qAA k = EpFromJoin.upper (glueAA k) := rfl

-- [D-2594] glueAA_qAA_le
theorem glueAA_qAA_le (k : ℕ) (z : D (k + 2)) : glueAA k (qAA k z) ≤ z :=
  EpFromJoin.map_upper_le (glueAA k) (glueAA_bot k) (GlueAAJoin.glueAAJoinPreserving k) z

-- [D-2595] le_qAA
theorem le_qAA (k : ℕ) {y : D (k + 1)} {z : D (k + 2)} (h : glueAA k y ≤ z) : y ≤ qAA k z :=
  EpFromJoin.le_upper (glueAA k) y z h

-- [D-2596] qAA_isGreatest
theorem qAA_isGreatest (k : ℕ) (z : D (k + 2)) :
    IsGreatest {y : D (k + 1) | glueAA k y ≤ z} (qAA k z) :=
  ⟨glueAA_qAA_le k z, fun _ hy => le_qAA k hy⟩

-- [D-2597] eq_qAA_of_isGreatest
theorem eq_qAA_of_isGreatest (k : ℕ) {z : D (k + 2)} {y : D (k + 1)}
    (h : IsGreatest {y : D (k + 1) | glueAA k y ≤ z} y) : y = qAA k z :=
  h.unique (qAA_isGreatest k z)

-- [D-2598] glueAA_le_iff_le_qAA
theorem glueAA_le_iff_le_qAA (k : ℕ) (y : D (k + 1)) (z : D (k + 2)) :
    glueAA k y ≤ z ↔ y ≤ qAA k z :=
  ⟨le_qAA k, fun h => le_trans (glueAA_monotone k h) (glueAA_qAA_le k z)⟩

-- [D-2599] §The-tower-s-base-projection-is-this-map
-- [D-2600] prj_zero_eq
theorem prj_zero_eq : phiTowerEP.prj 0 = qAA 0 := rfl

-- [D-2601] level_zero_isGreatest
theorem level_zero_isGreatest (x : B) :
    IsGreatest {y : D 1 | glueAA 0 y ≤ x.1 1} (x.1 0) := by
  have h : qAA 0 (x.1 1) = x.1 0 := x.2 0
  rw [← h]
  exact qAA_isGreatest 0 (x.1 1)

-- [D-2602] §The-payload-of-a-strict-constant-pinned
-- [D-2603] ins_eq_bot_iff
theorem ins_eq_bot_iff (j : ℕ) (w : D (j + 1)) :
    phiTowerEP.ins j w = (⊥ : B) ↔ w = (⊥ : D (j + 1)) := by
  constructor
  · intro h
    have h2 := congrArg (fun z : B => z.1 j) h
    rw [EpPairTower.ins_self] at h2
    exact h2
  · intro h
    rw [h]
    exact ins_bot j

-- [D-2604] projEndDown_strictConst_bot
theorem projEndDown_strictConst_bot (j : ℕ) (c : B) :
    ((PhiCocone.projEndDown j).toFun (SigmaRebuild.strictConst c)) (⊥ : D (j + 1))
      = (⊥ : D (j + 1)) := by
  show (SigmaRebuild.strictFun c (phiTowerEP.ins j (⊥ : D (j + 1)))).1 j = (⊥ : D (j + 1))
  rw [ins_bot j, SigmaRebuild.strictFun_bot_case (rfl : botB = ⊥)]
  rfl

-- [D-2605] projEndDown_strictConst_ne
theorem projEndDown_strictConst_ne (j : ℕ) (c : B) {w : D (j + 1)}
    (hw : w ≠ (⊥ : D (j + 1))) :
    ((PhiCocone.projEndDown j).toFun (SigmaRebuild.strictConst c)) w = c.1 j := by
  have hne : phiTowerEP.ins j w ≠ (⊥ : B) := fun h => hw ((ins_eq_bot_iff j w).mp h)
  show (SigmaRebuild.strictFun c (phiTowerEP.ins j w)).1 j = c.1 j
  rw [SigmaRebuild.strictFun_ne_case hne]

-- [D-2606] §The-base-equation-for-a-fixed-point
-- [D-2607] fix_level_one
theorem fix_level_one {x : B} (hx : SigmaRebuild.ifsS.sigmaA x = x) :
    (x.1 1).1 = Sum.inl ((PhiCocone.projEndDown 0).toFun (SigmaRebuild.strictConst x)) := by
  have h1 : ((SigmaRebuild.ifsS.sigmaA x).1 1).1 = (x.1 1).1 :=
    congrArg (fun z : B => (z.1 1).1) hx
  rw [← h1]
  exact InternalIFSInstance.pLeg_val 0 (SigmaRebuild.strictConst x)

-- [D-2608] fix_level_zero
theorem fix_level_zero {x : B} (hx : SigmaRebuild.ifsS.sigmaA x = x) :
    IsGreatest {y : D 1 | glueAA 0 y ≤ x.1 1} (x.1 0)
      ∧ (x.1 1).1 = Sum.inl ((PhiCocone.projEndDown 0).toFun (SigmaRebuild.strictConst x))
      ∧ ((PhiCocone.projEndDown 0).toFun (SigmaRebuild.strictConst x)) (⊥ : D 1) = ⊥
      ∧ ∀ w : D 1, w ≠ ⊥ →
          ((PhiCocone.projEndDown 0).toFun (SigmaRebuild.strictConst x)) w = x.1 0 :=
  ⟨level_zero_isGreatest x, fix_level_one hx, projEndDown_strictConst_bot 0 x,
    fun w hw => projEndDown_strictConst_ne 0 x hw⟩

end QAAExplicit
