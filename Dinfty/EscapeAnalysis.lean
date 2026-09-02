import Dinfty.InternalIFSInstance

open GluingTowerLibrary SierpinskiApplication

-- [D-3508] §Fix-A-is-not-a-singleton-Theorem-ESCAPE-fails
namespace EscapeAnalysis

open PhiIterateTower PhiBilimit GlueTag GenContinuity InternalIFSInstance

attribute [-instance] OrderHom.instDecidableEqOfForall

-- [D-3509] §pLeg-of-the-marked-tag-A-point
-- [D-3510] pLeg_markedB
theorem pLeg_markedB (j : ℕ) :
    PhiCocone.pLeg j (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB)
      = dMid (j + 2) := by
  refine Subtype.ext ?_
  rw [pLeg_val j markedB, projEndDown_markedB j]
  rfl

-- [D-3511] §The-marked-point-is-fixed
-- [D-3512] sigmaA_mid
theorem sigmaA_mid : ifsB.sigmaA midB = midB := by
  refine Subtype.ext (funext (fun n => ?_))
  cases n with
  | zero =>
      show phiTowerEP.prj 0
          (PhiCocone.pLeg 0 (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB))
        = dMid 1
      rw [pLeg_markedB 0]
      exact (iter 0).prj_mid
  | succ n =>
      show PhiCocone.pLeg n (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB)
        = dMid (n + 2)
      exact pLeg_markedB n

-- [D-3513] mid_mem_fix
theorem mid_mem_fix : midB ∈ Fix ifsB.sigmaA := sigmaA_mid

-- [D-3514] §and-it-is-in-the-orbit
-- [D-3515] tagB_bot_eq_mark
theorem tagB_bot_eq_mark :
    tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)
      = tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB := by
  refine Subtype.ext ?_
  show (if (⊥ : ScottEndP B) = ⊥ then (Sum.inl markedB : GlueBaseGen (ScottEndP B))
        else Sum.inr (Sum.inl (⊥ : ScottEndP B))) = Sum.inl markedB
  rw [if_pos rfl]

-- [D-3516] sigmaB_bot
theorem sigmaB_bot : ifsB.sigmaB (⊥ : B) = midB := by
  show sec (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (constS (⊥ : B))) = midB
  rw [constS_bot, tagB_bot_eq_mark]
  exact sigmaA_mid

-- [D-3517] §Theorem-ESCAPE-fails
-- [D-3518] fix_sigmaA_not_singleton
theorem fix_sigmaA_not_singleton (b : B) : Fix ifsB.sigmaA ≠ {b} := by
  intro h
  have hbot : (⊥ : B) ∈ Fix ifsB.sigmaA := bot_mem_fix_sigmaA
  have hmid : midB ∈ Fix ifsB.sigmaA := mid_mem_fix
  rw [h] at hbot hmid
  exact midB_ne_botB (hmid.trans hbot.symm)

-- [D-3519] no_fixA
theorem no_fixA (botC : B) (hfixA : Fix ifsB.sigmaA = {botC}) : False :=
  fix_sigmaA_not_singleton botC hfixA

end EscapeAnalysis
