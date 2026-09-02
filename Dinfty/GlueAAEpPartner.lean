import Dinfty.JoinPrime
import Dinfty.EpFromJoin
import Dinfty.ProjectionTripointed
import Dinfty.TowerShift

open GluingTowerLibrary SierpinskiApplication

-- [D-2215] §79-s-question-as-a-single-named-Prop-and-what
open scoped Classical

namespace GlueAAEpPartner

open JoinPrimality

-- [D-2216] GlueAAJoinPreserving
def GlueAAJoinPreserving (k : ℕ) : Prop :=
  ∀ x y : D (k + 1), glueAA k (x ⊔ y) = glueAA k x ⊔ glueAA k y

-- [D-2217] §The-two-hypotheses-that-are-not-the-question
-- [D-2218] iotaEndP_bot
theorem iotaEndP_bot (k : ℕ) :
    iotaEndP k (⊥ : EndP (D k)) = (⊥ : EndP (D (k + 1))) := by
  ext w
  show iotaD k ((⊥ : EndP (D k)) (pD k w)) = (⊥ : EndP (D (k + 1))) w
  rw [endPBot_apply, endPBot_apply]
  exact iotaGenM_bot (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial

-- [D-2219] glueAA_bot
theorem glueAA_bot (k : ℕ) : glueAA k (⊥ : D (k + 1)) = (⊥ : D (k + 2)) := by
  rw [PhiTriTower.bot_succ_eq k, PhiTriTower.bot_succ_eq (k + 1)]
  exact Subtype.ext (congrArg Sum.inl (iotaEndP_bot k))

-- [D-2220] §What-the-question-buys
-- [D-2221] exists_glueAA_epPartner
theorem exists_glueAA_epPartner (k : ℕ) (h : GlueAAJoinPreserving k) :
    ∃ q : D (k + 2) → D (k + 1), Monotone q ∧ (∀ x, q (glueAA k x) = x)
      ∧ (∀ z, glueAA k (q z) ≤ z) :=
  EpFromJoin.exists_epPartner (glueAA k) (glueAA_bot k) h
    (fun _ _ hab => glueAA_reflect k hab)

-- [D-2222] qAA
noncomputable def qAA (k : ℕ) : D (k + 2) → D (k + 1) := EpFromJoin.upper (glueAA k)

-- [D-2223] fTower
noncomputable def fTower (h : ∀ k, GlueAAJoinPreserving k) : EpPairTower where
  carrier k := D (k + 1)
  order k := inferInstance
  emb k := glueAA k
  prj k := qAA k
  emb_mono k := fun _ _ hxy => glueAA_monotone k hxy
  prj_mono k := EpFromJoin.upper_monotone (glueAA k) (glueAA_bot k) (h k)
  retraction k := EpFromJoin.upper_map (glueAA k) (h k) (fun _ _ hab => glueAA_reflect k hab)
  deflation k := EpFromJoin.map_upper_le (glueAA k) (glueAA_bot k) (h k)

-- [D-2224] fTower_carrier
@[simp] theorem fTower_carrier (h : ∀ k, GlueAAJoinPreserving k) (k : ℕ) :
    (fTower h).carrier k = D (k + 1) := rfl

-- [D-2225] fTower_emb
@[simp] theorem fTower_emb (h : ∀ k, GlueAAJoinPreserving k) (k : ℕ) :
    (fTower h).emb k = glueAA k := rfl

end GlueAAEpPartner
