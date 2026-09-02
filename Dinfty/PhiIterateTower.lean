import Dinfty.FTowerTripointed

open GluingTowerLibrary SierpinskiApplication

-- [D-2310] §The-genuine-iterate-tower
open scoped Classical

namespace PhiIterateTower

open GlueAAJoin GlueAAEpPartner FTowerTripointed PhiTriFunctor PhiTriTower GenContinuity

-- [D-2311] §Tripointed-ep-pairs-between-consecutive-levels
-- [D-2312] TriEP
structure TriEP (k : ℕ) where
  emb : D k → D (k + 1)
  prj : D (k + 1) → D k
  emb_mono : Monotone emb
  prj_mono : Monotone prj
  retraction : ∀ x, prj (emb x) = x
  deflation : ∀ z, emb (prj z) ≤ z
  emb_bot : emb ⊥ = ⊥
  emb_mid : emb (dMid k) = dMid (k + 1)
  emb_top : emb ⊤ = ⊤

namespace TriEP

variable {k : ℕ} (E : TriEP k)

-- [D-2313] prj_bot
theorem prj_bot : E.prj (⊥ : D (k + 1)) = ⊥ := by
  rw [← E.emb_bot, E.retraction]

-- [D-2314] prj_mid
theorem prj_mid : E.prj (dMid (k + 1)) = dMid k := by
  rw [← E.emb_mid, E.retraction]

-- [D-2315] prj_top
theorem prj_top : E.prj (⊤ : D (k + 1)) = ⊤ := by
  rw [← E.emb_top, E.retraction]

-- [D-2316] §The-two-End-actions
-- [D-2317] endUpFun
noncomputable def endUpFun (h : EndP (D k)) : EndP (D (k + 1)) :=
  ⟨fun x => E.emb (h (E.prj x)),
    fun _ _ hxy => E.emb_mono (h.monotone (E.prj_mono hxy))⟩

-- [D-2318] endUpFun_mono
theorem endUpFun_mono : Monotone E.endUpFun := by
  intro h h' hh
  rw [OrderHom.le_def]
  intro x
  exact E.emb_mono (OrderHom.le_def.mp hh (E.prj x))

-- [D-2319] endDownFun
noncomputable def endDownFun (h : EndP (D (k + 1))) : EndP (D k) :=
  ⟨fun x => E.prj (h (E.emb x)),
    fun _ _ hxy => E.prj_mono (h.monotone (E.emb_mono hxy))⟩

-- [D-2320] endDownFun_mono
theorem endDownFun_mono : Monotone E.endDownFun := by
  intro h h' hh
  rw [OrderHom.le_def]
  intro x
  exact E.prj_mono (OrderHom.le_def.mp hh (E.emb x))

-- [D-2321] endUp
noncomputable def endUp : TowerHom k (k + 1) where
  toFun := ⟨E.endUpFun, E.endUpFun_mono⟩
  map_bot := by
    ext x
    show E.emb ((⊥ : EndP (D k)) (E.prj x)) = (⊥ : EndP (D (k + 1))) x
    rw [endPBot_apply, endPBot_apply, E.emb_bot]
  map_mark := by
    ext x
    show E.emb ((markedPt k) (E.prj x)) = (markedPt (k + 1)) x
    rw [markedPt_apply, markedPt_apply, E.emb_mid]
  map_top := by
    ext x
    show E.emb ((⊤ : EndP (D k)) (E.prj x)) = (⊤ : EndP (D (k + 1))) x
    rw [endPTop_apply, endPTop_apply, E.emb_top]

-- [D-2322] endDown
noncomputable def endDown : TowerHom (k + 1) k where
  toFun := ⟨E.endDownFun, E.endDownFun_mono⟩
  map_bot := by
    ext x
    show E.prj ((⊥ : EndP (D (k + 1))) (E.emb x)) = (⊥ : EndP (D k)) x
    rw [endPBot_apply, endPBot_apply, E.prj_bot]
  map_mark := by
    ext x
    show E.prj ((markedPt (k + 1)) (E.emb x)) = (markedPt k) x
    rw [markedPt_apply, markedPt_apply, E.prj_mid]
  map_top := by
    ext x
    show E.prj ((⊤ : EndP (D (k + 1))) (E.emb x)) = (⊤ : EndP (D k)) x
    rw [endPTop_apply, endPTop_apply, E.prj_top]

-- [D-2323] §The-two-composites-before
-- [D-2324] endDown_endUp
theorem endDown_endUp : (E.endDown.comp E.endUp).toFun = (TriHom.id (markedPt k)).toFun := by
  ext h x
  show E.prj (E.emb (h (E.prj (E.emb x)))) = h x
  rw [E.retraction, E.retraction]

-- [D-2325] endUp_endDown_le
theorem endUp_endDown_le :
    (E.endUp.comp E.endDown).toFun ≤ (TriHom.id (markedPt (k + 1))).toFun := by
  intro h
  rw [OrderHom.le_def]
  intro y
  show E.emb (E.prj (h (E.emb (E.prj y)))) ≤ h y
  exact le_trans (E.deflation _) (h.monotone (E.deflation y))

end TriEP

-- [D-2326] §is-monotone-in-its-morphism-argument
-- [D-2327] phiTower_le_of_le
theorem phiTower_le_of_le {k k' : ℕ} {f g : TowerHom k k'} (h : f.toFun ≤ g.toFun)
    (x : D (k + 1)) : phiTowerD f x ≤ phiTowerD g x :=
  leGlueGen_canon (markedPt k') ((D_marked_point_nondegenerate k').1)
    ((D_marked_point_nondegenerate k').2.1) ((D_marked_point_nondegenerate k').2.2)
    (baseMapGen_leGlueGen_of_le (markedPt k') h x.1)

-- [D-2328] phiTower_congr
theorem phiTower_congr {k k' : ℕ} {f g : TowerHom k k'} (h : f.toFun = g.toFun)
    (x : D (k + 1)) : phiTowerD f x = phiTowerD g x := by
  refine Subtype.ext ?_
  show canonGen (markedPt k') (baseMapGen f.toFun x.1)
    = canonGen (markedPt k') (baseMapGen g.toFun x.1)
  rw [h]

-- [D-2329] §The-step
section Step

variable {k : ℕ} (E : TriEP k)

-- [D-2330] step_retraction
theorem step_retraction (z : D (k + 1)) :
    phiTowerD E.endDown (phiTowerD E.endUp z) = z := by
  have hc := phiTower_comp E.endUp E.endDown
  have h1 : phiTowerD (E.endDown.comp E.endUp) z = phiTowerD E.endDown (phiTowerD E.endUp z) := by
    show phiTower (E.endDown.comp E.endUp) z = _
    rw [hc]
    rfl
  rw [← h1, phiTower_congr E.endDown_endUp z]
  show phiTower (TriHom.id (markedPt k)) z = z
  rw [phiTower_id k]
  rfl

-- [D-2331] step_deflation
theorem step_deflation (z : D (k + 2)) :
    phiTowerD E.endUp (phiTowerD E.endDown z) ≤ z := by
  have hc := phiTower_comp E.endDown E.endUp
  have h1 : phiTowerD (E.endUp.comp E.endDown) z = phiTowerD E.endUp (phiTowerD E.endDown z) := by
    show phiTower (E.endUp.comp E.endDown) z = _
    rw [hc]
    rfl
  have h2 : phiTowerD (E.endUp.comp E.endDown) z
      ≤ phiTowerD (TriHom.id (markedPt (k + 1))) z :=
    phiTower_le_of_le E.endUp_endDown_le z
  have h3 : phiTowerD (TriHom.id (markedPt (k + 1))) z = z := by
    show phiTower (TriHom.id (markedPt (k + 1))) z = z
    rw [phiTower_id (k + 1)]
    rfl
  rw [← h1]
  exact le_of_le_of_eq h2 h3

-- [D-2332] phiStep
noncomputable def phiStep : TriEP (k + 1) where
  emb := phiTowerD E.endUp
  prj := phiTowerD E.endDown
  emb_mono := fun _ _ h => phiTower_monotone E.endUp h
  prj_mono := fun _ _ h => phiTower_monotone E.endDown h
  retraction := step_retraction E
  deflation := step_deflation E
  emb_bot := by
    rw [PhiTriTower.bot_succ_eq k, PhiTriTower.bot_succ_eq (k + 1)]
    exact phiTower_triBot E.endUp
  emb_mid := by
    rw [PhiTriTower.dMid_succ_eq k, PhiTriTower.dMid_succ_eq (k + 1)]
    exact phiTower_triMark E.endUp
  emb_top := by
    rw [PhiTriTower.top_succ_eq k, PhiTriTower.top_succ_eq (k + 1)]
    exact phiTower_triTop E.endUp

end Step

-- [D-2333] §The-base-and-the-tower
-- [D-2334] baseEP
noncomputable def baseEP : TriEP 1 where
  emb := glueAA 0
  prj := qAA 0
  emb_mono := fun _ _ h => glueAA_monotone 0 h
  prj_mono := EpFromJoin.upper_monotone (glueAA 0) (GlueAAEpPartner.glueAA_bot 0)
    (glueAAJoinPreserving 0)
  retraction := qAA_glueAA 0
  deflation := EpFromJoin.map_upper_le (glueAA 0) (GlueAAEpPartner.glueAA_bot 0)
    (glueAAJoinPreserving 0)
  emb_bot := GlueAAEpPartner.glueAA_bot 0
  emb_mid := glueAA_mid 0
  emb_top := glueAA_top 0

-- [D-2335] iter
noncomputable def iter : (n : ℕ) → TriEP (n + 1)
  | 0 => baseEP
  | n + 1 => phiStep (iter n)

-- [D-2336] phiTowerEP
noncomputable def phiTowerEP : EpPairTower where
  carrier n := D (n + 1)
  order n := inferInstance
  emb n := (iter n).emb
  prj n := (iter n).prj
  emb_mono n := (iter n).emb_mono
  prj_mono n := (iter n).prj_mono
  retraction n := (iter n).retraction
  deflation n := (iter n).deflation

-- [D-2337] phiTowerEP_carrier
@[simp] theorem phiTowerEP_carrier (n : ℕ) : phiTowerEP.carrier n = D (n + 1) := rfl

-- [D-2338] phiTowerEP_emb
@[simp] theorem phiTowerEP_emb (n : ℕ) : phiTowerEP.emb n = (iter n).emb := rfl

-- [D-2339] emb_succ
theorem emb_succ (n : ℕ) : (iter (n + 1)).emb = phiTowerD (iter n).endUp := rfl

-- [D-2340] prj_succ
theorem prj_succ (n : ℕ) : (iter (n + 1)).prj = phiTowerD (iter n).endDown := rfl

-- [D-2341] emb_tripointed
theorem emb_tripointed (n : ℕ) :
    (iter n).emb (⊥ : D (n + 1)) = ⊥
      ∧ (iter n).emb (dMid (n + 1)) = dMid (n + 2)
      ∧ (iter n).emb (⊤ : D (n + 1)) = ⊤ :=
  ⟨(iter n).emb_bot, (iter n).emb_mid, (iter n).emb_top⟩

end PhiIterateTower
