import Dinfty.GlueAAJoin

open GluingTowerLibrary SierpinskiApplication

-- [D-2282] §Obstruction-T-does-not-apply-to-the-F-tower
open scoped Classical

namespace FTowerTripointed

open GlueAAJoin GlueAAEpPartner

-- [D-2283] §The-embedding-is-tripointed
-- [D-2284] iotaEndP_markedPt
theorem iotaEndP_markedPt (k : ℕ) : iotaEndP k (markedPt k) = markedPt (k + 1) :=
  iotaEndPGenM_constHom (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
    bot_ne_top_of_nontrivial (dMid k)

-- [D-2285] glueAA_mid
theorem glueAA_mid (k : ℕ) : glueAA k (dMid (k + 1)) = dMid (k + 2) := by
  rw [CopyBCStructure.dMid_eq_glueA k, glueAA_glueA, iotaEndP_markedPt k,
    ← CopyBCStructure.dMid_eq_glueA (k + 1)]

-- [D-2286] top_eq_glueC
theorem top_eq_glueC (k : ℕ) :
    (⊤ : D (k + 1)) = glueC (markedPt k) (⊤ : EndP (D k))
      (Ne.symm (D_marked_point_nondegenerate k).2.2)
      (Ne.symm (markedPt_ne_top k)) := by
  rw [PhiTriTower.top_succ_eq k]
  exact Subtype.ext rfl

-- [D-2287] glueAA_top
set_option maxHeartbeats 4000000 in
theorem glueAA_top (k : ℕ) : glueAA k (⊤ : D (k + 1)) = (⊤ : D (k + 2)) := by
  rw [top_eq_glueC k, glueAA_glueC, top_eq_glueC (k + 1)]
  exact Subtype.ext (congrArg (fun a : EndP (D (k + 1)) => Sum.inr (Sum.inr a))
    (liftT_top k))

-- [D-2288] glueAA_tripointed
theorem glueAA_tripointed (k : ℕ) :
    glueAA k (⊥ : D (k + 1)) = ⊥
      ∧ glueAA k (dMid (k + 1)) = dMid (k + 2)
      ∧ glueAA k (⊤ : D (k + 1)) = ⊤ :=
  ⟨GlueAAEpPartner.glueAA_bot k, glueAA_mid k, glueAA_top k⟩

-- [D-2289] iotaD_not_top_but_glueAA_is
theorem iotaD_not_top_but_glueAA_is (k : ℕ) :
    (∀ x : D k, iotaD k x ≠ (⊤ : D (k + 1)))
      ∧ glueAA k (⊤ : D (k + 1)) = (⊤ : D (k + 2)) :=
  ⟨iotaD_ne_top k, glueAA_top k⟩

-- [D-2290] §hence-so-is-the-projection
-- [D-2291] qAA_glueAA
theorem qAA_glueAA (k : ℕ) (x : D (k + 1)) : qAA k (glueAA k x) = x :=
  EpFromJoin.upper_map (glueAA k) (glueAAJoinPreserving k)
    (fun _ _ h => glueAA_reflect k h) x

-- [D-2292] qAA_bot
theorem qAA_bot (k : ℕ) : qAA k (⊥ : D (k + 2)) = (⊥ : D (k + 1)) := by
  rw [← GlueAAEpPartner.glueAA_bot k, qAA_glueAA]

-- [D-2293] qAA_mid
theorem qAA_mid (k : ℕ) : qAA k (dMid (k + 2)) = dMid (k + 1) := by
  rw [← glueAA_mid k, qAA_glueAA]

-- [D-2294] qAA_top
theorem qAA_top (k : ℕ) : qAA k (⊤ : D (k + 2)) = (⊤ : D (k + 1)) := by
  rw [← glueAA_top k, qAA_glueAA]

-- [D-2295] §The-three-points-assemble-along-the-F-tower
-- [D-2296] botF
set_option maxHeartbeats 4000000 in
noncomputable def botF : fTowerReal.Bilim :=
  ⟨fun k => (⊥ : D (k + 1)), fun k => qAA_bot k⟩

-- [D-2297] midF
set_option maxHeartbeats 4000000 in
noncomputable def midF : fTowerReal.Bilim :=
  ⟨fun k => dMid (k + 1), fun k => qAA_mid k⟩

-- [D-2298] topF
set_option maxHeartbeats 4000000 in
noncomputable def topF : fTowerReal.Bilim :=
  ⟨fun k => (⊤ : D (k + 1)), fun k => qAA_top k⟩

-- [D-2299] botF_le
theorem botF_le (y : fTowerReal.Bilim) : botF ≤ y := by
  intro k
  show (⊥ : D (k + 1)) ≤ y.1 k
  exact bot_le

-- [D-2300] le_topF
theorem le_topF (y : fTowerReal.Bilim) : y ≤ topF := by
  intro k
  exact @le_top (D (k + 1)) _ _ (y.1 k)

-- [D-2301] inst-OrderBot
noncomputable instance : OrderBot fTowerReal.Bilim where
  bot := botF
  bot_le := botF_le

-- [D-2302] inst-OrderTop
noncomputable instance : OrderTop fTowerReal.Bilim where
  top := topF
  le_top := le_topF

-- [D-2303] inst-BoundedOrder
noncomputable instance : BoundedOrder fTowerReal.Bilim := {}

-- [D-2304] midF_ne_botF
theorem midF_ne_botF : midF ≠ botF := by
  intro h
  exact dMid_ne_bot 1 (congrArg (fun z : fTowerReal.Bilim => z.1 0) h)

-- [D-2305] midF_ne_topF
theorem midF_ne_topF : midF ≠ topF := by
  intro h
  exact dMid_ne_top 1 (congrArg (fun z : fTowerReal.Bilim => z.1 0) h)

-- [D-2306] bilim_tripointed
theorem bilim_tripointed :
    (∀ y : fTowerReal.Bilim, botF ≤ y) ∧ (∀ y : fTowerReal.Bilim, y ≤ topF)
      ∧ midF ≠ botF ∧ midF ≠ topF :=
  ⟨botF_le, le_topF, midF_ne_botF, midF_ne_topF⟩

-- [D-2307] §But-the-F-tower-is-not-the-iterate-tower
-- [D-2308] glueAA_top_ne_iotaD_top
theorem glueAA_top_ne_iotaD_top (k : ℕ) :
    glueAA k (⊤ : D (k + 1)) ≠ iotaD (k + 1) (⊤ : D (k + 1)) := by
  rw [glueAA_top k]
  exact fun h => iotaD_ne_top (k + 1) (⊤ : D (k + 1)) h.symm

-- [D-2309] fTower_not_phi_iterate
theorem fTower_not_phi_iterate (k : ℕ) :
    ∃ w : D (k + 1),
      glueAA k ((⊤ : EndP (D (k + 1))) w) ≠ iotaD (k + 1) ((⊤ : EndP (D (k + 1))) w) :=
  ⟨⊥, glueAA_top_ne_iotaD_top k⟩

end FTowerTripointed
