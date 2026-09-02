import Dinfty.PhiTriTower

open GluingTowerLibrary SierpinskiApplication

-- [D-2109] §The-obstruction-is-one-directional-acts
universe u

namespace ProjectionTripointed

open PhiTriFunctor PhiTriTower GenContinuity

attribute [local instance 2000] endPDecidableEq

-- [D-2110] §The-projection-is-tripointed
-- [D-2111] pEndPHom
noncomputable def pEndPHom (k : ℕ) : EndP (D (k + 1)) →o EndP (D k) :=
  ⟨pEndP k, pEndP_monotone k⟩

-- [D-2112] pEndPHom_apply
@[simp] theorem pEndPHom_apply (k : ℕ) (g : EndP (D (k + 1))) :
    pEndPHom k g = pEndP k g := rfl

-- [D-2113] pEndP_markedPt
theorem pEndP_markedPt (k : ℕ) : pEndP k (markedPt (k + 1)) = markedPt k := by
  ext x
  show pD k ((markedPt (k + 1)) (iotaD k x)) = dMid k
  rw [markedPt_apply]
  exact pD_dMid_succ k

-- [D-2114] pTri
noncomputable def pTri (k : ℕ) : TowerHom (k + 1) k where
  toFun := pEndPHom k
  map_bot := pEndP_bot k
  map_mark := pEndP_markedPt k
  map_top := pEndP_top k

-- [D-2115] pTri_toFun
@[simp] theorem pTri_toFun (k : ℕ) (g : EndP (D (k + 1))) :
    (pTri k).toFun g = pEndP k g := rfl

-- [D-2116] §The-embedding-is-not
-- [D-2117] iotaEndP_top_ne_top
theorem iotaEndP_top_ne_top (k : ℕ) :
    iotaEndP k (⊤ : EndP (D k)) ≠ (⊤ : EndP (D (k + 1))) := by
  intro h
  have h1 := congrArg (fun f : EndP (D (k + 1)) => f (⊥ : D (k + 1))) h
  exact iotaD_ne_top k _ h1

-- [D-2118] no_towerHom_iotaEndP
theorem no_towerHom_iotaEndP (k : ℕ) (f : TowerHom k (k + 1)) :
    (f.toFun : EndP (D k) → EndP (D (k + 1))) ≠ iotaEndP k := by
  intro h
  exact iotaEndP_top_ne_top k (h ▸ f.map_top)

-- [D-2119] §applied-to-the-projection
-- [D-2120] phiP
noncomputable def phiP (k : ℕ) : D (k + 2) → D (k + 1) := phiTowerD (pTri k)

-- [D-2121] phiP_val
@[simp] theorem phiP_val (k : ℕ) (x : D (k + 2)) :
    (phiP k x).1 = canonGen (markedPt k) (baseMapGen (pEndPHom k) x.1) := rfl

-- [D-2122] phiP_monotone
theorem phiP_monotone (k : ℕ) : Monotone (phiP k) := fun _ _ h =>
  phiTower_monotone (pTri k) h

-- [D-2123] §Values-on-the-three-copies
-- [D-2124] phiP_tagA
theorem phiP_tagA (k : ℕ) (g : EndP (D (k + 1))) (h) :
    phiP k ⟨Sum.inl g, h⟩ = ⟨Sum.inl (pEndP k g), rfl⟩ :=
  Subtype.ext rfl

-- [D-2125] phiP_bot
theorem phiP_bot (k : ℕ) : phiP k (⊥ : D (k + 2)) = (⊥ : D (k + 1)) := by
  rw [bot_succ_eq (k + 1), bot_succ_eq k]
  exact phiTower_triBot (pTri k)

-- [D-2126] phiP_mid
theorem phiP_mid (k : ℕ) : phiP k (dMid (k + 2)) = dMid (k + 1) := by
  rw [dMid_succ_eq (k + 1), dMid_succ_eq k]
  exact phiTower_triMark (pTri k)

-- [D-2127] phiP_top
theorem phiP_top (k : ℕ) : phiP k (⊤ : D (k + 2)) = (⊤ : D (k + 1)) := by
  rw [top_succ_eq (k + 1), top_succ_eq k]
  exact phiTower_triTop (pTri k)

-- [D-2128] §The-retraction-p-glueAA-id
-- [D-2129] pEndP_liftGenM
set_option maxHeartbeats 4000000 in
theorem pEndP_liftGenM (k : ℕ) (f : EndP (D k)) :
    pEndP k (liftGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
      bot_ne_top_of_nontrivial f) = f := by
  ext x
  show pGenM (dMid k) ((liftGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
    bot_ne_top_of_nontrivial f) (iotaGenM (dMid k) x)) = f x
  by_cases hft : (⊤ : EndP (D k)) ≤ f
  · have hf : f = (⊤ : EndP (D k)) := top_le_iff.mp hft
    subst hf
    rw [liftGenM_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial]
    simp only [endPTop_apply]
    exact pGenM_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial
  · rw [liftGenM_apply_iotaGenM_of_not_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
      bot_ne_top_of_nontrivial hft x]
    exact pGenM_section (dMid k) (f x)

-- [D-2130] pEndP_iotaEndPGenM
theorem pEndP_iotaEndPGenM (k : ℕ) (f : EndP (D k)) :
    pEndP k (iotaEndPGenM (L := D k) (dMid_ne_bot k) (dMid_ne_top k)
      bot_ne_top_of_nontrivial f) = f :=
  pEndP_iotaEndP k f

-- [D-2131] phiP_glueAA
set_option maxHeartbeats 4000000 in
theorem phiP_glueAA (k : ℕ) (x : D (k + 1)) : phiP k (glueAA k x) = x := by
  refine Subtype.ext ?_
  obtain ⟨xv, hxv⟩ := x
  have hstrip : ∀ v : GlueBaseGen (EndP (D (k + 1))),
      canonGen (markedPt k) (baseMapGen (pTri k).toFun (canonGen (markedPt (k + 1)) v))
        = canonGen (markedPt k) (baseMapGen (pTri k).toFun v) :=
    fun v => canonGen_baseMapGen_canon (pTri k) (markedPt_ne_bot (k + 1))
      (markedPt_ne_bot k) (D_marked_point_nondegenerate k).2.2 v
  rcases xv with f | f | f
  · show Sum.inl (pEndP k (iotaEndPGenM (L := D k) (dMid_ne_bot k)
        (dMid_ne_top k) bot_ne_top_of_nontrivial f)) = Sum.inl f
    rw [pEndP_iotaEndPGenM k f]
  · show canonGen (markedPt k) (baseMapGen (pTri k).toFun
      (canonGen (markedPt (k + 1)) (Sum.inr (Sum.inl (liftGenM (L := D k) (dMid_ne_bot k)
        (dMid_ne_top k) bot_ne_top_of_nontrivial f))))) = Sum.inr (Sum.inl f)
    rw [hstrip]
    show canonGen (markedPt k) (Sum.inr (Sum.inl (pEndP k (liftGenM (L := D k)
      (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial f))))
        = Sum.inr (Sum.inl f)
    rw [pEndP_liftGenM k f]
    exact hxv
  · show canonGen (markedPt k) (baseMapGen (pTri k).toFun
      (canonGen (markedPt (k + 1)) (Sum.inr (Sum.inr (liftGenM (L := D k) (dMid_ne_bot k)
        (dMid_ne_top k) bot_ne_top_of_nontrivial f))))) = Sum.inr (Sum.inr f)
    rw [hstrip]
    show canonGen (markedPt k) (Sum.inr (Sum.inr (pEndP k (liftGenM (L := D k)
      (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial f))))
        = Sum.inr (Sum.inr f)
    rw [pEndP_liftGenM k f]
    exact hxv

-- [D-2132] §But-it-is-not-an-ep-pair-the-deflation-fails
-- [D-2133] constHom_iotaD_top_ne_bot
theorem constHom_iotaD_top_ne_bot (k : ℕ) :
    (constHom (iotaD k (⊤ : D k)) : EndP (D (k + 1))) ≠ ⊥ := by
  intro h
  have h2 : iotaD k (⊤ : D k) = (⊥ : D (k + 1)) :=
    congrArg (fun f : EndP (D (k + 1)) => f (⊥ : D (k + 1))) h
  have h3 : iotaD k (dMid k) ≤ iotaD k (⊤ : D k) := iotaD_monotone k le_top
  rw [h2] at h3
  exact dMid_ne_bot (k + 1) (le_bot_iff.mp h3)

-- [D-2134] constHom_iotaD_top_ne_top
theorem constHom_iotaD_top_ne_top (k : ℕ) :
    (constHom (iotaD k (⊤ : D k)) : EndP (D (k + 1))) ≠ ⊤ := fun h =>
  iotaD_ne_top k (⊤ : D k)
    (congrArg (fun f : EndP (D (k + 1)) => f (⊥ : D (k + 1))) h)

-- [D-2135] pEndP_constHom_iotaD_top
theorem pEndP_constHom_iotaD_top (k : ℕ) :
    pEndP k (constHom (iotaD k (⊤ : D k))) = (⊤ : EndP (D k)) := by
  ext x
  show pD k (iotaD k (⊤ : D k)) = (⊤ : EndP (D k)) x
  rw [pD_iotaD, endPTop_apply]

-- [D-2136] not_glueAA_phiP_deflation
set_option maxHeartbeats 4000000 in

theorem not_glueAA_phiP_deflation (k : ℕ) :
    ¬ ∀ z : D (k + 2), glueAA k (phiP k z) ≤ z := by
  intro hdefl
  obtain ⟨c, hc⟩ : ∃ c : EndP (D (k + 1)), c = constHom (iotaD k (⊤ : D k)) := ⟨_, rfl⟩
  have hne : c ≠ ⊥ := by rw [hc]; exact constHom_iotaD_top_ne_bot k
  have hct : c ≠ ⊤ := by rw [hc]; exact constHom_iotaD_top_ne_top k
  have hpc : pEndP k c = (⊤ : EndP (D k)) := by rw [hc]; exact pEndP_constHom_iotaD_top k
  have hbt : (⊥ : EndP (D k)) ≠ ⊤ := (D_marked_point_nondegenerate k).2.2
  have hbt1 : (⊥ : EndP (D (k + 1))) ≠ ⊤ := (D_marked_point_nondegenerate (k + 1)).2.2
  have hz : canonGen (markedPt (k + 1)) (Sum.inr (Sum.inl c)) = Sum.inr (Sum.inl c) := by
    simp only [canonGen]
    rw [if_neg hne]
  have hzt : canonGen (markedPt k) (Sum.inr (Sum.inl (⊤ : EndP (D k))))
      = Sum.inr (Sum.inl (⊤ : EndP (D k))) := by
    simp only [canonGen]
    rw [if_neg (Ne.symm hbt)]
  have hphi : phiP k ⟨Sum.inr (Sum.inl c), hz⟩
      = (⟨Sum.inr (Sum.inl (⊤ : EndP (D k))), hzt⟩ : D (k + 1)) := by
    refine Subtype.ext ?_
    show canonGen (markedPt k) (Sum.inr (Sum.inl (pEndP k c))) = _
    rw [hpc]
    exact hzt
  have hglue : (glueAA k (⟨Sum.inr (Sum.inl (⊤ : EndP (D k))), hzt⟩ : D (k + 1))).1
      = Sum.inr (Sum.inl (⊤ : EndP (D (k + 1)))) := by
    show canonGen (markedPt (k + 1)) (Sum.inr (Sum.inl (liftGenM (L := D k)
      (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial (⊤ : EndP (D k))))) = _
    rw [liftGenM_top (L := D k) (dMid_ne_bot k) (dMid_ne_top k) bot_ne_top_of_nontrivial]
    simp only [canonGen]
    split_ifs with hcon
    · exact absurd hcon.symm hbt1
    · rfl
  have hle := hdefl ⟨Sum.inr (Sum.inl c), hz⟩
  rw [hphi] at hle
  have hraw : leGlueGen (markedPt (k + 1))
      ((glueAA k (⟨Sum.inr (Sum.inl (⊤ : EndP (D k))), hzt⟩ : D (k + 1))).1)
      (Sum.inr (Sum.inl c)) := hle
  rw [hglue] at hraw
  have hle2 : (⊤ : EndP (D (k + 1))) ≤ c :=
    (leGlue_tagB_tagB_iffGen (markedPt (k + 1)) _ _ hct (Ne.symm hbt1)).mp hraw
  rw [hc] at hle2
  exact iotaD_ne_top k (⊤ : D k)
    (top_le_iff.mp (OrderHom.le_def.mp hle2 (⊥ : D (k + 1))))

end ProjectionTripointed
