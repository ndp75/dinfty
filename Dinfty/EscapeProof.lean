import Dinfty.QAAExplicit

open GluingTowerLibrary SierpinskiApplication

-- [D-2609] §Theorem-ESCAPE-holds-for-the-rebuilt
namespace EscapeProof

open PhiIterateTower PhiBilimit GlueTag GenContinuity QAAExplicit FTowerTripointed

attribute [-instance] OrderHom.instDecidableEqOfForall

-- [D-2610] §Small-facts-about-the-tower-s-copy-A-inclusion
-- [D-2611] botD_val
theorem botD_val (k : ℕ) : ((⊥ : D (k + 1)) : D (k + 1)).1 = Sum.inl (⊥ : EndP (D k)) := by
  rw [PhiTriTower.bot_succ_eq k]
  rfl

-- [D-2612] iotaD_eq_bot_iff
theorem iotaD_eq_bot_iff (k : ℕ) (c : D k) : iotaD k c = (⊥ : D (k + 1)) ↔ c = ⊥ := by
  have hbotval := botD_val k
  have hcst : (⊥ : EndP (D k)) = constHom (⊥ : D k) := by ext x; rfl
  constructor
  · intro h
    have h1 : (Sum.inl (constHom c) : GlueBaseGen (EndP (D k))) = Sum.inl ⊥ := by
      rw [← hbotval]
      exact congrArg Subtype.val h
    exact constHom_injective ((Sum.inl.inj h1).trans hcst)
  · intro h
    refine Subtype.ext ?_
    rw [hbotval, h]
    exact congrArg Sum.inl hcst.symm

-- [D-2613] dMid_le_of_not_tagA
theorem dMid_le_of_not_tagA {k : ℕ} (y : D (k + 1)) (h : ∀ f, y.1 ≠ Sum.inl f) :
    dMid (k + 1) ≤ y := by
  have hd : (dMid (k + 1) : D (k + 1)).1 = Sum.inl (markedPt k) := by
    rw [PhiTriTower.dMid_succ_eq k]
    rfl
  show leGlueGen (markedPt k) (dMid (k + 1)).1 y.1
  rw [hd]
  refine ⟨Sum.inl (markedPt k), self_mem_occsGen _ _, y.1, self_mem_occsGen _ _, ?_⟩
  rcases hy : y.1 with f | f | f
  · exact absurd hy (h f)
  · exact le_refl _
  · trivial

-- [D-2614] §The-key-inequality
-- [D-2615] eq_bot_of_glueAA_le
set_option maxHeartbeats 1000000 in
theorem eq_bot_of_glueAA_le {y : D 1} {a : EndP (D 1)}
    (hle : glueAA 0 y ≤ glueA (markedPt 1) a)
    (hstrict : a (⊥ : D 1) = (⊥ : D 1))
    (hval : ∀ w : D 1, w ≠ (⊥ : D 1) → a w = y) : y = (⊥ : D 1) := by
  have hBC : (∀ f : EndP (D 0), y.1 ≠ Sum.inl f) → False := by
    intro hA
    have hmid : dMid 1 ≤ y := dMid_le_of_not_tagA y hA
    have h2 : dMid 2 ≤ glueA (markedPt 1) a :=
      le_trans (le_trans (le_of_eq (glueAA_mid 0).symm) (glueAA_monotone 0 hmid)) hle
    have hd2 : (dMid 2 : D 2).1 = Sum.inl (markedPt 1) := by
      rw [PhiTriTower.dMid_succ_eq 1]
      rfl
    have h4 : leGlueGen (markedPt 1) (Sum.inl (markedPt 1)) (Sum.inl a) := by
      have h5 : leGlueGen (markedPt 1) (dMid 2 : D 2).1 (Sum.inl a) := h2
      rwa [hd2] at h5
    have h3 : markedPt 1 ≤ a :=
      (leGlueGen_tagA_tagA_iff (markedPt 1) (D_marked_point_nondegenerate 1).1 _ _).mp h4
    have h6 : (markedPt 1) (⊥ : D 1) ≤ a (⊥ : D 1) := h3 (⊥ : D 1)
    rw [hstrict] at h6
    exact dMid_ne_bot 1 (le_antisymm h6 bot_le)
  rcases hy : y.1 with f | f | f
  ·
    have hyA : y = glueA (markedPt 0) f := Subtype.ext hy
    have hstep : glueAA 0 y = glueA (markedPt 1) (iotaEndP 0 f) := by
      rw [hyA]; exact GlueAAJoin.glueAA_glueA 0 f
    have hpay : iotaEndP 0 f ≤ a := by
      rw [hstep] at hle
      exact (leGlueGen_tagA_tagA_iff (markedPt 1) (D_marked_point_nondegenerate 1).1 _ _).mp hle
    have hfb : f (⊥ : D 0) = ⊥ := by
      have h1 : iotaD 0 (f (pD 0 (⊥ : D 1))) ≤ a (⊥ : D 1) := hpay (⊥ : D 1)
      rw [pD_bot 0, hstrict] at h1
      exact (iotaD_eq_bot_iff 0 _).mp (le_antisymm h1 bot_le)
    have hoff : ∀ u : D 0, u ≠ (⊥ : D 0) → f u = f (⊥ : D 0) := by
      intro u hu
      have hiu : iotaD 0 u ≠ (⊥ : D 1) := fun hc => hu ((iotaD_eq_bot_iff 0 u).mp hc)
      have h1 : iotaD 0 (f (pD 0 (iotaD 0 u))) ≤ a (iotaD 0 u) := hpay (iotaD 0 u)
      rw [pD_iotaD, hval _ hiu, hyA] at h1
      have h1u : leGlueGen (markedPt 0) (Sum.inl (constHom (f u))) (Sum.inl f) := h1
      have h2 : constHom (f u) ≤ f :=
        (leGlueGen_tagA_tagA_iff (markedPt 0) (D_marked_point_nondegenerate 0).1 _ _).mp h1u
      exact le_antisymm (h2 (⊥ : D 0)) (f.monotone bot_le)
    have hfbot : f = ⊥ := by
      refine OrderHom.ext _ _ (funext (fun u => ?_))
      rcases eq_or_ne u (⊥ : D 0) with hu | hu
      · rw [hu, hfb]; rfl
      · rw [hoff u hu, hfb]; rfl
    refine Subtype.ext ?_
    rw [hy, hfbot]
    exact (botD_val 0).symm
  · exact (hBC (fun g hg => by rw [hy] at hg; simp at hg)).elim
  · exact (hBC (fun g hg => by rw [hy] at hg; simp at hg)).elim

-- [D-2616] §and-the-theorem
-- [D-2617] fix_level_succ
theorem fix_level_succ {x : B} (hx : SigmaRebuild.ifsS.sigmaA x = x) (n : ℕ) :
    (x.1 (n + 1)).1 = Sum.inl ((PhiCocone.projEndDown n).toFun (SigmaRebuild.strictConst x)) := by
  have h1 : ((SigmaRebuild.ifsS.sigmaA x).1 (n + 1)).1 = (x.1 (n + 1)).1 :=
    congrArg (fun z : B => (z.1 (n + 1)).1) hx
  rw [← h1]
  exact InternalIFSInstance.pLeg_val n (SigmaRebuild.strictConst x)

-- [D-2618] level_zero_eq_bot
theorem level_zero_eq_bot {x : B} (hx : SigmaRebuild.ifsS.sigmaA x = x) :
    x.1 0 = (⊥ : D 1) := by
  refine eq_bot_of_glueAA_le (a := (PhiCocone.projEndDown 0).toFun (SigmaRebuild.strictConst x))
    ?_ (projEndDown_strictConst_bot 0 x) (fun w hw => projEndDown_strictConst_ne 0 x hw)
  have hq : GlueAAEpPartner.qAA 0 (x.1 1) = x.1 0 := x.2 0
  have hd : glueAA 0 (x.1 0) ≤ x.1 1 := by
    have h := QAAExplicit.glueAA_qAA_le 0 (x.1 1)
    rwa [hq] at h
  have he : x.1 1 = glueA (markedPt 1)
      ((PhiCocone.projEndDown 0).toFun (SigmaRebuild.strictConst x)) :=
    Subtype.ext (fix_level_succ hx 0)
  rwa [he] at hd

-- [D-2619] eq_bot_of_fix
theorem eq_bot_of_fix {x : B} (hx : SigmaRebuild.ifsS.sigmaA x = x) : x = (⊥ : B) := by
  refine Subtype.ext (funext (fun n => ?_))
  induction n with
  | zero => exact level_zero_eq_bot hx
  | succ n ih =>
      have hpay : (PhiCocone.projEndDown n).toFun (SigmaRebuild.strictConst x)
          = (⊥ : EndP (D (n + 1))) := by
        refine OrderHom.ext _ _ (funext (fun w => ?_))
        rcases eq_or_ne w (⊥ : D (n + 1)) with hw | hw
        · rw [hw, projEndDown_strictConst_bot n x]; rfl
        · rw [projEndDown_strictConst_ne n x hw, ih]; rfl
      refine Subtype.ext ?_
      rw [fix_level_succ hx n, hpay]
      exact (botD_val (n + 1)).symm

-- [D-2620] fix_sigmaA
theorem fix_sigmaA : Fix SigmaRebuild.ifsS.sigmaA = {(⊥ : B)} := by
  ext x
  constructor
  · intro hx
    exact eq_bot_of_fix hx
  · intro hx
    rw [hx]
    exact SigmaRebuild.sigmaA_bot

end EscapeProof
