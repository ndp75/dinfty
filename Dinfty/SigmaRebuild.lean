import Dinfty.InternalIFSInstance

open GluingTowerLibrary SierpinskiApplication

-- [D-2565] §Rebuilding-and-a-correction-about-what-ESCAPE
universe u

namespace SigmaRebuild

open PhiIterateTower PhiBilimit GlueTag GenContinuity InternalIFSInstance

attribute [-instance] OrderHom.instDecidableEqOfForall

-- [D-2566] §The-correction-stated-and-proved
section Uniqueness

variable {Dinf Gamma : Type u} [TopologicalSpace Gamma] {K : CoreIFS Dinf Gamma}

-- [D-2567] base_pin_of_mem
theorem base_pin_of_mem {b : K.Core} (hb : b ∈ Fix K.sigmaA)
    (hFixA : Subsingleton (Fix K.fA)) {rho1 rho2 : K.Core → Gamma}
    (hA1 : ∀ x, rho1 (K.sigmaA x) = K.fA (rho1 x))
    (hA2 : ∀ x, rho2 (K.sigmaA x) = K.fA (rho2 x)) :
    rho1 b = rho2 b := by
  have h1 : rho1 b ∈ Fix K.fA := equivariant_fixes_fix hA1 hb
  have h2 : rho2 b ∈ Fix K.fA := equivariant_fixes_fix hA2 hb
  exact congrArg Subtype.val (hFixA.elim (⟨rho1 b, h1⟩ : Fix K.fA) ⟨rho2 b, h2⟩)

-- [D-2568] theoremA_unique_of_mem
theorem theoremA_unique_of_mem [T2Space Gamma] {b : K.Core} (hb : b ∈ Fix K.sigmaA)
    (hFixA : Subsingleton (Fix K.fA)) (hDense : Dense (Orbit (K := K) b))
    {rho1 rho2 : K.Core → Gamma}
    (hc1 : Continuous rho1) (hc2 : Continuous rho2)
    (hA1 : ∀ x, rho1 (K.sigmaA x) = K.fA (rho1 x))
    (hB1 : ∀ x, rho1 (K.sigmaB x) = K.fB (rho1 x))
    (hC1 : ∀ x, rho1 (K.sigmaC x) = K.fC (rho1 x))
    (hA2 : ∀ x, rho2 (K.sigmaA x) = K.fA (rho2 x))
    (hB2 : ∀ x, rho2 (K.sigmaB x) = K.fB (rho2 x))
    (hC2 : ∀ x, rho2 (K.sigmaC x) = K.fC (rho2 x)) :
    rho1 = rho2 :=
  Continuous.ext_on hDense hc1 hc2
    (agree_on_orbit hA1 hB1 hC1 hA2 hB2 hC2 (base_pin_of_mem hb hFixA hA1 hA2))

end Uniqueness

-- [D-2569] §The-strict-constant
-- [D-2570] strictFun
noncomputable def strictFun (c : B) (y : B) : B := @ite B (y = ⊥) (Classical.dec _) ⊥ c

-- [D-2571] strictFun_bot_case
theorem strictFun_bot_case {c y : B} (hy : y = ⊥) : strictFun c y = ⊥ := by
  simp only [strictFun]
  rw [if_pos hy]

-- [D-2572] strictFun_ne_case
theorem strictFun_ne_case {c y : B} (hy : y ≠ ⊥) : strictFun c y = c := by
  simp only [strictFun]
  rw [if_neg hy]

-- [D-2573] strictFun_mono
theorem strictFun_mono (c : B) : Monotone (strictFun c) := by
  intro y y' h
  by_cases hy : y = ⊥
  · rw [strictFun_bot_case hy]
    exact bot_le
  · have hy' : y' ≠ ⊥ := fun hc => hy (le_antisymm (hc ▸ h) bot_le)
    rw [strictFun_ne_case hy, strictFun_ne_case hy']

-- [D-2574] strictFun_scott
theorem strictFun_scott (c : B) : ScottContinuous (strictFun c) := by
  intro S hne hdir a ha
  by_cases ha0 : a = ⊥
  · have hS : ∀ s ∈ S, s = ⊥ := fun s hs => le_antisymm (ha0 ▸ ha.1 hs) bot_le
    rw [strictFun_bot_case ha0]
    constructor
    · rintro _ ⟨s, hs, rfl⟩
      rw [strictFun_bot_case (hS s hs)]
    · intro w _
      exact bot_le
  · obtain ⟨s0, hs0, hs0b⟩ : ∃ s ∈ S, s ≠ ⊥ := by
      by_contra hc
      push_neg at hc
      exact ha0 (le_antisymm (ha.2 (fun s hs => le_of_eq (hc s hs))) bot_le)
    rw [strictFun_ne_case ha0]
    constructor
    · rintro _ ⟨s, hs, rfl⟩
      by_cases hsb : s = ⊥
      · rw [strictFun_bot_case hsb]; exact bot_le
      · rw [strictFun_ne_case hsb]
    · intro w hw
      have hle := hw ⟨s0, hs0, rfl⟩
      rwa [strictFun_ne_case hs0b] at hle

-- [D-2575] strictConst
noncomputable def strictConst (c : B) : ScottEndP B :=
  ⟨⟨strictFun c, strictFun_mono c⟩, strictFun_scott c⟩

-- [D-2576] strictConst_apply
@[simp] theorem strictConst_apply (c y : B) : (strictConst c).1 y = strictFun c y := rfl

-- [D-2577] topB_ne_bot
theorem topB_ne_bot : topB ≠ (⊥ : B) := fun h => botB_ne_topB h.symm

-- [D-2578] strictConst_injective
theorem strictConst_injective : Function.Injective strictConst := by
  intro x y h
  have h1 : strictFun x topB = strictFun y topB :=
    congrArg (fun F : ScottEndP B => F.1 topB) h
  rwa [strictFun_ne_case (c := x) topB_ne_bot, strictFun_ne_case (c := y) topB_ne_bot] at h1

-- [D-2579] strictConst_bot
theorem strictConst_bot : strictConst (⊥ : B) = (⊥ : ScottEndP B) := by
  refine Subtype.ext (OrderHom.ext _ _ (funext (fun y => ?_)))
  show strictFun (⊥ : B) y = (⊥ : ScottEndP B).1 y
  by_cases hy : y = ⊥
  · rw [strictFun_bot_case hy]; rfl
  · rw [strictFun_ne_case hy]; rfl

-- [D-2580] §The-rebuilt-internal-IFS
-- [D-2581] ifsS
noncomputable def ifsS : InternalIFS B where
  sigmaA x := sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x))
  sigmaB x := sec (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x))
  sigmaC x := sec (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst x))

-- [D-2582] sigmaS_inj
private theorem sigmaS_inj (t : ℕ) {x y : B}
    (h : sec (tagPt t markedB markedB_ne_bot endPB_bot_ne_top (strictConst x))
       = sec (tagPt t markedB markedB_ne_bot endPB_bot_ne_top (strictConst y))) : x = y :=
  strictConst_injective
    (tagPt_injective t markedB markedB_ne_bot endPB_bot_ne_top (sec_injective h))

-- [D-2583] sigmaA_injective
theorem sigmaA_injective : Function.Injective ifsS.sigmaA := fun _ _ h => sigmaS_inj 0 h
-- [D-2584] sigmaB_injective
theorem sigmaB_injective : Function.Injective ifsS.sigmaB := fun _ _ h => sigmaS_inj 1 h
-- [D-2585] sigmaC_injective
theorem sigmaC_injective : Function.Injective ifsS.sigmaC := fun _ _ h => sigmaS_inj 2 h

-- [D-2586] §is-still-fixed-and-the-marked-point-is-not
-- [D-2587] sigmaA_bot
theorem sigmaA_bot : ifsS.sigmaA (⊥ : B) = ⊥ := by
  show sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (strictConst (⊥ : B))) = ⊥
  rw [strictConst_bot]
  exact InternalIFSInstance.sigmaA_bot

-- [D-2588] bot_mem_fix
theorem bot_mem_fix : (⊥ : B) ∈ Fix ifsS.sigmaA := sigmaA_bot

-- [D-2589] sigmaA_mid_ne
theorem sigmaA_mid_ne : ifsS.sigmaA midB ≠ midB := by
  intro h
  have h1 : (ifsS.sigmaA midB).1 1 = midB.1 1 := congrArg (fun z : B => z.1 1) h
  have hval : (Sum.inl ((PhiCocone.projEndDown 0).toFun (strictConst midB))
      : GlueBaseGen (EndP (D 1))) = Sum.inl (markedPt 1) := by
    rw [← InternalIFSInstance.pLeg_val 0 (strictConst midB)]
    exact congrArg Subtype.val h1
  have hpay : (PhiCocone.projEndDown 0).toFun (strictConst midB) = markedPt 1 :=
    Sum.inl.inj hval
  have hbot : ((PhiCocone.projEndDown 0).toFun (strictConst midB)) (⊥ : D 1)
      = (markedPt 1) (⊥ : D 1) := congrArg (fun f : EndP (D 1) => f (⊥ : D 1)) hpay
  have hlhs : ((PhiCocone.projEndDown 0).toFun (strictConst midB)) (⊥ : D 1) = (⊥ : D 1) := by
    show ((strictConst midB).1 (phiTowerEP.ins 0 (⊥ : D 1))).1 0 = (⊥ : D 1)
    rw [ins_bot 0]
    show (strictFun midB botB).1 0 = (⊥ : D 1)
    rw [strictFun_bot_case (rfl : botB = ⊥)]
    rfl
  rw [hlhs] at hbot
  exact dMid_ne_bot 1 hbot.symm

-- [D-2590] mid_not_mem_fix
theorem mid_not_mem_fix : midB ∉ Fix ifsS.sigmaA := sigmaA_mid_ne

end SigmaRebuild
