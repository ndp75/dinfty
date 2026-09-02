import Dinfty.EscapeProof
import Dinfty.GasketNotOpen

open GluingTowerLibrary SierpinskiApplication

-- [D-2779] §What-forces-on-any-internal-IFS
open Metric Set

namespace Gasket

-- [D-2780] §1-A-contraction-has-at-most-one-fixed-point
-- [D-2781] eq_of_contract_fixed
theorem eq_of_contract_fixed (c : E) {x y : E}
    (hx : contract c x = x) (hy : contract c y = y) : x = y := by
  have h := (contract_lipschitz c).dist_le_mul x y
  rw [hx, hy] at h
  have h2 : dist x y ≤ 2⁻¹ * dist x y := by
    refine h.trans (le_of_eq ?_)
    norm_num
  have h3 : (0 : ℝ) ≤ dist x y := dist_nonneg
  have h4 : dist x y = 0 := le_antisymm (by linarith) h3
  exact dist_eq_zero.1 h4

-- [D-2782] fA_fixed_unique
theorem fA_fixed_unique {x : Gamma} (hx : fA x = x) : x = gA := by
  refine Subtype.ext ?_
  exact eq_of_contract_fixed cA (congrArg Subtype.val hx) contract_vA

-- [D-2783] fB_fixed_unique
theorem fB_fixed_unique {x : Gamma} (hx : fB x = x) : x = gB := by
  refine Subtype.ext ?_
  exact eq_of_contract_fixed cB (congrArg Subtype.val hx) contract_vB

-- [D-2784] fC_fixed_unique
theorem fC_fixed_unique {x : Gamma} (hx : fC x = x) : x = gC := by
  refine Subtype.ext ?_
  exact eq_of_contract_fixed cC (congrArg Subtype.val hx) contract_vC

-- [D-2785] §2-Equivariance-is-constant-on-fixed-point-sets
section Equivariance

variable {X : Type*} {rho : X → Gamma}

-- [D-2786] rho_eq_gA
theorem rho_eq_gA {sA : X → X} (h : ∀ x, rho (sA x) = fA (rho x))
    {p : X} (hp : sA p = p) : rho p = gA :=
  fA_fixed_unique (by rw [← h p, hp])

-- [D-2787] rho_eq_gB
theorem rho_eq_gB {sB : X → X} (h : ∀ x, rho (sB x) = fB (rho x))
    {p : X} (hp : sB p = p) : rho p = gB :=
  fB_fixed_unique (by rw [← h p, hp])

-- [D-2788] rho_eq_gC
theorem rho_eq_gC {sC : X → X} (h : ∀ x, rho (sC x) = fC (rho x))
    {p : X} (hp : sC p = p) : rho p = gC :=
  fC_fixed_unique (by rw [← h p, hp])

-- [D-2789] no_shared_fix_AB
theorem no_shared_fix_AB {sA sB : X → X}
    (hA : ∀ x, rho (sA x) = fA (rho x)) (hB : ∀ x, rho (sB x) = fB (rho x))
    {p : X} (hpA : sA p = p) (hpB : sB p = p) : False :=
  gA_ne_gB ((rho_eq_gA hA hpA).symm.trans (rho_eq_gB hB hpB))

-- [D-2790] no_shared_fix_AC
theorem no_shared_fix_AC {sA sC : X → X}
    (hA : ∀ x, rho (sA x) = fA (rho x)) (hC : ∀ x, rho (sC x) = fC (rho x))
    {p : X} (hpA : sA p = p) (hpC : sC p = p) : False :=
  gA_ne_gC ((rho_eq_gA hA hpA).symm.trans (rho_eq_gC hC hpC))

-- [D-2791] no_shared_fix_BC
theorem no_shared_fix_BC {sB sC : X → X}
    (hB : ∀ x, rho (sB x) = fB (rho x)) (hC : ∀ x, rho (sC x) = fC (rho x))
    {p : X} (hpB : sB p = p) (hpC : sC p = p) : False :=
  gB_ne_gC ((rho_eq_gB hB hpB).symm.trans (rho_eq_gC hC hpC))

end Equivariance

-- [D-2792] §3-Running-the-test-on-SigmaRebuild-ifsS
open PhiIterateTower PhiBilimit GlueTag InternalIFSInstance SigmaRebuild

-- [D-2793] tagB_bot_eq_mark
theorem tagB_bot_eq_mark :
    tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)
      = tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB := by
  refine Subtype.ext ?_
  show (if (⊥ : ScottEndP B) = ⊥ then (Sum.inl markedB : GlueBaseGen (ScottEndP B))
        else Sum.inr (Sum.inl (⊥ : ScottEndP B))) = Sum.inl markedB
  rw [if_pos rfl]

-- [D-2794] tagC_bot_eq_top
theorem tagC_bot_eq_top :
    tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)
      = tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊤ : ScottEndP B) := by
  refine Subtype.ext ?_
  show (if (⊥ : ScottEndP B) = ⊥ then (Sum.inl ⊤ : GlueBaseGen (ScottEndP B))
        else if (⊥ : ScottEndP B) = markedB then Sum.inr (Sum.inl ⊤)
        else Sum.inr (Sum.inr (⊥ : ScottEndP B))) = Sum.inl ⊤
  rw [if_pos rfl]

-- [D-2795] sec_tagA_bot
theorem sec_tagA_bot :
    sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)) = (⊥ : B) := by
  have h := SigmaRebuild.sigmaA_bot
  show sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)) = (⊥ : B)
  rw [← strictConst_bot]
  exact h

-- [D-2796] ifsS_sigmaB_bot
theorem ifsS_sigmaB_bot :
    ifsS.sigmaB (⊥ : B)
      = sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB) := by
  show sec (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst (⊥ : B))) = _
  rw [strictConst_bot, tagB_bot_eq_mark]

-- [D-2797] ifsS_sigmaC_bot
theorem ifsS_sigmaC_bot :
    ifsS.sigmaC (⊥ : B)
      = sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊤ : ScottEndP B)) := by
  show sec (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst (⊥ : B))) = _
  rw [strictConst_bot, tagC_bot_eq_top]

-- [D-2798] ifsS_sigmaB_bot_ne
theorem ifsS_sigmaB_bot_ne : ifsS.sigmaB (⊥ : B) ≠ (⊥ : B) := by
  intro hc
  rw [ifsS_sigmaB_bot, ← sec_tagA_bot] at hc
  exact markedB_ne_bot
    (tagPt_injective 0 markedB markedB_ne_bot endPB_bot_ne_top (sec_injective hc))

-- [D-2799] ifsS_sigmaC_bot_ne
theorem ifsS_sigmaC_bot_ne : ifsS.sigmaC (⊥ : B) ≠ (⊥ : B) := by
  intro hc
  rw [ifsS_sigmaC_bot, ← sec_tagA_bot] at hc
  exact endPB_bot_ne_top
    (tagPt_injective 0 markedB markedB_ne_bot endPB_bot_ne_top (sec_injective hc)).symm

-- [D-2800] bot_not_mem_fix_B
theorem bot_not_mem_fix_B : (⊥ : B) ∉ Fix ifsS.sigmaB := ifsS_sigmaB_bot_ne

-- [D-2801] bot_not_mem_fix_C
theorem bot_not_mem_fix_C : (⊥ : B) ∉ Fix ifsS.sigmaC := ifsS_sigmaC_bot_ne

-- [D-2802] ifsS_fix_disjoint_AB
theorem ifsS_fix_disjoint_AB : Disjoint (Fix ifsS.sigmaA) (Fix ifsS.sigmaB) := by
  rw [Set.disjoint_left]
  intro a ha hb
  rw [EscapeProof.fix_sigmaA] at ha
  rw [show a = (⊥ : B) from ha] at hb
  exact bot_not_mem_fix_B hb

-- [D-2803] ifsS_fix_disjoint_AC
theorem ifsS_fix_disjoint_AC : Disjoint (Fix ifsS.sigmaA) (Fix ifsS.sigmaC) := by
  rw [Set.disjoint_left]
  intro a ha hc
  rw [EscapeProof.fix_sigmaA] at ha
  rw [show a = (⊥ : B) from ha] at hc
  exact bot_not_mem_fix_C hc

-- [D-2804] rho_bot
theorem rho_bot {rho : B → Gamma}
    (hA : ∀ x, rho (ifsS.sigmaA x) = fA (rho x)) : rho (⊥ : B) = gA :=
  rho_eq_gA hA SigmaRebuild.sigmaA_bot

end Gasket
