import Dinfty.PhiSurjective
import Dinfty.CopyCHigh
import Dinfty.InternalIFSInstance
import Dinfty.EscapeAnalysis
import Dinfty.SigmaRebuild
import Dinfty.QAAExplicit
import Dinfty.EscapeProof
import Dinfty.GasketCoreIFS
import Dinfty.GasketNotOpen
import Dinfty.CodeB
import Dinfty.RhoContinuity
import Dinfty.AddressConvergence
import Dinfty.BilimitGap
import Dinfty.CopyIdeal
import Dinfty.SeamTriangle
import Dinfty.StageRigidity
import Dinfty.PhiStagePipe
import Dinfty.StageEmbedding
import Dinfty.EmbDImage
import Dinfty.LevelEmbNotGeneric
import Dinfty.EmbTagwise
import Dinfty.SeamFixed
import Dinfty.PatchedEmbedding
import Dinfty.StageCofinal
import Dinfty.AtomlessBilimit
import Dinfty.StageCover
import Dinfty.CanonicalChain
import Dinfty.SeamCut
import Dinfty.IdealInvariant

-- [D-3601] §Dinfty-Verify-the-single-entry-point
open GluingTowerLibrary SierpinskiApplication

section PillarA

-- [D-3602] example-phiB
noncomputable example : PhiBilimit.phiB ≃o PhiIterateTower.phiTowerEP.Bilim :=
  PhiSurjective.theoremA_orderIso

end PillarA

section PillarB

-- [D-3603] example-Subsingleton
example : Subsingleton (DInfty ≃o DInfty) := CopyCHigh.colimit_compat

-- [D-3604] example-Subsingleton
example : Subsingleton (DBilimit ≃o DBilimit) := CopyCHigh.DBilimit_rigid

end PillarB

section InternalIFS

-- [D-3605] example-InternalIFS
noncomputable example : InternalIFS PhiBilimit.B := InternalIFSInstance.ifsB

-- [D-3606] example-Injective
example : Function.Injective InternalIFSInstance.ifsB.sigmaA :=
  InternalIFSInstance.sigmaA_injective
-- [D-3607] example-Injective
example : Function.Injective InternalIFSInstance.ifsB.sigmaB :=
  InternalIFSInstance.sigmaB_injective
-- [D-3608] example-Injective
example : Function.Injective InternalIFSInstance.ifsB.sigmaC :=
  InternalIFSInstance.sigmaC_injective

end InternalIFS

section Escape

-- [D-3609] example-B
example (b : PhiBilimit.B) : Fix InternalIFSInstance.ifsB.sigmaA ≠ {b} :=
  EscapeAnalysis.fix_sigmaA_not_singleton b

-- [D-3610] example-sigmaA
example : InternalIFSInstance.ifsB.sigmaA PhiBilimit.midB = PhiBilimit.midB :=
  EscapeAnalysis.sigmaA_mid

-- [D-3611] example-sigmaB
example : InternalIFSInstance.ifsB.sigmaB (⊥ : PhiBilimit.B) = PhiBilimit.midB :=
  EscapeAnalysis.sigmaB_bot

end Escape

section Rebuilt

-- [D-3612] example-InternalIFS
noncomputable example : InternalIFS PhiBilimit.B := SigmaRebuild.ifsS

-- [D-3613] example-Injective
example : Function.Injective SigmaRebuild.ifsS.sigmaA := SigmaRebuild.sigmaA_injective
-- [D-3614] example-Injective
example : Function.Injective SigmaRebuild.ifsS.sigmaB := SigmaRebuild.sigmaB_injective
-- [D-3615] example-Injective
example : Function.Injective SigmaRebuild.ifsS.sigmaC := SigmaRebuild.sigmaC_injective

-- [D-3616] example-sigmaA
example : SigmaRebuild.ifsS.sigmaA (⊥ : PhiBilimit.B) = ⊥ := SigmaRebuild.sigmaA_bot
-- [D-3617] example-midB
example : PhiBilimit.midB ∉ Fix SigmaRebuild.ifsS.sigmaA := SigmaRebuild.mid_not_mem_fix

-- [D-3618] example-True
example : True := trivial

end Rebuilt

section Projection

-- [D-3619] example-D
example (k : ℕ) (z : D (k + 2)) :
    IsGreatest {y : D (k + 1) | glueAA k y ≤ z} (GlueAAEpPartner.qAA k z) :=
  QAAExplicit.qAA_isGreatest k z

-- [D-3620] example-D
example (k : ℕ) (y : D (k + 1)) (z : D (k + 2)) :
    glueAA k y ≤ z ↔ y ≤ GlueAAEpPartner.qAA k z :=
  QAAExplicit.glueAA_le_iff_le_qAA k y z

-- [D-3621] example-prj
example : PhiIterateTower.phiTowerEP.prj 0 = GlueAAEpPartner.qAA 0 :=
  QAAExplicit.prj_zero_eq

end Projection

section EscapeHolds

-- [D-3622] example-Fix
example : Fix SigmaRebuild.ifsS.sigmaA = {(⊥ : PhiBilimit.B)} := EscapeProof.fix_sigmaA

end EscapeHolds

section Gasket

open Topology

-- [D-3623] §is-a-definition-not-a-parameter
-- [D-3624] example-gasketSet
example : Gasket.gasketSet
    = (Gasket.contract Gasket.cA '' Gasket.gasketSet)
      ∪ (Gasket.contract Gasket.cB '' Gasket.gasketSet)
      ∪ (Gasket.contract Gasket.cC '' Gasket.gasketSet) := Gasket.gasketSet_eq

-- [D-3625] example-Nontrivial
example : Nontrivial Gasket.Gamma := Gasket.gamma_nontrivial

-- [D-3626] §The-coding-map-A-B-C
-- [D-3627] example-Continuous
example : Continuous Gasket.codeGamma := Gasket.continuous_codeGamma

-- [D-3628] example-Surjective
example : Function.Surjective Gasket.codeGamma := Gasket.codeGamma_surjective

-- [D-3629] example
example (w : ℕ → Fin 3) :
    Gasket.codeGamma (Gasket.cons 0 w) = Gasket.fA (Gasket.codeGamma w) :=
  Gasket.codeGamma_cons_zero w

-- [D-3630] example
example (r : (ℕ → Fin 3) → Gasket.Gamma)
    (hA : ∀ w, r (Gasket.cons 0 w) = Gasket.fA (r w))
    (hB : ∀ w, r (Gasket.cons 1 w) = Gasket.fB (r w))
    (hC : ∀ w, r (Gasket.cons 2 w) = Gasket.fC (r w)) :
    r = Gasket.codeGamma := Gasket.coding_unique r hA hB hC

-- [D-3631] example-IsQuotientMap
example : IsQuotientMap Gasket.codeGamma := Gasket.isQuotientMap_codeGamma

-- [D-3632] example
example : ¬ IsOpenMap Gasket.codeGamma := Gasket.notOpen

-- [D-3633] example-Gamma
example : ¬ IsOpen {x : Gasket.Gamma | (x : Gasket.E)
    ∈ Gasket.contract Gasket.cA '' Gasket.gasketSet} := Gasket.not_isOpen_imageA

end Gasket

section Link

-- [D-3634] §The-address-map-into-B
-- [D-3635] example-Fin
example (j : Fin 3) (w : ℕ → Fin 3) :
    CodeB.codeB (Gasket.cons j w) = CodeB.sig j (CodeB.codeB w) := CodeB.codeB_cons j w

-- [D-3636] example-Injective
example : Function.Injective CodeB.codeB := CodeB.codeB_injective

-- [D-3637] example-Surjective
example : Function.Surjective CodeB.rho := CodeB.rho_surjective

-- [D-3638] example
example (w : ℕ → Fin 3) :
    CodeB.rho ⟨CodeB.codeB w, CodeB.codeB_mem_attractor w⟩ = Gasket.codeGamma w :=
  CodeB.rho_codeB w

-- [D-3639] example-Fin
example (j j' : Fin 3) (h : j ≠ j') (x y : PhiBilimit.B) :
    CodeB.sig j x ≠ CodeB.sig j' y := CodeB.sig_ne_of_ne j j' h x y

-- [D-3640] example-Disjoint
example : Disjoint (Fix SigmaRebuild.ifsS.sigmaA) (Fix SigmaRebuild.ifsS.sigmaB) :=
  Gasket.ifsS_fix_disjoint_AB

-- [D-3641] example-B
example {rho : PhiBilimit.B → Gasket.Gamma}
    (hA : ∀ x, rho (SigmaRebuild.ifsS.sigmaA x) = Gasket.fA (rho x)) :
    rho (⊥ : PhiBilimit.B) = Gasket.gA := Gasket.rho_bot hA

end Link

section Continuity

-- [D-3642] §Which-topology-can-be-continuous
-- [D-3643] example-rho
example : CodeB.rho ⟨(⊥ : PhiBilimit.B), CodeB.bot_mem_attractor⟩ = Gasket.gA :=
  RhoContinuity.rho_bot_eq

-- [D-3644] example-TopologicalSpace
example (τ : TopologicalSpace CodeB.Attractor)
    (hup : RhoContinuity.UpwardClosedOpens τ)
    (hcont : @Continuous CodeB.Attractor Gasket.Gamma τ _ CodeB.rho) : False :=
  RhoContinuity.no_continuous_rho_of_upwardClosed τ hup hcont

-- [D-3645] example-AddressesConverge
example : RhoContinuity.AddressesConverge := CodeB.addressesConverge

-- [D-3646] example-ChainContinuous
example : RhoContinuity.ChainContinuous CodeB.rho := CodeB.rho_chainContinuous

-- [D-3647] example-Attractor
example (r : CodeB.Attractor → Gasket.Gamma)
    (hA : ∀ b : CodeB.Attractor,
      r ⟨CodeB.sig 0 (b : PhiBilimit.B), CodeB.mapsTo_sig 0 b.2⟩ = Gasket.fA (r b))
    (hB : ∀ b : CodeB.Attractor,
      r ⟨CodeB.sig 1 (b : PhiBilimit.B), CodeB.mapsTo_sig 1 b.2⟩ = Gasket.fB (r b))
    (hC : ∀ b : CodeB.Attractor,
      r ⟨CodeB.sig 2 (b : PhiBilimit.B), CodeB.mapsTo_sig 2 b.2⟩ = Gasket.fC (r b)) :
    r = CodeB.rho := CodeB.rho_unique r hA hB hC

-- [D-3648] example-Fin
example (j : Fin 3) (x y : PhiBilimit.B) : CodeB.sig j x ≤ CodeB.sig j y ↔ x ≤ y :=
  CodeB.sig_le_iff j x y

end Continuity

section TwoObjects

-- [D-3649] §Theorem-A-and-Theorem-B-are-about-DIFFERENT
-- [D-3650] example
example : ¬ BilimitGap.OmegaCompact topSeq := BilimitGap.topSeq_not_omegaCompact

-- [D-3651] example-OmegaCompact
example : BilimitGap.OmegaCompact (PhiBilimit.topB : PhiBilimit.B) := BilimitGap.topB_omegaCompact

-- [D-3652] example
example : ¬ Nonempty (PhiBilimit.B ≃o DBilimit) := BilimitGap.no_orderIso

-- [D-3753] example
example : ¬ Nonempty (PhiBilimit.B ≃o DInfty) := BilimitGap.no_orderIso_DInfty

-- [D-3653] example
example (k : ℕ) :
    (∀ x : D k, iotaD k x ∈ CopyIdeal.CopyA (markedPt k)
        ∧ iotaD k x ≠ (⊤ : D (k + 1)))
      ∧ glueAA k (⊤ : D (k + 1)) = (⊤ : D (k + 2)) :=
  CopyIdeal.legacy_confined_phi_not k

-- [D-3654] example-B
example (e : PhiBilimit.B ≃o DBilimit) : Subsingleton (PhiBilimit.B ≃o PhiBilimit.B) :=
  BilimitGap.rigid_of_orderIso e

end TwoObjects

-- [D-3655] §Axiom-dependencies
#print axioms PhiSurjective.theoremA_orderIso
#print axioms PhiSurjective.phiSupExists
#print axioms PhiSurjective.phiProjContinuous
#print axioms PhiCoconeLUB.phiCoconeIsLUB
#print axioms PhiCoconeLUB.isColimitCocone

#print axioms InternalIFSInstance.ifsB
#print axioms InternalIFSInstance.sigmaA_injective
#print axioms InternalIFSInstance.sigmaB_injective
#print axioms InternalIFSInstance.sigmaC_injective
#print axioms InternalIFSInstance.sigmaA_bot

#print axioms EscapeAnalysis.sigmaA_mid
#print axioms EscapeAnalysis.sigmaB_bot
#print axioms EscapeAnalysis.fix_sigmaA_not_singleton

#print axioms SigmaRebuild.ifsS
#print axioms SigmaRebuild.sigmaA_bot
#print axioms SigmaRebuild.sigmaA_mid_ne
#print axioms SigmaRebuild.base_pin_of_mem
#print axioms SigmaRebuild.theoremA_unique_of_mem

#print axioms QAAExplicit.qAA_isGreatest
#print axioms QAAExplicit.glueAA_le_iff_le_qAA
#print axioms QAAExplicit.level_zero_isGreatest
#print axioms QAAExplicit.fix_level_zero

#print axioms EscapeProof.fix_sigmaA
#print axioms EscapeProof.eq_bot_of_glueAA_le

#print axioms Gasket.gasketSet_eq
#print axioms Gasket.gamma_nontrivial
#print axioms Gasket.continuous_codeGamma
#print axioms Gasket.codeGamma_surjective
#print axioms Gasket.coding_unique
#print axioms Gasket.isQuotientMap_codeGamma
#print axioms Gasket.addressCoreIFS
#print axioms Gasket.not_isOpen_imageA
#print axioms Gasket.notOpen
#print axioms Gasket.ifsS_fix_disjoint_AB
#print axioms Gasket.rho_bot

#print axioms CodeB.codeB_cons
#print axioms CodeB.sig_ne_of_ne
#print axioms CodeB.codeB_injective
#print axioms CodeB.rho_codeB
#print axioms CodeB.rho_surjective
#print axioms CodeB.attractorEquiv
#print axioms CodeB.sig_le_iff

#print axioms RhoContinuity.rho_bot_eq
#print axioms RhoContinuity.no_continuous_rho_of_upwardClosed
#print axioms RhoContinuity.chainContinuous_of_addressesConverge
#print axioms CodeB.head_le_of_codeB_le
#print axioms CodeB.head_eventually_const
#print axioms CodeB.addressesConverge
#print axioms CodeB.rho_chainContinuous
#print axioms CodeB.rho_unique

#print axioms BilimitGap.topSeq_not_omegaCompact
#print axioms BilimitGap.topB_omegaCompact
#print axioms BilimitGap.no_orderIso
#print axioms BilimitGap.no_orderIso_DInfty
#print axioms BilimitGap.rigid_of_orderIso
#print axioms CopyIdeal.copyA_isLowerSet
#print axioms CopyIdeal.legacy_confined_phi_not

#print axioms CopyCHigh.colimit_compat
#print axioms CopyCHigh.DBilimit_rigid
#print axioms CopyCHigh.firstSlice

#print axioms glue_trans
#print axioms glueGen_trans
#print axioms glueCarPartialOrder
#print axioms glueCarPartialOrderGen

-- [D-3656] §The-seam-triangle
section SeamTriangleCheck

-- [D-3657] example-tagB_bot_eq_mark
example : Gasket.tagB_bot_eq_mark = Gasket.tagB_bot_eq_mark := rfl
-- [D-3658] example-tagC_bot_eq_top
example : Gasket.tagC_bot_eq_top = Gasket.tagC_bot_eq_top := rfl
-- [D-3659] example-tagC_mark_eq_tagB_top
example : SeamTriangle.tagC_mark_eq_tagB_top = SeamTriangle.tagC_mark_eq_tagB_top := rfl

-- [D-3660] example-Seamed
example : SeamTriangle.Seamed SeamTriangle.fseq SeamTriangle.gseq :=
  SeamTriangle.gasket_seamed
-- [D-3661] example-Seamless
example : SeamTriangle.Seamless (fun j : Fin 3 => Gasket.cons j) :=
  SeamTriangle.address_seamless
-- [D-3662] example-Seamless
example : SeamTriangle.Seamless CodeB.sig := SeamTriangle.codeB_seamless
-- [D-3663] example-Fin
example (p : Fin 3 → PhiBilimit.B) : ¬ SeamTriangle.Seamed CodeB.sig p :=
  SeamTriangle.codeB_not_seamed p

-- [D-3664] example-Fin
example (i j : Fin 3) (hij : i ≠ j) :
    Gasket.codeGamma (Gasket.cons i (fun _ => j))
      = Gasket.codeGamma (Gasket.cons j (fun _ => i)) := SeamTriangle.codeGamma_seam i j hij
-- [D-3665] example-Fin
example (i j : Fin 3) (hij : i ≠ j) :
    CodeB.codeB (Gasket.cons i (fun _ => j)) ≠ CodeB.codeB (Gasket.cons j (fun _ => i)) :=
  SeamTriangle.codeB_seam_ne i j hij
-- [D-3666] example
example : ¬ Function.Injective CodeB.rho := SeamTriangle.rho_not_injective

-- [D-3667] example-mid
example : Gasket.mid = ((SeamTriangle.fseq 0 (SeamTriangle.gseq 1) : Gasket.Gamma) : Gasket.E) :=
  SeamTriangle.mid_eq_seam

-- [D-3668] example-Fin
example (j : Fin 3) : Fix (Gasket.cons j) = {(fun _ => j : ℕ → Fin 3)} :=
  SeamTriangle.fix_cons j
-- [D-3669] example-Fin
example (j : Fin 3) :
    Fix (CodeB.sig j) ∩ CodeB.Attractor = {CodeB.codeB (fun _ => j)} :=
  SeamTriangle.fix_sig_inter_attractor j
-- [D-3670] example-FixPoints
example (P : FixPoints Gasket.addressCoreIFS) [FixData P] : False :=
  SeamTriangle.no_fixData_address P

end SeamTriangleCheck

#print axioms SeamTriangle.tagC_mark_eq_tagB_top
#print axioms SeamTriangle.gasket_seamed
#print axioms SeamTriangle.address_seamless
#print axioms SeamTriangle.codeB_seamless
#print axioms SeamTriangle.not_seamed_of_seamless
#print axioms SeamTriangle.fix_disjoint_of_seamless
#print axioms SeamTriangle.codeGamma_seam
#print axioms SeamTriangle.codeB_seam_ne
#print axioms SeamTriangle.rho_not_injective
#print axioms SeamTriangle.mid_eq_seam
#print axioms SeamTriangle.fix_cons
#print axioms SeamTriangle.fix_sig_inter_attractor
#print axioms SeamTriangle.no_fixData_address
#print axioms SeamTriangle.addressSeamedIFS

-- [D-3671] §From-the-copy-A-ideal-to-the-whole
section StageRigidityCheck

-- [D-3672] example-B
example (θ : PhiBilimit.B ≃o PhiBilimit.B)
    (key : ∀ (k : ℕ) (x : PhiIterateTower.phiTowerEP.carrier k),
      θ (EpPairTower.ins PhiIterateTower.phiTowerEP k x)
        = EpPairTower.ins PhiIterateTower.phiTowerEP k x) :
    θ = OrderIso.refl PhiBilimit.B :=
  StageRigidity.eq_refl_of_fixes_stages θ key

-- [D-3673] example-LevelsMaximallyRigid
example : StageRigidity.LevelsMaximallyRigid PhiIterateTower.phiTowerEP :=
  PhiRigidity.levels_maximally_rigid

-- [D-3674] example-PhiStageDefinable
example : PhiRigidity.PhiStageDefinable →
    Subsingleton (PhiBilimit.B ≃o PhiBilimit.B) :=
  PhiRigidity.B_rigid_of_stageDefinable

-- [D-3675] example-D
example (k : ℕ) (x : D k) : glueAA k (iotaD k x) = iotaD (k + 1) (iotaD k x) :=
  PhiRigidity.legacy_subtower k x

-- [D-3676] example-D
example (n : ℕ) (x : D (n + 1)) :
    (PhiIterateTower.iter n).emb (⊤ : D (n + 1)) ≠ iotaD (n + 1) x :=
  PhiRigidity.phi_emb_top_not_legacy n x

end StageRigidityCheck

#print axioms StageRigidity.ins_le_iff
#print axioms StageRigidity.ins_injective
#print axioms StageRigidity.eq_refl_of_fixes_stages
#print axioms StageRigidity.eq_on_stages
#print axioms StageRigidity.eq_refl_of_stageDefinable
#print axioms StageRigidity.rigid_of_stageDefinable
#print axioms PhiRigidity.levels_maximally_rigid
#print axioms PhiRigidity.B_rigid_of_stageDefinable
#print axioms PhiRigidity.legacy_subtower
#print axioms PhiRigidity.phi_emb_top_not_legacy
#print axioms PhiRigidity.pillars_share_one_reduction

-- [D-3677] §The-residue-cleaned
section PhiStagePipeCheck

-- [D-3678] example-D
example (k : ℕ) (a : D (k + 1)) (u : PhiBilimit.B) :
    PhiStagePipe.insD k a ≤ u ↔ a ≤ u.1 k := PhiStagePipe.insD_le_iff k a u

-- [D-3679] example-Set
example (k : ℕ) (S : Set PhiBilimit.B) (z : PhiBilimit.B)
    (hS : ∀ w ∈ S, ∃ y : D (k + 1), PhiStagePipe.insD k y = w) (hz : IsLUB S z) :
    ∃ y : D (k + 1), PhiStagePipe.insD k y = z := PhiStagePipe.stageSupClosed k S z hS hz

-- [D-3680] example-D
example (k : ℕ) (x : D (k + 1)) :
    IsLUB (PhiStagePipe.stageJI k x) (PhiStagePipe.insD k x) :=
  PhiStagePipe.stageJoinRecoverable k x

-- [D-3681] example-B
example (z : PhiBilimit.B) :
    BilimitGap.OmegaCompact z ↔ ∃ (k : ℕ) (y : D (k + 1)), PhiStagePipe.insD k y = z :=
  PhiStagePipe.omegaCompact_iff_stage z

-- [D-3682] example-B
example (θ : PhiBilimit.B ≃o PhiBilimit.B) (k : ℕ) (x : D (k + 1)) :
    ∃ (n : ℕ) (y : D (n + 1)), θ (PhiStagePipe.insD k x) = PhiStagePipe.insD n y :=
  PhiStagePipe.stages_union_preserved θ k x

-- [D-3683] example-B
example (θ : PhiBilimit.B ≃o PhiBilimit.B) (k : ℕ) :
    θ (PhiStagePipe.insD k ⊥) = PhiStagePipe.insD k ⊥ := PhiStagePipe.apply_insD_bot θ k
-- [D-3684] example-B
example (θ : PhiBilimit.B ≃o PhiBilimit.B) (k : ℕ) :
    θ (PhiStagePipe.insD k ⊤) = PhiStagePipe.insD k ⊤ := PhiStagePipe.apply_insD_top θ k

end PhiStagePipeCheck

#print axioms StageRigidity.ins_le_iff'
#print axioms PhiStagePipe.stageSupClosed
#print axioms PhiStagePipe.stageJoinRecoverable
#print axioms PhiStagePipe.insD_omegaCompact
#print axioms PhiStagePipe.exists_stage_of_omegaCompact
#print axioms PhiStagePipe.omegaCompact_iff_stage
#print axioms PhiStagePipe.stages_union_preserved
#print axioms PhiStagePipe.apply_insD_bot
#print axioms PhiStagePipe.apply_insD_top

-- [D-3685] §The-residue-is-level-local
section StageEmbeddingCheck

-- [D-3686] example-B
example (θ : PhiBilimit.B ≃o PhiBilimit.B) (k : ℕ) :
    ∃ m : ℕ, k ≤ m ∧ ∃ f : D (k + 1) → D (m + 1),
      (∀ x, θ (PhiStagePipe.insD k x) = PhiStagePipe.insD m (f x))
        ∧ Monotone f ∧ (∀ a b, f a ≤ f b → a ≤ b)
        ∧ f ⊥ = ⊥ ∧ f ⊤ = ⊤ ∧ (∀ a b, f (a ⊔ b) = f a ⊔ f b) :=
  StageEmbedding.stage_map_exists θ k

-- [D-3687] example-k
example {k m : ℕ} (h : k ≤ m) (a b : D (k + 1)) :
    StageEmbedding.embD h (a ⊔ b) = StageEmbedding.embD h a ⊔ StageEmbedding.embD h b :=
  StageEmbedding.embD_sup h a b

-- [D-3688] example-D
example (k : ℕ) (f : D (k + 1) → D (k + 1)) (hmono : Monotone f)
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b) : f = StageEmbedding.embD (le_refl k) :=
  StageEmbedding.levelEmbUnique_diagonal k f hmono hrefl

-- [D-3689] example-LevelEmbUnique
example : StageEmbedding.LevelEmbUnique →
    Subsingleton (PhiBilimit.B ≃o PhiBilimit.B) :=
  StageEmbedding.B_rigid_of_levelEmbUnique

end StageEmbeddingCheck

#print axioms StageEmbedding.insD_isLUB_pair
#print axioms StageEmbedding.embD_sup
#print axioms StageEmbedding.stage_map_exists
#print axioms StageEmbedding.stage_map_comp
#print axioms StageEmbedding.levelEmbUnique_diagonal
#print axioms StageEmbedding.phiStageDefinable_of_levelEmbUnique
#print axioms StageEmbedding.B_rigid_of_levelEmbUnique

-- [D-3690] §embD-and-the-residue-as-an-image-statement
section EmbDImageCheck

-- [D-3691] example-k
example {k m : ℕ} (h : k ≤ m) (x : D (k + 1)) : EmbDImage.prjD h (StageEmbedding.embD h x) = x :=
  EmbDImage.prjD_embD h x
-- [D-3692] example-k
example {k m : ℕ} (h : k ≤ m) (z : D (m + 1)) :
    StageEmbedding.embD h (EmbDImage.prjD h z) ≤ z := EmbDImage.embD_prjD_le h z

-- [D-3693] example-k
example {k m : ℕ} (h : k ≤ m) (z : D (m + 1)) :
    z ∈ Set.range (StageEmbedding.embD h) ↔ StageEmbedding.embD h (EmbDImage.prjD h z) = z :=
  EmbDImage.mem_range_embD_iff h z

-- [D-3694] example-k
example {k m : ℕ} (h : k ≤ m) : (Set.range (StageEmbedding.embD h)).ncard = Nat.card (D (k + 1)) :=
  EmbDImage.ncard_range_embD h
-- [D-3695] example-k
example {k m : ℕ} (h : k ≤ m) (f : D (k + 1) → D (m + 1))
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b)
    (hsub : Set.range f ⊆ Set.range (StageEmbedding.embD h)) :
    Set.range f = Set.range (StageEmbedding.embD h) := EmbDImage.range_eq_of_subset h f hrefl hsub

-- [D-3696] example-k
example {k m : ℕ} (h : k ≤ m) (f : D (k + 1) → D (m + 1)) (hmono : Monotone f)
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b)
    (hrange : ∀ x, StageEmbedding.embD h (EmbDImage.prjD h (f x)) = f x) :
    f = StageEmbedding.embD h := EmbDImage.eq_embD_of_range_subset h f hmono hrefl hrange

-- [D-3697] example-k
example {k m : ℕ} (h : k ≤ m) : StageEmbedding.embD h (⊥ : D (k + 1)) = (⊥ : D (m + 1)) :=
  EmbDImage.embD_bot h
-- [D-3698] example-k
example {k m : ℕ} (h : k ≤ m) : StageEmbedding.embD h (⊤ : D (k + 1)) = (⊤ : D (m + 1)) :=
  EmbDImage.embD_top h

-- [D-3699] example-LevelImageStableJI
example : EmbDImage.LevelImageStableJI → Subsingleton (PhiBilimit.B ≃o PhiBilimit.B) :=
  EmbDImage.B_rigid_of_levelImageStableJI

end EmbDImageCheck

#print axioms EmbDImage.prjLe_embLe
#print axioms EmbDImage.embLe_prjLe_le
#print axioms EmbDImage.prjD_embD
#print axioms EmbDImage.embD_prjD_le
#print axioms EmbDImage.mem_range_embD_iff
#print axioms EmbDImage.embD_bot
#print axioms EmbDImage.embD_top
#print axioms EmbDImage.ncard_range_embD
#print axioms EmbDImage.range_eq_of_subset
#print axioms EmbDImage.eq_embD_of_range_subset
#print axioms EmbDImage.map_finset_sup
#print axioms EmbDImage.image_stable_of_joinIrred
#print axioms EmbDImage.levelImageStable_of_JI
#print axioms EmbDImage.B_rigid_of_levelImageStableJI
#print axioms EmbDImage.rigidity_finish_line

-- [D-3700] §The-embeddings-are-tagwise-and-copy
section TagwiseCheck

-- [D-3701] example-D
example (n : ℕ) (x : D (n + 2)) :
    ((PhiIterateTower.iter (n + 1)).emb x).1
      = GenContinuity.baseMapGen (PhiIterateTower.iter n).endUp.toFun x.1 :=
  EmbTagwise.emb_succ_val n x

-- [D-3702] example-D
example (n : ℕ) (x : D (n + 2)) :
    CopyHierarchy.copyIdx ((PhiIterateTower.iter (n + 1)).emb x).1
      = CopyHierarchy.copyIdx x.1 :=
  EmbTagwise.emb_succ_copyIdx n x

-- [D-3703] example-D
example (n : ℕ) (z : D (n + 3)) (a : EndP (D (n + 2))) (hz : z.1 = Sum.inl a) :
    z ∈ Set.range ((PhiIterateTower.iter (n + 1)).emb)
      ↔ a ∈ Set.range (PhiIterateTower.iter n).endUpFun :=
  EmbTagwise.range_val_emb_succ_inl n z a hz

-- [D-3704] example-D
example (k : ℕ) (x : D (k + 1)) :
    (∃ a : EndP (D k), x.1 = Sum.inl a) ↔ x ≤ SeamFixed.cSeam k :=
  SeamFixed.mem_copyA_iff_le_cSeam k x

-- [D-3705] example-D
example {k m : ℕ} (f : D (k + 1) → D (m + 1)) (hmono : Monotone f)
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b) (hseam : f (SeamFixed.cSeam k) = SeamFixed.cSeam m)
    (x : D (k + 1)) :
    (∃ a : EndP (D m), (f x).1 = Sum.inl a) ↔ (∃ a : EndP (D k), x.1 = Sum.inl a) :=
  SeamFixed.copyA_preserved f hmono hrefl hseam x

-- [D-3706] example-D
example {k m : ℕ} (f : D (k + 1) → D (m + 1)) (hmono : Monotone f)
    (hseam : f (SeamFixed.cSeam k) ≤ SeamFixed.cSeam m) (x : D (k + 1))
    (hx : ∃ a : EndP (D k), x.1 = Sum.inl a) :
    ∃ a : EndP (D m), (f x).1 = Sum.inl a :=
  SeamFixed.copyA_mapsTo f hmono hseam x hx

end TagwiseCheck

#print axioms EmbTagwise.canonGen_baseMapGen
#print axioms EmbTagwise.phiFun_val_tagwise
#print axioms EmbTagwise.endUpFun_injective
#print axioms EmbTagwise.emb_succ_val
#print axioms EmbTagwise.emb_succ_copyIdx
#print axioms EmbTagwise.mem_range_emb_succ_iff
#print axioms EmbTagwise.range_val_emb_succ_inl
#print axioms self_mem_occsGen
#print axioms SeamFixed.mem_copyA_iff_le_cSeam
#print axioms SeamFixed.copyA_preserved
#print axioms SeamFixed.copyA_mapsTo

-- [D-3707] §Running-the-split-no-generic-proof
section SplitCheck

-- [D-3708] example
example :
    ∃ f g : Fin 3 → Fin 4,
      (Monotone f ∧ (∀ a b, f a ≤ f b → a ≤ b) ∧ f ⊥ = ⊥ ∧ f ⊤ = ⊤
        ∧ ∀ a b, f (a ⊔ b) = f a ⊔ f b)
      ∧ (Monotone g ∧ (∀ a b, g a ≤ g b → a ≤ b) ∧ g ⊥ = ⊥ ∧ g ⊤ = ⊤
        ∧ ∀ a b, g (a ⊔ b) = g a ⊔ g b)
      ∧ f ≠ g :=
  LevelEmbNotGeneric.chain_not_unique

end SplitCheck

#print axioms LevelEmbNotGeneric.chain_not_unique

-- [D-3709] §The-residue-chain-is-REFUTED
section RefutationCheck

-- [D-3710] example-Monotone
example (k : ℕ) : Monotone (PatchedEmbedding.patched k) := PatchedEmbedding.patched_monotone k
-- [D-3711] example-D
example (k : ℕ) (x y : D (k + 1)) :
    PatchedEmbedding.patched k x ≤ PatchedEmbedding.patched k y → x ≤ y :=
  PatchedEmbedding.patched_reflect k x y
-- [D-3712] example-D
example (k : ℕ) (x y : D (k + 1)) :
    PatchedEmbedding.patched k (x ⊔ y)
      = PatchedEmbedding.patched k x ⊔ PatchedEmbedding.patched k y :=
  PatchedEmbedding.patched_sup k x y
-- [D-3713] example-D
example (k : ℕ) {x y : D k} (h : x ⊔ y = ⊤) : x = ⊤ ∨ y = ⊤ :=
  PatchedEmbedding.top_joinIrred k h
-- [D-3714] example
example : ¬ StageEmbedding.LevelEmbUnique := PatchedEmbedding.not_levelEmbUnique
-- [D-3715] example
example : ¬ EmbDImage.LevelImageStableJI := PatchedEmbedding.not_levelImageStableJI

end RefutationCheck

#print axioms PatchedEmbedding.top_joinIrred
#print axioms PatchedEmbedding.patched_monotone
#print axioms PatchedEmbedding.patched_reflect
#print axioms PatchedEmbedding.patched_bot
#print axioms PatchedEmbedding.patched_sup
#print axioms PatchedEmbedding.top_val_two
#print axioms PatchedEmbedding.not_levelEmbUnique
#print axioms PatchedEmbedding.not_levelImageStable
#print axioms PatchedEmbedding.not_levelImageStableJI

-- [D-3716] §The-residue-weakened-cofinally-many-stable
section CofinalCheck

open StageCofinal StageEmbedding PhiIterateTower PhiBilimit EpPairTower

-- [D-3717] example-B
example (θ : B ≃o B) (k : ℕ) :
    ∃ m, k ≤ m ∧ ∃ f : D (k + 1) → D (m + 1), IsStageMap θ k m f :=
  StageCofinal.stage_map_exists' θ k

-- [D-3718] example-B
example (θ : B ≃o B) {k m m' : ℕ} {f : D (k + 1) → D (m + 1)} {f' : D (k + 2) → D (m' + 1)}
    (hf : IsStageMap θ k m f) (hf' : IsStageMap θ (k + 1) m' f')
    (hmm : m ≤ m') (hk : k ≤ k + 1) (x : D (k + 1)) :
    embD hmm (f x) = f' (embD hk x) :=
  StageCofinal.isStageMap_coherent hf hf' hmm hk x

-- [D-3719] example-B
example (θ : B ≃o B) {k : ℕ} {f : D (k + 1) → D (k + 1)} (hf : IsStageMap θ k k f) :
    f = id := hf.diagonal

-- [D-3720] example-PhiStageDefinableCofinal
example : PhiRigidity.PhiStageDefinableCofinal → Subsingleton (B ≃o B) :=
  PhiRigidity.B_rigid_of_cofinal

-- [D-3721] example-PhiStageDefinable
example : PhiRigidity.PhiStageDefinable → PhiRigidity.PhiStageDefinableCofinal :=
  PhiRigidity.phiStageDefinable_cofinal

end CofinalCheck

#print axioms StageRigidity.fixes_stage
#print axioms StageRigidity.fixes_stages_below
#print axioms StageRigidity.eq_refl_of_cofinal_stable
#print axioms StageRigidity.rigid_of_cofinal_stageDefinable
#print axioms StageCofinal.stage_map_exists'
#print axioms StageCofinal.IsStageMap.unique
#print axioms StageCofinal.IsStageMap.push
#print axioms StageCofinal.isStageMap_coherent
#print axioms StageCofinal.IsStageMap.diagonal
#print axioms StageCofinal.IsStageMap.fixes
#print axioms PhiRigidity.phiStageDefinable_cofinal
#print axioms PhiRigidity.eq_id_of_cofinal
#print axioms PhiRigidity.B_rigid_of_cofinal

-- [D-3722] §The-singular-atom-of-a-slice-does-not-reach-B
section AtomCheck

open AtomlessBilimit TowerNoAbsorption PhiIterateTower

-- [D-3723] example-lamD
example (k : ℕ) : lamD (k + 1) = glueA (markedPt k) (spikeHom (lamD k)) :=
  AtomlessBilimit.lamD_succ k

-- [D-3724] example-TriEP
example {k : ℕ} (E : TriEP k) (v : D k) :
    E.endUpFun (spikeHom v) = spikeHom (E.emb v) :=
  AtomlessBilimit.endUpFun_spikeHom E v

-- [D-3725] example
example : (iter 0).emb (lamD 1) ≠ lamD 2 := AtomlessBilimit.base_emb_lamD_ne

-- [D-3726] example
example (k : ℕ) : (iter k).emb (lamD (k + 1)) ≠ lamD (k + 2) :=
  AtomlessBilimit.emb_lamD_ne k

-- [D-3727] example-B
example (a : PhiBilimit.B) : ¬ IsAtom a := AtomlessBilimit.no_isAtom a

end AtomCheck

#print axioms AtomlessBilimit.spikeHom_injective
#print axioms AtomlessBilimit.eq_lamD
#print axioms AtomlessBilimit.lamD_succ
#print axioms AtomlessBilimit.prj_eq_top_iff
#print axioms AtomlessBilimit.endUpFun_spikeHom
#print axioms AtomlessBilimit.emb_succ_glueA
#print axioms AtomlessBilimit.base_emb_lamD_ne
#print axioms AtomlessBilimit.emb_lamD_ne
#print axioms AtomlessBilimit.botB_eq_bot
#print axioms AtomlessBilimit.stage_atom_lt
#print axioms AtomlessBilimit.exists_lt_lt_of_ne_bot
#print axioms AtomlessBilimit.no_isAtom

-- [D-3728] §The-hunt-is-the-117-freedom-invertible
section CoverCheck

open StageCover StageCofinal PatchedEmbedding StageEmbedding PhiIterateTower PhiBilimit PhiStagePipe

-- [D-3729] example-TriEP
example {k : ℕ} (E : TriEP k) (x : D k) : E.endUpFun (constHom x) = constHom (E.emb x) :=
  StageCover.endUpFun_constHom E x

-- [D-3730] example-D
example (k : ℕ) (x : D (k + 1)) :
    (iter (k + 1)).emb (patched k x) = patched (k + 1) ((iter k).emb x) :=
  StageCover.patched_coherent k x

-- [D-3731] example-D
example (m : ℕ) (h : 1 ≤ m) (y : D 2) :
    CopyHierarchy.copyIdx (embD h y).1 = CopyHierarchy.copyIdx y.1 :=
  StageCover.embD_copyIdx m h y

-- [D-3732] example-B
example : ¬ ∃ θ : PhiBilimit.B ≃o PhiBilimit.B,
    ∀ (k : ℕ) (x : D (k + 1)), θ (insD k x) = insD (k + 1) (patched k x) :=
  StageCover.no_patched_automorphism

end CoverCheck

#print axioms StageCover.endUpFun_constHom
#print axioms StageCover.emb_eq_top_iff
#print axioms StageCover.patched_coherent
#print axioms StageCover.embD_copyIdx
#print axioms StageCover.stage_map_covers
#print axioms StageCover.no_patched_automorphism

-- [D-3733] §Splitting-again-the-canonical-chain
section ChainCheck

open CanonicalChain PatchedEmbedding SeamFixed PhiIterateTower PhiBilimit PhiStagePipe

-- [D-3734] example
example (n : ℕ) : (iter (n + 1)).emb (cSeam (n + 1)) = cSeam (n + 2) :=
  CanonicalChain.emb_cSeam_succ n

-- [D-3735] example
example : (iter 0).emb (cSeam 0) ≠ cSeam 1 := CanonicalChain.base_emb_cSeam_ne

-- [D-3736] example-insD
example (n : ℕ) : insD (n + 1) (cSeam (n + 1)) = cSeamB := CanonicalChain.insD_cSeam n

-- [D-3737] example-midB
example : midB < cSeamB := CanonicalChain.midB_lt_cSeamB
-- [D-3738] example-cSeamB
example : cSeamB < (⊤ : PhiBilimit.B) := CanonicalChain.cSeamB_lt_top

-- [D-3739] example-D
example (n : ℕ) (x : D (n + 2)) :
    insD (n + 1) x ≤ cSeamB ↔ ∃ a : EndP (D (n + 1)), x.1 = Sum.inl a :=
  CanonicalChain.le_cSeamB_iff n x

-- [D-3740] example-iotaD
example (k : ℕ) : iotaD k (dMid k) = dMid (k + 1) := CanonicalChain.iotaD_preserves_mid k
-- [D-3741] example-patched
example (k : ℕ) : patched k (cSeam k) ≠ cSeam (k + 1) := CanonicalChain.patched_ne_cSeam k

end ChainCheck

#print axioms CanonicalChain.top_val_succ
#print axioms CanonicalChain.cSeam_ne_top
#print axioms CanonicalChain.insD_emb
#print axioms CanonicalChain.endUpFun_top
#print axioms CanonicalChain.emb_cSeam_succ
#print axioms CanonicalChain.base_emb_cSeam_ne
#print axioms CanonicalChain.insD_cSeam
#print axioms CanonicalChain.midB_lt_cSeamB
#print axioms CanonicalChain.cSeamB_lt_top
#print axioms CanonicalChain.le_cSeamB_iff
#print axioms CanonicalChain.iotaD_preserves_mid
#print axioms CanonicalChain.patched_ne_cSeam

-- [D-3742] §CSeamFixed-structure-settled-decision-NOT
section SeamCutCheck

open SeamCut CanonicalChain SeamFixed PhiIterateTower PhiBilimit

-- [D-3743] example-D
example (k : ℕ) (z : D (k + 1)) :
    cSeam k ≤ z ↔ (z.1 = Sum.inl (⊤ : EndP (D k))
      ∨ z.1 = Sum.inr (Sum.inl (⊤ : EndP (D k)))
      ∨ ∃ c : EndP (D k), z.1 = Sum.inr (Sum.inr c)) :=
  SeamCut.cSeam_le_iff k z

-- [D-3744] example-CSeamFixed
example : CanonicalChain.CSeamFixed
    ↔ ∀ (θ : PhiBilimit.B ≃o PhiBilimit.B) (y : PhiBilimit.B),
        y ≤ cSeamB ↔ θ y ≤ cSeamB :=
  SeamCut.cSeamFixed_iff_ideal_stable

-- [D-3745] example-EndP
example (k : ℕ) (u : EndP (D k)) (hu : u ≠ ⊥) :
    spikeHom (TowerNoAbsorption.lamD k) ≤ u :=
  SeamCut.spikeHom_lamD_le k u hu

end SeamCutCheck

#print axioms SeamCut.canon_tagC_bot
#print axioms SeamCut.cSeam_le_iff
#print axioms SeamCut.cSeamFixed_iff_ideal_stable
#print axioms SeamCut.spikeHom_lamD_le

-- [D-3746] §The-global-invariants-at-the-seam
section IdealCheck

open IdealInvariant CanonicalChain SeamFixed PhiIterateTower PhiBilimit PhiStagePipe

-- [D-3747] example-B
noncomputable example (θ : PhiBilimit.B ≃o PhiBilimit.B) (c : PhiBilimit.B) :
    {y : PhiBilimit.B // y ≤ c} ≃o {y : PhiBilimit.B // y ≤ θ c} :=
  IdealInvariant.idealIso θ c

-- [D-3748] example-B
example (θ : PhiBilimit.B ≃o PhiBilimit.B) :
    ∃ (n : ℕ) (y : D (n + 1)), θ cSeamB = insD n y :=
  IdealInvariant.theta_cSeamB_stage θ

-- [D-3749] example
example :
    (∀ z : PhiBilimit.B,
        Nonempty ({y : PhiBilimit.B // y ≤ z} ≃o {y : PhiBilimit.B // y ≤ cSeamB}) →
          z = cSeamB)
      → CanonicalChain.CSeamFixed :=
  IdealInvariant.cSeamFixed_of_ideal_pins

-- [D-3750] example-D
example {k : ℕ} {z : D (k + 1)} (hne : z ≠ cSeam k) (hc : z ≤ cSeam k ∨ cSeam k ≤ z) :
    ¬ Nonempty ({w : D (k + 1) // w ≤ z} ≃o {w : D (k + 1) // w ≤ cSeam k}) :=
  IdealInvariant.not_idealIso_of_ne_of_comp hne hc

-- [D-3751] example-D
example {k : ℕ} (z : D (k + 1)) :
    (z ≤ cSeam k ∨ cSeam k ≤ z) ∨ ∃ y : EndP (D k), z.1 = Sum.inr (Sum.inl y) :=
  IdealInvariant.comparable_or_tagB z

end IdealCheck

#print axioms IdealInvariant.idealIso
#print axioms IdealInvariant.theta_cSeamB_stage
#print axioms IdealInvariant.cSeamFixed_of_ideal_pins
#print axioms IdealInvariant.ideal_ncard_lt_of_lt
#print axioms IdealInvariant.ideal_ncard_lt_of_gt
#print axioms IdealInvariant.not_idealIso_of_ne_of_comp
#print axioms IdealInvariant.comparable_or_tagB
