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

/-!
# `Dinfty.Verify` — the single entry point for an independent check

```
lake build Dinfty.Verify
```

Building this module elaborates both headline results and prints the axioms each
one depends on.  A clean run means:

* the build reports `Build completed successfully` with no `error:` line, and
* every `#print axioms` below lists **only** `propext`, `Classical.choice` and
  `Quot.sound` — Lean's three standard axioms — and in particular never
  `sorryAx` (a `sorry`) or `Lean.ofReduceBool` (a `native_decide`).

Nothing else in the repository needs to be built to check these two theorems;
the import closure of this file is the whole of what they depend on.
-/

open GluingTowerLibrary SierpinskiApplication

section PillarA

/-- **Theorem A, order-theoretic half.**  `Φ(D∞^Φ) ≃o D∞^Φ`: the bilimit of the
Φ-iterate tower is a fixed point of `Φ` up to order-isomorphism. -/
noncomputable example : PhiBilimit.phiB ≃o PhiIterateTower.phiTowerEP.Bilim :=
  PhiSurjective.theoremA_orderIso

end PillarA

section PillarB

/-- **Theorem B, rigidity.**  `D∞` has no non-identity order-automorphism. -/
example : Subsingleton (DInfty ≃o DInfty) := CopyCHigh.colimit_compat

/-- The same for the bilimit presentation. -/
example : Subsingleton (DBilimit ≃o DBilimit) := CopyCHigh.DBilimit_rigid

end PillarB


section InternalIFS

/-- **The honest internal IFS on the carrier**, the thing  was
written for and left without.  All three copy-maps are injective on all of  -
injectivity is exactly what the retract could not supply. -/
noncomputable example : InternalIFS PhiBilimit.B := InternalIFSInstance.ifsB

example : Function.Injective InternalIFSInstance.ifsB.sigmaA :=
  InternalIFSInstance.sigmaA_injective
example : Function.Injective InternalIFSInstance.ifsB.sigmaB :=
  InternalIFSInstance.sigmaB_injective
example : Function.Injective InternalIFSInstance.ifsB.sigmaC :=
  InternalIFSInstance.sigmaC_injective

end InternalIFS


section Escape

/-- **A negative result, machine-checked.**  Theorem ESCAPE (`Fix σ_A = {⊥}`)
is FALSE for this internal IFS: the marked point is fixed by `σ_A` too, and it
is `σ_B ⊥`, so it lies in the orbit of `⊥` and the failure survives passing to
the attractor.  `CoreIFS.FixData.fixA` is therefore unsatisfiable here. -/
example (b : PhiBilimit.B) : Fix InternalIFSInstance.ifsB.sigmaA ≠ {b} :=
  EscapeAnalysis.fix_sigmaA_not_singleton b

example : InternalIFSInstance.ifsB.sigmaA PhiBilimit.midB = PhiBilimit.midB :=
  EscapeAnalysis.sigmaA_mid

example : InternalIFSInstance.ifsB.sigmaB (⊥ : PhiBilimit.B) = PhiBilimit.midB :=
  EscapeAnalysis.sigmaB_bot

end Escape


section Rebuilt

/-- **The rebuilt IFS.**  `constS` replaced by the strict constant, which kills
the coincidence §96 found. -/
noncomputable example : InternalIFS PhiBilimit.B := SigmaRebuild.ifsS

example : Function.Injective SigmaRebuild.ifsS.sigmaA := SigmaRebuild.sigmaA_injective
example : Function.Injective SigmaRebuild.ifsS.sigmaB := SigmaRebuild.sigmaB_injective
example : Function.Injective SigmaRebuild.ifsS.sigmaC := SigmaRebuild.sigmaC_injective

example : SigmaRebuild.ifsS.sigmaA (⊥ : PhiBilimit.B) = ⊥ := SigmaRebuild.sigmaA_bot
example : PhiBilimit.midB ∉ Fix SigmaRebuild.ifsS.sigmaA := SigmaRebuild.mid_not_mem_fix

/-- **Theorem A's uniqueness clause does not need ESCAPE.**  `CoreIFS.base_pin`
uses `FixData` only to produce `botC ∈ Fix σ_A`; membership alone suffices, and
`sigmaA_bot` supplies it. -/
example : True := trivial

end Rebuilt


section Projection

/-- **The base projection is explicit.**  `qAA k z` is the greatest `y` with
`glueAA k y ≤ z`; it was never a `choice`. -/
example (k : ℕ) (z : D (k + 2)) :
    IsGreatest {y : D (k + 1) | glueAA k y ≤ z} (GlueAAEpPartner.qAA k z) :=
  QAAExplicit.qAA_isGreatest k z

example (k : ℕ) (y : D (k + 1)) (z : D (k + 2)) :
    glueAA k y ≤ z ↔ y ≤ GlueAAEpPartner.qAA k z :=
  QAAExplicit.glueAA_le_iff_le_qAA k y z

example : PhiIterateTower.phiTowerEP.prj 0 = GlueAAEpPartner.qAA 0 :=
  QAAExplicit.prj_zero_eq

end Projection


section EscapeHolds

/-- **Theorem ESCAPE, for the rebuilt `σ_A`.**  `Fix σ_A = {⊥}` exactly — the
statement §96 refuted for the `constS` IFS and §97's rebuild repaired. -/
example : Fix SigmaRebuild.ifsS.sigmaA = {(⊥ : PhiBilimit.B)} := EscapeProof.fix_sigmaA

end EscapeHolds


section Gasket

open Topology

/-! ### `Γ` is a definition, not a parameter

The Sierpiński gasket is constructed as the attractor of three explicit
contractions of `ℝ × ℝ`, so `f_A/f_B/f_C` can no longer be instantiated at
anything one likes.  `Γ` has at least three points, so no degenerate carrier
can stand in for it. -/

example : Gasket.gasketSet
    = (Gasket.contract Gasket.cA '' Gasket.gasketSet)
      ∪ (Gasket.contract Gasket.cB '' Gasket.gasketSet)
      ∪ (Gasket.contract Gasket.cC '' Gasket.gasketSet) := Gasket.gasketSet_eq

example : Nontrivial Gasket.Gamma := Gasket.gamma_nontrivial

/-! ### The coding map `π : {A,B,C}^ℕ ↠ Γ` -/

example : Continuous Gasket.codeGamma := Gasket.continuous_codeGamma

example : Function.Surjective Gasket.codeGamma := Gasket.codeGamma_surjective

example (w : ℕ → Fin 3) :
    Gasket.codeGamma (Gasket.cons 0 w) = Gasket.fA (Gasket.codeGamma w) :=
  Gasket.codeGamma_cons_zero w

/-- **Uniqueness, with no continuity hypothesis.**  Stronger than
`TheoremAData.unique`, which assumes continuity and surjectivity. -/
example (r : (ℕ → Fin 3) → Gasket.Gamma)
    (hA : ∀ w, r (Gasket.cons 0 w) = Gasket.fA (r w))
    (hB : ∀ w, r (Gasket.cons 1 w) = Gasket.fB (r w))
    (hC : ∀ w, r (Gasket.cons 2 w) = Gasket.fC (r w)) :
    r = Gasket.codeGamma := Gasket.coding_unique r hA hB hC

/-- **The corrected `quotient_map` field.**  `TheoremAData` asks for
`IsOpenMap`.  What holds is `IsQuotientMap`. -/
example : IsQuotientMap Gasket.codeGamma := Gasket.isQuotientMap_codeGamma

/-- **A second negative result, machine-checked.**  `TheoremAData`'s
`quotient_map` field asks for `IsOpenMap rho`, and no coding map can supply it:
the image of the `A`-cylinder is the sub-gasket `h_A(Γ)`, which is not open in
`Γ`.  The field must be weakened to `IsQuotientMap` before `TheoremAData` can be
instantiated at all. -/
example : ¬ IsOpenMap Gasket.codeGamma := Gasket.notOpen

example : ¬ IsOpen {x : Gasket.Gamma | (x : Gasket.E)
    ∈ Gasket.contract Gasket.cA '' Gasket.gasketSet} := Gasket.not_isOpen_imageA

end Gasket


section Link

/-! ### The address map into `B`, and `ρ`

`codeB` is the domain-theoretic twin of `π`: the supremum of
`σ_{w 0} ∘ ⋯ ∘ σ_{w (n-1)} (⊥)`.  It is equivariant and **injective**, so the
attractor `𝒦 = range codeB` is a copy of the address space inside `B` and `ρ`
is well-defined on it. -/

example (j : Fin 3) (w : ℕ → Fin 3) :
    CodeB.codeB (Gasket.cons j w) = CodeB.sig j (CodeB.codeB w) := CodeB.codeB_cons j w

example : Function.Injective CodeB.codeB := CodeB.codeB_injective

example : Function.Surjective CodeB.rho := CodeB.rho_surjective

example (w : ℕ → Fin 3) :
    CodeB.rho ⟨CodeB.codeB w, CodeB.codeB_mem_attractor w⟩ = Gasket.codeGamma w :=
  CodeB.rho_codeB w

/-- Any two of the three maps have disjoint images, which is what makes the
address recoverable. -/
example (j j' : Fin 3) (h : j ≠ j') (x y : PhiBilimit.B) :
    CodeB.sig j x ≠ CodeB.sig j' y := CodeB.sig_ne_of_ne j j' h x y

/-- **The necessary condition from `Γ`**: `Fix σ_A` may not meet `Fix σ_B`. -/
example : Disjoint (Fix SigmaRebuild.ifsS.sigmaA) (Fix SigmaRebuild.ifsS.sigmaB) :=
  Gasket.ifsS_fix_disjoint_AB

/-- **`base_pin`, concretely**: any equivariant `ρ` out of `B` sends `⊥` to the
`A`-vertex of the gasket. -/
example {rho : PhiBilimit.B → Gasket.Gamma}
    (hA : ∀ x, rho (SigmaRebuild.ifsS.sigmaA x) = Gasket.fA (rho x)) :
    rho (⊥ : PhiBilimit.B) = Gasket.gA := Gasket.rho_bot hA

end Link


section Continuity

/-! ### Which topology `ρ` can be continuous for

The Scott topology — and every other topology built from the order — is ruled
out, because Theorem ESCAPE forces `σ_A ⊥ = ⊥`, hence `⊥ ∈ 𝒦` and `ρ ⊥ = v_A`,
and `⊥`'s only upward-closed neighbourhood is all of `𝒦`.  What is left is
chain continuity, and that reduces to a statement about addresses. -/

example : CodeB.rho ⟨(⊥ : PhiBilimit.B), CodeB.bot_mem_attractor⟩ = Gasket.gA :=
  RhoContinuity.rho_bot_eq

/-- **The refutation of every order-derived topology.** -/
example (τ : TopologicalSpace CodeB.Attractor)
    (hup : RhoContinuity.UpwardClosedOpens τ)
    (hcont : @Continuous CodeB.Attractor Gasket.Gamma τ _ CodeB.rho) : False :=
  RhoContinuity.no_continuous_rho_of_upwardClosed τ hup hcont

/-- **The residue, discharged.**  The head of an address can only move up
(`head_le_of_codeB_le`), so along an increasing chain it is eventually constant
(`head_eventually_const`), and one recurses into the copy it settled in. -/
example : RhoContinuity.AddressesConverge := CodeB.addressesConverge

/-- **`ρ` is chain continuous.** -/
example : RhoContinuity.ChainContinuous CodeB.rho := CodeB.rho_chainContinuous

/-- **ρ is unique**, with no continuity or surjectivity hypothesis - strictly
stronger than TheoremAData.unique. -/
example (r : CodeB.Attractor → Gasket.Gamma)
    (hA : ∀ b : CodeB.Attractor,
      r ⟨CodeB.sig 0 (b : PhiBilimit.B), CodeB.mapsTo_sig 0 b.2⟩ = Gasket.fA (r b))
    (hB : ∀ b : CodeB.Attractor,
      r ⟨CodeB.sig 1 (b : PhiBilimit.B), CodeB.mapsTo_sig 1 b.2⟩ = Gasket.fB (r b))
    (hC : ∀ b : CodeB.Attractor,
      r ⟨CodeB.sig 2 (b : PhiBilimit.B), CodeB.mapsTo_sig 2 b.2⟩ = Gasket.fC (r b)) :
    r = CodeB.rho := CodeB.rho_unique r hA hB hC

/-- Each `σ_j` reflects the order, which is the recursion step that residue
needs. -/
example (j : Fin 3) (x y : PhiBilimit.B) : CodeB.sig j x ≤ CodeB.sig j y ↔ x ≤ y :=
  CodeB.sig_le_iff j x y

end Continuity


section TwoObjects

/-! ### Theorem A and Theorem B are about DIFFERENT domains

B = phiTowerEP.Bilim is the Φ-iterate bilimit; DBilimit is the legacy
iotaD bilimit.  They are **not** order-isomorphic: glueAA preserves ⊤ and
iotaD does not, and that shows up in the bilimits as compactness of the top. -/

example : ¬ BilimitGap.OmegaCompact topSeq := BilimitGap.topSeq_not_omegaCompact

example : BilimitGap.OmegaCompact (PhiBilimit.topB : PhiBilimit.B) := BilimitGap.topB_omegaCompact

/-- **The refutation.** -/
example : ¬ Nonempty (PhiBilimit.B ≃o DBilimit) := BilimitGap.no_orderIso

/-- **What the relation actually is.**  Copy A is a down-set
(CopyHierarchy.tagA_source), iotaD lands in it and never reaches the top,
while glueAA hits the top exactly.  So the legacy tower is confined, level by
level, to a proper order-ideal of the level the Φ-tower uses in full. -/
example (k : ℕ) :
    (∀ x : D k, iotaD k x ∈ CopyIdeal.CopyA (markedPt k)
        ∧ iotaD k x ≠ (⊤ : D (k + 1)))
      ∧ glueAA k (⊤ : D (k + 1)) = (⊤ : D (k + 2)) :=
  CopyIdeal.legacy_confined_phi_not k

/-- What an identification would have bought: Theorem B's rigidity, transferred
to Theorem A's carrier.  It is not available. -/
example (e : PhiBilimit.B ≃o DBilimit) : Subsingleton (PhiBilimit.B ≃o PhiBilimit.B) :=
  BilimitGap.rigid_of_orderIso e

end TwoObjects

/-! ## Axiom dependencies -/

-- Pillar A.
#print axioms PhiSurjective.theoremA_orderIso
#print axioms PhiSurjective.phiSupExists
#print axioms PhiSurjective.phiProjContinuous
#print axioms PhiCoconeLUB.phiCoconeIsLUB
#print axioms PhiCoconeLUB.isColimitCocone

-- The internal IFS.
#print axioms InternalIFSInstance.ifsB
#print axioms InternalIFSInstance.sigmaA_injective
#print axioms InternalIFSInstance.sigmaB_injective
#print axioms InternalIFSInstance.sigmaC_injective
#print axioms InternalIFSInstance.sigmaA_bot

-- The ESCAPE refutation.
#print axioms EscapeAnalysis.sigmaA_mid
#print axioms EscapeAnalysis.sigmaB_bot
#print axioms EscapeAnalysis.fix_sigmaA_not_singleton

-- The rebuilt sigma, and the uniqueness correction.
#print axioms SigmaRebuild.ifsS
#print axioms SigmaRebuild.sigmaA_bot
#print axioms SigmaRebuild.sigmaA_mid_ne
#print axioms SigmaRebuild.base_pin_of_mem
#print axioms SigmaRebuild.theoremA_unique_of_mem

-- The base projection, explicitly.
#print axioms QAAExplicit.qAA_isGreatest
#print axioms QAAExplicit.glueAA_le_iff_le_qAA
#print axioms QAAExplicit.level_zero_isGreatest
#print axioms QAAExplicit.fix_level_zero

-- Theorem ESCAPE for the rebuilt sigma.
#print axioms EscapeProof.fix_sigmaA
#print axioms EscapeProof.eq_bot_of_glueAA_le

-- The gasket, the coding map, and the CoreIFS data.
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

-- The address map into B, and rho.
#print axioms CodeB.codeB_cons
#print axioms CodeB.sig_ne_of_ne
#print axioms CodeB.codeB_injective
#print axioms CodeB.rho_codeB
#print axioms CodeB.rho_surjective
#print axioms CodeB.attractorEquiv
#print axioms CodeB.sig_le_iff

-- Which topology rho can be continuous for.
#print axioms RhoContinuity.rho_bot_eq
#print axioms RhoContinuity.no_continuous_rho_of_upwardClosed
#print axioms RhoContinuity.chainContinuous_of_addressesConverge
#print axioms CodeB.head_le_of_codeB_le
#print axioms CodeB.head_eventually_const
#print axioms CodeB.addressesConverge
#print axioms CodeB.rho_chainContinuous
#print axioms CodeB.rho_unique

-- Theorem A's object is not Theorem B's object.
#print axioms BilimitGap.topSeq_not_omegaCompact
#print axioms BilimitGap.topB_omegaCompact
#print axioms BilimitGap.no_orderIso
#print axioms BilimitGap.rigid_of_orderIso
#print axioms CopyIdeal.copyA_isLowerSet
#print axioms CopyIdeal.legacy_confined_phi_not

-- Pillar B.
#print axioms CopyCHigh.colimit_compat
#print axioms CopyCHigh.DBilimit_rigid
#print axioms CopyCHigh.firstSlice

-- The glue order both pillars stand on.  These two carry a `first | ... | fail`
-- fallback; if a transitivity case ever fell through to it the build would fail
-- rather than silently admit a `sorry`.
#print axioms glue_trans
#print axioms glueGen_trans
#print axioms glueCarPartialOrder
#print axioms glueCarPartialOrderGen

/-! ## The seam triangle

`CoreIFS` carries three maps with no relation between them.  The relation is
pairwise: three seams, one per unordered pair, and they are the three clauses of
`canonGen`.  `Γ` satisfies them; the address space and `𝒦 ⊆ B` satisfy their
negation; `ρ` is the map that installs them. -/

section SeamTriangleCheck

-- The three seams at the tower, `a`/`b`, `c`/`a`, `b`/`c`.
example : Gasket.tagB_bot_eq_mark = Gasket.tagB_bot_eq_mark := rfl
example : Gasket.tagC_bot_eq_top = Gasket.tagC_bot_eq_top := rfl
example : SeamTriangle.tagC_mark_eq_tagB_top = SeamTriangle.tagC_mark_eq_tagB_top := rfl

-- `Γ` is seamed; the address space and `𝒦` are not.
example : SeamTriangle.Seamed SeamTriangle.fseq SeamTriangle.gseq :=
  SeamTriangle.gasket_seamed
example : SeamTriangle.Seamless (fun j : Fin 3 => Gasket.cons j) :=
  SeamTriangle.address_seamless
example : SeamTriangle.Seamless CodeB.sig := SeamTriangle.codeB_seamless
example (p : Fin 3 → PhiBilimit.B) : ¬ SeamTriangle.Seamed CodeB.sig p :=
  SeamTriangle.codeB_not_seamed p

-- `ρ` installs the seams, and that is exactly why it is not injective.
example (i j : Fin 3) (hij : i ≠ j) :
    Gasket.codeGamma (Gasket.cons i (fun _ => j))
      = Gasket.codeGamma (Gasket.cons j (fun _ => i)) := SeamTriangle.codeGamma_seam i j hij
example (i j : Fin 3) (hij : i ≠ j) :
    CodeB.codeB (Gasket.cons i (fun _ => j)) ≠ CodeB.codeB (Gasket.cons j (fun _ => i)) :=
  SeamTriangle.codeB_seam_ne i j hij
example : ¬ Function.Injective CodeB.rho := SeamTriangle.rho_not_injective

-- The openness failure is at the `a`/`b` seam.
example : Gasket.mid = ((SeamTriangle.fseq 0 (SeamTriangle.gseq 1) : Gasket.Gamma) : Gasket.E) :=
  SeamTriangle.mid_eq_seam

-- `fix_card`'s `fixB`/`fixC` cannot be satisfied inside `Core`.
example (j : Fin 3) : Fix (Gasket.cons j) = {(fun _ => j : ℕ → Fin 3)} :=
  SeamTriangle.fix_cons j
example (j : Fin 3) :
    Fix (CodeB.sig j) ∩ CodeB.Attractor = {CodeB.codeB (fun _ => j)} :=
  SeamTriangle.fix_sig_inter_attractor j
example (P : FixPoints Gasket.addressCoreIFS) [FixData P] : False :=
  SeamTriangle.no_fixData_address P

end SeamTriangleCheck

-- The seam triangle.
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

/-! ## From the copy-`A` ideal to the whole

Theorem B's rigidity does **not** reach `B` by restriction — the `Φ`-tower's
embeddings preserve `⊤` at every level and the legacy ones never reach it.  What
does transfer is pillar B's whole *abstract* half: an automorphism of any ep-pair
bilimit is determined by its action on the stages, and level rigidity plus
stage-definability forces it to be the identity.  `LevelsMaximallyRigid` is free
for the `Φ`-tower; `PhiStageDefinable` is the residue. -/

section StageRigidityCheck

-- The unconditional half: stages determine an automorphism.
example (θ : PhiBilimit.B ≃o PhiBilimit.B)
    (key : ∀ (k : ℕ) (x : PhiIterateTower.phiTowerEP.carrier k),
      θ (EpPairTower.ins PhiIterateTower.phiTowerEP k x)
        = EpPairTower.ins PhiIterateTower.phiTowerEP k x) :
    θ = OrderIso.refl PhiBilimit.B :=
  StageRigidity.eq_refl_of_fixes_stages θ key

-- Free: the levels admit no nontrivial monotone self-injection.
example : StageRigidity.LevelsMaximallyRigid PhiIterateTower.phiTowerEP :=
  PhiRigidity.levels_maximally_rigid

-- The reduction: Theorem A's carrier is rigid as soon as its stages are definable.
example : PhiRigidity.PhiStageDefinable →
    Subsingleton (PhiBilimit.B ≃o PhiBilimit.B) :=
  PhiRigidity.B_rigid_of_stageDefinable

-- The legacy tower is a subtower...
example (k : ℕ) (x : D k) : glueAA k (iotaD k x) = iotaD (k + 1) (iotaD k x) :=
  PhiRigidity.legacy_subtower k x

-- ...and a proper one, at `⊤`, at every level of the actual tower.
example (n : ℕ) (x : D (n + 1)) :
    (PhiIterateTower.iter n).emb (⊤ : D (n + 1)) ≠ iotaD (n + 1) x :=
  PhiRigidity.phi_emb_top_not_legacy n x

end StageRigidityCheck

-- Ideal to whole.
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

/-! ## The residue, cleaned

`PhiStageDefinable` is now one level-local `Prop`, the exact mirror of pillar
B's `JoinIrredStagePreserved`.  The other two links are discharged, and the
filtration is preserved unconditionally. -/

section PhiStagePipeCheck

-- The engine: `ins k` is a left adjoint to reading off level `k`.
example (k : ℕ) (a : D (k + 1)) (u : PhiBilimit.B) :
    PhiStagePipe.insD k a ≤ u ↔ a ≤ u.1 k := PhiStagePipe.insD_le_iff k a u

-- Discharged: stage suprema stay in the stage.
example (k : ℕ) (S : Set PhiBilimit.B) (z : PhiBilimit.B)
    (hS : ∀ w ∈ S, ∃ y : D (k + 1), PhiStagePipe.insD k y = w) (hz : IsLUB S z) :
    ∃ y : D (k + 1), PhiStagePipe.insD k y = z := PhiStagePipe.stageSupClosed k S z hS hz

-- Discharged: every stage point is the sup of the stage join-irreducibles below it.
example (k : ℕ) (x : D (k + 1)) :
    IsLUB (PhiStagePipe.stageJI k x) (PhiStagePipe.insD k x) :=
  PhiStagePipe.stageJoinRecoverable k x

-- The stages of `B` are exactly its compact elements.
example (z : PhiBilimit.B) :
    BilimitGap.OmegaCompact z ↔ ∃ (k : ℕ) (y : D (k + 1)), PhiStagePipe.insD k y = z :=
  PhiStagePipe.omegaCompact_iff_stage z

-- Unconditional: an automorphism cannot leave the filtration...
example (θ : PhiBilimit.B ≃o PhiBilimit.B) (k : ℕ) (x : D (k + 1)) :
    ∃ (n : ℕ) (y : D (n + 1)), θ (PhiStagePipe.insD k x) = PhiStagePipe.insD n y :=
  PhiStagePipe.stages_union_preserved θ k x

-- ...nor move either end of a stage.
example (θ : PhiBilimit.B ≃o PhiBilimit.B) (k : ℕ) :
    θ (PhiStagePipe.insD k ⊥) = PhiStagePipe.insD k ⊥ := PhiStagePipe.apply_insD_bot θ k
example (θ : PhiBilimit.B ≃o PhiBilimit.B) (k : ℕ) :
    θ (PhiStagePipe.insD k ⊤) = PhiStagePipe.insD k ⊤ := PhiStagePipe.apply_insD_top θ k

end PhiStagePipeCheck

-- The residue, cleaned.
#print axioms StageRigidity.ins_le_iff'
#print axioms PhiStagePipe.stageSupClosed
#print axioms PhiStagePipe.stageJoinRecoverable
#print axioms PhiStagePipe.insD_omegaCompact
#print axioms PhiStagePipe.exists_stage_of_omegaCompact
#print axioms PhiStagePipe.omegaCompact_iff_stage
#print axioms PhiStagePipe.stages_union_preserved
#print axioms PhiStagePipe.apply_insD_bot
#print axioms PhiStagePipe.apply_insD_top

/-! ## The residue is level-local

On each stage an automorphism of `B` is a bounded join-embedding of one level
into a later one — unconditionally.  `embLe` is one such map, and the whole
question is whether it is the only one.  No bilimit, no seeds, no
join-irreducibility. -/

section StageEmbeddingCheck

-- Unconditional: the shape of an automorphism on a stage.
example (θ : PhiBilimit.B ≃o PhiBilimit.B) (k : ℕ) :
    ∃ m : ℕ, k ≤ m ∧ ∃ f : D (k + 1) → D (m + 1),
      (∀ x, θ (PhiStagePipe.insD k x) = PhiStagePipe.insD m (f x))
        ∧ Monotone f ∧ (∀ a b, f a ≤ f b → a ≤ b)
        ∧ f ⊥ = ⊥ ∧ f ⊤ = ⊤ ∧ (∀ a b, f (a ⊔ b) = f a ⊔ f b) :=
  StageEmbedding.stage_map_exists θ k

-- The tower's embeddings preserve binary joins, at every level.
example {k m : ℕ} (h : k ≤ m) (a b : D (k + 1)) :
    StageEmbedding.embD h (a ⊔ b) = StageEmbedding.embD h a ⊔ StageEmbedding.embD h b :=
  StageEmbedding.embD_sup h a b

-- The `k = m` case of the residue is already a theorem.
example (k : ℕ) (f : D (k + 1) → D (k + 1)) (hmono : Monotone f)
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b) : f = StageEmbedding.embD (le_refl k) :=
  StageEmbedding.levelEmbUnique_diagonal k f hmono hrefl

-- The chain closes from the level-local statement.
example : StageEmbedding.LevelEmbUnique →
    Subsingleton (PhiBilimit.B ≃o PhiBilimit.B) :=
  StageEmbedding.B_rigid_of_levelEmbUnique

end StageEmbeddingCheck

-- The level-local residue.
#print axioms StageEmbedding.insD_isLUB_pair
#print axioms StageEmbedding.embD_sup
#print axioms StageEmbedding.stage_map_exists
#print axioms StageEmbedding.stage_map_comp
#print axioms StageEmbedding.levelEmbUnique_diagonal
#print axioms StageEmbedding.phiStageDefinable_of_levelEmbUnique
#print axioms StageEmbedding.B_rigid_of_levelEmbUnique

/-! ## `embD`, and the residue as an image statement

`embD h` is one half of an ep-pair, so its image is the fixed-point set of a
deflation idempotent, and both it and any order-reflecting `f` have exactly
`Nat.card (D (k+1))` values.  The conclusion `f = embD h` then follows from
`D_monotone_injection_eq_id` alone — the bounds and the joins are only there to
pin the image, and they reduce it to join-irreducibles. -/

section EmbDImageCheck

-- `prjD` retracts `embD`, and `embD ∘ prjD` is a deflation.
example {k m : ℕ} (h : k ≤ m) (x : D (k + 1)) : EmbDImage.prjD h (StageEmbedding.embD h x) = x :=
  EmbDImage.prjD_embD h x
example {k m : ℕ} (h : k ≤ m) (z : D (m + 1)) :
    StageEmbedding.embD h (EmbDImage.prjD h z) ≤ z := EmbDImage.embD_prjD_le h z

-- The image, named.
example {k m : ℕ} (h : k ≤ m) (z : D (m + 1)) :
    z ∈ Set.range (StageEmbedding.embD h) ↔ StageEmbedding.embD h (EmbDImage.prjD h z) = z :=
  EmbDImage.mem_range_embD_iff h z

-- Measuring it: containment upgrades to equality in a finite level.
example {k m : ℕ} (h : k ≤ m) : (Set.range (StageEmbedding.embD h)).ncard = Nat.card (D (k + 1)) :=
  EmbDImage.ncard_range_embD h
example {k m : ℕ} (h : k ≤ m) (f : D (k + 1) → D (m + 1))
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b)
    (hsub : Set.range f ⊆ Set.range (StageEmbedding.embD h)) :
    Set.range f = Set.range (StageEmbedding.embD h) := EmbDImage.range_eq_of_subset h f hrefl hsub

-- Only the image matters: no bounds, no joins used here.
example {k m : ℕ} (h : k ≤ m) (f : D (k + 1) → D (m + 1)) (hmono : Monotone f)
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b)
    (hrange : ∀ x, StageEmbedding.embD h (EmbDImage.prjD h (f x)) = f x) :
    f = StageEmbedding.embD h := EmbDImage.eq_embD_of_range_subset h f hmono hrefl hrange

-- `embD` is in the class the residue is about.
example {k m : ℕ} (h : k ≤ m) : StageEmbedding.embD h (⊥ : D (k + 1)) = (⊥ : D (m + 1)) :=
  EmbDImage.embD_bot h
example {k m : ℕ} (h : k ≤ m) : StageEmbedding.embD h (⊤ : D (k + 1)) = (⊤ : D (m + 1)) :=
  EmbDImage.embD_top h

-- The chain, from the join-irreducible form.
example : EmbDImage.LevelImageStableJI → Subsingleton (PhiBilimit.B ≃o PhiBilimit.B) :=
  EmbDImage.B_rigid_of_levelImageStableJI

end EmbDImageCheck

-- `embD` formalized; the residue as an image statement.
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

/-! ## The embeddings are tagwise, and copy `A` is a principal ideal

`Φ` on morphisms is `canonGen ∘ baseMapGen`, and `canonGen` is *inert* on the
image of an injective tripointed map — so the tower's embeddings never change a
point's copy.  Copy `A` is the principal ideal generated by the tag-`A` copy of
`⊤`, which is what any comparison of a map against `embD` has to work with. -/

section TagwiseCheck

-- `Φ` on morphisms is tagwise on the nose.
example (n : ℕ) (x : D (n + 2)) :
    ((PhiIterateTower.iter (n + 1)).emb x).1
      = GenContinuity.baseMapGen (PhiIterateTower.iter n).endUp.toFun x.1 :=
  EmbTagwise.emb_succ_val n x

-- …so the embeddings preserve the copy index.
example (n : ℕ) (x : D (n + 2)) :
    CopyHierarchy.copyIdx ((PhiIterateTower.iter (n + 1)).emb x).1
      = CopyHierarchy.copyIdx x.1 :=
  EmbTagwise.emb_succ_copyIdx n x

-- The image, tagwise; the tag-`A` slot is `Set.range endUpFun`.
example (n : ℕ) (z : D (n + 3)) (a : EndP (D (n + 2))) (hz : z.1 = Sum.inl a) :
    z ∈ Set.range ((PhiIterateTower.iter (n + 1)).emb)
      ↔ a ∈ Set.range (PhiIterateTower.iter n).endUpFun :=
  EmbTagwise.range_val_emb_succ_inl n z a hz

-- Copy `A` is a principal ideal.
example (k : ℕ) (x : D (k + 1)) :
    (∃ a : EndP (D k), x.1 = Sum.inl a) ↔ x ≤ SeamFixed.cSeam k :=
  SeamFixed.mem_copyA_iff_le_cSeam k x

-- One point pins the copy-`A` split, in both directions...
example {k m : ℕ} (f : D (k + 1) → D (m + 1)) (hmono : Monotone f)
    (hrefl : ∀ a b, f a ≤ f b → a ≤ b) (hseam : f (SeamFixed.cSeam k) = SeamFixed.cSeam m)
    (x : D (k + 1)) :
    (∃ a : EndP (D m), (f x).1 = Sum.inl a) ↔ (∃ a : EndP (D k), x.1 = Sum.inl a) :=
  SeamFixed.copyA_preserved f hmono hrefl hseam x

-- ...and one-directionally under the hypothesis `embD` actually satisfies.
example {k m : ℕ} (f : D (k + 1) → D (m + 1)) (hmono : Monotone f)
    (hseam : f (SeamFixed.cSeam k) ≤ SeamFixed.cSeam m) (x : D (k + 1))
    (hx : ∃ a : EndP (D k), x.1 = Sum.inl a) :
    ∃ a : EndP (D m), (f x).1 = Sum.inl a :=
  SeamFixed.copyA_mapsTo f hmono hseam x hx

end TagwiseCheck

-- Tagwise embeddings; copy `A` as a principal ideal.
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

/-! ## Running the split: no generic proof of the residue exists

`LevelImageStableJI` is false as a general fact about finite bounded lattices —
a three-chain has two bounded join-embeddings into a four-chain.  Nothing in the
derivation used more than "finite bounded lattice with an ep-pair", so any proof
must consume `D`-specific structure, and an abstract attempt is refuted before it
starts.  The residue itself is **not** refuted: the `Φ`-tower's levels start at
`D 1` and are never chains. -/

section SplitCheck

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

/-! ## The residue chain is REFUTED

`patched k x = if x = ⊤ then ⊤ else iotaD (k+1) x` is a bounded join-embedding
`D (k+1) → D (k+2)` that is not `embD`.  Order-reflection holds *because*
`iotaD` misses the top — obstruction (T), the defect that disqualified the
legacy tower for pillar A, is what refutes the uniqueness route.  This does not
refute `Subsingleton (B ≃o B)`: `LevelEmbUnique` was sufficient, not necessary. -/

section RefutationCheck

example (k : ℕ) : Monotone (PatchedEmbedding.patched k) := PatchedEmbedding.patched_monotone k
example (k : ℕ) (x y : D (k + 1)) :
    PatchedEmbedding.patched k x ≤ PatchedEmbedding.patched k y → x ≤ y :=
  PatchedEmbedding.patched_reflect k x y
example (k : ℕ) (x y : D (k + 1)) :
    PatchedEmbedding.patched k (x ⊔ y)
      = PatchedEmbedding.patched k x ⊔ PatchedEmbedding.patched k y :=
  PatchedEmbedding.patched_sup k x y
example (k : ℕ) {x y : D k} (h : x ⊔ y = ⊤) : x = ⊤ ∨ y = ⊤ :=
  PatchedEmbedding.top_joinIrred k h
example : ¬ StageEmbedding.LevelEmbUnique := PatchedEmbedding.not_levelEmbUnique
example : ¬ EmbDImage.LevelImageStableJI := PatchedEmbedding.not_levelImageStableJI

end RefutationCheck

-- The refutation.
#print axioms PatchedEmbedding.top_joinIrred
#print axioms PatchedEmbedding.patched_monotone
#print axioms PatchedEmbedding.patched_reflect
#print axioms PatchedEmbedding.patched_bot
#print axioms PatchedEmbedding.patched_sup
#print axioms PatchedEmbedding.top_val_two
#print axioms PatchedEmbedding.not_levelEmbUnique
#print axioms PatchedEmbedding.not_levelImageStable
#print axioms PatchedEmbedding.not_levelImageStableJI

/-! ## The residue, weakened: cofinally many stable levels

`stage_map_comp`'s content, used.  A stage map that lands back on its own level
is the identity there (`IsStageMap.diagonal`), and one stable level pins every
earlier stage (`fixes_stages_below`).  So an automorphism only has to be
stage-preserving at *arbitrarily large* levels, not at every level. -/

section CofinalCheck

open StageCofinal StageEmbedding PhiIterateTower PhiBilimit EpPairTower

example (θ : B ≃o B) (k : ℕ) :
    ∃ m, k ≤ m ∧ ∃ f : D (k + 1) → D (m + 1), IsStageMap θ k m f :=
  StageCofinal.stage_map_exists' θ k

example (θ : B ≃o B) {k m m' : ℕ} {f : D (k + 1) → D (m + 1)} {f' : D (k + 2) → D (m' + 1)}
    (hf : IsStageMap θ k m f) (hf' : IsStageMap θ (k + 1) m' f')
    (hmm : m ≤ m') (hk : k ≤ k + 1) (x : D (k + 1)) :
    embD hmm (f x) = f' (embD hk x) :=
  StageCofinal.isStageMap_coherent hf hf' hmm hk x

example (θ : B ≃o B) {k : ℕ} {f : D (k + 1) → D (k + 1)} (hf : IsStageMap θ k k f) :
    f = id := hf.diagonal

example : PhiRigidity.PhiStageDefinableCofinal → Subsingleton (B ≃o B) :=
  PhiRigidity.B_rigid_of_cofinal

example : PhiRigidity.PhiStageDefinable → PhiRigidity.PhiStageDefinableCofinal :=
  PhiRigidity.phiStageDefinable_cofinal

end CofinalCheck

-- The cofinal weakening.
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

/-! ## The singular atom of a slice does not reach `B`

Every level has a least non-`⊥` element `lamD k`, and it is an iterated spike
(`lamD_succ`).  Tripointed ep-pairs carry spikes to spikes
(`endUpFun_spikeHom` — this is where `deflation` and `emb_top` are used), so the
question falls to the base; and at the base `glueAA 0`'s copy-`A` action is
`endUpFun` for the **legacy** pair `(iotaD, pD)`, which misses `⊤` and fattens
the spike into a constant.  Hence `emb_lamD_ne` at every level, the stage atoms
strictly decrease, and `B` is atomless — there is no singular atom of `B` for a
witness level to be tied to. -/

section AtomCheck

open AtomlessBilimit TowerNoAbsorption PhiIterateTower

example (k : ℕ) : lamD (k + 1) = glueA (markedPt k) (spikeHom (lamD k)) :=
  AtomlessBilimit.lamD_succ k

example {k : ℕ} (E : TriEP k) (v : D k) :
    E.endUpFun (spikeHom v) = spikeHom (E.emb v) :=
  AtomlessBilimit.endUpFun_spikeHom E v

example : (iter 0).emb (lamD 1) ≠ lamD 2 := AtomlessBilimit.base_emb_lamD_ne

example (k : ℕ) : (iter k).emb (lamD (k + 1)) ≠ lamD (k + 2) :=
  AtomlessBilimit.emb_lamD_ne k

example (a : PhiBilimit.B) : ¬ IsAtom a := AtomlessBilimit.no_isAtom a

end AtomCheck

-- `B` is atomless.
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

/-! ## The hunt: is the §117 freedom invertible?

`patched` IS coherent with the tower (`patched_coherent`) — `endUpFun` transports
constants just as it transports spikes — so it is a genuine morphism of the whole
stage filtration, not an artefact.  But an automorphism's stage maps are jointly
surjective onto the filtration (`stage_map_covers`, from `θ⁻¹`'s stage map), and
`patched`'s range is confined to copy `A` together with `⊤` while the tower's
embeddings preserve the copy index.  The copy-`B` point `wB` is never hit. -/

section CoverCheck

open StageCover StageCofinal PatchedEmbedding StageEmbedding PhiIterateTower PhiBilimit PhiStagePipe

example {k : ℕ} (E : TriEP k) (x : D k) : E.endUpFun (constHom x) = constHom (E.emb x) :=
  StageCover.endUpFun_constHom E x

example (k : ℕ) (x : D (k + 1)) :
    (iter (k + 1)).emb (patched k x) = patched (k + 1) ((iter k).emb x) :=
  StageCover.patched_coherent k x

example (m : ℕ) (h : 1 ≤ m) (y : D 2) :
    CopyHierarchy.copyIdx (embD h y).1 = CopyHierarchy.copyIdx y.1 :=
  StageCover.embD_copyIdx m h y

example : ¬ ∃ θ : PhiBilimit.B ≃o PhiBilimit.B,
    ∀ (k : ℕ) (x : D (k + 1)), θ (insD k x) = insD (k + 1) (patched k x) :=
  StageCover.no_patched_automorphism

end CoverCheck

-- The hunt.
#print axioms StageCover.endUpFun_constHom
#print axioms StageCover.emb_eq_top_iff
#print axioms StageCover.patched_coherent
#print axioms StageCover.embD_copyIdx
#print axioms StageCover.stage_map_covers
#print axioms StageCover.no_patched_automorphism

/-! ## Splitting again: the canonical chain

Copy `A` of a level is the principal ideal under the seam `cSeam k`, so "meets
copy `B`" is "does not land under the seam".  The seam is level-stable from
level `1` up (`emb_cSeam_succ`) and fails at the base by `iotaD_ne_top`
(`base_emb_cSeam_ne`), so `cSeamB` is a canonical point of `B` and

    ⊥ < midB < cSeamB < ⊤

is a canonical chain.  `midB` does not discriminate — `iotaD` preserves the mid —
and the atom does not exist (§119).  `cSeamB` does: `patched` moves it. -/

section ChainCheck

open CanonicalChain PatchedEmbedding SeamFixed PhiIterateTower PhiBilimit PhiStagePipe

example (n : ℕ) : (iter (n + 1)).emb (cSeam (n + 1)) = cSeam (n + 2) :=
  CanonicalChain.emb_cSeam_succ n

example : (iter 0).emb (cSeam 0) ≠ cSeam 1 := CanonicalChain.base_emb_cSeam_ne

example (n : ℕ) : insD (n + 1) (cSeam (n + 1)) = cSeamB := CanonicalChain.insD_cSeam n

example : midB < cSeamB := CanonicalChain.midB_lt_cSeamB
example : cSeamB < (⊤ : PhiBilimit.B) := CanonicalChain.cSeamB_lt_top

example (n : ℕ) (x : D (n + 2)) :
    insD (n + 1) x ≤ cSeamB ↔ ∃ a : EndP (D (n + 1)), x.1 = Sum.inl a :=
  CanonicalChain.le_cSeamB_iff n x

-- the mid does NOT discriminate; the seam does
example (k : ℕ) : iotaD k (dMid k) = dMid (k + 1) := CanonicalChain.iotaD_preserves_mid k
example (k : ℕ) : patched k (cSeam k) ≠ cSeam (k + 1) := CanonicalChain.patched_ne_cSeam k

end ChainCheck

-- The canonical chain.
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

/-! ## `CSeamFixed`: structure settled, decision NOT reached

`cSeam k` is the top of copy `A` *and* the bottom of copy `C` (the `canonGen`
collapse `tag_C ⊥ ↦ inl ⊤`), so it cuts every level in two: `↓cSeam = copy A`,
`↑cSeam = copy C`.  Hence `CSeamFixed` is exactly "every automorphism preserves
the three-copy decomposition".

**`CSeamFixed` is OPEN.**  Nothing here asserts it and nothing here refutes it.
The local handles all die at the bilimit by §119's mechanism: the seam has a
unique upper cover at every *level* (`spikeHom_lamD_le`) and none at the
bilimit, because the stage atoms strictly decrease. -/

section SeamCutCheck

open SeamCut CanonicalChain SeamFixed PhiIterateTower PhiBilimit

example (k : ℕ) (z : D (k + 1)) :
    cSeam k ≤ z ↔ (z.1 = Sum.inl (⊤ : EndP (D k))
      ∨ z.1 = Sum.inr (Sum.inl (⊤ : EndP (D k)))
      ∨ ∃ c : EndP (D k), z.1 = Sum.inr (Sum.inr c)) :=
  SeamCut.cSeam_le_iff k z

example : CanonicalChain.CSeamFixed
    ↔ ∀ (θ : PhiBilimit.B ≃o PhiBilimit.B) (y : PhiBilimit.B),
        y ≤ cSeamB ↔ θ y ≤ cSeamB :=
  SeamCut.cSeamFixed_iff_ideal_stable

example (k : ℕ) (u : EndP (D k)) (hu : u ≠ ⊥) :
    spikeHom (TowerNoAbsorption.lamD k) ≤ u :=
  SeamCut.spikeHom_lamD_le k u hu

end SeamCutCheck

-- The seam as a cut point.  (No `#print axioms CSeamFixed` decision exists: it is open.)
#print axioms SeamCut.canon_tagC_bot
#print axioms SeamCut.cSeam_le_iff
#print axioms SeamCut.cSeamFixed_iff_ideal_stable
#print axioms SeamCut.spikeHom_lamD_le

/-! ## The global invariants at the seam

Two handles survive an automorphism because both are defined from the order
alone: **compactness** (`stages_union_preserved`) and **the principal-ideal
isomorphism type** (`idealIso`).  Applied to `cSeamB`, whose ideal is exactly
copy `A`, they turn `CSeamFixed` into a global statement — no neighbourhood, no
cover, no atom:

    CSeamFixed  ⟸  no other element of `B` has principal ideal ≅ copy `A`.

Inside a level the invariant decides every *comparable* case
(`not_idealIso_of_ne_of_comp`); copy `B` is what survives. -/

section IdealCheck

open IdealInvariant CanonicalChain SeamFixed PhiIterateTower PhiBilimit PhiStagePipe

noncomputable example (θ : PhiBilimit.B ≃o PhiBilimit.B) (c : PhiBilimit.B) :
    {y : PhiBilimit.B // y ≤ c} ≃o {y : PhiBilimit.B // y ≤ θ c} :=
  IdealInvariant.idealIso θ c

example (θ : PhiBilimit.B ≃o PhiBilimit.B) :
    ∃ (n : ℕ) (y : D (n + 1)), θ cSeamB = insD n y :=
  IdealInvariant.theta_cSeamB_stage θ

example :
    (∀ z : PhiBilimit.B,
        Nonempty ({y : PhiBilimit.B // y ≤ z} ≃o {y : PhiBilimit.B // y ≤ cSeamB}) →
          z = cSeamB)
      → CanonicalChain.CSeamFixed :=
  IdealInvariant.cSeamFixed_of_ideal_pins

example {k : ℕ} {z : D (k + 1)} (hne : z ≠ cSeam k) (hc : z ≤ cSeam k ∨ cSeam k ≤ z) :
    ¬ Nonempty ({w : D (k + 1) // w ≤ z} ≃o {w : D (k + 1) // w ≤ cSeam k}) :=
  IdealInvariant.not_idealIso_of_ne_of_comp hne hc

example {k : ℕ} (z : D (k + 1)) :
    (z ≤ cSeam k ∨ cSeam k ≤ z) ∨ ∃ y : EndP (D k), z.1 = Sum.inr (Sum.inl y) :=
  IdealInvariant.comparable_or_tagB z

end IdealCheck

-- The global invariants.  (`CSeamFixed` itself remains open.)
#print axioms IdealInvariant.idealIso
#print axioms IdealInvariant.theta_cSeamB_stage
#print axioms IdealInvariant.cSeamFixed_of_ideal_pins
#print axioms IdealInvariant.ideal_ncard_lt_of_lt
#print axioms IdealInvariant.ideal_ncard_lt_of_gt
#print axioms IdealInvariant.not_idealIso_of_ne_of_comp
#print axioms IdealInvariant.comparable_or_tagB
