import Dinfty.EscapeProof
import Dinfty.GasketNotOpen

open GluingTowerLibrary SierpinskiApplication

/-!
# What `Γ` forces on any internal IFS

Now that `Γ` exists, it can be used as a **test**: any candidate `σ_A/σ_B/σ_C`
that is to carry an equivariant `ρ` has to satisfy conditions read off the
gasket, and those conditions are checkable against the tower.

The whole thing rests on one elementary fact: each `f_j` is a contraction of a
metric space, so it has **at most one** fixed point in `Γ`, and that point is the
vertex `v_j`.  Equivariance then forces

```
ρ (Fix σ_j) ⊆ {v_j}
```

so `ρ` is *constant* on each fixed-point set, and — because the three vertices
are distinct — the three fixed-point sets must be **pairwise disjoint**.  That is
a necessary condition on the internal IFS which mentions no analysis at all.

## The verdict on the rebuilt `σ`

`SigmaRebuild.ifsS` **passes**.  `Fix σ_A = {⊥}` (`EscapeProof.fix_sigmaA`), and
`σ_B ⊥ = midB ≠ ⊥`, `σ_C ⊥ ≠ ⊥`, so `⊥` is in neither of the other two
fixed-point sets.  This also pins the value of any equivariant `ρ` at the base:
`ρ ⊥ = v_A`.  That is `CoreIFS.base_pin`'s content, now with a concrete `Γ` on
the right-hand side instead of an abstract one.

The `constS` IFS is a different story and is not tested here: `Fix σ_A` is not
even a singleton for it (`EscapeAnalysis.fix_sigmaA_not_singleton`), so `ρ`
would have to send both `⊥` and `midB` to `v_A`, which is possible but tells us
`ρ` cannot be injective there.
-/

open Metric Set

namespace Gasket

/-! ## 1.  A contraction has at most one fixed point -/

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

theorem fA_fixed_unique {x : Gamma} (hx : fA x = x) : x = gA := by
  refine Subtype.ext ?_
  exact eq_of_contract_fixed cA (congrArg Subtype.val hx) contract_vA

theorem fB_fixed_unique {x : Gamma} (hx : fB x = x) : x = gB := by
  refine Subtype.ext ?_
  exact eq_of_contract_fixed cB (congrArg Subtype.val hx) contract_vB

theorem fC_fixed_unique {x : Gamma} (hx : fC x = x) : x = gC := by
  refine Subtype.ext ?_
  exact eq_of_contract_fixed cC (congrArg Subtype.val hx) contract_vC

/-! ## 2.  Equivariance is constant on fixed-point sets -/

section Equivariance

variable {X : Type*} {rho : X → Gamma}

theorem rho_eq_gA {sA : X → X} (h : ∀ x, rho (sA x) = fA (rho x))
    {p : X} (hp : sA p = p) : rho p = gA :=
  fA_fixed_unique (by rw [← h p, hp])

theorem rho_eq_gB {sB : X → X} (h : ∀ x, rho (sB x) = fB (rho x))
    {p : X} (hp : sB p = p) : rho p = gB :=
  fB_fixed_unique (by rw [← h p, hp])

theorem rho_eq_gC {sC : X → X} (h : ∀ x, rho (sC x) = fC (rho x))
    {p : X} (hp : sC p = p) : rho p = gC :=
  fC_fixed_unique (by rw [← h p, hp])

/-- **The obstruction.**  Two of the three maps may not share a fixed point. -/
theorem no_shared_fix_AB {sA sB : X → X}
    (hA : ∀ x, rho (sA x) = fA (rho x)) (hB : ∀ x, rho (sB x) = fB (rho x))
    {p : X} (hpA : sA p = p) (hpB : sB p = p) : False :=
  gA_ne_gB ((rho_eq_gA hA hpA).symm.trans (rho_eq_gB hB hpB))

theorem no_shared_fix_AC {sA sC : X → X}
    (hA : ∀ x, rho (sA x) = fA (rho x)) (hC : ∀ x, rho (sC x) = fC (rho x))
    {p : X} (hpA : sA p = p) (hpC : sC p = p) : False :=
  gA_ne_gC ((rho_eq_gA hA hpA).symm.trans (rho_eq_gC hC hpC))

theorem no_shared_fix_BC {sB sC : X → X}
    (hB : ∀ x, rho (sB x) = fB (rho x)) (hC : ∀ x, rho (sC x) = fC (rho x))
    {p : X} (hpB : sB p = p) (hpC : sC p = p) : False :=
  gB_ne_gC ((rho_eq_gB hB hpB).symm.trans (rho_eq_gC hC hpC))

end Equivariance

/-! ## 3.  Running the test on `SigmaRebuild.ifsS`

Note what is *not* imported: `EscapeAnalysis`.  The two computations below are
done from `canonGen` directly, so the test does not depend on the module that
refutes the old `σ` — `EscapeAnalysis` stays a leaf. -/

open PhiIterateTower PhiBilimit GlueTag InternalIFSInstance SigmaRebuild

/-- The tag-`B` copy of `⊥` is the tag-`A` copy of the marked point. -/
theorem tagB_bot_eq_mark :
    tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)
      = tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB := by
  refine Subtype.ext ?_
  show (if (⊥ : ScottEndP B) = ⊥ then (Sum.inl markedB : GlueBaseGen (ScottEndP B))
        else Sum.inr (Sum.inl (⊥ : ScottEndP B))) = Sum.inl markedB
  rw [if_pos rfl]

/-- The tag-`C` copy of `⊥` is the tag-`A` copy of `⊤`. -/
theorem tagC_bot_eq_top :
    tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)
      = tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊤ : ScottEndP B) := by
  refine Subtype.ext ?_
  show (if (⊥ : ScottEndP B) = ⊥ then (Sum.inl ⊤ : GlueBaseGen (ScottEndP B))
        else if (⊥ : ScottEndP B) = markedB then Sum.inr (Sum.inl ⊤)
        else Sum.inr (Sum.inr (⊥ : ScottEndP B))) = Sum.inl ⊤
  rw [if_pos rfl]

/-- `⊥` of `B` is the tag-`A` copy of `⊥`, transported by `sec`. -/
theorem sec_tagA_bot :
    sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)) = (⊥ : B) := by
  have h := SigmaRebuild.sigmaA_bot
  show sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)) = (⊥ : B)
  rw [← strictConst_bot]
  exact h

theorem ifsS_sigmaB_bot :
    ifsS.sigmaB (⊥ : B)
      = sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top markedB) := by
  show sec (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (strictConst (⊥ : B))) = _
  rw [strictConst_bot, tagB_bot_eq_mark]

theorem ifsS_sigmaC_bot :
    ifsS.sigmaC (⊥ : B)
      = sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊤ : ScottEndP B)) := by
  show sec (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (strictConst (⊥ : B))) = _
  rw [strictConst_bot, tagC_bot_eq_top]

theorem ifsS_sigmaB_bot_ne : ifsS.sigmaB (⊥ : B) ≠ (⊥ : B) := by
  intro hc
  rw [ifsS_sigmaB_bot, ← sec_tagA_bot] at hc
  exact markedB_ne_bot
    (tagPt_injective 0 markedB markedB_ne_bot endPB_bot_ne_top (sec_injective hc))

theorem ifsS_sigmaC_bot_ne : ifsS.sigmaC (⊥ : B) ≠ (⊥ : B) := by
  intro hc
  rw [ifsS_sigmaC_bot, ← sec_tagA_bot] at hc
  exact endPB_bot_ne_top
    (tagPt_injective 0 markedB markedB_ne_bot endPB_bot_ne_top (sec_injective hc)).symm

/-- `⊥` is fixed by `σ_A` only. -/
theorem bot_not_mem_fix_B : (⊥ : B) ∉ Fix ifsS.sigmaB := ifsS_sigmaB_bot_ne

theorem bot_not_mem_fix_C : (⊥ : B) ∉ Fix ifsS.sigmaC := ifsS_sigmaC_bot_ne

/-- **`ifsS` passes the necessary condition.**  `Fix σ_A` meets neither of the
other two fixed-point sets. -/
theorem ifsS_fix_disjoint_AB : Disjoint (Fix ifsS.sigmaA) (Fix ifsS.sigmaB) := by
  rw [Set.disjoint_left]
  intro a ha hb
  rw [EscapeProof.fix_sigmaA] at ha
  rw [show a = (⊥ : B) from ha] at hb
  exact bot_not_mem_fix_B hb

theorem ifsS_fix_disjoint_AC : Disjoint (Fix ifsS.sigmaA) (Fix ifsS.sigmaC) := by
  rw [Set.disjoint_left]
  intro a ha hc
  rw [EscapeProof.fix_sigmaA] at ha
  rw [show a = (⊥ : B) from ha] at hc
  exact bot_not_mem_fix_C hc

/-- **`base_pin`, concretely.**  Any equivariant `ρ` out of `B` sends `⊥` to the
`A`-vertex of the gasket. -/
theorem rho_bot {rho : B → Gamma}
    (hA : ∀ x, rho (ifsS.sigmaA x) = fA (rho x)) : rho (⊥ : B) = gA :=
  rho_eq_gA hA SigmaRebuild.sigmaA_bot

end Gasket
