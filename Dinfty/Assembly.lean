import Dinfty.JoinIrredLevelStable

open GluingTowerLibrary SierpinskiApplication

/-!
# Assembly scaffold: the pillars' reductions, compiled rather than narrated

`Meta/Status - Two Pillars (2026-08-28).md` claims each pillar reduces to one
open item.  That claim was about the mathematics; the *reductions themselves*
were prose.  This module compiles what can be compiled, and records precisely
what cannot.

## Pillar B — the reduction is now a theorem, not prose

`Colimit Compat Handoff.md` §3 argues informally: if each stage `toD k '' (D k)`
is order-definable inside `DInfty`, then any automorphism preserves it setwise,
restricts to an automorphism of `D k`, is the identity there by `D_all_rigid`,
and hence is the identity everywhere.

`colimit_rigid_of_stageDefinable` below **is that argument, in Lean**.  It had
never been formalized.  Two things are worth noting about how it goes through:

* it does not need the restriction to be an automorphism — only **monotone and
  injective**, which is weaker and easier to supply.  That is possible because
  of `TowerRigidity.D_monotone_injection_eq_id` (proved earlier today): on the
  finite, rigid `D k`, monotone + injective already forces the identity.  The
  §3 argument as written invokes `Aut(D k) = {id}`; the Lean proof invokes the
  strictly stronger embedding-rigidity, and is shorter for it.
* `StageDefinable` is stated in the weakest form that suffices — each stage maps
  *into* itself, not onto — since surjectivity is never used.

So pillar B's remaining content is exactly `StageDefinable`, and that is now a
named `Prop` with a proved consequence rather than a paragraph.

## What is still NOT compiled, stated exactly

* **The route from `NoCrossFiberTie` to `StageDefinable` is unwritten.**
  (An earlier version of this docstring said `NoCrossFiberTie` had no Lean
  statement.  **That was false** — `S5Invariant.lean:586` defines it as a `Prop`,
  deliberately a `def` rather than a `theorem` since it is known false for
  arbitrary `P` and open for `P := D_k`.  The claim came from a truncated grep.)
  What is missing is the implication: sub-problems #1/#2/#3 of handoff §7o are
  the intended path to `StageDefinable`, only #2 is fully closed, and
  `Dinfty/AssemblyChain.lean` now carries the shape of the rest.
* **Pillar A's identification — STALE AS WRITTEN, corrected 2026-08-29.**  This
  paragraph used to say `Φ_tri_v2` has no Lean definition and so pillar A is not
  statable.  That was true when written and is no longer: `Dinfty/PhiTri.lean`
  defines `TriPointed`, `Phi`, and `Phi.map`, and its `mapFun` is *literally*
  `GenContinuity.baseMapGen` — so the identification is definitional, not merely
  statable, and `Phi.map_id`/`Phi.map_comp` (ingredient 2) are proved.  Pillar
  A's remaining Lean content is ingredient 3, `Φ`'s local continuity on dcpos,
  which is informal and not finitely checkable, plus the Ψ-target marked-point
  question gated on mixed variance (`Dinfty/PsiTargetTripointed.lean`).

This asymmetry between the pillars was not visible before the scaffold was
attempted, and is the main thing it bought.
-/

open scoped Classical

namespace Assembly

/-- **Stage-definability**, in the weakest form the reduction needs: every
order-automorphism of `DInfty` carries each stage into itself.

Handoff §3 phrases this as the stages being *order-definable* — picked out by an
order-theoretic property, hence preserved by any automorphism.  That is a
sufficient condition for this `Prop`; this is the consequence actually used. -/
def StageDefinable : Prop :=
  ∀ (θ : DInfty ≃o DInfty) (k : ℕ) (x : D k), ∃ y : D k, θ (toD k x) = toD k y

/-- The stage maps are injective — from `toD_le_iff'` and antisymmetry. -/
theorem toD_inj (k : ℕ) : Function.Injective (toD k) := fun x y h =>
  le_antisymm ((toD_le_iff' k x y).mp (le_of_eq h))
    ((toD_le_iff' k y x).mp (le_of_eq h.symm))

/-- **Handoff §3's reduction, formalized.**  Stage-definability forces every
order-automorphism of `DInfty` to be the identity.

The restriction of `θ` to a stage is only shown monotone and injective — not
surjective, and not an isomorphism — because
`TowerRigidity.D_monotone_injection_eq_id` already forces such a map to be the
identity on the finite rigid `D k`. -/
theorem eq_refl_of_stageDefinable (hs : StageDefinable) (θ : DInfty ≃o DInfty) :
    θ = OrderIso.refl DInfty := by
  have key : ∀ (k : ℕ) (x : D k), θ (toD k x) = toD k x := by
    intro k
    choose f hf using hs θ k
    have hmono : Monotone f := by
      intro a b hab
      have h2 : θ (toD k a) ≤ θ (toD k b) := θ.monotone ((toD_le_iff' k a b).mpr hab)
      rw [hf a, hf b] at h2
      exact (toD_le_iff' k (f a) (f b)).mp h2
    have hinj : Function.Injective f := by
      intro a b hab
      have h1 : θ (toD k a) = θ (toD k b) := by rw [hf a, hf b, hab]
      exact toD_inj k (θ.injective h1)
    have hid : f = id := TowerRigidity.D_monotone_injection_eq_id k hmono hinj
    intro x
    rw [hf x, congrFun hid x]
    rfl
  refine RelIso.ext ?_
  intro z
  induction z using Quotient.inductionOn with
  | _ p => exact key p.1 p.2

/-- **Pillar B, reduced.**  Stage-definability gives `colimit_compat`'s open
half outright. -/
theorem colimit_rigid_of_stageDefinable (hs : StageDefinable) :
    Subsingleton (DInfty ≃o DInfty) :=
  ⟨fun a b => (eq_refl_of_stageDefinable hs a).trans
    (eq_refl_of_stageDefinable hs b).symm⟩

/-- And therefore the pillar-B conclusion, via the already-proven bridge. -/
theorem DBilimit_rigid_of_stageDefinable (hs : StageDefinable) :
    Subsingleton (DBilimit ≃o DBilimit) :=
  DBilimit_rigid_of_DInfty_rigid (colimit_rigid_of_stageDefinable hs)

end Assembly
