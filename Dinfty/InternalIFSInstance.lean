import Dinfty.PhiSurjective
import Dinfty.CoreIFS

open GluingTowerLibrary SierpinskiApplication

/-!
# The honest internal IFS on `D∞^Φ`

`CoreIFS.lean`'s header says why it was left without an instance:

> The concrete instantiation `dInftyCoreIFS` depended on the honest
> `σ_A/σ_B/σ_C : D∞ → D∞` that only the (false) iso `D∞ ≃ F(D∞)` could supply —
> with just the retract `(Psi, PsiInv)` those maps degenerate.  …  Reusable if an
> honest internal IFS on `D∞` is ever constructed.

`PhiSurjective.theoremA_orderIso` is such an isomorphism, so this module
constructs it.  `InternalIFS.lean`'s note is thereby discharged.

## What is proved here

* `ifsB : InternalIFS B` — the three copy-inclusions of `Φ`, read back through
  the isomorphism.
* **All three `σ` are injective on all of `B`** (`sigmaA/B/C_injective`).  This
  is strictly stronger than `TheoremAPipe`'s `sigmaA_injective` /
  `sigmaB_injOn`, which had to exclude the redirect `tag_B ⊥ ↦ tag_A m`: with
  `GlueTag.unTag` as an explicit left inverse, each `canonGen ∘ tagInj t` is
  injective *including* at its redirects, so no domain restriction is needed.
  Injectivity is exactly what the retract could not give.
* `sigmaA_bot` — copy `A`'s map fixes `⊥`, i.e. `⊥ ∈ Fix σ_A`.  (The converse
  inclusion, `Fix σ_A ⊆ {⊥}` — the companion note's Theorem ESCAPE — is *not*
  proved here.)

## What is still missing, and it is not order theory

`CoreIFS` additionally wants a carrier topology and a target space `Γ` with
three maps `f_A/f_B/f_C`, and `TheoremAData` wants `ρ : Core → Γ` continuous,
open, surjective and equivariant.  `Γ` is the Sierpiński gasket and `ρ` the
coding map; neither exists in this repository, and constructing them is
analysis, not order theory.

**A degenerate instance would be worthless and must not be built.**  Because
`Γ`, `f_A/f_B/f_C` are abstract parameters of `CoreIFS`, one *can* satisfy
`TheoremAData` by taking `Γ := B`, `f_j := σ_j` and `ρ := id`.  That typechecks
and proves nothing: `theorem_A` would then say only that the identity is the
unique continuous equivariant surjection `B → B`.  The content of Theorem A is
that `Γ` is the *gasket*.  Do not instantiate `CoreIFS` until a real `Γ` is
available.

What `CoreIFS` already supplies for that day is real, though:
`theoremA_unique_of_ingredients` proves `TheoremAData.unique` from
`Subsingleton (Fix K.fA)` (Banach) plus density of the orbit, and
`orbit_countable` / `agree_on_orbit` / `base_pin` are all in place.
-/

namespace InternalIFSInstance

open PhiIterateTower PhiBilimit GlueTag GenContinuity

attribute [-instance] OrderHom.instDecidableEqOfForall

/-- The isomorphism `Φ(D∞^Φ) ≃o D∞^Φ`, used as the section that reads the three
copy-inclusions back into the carrier. -/
noncomputable def sec : PhiBilimit.phiB ≃o B := PhiSurjective.theoremA_orderIso

theorem sec_injective : Function.Injective sec := sec.injective

theorem sec_surjective : Function.Surjective sec := sec.surjective

/-! ## Two small injectivity inputs -/

theorem constS_injective : Function.Injective (constS : B → ScottEndP B) := by
  intro x y h
  exact congrArg (fun F : ScottEndP B => F.1 botB) h

theorem constS_bot : constS (⊥ : B) = (⊥ : ScottEndP B) := rfl

/-! ## The glue bottom -/

theorem tagA_bot_le_raw (v : GlueBaseGen (ScottEndP B)) :
    leGlueGen markedB (Sum.inl (⊥ : ScottEndP B)) v := by
  refine ⟨Sum.inl (⊥ : ScottEndP B), self_mem_occsGen _ _, v, self_mem_occsGen _ _, ?_⟩
  cases v with
  | inl _ => exact bot_le
  | inr w => cases w with
    | inl _ => exact bot_le
    | inr _ => trivial

theorem tagA_bot_le (z : PhiBilimit.phiB) :
    tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B) ≤ z :=
  tagA_bot_le_raw z.1

/-! ## The internal IFS -/

/-- **The honest internal IFS on `D∞^Φ`.**  `σ_j` is `Φ`'s `j`-th copy-inclusion
of the constant endomorphism at `x`, read back through the isomorphism. -/
noncomputable def ifsB : InternalIFS B where
  sigmaA x := sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (constS x))
  sigmaB x := sec (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (constS x))
  sigmaC x := sec (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (constS x))

@[simp] theorem sigmaA_apply (x : B) :
    ifsB.sigmaA x = sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (constS x)) := rfl

@[simp] theorem sigmaB_apply (x : B) :
    ifsB.sigmaB x = sec (tagPt 1 markedB markedB_ne_bot endPB_bot_ne_top (constS x)) := rfl

@[simp] theorem sigmaC_apply (x : B) :
    ifsB.sigmaC x = sec (tagPt 2 markedB markedB_ne_bot endPB_bot_ne_top (constS x)) := rfl

/-! ## Injectivity — on all of `B`, for all three copies -/

private theorem sigma_inj (t : ℕ) {x y : B}
    (h : sec (tagPt t markedB markedB_ne_bot endPB_bot_ne_top (constS x))
       = sec (tagPt t markedB markedB_ne_bot endPB_bot_ne_top (constS y))) : x = y :=
  constS_injective
    (tagPt_injective t markedB markedB_ne_bot endPB_bot_ne_top (sec_injective h))

theorem sigmaA_injective : Function.Injective ifsB.sigmaA := fun _ _ h => sigma_inj 0 h
theorem sigmaB_injective : Function.Injective ifsB.sigmaB := fun _ _ h => sigma_inj 1 h
theorem sigmaC_injective : Function.Injective ifsB.sigmaC := fun _ _ h => sigma_inj 2 h

/-! ## `⊥` is fixed by copy `A` -/

theorem sigmaA_bot : ifsB.sigmaA (⊥ : B) = ⊥ := by
  refine le_antisymm ?_ bot_le
  obtain ⟨z, hz⟩ := sec_surjective (⊥ : B)
  show sec (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top (⊥ : ScottEndP B)) ≤ (⊥ : B)
  rw [← hz]
  exact sec.monotone (tagA_bot_le z)

theorem bot_mem_fix_sigmaA : (⊥ : B) ∈ Fix ifsB.sigmaA := sigmaA_bot

/-! ## `sec`'s coordinates are the projection legs

These four are generic facts about `sec` and the cocone's legs — nothing to do
with any particular choice of payload.  They live here, above the fork between
the `constS` IFS and the rebuilt one, so that no live result depends on the
refutation module. -/

theorem sec_apply_succ (z : PhiBilimit.phiB) (n : ℕ) :
    (sec z).1 (n + 1) = PhiCocone.pLeg n z := rfl

theorem sec_apply_zero (z : PhiBilimit.phiB) :
    (sec z).1 0 = phiTowerEP.prj 0 (PhiCocone.pLeg 0 z) := rfl

theorem projEndDown_markedB (j : ℕ) :
    (PhiCocone.projEndDown j).toFun markedB = markedPt (j + 1) := rfl

/-- `pLeg` of a tag-`A` point is tag `A` of the projected payload. -/
theorem pLeg_val (j : ℕ) (H : ScottEndP B) :
    (PhiCocone.pLeg j (tagPt 0 markedB markedB_ne_bot endPB_bot_ne_top H)).1
      = Sum.inl ((PhiCocone.projEndDown j).toFun H) :=
  congrArg Subtype.val (PhiSurjective.pLeg_tagPt j 0 H)

/-! ## Self-similarity, named -/

theorem selfSimilar : Nonempty (B ≃o PhiBilimit.phiB) := ⟨sec.symm⟩

end InternalIFSInstance
