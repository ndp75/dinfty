import Dinfty.SigmaRebuild

open GluingTowerLibrary SierpinskiApplication

/-!
# `qAA` explicitly — and a retraction

§97 said the base projection `qAA 0` is "`Exists.choose`-opaque" and that the
next step was to give it an explicit formula.  **That was wrong on both counts:
`qAA` was never a choice.**  `GlueAAEpPartner` defines it outright,

```lean
noncomputable def qAA (k : ℕ) : D (k + 2) → D (k + 1) := EpFromJoin.upper (glueAA k)
```

and `EpFromJoin.upper l y` is the `Finset.sup` of `{x | l x ≤ y}`.  Only
`exists_glueAA_epPartner` — a *different*, unused declaration — is existential.
`GlueAAJoin.glueAAJoinPreserving` is unconditional, so every hypothesis
`EpFromJoin` needs is discharged and the whole adjoint API applies.

## The formula, in the form that is actually usable

The `Finset.sup` spelling drags `EpFromJoin`'s `open scoped Classical`
`DecidablePred` instance around with it.  The instance-free description is
better and equivalent:

```lean
qAA_isGreatest : IsGreatest {y | glueAA k y ≤ z} (qAA k z)
```

`qAA k z` is *the greatest `y` with `glueAA k y ≤ z`* — which pins it uniquely
(`eq_qAA_of_isGreatest`) — together with the Galois connection
`glueAA k y ≤ z ↔ y ≤ qAA k z`.

## What it buys for ESCAPE

`phiTowerEP.prj 0` **is** `qAA 0`, definitionally, so the level-`0` coordinate of
any bilimit point is the greatest thing `glueAA 0` puts under its level-`1`
coordinate (`level_zero_isGreatest`).  For a fixed point of the rebuilt `σ_A`
the level-`1` coordinate is computed (`fix_level_one`), and the payload is
pinned: it is the strict constant at `x.1 j`
(`projEndDown_strictConst_bot` / `_ne`).  Put together, `fix_level_zero` states
the base equation with nothing opaque left in it.

What remains is a question about `glueAA 0` on the 27-element `D 1`, not about
the projection.
-/

namespace QAAExplicit

open PhiIterateTower PhiBilimit GlueAAEpPartner GlueTag GenContinuity

attribute [-instance] OrderHom.instDecidableEqOfForall

/-! ## `qAA` is a definition, not a choice -/

theorem qAA_eq (k : ℕ) : qAA k = EpFromJoin.upper (glueAA k) := rfl

theorem glueAA_qAA_le (k : ℕ) (z : D (k + 2)) : glueAA k (qAA k z) ≤ z :=
  EpFromJoin.map_upper_le (glueAA k) (glueAA_bot k) (GlueAAJoin.glueAAJoinPreserving k) z

theorem le_qAA (k : ℕ) {y : D (k + 1)} {z : D (k + 2)} (h : glueAA k y ≤ z) : y ≤ qAA k z :=
  EpFromJoin.le_upper (glueAA k) y z h

/-- **The explicit description.**  `qAA k z` is the greatest `y` with
`glueAA k y ≤ z`.  Instance-free, and it determines `qAA` uniquely. -/
theorem qAA_isGreatest (k : ℕ) (z : D (k + 2)) :
    IsGreatest {y : D (k + 1) | glueAA k y ≤ z} (qAA k z) :=
  ⟨glueAA_qAA_le k z, fun _ hy => le_qAA k hy⟩

theorem eq_qAA_of_isGreatest (k : ℕ) {z : D (k + 2)} {y : D (k + 1)}
    (h : IsGreatest {y : D (k + 1) | glueAA k y ≤ z} y) : y = qAA k z :=
  h.unique (qAA_isGreatest k z)

/-- The Galois connection, named. -/
theorem glueAA_le_iff_le_qAA (k : ℕ) (y : D (k + 1)) (z : D (k + 2)) :
    glueAA k y ≤ z ↔ y ≤ qAA k z :=
  ⟨le_qAA k, fun h => le_trans (glueAA_monotone k h) (glueAA_qAA_le k z)⟩

/-! ## The tower's base projection *is* this map -/

theorem prj_zero_eq : phiTowerEP.prj 0 = qAA 0 := rfl

/-- Every bilimit point's level-`0` coordinate is the greatest thing `glueAA 0`
puts under its level-`1` coordinate. -/
theorem level_zero_isGreatest (x : B) :
    IsGreatest {y : D 1 | glueAA 0 y ≤ x.1 1} (x.1 0) := by
  have h : qAA 0 (x.1 1) = x.1 0 := x.2 0
  rw [← h]
  exact qAA_isGreatest 0 (x.1 1)

/-! ## The payload of a strict constant, pinned -/

theorem ins_eq_bot_iff (j : ℕ) (w : D (j + 1)) :
    phiTowerEP.ins j w = (⊥ : B) ↔ w = (⊥ : D (j + 1)) := by
  constructor
  · intro h
    have h2 := congrArg (fun z : B => z.1 j) h
    rw [EpPairTower.ins_self] at h2
    exact h2
  · intro h
    rw [h]
    exact ins_bot j

theorem projEndDown_strictConst_bot (j : ℕ) (c : B) :
    ((PhiCocone.projEndDown j).toFun (SigmaRebuild.strictConst c)) (⊥ : D (j + 1))
      = (⊥ : D (j + 1)) := by
  show (SigmaRebuild.strictFun c (phiTowerEP.ins j (⊥ : D (j + 1)))).1 j = (⊥ : D (j + 1))
  rw [ins_bot j, SigmaRebuild.strictFun_bot_case (rfl : botB = ⊥)]
  rfl

theorem projEndDown_strictConst_ne (j : ℕ) (c : B) {w : D (j + 1)}
    (hw : w ≠ (⊥ : D (j + 1))) :
    ((PhiCocone.projEndDown j).toFun (SigmaRebuild.strictConst c)) w = c.1 j := by
  have hne : phiTowerEP.ins j w ≠ (⊥ : B) := fun h => hw ((ins_eq_bot_iff j w).mp h)
  show (SigmaRebuild.strictFun c (phiTowerEP.ins j w)).1 j = c.1 j
  rw [SigmaRebuild.strictFun_ne_case hne]

/-! ## The base equation for a fixed point of the rebuilt `σ_A`, with nothing
opaque in it -/

theorem fix_level_one {x : B} (hx : SigmaRebuild.ifsS.sigmaA x = x) :
    (x.1 1).1 = Sum.inl ((PhiCocone.projEndDown 0).toFun (SigmaRebuild.strictConst x)) := by
  have h1 : ((SigmaRebuild.ifsS.sigmaA x).1 1).1 = (x.1 1).1 :=
    congrArg (fun z : B => (z.1 1).1) hx
  rw [← h1]
  exact InternalIFSInstance.pLeg_val 0 (SigmaRebuild.strictConst x)

/-- **The base equation.**  `x.1 0` is the greatest `y : D 1` that `glueAA 0`
sends below the copy-`A` point whose payload is the strict constant at
`x.1 0`. -/
theorem fix_level_zero {x : B} (hx : SigmaRebuild.ifsS.sigmaA x = x) :
    IsGreatest {y : D 1 | glueAA 0 y ≤ x.1 1} (x.1 0)
      ∧ (x.1 1).1 = Sum.inl ((PhiCocone.projEndDown 0).toFun (SigmaRebuild.strictConst x))
      ∧ ((PhiCocone.projEndDown 0).toFun (SigmaRebuild.strictConst x)) (⊥ : D 1) = ⊥
      ∧ ∀ w : D 1, w ≠ ⊥ →
          ((PhiCocone.projEndDown 0).toFun (SigmaRebuild.strictConst x)) w = x.1 0 :=
  ⟨level_zero_isGreatest x, fix_level_one hx, projEndDown_strictConst_bot 0 x,
    fun w hw => projEndDown_strictConst_ne 0 x hw⟩

end QAAExplicit
