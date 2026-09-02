import Dinfty.EndLocalContinuity

open GluingTowerLibrary SierpinskiApplication

/-!
# The tower supplies the family: local continuity at the live `DBilimit`

`EndLocalContinuity` proves the `End` half of ingredient 3 conditionally — for
*any* family of deflations that is jointly directed and has pointwise suprema —
and records that "the tower supplies one is a statement about the tower and is
not proved here".

It is proved here, and almost entirely out of lemmas that were already on file.

## What was already there

`SierpinskiApplication` has the deflation family concretely, under the name of
its range:

* `insertAtLevel_monotone`, `insertAtLevel_le_self`, `insertAtLevel_chain_mono`;
* `chainSet y = Set.range fun n => insertAtLevel n (y.1 n)`;
* `chainSet_directedOn`, and **`chainSet_isLUB y : IsLUB (chainSet y) y`**.

`chainSet_isLUB` *is* `deflation_isLUB`'s pointwise-suprema hypothesis with
`δ∞ = id`, and joint directedness follows from `insertAtLevel_chain_mono` at
`k := max i j`.  Neither needed proving.

## What was missing, and it was one lemma

The family had never been bundled as a *map* `DBilimit → DBilimit`, so nothing
had been said about its Scott-continuity.  It factors as

    defl n  =  insertAtLevel n ∘ (· .1 n)

and both factors are Scott-continuous for reasons already in the library:

* `insertAtLevel n` has **finite domain** (`instFintypeD`), so
  `monotone_scottContinuous_of_finite_dom` applies — no completeness needed on
  the codomain;
* `(· .1 n)` is Scott-continuous by `IsLUB.dbilimit_apply`, which says exactly
  that a directed LUB is read levelwise.

That is the whole gap.  Note where the finiteness is spent: on the *level*
`D n`, never on `DBilimit`, so nothing here is a finite-level result in
disguise — the conclusion is about the bilimit.

## What this closes

* `end_defl_isLUB` — for every Scott-continuous `h : DBilimit → DBilimit`,
  `⨆ₙ δₙ ∘ h ∘ δₙ = h`, pointwise.  This is `deflation_isLUB` with its
  hypotheses discharged at the live tower.
* `endDefl_isLUB` — the same in `ScottEndP DBilimit`, the carrier the limit-side
  glue instantiation actually uses.
* `phi_endDefl_isLUB` — `Φ`'s morphism action carries that supremum, at
  copy-`A` points of `GlueCarGen (ScottEndP DBilimit) scottEndPId` — i.e. of
  `psiTargetOrder`, the live Ψ-target (`psiTargetOrder_eq`).

## What remains open

Ingredient 3 is local continuity of `Φ ∘ End` as a functor: this gives the
copy-`A` component at the tower's own deflation family.  Copies `B` and `C` do
**not** follow by analogy — their side conditions fail at this family, and
`endDefl_bot` is the witness.  They do follow on a **cofinal tail**, for every
`F ≠ ⊥`, which is enough for the supremum: see `Dinfty/DeflationCopies.lean`,
written after this module.
Ingredient 2 (`Φ_tri_v2`'s functor laws) is untouched, and the identification
of `Φ_tri_v2` with the `Gen` layer is untouched.  **Do not cite this as
ingredient 3.**  Cite it as: the tower supplies the family `EndLocalContinuity`
was conditional on, so that module's remaining hypothesis is discharged.

One caveat inherited rather than introduced: `psiTargetOrder`'s
`DecidableEq (ScottEndP DBilimit)` comes from `open scoped Classical`, the
`stepMap`/`glueJoinRaw` hazard, and this module runs through that instance.
-/

open scoped Classical

namespace DeflationContinuity

open EndLocalContinuity

/-! ## The deflation family as a map -/

/-- The `n`-th deflation of the bilimit: project to level `n`, insert back.
`SierpinskiApplication.chainSet` is the range of this, for fixed `y`. -/
noncomputable def defl (n : ℕ) (y : DBilimit) : DBilimit := insertAtLevel n (y.1 n)

theorem defl_monotone (n : ℕ) : Monotone (defl n) := fun _ _ h =>
  insertAtLevel_monotone n (h n)

noncomputable def deflHom (n : ℕ) : DBilimit →o DBilimit := ⟨defl n, defl_monotone n⟩

@[simp] theorem deflHom_apply (n : ℕ) (y : DBilimit) : deflHom n y = defl n y := rfl

/-- Reading a directed supremum at level `n` is Scott-continuous — this is
`IsLUB.dbilimit_apply` restated as continuity of the projection. -/
theorem proj_scottContinuous (n : ℕ) :
    ScottContinuous (fun y : DBilimit => y.1 n) := by
  intro S hne hdir a ha
  have hkey := ha.dbilimit_apply hne hdir n
  show IsLUB ((fun y : DBilimit => y.1 n) '' S) (a.1 n)
  rw [hkey]
  exact isLUB_sSup _

/-- `insertAtLevel n` is Scott-continuous because its **domain** `D n` is
finite, not because anything about `DBilimit` is. -/
theorem insertAtLevel_scottContinuous (n : ℕ) : ScottContinuous (insertAtLevel n) :=
  monotone_scottContinuous_of_finite_dom (insertAtLevel_monotone n)

theorem defl_scottContinuous (n : ℕ) : ScottContinuous (defl n) := by
  have h := (proj_scottContinuous n).comp (insertAtLevel_scottContinuous n)
  unfold defl
  simpa [Function.comp_def] using h

/-- The pointwise-suprema hypothesis, and it is `chainSet_isLUB`. -/
theorem defl_isLUB (y : DBilimit) : IsLUB (Set.range fun n => defl n y) y := by
  simpa [chainSet, defl] using chainSet_isLUB y

/-- The joint-directedness hypothesis, and it is `insertAtLevel_chain_mono`. -/
theorem defl_directed (i j : ℕ) :
    ∃ k, (∀ y, defl i y ≤ defl k y) ∧ (∀ y, defl j y ≤ defl k y) :=
  ⟨max i j, fun y => insertAtLevel_chain_mono y (le_max_left i j),
            fun y => insertAtLevel_chain_mono y (le_max_right i j)⟩

/-! ## The `End` half, unconditionally, at the live tower -/

/-- **`⨆ₙ δₙ ∘ h ∘ δₙ = h`, pointwise, for every Scott-continuous `h`.**

`EndLocalContinuity.deflation_isLUB` with all four hypotheses discharged: joint
directedness from `insertAtLevel_chain_mono`, pointwise suprema from
`chainSet_isLUB`, and Scott-continuity of each `δₙ` from the factorisation
above. -/
theorem end_defl_isLUB {h : DBilimit → DBilimit} (hh : ScottContinuous h)
    (x : DBilimit) :
    IsLUB (Set.range fun n => defl n (h (defl n x))) (h x) := by
  have hlub := deflation_isLUB (ι := ℕ) defl id h defl_directed defl_isLUB hh
    defl_scottContinuous x
  simpa using hlub

/-! ## The same in `ScottEndP DBilimit` -/

/-- The `End` action of the `n`-th deflation, on the carrier the limit-side
glue instantiation actually uses.  Well-defined because a composite of
Scott-continuous maps is Scott-continuous. -/
noncomputable def endDefl (n : ℕ) : ScottEndP DBilimit →o ScottEndP DBilimit where
  toFun F := ⟨(deflHom n).comp (F.1.comp (deflHom n)), by
    have h := ((defl_scottContinuous n).comp F.2).comp (defl_scottContinuous n)
    simpa [Function.comp_def] using h⟩
  monotone' _ _ hFG x := (deflHom n).monotone (hFG (defl n x))

@[simp] theorem endDefl_apply (n : ℕ) (F : ScottEndP DBilimit) (x : DBilimit) :
    (endDefl n F).1 x = defl n (F.1 (defl n x)) := rfl

/-- **The `End` half in `ScottEndP DBilimit`:** every `F` is the supremum of its
own deflation approximants. -/
theorem endDefl_isLUB (F : ScottEndP DBilimit) :
    IsLUB (Set.range fun n => endDefl n F) F := by
  constructor
  · rintro _ ⟨n, rfl⟩ x
    exact (end_defl_isLUB F.2 x).1 ⟨n, rfl⟩
  · intro w hw x
    refine (end_defl_isLUB F.2 x).2 ?_
    rintro _ ⟨n, rfl⟩
    exact hw ⟨n, rfl⟩ x

/-! ## Why only copy `A`

The copy-`B` and copy-`C` components of `Φ`'s local continuity carry side
conditions on the *values* of the family (`≠ ⊥` for `B`, and `≠ m` as well for
`C`).  Those conditions genuinely fail at this family, and the witness is
cheap: the deflations fix `⊥`, so at `F = ⊥` every approximant is `⊥`.  This is
recorded as a theorem rather than a remark so that nobody re-derives copy `B`
or `C` here by analogy with copy `A`. -/

section CopyALimit

theorem defl_bot (n : ℕ) : defl n (⊥ : DBilimit) = ⊥ :=
  le_antisymm (insertAtLevel_le_self ⊥ n) bot_le

/-- The deflation approximants of `⊥` are all `⊥`, so
`baseMapGen_isLUB_tagB`'s hypothesis `∀ i, g i a ≠ ⊥` is unsatisfiable at
`a = ⊥`, and likewise for copy `C`.  Copy `A` is the only one of the three that
applies to this family unconditionally. -/
theorem endDefl_bot (n : ℕ) : endDefl n (⊥ : ScottEndP DBilimit) = ⊥ := by
  apply Subtype.ext
  apply OrderHom.ext
  funext x
  show defl n ((⊥ : ScottEndP DBilimit).1 (defl n x)) = (⊥ : ScottEndP DBilimit).1 x
  rw [scottEndPBot_apply, scottEndPBot_apply, defl_bot]

end CopyALimit

/-! ## Through `Φ`'s morphism action, at the live Ψ-target -/

theorem psiTargetOrder_eq :
    psiTargetOrder = glueCarPartialOrderGen scottEndPId scottEndPId_ne_bot
      scottEndPId_ne_top scottEndPBot_ne_top := rfl

/-- **`Φ`'s morphism action carries the deflation supremum, at copy-`A` points
of the live Ψ-target.**

`EndLocalContinuity.baseMapGen_isLUB_tagA` instantiated at
`P = P' = ScottEndP DBilimit` with `m' = scottEndPId` — the same data
`psiTargetOrder` is built from (`psiTargetOrder_eq`).

This is one copy of one direction, not ingredient 3; see the module
docstring. -/
theorem phi_endDefl_isLUB (F : ScottEndP DBilimit) :
    letI := glueCarPartialOrderGen scottEndPId scottEndPId_ne_bot
      scottEndPId_ne_top scottEndPBot_ne_top
    IsLUB (Set.range fun n => tagAGen scottEndPId (endDefl n F))
      (tagAGen scottEndPId F) :=
  baseMapGen_isLUB_tagA scottEndPId scottEndPId_ne_bot scottEndPId_ne_top
    scottEndPBot_ne_top endDefl id (fun a => endDefl_isLUB a) F

end DeflationContinuity
