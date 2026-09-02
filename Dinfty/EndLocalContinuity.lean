import Dinfty.GenContinuityTransport

open GluingTowerLibrary SierpinskiApplication

/-!
# Gap 2 of `GenContinuity`: the mixed-variance (`End`) half

`GenContinuity` reduces local continuity of `Φ`'s morphism action to
Scott-continuity of the three copy-inclusions, and `GenContinuityTransport`
transports all three into `GlueCarGen`.  Its second recorded gap is the other
factor of the composite:

> **Mixed variance.**  This covers `Φ`'s action on hom-sets.  Ingredient 3 as
> cited is local continuity of `Φ ∘ End` on an O-category, and `End` is
> mixed-variance — contravariant in its first argument.  Nothing here touches
> the `End` half.

This module is the `End` half, and the composition step.

## Why the variance is not the obstruction it looks like

`End(D) = [D → D]` is the diagonal of the hom-bifunctor
`(A, B) ↦ [A → B]`, contravariant in `A` and covariant in `B`, with action
`(f, g) ↦ (h ↦ g ∘ h ∘ f)` for `f : A' → A` and `g : B → B'`.  Local continuity
is continuity of that assignment in the pair `(f, g)` — and in that
presentation *both* slots are covariant, the contravariance having been
absorbed into `A'`.

The reason this matters concretely: for an embedding-projection pair
`(e, p)`, `e ⊑ e'` is equivalent to `p ⊒ p'`, so a family of ep-pairs that
increases in its embeddings *decreases* in its projections, and
`(e, p) ↦ e ∘ h ∘ p` is not monotone along it.  What ingredient 3 actually
uses is not that family: it is the family of **deflations** `δ i = e i ∘ p i :
D∞ → D∞`, which increases to `id`, and which occupies *both* slots at once
(`deflation_isLUB`).  `comp_isLUB` is stated for independent families so that
the hypothesis doing the work — the two families being directed *together* —
is visible rather than hidden by the diagonal.

## What is proved

* `comp_isLUB` — the hom-bifunctor action `(f, g) ↦ g ∘ h ∘ f` preserves
  directed suprema, over arbitrary preorders, stated pointwise so that no
  function-space cpo structure is needed.  This is the `End` half.
* `deflation_isLUB` — the diagonal instance, `F = G = δ`: the shape the
  bilimit argument uses.
* `isLUB_orderHom_of_pointwise` — pointwise suprema *are* suprema in the
  pointwise-ordered hom-poset.  This is the bridge that turns the pointwise
  output of `comp_isLUB` into the hypothesis `baseMapGen_isLUB_tagA` wants.
* `endHom`, `endHom_isLUB` — the `End` action bundled as an `OrderHom`, and its
  local continuity in the bundled form.
* `baseMapGen_isLUB_tagA` / `_tagB` / `_tagC` — the `Φ` half, in `GlueCarGen`:
  the morphism action preserves suprema of a pointwise-directed family of
  morphisms, at points of each copy.  Copy `A` is unconditional; copies `B`
  and `C` carry the canon-fixed side conditions on the family's values.
* `phiEnd_isLUB_tagA` — the two halves composed.

## What is NOT proved, and the mismatch this exposes

1. **`ScottContinuous h` is a hypothesis, and it is discharged by the carrier,
   not by this module.**  `comp_isLUB` needs the endomorphism being transported
   to be Scott-continuous.  The *finite-level* tower is built on
   `EndP P = P →o P`, all monotone self-maps; the *limit-side* instantiation is
   already built on `ScottEndP`, where the hypothesis holds by construction —
   `SierpinskiApplication.psiTargetOrder` instantiates `glueCarPartialOrderGen`
   at `P := ScottEndP DBilimit`, with `scottEndPId`, `scottEndPId_ne_bot`,
   `scottEndPId_ne_top` and `scottEndPBot_ne_top` supplying `m`, `hm`, `hmt`,
   `hbt`.  At finite levels the two carriers coincide anyway: a monotone map on
   a finite poset is Scott-continuous, since directed subsets attain their sups.
   So this is an alignment between two constructions the project already has,
   **not** a missing one.  (An earlier draft of this docstring called it a new
   obligation on the grounds that "the tower is built on `EndP`".  That was
   wrong: it read the finite-level carrier and missed `psiTargetOrder`.)
2. **The tower's deflations — DISCHARGED in `Dinfty/DeflationContinuity.lean`,
   after this module was written.**  Everything here is conditional on a family
   with pointwise suprema and joint directedness.  The live tower supplies one:
   `SierpinskiApplication.chainSet_isLUB` *is* the pointwise-suprema hypothesis
   and `insertAtLevel_chain_mono` gives joint directedness, both already on
   file.  The only piece that had to be proved was Scott-continuity of
   `δ n = insertAtLevel n ∘ (· .1 n)`, from
   `monotone_scottContinuous_of_finite_dom` (finite *level*, not finite
   bilimit) and `IsLUB.dbilimit_apply`.  See `DeflationContinuity.end_defl_isLUB`
   and, for why only copy `A` follows, `DeflationContinuity.endDefl_bot`.
3. **Instance hygiene at the instantiation.**  `phiEnd_isLUB_tagA` keeps
   `[DecidableEq P]` as a hypothesis rather than instantiating `P` at a hom-type
   via `Classical.decEq`, deliberately: `canonGen` is defined by
   `DecidableEq`-guarded branches, and freezing a classical instance into them
   is the defect recorded for `stepMap`/`glueJoinRaw`.  A caller instantiating
   at `ScottEndP D` must supply a `DecidableEq` that matches the one the
   `GlueCarGen` side already uses.

So: gap 2's `End` half is discharged, the composition step is proved, and
(since `DeflationContinuity`) the family it is conditional on is supplied by the
live tower.  Ingredient 3 remains open: what is missing is ingredient 2 and the
identification of the `Gen`-layer morphism action with `Φ_tri_v2`, not the
continuity content.
-/

open scoped Classical

open Set

universe u v

namespace EndLocalContinuity

/-! ## The mixed-variance core -/

section MixedVariance

variable {ι : Type v} [Nonempty ι]
variable {X Y Z W : Type u} [Preorder X] [Preorder Y] [Preorder Z] [Preorder W]

/-- **The `End` half.**  The hom-bifunctor action `(f, g) ↦ g ∘ h ∘ f` preserves
suprema of a jointly directed family, at every point.

Stated pointwise on plain preorders: no dcpo instance, no function-space cpo,
no finiteness, and no induction.  `fLim` and `gLim` are given only by their
defining pointwise `IsLUB` properties, so neither has to be built.

The two halves of the proof use different hypotheses, which is worth seeing:

* the **upper bound** half needs only monotonicity — `F i x ≤ fLim x`, then `h`
  and `G i` monotone, then `G i y ≤ gLim y`.  Directedness plays no role;
* the **leastness** half is where both Scott-continuity and joint directedness
  are spent.  `h` carries the sup of `{F i x}` (`hh`), `G j` carries the sup of
  the image (`hGc j`), and then the double family `G j (h (F i x))` is
  collapsed to its diagonal by choosing, for each `(i, j)`, a `k` dominating
  `F i` and `G j` at once.  That last step is precisely where a family
  increasing in one slot and decreasing in the other would fail. -/
theorem comp_isLUB
    (F : ι → X → Y) (G : ι → Z → W) (h : Y → Z) (fLim : X → Y) (gLim : Z → W)
    (hdir : ∀ i j : ι, ∃ k : ι, (∀ x, F i x ≤ F k x) ∧ (∀ x, F j x ≤ F k x)
      ∧ (∀ z, G i z ≤ G k z) ∧ (∀ z, G j z ≤ G k z))
    (hF : ∀ x, IsLUB (Set.range fun i => F i x) (fLim x))
    (hG : ∀ z, IsLUB (Set.range fun i => G i z) (gLim z))
    (hh : ScottContinuous h) (hGc : ∀ i, ScottContinuous (G i)) (x : X) :
    IsLUB (Set.range fun i => G i (h (F i x))) (gLim (h (fLim x))) := by
  have hhm : Monotone h := hh.monotone
  have hGm : ∀ i, Monotone (G i) := fun i => (hGc i).monotone
  have hDne : (Set.range fun i => F i x).Nonempty :=
    ⟨F (Classical.arbitrary ι) x, ⟨_, rfl⟩⟩
  have hDdir : DirectedOn (· ≤ ·) (Set.range fun i => F i x) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk, -, -⟩ := hdir i j
    exact ⟨F k x, ⟨k, rfl⟩, hik x, hjk x⟩
  have hhD : IsLUB (h '' Set.range fun i => F i x) (h (fLim x)) := hh hDne hDdir (hF x)
  have hhDne : (h '' Set.range fun i => F i x).Nonempty := hDne.image h
  have hhDdir : DirectedOn (· ≤ ·) (h '' Set.range fun i => F i x) :=
    directedOn_image_of_monotone hhm hDdir
  constructor
  · rintro _ ⟨i, rfl⟩
    exact le_trans (hGm i (hhm ((hF x).1 ⟨i, rfl⟩))) ((hG (h (fLim x))).1 ⟨i, rfl⟩)
  · intro w hw
    refine (hG (h (fLim x))).2 ?_
    rintro _ ⟨j, rfl⟩
    have hjD : IsLUB (G j '' (h '' Set.range fun i => F i x)) (G j (h (fLim x))) :=
      hGc j hhDne hhDdir hhD
    refine hjD.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hy
    obtain ⟨k, hFik, -, -, hGjk⟩ := hdir i j
    calc G j (h (F i x)) ≤ G k (h (F i x)) := hGjk _
      _ ≤ G k (h (F k x)) := hGm k (hhm (hFik x))
      _ ≤ w := hw ⟨k, rfl⟩

/-- **The diagonal instance — the shape ingredient 3 uses.**  Both slots of the
hom-bifunctor receive the *same* increasing family of deflations `δ i`, so the
joint-directedness hypothesis of `comp_isLUB` is just directedness of that one
family, and the mixed variance costs nothing.

This is the local-continuity step of the classical bilimit argument
(`id = ⨆ δ i` pushed through the functor), with `dLim` left abstract. -/
theorem deflation_isLUB {D : Type u} [Preorder D]
    (δ : ι → D → D) (dLim : D → D) (h : D → D)
    (hdir : ∀ i j : ι, ∃ k : ι, (∀ x, δ i x ≤ δ k x) ∧ (∀ x, δ j x ≤ δ k x))
    (hδ : ∀ x, IsLUB (Set.range fun i => δ i x) (dLim x))
    (hh : ScottContinuous h) (hδc : ∀ i, ScottContinuous (δ i)) (x : D) :
    IsLUB (Set.range fun i => δ i (h (δ i x))) (dLim (h (dLim x))) :=
  comp_isLUB δ δ h dLim dLim
    (fun i j => by obtain ⟨k, h1, h2⟩ := hdir i j; exact ⟨k, h1, h2, h1, h2⟩)
    hδ hδ hh hδc x

end MixedVariance

/-! ## The variance fact itself, machine-checked

The module docstring's claim about why the variance matters is not narrated
here: it is proved.  `ep_le_iff` says that along embedding-projection pairs the
two slots of the hom-bifunctor move in *opposite* directions, so a family of
ep-pairs is never jointly directed unless it is constant.  That is precisely
why `comp_isLUB` is applied at the deflations (`deflation_isLUB`), where one
family occupies both slots, and not at the ep-pairs themselves. -/

section Variance

variable {A B : Type u} [PartialOrder A] [PartialOrder B]

/-- **Embeddings increase exactly when projections decrease.**

For two ep-pairs `(e, p)`, `(e', p') : A ◁ B` — `p ∘ e = id`, `e ∘ p ≤ id` —
the embeddings are ordered one way and the projections the other.

Forward: `p' b = p (e (p' b)) ≤ p (e' (p' b)) ≤ p b`, using `p ∘ e = id`, then
`e ≤ e'`, then `e' ∘ p' ≤ id`.  Backward is the adjunction `e a ≤ b ↔ a ≤ p b`
run at `b = e' a`: `a = p' (e' a) ≤ p (e' a)`, hence `e a ≤ e (p (e' a)) ≤ e' a`. -/
theorem ep_le_iff (e e' : A →o B) (p p' : B →o A)
    (hpe : ∀ a, p (e a) = a) (hep : ∀ b, e (p b) ≤ b)
    (hpe' : ∀ a, p' (e' a) = a) (hep' : ∀ b, e' (p' b) ≤ b) :
    (∀ a, e a ≤ e' a) ↔ (∀ b, p' b ≤ p b) := by
  constructor
  · intro hee b
    calc p' b = p (e (p' b)) := (hpe (p' b)).symm
      _ ≤ p (e' (p' b)) := p.monotone (hee (p' b))
      _ ≤ p b := p.monotone (hep' b)
  · intro hpp a
    calc e a ≤ e (p (e' a)) := e.monotone (by simpa [hpe' a] using hpp (e' a))
      _ ≤ e' a := hep (e' a)

end Variance

/-! ## The bridge: pointwise suprema are hom-poset suprema -/

section Bridge

variable {ι : Type v}
variable {X Y : Type u} [Preorder X] [PartialOrder Y]

/-- Pointwise `IsLUB` gives `IsLUB` in the pointwise order on `X →o Y`.

This is what makes the two halves composable: `comp_isLUB` produces its
conclusion one point at a time, while the `Φ` half consumes a family of
morphisms.  Nothing here needs the supremum to be *constructed* — it is given
as an `OrderHom` and only its pointwise property is used. -/
theorem isLUB_orderHom_of_pointwise (u : ι → (X →o Y)) (s : X →o Y)
    (h : ∀ x, IsLUB (Set.range fun i => (u i) x) (s x)) :
    IsLUB (Set.range u) s := by
  constructor
  · rintro _ ⟨i, rfl⟩
    exact OrderHom.le_def.mpr fun x => (h x).1 ⟨i, rfl⟩
  · intro w hw
    refine OrderHom.le_def.mpr fun x => (h x).2 ?_
    rintro _ ⟨i, rfl⟩
    exact OrderHom.le_def.mp (hw ⟨i, rfl⟩) x

end Bridge

/-! ## The `End` action, bundled -/

section EndAction

variable {ι : Type v} [Nonempty ι]
variable {D D' : Type u} [PartialOrder D] [PartialOrder D']

/-- The `End` functor's action on hom-sets, bundled: `h ↦ e ∘ h ∘ p`.

Monotone in `h`, which is all the bundling needs; monotonicity in `(e, p)` is
the *local* structure and is `comp_isLUB`'s subject, not this definition's. -/
def endHom (e : D →o D') (p : D' →o D) : (D →o D) →o (D' →o D') where
  toFun h := e.comp (h.comp p)
  monotone' _ _ hab := OrderHom.le_def.mpr fun x => e.monotone (OrderHom.le_def.mp hab (p x))

@[simp] theorem endHom_apply (e : D →o D') (p : D' →o D) (h : D →o D) (x : D') :
    endHom e p h x = e (h (p x)) := rfl

/-- **The `End` half in bundled form.**  For a family of ep-pair components that
is directed jointly in both slots, the `End` action preserves suprema in the
hom-poset `D' →o D'`.

The supremum `gLim` is supplied as an `OrderHom` together with its pointwise
property; `comp_isLUB` gives the pointwise statement and
`isLUB_orderHom_of_pointwise` lifts it. -/
theorem endHom_isLUB
    (e : ι → (D →o D')) (p : ι → (D' →o D)) (eLim : D →o D') (pLim : D' →o D)
    (h : D →o D) (gLim : D' →o D')
    (hdir : ∀ i j : ι, ∃ k : ι, (∀ x, p i x ≤ p k x) ∧ (∀ x, p j x ≤ p k x)
      ∧ (∀ z, e i z ≤ e k z) ∧ (∀ z, e j z ≤ e k z))
    (hp : ∀ x, IsLUB (Set.range fun i => (p i) x) (pLim x))
    (he : ∀ z, IsLUB (Set.range fun i => (e i) z) (eLim z))
    (hh : ScottContinuous (h : D → D)) (hec : ∀ i, ScottContinuous ((e i : D → D')))
    (hgLim : ∀ x, gLim x = eLim (h (pLim x))) :
    IsLUB (Set.range fun i => endHom (e i) (p i) h) gLim := by
  refine isLUB_orderHom_of_pointwise _ _ (fun x => ?_)
  have := comp_isLUB (fun i => (p i : D' → D)) (fun i => (e i : D → D'))
    (h : D → D) (pLim : D' → D) (eLim : D → D') hdir hp he hh hec x
  simpa [hgLim x] using this

end EndAction

/-! ## The `Φ` half, in `GlueCarGen`, and the composite -/

section PhiSide

open GenContinuity

variable {ι : Type v} [Nonempty ι]
variable {P : Type u} [DecidableEq P] [PartialOrder P] [BoundedOrder P]
variable {P' : Type u} [DecidableEq P'] [PartialOrder P'] [BoundedOrder P']

theorem image_range_eq {α β γ : Type*} (f : α → β) (u : γ → α) :
    f '' (Set.range u) = Set.range fun i => f (u i) := by
  ext y
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩

/-- **`Φ`'s morphism action is locally continuous at copy-`A` points**, as an
`IsLUB` statement in `GlueCarGen m'`.

`baseMapGen` is tagwise, so this is `tagAGen_isLUB` applied to the family's
values at `a` — which is `GenContinuity`'s reduction (`baseMapGen_range_eq`)
being cashed in.  Unconditional: copy `A` is the total inclusion. -/
theorem baseMapGen_isLUB_tagA (m' : P') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) (g : ι → (P →o P')) (gLim : P → P')
    (hg : ∀ a, IsLUB (Set.range fun i => (g i) a) (gLim a)) (a : P) :
    letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
    IsLUB (Set.range fun i => tagAGen m' ((g i) a)) (tagAGen m' (gLim a)) := by
  letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
  have hlub := tagAGen_isLUB m' hm' hmt' hbt' (hg a)
  rwa [image_range_eq] at hlub

/-- **`Φ`'s morphism action is locally continuous at copy-`B` points.**  The
side condition is copy `B`'s canon-fixed domain, on the family's values. -/
theorem baseMapGen_isLUB_tagB (m' : P') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) (g : ι → (P →o P')) (gLim : P → P')
    (hg : ∀ a, IsLUB (Set.range fun i => (g i) a) (gLim a)) (a : P)
    (hb : ∀ i, (g i) a ≠ ⊥) :
    letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
    IsLUB (Set.range fun i => tagBGen m' hm' hbt' ((g i) a))
      (tagBGen m' hm' hbt' (gLim a)) := by
  letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
  have hlub := tagBGen_isLUB m' hm' hmt' hbt' (hg a)
    ⟨(g (Classical.arbitrary ι)) a, ⟨_, rfl⟩⟩ (by rintro _ ⟨i, rfl⟩; exact hb i)
  rwa [image_range_eq] at hlub

/-- **`Φ`'s morphism action is locally continuous at copy-`C` points.**  The
side conditions are copy `C`'s canon-fixed domain, on the family's values.
There is **no** condition on the supremum: `GenContinuityTransport` absorbs the
case `gLim a = m'` into the seam. -/
theorem baseMapGen_isLUB_tagC (m' : P') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) (g : ι → (P →o P')) (gLim : P → P')
    (hg : ∀ a, IsLUB (Set.range fun i => (g i) a) (gLim a)) (a : P)
    (hb : ∀ i, (g i) a ≠ ⊥) (hm : ∀ i, (g i) a ≠ m') :
    letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
    IsLUB (Set.range fun i => tagCGen m' hm' hbt' ((g i) a))
      (tagCGen m' hm' hbt' (gLim a)) := by
  letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
  have hlub := tagCGen_isLUB m' hm' hmt' hbt' (hg a)
    ⟨(g (Classical.arbitrary ι)) a, ⟨_, rfl⟩⟩
    (by rintro _ ⟨i, rfl⟩; exact hb i) (by rintro _ ⟨i, rfl⟩; exact hm i)
  rwa [image_range_eq] at hlub

/-- **The two halves composed, at copy-`A` points.**

The hypothesis `hg` is exactly what `endHom_isLUB` produces (pointwise, before
the bridge), so this is `Φ ∘ End` local continuity at copy `A` with the `End`
half already discharged: the family `g i` is the `End` action of the `i`-th
deflation, and its pointwise suprema come from `comp_isLUB`.

`P` is kept abstract on purpose — see item 3 of the module docstring on why
this is not instantiated at a hom-type here. -/
theorem phiEnd_isLUB_tagA (m' : P') (hm' : m' ≠ ⊥) (hmt' : m' ≠ ⊤)
    (hbt' : (⊥ : P') ≠ ⊤) (g : ι → (P →o P')) (gLim : P →o P')
    (hg : ∀ a, IsLUB (Set.range fun i => (g i) a) (gLim a)) (a : P) :
    letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
    IsLUB (Set.range fun i => tagAGen m' ((g i) a)) (tagAGen m' (gLim a))
      ∧ IsLUB (Set.range g) gLim := by
  letI := glueCarPartialOrderGen (P := P') m' hm' hmt' hbt'
  exact ⟨baseMapGen_isLUB_tagA m' hm' hmt' hbt' g (gLim : P → P') hg a,
    isLUB_orderHom_of_pointwise g gLim hg⟩

end PhiSide

end EndLocalContinuity
